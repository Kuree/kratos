import ast
import textwrap
import inspect
import astor
import _kratos


class IfNodeVisitor(ast.NodeTransformer):
    def __init__(self, generator):
        super().__init__()
        self.generator = generator

    def __change_if_predicate(self, node):
        if not isinstance(node, ast.Compare):
            return node
        op = node.ops[0]
        if not isinstance(op, ast.Eq):
            return node
        left = node.left
        left_src = astor.to_source(left)
        left_val = eval(left_src, {"self": self.generator})
        if isinstance(left_val, _kratos.Var):
            # change it into a function all
            return ast.Call(func=ast.Attribute(value=left,
                                               attr="eq",
                                               cts=ast.Load()),
                            args=node.comparators,
                            keywords=[],
                            ctx=ast.Load)

    def visit_If(self, node: ast.If):
        predicate = node.test
        # if it's a var comparison, we change it to eq functional call
        predicate = self.__change_if_predicate(predicate)
        # we only replace stuff if the predicate has something to do with the
        # verilog variable
        predicate_src = astor.to_source(predicate)
        predicate_value = eval(predicate_src, {"self": self.generator})
        # if's a kratos var, we continue
        if not isinstance(predicate_value, _kratos.Var):
            return node

        expression = node.body
        else_expression = node.orelse

        # recursive call
        for idx, node in enumerate(expression):
            if_exp = IfNodeVisitor(self.generator)
            expression[idx] = if_exp.visit(node)
        for idx, node in enumerate(else_expression):
            else_exp = IfNodeVisitor(self.generator)
            else_expression[idx] = else_exp.visit(node)

        if_node = ast.Call(func=ast.Attribute(value=ast.Name(id="scope",
                                                             ctx=ast.Load()),
                                              attr="if_",
                                              cts=ast.Load()),
                           args=[predicate] + expression,
                           keywords=[],
                           ctx=ast.Load)
        else_node = ast.Call(func=ast.Attribute(attr="else_", value=if_node,
                                                cts=ast.Load()),
                             args=else_expression, keywords=[])

        return ast.Expr(value=else_node)


class AssignNodeVisitor(ast.NodeTransformer):
    def __init__(self, generator):
        super().__init__()
        self.generator = generator

    def visit_Assign(self, node):
        if len(node.targets) > 1:
            raise Exception("tuple unpacking not allowed. got " +
                            astor.to_source(node))
        return ast.Expr(
            value=ast.Call(func=ast.Attribute(value=ast.Name(id="scope",
                                                             ctx=ast.Load()),
                                              attr="assign",
                                              cts=ast.Load()),
                           args=node.targets + [node.value],
                           keywords=[]))


class Scope:
    def __init__(self, generator):
        self.stmt_list = []
        self.nested_stmts = set()
        self.generator = generator

    def if_(self, target, *args):
        class IfStatement:
            def __init__(self, scope):
                self._if = _kratos.IfStmt(target)
                self.scope = scope
                for stmt in args:
                    if hasattr(stmt, "stmt"):
                        stmt = stmt.stmt()
                    self.scope.nested_stmts.add(stmt)
                    self._if.add_then_stmt(stmt)

            def else_(self, *_args):
                for stmt in _args:
                    self.scope.nested_stmts.add(stmt)
                    if hasattr(stmt, "stmt"):
                        self._if.add_else_stmt(stmt.stmt())
                    else:
                        self._if.add_else_stmt(stmt)
                return self

            def stmt(self):
                return self._if

        if_stmt = IfStatement(self)
        self.stmt_list.append(if_stmt)
        return if_stmt

    def assign(self, a, b):
        assert isinstance(a, _kratos.Var)
        if isinstance(b, int):
            # we need to convert b into an integer
            b = self.generator.const(b, a.width, a.signed)
        stmt = a.assign(b)
        self.stmt_list.append(stmt)
        return stmt

    def statements(self):
        # we have some scope level and nested assignments
        # need to remove them
        scope_level_stmts = set(self.stmt_list)
        stmts_to_remove = scope_level_stmts & self.nested_stmts
        for stmt in stmts_to_remove:
            self.stmt_list.remove(stmt)
        return self.stmt_list


def transform_stmt_block(generator, fn):
    fn_src = inspect.getsource(fn)
    fn_name = fn.__name__
    func_tree = ast.parse(textwrap.dedent(fn_src))
    fn_body = func_tree.body[0]
    # extract the sensitivity list from the decorator
    sensitivity = extract_sensitivity_from_dec(fn_body.decorator_list,
                                               fn_name)
    # remove the decorator
    fn_body.decorator_list = []
    # check the function args. it should only has one self now
    args = fn_body.args.args
    assert len(args) == 1, f"statement block {fn_name} has " \
        f"to be defined as def {fn_name}(self)"
    # add out scope to the arg list to capture all the statements
    args.append(ast.arg(arg="scope", annotation=None))

    # transform assign
    assign_visitor = AssignNodeVisitor(generator)
    fn_body = assign_visitor.visit(fn_body)
    ast.fix_missing_locations(fn_body)

    # transform if
    if_visitor = IfNodeVisitor(generator)
    if_visitor.visit(fn_body)
    ast.fix_missing_locations(fn_body)

    # add code to run it
    call_node = ast.Call(func=ast.Name(id=fn_name, ctx=ast.Load()),
                         args=[ast.Name(id="_self", ctx=ast.Load()),
                               ast.Name(id="_scope", ctx=ast.Load())],
                         keywords=[],
                         ctx=ast.Load
                         )
    func_tree.body.append(ast.Expr(value=call_node))

    src = astor.to_source(func_tree)
    code_obj = compile(src, "<ast>", "exec")
    # transform the statement list
    scope = Scope(generator)
    exec(code_obj, {"_self": generator, "_scope": scope})
    stmts = scope.statements()
    return sensitivity, stmts


def extract_sensitivity_from_dec(deco_list, fn_name):
    if len(deco_list) == 0:
        return []
    else:
        assert len(deco_list) == 1, \
            f"{fn_name} is not called with @always block"
        call_obj = deco_list[0]
        assert isinstance(call_obj, ast.Call), \
            f"{fn_name} is not called with @always block"
        # making sure it's always
        call_name = call_obj.func.id
        assert call_name == "always"
        raw_sensitivity = call_obj.args[0]
        assert isinstance(raw_sensitivity, ast.List)
        result = []
        for entry in raw_sensitivity.elts:
            assert len(entry.elts) == 2
            edge_node, signal_name_node = entry.elts
            edge_type_name = edge_node.attr
            signal_name = signal_name_node.s
            result.append((edge_type_name, signal_name))
        return result
