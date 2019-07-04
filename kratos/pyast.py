import ast
import textwrap
import inspect
import astor
import _kratos
import os
from .util import print_src


# illegal syntax checker
class IllegalSyntaxVisitor(ast.NodeVisitor):
    def __init__(self, fn_src, if_lineno):
        self.fn_src = fn_src
        self.if_lineno = if_lineno

    def visit_For(self, node: ast.For):
        print_src(self.fn_src, [self.if_lineno, node.lineno])
        raise SyntaxError("Illegal Syntax: you are not allowed to have for loop"
                          "inside if statement. Please check the source code")


class IfNodeVisitor(ast.NodeTransformer):
    def __init__(self, generator, fn_src):
        super().__init__()
        self.generator = generator
        self.fn_src = fn_src

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
            if not isinstance(predicate_value, bool):
                print_src(self.fn_src, predicate.lineno)
                raise Exception("Cannot statically evaluate if predicate")
            if predicate_value:
                for i, n in enumerate(node.body):
                    if_exp = IfNodeVisitor(self.generator, self.fn_src)
                    node.body[i] = if_exp.visit(n)
                return node.body
            else:
                for i, n in enumerate(node.orelse):
                    if_exp = IfNodeVisitor(self.generator, self.fn_src)
                    node.orelse[i] = if_exp.visit(n)
                return node.orelse

        # check syntax
        visitor = IllegalSyntaxVisitor(self.fn_src, node.lineno)
        visitor.generic_visit(node)

        expression = node.body
        else_expression = node.orelse

        # recursive call
        for idx, node in enumerate(expression):
            if_exp = IfNodeVisitor(self.generator, self.fn_src)
            expression[idx] = if_exp.visit(node)
        for idx, node in enumerate(else_expression):
            else_exp = IfNodeVisitor(self.generator, self.fn_src)
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
    def __init__(self, generator, debug):
        super().__init__()
        self.generator = generator
        self.debug = debug

    def visit_Assign(self, node):
        if len(node.targets) > 1:
            raise Exception("tuple unpacking not allowed. got " +
                            astor.to_source(node))
        if self.debug:
            return ast.Expr(
                value=ast.Call(func=ast.Attribute(
                    value=ast.Name(id="scope",
                                   ctx=ast.Load()),
                    attr="assign",
                    cts=ast.Load()),
                    args=node.targets + [node.value, ast.Num(n=node.lineno)],
                    keywords=[]))
        else:
            return ast.Expr(
                value=ast.Call(func=ast.Attribute(
                    value=ast.Name(id="scope",
                                   ctx=ast.Load()),
                    attr="assign",
                    cts=ast.Load()),
                    args=node.targets + [node.value],
                    keywords=[]))


class Scope:
    def __init__(self, generator, filename, ln):
        self.stmt_list = []
        self.nested_stmts = set()
        self.generator = generator
        self.filename = filename
        self.ln = ln

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

    def assign(self, a, b, f_ln=None):
        assert isinstance(a, _kratos.Var)
        if isinstance(b, int):
            # we need to convert b into an integer
            b = self.generator.const(b, a.width, a.signed)
        try:
            stmt = a.assign(b)
        except _kratos.exception.VarException as ex:
            if f_ln is not None:
                print_src(self.filename, f_ln + self.ln - 1)
            # re-throw it
            raise ex
        if self.filename:
            assert f_ln is not None
            stmt.add_fn_ln((self.filename, f_ln + self.ln - 1))
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


def transform_stmt_block(generator, fn, debug=False):
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
    assign_visitor = AssignNodeVisitor(generator, debug)
    fn_body = assign_visitor.visit(fn_body)
    ast.fix_missing_locations(fn_body)

    # transform if
    if_visitor = IfNodeVisitor(generator, fn_src)
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
    # if in debug mode, we trace the filename
    if debug:
        filename, _ = get_fn_ln(3)
        ln = get_ln(fn)
    else:
        filename = ""
        ln = 0
    # notice that this ln is an offset
    scope = Scope(generator, filename, ln)
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


def get_fn_ln(depth: int = 2):
    frame = inspect.stack()[depth]
    filename = frame.filename
    filename = os.path.abspath(filename)
    ln = frame.lineno
    return filename, ln


def get_ln(fn):
    info = inspect.getsourcelines(fn)
    return info[1]
