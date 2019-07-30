import ast
import textwrap
import inspect
import astor
import _kratos
from .util import print_src, get_fn_ln
import copy


class ForNodeVisitor(ast.NodeTransformer):
    class NameVisitor(ast.NodeTransformer):
        def __init__(self, target, value):
            self.target = target
            self.value = value

        def visit_Name(self, node):
            if node.id == self.target.id:
                if isinstance(self.value, int):
                    return ast.Num(n=self.value, lineno=node.lineno)
                else:
                    return ast.Str(s=self.value, lineno=node.lineno)
            return node

    def __init__(self, generator, fn_src, local):
        super().__init__()
        self.generator = generator
        self.fn_src = fn_src
        self.local = local.copy()
        self.local["self"] = self.generator

    def visit_For(self, node: ast.For):
        # making sure that we don't have for/else case
        if len(node.orelse) > 0:
            # this is illegal syntax
            lines = [n.lineno for n in node.orelse]
            print_src(self.fn_src, lines)
            raise SyntaxError("Illegal Syntax: you are not allowed to use "
                              "for/else in code block")
        # get the target
        iter_ = node.iter
        iter_src = astor.to_source(iter_)
        try:
            iter_obj = eval(iter_src, self.local)
            iter_ = list(iter_obj)
        except RuntimeError:
            print_src(self.fn_src, node.iter.lineno)
            raise SyntaxError("Unable to statically evaluate loop iter")
        for v in iter_:
            if not isinstance(v, (int, str)):
                print_src(self.fn_src, node.iter.lineno)
                raise SyntaxError("Loop iter has to be either integer or "
                                  "string, got " + str(type(v)))
        target = node.target
        if not isinstance(target, ast.Name):
            print_src(self.fn_src, node.iter.lineno)
            raise SyntaxError("Unable to parse loop "
                              "target " + astor.to_source(target))
        new_node = []
        for value in iter_:
            loop_body = copy.deepcopy(node.body)
            for n in loop_body:
                # need to replace all the reference to
                visitor = ForNodeVisitor.NameVisitor(target, value)
                n = visitor.visit(n)
                new_node.append(n)
        return new_node


class IfNodeVisitor(ast.NodeTransformer):
    def __init__(self, generator, fn_src, local):
        super().__init__()
        self.generator = generator
        self.fn_src = fn_src
        self.local = local.copy()
        self.local["self"] = self.generator

    def __change_if_predicate(self, node):
        if not isinstance(node, ast.Compare):
            return node
        op = node.ops[0]
        if not isinstance(op, ast.Eq):
            return node
        left = node.left
        left_src = astor.to_source(left)
        left_val = eval(left_src, self.local)
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
        predicate_value = eval(predicate_src, self.local)
        # if's a kratos var, we continue
        if not isinstance(predicate_value, _kratos.Var):
            if not isinstance(predicate_value, bool):
                print_src(self.fn_src, predicate.lineno)
                raise Exception("Cannot statically evaluate if predicate")
            if predicate_value:
                for i, n in enumerate(node.body):
                    if_exp = IfNodeVisitor(self.generator, self.fn_src,
                                           self.local)
                    node.body[i] = if_exp.visit(n)
                return node.body
            else:
                for i, n in enumerate(node.orelse):
                    if_exp = IfNodeVisitor(self.generator, self.fn_src,
                                           self.local)
                    node.orelse[i] = if_exp.visit(n)
                return node.orelse

        expression = node.body
        else_expression = node.orelse

        # recursive call
        for idx, node in enumerate(expression):
            if_exp = IfNodeVisitor(self.generator, self.fn_src, self.local)
            expression[idx] = if_exp.visit(node)
        for idx, node in enumerate(else_expression):
            else_exp = IfNodeVisitor(self.generator, self.fn_src, self.local)
            else_expression[idx] = else_exp.visit(node)

        if self.generator.debug:
            keywords = [ast.keyword(arg="f_ln", value=ast.Num(n=node.lineno))]
        else:
            keywords = []

        if_node = ast.Call(func=ast.Attribute(value=ast.Name(id="scope",
                                                             ctx=ast.Load()),
                                              attr="if_",
                                              cts=ast.Load()),
                           args=[predicate] + expression,
                           keywords=keywords,
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
        self.generator = generator
        self.filename = filename
        self.ln = ln

        self._level = 0

    def if_(self, target, *args, f_ln=None):
        class IfStatement:
            def __init__(self, scope):
                self._if = _kratos.IfStmt(target)
                if f_ln is not None:
                    target.add_fn_ln((scope.filename,
                                      f_ln + scope.ln - 1))
                    self._if.add_fn_ln((scope.filename,
                                        f_ln + scope.ln - 1))
                self.scope = scope
                for stmt in args:
                    if hasattr(stmt, "stmt"):
                        stmt = stmt.stmt()
                    self._if.add_then_stmt(stmt)

            def else_(self, *_args):
                for stmt in _args:
                    if hasattr(stmt, "stmt"):
                        self._if.add_else_stmt(stmt.stmt())
                    else:
                        self._if.add_else_stmt(stmt)
                return self

            def stmt(self):
                return self._if

        if_stmt = IfStatement(self)
        return if_stmt

    def assign(self, a, b, f_ln=None):
        assert isinstance(a, _kratos.Var)
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
        return stmt

    def add_stmt(self, stmt):
        self.stmt_list.append(stmt)

    def statements(self):
        return self.stmt_list


def add_stmt_to_scope(fn_body):
    for i in range(len(fn_body.body)):
        node = fn_body.body[i]
        fn_body.body[i] = ast.Expr(
            value=ast.Call(func=ast.Attribute(
                value=ast.Name(id="scope",
                               ctx=ast.Load()),
                attr="add_stmt",
                cts=ast.Load()),
                args=[node],
                keywords=[]))


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
    assert len(args) <= 1, "statement block {0} has ".format(fn_name) + \
                           "to be defined as def {0}(self) or {0}()".format(
                               fn_name)
    insert_self = len(args) == 1
    if insert_self:
        _locals = {}
    else:
        # pre-compute the frames
        # we have 2 frames back
        f = inspect.currentframe().f_back.f_back
        _locals = f.f_locals.copy()
    # add out scope to the arg list to capture all the statements
    args.append(ast.arg(arg="scope", annotation=None))

    # transform assign
    assign_visitor = AssignNodeVisitor(generator, debug)
    fn_body = assign_visitor.visit(fn_body)
    ast.fix_missing_locations(fn_body)

    # static eval for loop
    for_visitor = ForNodeVisitor(generator, fn_src, _locals)
    fn_body = for_visitor.visit(fn_body)

    # transform if and static eval any for loop
    if_visitor = IfNodeVisitor(generator, fn_src, _locals)
    fn_body = if_visitor.visit(fn_body)
    ast.fix_missing_locations(fn_body)

    # add stmt to the scope
    add_stmt_to_scope(fn_body)

    # add code to run it
    if insert_self:
        args = [ast.Name(id="_self", ctx=ast.Load())]
    else:
        args = []
    args.append(ast.Name(id="_scope", ctx=ast.Load()))
    call_node = ast.Call(func=ast.Name(id=fn_name, ctx=ast.Load()),
                         args=args,
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
    _locals.update({"_self": generator, "_scope": scope})
    exec(code_obj, _locals)
    stmts = scope.statements()
    return sensitivity, stmts


def extract_sensitivity_from_dec(deco_list, fn_name):
    if len(deco_list) == 0:
        return []
    else:
        assert len(deco_list) == 1, \
            "{0} is not called with @always block".format(fn_name)
        call_obj = deco_list[0]
        assert isinstance(call_obj, ast.Call), \
            "{0} is not called with @always block".format(fn_name)
        # making sure it's always
        call_name = call_obj.func.id
        assert call_name == "always"
        raw_sensitivity = call_obj.args
        result = []
        for entry in raw_sensitivity:
            assert len(entry.elts) == 2
            edge_node, signal_name_node = entry.elts
            if isinstance(edge_node, ast.Name):
                edge_type = edge_node.id
            else:
                edge_type = edge_node.attr
            edge_type = edge_type.capitalize()
            signal_name = signal_name_node.s
            result.append((edge_type, signal_name))
        return result


def get_ln(fn):
    info = inspect.getsourcelines(fn)
    return info[1]
