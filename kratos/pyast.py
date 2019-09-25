import ast
import textwrap
import inspect
import astor
import _kratos
from .util import print_src, signed, const
import copy
import os
import enum


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

    def __init__(self, generator, fn_src, local, global_):
        super().__init__()
        self.generator = generator
        self.fn_src = fn_src
        self.local = local.copy()
        self.global_ = global_.copy()
        self.local["self"] = self.generator
        self.target_node = {}

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
            iter_obj = eval(iter_src, self.global_, self.local)
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
                n = self.generic_visit(n)
                new_node.append(n)
                self.target_node[n] = (target.id, value)
        return new_node


class IfNodeVisitor(ast.NodeTransformer):
    def __init__(self, generator, fn_src, local, global_):
        super().__init__()
        self.generator = generator
        self.fn_src = fn_src
        self.local = local.copy()
        self.global_ = global_
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
        predicate_value = eval(predicate_src, self.global_, self.local)
        # if's a kratos var, we continue
        if not isinstance(predicate_value, _kratos.Var):
            if not isinstance(predicate_value, bool):
                print_src(self.fn_src, predicate.lineno)
                raise Exception("Cannot statically evaluate if predicate")
            if predicate_value:
                for i, n in enumerate(node.body):
                    if_exp = IfNodeVisitor(self.generator, self.fn_src,
                                           self.local, self.global_)
                    node.body[i] = if_exp.visit(n)
                return node.body
            else:
                for i, n in enumerate(node.orelse):
                    if_exp = IfNodeVisitor(self.generator, self.fn_src,
                                           self.local, self.global_)
                    node.orelse[i] = if_exp.visit(n)
                return node.orelse

        expression = node.body
        else_expression = node.orelse

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

        return self.generic_visit(ast.Expr(value=else_node))


class AssignNodeVisitor(ast.NodeTransformer):
    def __init__(self, generator, debug):
        super().__init__()
        self.generator = generator
        self.debug = debug

    def visit_Assign(self, node):
        if len(node.targets) > 1:
            raise Exception("tuple unpacking not allowed. got " +
                            astor.to_source(node))
        args = node.targets[:] + [node.value]
        if self.debug:
            args.append(ast.Num(n=node.lineno))
        return ast.Expr(
            value=ast.Call(func=ast.Attribute(
                value=ast.Name(id="scope",
                               ctx=ast.Load()),
                attr="assign",
                cts=ast.Load()),
                args=args,
                keywords=[]))


class ReturnNodeVisitor(ast.NodeTransformer):
    def __init__(self, scope_name, debug=False):
        self.scope_name = scope_name
        self.debug = debug

    def visit_Return(self, node: ast.Return):
        value = node.value
        args = [value]
        if self.debug:
            args.append(ast.Num(n=node.lineno))

        return ast.Expr(value=ast.Call(func=ast.Attribute(
            value=ast.Name(id=self.scope_name,
                           ctx=ast.Load()),
            attr="return_",
            cts=ast.Load()),
            args=args,
            keywords=[]))


class AssignLocalVisitor(ast.NodeTransformer):
    def __init__(self, name, value, scope_name):
        self.name = name
        self.value = value
        self.scope_name = scope_name

    def visit_Call(self, node: ast.Call):
        if isinstance(node.func, ast.Attribute):
            attr = node.func
            if attr.attr == "assign" and \
                    isinstance(attr.value, ast.Name) \
                    and attr.value.id == self.scope_name:
                keyword = ast.keyword(arg=self.name,
                                      value=ast.Str(s=self.value))
                node.keywords.append(keyword)
        return node


def add_scope_context(stmt, _locals):
    for key, value in _locals.items():
        if isinstance(value, (int, float, str, bool)):
            # this is straight forward one
            stmt.add_scope_variable(key, str(value), False)
        elif isinstance(value, _kratos.Var):
            # it's a var
            stmt.add_scope_variable(key, value.handle_name(), True)


def get_frame_local(num_frame=2):
    frame = inspect.currentframe()
    for i in range(num_frame):
        frame = frame.f_back
    return frame.f_locals


class Scope:
    def __init__(self, generator, filename, ln):
        self.stmt_list = []
        self.generator = generator
        self.filename = filename
        if self.filename:
            assert os.path.isfile(self.filename)
        self.ln = ln

        self._level = 0

    def if_(self, target, *args, f_ln=None, **kargs):
        class IfStatement:
            def __init__(self, scope):
                self._if = _kratos.IfStmt(target)
                if f_ln is not None:
                    target.add_fn_ln((scope.filename,
                                      f_ln + scope.ln - 1))
                    self._if.add_fn_ln((scope.filename,
                                        f_ln + scope.ln - 1))
                    # this is additional info passed in
                    add_scope_context(self._if, kargs)

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

            def add_scope_variable(self, name, value, is_var=False):
                self._if.add_scope_variable(name, value, is_var)

        if_stmt = IfStatement(self)
        return if_stmt

    def assign(self, a, b, f_ln=None, **kargs):
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
            # obtain the previous call frame info
            __local = get_frame_local()
            add_scope_context(stmt, __local)
            # this is additional info passed in
            add_scope_context(stmt, kargs)
        return stmt

    def add_stmt(self, stmt):
        self.stmt_list.append(stmt)

    def statements(self):
        return self.stmt_list


class FuncScope(Scope):
    def __init__(self, generator, func_name, filename, ln):
        super().__init__(generator, filename, ln)
        if generator is not None:
            self.__func = generator.internal_generator.function(func_name)

        self.__var_ordering = {}

    def input(self, var_name, width, is_signed=False) -> _kratos.Var:
        return self.__func.input(var_name, width, is_signed)

    def return_(self, value, f_ln=None):
        stmt = self.__func.return_stmt(value)
        if f_ln is not None:
            stmt.add_fn_ln((self.filename, f_ln + self.ln - 1))
        return stmt


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


def __ast_transform_blocks(generator, func_tree, fn_src, fn_name, insert_self,
                           transform_return=False, pre_locals=None):
    # pre-compute the frames
    # we have 3 frames back
    f = inspect.currentframe().f_back.f_back.f_back
    # will go one above to get the locals as well?
    if f.f_back is not None:
        _locals = f.f_back.f_locals.copy()
    else:
        _locals = {}
    _locals.update(f.f_locals)
    _globals = f.f_globals.copy()

    if pre_locals is not None:
        _locals.update(pre_locals)

    # transform assign
    debug = generator.debug
    fn_body = func_tree.body[0]

    func_args = fn_body.args.args
    # add out scope to the arg list to capture all the statements
    func_args.append(ast.arg(arg="scope", annotation=None))

    if transform_return:
        return_visitor = ReturnNodeVisitor("scope", generator.debug)
        return_visitor.visit(fn_body)

    assign_visitor = AssignNodeVisitor(generator, debug)
    fn_body = assign_visitor.visit(fn_body)
    ast.fix_missing_locations(fn_body)

    # static eval for loop
    for_visitor = ForNodeVisitor(generator, fn_src, _locals, _globals)
    fn_body = for_visitor.visit(fn_body)

    # transform if and static eval any for loop
    if_visitor = IfNodeVisitor(generator, fn_src, _locals, _globals)
    fn_body = if_visitor.visit(fn_body)
    ast.fix_missing_locations(fn_body)

    # mark the local variables
    target_nodes = for_visitor.target_node
    for node, (key, value) in target_nodes.items():
        assign_local_visitor = AssignLocalVisitor(key, value, "scope")
        assign_local_visitor.visit(node)

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
    return _locals


def inject_import_code(code_src):
    line1 = "import kratos"
    line2 = "from kratos import *"
    return "\n".join([line1, line2, code_src])


class CodeBlockType(enum.Enum):
    Sequential = enum.auto()
    Combinational = enum.auto()
    Initial = enum.auto()


def transform_stmt_block(generator, fn):
    fn_src = inspect.getsource(fn)
    fn_name = fn.__name__
    func_tree = ast.parse(textwrap.dedent(fn_src))
    fn_body = func_tree.body[0]
    # needs debug
    debug = generator.debug
    # extract the sensitivity list from the decorator
    blk_type, sensitivity = extract_sensitivity_from_dec(fn_body.decorator_list,
                                                         fn_name)
    # remove the decorator
    fn_body.decorator_list = []
    # check the function args. it should only has one self now
    func_args = fn_body.args.args
    assert len(func_args) <= 1, \
        "statement block {0} has ".format(fn_name) + \
        "to be defined as def {0}(self) or {0}()".format(fn_name)
    insert_self = len(func_args) == 1

    _locals = __ast_transform_blocks(generator, func_tree, fn_src, fn_name,
                                     insert_self)

    src = astor.to_source(func_tree)
    src = inject_import_code(src)
    code_obj = compile(src, "<ast>", "exec")
    # transform the statement list
    # if in debug mode, we trace the filename
    if debug:
        filename = get_fn(fn)
        ln = get_ln(fn)
    else:
        filename = ""
        ln = 0
    # notice that this ln is an offset
    scope = Scope(generator, filename, ln)
    _locals.update({"_self": generator, "_scope": scope})
    exec(code_obj, _locals)
    stmts = scope.statements()
    return blk_type, sensitivity, stmts


def transform_function_block(generator, fn, arg_types):
    fn_src = inspect.getsource(fn)
    fn_name = fn.__name__
    func_tree = ast.parse(textwrap.dedent(fn_src))
    fn_body = func_tree.body[0]
    # needs debug
    debug = generator.debug

    # remove the decorator
    fn_body.decorator_list = []

    # check the function args. it should only has one self now
    func_args = fn_body.args.args
    insert_self = func_args[0].arg == "self"
    # only keep self
    fn_body.args.args = [func_args[0]]
    # add function args now
    if debug:
        filename = get_fn(fn)
        ln = get_ln(fn)
    else:
        filename = ""
        ln = 0
    scope = FuncScope(generator, fn_name, filename, ln)
    # add var creations
    arg_order = extract_arg_name_order_from_ast(func_args)
    var_body = declare_var_definition(arg_types, arg_order)
    var_src = astor.to_source(ast.Module(body=var_body))
    pre_locals = {"_scope": scope}
    var_code_obj = compile(var_src, "<ast>", "exec")
    exec(var_code_obj, pre_locals)
    _locals = __ast_transform_blocks(generator, func_tree, fn_src,
                                     fn_name, insert_self,
                                     transform_return=True,
                                     pre_locals=pre_locals)

    src = astor.to_source(func_tree)
    src = inject_import_code(src)
    code_obj = compile(src, "<ast>", "exec")

    _locals.update({"_self": generator, "_scope": scope})
    exec(code_obj, _locals)
    stmts = scope.statements()
    return arg_order, stmts


def declare_var_definition(var_def, arg_order):
    body = []
    for idx, name in arg_order.items():
        width, is_signed = var_def[idx]
        body.append(ast.Assign(targets=[ast.Name(id=name)],
                               value=ast.Call(func=ast.Attribute(
                                   value=ast.Name(id="_scope",
                                                  ctx=ast.Load()),
                                   attr="input",
                                   cts=ast.Load()),
                                   args=[ast.Str(s=name), ast.Num(n=width),
                                         ast.NameConstant(value=is_signed)],
                                   keywords=[])))
    return body


def extract_arg_name_order_from_ast(func_args):
    result = {}
    for idx, arg in enumerate(func_args):
        if arg.arg != "self":
            result[len(result)] = arg.arg
    return result


def extract_arg_name_order_from_fn(fn):
    fn_src = inspect.getsource(fn)
    func_tree = ast.parse(textwrap.dedent(fn_src))
    fn_body = func_tree.body[0]
    func_args = fn_body.args.args
    return extract_arg_name_order_from_ast(func_args)


def extract_sensitivity_from_dec(deco_list, fn_name):
    if len(deco_list) == 0:
        return CodeBlockType.Combinational, []
    else:
        assert len(deco_list) == 1, \
            "{0} is not called with multiple decorators blocks".format(fn_name)
        call_obj = deco_list[0]
        if isinstance(call_obj, ast.Call):
            call_name = call_obj.func.id
            assert call_name == "always", \
                "{0} is not called with @always block".format(fn_name)
        else:
            assert isinstance(call_obj, ast.Name)
            call_name = call_obj.id
            assert call_name == "initial", \
                "{0} is not called with @initial block".format(fn_name)
            return CodeBlockType.Initial, []
        blk_type = CodeBlockType.Sequential
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
        return blk_type, result


def get_ln(fn):
    info = inspect.getsourcelines(fn)
    return info[1]


def get_fn(fn):
    return os.path.abspath(inspect.getsourcefile(fn))
