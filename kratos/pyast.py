import ast
import copy
import enum
import inspect
import os
import sys
import textwrap

import _kratos
import astor
from _kratos import get_frame_local, StatementBlockType

from .util import print_src


def has_format_string():
    return sys.version_info[1] >= 7


def __pretty_source(source):
    return "".join(source)


class LogicOperatorVisitor(ast.NodeTransformer):
    def __init__(self, local, global_, filename, scope_ln):
        self.local = local
        self.global_ = global_
        self.filename = filename
        self.scope_ln = scope_ln

    def get_file_line(self, ln):
        ln += self.scope_ln
        with open(self.filename) as f:
            lines = f.readlines()
        return lines[ln - 2]

    @staticmethod
    def concat_ops(func_name, values):
        # this is a recursive call
        assert len(values) > 0
        if len(values) == 1:
            return values[0]
        node = ast.Call(func=ast.Attribute(attr=func_name, value=values[0],
                                           ctx=ast.Load()),
                        args=[values[1]], keywords=[])
        values = [node] + values[2:]
        return LogicOperatorVisitor.concat_ops(func_name, values)

    def check_var(self, var):
        r = eval(astor.to_source(var), self.local, self.global_)
        if not isinstance(r, _kratos.Var):
            raise SyntaxError("Cannot mix kratos variable with normal Python values in logical ops",
                              [self.filename, self.scope_ln + var.lineno,
                               var.col_offset, self.get_file_line(var.lineno)])

    def visit_BoolOp(self, node):
        # convert the bool op into a logical function
        # we don't allow mixing bool ops with normal python values and kratos values
        if isinstance(node.op, ast.And):
            # it's an and
            values = node.values
            for i in range(len(values)):
                values[i] = self.visit(values[i])
                self.check_var(values[i])
            return self.concat_ops("and_", values)
        elif isinstance(node.op, ast.Or):
            # it's an or
            values = node.values
            for i in range(len(values)):
                values[i] = self.visit(values[i])
            # the same as and
            return self.concat_ops("or_", values)
        else:
            raise SyntaxError("Invalid logical operator", (self.filename,
                                                           self.scope_ln + node.lineno,
                                                           node.col_offset,
                                                           self.get_file_line(node.lineno)))

    def visit_UnaryOp(self, node):
        if isinstance(node.op, ast.Not):
            return ast.Call(func=ast.Attribute(attr="r_not", value=node.operand,
                                               ctx=ast.Load()),
                            args=[], keywords=[])
        return node


class StaticElaborationNodeForVisitor(ast.NodeTransformer):
    class NameVisitor(ast.NodeTransformer):
        def __init__(self, target, value):
            self.target = target
            self.value = value

        def visit_Name(self, node):
            if node.id == self.target.id:
                if isinstance(self.value, int):
                    return ast.Constant(value=self.value, lineno=node.lineno)
                elif isinstance(self.value, str):
                    return ast.Str(s=self.value, lineno=node.lineno)
                else:
                    return self.value
            return node

    class HasVar(ast.NodeVisitor):
        def __init__(self, target):
            self.has_target = False
            self.target = target
            self.legal = True

        def visit_Name(self, node):
            if node.id == self.target and self.legal:
                self.has_target = True

        def visit_JoinedStr(self, _):
            self.legal = False
            self.has_target = False

    class LoopIndexVisitor(ast.NodeVisitor):
        def __init__(self, target, scope, local_env, global_env):
            self.target = target
            self.legal = True
            self.scope = scope
            self.local_env = local_env.copy()
            # just put 0 there
            self.local_env[target.id] = 0
            self.global_env = global_env

        def visit_Subscript(self, node: ast.Subscript):
            if not self.legal:
                return
            s = node.slice
            has_var = StaticElaborationNodeForVisitor.HasVar(self.target.id)
            has_var.visit(s)
            if has_var.has_target:
                # python changed its syntax ast
                if sys.version_info.minor < 9:
                    if not isinstance(s, ast.Index):
                        self.legal = False
                        return
                # make sure that the value is a kratos var
                value_src = astor.to_source(node.value)
                try:
                    value = eval(value_src, self.local_env, self.global_env)
                    if not isinstance(value, _kratos.Var):
                        self.legal = False
                    else:
                        # make sure we can index them
                        if value.width == 1:
                            self.legal = False
                except (AttributeError, NameError):
                    return
            elif not has_var.legal:
                self.legal = False
                return
            self.generic_visit(node)

    def __init__(self, generator, fn_src, scope, unroll_for, local, global_, filename, func_ln):
        super().__init__()
        self.generator = generator
        self.fn_src = fn_src
        self.local = local.copy()
        self.global_ = global_.copy()
        self.local["self"] = self.generator
        if "scope" in local and (not isinstance(local["scope"], Scope)):
            raise SyntaxError("scope is a reserved keyword and shall not be used in a kratos program")
        self.local["scope"] = scope
        self.target_node = {}
        self.scope = scope
        self.unroll_for = unroll_for

        self.filename = filename
        self.scope_ln = func_ln

        self.key_pair = []

    def __loop_self_var(self, target, nodes):
        valid = True
        for node in nodes:
            if valid:
                visitor = StaticElaborationNodeForVisitor.LoopIndexVisitor(target, self.scope, self.local, self.global_)
                visitor.visit(node)
                valid = visitor.legal
        return valid

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

        # if not in debug mode and we are allowed to do so
        if not self.generator.debug and not self.unroll_for and isinstance(iter_obj, range) and \
                self.__loop_self_var(target, node.body):
            # return it as a function call
            _vars = iter_obj.start, iter_obj.stop, iter_obj.step, node.lineno
            _vars = [ast.Num(n=n) for n in _vars]
            keywords = []
            if self.generator.debug:
                keywords = [ast.keyword(arg="f_ln", value=ast.Constant(value=node.lineno))]
            # we redirect the var to one of the scope vars. the index is based
            # on the line number
            index_num = node.lineno
            # create the for statement in the scope
            for_stmt = _kratos.ForStmt(target.id, iter_obj.start, iter_obj.stop, iter_obj.step)
            self.scope.for_stmt[index_num] = for_stmt
            # set the for iter var
            # redirect the variable to env
            self.scope.iter_var[index_num] = for_stmt.get_iter_var()
            index = ast.Subscript(
                slice=ast.Index(value=ast.Num(n=index_num)),
                value=ast.Attribute(
                    value=ast.Name(id="scope", ctx=ast.Load()),
                    attr="iter_var", ctx=ast.Load()))
            for_node = ast.Call(func=ast.Attribute(value=ast.Name(id="scope", ctx=ast.Load()),
                                                   attr="for_", ctx=ast.Load()),
                                args=[ast.Str(s=target.id)] + _vars,
                                keywords=keywords,
                                ctx=ast.Load())
            body_visitor = StaticElaborationNodeForVisitor.NameVisitor(target, index)
            body = []
            for i in range(len(node.body)):
                n = self.visit(body_visitor.visit(node.body[i]))
                if isinstance(n, list):
                    for nn in n:
                        body.append(nn)
                else:
                    body.append(n)
            body_node = ast.Call(func=ast.Attribute(attr="loop", value=for_node, ctx=ast.Load()),
                                 args=body, keywords=[])
            # create an entry for the target
            self.local[str(target.id)] = 0
            return self.visit(ast.Expr(body_node))
        else:
            new_node = []
            for value in iter_:
                loop_body = copy.deepcopy(node.body)
                for n in loop_body:
                    # need to replace all the reference to
                    visitor = StaticElaborationNodeForVisitor.NameVisitor(target, value)
                    n = visitor.visit(n)
                    self.key_pair.append((target.id, value))
                    n = self.visit(n)
                    self.key_pair.pop(len(self.key_pair) - 1)

                    if isinstance(n, list):
                        for n_ in n:
                            new_node.append(n_)
                            self.target_node[n_] = (target.id, value)
                    else:
                        new_node.append(n)
                        self.target_node[n] = (target.id, value)
            return new_node


class StaticElaborationNodeIfVisitor(ast.NodeTransformer):
    def __init__(self, generator, fn_src, scope, local, global_, filename, func_ln):
        super().__init__()
        self.generator = generator
        self.fn_src = fn_src
        self.local = local.copy()
        self.global_ = global_.copy()
        self.local["self"] = self.generator
        if "scope" in local and (not isinstance(local["scope"], Scope)):
            raise SyntaxError("scope is a reserved keyword and shall not be used in a kratos program")
        self.local["scope"] = scope
        self.target_node = {}
        self.scope = scope

        self.filename = filename
        self.scope_ln = func_ln

        self.key_pair = []

    def __change_if_predicate(self, node):
        if isinstance(node, ast.UnaryOp):
            # notice that if the user uses `not var`, due to Python
            # implementation, it will return True/False, we need to
            # change that into r_not call
            if isinstance(node.op, ast.Not):
                target = node.operand
                target_src = astor.to_source(target)
                target_eval = eval(target_src, self.local)
                if isinstance(target_eval, _kratos.Var):
                    return ast.Call(func=ast.Attribute(value=target, attr="r_not", ctx=ast.Load()),
                                    args=[], keywords=[], ctx=ast.Load())
            else:
                return node
        elif not isinstance(node, ast.Compare):
            return node
        op = node.ops[0]
        if not isinstance(op, ast.Eq):
            return node
        left = node.left
        left_src = astor.to_source(left)
        try:
            left_val = eval(left_src, self.local)
        except _kratos.exception.VarException:
            left_val = None

        if isinstance(left_val, _kratos.Var):
            # change it into a function all
            return ast.Call(func=ast.Attribute(value=left,
                                               attr="eq",
                                               ctx=ast.Load()),
                            args=node.comparators,
                            keywords=[],
                            ctx=ast.Load)
        return node

    def visit_If(self, node: ast.If):
        predicate = node.test
        # if it's a var comparison, we change it to eq functional call
        predicate = self.__change_if_predicate(predicate)
        # we only replace stuff if the predicate has something to do with the
        # verilog variable
        predicate_src = astor.to_source(predicate)
        has_var = False
        try:
            predicate_value = eval(predicate_src, self.global_, self.local)
        except (_kratos.exception.InvalidConversionException, _kratos.exception.UserException,
                _kratos.exception.VarException) as _:
            has_var = True
            predicate_value = None

        # if's a kratos var, we continue
        if not has_var and not isinstance(predicate_value, _kratos.Var):
            if not isinstance(predicate_value, bool):
                print_src(self.fn_src, predicate.lineno)
                raise SyntaxError("Cannot statically evaluate if predicate")
            if predicate_value:
                for i, n in enumerate(node.body):
                    if_exp = StaticElaborationNodeIfVisitor(self.generator, self.fn_src, self.scope,
                                                            self.local, self.global_, self.filename, self.scope_ln)
                    node.body[i] = if_exp.visit(n)
                return node.body
            else:
                for i, n in enumerate(node.orelse):
                    if_exp = StaticElaborationNodeIfVisitor(self.generator, self.fn_src, self.scope,
                                                            self.local, self.global_, self.filename, self.scope_ln)
                    node.orelse[i] = if_exp.visit(n)
                return node.orelse
        else:
            # need to convert the logical operators to either reduced function calls, or
            # expression or
            if_test = LogicOperatorVisitor(self.local, self.global_, self.filename, self.scope_ln)
            predicate = if_test.visit(node.test)

        expression = node.body
        else_expression = node.orelse

        if self.generator.debug:
            keywords_if = [ast.keyword(arg="f_ln",
                                       value=ast.Constant(value=node.lineno))]
            # do our best guess
            if len(else_expression) > 0:
                if else_expression[0].lineno != expression[0].lineno:
                    ln = else_expression[0].lineno + 1
                else:
                    ln = else_expression[0].lineno
                keywords_else = [ast.keyword(arg="f_ln",
                                             value=ast.Constant(value=ln))]
            else:
                keywords_else = []
        else:
            keywords_if = []
            keywords_else = []
        for key, value in self.key_pair:
            keywords_if.append(ast.keyword(arg=key, value=ast.Str(s=value)))

        if_node = ast.Call(func=ast.Attribute(value=ast.Name(id="scope",
                                                             ctx=ast.Load()),
                                              attr="if_",
                                              ctx=ast.Load()),
                           args=[predicate] + expression,
                           keywords=keywords_if,
                           ctx=ast.Load)
        else_node = ast.Call(func=ast.Attribute(attr="else_", value=if_node,
                                                ctx=ast.Load()),
                             args=else_expression, keywords=keywords_else)
        # store the mapping
        self.target_node[node] = else_node
        return self.visit(ast.Expr(value=else_node))


class AugAssignNodeVisitor(ast.NodeTransformer):
    def visit_AugAssign(self, node):
        # change any aug assign to normal assign
        return ast.Assign(targets=[node.target],
                          value=ast.BinOp(left=node.target, op=node.op,
                                          right=node.value),
                          lineno=node.lineno)


class AssignNodeVisitor(ast.NodeTransformer):
    def __init__(self, generator, debug):
        super().__init__()
        self.generator = generator
        self.debug = debug
        self.target_node = {}

    def visit_Assign(self, node):
        if len(node.targets) > 1:
            raise SyntaxError("tuple unpacking not allowed. got " +
                              astor.to_source(node))
        args = node.targets[:] + [node.value]
        if self.debug:
            args.append(ast.Constant(value=node.lineno))
        new_node = ast.Expr(
            value=ast.Call(func=ast.Attribute(
                value=ast.Name(id="scope",
                               ctx=ast.Load()),
                attr="assign",
                ctx=ast.Load()),
                args=args,
                keywords=[],
                lineno=node.lineno))
        self.target_node[node] = new_node
        return new_node


class AssertNodeVisitor(ast.NodeTransformer):
    def __init__(self, generator, debug):
        super().__init__()
        self.generator = generator
        self.debug = debug

    def visit_Call(self, node: ast.Call):
        if isinstance(node.func, ast.Name) and node.func.id == "assert_":
            # we need to transform it to scope.assert_()
            args = node.args
            if self.debug:
                args.append(ast.Constant(value=node.lineno))
            return ast.Call(func=ast.Attribute(
                value=ast.Name(id="scope", ctx=ast.Load()),
                attr="assert_",
                ctx=ast.Load()),
                args=args,
                keywords=[],
                lineno=node.lineno)
        return node


class ExceptionNodeVisitor(ast.NodeTransformer):
    def __init__(self, generator, debug):
        super().__init__()
        self.generator = generator
        self.debug = debug

    def visit_Raise(self, node: ast.Raise):
        func = node.exc
        if not isinstance(func, ast.Call):
            raise SyntaxError(astor.to_source(node) + " not supported")
        name = func.func
        if not isinstance(name, ast.Name):
            raise SyntaxError(astor.to_source(node) + " not supported")
        if name.id != "Exception":
            raise SyntaxError(astor.to_source(node) + " not supported")
        # change it to assert 0
        args = [ast.Constant(0)]
        if self.debug:
            args.append(ast.Constant(value=node.lineno))
        return ast.Call(func=ast.Attribute(value=ast.Name(id="scope", ctx=ast.Load()),
                                           attr="assert_", ctx=ast.Load()), args=args, keywords=[], lineno=node.lineno)


class ReturnNodeVisitor(ast.NodeTransformer):
    def __init__(self, scope_name, debug=False):
        self.scope_name = scope_name
        self.debug = debug

    def visit_Return(self, node: ast.Return):
        value = node.value
        args = [value]
        if self.debug:
            args.append(ast.Constant(value=node.lineno))

        return ast.Expr(value=ast.Call(func=ast.Attribute(
            value=ast.Name(id=self.scope_name,
                           ctx=ast.Load()),
            attr="return_",
            ctx=ast.Load()),
            args=args,
            keywords=[],
            lineno=node.lineno),
            lineno=node.lineno)


class GenVarLocalVisitor(ast.NodeTransformer):
    def __init__(self, key, value, scope_name):
        self.key = key
        self.value = value
        self.scope_name = scope_name

    def visit_Call(self, node: ast.Call):
        if isinstance(node.func, ast.Attribute):
            attr = node.func
            insert_keywords = False
            if attr.attr == "assign" and isinstance(attr.value, ast.Name) and attr.value.id == self.scope_name:
                insert_keywords = True
            if insert_keywords:
                keyword = ast.keyword(arg=self.key,
                                      value=ast.Str(s=self.value))
                node.keywords.append(keyword)

        return self.generic_visit(node)


def transform_event(ast_tree, debug, fn, ln):
    # need to transform transaction @ event syntax into the one that supports fn ln
    class ChangeMatMult(ast.NodeTransformer):
        def visit_BinOp(self, node: ast.BinOp):
            if not isinstance(node.op, ast.MatMult):
                return node
            # replace it with a function call that calls belongs() and set filename and line number
            if debug:
                args = [node.left, ast.Constant(value=fn), ast.Constant(value=ln + node.lineno - 1)]
            else:
                args = [node.left]
            return ast.Expr(
                value=ast.Call(func=ast.Attribute(attr="belongs", value=node.right, ctx=ast.Load()), args=args,
                               ctx=ast.Load(), keywords=[]),
                lineno=node.lineno)
    visitor = ChangeMatMult()
    return visitor.visit(ast_tree)


def transform_always_comb_ssa(ast_tree, gen, _locals):
    class SSAScope:
        def __init__(self, var_ref):
            self.var_ref = var_ref.copy()
            self.created_vars = {}
            self.enable_cond = []

    class SSAVisitor(ast.NodeTransformer):
        # https://github.com/usagitoneko97/python-static-code-analysis/tree/master/cfg_and_ssa
        def __init__(self):
            self.vars = set()
            self.var_ref = {}

            self.phi_scope = [SSAScope({})]

        def visit_Assign(self, node):
            node.value = self.visit(node.value)
            # see if there is any target we need to be careful
            assert len(node.targets) == 1, "Unpacking not supported"
            target = node.targets[0]
            target = self.visit(target)
            node.targets = [target]
            return node

        def create_new_var(self, name):
            from .passes import Attribute
            assert name in _locals, "Only local variable scope is currently supported"
            var = _locals[name]
            new_name = gen.internal_generator.get_unique_variable_name("", name)
            new_var = gen.var_from_def(var, new_name)
            # this is used to indicate the original names
            new_var.add_attribute(Attribute.create("ssa={0}:{1}".format(name, var.name)))
            # scope is used to indicate the hierarchy of scopes so that the backend can reconstruct
            # the scopes
            new_var.add_attribute(Attribute.create("ssa-scope={0}".format(len(self.phi_scope))))
            # set the ssa enable condition
            if len(self.phi_scope) > 0:
                for phi in self.phi_scope:
                    cond = phi.enable_cond
                    for var in cond:
                        new_var.add_attribute(Attribute.create("ssa-en={0}".format(var)))
            _locals[new_name] = new_var
            self.var_ref[name] = new_name
            self.phi_scope[-1].created_vars[name] = new_name
            return new_name

        def visit_Name(self, node: ast.Name):
            if node.id not in self.vars:
                # whether it's a usage or an actual assign
                if isinstance(node.ctx, ast.Load):
                    return node
                else:
                    self.vars.add(node.id)
                    # need to create a rename
                    name = self.create_new_var(node.id)
                    node.id = name
                    return node
            else:
                if isinstance(node.ctx, ast.Store):
                    # need to rename again
                    name = self.create_new_var(node.id)
                    node.id = name
                else:
                    # use the existing name
                    assert node.id in self.var_ref
                    var_name = self.var_ref[node.id]
                    node.id = var_name
                return node

        def __find_var_def(self, name):
            for scope in reversed(self.phi_scope):
                if name in scope.created_vars:
                    return scope.created_vars[name]
            return None

        @staticmethod
        def __add_list(target, result):
            if isinstance(result, list):
                for e in result:
                    target.append(e)
            else:
                target.append(result)

        def set_enable_cond(self, node, is_else):
            node_str = astor.to_source(node)
            phi = self.phi_scope[-1]
            # add it to the enable
            if is_else:
                node_str = "~" + node_str
            node_str = node_str.strip()
            phi.enable_cond.append(node_str)

        def visit_If(self, node: ast.If):
            # push the mapping into a stack
            # need to flatten the if statement and add phi function
            test = self.visit(node.test)
            body = []
            self.phi_scope.append(SSAScope(self.var_ref))
            # compute the enable condition
            self.set_enable_cond(test, False)
            for stmt in node.body:
                stmt = self.visit(stmt)
                self.__add_list(body, stmt)
            body_scope: SSAScope = self.phi_scope[-1]
            # pop the last scope
            self.phi_scope = self.phi_scope[:-1]

            else_scope: SSAScope = SSAScope({})
            if node.orelse:
                self.phi_scope.append(SSAScope(self.var_ref))
                else_scope = self.phi_scope[-1]
                # compute the enable condition
                self.set_enable_cond(test, True)
                for stmt in node.orelse:
                    stmt = self.visit(stmt)
                    self.__add_list(body, stmt)
                # pop the last scope
                self.phi_scope = self.phi_scope[:-1]

            # if there is any variable created, need to create phi functions
            vars_ = []
            for var in body_scope.created_vars:
                if var not in vars_:
                    vars_.append(var)
            for var in else_scope.created_vars:
                if var not in vars_:
                    vars_.append(var)
            for var in vars_:
                if var in body_scope.created_vars:
                    true_var = body_scope.created_vars[var]
                    # both?
                    if var in else_scope.created_vars:
                        # create a phi node, in this, just a ternary
                        else_var = else_scope.created_vars[var]
                    else:
                        # need previous scope value
                        else_var = self.__find_var_def(var)
                        assert else_var is not None, "Latch {0} is created!".format(var)
                else:
                    else_var = else_scope.created_vars[var]
                    # need previous scope value
                    true_var = self.__find_var_def(var)
                    assert true_var is not None, "Latch {0} is created!".format(var)
                n = ast.Expr(value=ast.Call(func=ast.Name(id="ternary"), args=[test, ast.Name(id=true_var),
                                                                               ast.Name(id=else_var)],
                                            ctx=ast.Load(), keywords=[]),
                             lineno=test.lineno)
                new_name = self.create_new_var(var)
                n = ast.Assign(targets=[ast.Name(id=new_name, ctx=ast.Store())],
                               value=n, lineno=node.lineno)
                body.append(n)

            return body

    ssa = SSAVisitor()
    ast_tree = ssa.visit(ast_tree)

    # need to add all the wires for each ref
    for v1, v2 in ssa.var_ref.items():
        gen.wire(gen.vars[v1], gen.vars[v2], no_fn_ln=True)
    return ast_tree


def add_scope_context(stmt, _locals):
    for key, value in _locals.items():
        if isinstance(value, (int, float, str, bool)):
            # this is straight forward one
            stmt.add_scope_variable(key, str(value), False)
        elif isinstance(value, _kratos.Var) and len(value.name) > 0:
            # it's a var
            stmt.add_scope_variable(key, value.name, True)


class Scope:
    def __init__(self, generator, filename, ln, add_local):
        self.stmt_list = []
        self.generator = generator
        self.filename = filename
        if self.filename:
            assert os.path.isfile(self.filename)
        self.ln = ln
        self.add_local = add_local

        self._level = 0

        self.iter_var = {}
        self.for_stmt = {}

    def if_(self, target, *args, f_ln=None, **kargs):
        add_local = self.add_local

        class IfStatement:
            def __init__(self, scope):
                self._if = _kratos.IfStmt(target)
                if f_ln is not None:
                    fn_ln = (scope.filename, f_ln + scope.ln - 1)
                    target.add_fn_ln(fn_ln, True)
                    self._if.add_fn_ln(fn_ln, True)
                    self._if.then_body().add_fn_ln(fn_ln, True)
                    # this is additional info passed in
                    if add_local:
                        add_scope_context(self._if, kargs)

                self.scope = scope
                for stmt in args:
                    if hasattr(stmt, "stmt"):
                        stmt = stmt.stmt()
                    self._if.add_then_stmt(stmt)

            def else_(self, *_args, f_ln=None):
                for stmt in _args:
                    if hasattr(stmt, "stmt"):
                        self._if.add_else_stmt(stmt.stmt())
                    else:
                        self._if.add_else_stmt(stmt)
                if f_ln is not None:
                    fn_ln = (self.scope.filename, f_ln + self.scope.ln - 1)
                    self._if.else_body().add_fn_ln(fn_ln, True)
                return self

            def stmt(self):
                return self._if

            def add_scope_variable(self, name, value, is_var=False):
                self._if.add_scope_variable(name, value, is_var)

        if_stmt = IfStatement(self)
        return if_stmt

    def for_(self, var_name, start, end, step, index, f_ln=None, **kargs):
        add_local = self.add_local
        generator = self.generator

        class ForStatement:
            def __init__(self, scope):
                self.__scope = scope
                self.__for = self.__scope.for_stmt[index]
                self.__for.get_iter_var().set_generator(generator.internal_generator)
                if f_ln is not None:
                    fn_ln = (scope.filename, f_ln + scope.ln - 1)
                    self.__for.add_fn_ln(fn_ln, True)
                    self.__for.get_loop_body().add_fn_ln(fn_ln, True)
                    # this is additional info passed in
                    if add_local:
                        add_scope_context(self.__for, kargs)

            def loop(self, *args):
                for stmt in args:
                    if hasattr(stmt, "stmt"):
                        self.__for.add_stmt(stmt.stmt())
                    else:
                        self.__for.add_stmt(stmt)
                return self

            def stmt(self):
                return self.__for

        for_stmt = ForStatement(self)
        return for_stmt

    def assign(self, a, b, f_ln=None, **kargs):
        assert isinstance(a, _kratos.Var)
        try:
            stmt = a.assign(b)
        except _kratos.exception.VarException as ex:
            if f_ln is not None:
                print_src(self.filename, f_ln + self.ln - 1)
            # re-throw it
            raise ex
        if self.generator.debug:
            assert f_ln is not None
            stmt.add_fn_ln((self.filename, f_ln + self.ln - 1), True)
            if self.add_local:
                # obtain the previous call frame info
                __local = get_frame_local()
                add_scope_context(stmt, __local)
                # this is additional info passed in
                add_scope_context(stmt, kargs)
        return stmt

    def assert_(self, value, f_ln=None, **kargs):
        assert isinstance(value, (_kratos.Var, int))
        if isinstance(value, int):
            assert value == 0
            value = _kratos.constant(0, 1, False)
        stmt = _kratos.AssertValueStmt(value)
        if self.generator.debug:
            stmt.add_fn_ln((self.filename, f_ln + self.ln - 1), True)
            if self.add_local:
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
        super().__init__(generator, filename, ln, generator.debug)
        if generator is not None:
            self.__func = generator.internal_generator.function(func_name)

        self.__var_ordering = {}

    def input(self, var_name, width, is_signed=False) -> _kratos.Var:
        return self.__func.input(var_name, width, is_signed)

    def return_(self, value, f_ln=None):
        stmt = self.__func.return_stmt(value)
        if f_ln is not None:
            stmt.add_fn_ln((self.filename, f_ln + self.ln - 1), True)
        return stmt


def transform_block_comment(fn_body):
    for i in range(len(fn_body.body)):
        node = fn_body.body[i]
        if isinstance(node, ast.Expr) and isinstance(node.value, ast.Str):
            comment = node.value.s
            comment = comment.replace("\"", "").replace("'", "")
            node.value.s = comment
            fn_body.body[i] = ast.Expr(value=ast.Call(func=ast.Name(id="comment"), args=[node.value],
                                                      ctx=ast.Load(), keywords=[]))


def add_stmt_to_scope(fn_body):
    for i in range(len(fn_body.body)):
        node = fn_body.body[i]
        fn_body.body[i] = ast.Expr(
            value=ast.Call(func=ast.Attribute(value=ast.Name(id="scope", ctx=ast.Load()),
                                              attr="add_stmt", ctx=ast.Load()),
                           args=[node], keywords=[]))


def compute_target_node(for_nodes, new_nodes):
    result = {}
    for origin_node, values in for_nodes.items():
        if origin_node in new_nodes:
            target_node = new_nodes[origin_node]
            result[target_node] = values
    return result


def __ast_transform_blocks(generator, func_tree, fn_src, fn_name, scope, insert_self,
                           filename, func_ln,
                           transform_return=False, pre_locals=None, unroll_for=False,
                           apply_ssa=False):
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

    debug = generator.debug
    fn_body = func_tree.body[0]

    func_args = fn_body.args.args
    # add out scope to the arg list to capture all the statements
    func_args.append(ast.arg(arg="scope", annotation=None))

    if transform_return:
        return_visitor = ReturnNodeVisitor("scope", generator.debug)
        return_visitor.visit(fn_body)

    # change to block comment to comment_
    transform_block_comment(fn_body)

    # transform aug assign
    aug_assign_visitor = AugAssignNodeVisitor()
    fn_body = aug_assign_visitor.visit(fn_body)

    # if there is a need to apply ssa
    if apply_ssa:
        # only elaborate for
        for_visitor = StaticElaborationNodeForVisitor(generator, fn_src, scope, True, _locals,
                                                      _globals, filename, func_ln)
        fn_body = for_visitor.visit(fn_body)
        target_nodes = for_visitor.target_node
        fn_body = transform_always_comb_ssa(fn_body, generator, _locals)
    else:
        # static eval for loop and if statement
        for_visitor = StaticElaborationNodeForVisitor(generator, fn_src, scope, unroll_for, _locals,
                                                      _globals, filename, func_ln)
        fn_body = for_visitor.visit(fn_body)
        if_visitor = StaticElaborationNodeIfVisitor(generator, fn_src, scope, _locals, _globals, filename, func_ln)
        fn_body = if_visitor.visit(fn_body)
        target_nodes = compute_target_node(for_visitor.target_node, if_visitor.target_node)

    # transform assign
    assign_visitor = AssignNodeVisitor(generator, debug)
    fn_body = assign_visitor.visit(fn_body)
    ast.fix_missing_locations(fn_body)

    if apply_ssa:
        target_nodes = compute_target_node(target_nodes, assign_visitor.target_node)

    # transform the assert_ function to get fn_ln
    assert_visitor = AssertNodeVisitor(generator, debug)
    fn_body = assert_visitor.visit(fn_body)
    exception_visitor = ExceptionNodeVisitor(generator, debug)
    fn_body = exception_visitor.visit(fn_body)

    # transform event
    transform_event(fn_body, debug, filename, func_ln)

    # mark the local variables
    for node, (key, value) in target_nodes.items():
        assign_local_visitor = GenVarLocalVisitor(key, value, "scope")
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
                         args=args, keywords=[], ctx=ast.Load)
    func_tree.body.append(ast.Expr(value=call_node))
    return _locals, _globals


def inject_import_code(code_src):
    line1 = "import kratos"
    line2 = "from kratos import *"
    return "\n".join([line1, line2, code_src])


class AlwaysWrapper:
    def __init__(self, fn):
        self.fn = fn
        assert callable(fn)
        args = extract_arg_name_order_from_fn(fn)
        self.args = set()
        for name in args.values():
            if name != "self":
                self.args.add(name)

    def __call__(self, *args, **kwargs):
        raise SyntaxError("always block cannot be called normally. "
                          "Please do self.add_block()")


def filter_fn_args(fn_args):
    args = []
    for arg in fn_args:
        assert isinstance(arg, ast.arg), astor.to_source(arg) + " is not an argument"
        if arg.arg == "self":
            args.append(arg)
    return args


def transform_stmt_block(generator, fn, unroll_for=False, apply_ssa=False, fn_ln=None, kargs=None):
    if kargs is None:
        kargs = dict()
    env_kargs = dict()

    if callable(fn) or isinstance(fn, AlwaysWrapper):
        if isinstance(fn, AlwaysWrapper):
            assert len(kargs) >= len(fn.args), "missing arguments in function"
            for name in fn.args:
                assert name in kargs, name + " not found in function args"
                env_kargs[name] = kargs[name]
            fn = fn.fn
        else:
            import warnings
            warnings.warn("Bare function code as always block will be "
                          "deprecated soon. Please use @always_ff or "
                          "@always_comb", SyntaxWarning)
            print_src(get_fn(fn), get_ln(fn))
        fn_src = inspect.getsource(fn)
        fn_name = fn.__name__
        func_tree = ast.parse(textwrap.dedent(fn_src))
    else:
        assert isinstance(fn, ast.FunctionDef)
        # user directly passed in ast nodes
        assert fn_ln is not None
        fn_name = fn.name
        func_tree = ast.Module(body=[fn])
        fn_src = astor.to_source(fn)

    fn_body = func_tree.body[0]
    # needs debug
    debug = generator.debug
    store_local = debug and fn_ln is None
    filename = get_fn(fn) if fn_ln is None else fn_ln[0]
    ln = get_ln(fn) if fn_ln is None else fn_ln[1]

    # extract the sensitivity list from the decorator
    blk_type, sensitivity = extract_sensitivity_from_dec(fn_body.decorator_list, fn_name)
    # remove the decorator
    fn_body.decorator_list = []
    # check the function args. it should only has one self now
    func_args = filter_fn_args(fn_body.args.args)
    insert_self = len(func_args) == 1
    fn_body.args.args = func_args
    # creating the scope here
    scope = Scope(generator, filename, ln, store_local)

    apply_ssa = blk_type == StatementBlockType.Combinational and apply_ssa

    _locals, _globals = __ast_transform_blocks(generator, func_tree, fn_src,
                                               fn_name, scope,
                                               insert_self, filename, ln,
                                               unroll_for=unroll_for,
                                               apply_ssa=apply_ssa,
                                               pre_locals=env_kargs)

    src = astor.to_source(func_tree, pretty_source=__pretty_source)
    src = inject_import_code(src)
    code_obj = compile(src, "<ast>", "exec")

    # notice that this ln is an offset
    _locals.update({"_self": generator, "_scope": scope})
    # use user specified args
    _locals.update(env_kargs)
    for name in env_kargs:
        kargs.pop(name)
    _globals.update(_locals)
    exec(code_obj, _globals)
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
    filename = get_fn(fn)
    ln = get_ln(fn)
    scope = FuncScope(generator, fn_name, filename, ln)
    # add var creations
    arg_order = extract_arg_name_order_from_ast(func_args)
    var_body = declare_var_definition(arg_types, arg_order)
    var_src = astor.to_source(ast.Module(body=var_body))
    pre_locals = {"_scope": scope}
    var_code_obj = compile(var_src, "<ast>", "exec")
    exec(var_code_obj, pre_locals)
    _locals, _globals = __ast_transform_blocks(generator, func_tree, fn_src,
                                               fn_name, scope, insert_self,
                                               filename, ln,
                                               transform_return=True,
                                               pre_locals=pre_locals)

    src = astor.to_source(func_tree)
    src = inject_import_code(src)
    code_obj = compile(src, "<ast>", "exec")

    _locals.update({"_self": generator, "_scope": scope})
    _globals.update(_locals)
    exec(code_obj, _globals)
    stmts = scope.statements()
    return arg_order, stmts


def declare_var_definition(var_def, arg_order):
    body = []
    for idx, name in arg_order.items():
        width, is_signed = var_def[idx]
        body.append(ast.Assign(targets=[ast.Name(id=name)],
                               value=ast.Call(func=ast.Attribute(value=ast.Name(id="_scope", ctx=ast.Load()),
                                                                 attr="input", ctx=ast.Load()),
                                              args=[ast.Str(s=name), ast.Constant(value=width),
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
        return StatementBlockType.Combinational, []
    else:
        assert len(deco_list) == 1, "{0} is not called with multiple decorators blocks".format(fn_name)
        call_obj = deco_list[0]
        if isinstance(call_obj, ast.Call):
            call_name = call_obj.func.id
        else:
            assert isinstance(call_obj, ast.Name), "Unrecognized  function decorator {0}".format(call_obj)
            call_name = call_obj.id
        if call_name == "always_comb":
            return StatementBlockType.Combinational, []
        elif call_name == "initial":
            return StatementBlockType.Initial, []
        elif call_name == "always_latch":
            return StatementBlockType.Latch, []
        elif call_name == "final":
            return StatementBlockType.Final, []
        else:
            assert call_name == "always_ff", "Unrecognized function decorator {0}".format(call_name)
        blk_type = StatementBlockType.Sequential
        raw_sensitivity = call_obj.args
        result = []
        # TODO: fix me. the frame num calculation is a hack
        local = get_frame_local(4)
        for entry in raw_sensitivity:
            assert len(entry.elts) == 2
            edge_node, signal_name_node = entry.elts
            if isinstance(edge_node, ast.Name):
                edge_type = edge_node.id
            else:
                edge_type = edge_node.attr
            edge_type = edge_type.capitalize()
            if isinstance(signal_name_node, ast.Name):
                name = signal_name_node.id
                assert name in local, "{0} not found".format(name)
                n = eval(name, local)
                assert isinstance(n, _kratos.Var), "{0} is not a variable".format(name)
                signal_name = n
            elif isinstance(signal_name_node, ast.Attribute):
                # need to eval the actual name
                n = eval(astor.to_source(signal_name_node), local)
                assert isinstance(n, _kratos.Var), "{0} is not a variable".format(signal_name_node)
                signal_name = n
            else:
                signal_name = signal_name_node.s
            result.append((edge_type, signal_name))
        return blk_type, result


def get_ln(fn):
    info = inspect.getsourcelines(fn)
    return info[1]


def get_fn(fn):
    return os.path.abspath(inspect.getsourcefile(fn))
