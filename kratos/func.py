from .pyast import FuncScope, transform_function_block
import inspect
import _kratos


# for type checking tools
func_scope = FuncScope(None, "", "", 0)


class FunctionCall:
    __cache_ordering = {}

    def __init__(self, fn):
        self.__fn = fn

    def __call__(self, *args):
        # notice that we need to get self from the upper locals
        f = inspect.currentframe().f_back
        if "self" not in f.f_locals:
            raise Exception("Unable to find self from local scope")
        generator = f.f_locals["self"]
        fn_name = self.__fn.__name__
        if not generator.internal_generator.has_function(fn_name):
            # we infer the types. notice that we don't have names here
            arg_types = []
            for arg in args:
                arg_types.append((arg.width, arg.signed))
            args_order, stmts = transform_function_block(generator, self.__fn,
                                                         arg_types)

            # add statements
            func = generator.internal_generator.get_function(fn_name)
            for stmt in stmts:
                if not isinstance(stmt, _kratos.Stmt):
                    stmt = stmt.stmt()
                func.add_stmt(stmt)
            self.__cache_ordering[generator.name, fn_name] = args_order
        else:
            args_order = self.__cache_ordering[generator.name, fn_name]
        mapping = {}
        for idx, value in enumerate(args):
            var_name = args_order[idx]
            mapping[var_name] = value

        return generator.internal_generator.call(fn_name, mapping)


# name alias
function = FunctionCall
