from .pyast import FuncScope, transform_function_block
import inspect


# for type checking tools
func_scope = FuncScope(None, "", "", 0)


class FunctionCall:
    __cache_mapping = {}

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
            args_order, stmts = transform_function_block(generator, self.__fn)
            mapping = {}
            for idx, value in enumerate(args):
                var_name, width, signed = args_order[idx]
                mapping[var_name] = value
            # add statements
            func = generator.internal_generator.get_function(fn_name)
            for stmt in stmts:
                func.add_stmt(stmt)
            self.__cache_mapping[generator.name, fn_name] = mapping
        else:
            mapping = self.__cache_mapping[generator.name, fn_name]
        return generator.internal_generator.call(fn_name, mapping)


# name alias
function = FunctionCall
