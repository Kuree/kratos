from .pyast import transform_function_block, get_fn, get_ln, \
    extract_arg_name_order_from_fn
import inspect
import _kratos


class FunctionCall:
    cache_ordering = {}

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
            # set ordering
            func.set_port_ordering(args_order)
            self.cache_ordering[generator.name, fn_name] = args_order
            if generator.debug:
                fn, ln = get_fn(self.__fn), get_ln(self.__fn)
                for _, var_name in args_order.items():
                    port = func.get_port(var_name)
                    port.add_fn_ln((fn, ln + 1))
        else:
            args_order = self.cache_ordering[generator.name, fn_name]
        mapping = {}
        for idx, value in enumerate(args):
            var_name = args_order[idx]
            mapping[var_name] = value

        return generator.internal_generator.call(fn_name, mapping)


class DPIFunctionCall:
    cache_ordering = {}

    def __init__(self, width=0, is_pure=False, is_context=False):
        self.width = width
        if is_pure or is_context:
            assert is_pure ^ is_context, "DPI can be either pure or context"
        self.is_pure = is_pure
        self.is_context = is_context

    def __call__(self, fn):
        width = self.width
        is_pure = self.is_pure
        is_context = self.is_context

        class _DPIFunctionCall:
            def __init__(self):
                self.width = width
                self.__fn = fn

            def __call__(self, *args):
                fn_name = self.__fn.__name__
                cache = DPIFunctionCall.cache_ordering
                arg_types = []
                gen = None
                for arg in args:
                    arg_types.append((arg.width, arg.signed))
                    if gen is None:
                        gen = arg.generator
                if not gen.has_function(fn_name):
                    func = gen.dpi_function(fn_name)
                    func.set_return_width(self.width)
                    if is_pure:
                        func.set_is_pure(is_pure)
                    elif is_context:
                        func.set_is_context(is_context)
                else:
                    func = gen.get_function(fn_name)
                if fn_name not in DPIFunctionCall.cache_ordering:

                    assert gen is not None, "Unable to determine args"
                    args_order = extract_arg_name_order_from_fn(self.__fn)
                    lst = list(args_order.keys())
                    lst.sort()
                    for idx in lst:
                        name = args_order[idx]
                        w, signed = arg_types[idx]
                        func.input(name, w, signed)
                    func.set_port_ordering(args_order)
                    cache[fn_name] = args_order, gen, arg_types
                else:
                    args_order, gen, arg_types = cache[fn_name]
                mapping = {}
                for idx, value in enumerate(args):
                    var_name = args_order[idx]
                    mapping[var_name] = value

                return gen.call(fn_name, mapping)

        return _DPIFunctionCall()


def get_built_in(gen, func_name):
    class _BuiltinFunctionCall:
        def __init__(self):
            self.func_name = func_name
            self.gen = gen

        def __call__(self, *args):
            if not gen.has_function(self.func_name):
                gen.builtin_function(self.func_name)
            return gen.call(self.func_name, args)
    return _BuiltinFunctionCall()


# name alias
function = FunctionCall
dpi_function = DPIFunctionCall


def clear_context():
    FunctionCall.cache_ordering.clear()
    DPIFunctionCall.cache_ordering.clear()
