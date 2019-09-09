import _kratos
from .generator import Generator


def extract_symbol_table(generator: Generator):
    # this has to be run after the unification pass
    from queue import Queue
    table = {}
    gen_queue = Queue()
    gen_queue.put(generator)
    while not gen_queue.empty():
        gen: Generator = gen_queue.get()
        if gen.debug:
            # introspect the variable tables
            entry = {}
            variables = vars(gen)
            for name, var in variables.items():
                if isinstance(var, _kratos.Var):
                    # I think bundle -> packed struct will not work here
                    if isinstance(var, (_kratos.PortPacked, _kratos.VarPacked,
                                        _kratos.PortBundleRef)):
                        member_names = var.member_names()
                        for var_name in member_names:
                            var = var[var_name]
                    entry[name] = var.handle_name()
            table[gen] = entry
            # push all the child generator to the queue
            children = gen.child_generator()
            for _, child in children.items():
                if child.internal_generator.parent_generator() is not None:
                    # it could be removed
                    gen_queue.put(child)
    return table


def enable_runtime_debug(generator: Generator):
    # insert breakpoints
    _kratos.inject_debug_break_points(generator.internal_generator)


def dump_debug_database(generator: Generator, top_name: str, filename: str):
    db = _kratos.DebugDataBase(top_name)
    raw_symbol_table = extract_symbol_table(generator)
    db.set_break_points(generator.internal_generator)
    # convert raw table to internal generator
    symbol_table = {}
    for gen, value in raw_symbol_table.items():
        symbol_table[gen.internal_generator] = value
    db.set_variable_mapping(symbol_table)
    db.save_database(filename)
