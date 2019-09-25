import _kratos
from .generator import Generator


def extract_symbol_table(generator: Generator):
    # this has to be run after the unification pass
    from queue import Queue
    gen_table = {}
    self_table = {}
    gen_queue = Queue()
    gen_queue.put(generator)
    while not gen_queue.empty():
        gen: Generator = gen_queue.get()
        if gen.debug:
            # introspect the variable tables
            gen_entry = {}
            self_entry = {}
            variables = vars(gen)
            for name, var in variables.items():
                if isinstance(var, _kratos.Var):
                    # I think bundle -> packed struct will not work here
                    if isinstance(var, (_kratos.PortPacked, _kratos.VarPacked,
                                        _kratos.PortBundleRef)):
                        member_names = var.member_names()
                        for var_name in member_names:
                            var = var[var_name]
                    gen_entry[name] = var
                elif isinstance(var, (bool, int, str)):
                    self_entry[name] = str(var)
            gen_table[gen] = gen_entry
            self_table[gen] = self_entry
            # push all the child generator to the queue
            children = gen.child_generator()
            for _, child in children.items():
                if child.internal_generator.parent_generator() is not None:
                    # it could be removed
                    gen_queue.put(child)
    return gen_table, self_table


def enable_runtime_debug(generator: Generator):
    # insert breakpoints
    _kratos.inject_debug_break_points(generator.internal_generator)


def dump_debug_database(generator: Generator, top_name: str, filename: str):
    db = _kratos.DebugDataBase(top_name)
    raw_symbol_table, raw_self_table = extract_symbol_table(generator)
    db.set_break_points(generator.internal_generator)
    # convert raw table to internal generator
    symbol_table = {}
    self_table = {}
    for gen, value in raw_symbol_table.items():
        symbol_table[gen.internal_generator] = value
    for gen, value in raw_self_table.items():
        self_table[gen.internal_generator] = value
    db.set_variable_mapping(symbol_table)
    # store the self table
    db.set_generator_variable(self_table)
    # insert other metadata information
    db.set_generator_connection(generator.internal_generator)
    db.set_generator_hierarchy(generator.internal_generator)
    db.set_stmt_context(generator.internal_generator)
    db.save_database(filename)
