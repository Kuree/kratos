import _kratos
from .generator import Generator
from typing import List


def extract_symbol_table(generator: Generator):
    # this has to be run after the unification pass
    # if you are using kratos from a different system
    # this function serves a reference implementation of how to obtain
    # data from the python side
    from queue import Queue
    var_table = {}
    str_table = {}
    gen_queue = Queue()
    gen_queue.put(generator)
    while not gen_queue.empty():
        gen: Generator = gen_queue.get()
        if gen.debug:
            # introspect the variable tables
            var_entry = {}
            str_entry = {}
            variables = vars(gen)
            for name, var in variables.items():
                # since this is python, we use self to refer to itself
                name = "self." + name
                if isinstance(var, _kratos.Var):
                    # I think bundle -> packed struct will not work here
                    var_entry[name] = var
                elif isinstance(var, (bool, int, str)):
                    str_entry[name] = str(var)
            var_table[gen] = var_entry
            str_table[gen] = str_entry
        # push all the child generator to the queue
        children = gen.child_generator()
        for _, child in children.items():
            if child.internal_generator.parent_generator() is not None:
                # it could be removed
                gen_queue.put(child)
    return var_table, str_table


def enable_runtime_debug(generator: Generator):
    # insert breakpoints
    _kratos.inject_instance_ids(generator.internal_generator)
    _kratos.inject_debug_break_points(generator.internal_generator)


def dump_debug_database(generator: Generator, filename: str):
    db = _kratos.DebugDataBase()
    raw_symbol_table, raw_str_table = extract_symbol_table(generator)
    db.set_break_points(generator.internal_generator)
    # convert raw table to internal generator
    symbol_table = {}
    str_table = {}
    for gen, value in raw_symbol_table.items():
        symbol_table[gen.internal_generator] = value
    for gen, value in raw_str_table.items():
        str_table[gen.internal_generator] = value
    db.set_variable_mapping(symbol_table)
    # store the string values
    db.set_variable_mapping(str_table)
    # insert other metadata information
    db.set_stmt_context(generator.internal_generator)
    db.save_database(filename)


def dump_external_database(generators: List[Generator], top_name: str, filename: str):
    # create a dummy generator at the top
    top = Generator(top_name, True)
    for gen in generators:
        # remove top name with given one
        instance_name = gen.instance_name.split(".")[1:]
        if instance_name:
            top.add_child(".".join(instance_name), gen)
        else:
            # only has one generator
            assert len(generators) == 1
            gen.instance_name = top_name
            top = gen
    dump_debug_database(top, filename)
