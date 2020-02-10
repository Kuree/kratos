import _kratos
from .generator import Generator
from typing import List


def extract_symbol_table(generator: Generator):
    # this has to be run after the unification pass
    # if you are using kratos from a different system
    # this function serves a reference implementation of how to obtain
    # data python the python side
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
                # since this is python, we use self to refer to itself
                name = "self." + name
                if isinstance(var, _kratos.Var):
                    # I think bundle -> packed struct will not work here
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
    _kratos.inject_instance_ids(generator.internal_generator)
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
    dump_debug_database(top, top_name, filename)
