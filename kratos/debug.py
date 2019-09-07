import _kratos
from .generator import Generator
from .passes import extract_symbol_table


def enable_runtime_debug(generator: Generator):
    # insert breakpoints
    table = _kratos.inject_debug_break_points(generator.internal_generator)
    _kratos.insert_debugger_setup(generator.internal_generator)
    return table


def dump_debug_database(generator: Generator, break_points, filename: str):
    raw_table = extract_symbol_table(generator)
