import _kratos
from .generator import Generator


def enable_runtime_debug(generator: Generator):
    # insert breakpoints
    table = _kratos.inject_debug_break_points(generator.internal_generator)
    _kratos.insert_debugger_setup(generator.internal_generator)
    return table

