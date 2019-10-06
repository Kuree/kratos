import sys
from typing import Union, List
import os
import math
import inspect
from _kratos import ConditionalExpr, get_fn_ln as _get_fn_ln
import _kratos
import enum
import functools
import operator


class CLIColors:
    HEADER = '\033[95m'
    OKBLUE = '\033[94m'
    OKGREEN = '\033[92m'
    WARNING = '\033[93m'
    FAIL = '\033[91m'
    ENDC = '\033[0m'
    BOLD = '\033[1m'
    UNDERLINE = '\033[4m'


def print_src(src, line_no: Union[List[int], int], offset: int = 1,
              code_range: int = 2):
    if os.path.isfile(src):
        with open(src) as f:
            lines = f.readlines()
    else:
        lines = src.split("\n")
    line_start = 0
    line_end = len(lines) - 1
    if isinstance(line_no, int):
        line_no = [line_no]
    for line in line_no:
        line_start = max(0, line - offset - code_range)
        line_end = min(len(lines) - 1, line - offset + code_range)
    # print a line
    print(CLIColors.OKBLUE + "-" * 80 + CLIColors.ENDC, file=sys.stderr)
    for idx in range(line_start, line_end + 1):
        if idx + offset in line_no:
            print(CLIColors.FAIL + ">", lines[idx] + CLIColors.ENDC,
                  file=sys.stderr)
        else:
            print(CLIColors.OKGREEN + " ", lines[idx] + CLIColors.ENDC,
                  file=sys.stderr)

    # print a line
    print(CLIColors.OKBLUE + "-" * 80 + CLIColors.ENDC, file=sys.stderr)


def clog2(x: int) -> int:
    if x == 0:
        return 0
    return int(math.ceil(math.log2(x)))


def flog2(x: int) -> int:
    if x == 0:
        return 0
    return int(math.floor(math.log2(x)))


# these are helper functions tp construct complex expressions
def reduce_or(*args):
    return functools.reduce(operator.or_, args)


def reduce_and(*args):
    return functools.reduce(operator.and_, args)


def reduce_add(*args):
    return functools.reduce(operator.add, args)


def reduce_mul(*args):
    return functools.reduce(operator.mul, args)


def concat(*args):
    expr = args[0].concat(args[1])
    for i in range(2, len(args)):
        expr = expr.concat(args[i])
    return expr


def get_fn_ln(depth: int = 2):
    # need to minus one before C++ is an extra frame
    return _get_fn_ln(depth + 1)


def zext(var, width):
    if var.width > width:
        raise ValueError("Cannot extend {0}".format(var))
    elif var.width == width:
        return var
    else:
        diff = width - var.width
        return const(0, diff, var.signed).concat(var)


def mux(cond, left, right):
    return ConditionalExpr(cond, left, right)


class VarCastType(enum.Enum):
    Signed = _kratos.VarCastType.Signed
    Unsigned = _kratos.VarCastType.Unsigned
    Clock = _kratos.VarCastType.Clock
    AsyncReset = _kratos.VarCastType.AsyncReset


def cast(var, cast_type):
    assert isinstance(var, _kratos.Var)
    return var.cast(cast_type.value)


def signed(var):
    return cast(var, VarCastType.Signed)


def unsigned(var):
    return cast(var, VarCastType.Unsigned)


def clock(var):
    return cast(var, VarCastType.Clock)


def async_reset(var):
    return cast(var, VarCastType.AsyncReset)


def const(value: int, width: int, is_signed: bool = False):
    return _kratos.constant(value, width, is_signed)


def comment(node, comment_str):
    if comment:
        node.comment = comment_str


# bit vector style syntax
class ConstConstructor:
    def __getitem__(self, width):
        class ConstWidth:
            def __call__(self, value, is_signed=False):
                return _kratos.constant(value, width, is_signed)
        return ConstWidth()


Const = ConstConstructor()

# also create an alias
ternary = mux
