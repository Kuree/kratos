import sys
from typing import Union, List
import os
import math
from _kratos import mux as _mux, get_fn_ln, comment as _comment, \
    create_stub as _create_stub
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
                  file=sys.stderr, end="")
        else:
            print(CLIColors.OKGREEN + " ", lines[idx] + CLIColors.ENDC,
                  file=sys.stderr, end="")

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


def ext(var, target_width):
    return var.extend(target_width)


def mux(cond, left, right):
    return _mux(cond, left, right)


class VarCastType(enum.Enum):
    Signed = _kratos.VarCastType.Signed
    Unsigned = _kratos.VarCastType.Unsigned
    Clock = _kratos.VarCastType.Clock
    AsyncReset = _kratos.VarCastType.AsyncReset
    Enum = _kratos.VarCastType.Enum


def cast(var, cast_type, **kargs):
    assert isinstance(var, _kratos.Var)
    _v = var.cast(cast_type.value)
    for k, v in kargs.items():
        setattr(_v, k, v)
    return _v


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


def comment(comment_str):
    return _comment(comment_str)


def create_stub(generator, flatten_array=False, verilog95_def=False,
                filename=""):
    s = _create_stub(generator.internal_generator, flatten_array, verilog95_def)
    if filename:
        with open(filename) as f:
            f.write(s)
    return s


def max_value(values):
    s = set()
    for x in values.values():
        s.add(x)
    return max(s)


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


# helper function to interface with magma
def to_magma(kratos_inst, **kargs):
    import magma as m
    from kratos import verilog
    circ_name = kratos_inst.name
    internal_gen = kratos_inst.internal_generator
    ports = internal_gen.get_port_names()
    io = []
    for port_name in ports:
        io.append(port_name)
        port = kratos_inst.ports[port_name]
        width = port.width
        size = port.size
        dir_ = m.In if port.port_direction == _kratos.PortDirection.In \
            else m.Out
        type_ = port.port_type
        signed = port.signed
        if type_ == _kratos.PortType.Clock:
            type_value = m.Clock
        elif type_ == _kratos.PortType.AsyncReset:
            if port.active_high or port.active_high is None:
                type_value = m.AsyncReset
            else:
                type_value = m.AsyncResetN
        else:
            # normal logic/wire, loop through the ndarray to construct
            # magma arrays, notice it's in reversed order
            type_value = m.Bits[width] if not signed else m.SInt[width]
            for idx, array_width in enumerate(reversed(size)):
                type_value = m.Array[array_width, type_value]
        io.append(dir_(type_value))

    defn = m.DefineCircuit(circ_name, *io, kratos=kratos_inst)
    os.makedirs(".magma", exist_ok=True)
    filename = f".magma/{circ_name}-kratos.sv"
    # multiple definition inside the kratos instance is taken care of by
    # the track definition flag
    verilog(kratos_inst, filename=filename, track_generated_definition=True,
            **kargs)
    with open(filename, 'r') as f:
        defn.verilogFile = f.read()
    m.EndCircuit()
    return defn
