import sys
from typing import Union, List
import os
import math
from _kratos import mux as _mux, comment as _comment, \
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


def clog2(x: Union[int, _kratos.Var]) -> Union[int, _kratos.Var]:
    if isinstance(x, _kratos.Var):
        from kratos.func import get_built_in
        fn = get_built_in(x.generator, "clog2")
        return fn(x)
    else:
        if x == 0:
            return 0
        return int(math.ceil(math.log2(x)))


def flog2(x: int) -> int:
    if x == 0:
        return 0
    return int(math.floor(math.log2(x)))


# these are helper functions tp construct complex expressions
def __reduce(func, args):
    r = functools.reduce(func, args)
    if isinstance(r, (list, tuple)) and len(r) == 1:
        return r[0]
    return r


def reduce_or(*args):
    return __reduce(operator.or_, args)


def reduce_and(*args):
    return __reduce(operator.and_, args)


def reduce_add(*args):
    return __reduce(operator.add, args)


def reduce_mul(*args):
    return __reduce(operator.mul, args)


def concat(*args):
    def _concat(a, b):
        return a.concat(b)
    return __reduce(_concat, args)


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
    Resize = _kratos.VarCastType.Resize
    ClockEn = _kratos.VarCastType.ClockEnable


def cast(var, cast_type, **kargs):
    assert isinstance(var, _kratos.Var)
    _v = var.cast(cast_type.value)
    for k, v in kargs.items():
        setattr(_v, k, v)
    return _v


def signed(var):
    return cast(var, VarCastType.Signed)


def resize(var, target_width):
    if isinstance(var, int):
        return const(var, target_width, var <= 0)
    return cast(var, VarCastType.Resize, target_width=target_width)


def unsigned(var):
    return cast(var, VarCastType.Unsigned)


def clock(var):
    return cast(var, VarCastType.Clock)


def clock_en(var):
    return cast(var, VarCastType.ClockEn)


def async_reset(var):
    return cast(var, VarCastType.AsyncReset)


def const(value: int, width: int, is_signed: bool = False):
    assert isinstance(value, int)
    return _kratos.constant(value, width, is_signed)


def comment(comment_str):
    return _comment(comment_str)


def create_stub(generator, filename=""):
    s = _create_stub(generator.internal_generator)
    if filename:
        with open(filename) as f:
            f.write(s)
    return s


def max_value(values):
    s = set()
    for x in values.values():
        s.add(x)
    return max(s)


def enable_multi_generate():
    # need to enable if verilog() function is called multiple times
    # and all of them will go to the same RTL code
    from kratos import Generator
    Generator.get_context().track_generated = True


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
def to_magma(kratos_inst, flatten_array=False, top_name=None, **kargs):  # pragma: no cover
    import magma as m
    from kratos import verilog, Generator
    from _kratos import create_wrapper_flatten
    if flatten_array:
        inst = create_wrapper_flatten(kratos_inst.internal_generator,
                                      kratos_inst.name + "_W")
        inst = Generator(kratos_inst.name,
                         internal_generator=inst)
        # only add the child, nothing more
        inst.add_child(kratos_inst.instance_name, kratos_inst, python_only=True)
        kratos_inst = inst
        if top_name is not None:
            kratos_inst.instance_name = top_name
    circ_name = kratos_inst.name
    internal_gen = kratos_inst.internal_generator
    ports = internal_gen.get_port_names()
    io = {}
    for port_name in ports:
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
            if len(size) > 1 or size[0] > 1:
                for idx, array_width in enumerate(reversed(size)):
                    type_value = m.Array[array_width, type_value]
        io[port_name] = (dir_(type_value))
    magma_io = m.IO(**io)

    class _Definition(m.Circuit):
        name = circ_name
        io = magma_io
        kratos = kratos_inst
    os.makedirs(".magma", exist_ok=True)
    filename = f".magma/{circ_name}-kratos.sv"
    enable_multi_generate()
    # multiple definition inside the kratos instance is taken care of by
    # the track definition flag
    verilog(kratos_inst, filename=filename, track_generated_definition=True,
            **kargs)
    with open(filename, 'r') as f:
        _Definition.verilogFile = f.read()

    return _Definition
