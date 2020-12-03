import enum
from .pyast import transform_stmt_block, CodeBlockType, add_scope_context, \
    get_frame_local, AlwaysWrapper
from .util import clog2, max_value, cast, VarCastType
from .stmts import if_, switch_, IfStmt, SwitchStmt
from .ports import PortBundle
from .fsm import FSM
from .interface import InterfaceWrapper
import _kratos
from _kratos import get_fn_ln
from typing import List, Dict, Union, Tuple

__GLOBAL_DEBUG = False


def set_global_debug(value: bool):
    global __GLOBAL_DEBUG
    assert isinstance(value, bool)
    __GLOBAL_DEBUG = value


def get_global_debug():
    return __GLOBAL_DEBUG


# this is a wrapper python class to interface with the underlying python
# binding
class PortDirection(enum.Enum):
    In = _kratos.PortDirection.In
    Out = _kratos.PortDirection.Out
    InOut = _kratos.PortDirection.InOut


class PortType(enum.Enum):
    Data = _kratos.PortType.Data
    Clock = _kratos.PortType.Clock
    AsyncReset = _kratos.PortType.AsyncReset
    ClockEnable = _kratos.PortType.ClockEnable
    Reset = _kratos.PortType.Reset


class BlockEdgeType(enum.Enum):
    Posedge = _kratos.BlockEdgeType.Posedge
    Negedge = _kratos.BlockEdgeType.Negedge


class StatementBlockType(enum.Enum):
    Combinational = _kratos.StatementBlockType.Combinational
    Sequential = _kratos.StatementBlockType.Sequential
    Initial = _kratos.StatementBlockType.Initial
    Latch = _kratos.StatementBlockType.Latch


class CodeBlock:
    def __init__(self, generator, block_type: StatementBlockType,
                 debug_frame_depth):
        self.block_type = block_type
        self._generator = generator
        if block_type == StatementBlockType.Combinational:
            self._block = generator.internal_generator.combinational()
        elif block_type == StatementBlockType.Initial:
            self._block = generator.internal_generator.initial()
        elif block_type == StatementBlockType.Latch:
            self._block = generator.internal_generator.latch()
        else:
            self._block = generator.internal_generator.sequential()

        if generator.debug:
            fn, ln = get_fn_ln(debug_frame_depth)
            self._block.add_fn_ln((fn, ln))

    def add_stmt(self, stmt, add_fn_ln: bool = True, depth=2):
        if hasattr(stmt, "stmt"):
            self._block.add_stmt(stmt.stmt())
        else:
            self._block.add_stmt(stmt)
        if add_fn_ln and self._generator.debug:
            info = get_fn_ln(depth)
            stmt.add_fn_ln(info)
            add_scope_context(stmt, get_frame_local(depth))

    def remove_stmt(self, stmt):
        if hasattr(stmt, "stmt"):
            self._block.remove_stmt(stmt.stmt())
        else:
            self._block.remove_stmt(stmt)

    def stmt(self):
        return self._block

    def if_(self, predicate: _kratos.Var) -> IfStmt:
        stmt = if_(predicate)
        self.add_stmt(stmt.stmt(), depth=3)
        return stmt

    def switch_(self, predicate: _kratos.Var) -> SwitchStmt:
        stmt = switch_(predicate)
        self.add_stmt(stmt.stmt(), depth=3)
        return stmt

    def __getitem__(self, item):
        return self._block[item]

    def add_attribute(self, attr):
        self._block.add_attribute(attr)


class SequentialCodeBlock(CodeBlock):
    def __init__(self, generator, sensitivity_list,
                 debug_frame_depth: int = 4):
        super().__init__(generator, StatementBlockType.Sequential,
                         debug_frame_depth)
        for cond, var in sensitivity_list:
            assert isinstance(cond, BlockEdgeType)
            assert isinstance(var, _kratos.Var)
            self._block.add_condition([cond.value, var])


class CombinationalCodeBlock(CodeBlock):
    def __init__(self, generator,
                 debug_frame_depth: int = 4):
        super().__init__(generator, StatementBlockType.Combinational,
                         debug_frame_depth)


class InitialCodeBlock(CodeBlock):
    def __init__(self, generator,
                 debug_frame_depth: int = 4):
        super().__init__(generator, StatementBlockType.Initial,
                         debug_frame_depth)


class LatchCodeBlock(CodeBlock):
    def __init__(self, generator,
                 debug_frame_depth: int = 4):
        super().__init__(generator, StatementBlockType.Latch,
                         debug_frame_depth)


def enum(name, definition, width=None):
    if isinstance(name, _kratos.Var):
        assert isinstance(definition, _kratos.Enum)
        v = cast(name, VarCastType.Enum, enum_type=definition)
        return v
    if isinstance(definition, (list, tuple)):
        defs = {}
        for n in definition:
            if isinstance(n, (list, tuple)):
                defs[n[0]] = n[1]
            else:
                defs[n] = len(defs)
        definition = defs
    if width is None:
        width = clog2(max_value(definition) + 1)
    return Generator.get_context().enum(name, definition, width)


def has_enum(name):
    return Generator.get_context().has_enum(name)


class PortProxy:
    def __init__(self, generator: "Generator"):
        self.__generator = generator

    def __getitem__(self, key):
        if self.__generator.internal_generator.has_port_bundle(key):
            p = self.__generator.internal_generator.get_bundle_ref(key)
        else:
            p = self.__generator.internal_generator.get_port(key)
        if p is None:
            raise AttributeError("{0} doesn't exist".format(key))
        return p

    def __getattr__(self, key):
        return self[key]

    def __contains__(self, key):
        return self.__generator.internal_generator.has_port(key)

    def __iter__(self):
        return self.__generator.internal_generator.ports_iter()


class ParamProxy:
    def __init__(self, generator: "Generator"):
        self.__generator = generator

    def __getitem__(self, key):
        p = self.__generator.internal_generator.get_param(key)
        if p is None:
            raise AttributeError("{0} doesn't exist".format(key))
        return p

    def __getattr__(self, key):
        return self[key]

    def __contains__(self, item):
        return self.__generator.internal_generator.get_param(item) is not None

    def __iter__(self):
        return self.__generator.internal_generator.param_iter()


class VarProxy:
    def __init__(self, generator):
        self.__generator = generator.internal_generator

    def __getitem__(self, key):
        v = self.__generator.get_var(key)
        if v is None:
            raise AttributeError("{0} doesn't exist".format(key))
        return v

    def __getattr__(self, key):
        return self[key]

    def __contains__(self, key):
        return self.__generator.has_var(key)

    def __iter__(self):
        return self.__generator.vars_iter()


class InterfaceProxy:
    def __init__(self, generator):
        self.__generator = generator.internal_generator

    def __getitem__(self, item):
        return self.__generator.get_interface(item)

    def __getattr__(self, key):
        return self[key]


class GeneratorMeta(type):
    def __init__(cls, name, bases, attrs):
        super().__init__(name, bases, attrs)
        cls._cache = {}


class Generator(metaclass=GeneratorMeta):
    __context = _kratos.Context()
    __inspect_frame_depth: int = 2

    def __init__(self, name: str, debug: bool = False, is_clone: bool = False,
                 internal_generator=None):
        """
        Base class for all generators
        :param name: generator name
        :param debug: set to ``True`` if you want to collect debug information
        on this particular generator
        :param is_clone: mark whether the generator is a clone or not.
        :param internal_generator: native C++ handle
        """
        # for initialization
        self.__cached_initialization = []

        if internal_generator is not None:
            assert isinstance(internal_generator, _kratos.Generator)
            self.__generator = internal_generator
        else:
            if not is_clone and len(name) > 0:
                self.__generator = self.__context.generator(name)
            else:
                self.__generator = self.__context.empty_generator()
                self.__generator.is_cloned = True
            self.__set_generator_name(name)

        self.__child_generator: Dict[str, Generator] = {}

        if not debug:
            self.debug = get_global_debug()
        else:
            self.debug = debug

        if debug:
            fn, ln = get_fn_ln(Generator.__inspect_frame_depth)
            self.__generator.add_fn_ln((fn, ln))

        # gemstone style port interface
        self.ports = PortProxy(self)
        self.params = ParamProxy(self)
        self.vars = VarProxy(self)
        self.interfaces = InterfaceProxy(self)

        self.__def_instance = self

        # helper function data
        self.__reg_next_stmt = {}
        self.__reg_init_stmt = {}
        self.__reg_en_stmt = {}

        # meta data
        self.__stmt_label_mapping = {}
        self.__parent = None

    def __getitem__(self, instance_name: str):
        """
        Get child instance through instance name
        :param instance_name: instance name of the child generator
        :return: Child generator
        """
        assert instance_name in self.__child_generator, \
            "{0} does not exist in {1}".format(instance_name,
                                               self.instance_name)
        return self.__child_generator[instance_name]

    @property
    def def_instance(self):
        """
        The definition instance of this generator. It can be itself or
        the clone reference
        :return: definition instance
        """
        return self.__def_instance

    @property
    def name(self):
        """
        Generator name usually corresponds to the name of the module. However,
        if unification happens, its verilog name will change.
        :return: The name of the generator
        """
        return self.__generator.name

    @name.setter
    def name(self, name: str):
        self.__generator.name = name

    @property
    def instance_name(self):
        """
        Instance name of a generator. It has to be unique within a parent
        generator.
        :return: the instance name of the generator
        """
        return self.__generator.instance_name

    @instance_name.setter
    def instance_name(self, name: str):
        if self.__parent is not None:
            old_name = self.__generator.instance_name
            ref = self.__parent.__child_generator.pop(old_name)
            assert ref == self
            self.__parent.__child_generator[name] = self
        self.__generator.instance_name = name

    @property
    def is_stub(self):
        """
        If a generator is mark as a stub, most of the passes won't touch it
        and it's the user's responsibility to keep track of it. Kratos will
        attempt to zero out the stub outputs.
        :return: ``True`` if it's a stub
        """
        return self.__generator.is_stub()

    @is_stub.setter
    def is_stub(self, value: bool):
        self.__generator.set_is_stub(value)

    @property
    def external(self):
        """
        External module typically is used when importing external verilog files.
        If set from user, all the passes and code gen will skip this generator
        definition.
        :return: ``True`` if it's an external generator
        """
        return self.__generator.external()

    @external.setter
    def external(self, value: bool):
        self.__generator.set_external(value)

    @property
    def debug(self):
        return self.__generator.debug

    @debug.setter
    def debug(self, value):
        self.__generator.debug = value

    @property
    def is_cloned(self):
        return self.__generator.is_cloned

    @property
    def stmts_count(self):
        return self.__generator.stmts_count()

    def get_stmt_by_index(self, index):
        return self.__generator.get_stmt(index)

    def var(self, name: str, width: Union[int, _kratos.Param, _kratos.Enum,
                                          _kratos.PackedStruct],
            is_signed: bool = False, size: Union[int, Union[List, Tuple]] = 1,
            packed: bool = False, explicit_array: bool = False) -> _kratos.Var:
        size, params = self.__filter_size(size)
        if isinstance(width, _kratos.Enum):
            v = self.__generator.enum_var(name, width)
        elif isinstance(width, _kratos.PackedStruct):
            v = self.__generator.var_packed(name, width, size)
        else:
            v = self.__generator.var(name, width, size, is_signed)
        if self.debug:
            v.add_fn_ln(get_fn_ln())
        if not isinstance(width, _kratos.PackedStruct):
            v.is_packed = packed
            v.explicit_array = explicit_array
        self.__set_var_size(v, params)
        return v

    def combinational(self):
        if self.is_cloned:
            self.__cached_initialization.append((self.combinational, []))
            return
        return CombinationalCodeBlock(self, 3)

    def sequential(self, *sensitivity_list: Tuple[BlockEdgeType,
                                                  _kratos.Var]):
        if self.is_cloned:
            self.__cached_initialization.append((self.sequential,
                                                 [sensitivity_list]))
            return
        return SequentialCodeBlock(self, sensitivity_list, 3)

    @staticmethod
    def __filter_size(size):
        if isinstance(size, int):
            return size, {}
        else:
            if isinstance(size, _kratos.Var):
                return 1, {0: size}
            assert isinstance(size, (list, tuple))
            result = []
            params = {}
            for i in range(len(size)):
                var = size[i]
                if isinstance(var, _kratos.Var):
                    params[i] = var
                    var = 1
                result.append(var)
            return result, params

    @staticmethod
    def __set_var_size(var, params: Dict[int, _kratos.Var]):
        for index, param in params.items():
            var.set_size_param(index, param)

    def port(self, name: str, width: Union[int, _kratos.Param, _kratos.Enum],
             direction: PortDirection,
             port_type: PortType = PortType.Data,
             is_signed: bool = False, size: Union[int, Union[List, Tuple]] = 1,
             packed: bool = False,
             explicit_array: bool = False) -> _kratos.Port:
        size, params = self.__filter_size(size)
        if isinstance(width, _kratos.Enum):
            p = self.__generator.port(direction.value, name, width)
        else:
            p = self.__generator.port(direction.value, name, width, size,
                                      port_type.value, is_signed)
        if self.debug:
            p.add_fn_ln(get_fn_ln())
        p.is_packed = packed
        p.explicit_array = explicit_array
        self.__set_var_size(p, params)
        return p

    def port_from_def(self, port: _kratos.Port, name="", check_param: bool = True):
        if name:
            return self.__generator.port(port, name, check_param)
        else:
            return self.__generator.port(port, check_param)

    def var_from_def(self, var: _kratos.Var, name):
        return self.__generator.var(var, name)

    def param_from_def(self, param: _kratos.Param, name=None):
        return self.__generator.parameter(param, name)

    def input(self, name, width: Union[int, _kratos.Param, _kratos.Enum,
                                       _kratos.PackedStruct],
              port_type: PortType = PortType.Data,
              is_signed: bool = False, size: Union[int, Union[List, Tuple]] = 1,
              packed: bool = False,
              explicit_array: bool = False) -> _kratos.Port:
        size, params = self.__filter_size(size)
        if isinstance(width, _kratos.Enum):
            p = self.__generator.port(PortDirection.In.value, name, width)
        elif isinstance(width, _kratos.PackedStruct):
            p = self.__generator.port_packed(PortDirection.In.value, name,
                                             width, size)
        else:
            p = self.__generator.port(PortDirection.In.value, name, width, size,
                                      port_type.value, is_signed)
        if self.debug:
            p.add_fn_ln(get_fn_ln())
        if not isinstance(width, _kratos.PackedStruct):
            p.is_packed = packed
            p.explicit_array = explicit_array
        self.__set_var_size(p, params)
        return p

    def clock(self, name, is_input=True):
        direction = PortDirection.In if is_input else PortDirection.Out
        p = self.__generator.port(direction.value, name, 1, 1,
                                  PortType.Clock.value, False)
        if self.debug:
            p.add_fn_ln(get_fn_ln())
        return p

    def clock_en(self, name, is_input=True):
        direction = PortDirection.In if is_input else PortDirection.Out
        p = self.__generator.port(direction.value, name, 1, 1,
                                  PortType.ClockEnable.value, False)
        if self.debug:
            p.add_fn_ln(get_fn_ln())
        return p

    def reset(self, name, is_input=True, is_async=True, active_high=None):
        direction = PortDirection.In if is_input else PortDirection.Out
        reset = PortType.AsyncReset if is_async else PortType.Reset
        p = self.__generator.port(direction.value, name, 1, 1, reset.value,
                                  False)
        if self.debug:
            p.add_fn_ln(get_fn_ln())
        if active_high is not None:
            p.active_high = active_high
        return p

    def output(self, name, width: Union[int, _kratos.Param, _kratos.Enum,
                                        _kratos.PackedStruct],
               port_type: PortType = PortType.Data,
               is_signed: bool = False,
               size: Union[int, Union[List, Tuple]] = 1, packed: bool = False,
               explicit_array: bool = False) -> _kratos.Port:
        size, params = self.__filter_size(size)
        if isinstance(width, _kratos.Enum):
            p = self.__generator.port(PortDirection.Out.value, name, width)
        elif isinstance(width, _kratos.PackedStruct):
            p = self.__generator.port_packed(PortDirection.Out.value, name,
                                             width, size)
        else:
            p = self.__generator.port(PortDirection.Out.value, name, width,
                                      size,
                                      port_type.value, is_signed)
        if self.debug:
            p.add_fn_ln(get_fn_ln())
        if not isinstance(width, _kratos.PackedStruct):
            p.is_packed = packed
            p.explicit_array = explicit_array
        self.__set_var_size(p, params)
        return p

    def var_packed(self, name: str, struct_packed: _kratos.PortPackedStruct):
        v = self.__generator.var_packed(name, struct_packed)
        if self.debug:
            v.add_fn_ln(get_fn_ln())
        return v

    def port_bundle(self, bundle_name, bundle: PortBundle):
        assert isinstance(bundle, PortBundle)
        if self.debug:
            return self.__generator.add_bundle_port_def(bundle_name,
                                                        bundle.definition,
                                                        get_fn_ln())
        else:
            return self.__generator.add_bundle_port_def(bundle_name,
                                                        bundle.definition)

    def parameter(self, name: str, width: int = 32, value=None,
                  is_signed: bool = False, initial_value=None,
                  is_raw_type: bool = False) -> _kratos.Param:
        if is_raw_type:
            param = self.__generator.parameter(name)
        else:
            if isinstance(width, _kratos.Enum):
                param = self.__generator.parameter(name, width)
            else:
                param = self.__generator.parameter(name, width, is_signed)
        if value is not None:
            param.value = value
        if initial_value is not None:
            param.initial_value = initial_value
            # set value as well
            if value is None:
                param.value = initial_value
        if self.debug:
            fn, ln = get_fn_ln()
            param.add_fn_ln((fn, ln))
        return param

    # alias
    param = parameter

    def enum(self, name: str, values: Dict[str, int], width=None):
        if width is None:
            width = clog2(max_value(values) + 1)
        return self.__generator.enum(name, values, width)

    def enum_var(self, name: str, def_: _kratos.Enum):
        return self.__generator.enum_var(name, def_)

    def interface(self, interface, name, is_port: bool = False):
        return InterfaceWrapper(
            self.__generator.interface(interface, name, is_port))

    def get_var(self, name):
        return self.__generator.get_var(name)

    def remove_port(self, port_name):
        assert self.__generator.has_port(port_name)
        self.__generator.remove_port(port_name)

    def remove_var(self, var_name):
        assert self.__generator.has_var(var_name)
        self.__generator.remove_var(var_name)

    def add_attribute(self, attr):
        self.__generator.add_attribute(attr)

    def find_attribute(self, func):
        return self.__generator.find_attribute(func)

    @property
    def internal_generator(self):
        return self.__generator

    def add_always(self, fn, comment="", label="", sensitivity=None,
                   fn_ln=None, unroll_for=False, ssa_transform=False,
                   **kargs):
        if self.is_cloned:
            # TODO: fix this with kargs
            self.__cached_initialization.append((self.add_code, [fn, comment]))
            return
        block_type, raw_sensitives, stmts = transform_stmt_block(self, fn, unroll_for=unroll_for,
                                                                 fn_ln=fn_ln, kargs=kargs,
                                                                 apply_ssa=ssa_transform)
        if sensitivity:
            # override the block type and sensivitives
            block_type = CodeBlockType.Sequential
            raw_sensitives = sensitivity
        if block_type == CodeBlockType.Combinational:
            # it's a combinational block
            comb = CombinationalCodeBlock(self)
            for stmt in stmts:
                comb.add_stmt(stmt, False)
            node = comb
        elif block_type == CodeBlockType.Initial:
            # it's a initial block
            init = InitialCodeBlock(self)
            for stmt in stmts:
                init.add_stmt(stmt, False)
            node = init
        elif block_type == CodeBlockType.Latch:
            # it's a latch block
            latch = LatchCodeBlock(self)
            for stmt in stmts:
                latch.add_stmt(stmt, False)
            node = latch
        else:
            sensitivity_list = []
            for edge, var_name in raw_sensitives:
                edge = BlockEdgeType[edge]
                if isinstance(var_name, str):
                    var = self.internal_generator.get_var(var_name)
                else:
                    assert isinstance(var_name, _kratos.Var)
                    var = var_name
                sensitivity_list.append((edge, var))
            seq = SequentialCodeBlock(self, sensitivity_list)
            for stmt in stmts:
                seq.add_stmt(stmt, False)
            node = seq
        # add context vars
        if self.debug and fn_ln is None:
            for stmt in stmts:
                add_scope_context(stmt, get_frame_local(2))
        if comment:
            node.comment = comment
        if label:
            self.mark_stmt(label, node)
        if len(kargs) > 0:
            from .passes import Attribute
            for key, value in kargs.items():
                bool_val = bool(value)
                if bool_val:
                    node.add_attribute(Attribute.create(key))
        if ssa_transform:
            from .passes import Attribute
            node.add_attribute(Attribute.create("ssa"))
        return node

    add_code = add_always

    def __assign(self, var_to, var_from):
        correct_dir, correct_assign = self.__generator.correct_wire_direction(
            var_to, var_from)
        if not correct_assign:
            raise ValueError(str(var_to) + " cannot be assign to " +
                             str(var_from) +
                             ". Please check your module hierarchy")
        if correct_dir:
            stmt = var_to.assign(var_from)
        else:
            stmt = var_from.assign(var_to)
        self.add_stmt(stmt, False)
        return stmt

    def wire(self, var_to, var_from,
             attributes: Union[List[_kratos.passes.Attribute],
                               _kratos.passes.Attribute] = None,
             comment="", locals_=None, fn_ln=None, additional_frame=0):
        if self.is_cloned:
            if self.debug and locals_ is None:
                locals_ = get_frame_local(2 + additional_frame)
            self.__cached_initialization.append((self.wire, [var_to, var_from,
                                                             attributes,
                                                             comment, locals_]))
            return
        # wire interface is a special treatment
        if isinstance(var_from, (_kratos.InterfaceRef, InterfaceWrapper)) or \
                isinstance(var_to, (_kratos.InterfaceRef, InterfaceWrapper)):
            if isinstance(var_from, InterfaceWrapper):
                var_from = var_from.internal_interface
            if isinstance(var_to, InterfaceWrapper):
                var_to = var_to.internal_interface
            assert isinstance(var_from, _kratos.InterfaceRef)
            assert isinstance(var_to, _kratos.InterfaceRef)
            # TODO: add debug info to interface wiring
            self.__generator.wire_interface(var_to, var_from)
            return
        # this is a top level direct wire assignment
        # notice that we can figure out the direction automatically if
        # both of them are ports
        # handle port bundles
        if isinstance(var_to, _kratos.PortBundleRef):
            assert isinstance(var_from, _kratos.PortBundleRef)
            if self.debug:
                entry = get_fn_ln(2 + additional_frame)
            else:
                entry = []
            var_from.assign(var_to, self.__generator, entry)
            return
        if isinstance(var_to, _kratos.Port) and isinstance(var_from,
                                                           _kratos.Port):
            stmt = self.__generator.wire_ports(var_to, var_from)
        else:
            stmt = self.__assign(var_to, var_from)

        if self.debug:
            if fn_ln is not None:
                stmt.add_fn_ln(fn_ln)
            else:
                stmt.add_fn_ln(get_fn_ln(2 + additional_frame))
                if locals_ is None:
                    locals_ = get_frame_local(2 + additional_frame)
                add_scope_context(stmt, locals_)

        if attributes is not None:
            if not isinstance(attributes, list):
                attributes = [attributes]
            for attr in attributes:
                stmt.add_attribute(attr)

        if comment:
            stmt.comment = comment

    def add_fsm(self, fsm_name: str, clk_name=None, reset_name=None,
                reset_high=True):
        if clk_name is not None and reset_name is not None:
            clk = self.__generator.get_var(clk_name)
            reset = self.__generator.get_var(reset_name)
            fsm = FSM(self, self.__generator.fsm(fsm_name, clk, reset))
        else:
            fsm = FSM(self, self.__generator.fsm(fsm_name))
        fsm.set_reset_high(reset_high)
        return fsm

    def property(self, property_name: str, seq):
        return self.__generator.property(property_name, seq)

    def add_stmt(self, stmt, add_ln_info=True):
        if self.is_cloned:
            self.__cached_initialization.append((self.add_stmt, [stmt]))
            return
        self.__generator.add_stmt(stmt)
        if add_ln_info and self.debug:
            stmt.add_fn_ln(get_fn_ln())
            add_scope_context(stmt, get_frame_local(2))

    def remove_stmt(self, stmt):
        if self.is_cloned:
            self.__cached_initialization.append((self.remove_stmt, [stmt]))
            return
        self.__generator.remove_stmt(stmt)

    def add_child_generator(self, instance_name: str, generator: "Generator",
                            comment="", python_only=False, **kargs):
        if self.is_cloned:
            self.__cached_initialization.append((self.add_child_generator,
                                                 (instance_name, generator)))
            return
        if instance_name in self.__child_generator:
            raise Exception(
                "{0} already exists in {1}".format(instance_name,
                                                   self.instance_name))
        assert isinstance(generator,
                          Generator), "generator is not a Generator instance"

        self.__child_generator[instance_name] = generator
        generator.__parent = self

        if python_only:
            # only add it to the python level interface, the caller is
            # responsible for the connections etc
            return
        else:
            generator.__generator.instance_name = instance_name

        if self.debug:
            fn, ln = get_fn_ln()
            self.__generator.add_child_generator(instance_name,
                                                 generator.__generator,
                                                 (fn, ln))
        else:
            self.__generator.add_child_generator(instance_name,
                                                 generator.__generator)
        if comment:
            self.__generator.set_child_comment(instance_name, comment)

        # set parameter values first
        for child_param, parent_value in kargs.items():
            if child_param in generator.params:
                generator.params[child_param].value = parent_value

        # bulk wiring
        for child_port, parent_port in kargs.items():
            # it can be parameter as well. we already taken care of that
            if child_port in generator.params:
                continue
            if isinstance(parent_port, str):
                if parent_port in self.ports:
                    parent_port = self.ports[parent_port]
                else:
                    parent_port = self.vars[parent_port]
            self.wire(generator.ports[child_port], parent_port,
                      additional_frame=1)

    # alias
    add_child = add_child_generator

    def remove_child_generator(self, generator):
        if self.is_cloned:
            self.__cached_initialization.append((self.remove_child_generator,
                                                 [generator]))
            return
        if generator.instance_name not in self.__child_generator:
            raise Exception("{0} doesn't exist in {1}".format(generator.name,
                                                              self.name))
        self.__child_generator.pop(generator.instance_name)
        self.__generator.remove_child_generator(generator.__generator)

    def replace(self, child_name: str, new_child: "Generator"):
        assert child_name in self.__child_generator
        if self.debug:
            debug_info = get_fn_ln()
            self.__generator.replace(child_name, new_child.internal_generator,
                                     debug_info)
        else:
            self.__generator.replace(child_name, new_child.internal_generator)
        self.__child_generator[child_name] = new_child

    def child_generator(self):
        return self.__child_generator

    @staticmethod
    def clear_context():
        Generator.__context.clear()
        # also clean the caches
        clses = Generator.__subclasses__()
        for cls in clses:  # type: Generator
            cls._cache.clear()
        # clean the function calls
        from .func import clear_context
        clear_context()

    @staticmethod
    def clear_context_hash():
        Generator.__context.clear_hash()

    @staticmethod
    def get_context():
        return Generator.__context

    @staticmethod
    def from_verilog(top_name: str, src_file: str, lib_files: List[str],
                     port_mapping: Dict[str, PortType]):
        g = Generator("")
        _port_mapping = {}
        for name, _type in port_mapping.items():
            _port_mapping[name] = _type.value
        g.__generator = _kratos.Generator.from_verilog(Generator.__context,
                                                       src_file, top_name,
                                                       lib_files, _port_mapping)
        Generator.__context.add(g.__generator)
        return g

    def __contains__(self, generator: "Generator"):
        if not isinstance(generator, (Generator, _kratos.Generator)):
            return False
        elif isinstance(generator, Generator):
            return generator.__generator in self.__generator
        else:
            return generator in self.__generator

    def initialize_clone(self):
        if self.is_cloned:
            self.__generator.is_cloned = False
            for fn, args in self.__cached_initialization:
                fn(*args)
            self.__cached_initialization.clear()

    def __set_generator_name(self, name):
        self.__generator.name = name

    @classmethod
    def __cached_py_generator(cls, **kargs):
        hash_value = 0
        for key, value in kargs.items():
            hash_value = hash_value ^ (hash(key) << 16) ^ hash(value)
        if hash_value not in cls._cache:
            g = cls(**kargs)
            cls._cache[hash_value] = g
            return g, False
        else:
            return cls._cache[hash_value], True

    @classmethod
    def clone(cls, **kargs):
        gen, cached = cls.__cached_py_generator(**kargs)
        if not cached:
            return gen
        else:
            g = Generator("")
            g.__generator = gen.__generator.clone()
            g.__def_instance = gen
            return g

    @classmethod
    def create(cls, **kargs):
        # if the debug is set to True globally, we don't create any
        # clones
        if get_global_debug():
            return cls(**kargs)
        gen, cached = cls.__cached_py_generator(**kargs)
        if not cached:
            return gen
        else:
            kargs["is_clone"] = True
            g = cls(**kargs)
            g.__def_instance = gen
            g.__generator.def_instance = gen.internal_generator
            return g

    # list of helper functions similar to chisel, but force good naming
    # so that we can produce a readable verilog
    def __get_port_name_type(self, port, port_type):
        if port is None:
            clock_names = self.__generator.get_ports(port_type.value)
            assert len(clock_names) > 0, str(port_type) + " signal not found"
            port = clock_names[0]
        if isinstance(port, str):
            port = self.ports[port]
        assert self.__generator.has_port(port.name)
        return port.name

    def __get_var_assert(self, var):
        if isinstance(var, str):
            var = self.vars[var]
            assert self.__generator.has_var(var.name)
        return var

    def __create_new_var(self, var_name, var_ref):
        new_var = self.var(var_name, var_ref.width, var_ref.signed,
                           var_ref.size)
        if self.debug:
            new_var.add_fn_ln(get_fn_ln())
        return new_var

    def __add_stmt_with_debug(self, block, stmt):
        if self.debug:
            stmt.add_fn_ln(get_fn_ln())
        block.add_stmt(stmt)

    def dpi(self, func_name):
        return self.__generator.dpi_function(func_name)

    def reg_next(self, var_name, var, clk=None):
        clk_name = self.__get_port_name_type(clk, PortType.Clock)
        clk = self.ports[clk_name]
        if clk_name not in self.__reg_next_stmt:
            self.__reg_next_stmt[clk_name] = self.sequential(
                (BlockEdgeType.Posedge, clk))
        var = self.__get_var_assert(var)
        new_var = self.__create_new_var(var_name, var)
        self.__add_stmt_with_debug(self.__reg_next_stmt[clk_name],
                                   new_var.assign(var))
        return new_var

    def reg_init(self, var_name, var, clk=None, reset=None, init_value=0):
        clk_name = self.__get_port_name_type(clk, PortType.Clock)
        rst_name = self.__get_port_name_type(reset, PortType.AsyncReset)
        clk = self.ports[clk_name]
        reset = self.ports[rst_name]
        if (clk_name, rst_name) not in self.__reg_init_stmt:
            seq = self.sequential((BlockEdgeType.Posedge, clk),
                                  (BlockEdgeType.Posedge, reset))
            if_stmt = seq.if_(reset)
            self.__reg_init_stmt[(clk_name, rst_name)] = if_stmt
        if_stmt = self.__reg_init_stmt[(clk_name, rst_name)]
        var = self.__get_var_assert(var)
        new_var = self.__create_new_var(var_name, var)
        self.__add_stmt_with_debug(if_stmt.else_body(), new_var.assign(var))
        self.__add_stmt_with_debug(if_stmt.then_body(),
                                   new_var.assign(init_value))
        return new_var

    def reg_enable(self, var_name, var, en, clk=None):
        clk_name = self.__get_port_name_type(clk, PortType.Clock)
        clk = self.ports[clk_name]
        if isinstance(var, str):
            var = self.ports[var]
        assert self.__generator.has_var(var.name)
        if isinstance(en, str):
            en = self.ports[en]
        assert self.__generator.has_var(en.name)
        if (clk.name, en.name) not in self.__reg_en_stmt:
            seq = self.sequential((BlockEdgeType.Posedge, clk))
            if_stmt = seq.if_(en)
            self.__reg_en_stmt[(clk_name, en.name)] = if_stmt
        if_stmt = self.__reg_en_stmt[(clk_name, en.name)]
        var = self.__get_var_assert(var)
        new_var = self.__create_new_var(var_name, var)
        self.__add_stmt_with_debug(if_stmt.then_body(), new_var.assign(var))
        return new_var

    # meta values
    def mark_stmt(self, name: str, stmt):
        if not isinstance(stmt, _kratos.StmtBlock):
            raw_stmt = stmt.stmt()
        else:
            raw_stmt = stmt
        if self.__generator.has_named_block(name):
            raise ValueError(name + " already exists")

        self.__stmt_label_mapping[name] = stmt
        self.__generator.add_named_block(name, raw_stmt)

    def get_marked_stmt(self, name):
        assert name in self.__stmt_label_mapping
        return self.__stmt_label_mapping[name]


def always_ff(*sensitivity):
    assert len(sensitivity) > 0, "always_ff needs at least one signal"
    for edge, var in sensitivity:
        assert isinstance(edge, BlockEdgeType)
        assert isinstance(var, (str, _kratos.Var))

    return AlwaysWrapper


def always_latch(fn):
    return AlwaysWrapper(fn)


def always_comb(fn):
    return AlwaysWrapper(fn)


def initial(fn):
    return AlwaysWrapper(fn)
