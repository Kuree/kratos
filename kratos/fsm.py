from .util import get_fn_ln


class FSM:
    """Wrapper class for _kratos.FSM"""
    def __init__(self, generator, fsm):
        self.__generator = generator
        self.__fsm = fsm

    def output(self, var):
        self.__fsm.output(var)

    def add_state(self, name):
        if self.__generator.debug:
            debug = get_fn_ln()
            return FSMState(self.__generator, self.__fsm.add_state(name, debug))
        else:
            return FSMState(self.__generator, self.__fsm.add_state(name))

    def set_start_state(self, state):
        if isinstance(state, str):
            self.__fsm.set_start_state(state)
        elif isinstance(state, FSMState):
            self.__fsm.set_start_state(state.internal_state)
        else:
            self.__fsm.set_start_state(state)

    def dot_graph(self, filename=None):
        if filename is not None:
            return self.__fsm.dot_graph(filename)
        else:
            return self.__fsm.dot_graph()

    def output_table(self, filename=None):
        if filename is not None:
            return self.__fsm.output_table(filename)
        else:
            return self.__fsm.output_table()


class FSMState:
    def __init__(self, generator, fsm_state):
        self.__generator = generator
        self.__fsm_state = fsm_state

    def next(self, next_state, cond):
        if self.__generator.debug:
            debug = get_fn_ln()
            self.__fsm_state.next(next_state.internal_state, cond, debug)
        else:
            self.__fsm_state.next(next_state.internal_state, cond)

    def output(self, var, value):
        if self.__generator.debug:
            debug = get_fn_ln()
            self.__fsm_state.output(var, value, debug)
        else:
            self.__fsm_state.output(var, value)

    @property
    def internal_state(self):
        return self.__fsm_state
