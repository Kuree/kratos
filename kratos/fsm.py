from _kratos import get_fn_ln


class FSM:
    """Wrapper class for _kratos.FSM"""
    def __init__(self, generator, fsm):
        self.__generator = generator
        self.__fsm = fsm
        self.__states = {}

    def output(self, var):
        self.__fsm.output(var)

    def add_state(self, name):
        if self.__generator.debug:
            debug = get_fn_ln()
            state = FSMState(self.__generator, self.__fsm.add_state(name, debug))
        else:
            state = FSMState(self.__generator, self.__fsm.add_state(name))
        self.__states[name] = state
        return state

    def set_start_state(self, state):
        if isinstance(state, FSMState):
            state = state.internal_state
        if self.__generator.debug:
            debug = get_fn_ln()
            self.__fsm.set_start_state(state, debug)
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

    def __getitem__(self, fsm_name):
        return self.__states[fsm_name]

    def add_child_fsm(self, fsm):
        self.__fsm.add_child_fsm(fsm.__fsm)

    def realize(self):
        self.__fsm.realize()

    @property
    def current_state(self):
        return self.__fsm.current_state

    @property
    def is_moore(self):
        return self.__fsm.is_moore()

    @is_moore.setter
    def is_moore(self, value):
        self.__fsm.set_moore(value)

    def set_reset_high(self, value: bool):
        self.__fsm.set_reset_high(value)


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
