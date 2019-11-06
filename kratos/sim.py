from _kratos import Simulator as _Simulator
from .generator import Generator


# Python wrapper for the simulator
class Simulator:
    def __init__(self, generator: Generator):
        self._sim = _Simulator(generator.internal_generator)

    def set(self, var, value):
        self._sim.set(var, value)

    def get(self, var):
        if len(var.size) > 1 or var.size[0] > 1:
            return self._sim.get_array(var)
        else:
            return self._sim.get(var)
