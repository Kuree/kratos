from _kratos import Simulator as _Simulator
from .generator import Generator, PortType


# Python wrapper for the simulator
class Simulator:
    def __init__(self, generator: Generator):
        self._sim = _Simulator(generator.internal_generator)
        # get the clock and reset
        clks = generator.internal_generator.get_ports(PortType.Clock)
        if len(clks) == 1:
            self._clk = generator.ports[clks[0]]
        else:
            self._clk = None
        resets = generator.internal_generator.get_ports(PortType.AsyncReset)
        if len(resets) == 1:
            self._reset = generator.ports[resets[0]]
        else:
            self._reset = None

    def set(self, var, value):
        self._sim.set(var, value)

    def get(self, var):
        if len(var.size) > 1 or var.size[0] > 1:
            return self._sim.get_array(var)
        else:
            return self._sim.get(var)

    def cycle(self, n=1):
        if self._clk is None:
            raise RuntimeError("Single clock not found")
        for _ in range(n):
            self.set(self._clk, 1)
            self.set(self._clk, 0)

    def reset(self, reset_high=True):
        if self._reset is None:
            raise RuntimeError("Single reset not found")
        if reset_high:
            self.set(self._reset, 1)
            self.set(self._reset, 0)
        else:
            self.set(self._reset, 0)
            self.set(self._reset, 1)
