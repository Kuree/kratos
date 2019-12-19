from kratos import Simulator, Generator, posedge, always_ff, negedge


def test_sim_reg():
    class AsyncReg(Generator):
        def __init__(self, width, debug=False):
            super().__init__("Register", debug)

            self.in_ = self.input("in", width)
            self.out = self.output("out", width)
            self.clk = self.clock("clk")
            self.rst = self.reset("rst")

            self.add_always(self.seq_code_block)

        @always_ff((posedge, "clk"), (negedge, "rst"))
        def seq_code_block(self):
            if ~self.rst:
                self.out = 0
            else:
                self.out = self.in_

    reg = AsyncReg(16)
    sim = Simulator(reg)
    val = sim.get(reg.out)
    assert val is None
    # reset
    sim.reset(False)
    val = sim.get(reg.out)
    assert val == 0
    # put in some values
    for v in range(1, 10 + 1):
        sim.set(reg.in_, v)
        val = sim.get(reg.out)
        # 1 cycle delay
        assert val == v - 1
        # toggle the clock
        sim.cycle()
        val = sim.get(reg.out)
        assert val == v


def test_expr():
    mod = Generator("mod")
    a = mod.input("a", 16)
    b = mod.output("b", 16)
    e = a + a
    for i in range(4):
        e = e + a
    mod.add_stmt(b.assign(e))

    sim = Simulator(mod)
    assert sim.get(b) is None
    sim.set(a, 2)
    assert sim.get(b) == 12


if __name__ == "__main__":
    test_expr()
