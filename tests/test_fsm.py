from kratos import Generator, always_ff, verilog, posedge, const


def setup_fsm(fsm, out_, in_):
    # add outputs
    fsm.output(out_)
    # add states
    red = fsm.add_state("Red")
    blue = fsm.add_state("Blue")
    # set the state transition
    red.next(red, in_ == 0)
    red.next(blue, in_ == 1)
    blue.next(red, in_ == 1)
    # fill in outputs
    red.output(out_, 2)
    blue.output(out_, 1)
    # set the start case
    fsm.set_start_state("Red")


def test_fsm(check_gold, check_file):
    mod = Generator("mod", debug=True)
    out_ = mod.output("out", 2)
    in_ = mod.input("in", 2)
    # fsm requires a clk and async rst
    mod.clock("clk")
    mod.reset("rst")
    # add a dummy fsm
    fsm = mod.add_fsm("Color")
    # setup FSM
    setup_fsm(fsm, out_, in_)

    check_gold(mod, "test_fsm", optimize_if=False)
    # output fsm graph
    dot = fsm.dot_graph()
    check_file(dot, "test_fsm.dot")
    csv = fsm.output_table()
    check_file(csv, "test_fsm.csv")


def test_fsm_mealy(check_gold):
    mod = Generator("mod", debug=True)
    out_ = mod.output("out", 2)
    in_ = mod.input("in", 2)
    # fsm requires a clk and async rst
    mod.clock("clk")
    mod.reset("rst")
    # add a dummy fsm
    fsm = mod.add_fsm("Color")
    # setup FSM
    setup_fsm(fsm, out_, in_)
    # use mealy
    fsm.is_moore = False
    check_gold(mod, "test_fsm_mealy", optimize_if=False)


def test_fsm_default_output():
    mod = Generator("mod", debug=True)
    out_ = mod.output("out", 2)
    in_ = mod.input("in", 2)
    # fsm requires a clk and async rst
    mod.clock("clk")
    mod.reset("rst")
    fsm = mod.add_fsm("Color")
    fsm.output(out_, const(2, 2))
    # add states
    red = fsm.add_state("Red")
    blue = fsm.add_state("Blue")
    red.next(blue, in_ == 0)
    blue.next(red, in_ == 1)
    blue.output(out_, 1)
    fsm.set_start_state("Red")
    src = verilog(mod)["mod"]
    assert "out = 2'h2;" in src


def test_fsm_state(check_gold):
    from kratos import negedge
    mod = Generator("mod", debug=True)
    out_ = mod.output("out", 2)
    in_ = mod.input("in", 2)
    # fsm requires a clk and async rst
    clk = mod.clock("clk")
    rst = mod.reset("rst")
    # add a dummy fsm
    fsm = mod.add_fsm("Color", reset_high=False)
    # setup FSM
    setup_fsm(fsm, out_, in_)
    # realize fsm now
    fsm.realize()
    current_state = fsm.current_state
    # create an enum var based on current_state
    state_enum = current_state.enum_type()
    # can create a variable from the enum definition
    # notice that variable s will be optimized away if not used
    s = mod.enum_var("s", state_enum)
    c = mod.var("counter", 1)

    @always_ff((posedge, clk), (negedge, rst))
    def counter():
        if rst.r_not():
            c = 0
        elif current_state == state_enum.Red:
            c = c + 1

    mod.add_always(counter)
    check_gold(mod, "test_fsm_state", optimize_if=False)


def test_nested_fsm(check_gold, check_file):
    mod = Generator("mod", debug=True)
    out_ = mod.output("out", 2)
    in_ = mod.input("in", 2)
    # fsm requires a clk and async rst
    mod.clock("clk")
    mod.reset("rst")
    # add a dummy fsm
    fsm = mod.add_fsm("Color")
    setup_fsm(fsm, out_, in_)
    second_fsm = mod.add_fsm("HSV")
    fsm.add_child_fsm(second_fsm)
    idle = second_fsm.add_state("idle")
    idle.next(fsm["Red"], in_ == 0)
    fsm["Red"].next(idle, in_ == 2)
    second_fsm.output(out_)
    idle.output(out_, 2)

    dot = fsm.dot_graph()
    check_file(dot, "test_nested_fsm.dot")
    check_gold(mod, "test_nested_fsm", optimize_if=False)
