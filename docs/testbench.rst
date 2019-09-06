Generate SystemVerilog Test Bench
##################################

Kratos offers a simple and handy way to create test bench for your generators.
However, due to the complex semantics in SystemVerilog, we don't have support
for verilator yet. All the functionality has been tested with VCS and
Incisive though.


Creating a Test Bench for your design
=====================================
Let's look at the following example:

.. code-block:: Python

    dut = Generator("mod")
    dut.wire(dut.output("out", 1), dut.input("in", 1))
    dut.wire(dut.var("val", 1), dut.ports["in"])

    tb = TestBench()

    tb.add_child("dut", dut)
    in_ = tb.var("in", 1)
    out_ = tb.var("out", 1)
    tb.wire(dut.ports["in"], in_)
    tb.wire(out_, dut.ports["out"])

First, we created a Design-under-Test (dut) module, then we create a tb
TestBench object, and add our dut as a child instance. We then wire
these variables together, as we do to the normal generators.


You can then call the initial block and use free-style to program your
tests, as shown below:

.. code-block:: Python

    @initial
    def code():
        in_ = 1
        assert_(out_ == 1)
        # access internal signal
        assert_(dut.vars.val == 1)

Notice that we use ``assert_`` as a assertion call: it is because ``assert``
is a system built-in function. You can access internal signals we you'd
normally do in the SystemVerilog test bench.


To insert delay, you can call the ``delay()`` function and specify the number
of time for the delay. You can only put delay on an assignment statement.

SystemVerilog Property Assertion
================================
Kratos supports complex property check on sequences. Let's take a look at the
following example based on the previous generator setup:

.. code-block:: Python

    # add a clock and wire them together
    tb.wire(dut.clock("clk"), tb.var("clk", 1))

    seq = Sequence(in_ == 1)
    seq.imply(out_ == 1).wait(1).imply(out_ == 0)

    prop = tb.property("test_out", seq)


Since sequence requires clock, as specified by the SystemVerilog spec,
we need to add clock signals. After that, we first created an initial
sequence, called ``seq``,
then we specify the next sequence using ``imply`` call, which returns
the next sequence object. We want that to wait one clock cycle, hence
calling ``wait(1)``. This sequence also implies ``out_ == 0``.
This chained creation allows you to meta-program the sequence.

After creating the sequence, we can add the it to a property. We call
``tb.property()`` to give it a name. Kratos will automatically wire
the clocks to the sequence.

.. note::

  If your design has multiple clocks, you need to specify the clock on
  sequences by yourself. Here is an example on how to specify the clock
  edges.

  .. code-block:: Python

      prop.edge(BlockEdgeType.Posedge.value, clk)

Road Map
========
- Assume and coverage
- More syntax sugar to reduce the amount of typings
