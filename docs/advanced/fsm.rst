Finite State Machine
####################

FSM in kratos is a first-class object, just like variables or ports.
This design choice is made to help engineers to design complex FSM
with ease.

Create a FSM
============
Lets look at the following code example

.. code-block:: Python

    mod = Generator("mod", debug=True)
    out_ = mod.output("out", 2)
    in_ = mod.input("in", 2)
    # fsm requires a clk and async rst
    mod.clock("clk")
    mod.reset("rst")
    # add a dummy fsm
    fsm = mod.add_fsm("Color")
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


First, we create a FSM called ``"Color"`` using ``[gen].add_fsm()``, which
returns an FSM object. By default, it searches for clock and async reset
signal in the generator. If the generator has multiple clocks/reset, you
can provide the variable in ``[gen].add_fsm()`` (see API for more information).

Then, we specify the outputs by calling ``fsm.output()``. All the outputs have
to be fully specified. This allows Kratos to check the completeness of the FSM.

You can add a state by calling ``fsm.add_state(state_name)``. It will return
an object that represent the state. You can describe the state transition by
calling ``state.next(next_state, condition)``, where ``next_state`` can either
be a ``str`` or state object. You also need to fully specify the outputs for
each output variable, using ``state.output(output_var, value)``. If the output
value is not changed, you can use ``None`` as value.

By default, the start state is the first state in alphabetical order. You can
set the start state using ``fsm.set_start_state(state)``, where ``state`` can
either be a ``str`` or state object.


Here is the generated SystemVerilog code. Notice that all the output code
blocks are named to help you debug in simulation.

.. code-block:: SystemVerilog

  module mod (
    input logic  clk,
    input logic [1:0] in,
    output logic [1:0] out,
    input logic  rst
  );

  typedef enum {
    Blue = 1'h0,
    Red = 1'h1
  } Color_state;
  Color_state   Color_current_state;
  Color_state   Color_next_state;

  always @(posedge clk, posedge rst) begin
    if (rst) begin
      Color_current_state <= Red;
    end
    else Color_current_state <= Color_next_state;
  end
  always_comb begin
    unique case (Color_current_state)
      Blue: if (in == 2'h1) begin
        Color_next_state = Red;
      end
      Red: if (in == 2'h1) begin
        Color_next_state = Blue;
      end
      else if (in == 2'h0) begin
        Color_next_state = Red;
      end
    endcase
  end
  always_comb begin
    unique case (Color_current_state)
      Blue: begin :Color_Blue_Output
          out = 2'h1;
        end
      Red: begin :Color_Red_Output
          out = 2'h2;
        end
    endcase
  end
  endmodule   // mod


How to debug FSM
================

Kratos has built-in ability to output state transition diagram and output
table. You can obtain the diagram using ``fsm.dot_graph()`` or
``fsm.dot_graph(filename)``. If ``filename`` is not provided, a string version
will be returned. ``dot_graph()`` returns a standard ``dot`` graph that can
be converted into images via ``dot``. You can also use ``fsm.output_table()``
to obtain the table for each state's output. Again, providing the function
with a file name will save the output to a file.

Here is the state transition graph generated from the example

.. figure:: /images/fsm.svg
    :align: center

As always, if you set the ``debug`` in the generator to be ``true``, Kratos
will generate full trace of each statements back to the original python
functions. In addition, it utilizes named block to group outputs signals
together in generated SystemVerilog. This will make debugging with waveform
much easier.

Coming Soon
===========

1. Formal verification on FSM: both general cases and per-design
2. Automatic Moore machine -> Mealy machine conversation
