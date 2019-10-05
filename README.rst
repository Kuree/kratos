Kratos
======

|Build Status| |PyPI - Format| |PyPI - Version| |Documentation Status|

Kratos is a hardware design language written in C++/Python. It
differentiates itself from other DSL with the following design
philosophy:

- Fully debuggable: debug hardware just like debugging Python code!
- Highly efficient: Python frontend powered by
  Modern C++ binding. Designed with multi-processing in mind.
- Human-readable verilog: we know how difficult it is to read machine
  generated verilog. kratos has multiple passes to produce nice-looking
  verilog.
- Generator of generators: every python object is a generator
  that can be modified at any time, even after instantiation. This allows
  complex passes on the generators without ripping old structure apart.
- Keep the good parts of verilog: The ``always`` block in behavioral
  verilog is close to other programming languages. Kratos allows you to
  write python code similar to behavioral verilog
- Single source of truth: kratos encourages users to infuse generator
  information inside generator itself. This makes debugging and
  verification much easier.
- Static elaboration: kratos allows user to write parametrized code,
  even in the ``always`` block, all in Python.
- Type checking: kratos check the variable types
  for each assignment to make sure there is no implicit conversion.

Install
-------

::

   pip install kratos

Pre-built wheels supports all Python 3.5+ on Linux and Python 3.7 on OSX.
To build it from scratch, you need a ``C++17`` compatible compiler, such
as ``g++-8``.

Documentation and Examples
--------------------------

You can check the documentation at `Read the
Docs <https://kratos-doc.readthedocs.io/en/latest/>`__

Here are some examples to showcase the ability of kratos.

Asnyc Reset Register
~~~~~~~~~~~~~~~~~~~~

Python code that parametrizes based on the ``width``. Notice that we
specify the sensitivity of the ``always`` block when defining
``seq_code_block``.

.. code:: python

   class AsyncReg(Generator):
       def __init__(self, width):
           super().__init__("register")

           # define inputs and outputs
           self._in = self.input("in", width)
           self._out = self.output("out", width)
           self._clk = self.clock("clk")
           self._rst = self.reset("rst")
           self._val = self.var("val", width)

           # add combination and sequential blocks
           self.add_code(self.seq_code_block)

           self.add_code(self.comb_code_block)

       @always((posedge, "clk"), (posedge, "rst"))
       def seq_code_block(self):
           if self._rst:
               self._val = 0
           else:
               self._val = self._in

       def comb_code_block(self):
           self._out = self._val

Here is the generated verilog

.. code:: verilog

   module register (
     input  clk,
     input [15:0] in,
     output reg [15:0] out,
     input  rst
   );

   logic  [15:0] val;

   always @(posedge clk, posedge rst) begin
     if rst begin
       val <= 16'h0;
     end
     else begin
       val <= in;
     end
   end
   always_comb begin
     out = val;
   end
   endmodule   // register

Fanout module
~~~~~~~~~~~~~

This is an example to showcase the kratos’ static elaboration ability in
``always`` block. In practice we would not write it this way.

.. code:: python

   class PassThrough(Generator):
       def __init__(self, num_loop):
           super().__init__("PassThrough", True)
           self.in_ = self.input("in", 1)
           self.out_ = self.output("out", num_loop)
           self.num_loop = num_loop

           self.add_code(self.code)

       def code(self):
           if self.in_ == self.const(1, 1):
               for i in range(self.num_loop):
                   self.out_[i] = 1
           else:
               for i in range(self.num_loop):
                   self.out_[i] = 0

Here is generated verilog

.. code:: verilog

   module PassThrough (
     input  in,
     output reg [3:0] out
   );

   always_comb begin
     if (in == 1'h1) begin
       out[0:0] = 1'h1;
       out[1:1] = 1'h1;
       out[2:2] = 1'h1;
       out[3:3] = 1'h1;
     end
     else begin
       out[0:0] = 1'h0;
       out[1:1] = 1'h0;
       out[2:2] = 1'h0;
       out[3:3] = 1'h0;
     end
   end
   endmodule   // PassThrough

How to debug
------------

Because Python is quite slow, By default the debug option is off. You
can turn on debugging for individual modules. Here is an example on how
to turn on debug (see ``tests/test_generator.py`` for more details).

.. code:: python

   class PassThroughMod(Generator):
       def __init__(self):
           super().__init__("mod1", True)
           self.in_ = self.input("in", 1)
           self.out_ = self.output("out", 1)
           self.wire(self.out_, self.in_)

   # ... some other code
   class Top(Generator):
       def __init__(self):
           super().__init__("top", True)

           self.input("in", 1)
           self.output("out", 1)

           pass_through = PassThroughMod()
           self.add_child("pass", pass_through)
           self.wire(self["pass"].ports["in"], self.ports["in"])

           self.wire(self.ports.out, self["pass"].ports.out)

   mod = Top()
   mod_src, debug_info = verilog(mod, debug=True)

You can see the generated verilog:

.. code:: verilog

   module top (
     input logic  in,
     output logic  out
   );

   assign out = in;
   endmodule   // top

The ``pass`` sub-module disappeared due to the compiler optimization.
However, if we print out the debug information, we can see the full
trace of debug info on ``assign out = in;``

.. code:: python

   {
     1: [('/home/keyi/workspace/kratos/tests/test_generator.py', 532)],
     2: [('/home/keyi/workspace/kratos/tests/test_generator.py', 534)],
     3: [('/home/keyi/workspace/kratos/tests/test_generator.py', 535)],
     6: [('/home/keyi/workspace/kratos/tests/test_generator.py', 539),
         ('/home/keyi/workspace/kratos/src/expr.cc', 455),
         ('/home/keyi/workspace/kratos/tests/test_generator.py', 541),
         ('/home/keyi/workspace/kratos/src/expr.cc', 485),
         ('/home/keyi/workspace/kratos/src/pass.cc', 653)]
   }

These ``pass.cc`` is the pass that removed the pass through module.

If we modified the source code a little bit that change the wire
assignment into a combination block, such as

.. code:: python

   class Top(Generator):
       def __init__(self):
           super().__init__("top", True)

           self.input("in", 1)
           self.output("out", 1)

           pass_through = PassThroughMod()
           self.add_child("pass", pass_through)
           self.wire(self["pass"].ports["in"], self.ports["in"])

           self.add_code(self.code_block)

       def code_block(self):
           self.ports.out = self["pass"].ports.out

We can see the generated verilog will be a little bit verbose:

.. code:: verilog

   module top (
     input logic  in,
     output logic  out
   );

   logic   top$in_0;
   assign top$in_0 = in;
   always_comb begin
     out = top$in_0;
   end
   endmodule   // top

And the debug info shows all the information as well:

.. code:: python

   {
     1: [('/home/keyi/workspace/kratos/tests/test_generator.py', 554)],
     2: [('/home/keyi/workspace/kratos/tests/test_generator.py', 556)],
     3: [('/home/keyi/workspace/kratos/tests/test_generator.py', 557)],
     7: [('/home/keyi/workspace/kratos/tests/test_generator.py', 561), ('/home/keyi/workspace/kratos/src/expr.cc', 455)],
     8: [('/home/keyi/workspace/kratos/tests/test_generator.py', 563)],
     9: [('/home/keyi/workspace/kratos/tests/test_generator.py', 566), ('/home/keyi/workspace/kratos/src/expr.cc', 485)]}

Ecosystem
---------

Kratos has its own ecosystem to program behavioral verilog in Python. Most of them
are plugins that will help users to debug, prototype, and testing.

`kratos <https://github.com/Kuree/kratos>`__ is a programming model for
building hardware. The main abstraction in kratos in a ``Generator``.
``Generator`` can be modified at any time through passes.

`kratos-debug <https://github.com/Kuree/kratos-debug>`__ is a GUI for user to
view generated verilog. It offers a source viewer to see the line mapping that
kratos provides.

`kratos-dpi <https://github.com/Kuree/kratos-dpi>`__ is a DPI plugin that
allows users to run arbitrary Python code to emulate a SystemVerilog function.
This is extremely helpful for rapid prototyping and testing.

`kratos-runtime <https://github.com/Kuree/kratos-runtime>`__ is a necessary
component if you want to debug kratos with standard simulators. It supports
value inspection and breakpoints.

`kratos-vscode <https://github.com/Kuree/kratos-vscode>`__ is a Visual Studio
Code extension that allows user to debug with Kratos. The simulator has to be
loaded with ``kratos-runtime``.

.. |Build Status| image:: https://travis-ci.com/Kuree/kratos.svg?branch=master
   :target: https://travis-ci.com/Kuree/kratos
.. |PyPI - Format| image:: https://img.shields.io/pypi/format/kratos
   :target: https://pypi.org/project/kratos/
.. |PyPI - Version| image:: https://badge.fury.io/py/kratos.svg
   :target: https://pypi.org/project/kratos/
.. |Documentation Status| image:: https://readthedocs.org/projects/kratos-doc/badge/?version=latest
   :target: https://kratos-doc.readthedocs.io/en/latest/?badge=latest
