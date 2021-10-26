Kratos
======

|Build Status| |Appveyor Build status| |PyPI - Version|
|Coverage| |Documentation Status|

Kratos is a hardware design language written in C++/Python. It
differentiates itself from other DSL with the following design
philosophy:

- Fully debuggable: debug hardware just like debugging Python code!
  Thanks to `hgdb`_.
- Highly efficient: Python frontend powered by
  Modern C++ binding. Designed with multi-processing in mind.
- Human-readable verilog: we know how difficult it is to read machine
  generated verilog. kratos has multiple passes to produce nice-looking
  verilog.
- Generator of generators: every python object is a generator
  that can be modified at any time, even after instantiation. This allows
  complex passes on the generators without ripping old structure apart.
- Keep the good parts of SystemVerilog, such as ``always_ff``,
  ``always_comb``, ``interface``, and ``unique case``. Users control
  how and when to generate these semantics.
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

Pre-built wheels support all Python 3.6+ on Linux, Windows, and
OSX. To build it from scratch, you need a ``C++17`` compatible
compiler, such as ``g++-8`` or ``clang-8``.

Documentation and Examples
--------------------------

You can check the documentation at `Read the
Docs <https://kratos-doc.readthedocs.io/en/latest/>`__.

Here are some examples to showcase the ability of kratos.

Asnyc Reset Register
~~~~~~~~~~~~~~~~~~~~

Python code that parametrizes based on the ``width``. Notice that we
specify the sensitivity of the ``always_ff`` block when defining
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

           # add combination and sequential blocks
           self.add_code(self.seq_code_block)

       @always_ff((posedge, "clk"), (posedge, "rst"))
       def seq_code_block(self):
           if self._rst:
               self._out = 0
           else:
               self._out = self._in

Here is the generated SystemVerilog

.. code:: SystemVerilog

   module register (
     input logic clk,
     input logic [15:0] in,
     output logic [15:0] out,
     input logic rst
   );


   always_ff @(posedge clk, posedge rst) begin
     if (rst) begin
       out <= 16'h0;
     end
     else out <= in;
   end
   endmodule   // register


Fanout module
~~~~~~~~~~~~~

This is another example to showcase the kratos' ability to produce high-quality
SystemVerilog. In practice we would not write it this way.

.. code:: python

   class PassThrough(Generator):
       def __init__(self, num_loop):
           super().__init__("PassThrough")
           self.in_ = self.input("in", 1)
           self.out_ = self.output("out", num_loop)
           self.num_loop = num_loop

           self.add_code(self.code)

       @always_comb
       def code(self):
           if self.in_:
               for i in range(self.num_loop):
                   self.out_[i] = 1
           else:
               for i in range(self.num_loop):
                   self.out_[i] = 0

Here is generated SystemVerilog. Notice that the iteration variable ``i``
has been properly checked and resized to avoid index out of range.

.. code:: SystemVerilog

  module PassThrough (
    input logic in,
    output logic [3:0] out
  );

  always_comb begin
    if (in) begin
      for (int unsigned i = 0; i < 4; i += 1) begin
          out[2'(i)] = 1'h1;
        end
    end
    else begin
      for (int unsigned i = 0; i < 4; i += 1) begin
          out[2'(i)] = 1'h0;
        end
    end
  end
  endmodule   // PassThrough


How to debug
------------

Because Python is quite slow, By default the debug option is off. You
can turn on debugging for individual modules. See
``tests/test_generator.py`` for more details).


Use an IDE Debugger
-------------------

.. image:: https://cdn.jsdelivr.net/gh/Kuree/kratos-vscode@master/images/demo.gif
     :alt: demo

Thanks to the native support of `hgdb`_, you can debug the generated RTL with a
professional debugger as if you are debugging Python code. ``gdb``-like console version
is also available. Check out `hgdb`_ to see how it works!



.. |Build Status| image:: https://github.com/Kuree/kratos/workflows/Linux%20Wheel%20Test/badge.svg
   :target: https://github.com/Kuree/kratos/actions
.. |Appveyor Build status| image:: https://ci.appveyor.com/api/projects/status/en1u36q9tdqbaoh9/branch/master?svg=true
   :target: https://ci.appveyor.com/project/Kuree/kratos/branch/master
.. |PyPI - Version| image:: https://badge.fury.io/py/kratos.svg
   :target: https://pypi.org/project/kratos/
.. |Coverage| image:: https://codecov.io/gh/Kuree/kratos/branch/master/graph/badge.svg
  :target: https://codecov.io/gh/Kuree/kratos
.. |Documentation Status| image:: https://readthedocs.org/projects/kratos-doc/badge/?version=latest
   :target: https://kratos-doc.readthedocs.io/en/latest/?badge=latest
.. _hgdb: https://github.com/Kuree/hgdb
