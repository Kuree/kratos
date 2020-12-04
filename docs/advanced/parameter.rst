Generator Parameters
####################

Although it is perfectly fine to create different modules given different
generator parameters, sometimes it's much cleaner to create a "verilog"
parameter. Using this kind of parameter reduces the number of modules
being generated and make the code more readable. An example for this usage
is configuration registers, where the register enable is on if the address
matches with a fixed value. We can of course pass the fixed value, ``i``
into the system and make the generator name into ``config_ref_{i}``.
The problem comes when you have multiple configuration registers. With
kratos' parameter feature, you can specify the fixed value as a parameter,
just as in verilog.

Examples
========

Kratos allows you to either parameterize constant values or variable widths.
Although it's more restricted than what SystemVerilog offers, it should cover
the majority of use cases. You can also directly use Python's meta-programming
to parameterize your generators.

Here is the function definition for parameter

.. code-block:: Python

  def parameter(self, name: str, width: int, default_value=0,
                  is_signed: bool = False)
  # param is an alias of parameter
  def param(self, name: str, width: int, default_value=0,
            is_signed: bool = False)

Parameterize constant values
----------------------------

We can create a module that add ``value`` to the input and then output the
sum. Here is the python code that defines a module called ``add_value``. Here
we created a parameter called ``value``.

.. code-block:: Python

  class ParameterModule(kratos.Generator):
    def __init__(self, width):
        super().__init__("add_value")
        in_  = self.port("in", width, kratos.PortDirection.In)
        out_ = self.port("out", width, kratos.PortDirection.Out)
        self.value_param = self.param("value", width, default_value=0)
        self.add_stmt(out_.assign(in_ + self.value_param))

Here is the generated verilog:

.. code-block:: SystemVerilog

  module add_value (
    input logic [15:0] in,
    output logic [15:0] out
  );

  parameter value = 16'h0;
  assign out = in + value;
  endmodule   // add_value


To use the parameter in a parent generator, you can simply set the parameter
value on that generator instance. In the following example, we set the
parameter to ``42``.

.. code-block:: Python

    class ParentModule(kratos.Generator):
        def __init__(self):
            super().__init__("parent")
            width = 16
            self.port("in", width, kratos.PortDirection.In)
            self.port("out", width, kratos.PortDirection.Out)
            adder = ParameterModule(width)
            adder.value_param.value = 42
            self.add_child("adder", adder)
            self.wire(adder.ports["in"], self.ports["in"])
            self.wire(self.ports["out"], adder.ports["out"])

Here is the generated verilog for the parent module:

.. code-block:: SystemVerilog

  module parent (
    input logic [15:0] in,
    output logic [15:0] out
  );

  add_value #(
    .value(16'h2A)) adder (
    .out(out),
    .in(in)
  );

  endmodule   // parent

Parameterize variable width
---------------------------
When you create a port or a variable from the generator, you can pass in a
parameter as ``width``.

Here is an example on how to use it:

.. code-block:: Python

    mod = Generator("mod")
    param = mod.param("P", 4, 4)
    in_ = mod.input("in", param)
    out = mod.output("out", param)
    var = mod.var("v", param)
    mod.wire(var, in_)
    mod.wire(out, var * 2)

Here is generated SystemVerilog:

.. code-block:: SystemVerilog

  module mod #(parameter P = 4'h4)
  (
    input logic [P-1:0] in,
    output logic [P-1:0] out
  );

  logic  [P-1:0] v;
  assign v = in;
  assign out = v * 4'h2;
  endmodule   // mod
