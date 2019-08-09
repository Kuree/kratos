Kratos Functions
################

Functions in general have many benefits:

- It allows users to re-use existing code, thus improving debuggability
- It increases design readability and allows abstraction
- ...

Kratos has first-class support for functions that can turn python
functions into a nice looking system verilog functions, while keeping
the same semantics as in Python. The usage is very similar to how
free-style code blocks works, all you need is to mark your function
with ``@function``, which can be import from
``from kratos.func import function``. All the features in free-style
code such as static-elaboration is supported in kratos' functions.

Usage
=====

Here is an example of how to use functions. Notice that you can only
call the function inside a code block (this rule applies to both
free-style code blocks and procedural code generation.)

.. code-block:: Python

    from kratos.func import function

    class Mod(Generator):
        def __init__(self):
            super().__init__("mod")
            self._in = self.input("in", 2)
            self._out = self.output("out", 2)
            self._out2 = self.output("out2", 2)

            self.add_code(self.code)

        @function
        def update_out(self, value, predicate):
            self._out2 = value
            if predicate:
                return value + self._in
            else:
                return value

        def code(self):
            # because the types are inferred
            # implicit const conversion doesn't work here
            self._out = self.update_out(self._in, const(1, 1))

Notice that we can directly call the function as ``self.update_out()``
in the code block. This is the same semantics as normal Python function
calls. Below is the generated SystemVerilog.

.. code-block:: SystemVerilog

  module mod (
    input logic [1:0] in,
    output logic [1:0] out,
    output logic [1:0] out2
  );

  function update_out(
    input logic [1:0] value,
    input logic  predicate
  );
  begin
    out2 = value;
    if (predicate) begin
      return value + in;
    end
    else return value;
  end
  endfunction
  always_comb begin
    out = update_out (in, 1'h1);
  end
  endmodule   // mod

Debug
=====

Kratos will produce source map for debugging function definitions, the
same way as free-style code blocks. You can use ``kratos-debug`` to view
the source mapping.


Type Deduction and limitations
==============================

Kratos is type-safe by design. As a result, all the function call will
be type-checked at runtime. Similar to modern C++'s type deduction,
kratos can deduct types based on function invocations, which removes
the requirement of specifying types in the function definition. Kratos
will inspect the arguments in the function invocation and inspect the
types of each arguments and use that to construct the function
interface. This is convenient for users in most cases. However, that
also requires to to specify the type for constants as well. As shown
in the example above, you have to call ``const()`` to construct
a constant.
