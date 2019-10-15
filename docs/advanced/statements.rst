Procedural Code Generation in Depth
###################################

Kratos allows you to construct complex expressions and
statements programmatically. As hinted in :ref:`generator`, the python
free-style front-end uses the procedural code generation to support
the Python-style codes.

Expressions
===========

You can construct expression the same way you expect in Python or C++. You
can reuse old expressions by adding more operators to them.

Expression Stacking
-------------------
Some assignments may need complex expressions that span multiple variables.
This is very straightforward in kratos since kratos' expression is just an
ordinary Python/C++ object.

For instance, if we want to have a reduce summation on a list variables, you
can do this in Python

.. code-block:: Python

    vars = []
    for i in range(num_vars):
        vars.append(self.var("variable_{0}".format(i), width))

    sum = vars[0]
    for i in range(1, num_vars):
        sum = sum + vars[i]

    output = self.var("output", width)
    self.add_stmt(output.assign(sum))

In this example we create a list of variables that stored in ``vars`` with
``width``. Then we use ``sum`` to create the sum reduction. In the end, we
create a output variable and assign ``sum`` to the output using ``assign()``
function call. Notice that we add this assign statement into the top level
(using ``self``). We will cover more details about the assign statement below.
The generated verilog looks like below for this example code block when
``width = 16`` and ``num_vars = 4``.

.. code-block:: SystemVerilog

    logic  [15:0] variable_0;
    logic  [15:0] variable_1;
    logic  [15:0] variable_2;
    logic  [15:0] variable_3;
    logic  [15:0] output;
    assign output = ((variable_0 + variable_1) + variable_2) + variable_3;

Statements
==========
Statements are the building blocks of kratos IR. Each statement object has
it's parent block. The parent can either be the generator or another statement.
If it is generator, it has to be the following statement types
- ``SequentialCodeBlock``
- ``CombinationalCodeBlock``
- ``AssignStmt``

.. note::
    If a ``AssignStmt``'s parent is the generator, it will be a continuous
    assignment, i.e., ``assign var1 = var2``. Due to the backend optimization,
    the assign statement may not be realized into the verilog code. You should
    use the debugger if you want to debug the optimization and verilog code
    generation.

To add a statement to the generator, you can use

.. code-block:: Python

    [gen].add_stmt(stmt)

where ``[gen]`` can either be ``self`` in the generator or some generator
object.


``AssignStmt``
--------------
``AssignStmt`` is the mostly used statements. kratos provides ``assign``
function call to handle the directional assignment. As shown in the examples
below, to create an ``AssignStmt``, you can call

.. code-block:: Python

    var_to.assign(var_from)

Where the ``var_from`` is assigned to ``var_to``. Notice that kratos also
provides finer control over the assignment type by passing additional
flag:

.. code-block:: Python

    var_to.assign(var_from, AssignmentType.Blocking)

This will create a blocking assignment. If you don't provide the flag, kratos
will determine the assignment type at compile time. Since the compiler is
checking and validating the assignment type, it's recommended to just leave
it blank and let the compiler figure it out, unless you have some practical
reasons.


``SequentialCodeBlock``
-----------------------
Kratos's Python interface provides an easy way to create sequential code block.
Similar to verilog, the sequential block needs a sensitivity list. The
sensitivity list is constructed the same way as in the ``@always`` block. It's
in the format of ``List[Tuple[BlockEdgeType, Var]]``, i.e. a list of tuples.
You can either use ``BlockEdgeType.Posedge`` or ``BlockEdgeType.Negedge`` for
the first entry. The second entry is the variable/port defined in the
generator. You can obtained a sequential block by calling ``sequential`` from
the generator instance. For instance:

.. code-block:: Python

    clk = self.clock("clk")
    seq_block = self.sequential((posedge, clk))

This will produce the following verilog code:

.. code-block:: SystemVerilog

    input logic  clk
    // ...
    always @(posedge clk) begin
    end


To add more statements to it, you can construct other types of statements and
then call ``add_stmt(new_stmt)``, such as ``seq_block.add_stmt(new_stmt)``.

.. note::

    - By calling ``[gen].sequential()``, we implicitly add the sequential block
      into the generator. As a result, you don't have to call
      ``[gen].add_stmt(seq)`` to add to the generator.
    - All the assign statement in ``SequentialCodeBlock`` will be either
      converted or checked to make sure they're all non-blocking assignments.


``CombinationalCodeBlock``
--------------------------
``CombinationalCodeBlock`` is very similar to ``SequentialCodeBlock``, except
that they don't need a sensitivity list. To construct one, you can call

.. code-block:: Python

    comb_block = self.combinational()

Kratos will generate the following system verilog code:

.. code-block:: SystemVerilog

    always_comb begin
    end

You can add statements the same as ``SequentialCodeBlock`` by calling
``add_stmt``.

.. note::

    - By calling ``[gen].combinational()``, we implicitly add the combinational block
      into the generator. As a result, you don't have to call
      ``[gen].add_stmt(seq)`` to add to the generator.
    - All the assign statement in ``CombinationalCodeBlock`` will be either
      converted or checked to make sure they're all blocking assignments.

``SwitchStmt``
--------------

Switch statement allows you to construct ``case`` blocks in verilog. Similar
to C++ or verilog, you need to have a condition (target). In kratos, this
should be either an expression or a port/variable. You can add a switch
case by using ``add_switch_case(value, stmts)`` statement. You can provide
``None`` to ``value`` to specify the default case.

Here is an example on how can you can construct a switch statement:

.. code-block:: Python

    var = self.var("value", 16)
    var_1 = self.var("value1", 16)
    var_2 = self.var("value2", 16)
    stmt = SwitchStmt(var)
    # you can use a single statement
    stmt.case_(1, var_1.assign(1))
    stmt.case_(2, var_2.assign(1))
    # you can also pass in a list of statements
    stmt.case_(None, [var_1.assign(0),
                      var_2.assign(0)])
    # remember to add it to a either sequential or combinational code block!
    # we re-use the sequential block we created above.
    seq_block.add_stmt(stmt)

Here is the generated system verilog:

.. code-block:: SystemVerilog

    logic  [15:0] value;
    logic  [15:0] value1;
    logic  [15:0] value2;

    always @(posedge clk) begin
      case (value)
        default: begin
          value1 <= 16'h0;
          value2 <= 16'h0;
        end
        16'h2: begin
          value2 <= 16'h1;
        end
        16'h1: begin
          value1 <= 16'h1;
        end
      endcase
    end

``IfStmt``
----------
Similar to the ``SwitchStmt``, the ``IfStmt`` needs a condition/target as well.
An ``IfStmt`` has two parts, the then body and else body. You can add
statements to either body by calling ``add_then_stmt`` and ``add_else_stmt``.

Here is an example on how to construct an ``IfStmt``.

.. code-block:: Python

    var = self.var("var", 1)
    value = self.var("value", 1)

    if_ = IfStmt(var == 0)
    if_.then_(value.assign(1))
    if_.else_(value.assign(0))

    # remember to add it to a either sequential or combinational code block!
    # we re-use the combinational block we created above.
    comb_block.add_stmt(if_stmt)

Notice that by design choice kratos doesn't override ``__eq__`` in Python.
Unless it's changed you have to use ``eq`` function call.

Here is the generated verilog:

.. code-block:: SystemVerilog

    logic   value;
    logic   var;
    always_comb begin
      if (var == 1'h0) begin
        value = 1'h1;
      end
      else begin
        value = 1'h0;
      end
    end

.. note::
    If you have nested ``IfStmt``, in some cases the compiler may do some
    optimization to optimize them away. Please refer to the passes to
    see more details.

Syntax sugars
-------------

Kratos provides some syntax sugar to make statement creations less verbose.
You can call ``if_`` and ``switch_`` to create statements in a functional
manner. Notice that if you call ``if_`` and ``switch_`` directly from
``combinational`` and ``sequential``, the statements will be added to the
always block automatically.

For assignments, you can use functional call the assign the values, such as
``var_to(var_src)``. Here are some examples on the syntax sugars:

.. code-block:: Python

    mod = Generator("mod")
    out_ = mod.var("out", 1)
    in_ = mod.port("in", 1, PortDirection.In)
    comb = mod.combinational()
    comb.if_(in_ == 1).then_(out_(0)).else_(out_(1))

.. code-block:: Python

    mod = Generator("mod")
    out_ = mod.var("out", 1)
    in_ = mod.port("in", 1, PortDirection.In)
    comb = mod.combinational()
    comb.switch_(in_).case_(1, out_(1)).case_(0, out_(0))


Comments
--------

Almost every statement in kratos have an attribute called `comment`, you can
set it any comment you want. It will be generated as a comment above the
statement. For instance:

.. code-block:: Python

  stmt = a.assign(b)
  self.add_stmt(stmt)
  stmt.comment = "this is a comment"
  a.comment = "this is another comment"

When you're using ``always`` function, you don't have access to the stmt
object. In this case, you can use ``comment`` function. For instance,


.. code-block:: Python

    def code(self):
        comment("Another comment")
        self._out3 = self._in
