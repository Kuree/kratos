Passes in Kratos
################

Kratos allows you to modify the entire design at any time before
the code generation step. The most efficient way to modify the
design is through passes. A pass is defined as a function that
takes a generator and change the generator in-place to produce
a different generator. There are roughly two kinds of passes
in kratos:

1. Application specific passes
2. Symbol-level passes


Application specific Passes
===========================

Application specific passes such as power domain insertion have
to be done with a particular domain knowledge. Since kratos
encourages you to fuse application information into the generator
class, writing a function to identify these information and act
accordingly can be very straightforward. This documentation will
focus on more systematic passes: symbol-level.

Symbol-Level Passes
===================
The internal IR in kratos is constructed as an abstract syntax
tree (AST) where each node is linked with a symbol. By visiting
the AST we can modify the IR as well as checking for errors.
This is very close to the passes in LLVM. Depending on whether
the pass mutates the IR, a pass is categorized as either a
analysis passes or a transformation pass. For instance, a pass
to extract all the debug information is an analysis pass since it
doesn't mutate any IR node. A module instantiation pass is a
transformation pass since it mutate the generate node to create
module instantiation statement.

Built-in Passes
===============

Kratos ships with many useful passes to make the verilog more
readable and your life easier:

- ``fix_assignment_type``: change ``Undefined`` assignment types
  into appropriate types. For instance, it will change top level
  assignments into blocking assignment, which will be code generated
  into ``assign`` statement.
- ``remove_unused_vars``: remove unused variables. It can be run
  multiple times after different passes to remove the artifacts.
- ``verify_generator_connectivity``: verify that each generator is
  connected properly.
- ``create_module_instantiation``: create module instantiation
  statement after user calls ``add_child_generator``.
- ``zero_out_stubs``: zero out the stub outputs.
- ``check_mixed_assignment``: check if there is any mixed
  blocking/non-blocking assignments in code blocks.
- ``hash_generators``: hash generators for code generation.
- ``decouple_generator_ports``: create extra variable to connect
  sub modules, if necessary.
- ``uniquify_generators``: assign different module name if two
  are indeed different
- ``generate_verilog``: verilog code generation pass.
- ``extract_struct_info``: extract packed struct information
- ``transform_if_to_case``: transform if statement into case statement
  if it determines appropriate. It is because Python doesn't have
  switch statement, the AST produce a chained if-else statement. This
  pass will handle that.
- ``remove_fanout_one_wires``: this pass remove unnecessary wires
- ``remove_pass_through_modules``: this pass will remove any pass-through
  modules created by user. It is not necessary for the physical design,
  but extremely helpful to reduce the simulation size.
- ``merge_wire_assignments``: this pass merges top level wire slices into
  a single wire assignment.

Write your own Pass
===================
Because kratos is based on C++ and binds to Python through pybind, there
are two ways to write a pass:

- C++
- Python

The procedure to add a pass is very similar. The function has to take
a top level ``Generator`` class the perform some analysis or transformation
on it. All the passes in kratos rely on the ``ASTVisitor`` class, which
recursively visit each symbols in the IR. For ``C++`` users you need to
check how the passes is done in `src/pass.cc`_, where all the passes listed
above are implemented there.

To write a pass in Python, you can inherit the class in the same way
as ``C++``. Here is an example that changes every generator's ``out``
port into ``test``

.. code-block:: Python

    def change_name(generator):
        class Visitor(ASTVisitor):
            def __init__(self):
                ASTVisitor.__init__(self)

            def visit(self, node):
                if isinstance(node, Port):
                    # rename the output port
                    if node.name == "out":
                        node.name = "test"

        visitor = Visitor()
        visitor.visit_root(generator)

To add the pass, you can add the pass into ``verilog`` function
call

.. code-block:: Python

    verilog(mod, additional_passes={"name_change": change_name})

At the time of writing there is no easy way to control the ordering of
additional passes. It is added to the every-end by default. If you want
to fine-control the ordering, you have to construct the ``kratos.PassManager``
by yourself and add all the necessary passes.


.. _src/pass.cc: https://github.com/Kuree/kratos/blob/master/src/pass.cc
