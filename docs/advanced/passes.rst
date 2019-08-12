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
transformation pass since it mutates the generate node to create
a module instantiation statement.

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
- ``hash_generators_sequential``: hash generators for code generation
  sequentially. This not encouraged to use since it's slow.
- ``hash_generators_parallel``: hash generators for code generation.
  This is a lock-free thread-pool implementation of the hash function.
- ``remove_unused_stmts``: remove empty statements in top level.
- ``decouple_generator_ports``: create extra variable to connect
  sub modules, if necessary.
- ``uniquify_generators``: assign different module name if two
  are indeed different
- ``generate_verilog``: verilog code generation pass.
- ``extract_debug_info``: extract debug information.
- ``extract_struct_info``: extract packed struct information
- ``transform_if_to_case``: transform if statement into case statement
  if it determines appropriate. It is because Python doesn't have
  switch statement, the AST produce a chained if-else statement. This
  pass will handle that.
- ``remove_fanout_one_wires``: this pass removes unnecessary wires
- ``remove_pass_through_modules``: this pass will remove any pass-through
  modules created by user. It is not necessary for the physical design,
  but extremely helpful to reduce the simulation size.
- ``merge_wire_assignments``: this pass merges top level wire slices into
  a single wire assignment.
- ``insert_pipeline_stages``: this pass insert pipeline registers on the
  output. You need to add an attribute to the generator you want to
  insert. The type string should be ``pipeline`` and value string should
  be ``[num_stages]`` in string. If your generator has multiple clock
  inputs, you have to add an attribute with ``{pipeline_clk, port_name}``
  as well.
- ``zero_generator_inputs``: this is a pass that wires all child
  generator's un-connected inputs to zero. You need to add an attribute to
  the parent generator. The ``type_str`` should be ``zero_inputs``, no
  ``value_str`` needed. Notice that it only handles one-level down.
- ``change_port_bundle_struct``: automatically change the port bundle into
  packed struct whenever possible
- ``realize_fsm``: realize finite state machine into more basic primitives.
- ``check_function_return``: check return statement related bugs, such as
  missing return in some code blocks or unreachable code due to early
  return.
- ``sort_stmts``: sort the statements in the order of assignment, module
  instantiation, combinational, and sequential logic. This is off by default.


Write your own Pass
===================
Because kratos is based on C++ and binds to Python through pybind, there
are two ways to write a pass:

- C++
- Python

The procedure to add a pass is very similar. The function has to take
a top level ``Generator`` class then perform some analysis or transformation
on it. All the passes in kratos rely on the ``IRVisitor`` class, which
recursively visit each symbols in the IR. For ``C++`` users you need to
check how the passes is done in `src/pass.cc`_, where all the passes listed
above are implemented there.

To write a pass in Python, you can inherit the class in the same way
as ``C++``. Here is an example that changes every generator's ``out``
port into ``test``

.. code-block:: Python

    def change_name(generator):
        class Visitor(IRVisitor):
            def __init__(self):
                IRVisitor.__init__(self)

            def visit(self, node):
                if isinstance(node, Port):
                    # rename the output port
                    if node.name == "out":
                        node.name = "test"

        visitor = Visitor()
        visitor.visit_root(generator)

To add the pass, you can add the pass into ``verilog`` function
call. The additional passes will be executed at the very beginning.

.. code-block:: Python

    verilog(mod, additional_passes={"name_change": change_name})

If you want to control the ordering of the passes being executed, it is very
easy to do so in kratos. You can obtain a ``PassManager`` from ``VerilogModule``:

.. code-block:: Python

    code_gen = _kratos.VerilogModule(generator.internal_generator)
    pass_manager = code_gen.pass_manager()

Then you have to register your own passes using the following function call:

.. code-block:: Python

    pass_manager.register_pass(name, fn)

where ``name`` is the name to be registered in the ``PassManager`` and ``fn``
is the function. After pass registration, you can call ``add_pass(pass_name)``
to add passes in order, such as

.. code-block:: Python

    pass_manager.add_pass("fix_assignment_type")

After registering and adding passes, you can call ``code_gen.run_passes`` to
run all the passes in the order you give. To get verilog out, you can use
``code_gen.verilog_src()``, which returns a dictionary of verilog source code
indexed by the module name.

.. note::

    All the built-in passes have been pre-registered. You can just use
    the name to add the built-in passes.

.. _src/pass.cc: https://github.com/Kuree/kratos/blob/master/src/pass.cc

A note on parallelism
=====================

Kratos tries to speed up as much as possible by using a threadp pool. By
default, it uses up to half of the number of CPUs reported by your system.
This is to ensure the compilation won't interference with other jobs.
However, should you want to change this behavior, you can use
``_kratos.util.set_num_cpus(num)``` to change the behavior.

.. note::

    Due to Python's GIL, you cannot run a passes written in Python in
    parallel in kratos' backend. This is the technical limitation of
    Python.


Helper functions for your passes
================================

Kratos comes with many helper functions to make writing passes easier. Here
is a list of helper functions:

- ``[gen].replace(child_instance_name, new_child)``. This function replace
  the child generator ``child_instance_name`` with the new generator child
  ``new_child``, in the context of ``[gen]``, which is a ``Generator`` object.
  It does all the proper type checking and connection linking for you, in a
  very efficient manner.
- ``Var.move_src_to(old_var, new_var, parent_gen, keep_connection)``. This is
  a static function that moves the ``old_var``'s sources to ``new_var``, in
  the context of ``parent_gen``. If ``keep_connection`` is set to ``true``,
  it will create a wiring connection between the ``old_var`` and the
  ``new_var``. Notice that if you're using this function in Python, you have
  to call ``[gen].internal_generator`` to get the actual C++ generator
  object as ``parent_gen``.
- ``Var.move_sink_to(old_var, new_var, parent_gen, keep_connection)``. This is
  a static function that moves the ``old_var``'s sinks to ``new_var``, in
  the context of ``parent_gen``. This serves the similar functionality as
  ``Var.move_src_to()``.
