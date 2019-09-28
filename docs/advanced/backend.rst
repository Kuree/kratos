Use Kratos as a Backend
#######################

The front end Python package is the of the best examples on how to use Kratos'
backend API. In particular, `generator.py` shows how to wrap
``_kratos.Generator`` with a Python class. ``pyast.py`` shows how to to use
``ast`` module to convert Python code into Kratos's IR.

In general unless you're very familiar with the raw ``_kratos`` bindings, you
should use as much ``kratos`` wrappers as possible.


How to specify source mapping
=============================

Every IR element in Kratos has ``add_fn_ln`` functions which take a pair of
string and unsigned integer (filename and line number). The line number
reported from ``inspect`` module starts from 1, which is consistent from with
the Visual Studio Code Debugger.

When dumping the debug database, Kratos search the filename amd line number
from the source list starting from index 0. That means that you have to insert
your own DSL's source code location in the first entry. To do so, you can call
something like

.. code-block:: Python

    stmt.add_fn_ln(("/home/keyi/kratos/example/example.py", 10), True))

The extra ``True`` will ensure inserting at the front.

.. note::

    ``filename`` passed in has to be absolute path.

How to specify context/scope variables
======================================

Context/scope variables are variables that will be displayed during the
debugging once a breakpoint is hit. There are two different type of variables:

1. Local variables
2. Generator variables

Local variables are the ones accessible when the IR node is instantiated. You
can think as the ``locals()`` when a particular variable or statement is
generated. Local variables will be shown in the local scope in the debugger.

Generator variables are these accessible through ``self.XX``, where
``XX`` is the attribute name. Generator variable will be shown in the ``self``
object in the debugger. You can use ``setattr()`` to set ``Generator`` instance
to dynamically add the attributes.

You can use ``kratos.add_scope_context`` to set the context/scope variables
by providing the statement and locals.

.. note::

    Combined with local and generator variables, Kratos aims to capture the
    generation environment as if it's running in Python. To do so, it will
    store any ``int``, ``flaot``, ``str``, and ``bool`` variable as constants
    in the debug database. These values will be "replayed" during Verilog
    simulator to emulate the sense of source-level debugging.

How to store the debug information
==================================

When you call ``verilog`` function, you can specify ``debug_db_filename``
as a positional argument. This will dump the design infortion to the file.

.. note::

    You have to make sure to turn the debug on for any modules you are
    interested in. By default the debug option is off for every generator
    instance. You can either do ``[gen].debug = True``, or turn the global
    debug on (same as ``-g`` in ``gdb``) by calling
    ``kratos.set_global_debug(True)``.


You should see ``tests/test_debug.py`` for more usage information.
