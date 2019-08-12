How to debug in Kratos
######################

kratos comes with a GUI to help you debug the system verilog it
generated. You need to install ``kratos-debug`` to use the tool:

.. code-block:: bash

    pip install kratos-debug

Once installed, you can do

.. code-block:: bash

    kratos-debug [src.sv]

It will launch a window as the one below:

.. image:: https://cdn.jsdelivr.net/gh/Kuree/kratos-debug@master/.images/screenshot.png
    :alt: screenshot

The left panel shows the generated verilog. You can click on any
line that's highlighted and the right panel will show you the source
code that's responsible for that particular line.

.. note::
    To use this feature, you have to set `debug=True` when initializing
    the ``Generator.__init__()``. In addition, you also need to
    use ``verilog(mod, debug=True, filename=[src.sv])`` when generating
    the verilog, where ``mod`` is the top generator, and ``[src.sv]``
    is the target system source file. The function will also produce
    ``[src.sv.].debug`` in the same directory as ``[src.sv]``. You
    need that file for ``kratos-debug``.

    You can slo turn the debug mode on on a global scale. You can think
    global debug as ``-g`` in C/C++ compilers.

    To do so, simply do

    .. code-block:: Python

        kratos.generator.set_global_debug(True)