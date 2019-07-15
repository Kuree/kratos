.. _verilog:

Generate System Verilog
#######################

kratos can only generate SystemVerilog. However, it only uses a subset
of SystemVerilog features that can be understood by most open-source
EDA tools such as ``verilator``.

kratos shipped with a simple helper function that generate verilog for
you:

.. code-block:: Python

    def verilog(generator: Generator, optimize_if: bool = True,
                optimize_passthrough: bool = True,
                optimize_fanout: bool = True,
                debug: bool = False,
                additional_passes: Dict = None,
                extra_struct: bool = False,
                filename:str = None):

The required argument ``generator`` has to be the top level circuit
you want to generate. The function returns a Python dictionary indexed
by module name. If you only want to generate a system verilog file,
you can provide a path to ``filename`` argument, which will output
all the module definition into a single file. The reset of the argument
wil be explained in advanced topics.
