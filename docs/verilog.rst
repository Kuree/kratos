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
                optimize_bundle: bool = True,
                reorder_stmts: bool = False,
                check_active_high: bool = True,
                debug: bool = False,
                additional_passes: Dict = None,
                extrat_struct: bool = False,
                int_dpi_interface: bool = True,
                filename: str = None,
                output_dir: str = None,
                use_parallel: bool = True)

The required argument ``generator`` has to be the top level circuit
you want to generate. The function returns a Python dictionary indexed
by module name. If you only want to generate a system verilog file,
you can provide a path to ``filename`` argument, which will output
all the module definition into a single file. The reset of the argument
wil be explained in advanced topics.

Notice that we can also generate a group of SystemVerilog files by
specifying ``output_dir``. Every module definition will have its own
filename. If special construct is used, such as DPI function calls or
packed struct, ``definition.svh`` will be created in that directory and
all module files will include that header file. Kratos only override
the file content if it detects a change. This very useful for incremental
build for commercial simulators.

.. note::
    Once ``filename`` or ``output_dir`` is specified, the code generator
    will ignore ``extract_struct`` option to ensure the generated SystemVerilog
    code is correct.
