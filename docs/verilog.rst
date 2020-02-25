.. _verilog:

Generate SystemVerilog
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
                debug_fn_ln: bool = False,
                additional_passes: Dict = None,
                int_dpi_interface: bool = True,
                remove_assertion: bool = False,
                check_inferred_latch: bool = True,
                check_multiple_driver: bool = True,
                check_combinational_loop: bool = True,
                insert_pipeline_stages: bool = False,
                filename: str = None,
                output_dir: str = None,
                insert_debug_info: bool = False,
                insert_verilator_info: bool = False,
                insert_break_on_edge: bool = False,
                check_flip_flop_always_ff: bool = True,
                debug_db_filename: str = "",
                use_parallel: bool = True,
                track_generated_definition: bool = False,
                compile_to_verilog: bool = False):

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

.. note::
    If old Verilog, e.g., Verilog-95, is required for some EDA tools, such as
    yosys, you can set ``compile_ti_verilog`` to ``True``, which will invoke
    ``sv2v`` to trans-compile the generated SystemVerilog code into plain
    Verilog code. You need to have ``sv2v`` in your ``PATH``. You can install
    it from the official website: https://github.com/zachjs/sv2v, or simply
    install the unofficial build ``pip install pysv2v``.