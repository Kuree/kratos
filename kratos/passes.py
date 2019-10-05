from _kratos.passes import *
from .generator import Generator
import _kratos
from .debug import dump_debug_database
from typing import Dict
import os


class Attribute(_kratos.passes.Attribute):
    def __init__(self):
        _kratos.passes.Attribute.__init__(self, self)


def verilog(generator: Generator, optimize_if: bool = True,
            optimize_passthrough: bool = True,
            optimize_fanout: bool = True,
            optimize_bundle: bool = True,
            reorder_stmts: bool = False,
            check_active_high: bool = True,
            debug: bool = False,
            additional_passes: Dict = None,
            extract_struct: bool = False,
            int_dpi_interface: bool = True,
            filename: str = None,
            output_dir: str = None,
            debug_db_filename: str = "",
            debug_top_name: str = "TOP",
            use_parallel: bool = True):
    code_gen = _kratos.VerilogModule(generator.internal_generator)
    pass_manager = code_gen.pass_manager()
    if additional_passes is not None:
        for name, fn in additional_passes.items():
            pass_manager.register_pass(name, fn)
            pass_manager.add_pass(name)
    # load all the passes
    # you can easily roll your own functions to control how the passes
    # are run

    pass_manager.add_pass("realize_fsm")
    if optimize_passthrough:
        pass_manager.add_pass("remove_pass_through_modules")
    if optimize_if:
        pass_manager.add_pass("transform_if_to_case")
    # fsm elaboration has to happen before unused vars removal
    pass_manager.add_pass("zero_out_stubs")
    if optimize_fanout:
        pass_manager.add_pass("remove_fanout_one_wires")
    pass_manager.add_pass("zero_generator_inputs")
    if optimize_bundle:
        pass_manager.add_pass("change_port_bundle_struct")
    pass_manager.add_pass("decouple_generator_ports")
    pass_manager.add_pass("fix_assignment_type")
    pass_manager.add_pass("remove_unused_vars")
    pass_manager.add_pass("remove_unused_stmts")
    pass_manager.add_pass("verify_assignments")
    pass_manager.add_pass("verify_generator_connectivity")
    pass_manager.add_pass("check_mixed_assignment")
    pass_manager.add_pass("check_always_sensitivity")
    pass_manager.add_pass("check_inferred_latch")
    if check_active_high:
        pass_manager.add_pass("check_active_high")
    pass_manager.add_pass("check_function_return")
    pass_manager.add_pass("merge_wire_assignments")
    # insert debug break points if needed
    if debug_db_filename:
        pass_manager.add_pass("inject_debug_break_points")
        pass_manager.add_pass("inject_clock_break_points")
    if use_parallel:
        pass_manager.add_pass("hash_generators_parallel")
    else:
        pass_manager.add_pass("hash_generators_sequential")
    pass_manager.add_pass("uniquify_generators")
    pass_manager.add_pass("create_module_instantiation")
    pass_manager.add_pass("insert_pipeline_stages")
    if reorder_stmts:
        pass_manager.add_pass("sort_stmts")

    code_gen.run_passes()
    if output_dir is not None:
        if not os.path.isdir(output_dir):
            os.makedirs(output_dir)
        package_name = generator.internal_generator.name + "_pkg"
        _kratos.passes.generate_verilog(generator.internal_generator,
                                        output_dir,
                                        package_name,
                                        debug)
        r = None
    else:
        src = code_gen.verilog_src()
        result = [src]
        gen = generator.internal_generator
        if debug:
            info = _kratos.passes.extract_debug_info(gen)
            result.append(info)
        else:
            info = {}

        if extract_struct or filename:
            struct_info = _kratos.passes.extract_struct_info(
                generator.internal_generator)
            if extract_struct:
                result.append(struct_info)
        else:
            struct_info = {}

        # dpi info
        dpi_func = _kratos.passes.extract_dpi_function(gen, int_dpi_interface)
        if len(dpi_func) > 0:
            result.append(dpi_func)

        if filename is not None:
            output_verilog(filename, src, info, struct_info, dpi_func)

        r = result[0] if len(result) == 1 else result

    # debug database
    if debug_db_filename:
        dump_debug_database(generator,
                            generator.internal_generator.handle_name(),
                            debug_db_filename)

    return r


def output_verilog(filename, mod_src, info, struct_info, dpi_func):
    line_no = 1
    debug_info = {}
    with open(filename, "w+") as f:
        for func_name in dpi_func:
            def_ = dpi_func[func_name]
            f.write(def_ + "\n")
        for struct_name in struct_info:
            def_ = struct_info[struct_name]
            f.write(def_ + "\n")

        mod_src_names = list(mod_src.keys())
        mod_src_names.sort()
        for mod_name in mod_src_names:
            src = mod_src[mod_name]
            mod_info = info[mod_name] if mod_name in info else {}
            lines = src.split("\n")
            for index, line in enumerate(lines):
                f.write(line + "\n")
                if index + 1 in mod_info:
                    debug_info[line_no] = mod_info[index + 1]
                line_no += 1

    if len(debug_info) > 0:
        with open(filename + ".debug", "w+") as f:
            import json
            json.dump(debug_info, f)
