from _kratos.passes import *
from .generator import Generator
import _kratos
from .debug import dump_debug_database
from typing import Dict
import os


class Attribute(_kratos.passes.Attribute):
    def __init__(self):
        _kratos.passes.Attribute.__init__(self, self)


__generated_definitions = set()


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
            check_flip_flop_always_ff: bool = True,
            remove_unused: bool = True,
            merge_const_port_assignment: bool = True,
            debug_db_filename: str = "",
            ssa_transform: bool = False,
            use_parallel: bool = True,
            track_generated_definition: bool = False,
            contains_event: bool = False,
            lift_genvar_instances: bool = False,
            compile_to_verilog: bool = False):
    code_gen = _kratos.VerilogModule(generator.internal_generator)
    pass_manager = code_gen.pass_manager()
    if additional_passes is not None:
        for name, fn in additional_passes.items():
            pass_manager.register_pass(name, fn)
            pass_manager.add_pass(name)
    # load all the passes
    # you can easily roll your own functions to control how the passes
    # are run
    if remove_assertion:
        pass_manager.add_pass("remove_assertion")
    pass_manager.add_pass("realize_fsm")
    if ssa_transform:
        pass_manager.add_pass("ssa_transform_fix")
    if optimize_passthrough:
        pass_manager.add_pass("remove_pass_through_modules")
    if optimize_if:
        pass_manager.add_pass("merge_if_block")
        pass_manager.add_pass("transform_if_to_case")
    # fsm elaboration has to happen before unused vars removal
    pass_manager.add_pass("zero_out_stubs")
    if optimize_fanout:
        pass_manager.add_pass("remove_fanout_one_wires")
    pass_manager.add_pass("zero_generator_inputs")
    if optimize_bundle:
        pass_manager.add_pass("change_port_bundle_struct")
    pass_manager.add_pass("verify_generator_connectivity")
    if merge_const_port_assignment:
        pass_manager.add_pass("merge_const_port_assignment")
    pass_manager.add_pass("decouple_generator_ports")
    pass_manager.add_pass("fix_assignment_type")
    if remove_unused and not insert_debug_info:
        pass_manager.add_pass("remove_unused_vars")
        pass_manager.add_pass("remove_unused_stmts")
    pass_manager.add_pass("verify_assignments")
    if check_combinational_loop:
        pass_manager.add_pass("check_combinational_loop")
    pass_manager.add_pass("check_mixed_assignment")
    pass_manager.add_pass("check_always_sensitivity")
    if check_inferred_latch:
        pass_manager.add_pass("check_inferred_latch")
    if check_active_high:
        pass_manager.add_pass("check_active_high")
    pass_manager.add_pass("check_function_return")
    pass_manager.add_pass("merge_wire_assignments")
    if check_multiple_driver:
        pass_manager.add_pass("check_multiple_driver")
    if check_flip_flop_always_ff:
        pass_manager.add_pass("check_flip_flop_always_ff")
    # insert debug break points if needed
    if insert_debug_info:
        pass_manager.add_pass("propagate_scope_variable")
        pass_manager.add_pass("inject_instance_ids")
        pass_manager.add_pass("inject_debug_break_points")
        pass_manager.add_pass("inject_assert_fail_exception")
    if use_parallel:
        pass_manager.add_pass("hash_generators_parallel")
    else:
        pass_manager.add_pass("hash_generators_sequential")
    pass_manager.add_pass("change_property_into_stmt")
    pass_manager.add_pass("uniquify_generators")
    pass_manager.add_pass("create_module_instantiation")
    pass_manager.add_pass("create_interface_instantiation")
    # genvar instance lifting only happens after the module hash
    if lift_genvar_instances:
        pass_manager.add_pass("lift_genvar_instances")
    if insert_pipeline_stages:
        pass_manager.add_pass("insert_pipeline_stages")
    if reorder_stmts:
        pass_manager.add_pass("sort_stmts")

    code_gen.run_passes()

    # debug database
    if debug_db_filename:
        dump_debug_database(generator, debug_db_filename)

    # notice the ordering. we need to keep events passes but we don't
    # won't them in the codegen
    post_pass_manager = _kratos.passes.PassManager()
    post_pass_manager.register_builtin_passes()
    if contains_event:
        # need to remove the event statement since it doesn't have codegen
        post_pass_manager.add_pass("remove_event_stmts")
    post_pass_manager.run_passes(generator.internal_generator)

    if compile_to_verilog:
        assert output_dir is None and filename is not None,\
            "Trans-compile to verilog is only supported by a single file"
        import shutil
        assert shutil.which("sv2v") is not None,\
            "Compiling to verilog requires sv2v"

    if insert_verilator_info:
        _kratos.passes.insert_verilator_public(generator.internal_generator)

    if output_dir is not None:
        if not os.path.isdir(output_dir):
            os.makedirs(output_dir)
        package_name = generator.internal_generator.name + "_pkg"
        _kratos.passes.generate_verilog(generator.internal_generator,
                                        output_dir,
                                        package_name,
                                        debug_fn_ln)
        r = None
    else:
        src = code_gen.verilog_src()
        result = [src]
        gen = generator.internal_generator
        if debug_fn_ln:
            info = _kratos.passes.extract_debug_info(gen)
            result.append(info)
        else:
            info = {}

        # struct info
        struct_info = _kratos.passes.extract_struct_info(
            generator.internal_generator)
        if len(struct_info) > 0:
            result.append(struct_info)

        # dpi info
        dpi_func = _kratos.passes.extract_dpi_function(gen, int_dpi_interface)
        if len(dpi_func) > 0:
            result.append(dpi_func)
        enum_def = _kratos.passes.extract_enum_info(gen)
        if len(enum_def) > 0:
            result.append(enum_def)

        # interface info
        interface_info = _kratos.passes.extract_interface_info(gen)
        if len(interface_info) > 0:
            result.append(interface_info)

        if filename is not None:
            output_verilog(filename, src, info, struct_info, dpi_func, enum_def,
                           interface_info, track_generated_definition)
            if compile_to_verilog:
                pipe = os.popen("sv2v " + filename, "r")
                s = pipe.read()
                with open(filename, "w+") as f:
                    f.write(s)
            generator.internal_generator.verilog_fn = filename
        r = result[0] if len(result) == 1 else result

    return r


def output_verilog(filename, mod_src, info, struct_info, dpi_func, enum_def,
                   interface_info, track_generated_definition):
    line_no = 1
    debug_info = {}
    with open(filename, "w+") as f:
        definitions = [dpi_func, struct_info, enum_def, interface_info]
        for definition in definitions:
            for name, def_ in definition.items():
                if track_generated_definition \
                        and name in __generated_definitions:
                    continue
                lines = def_.split("\n")
                for line in lines:
                    f.write(line + "\n")
                    line_no += 1
                if track_generated_definition:
                    __generated_definitions.add(name)

        mod_src_names = list(mod_src.keys())
        mod_src_names.sort()
        for mod_name in mod_src_names:
            if track_generated_definition and \
                    mod_name in __generated_definitions:
                continue
            src = mod_src[mod_name]
            # get mod
            mods = Generator.get_context().get_generators_by_name(mod_name)
            for mod in mods:
                # fix the line number
                # need to subtract 1 since on the C++'s side already
                # has 1 offset
                _kratos.fix_verilog_ln(mod, line_no - 1)
            mod_info = info[mod_name] if mod_name in info else {}
            lines = src.split("\n")
            for index, line in enumerate(lines):
                f.write(line + "\n")
                if index + 1 in mod_info:
                    debug_info[line_no] = mod_info[index + 1]
                line_no += 1
            if track_generated_definition:
                __generated_definitions.add(mod_name)

    if len(debug_info) > 0:
        with open(filename + ".debug", "w+") as f:
            import json
            json.dump(debug_info, f)


def clear_context():
    Generator.clear_context()
    __generated_definitions.clear()
