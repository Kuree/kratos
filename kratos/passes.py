from _kratos.passes import *
from .generator import Generator
import _kratos
from typing import Dict


class Attribute(_kratos.passes.Attribute):
    def __init__(self):
        _kratos.passes.Attribute.__init__(self, self)


def verilog(generator: Generator, optimize_if: bool = True,
            optimize_passthrough: bool = True,
            optimize_fanout: bool = True,
            debug: bool = False,
            additional_passes: Dict = None,
            extra_struct: bool = False,
            filename: str = None,
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
    if optimize_passthrough:
        pass_manager.add_pass("remove_pass_through_modules")
    if optimize_if:
        pass_manager.add_pass("transform_if_to_case")
    pass_manager.add_pass("fix_assignment_type")
    pass_manager.add_pass("zero_out_stubs")
    if optimize_fanout:
        pass_manager.add_pass("remove_fanout_one_wires")
    pass_manager.add_pass("zero_generator_inputs")
    pass_manager.add_pass("decouple_generator_ports")
    pass_manager.add_pass("remove_unused_vars")
    pass_manager.add_pass("remove_unused_stmts")
    pass_manager.add_pass("verify_assignments")
    pass_manager.add_pass("verify_generator_connectivity")
    pass_manager.add_pass("check_mixed_assignment")
    pass_manager.add_pass("merge_wire_assignments")
    if use_parallel:
        pass_manager.add_pass("hash_generators_parallel")
    else:
        pass_manager.add_pass("hash_generators_sequential")
    pass_manager.add_pass("uniquify_generators")
    pass_manager.add_pass("create_module_instantiation")
    pass_manager.add_pass("insert_pipeline_stages")

    code_gen.run_passes()
    src = code_gen.verilog_src()
    result = [src]
    if debug:
        info = _kratos.passes.extract_debug_info(generator.internal_generator)
        result.append(info)
    else:
        info = {}

    if extra_struct:
        struct_info = _kratos.passes.extract_struct_info(
            generator.internal_generator)
        result.append(struct_info)
    else:
        struct_info = {}

    if filename is not None:
        output_verilog(filename, src, info, struct_info)

    return result[0] if len(result) == 1 else result


def output_verilog(filename, mod_src, info, struct_info):
    line_no = 1
    debug_info = {}
    with open(filename, "w+") as f:
        for struct_name in struct_info:
            def_ = struct_info[struct_name]
            f.write(def_ + "\n")

        for mod_name in mod_src:
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
