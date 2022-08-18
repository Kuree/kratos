#include "pass.hh"

#include <functional>
#include <iostream>
#include <mutex>
#include <numeric>

#include "codegen.hh"
#include "debug.hh"
#include "event.hh"
#include "except.hh"
#include "fmt/format.h"
#include "fsm.hh"
#include "generator.hh"
#include "interface.hh"
#include "port.hh"
#include "tb.hh"
#include "util.hh"

using fmt::format;
using std::runtime_error;

namespace kratos {

std::map<uint32_t, std::vector<std::pair<std::string, uint32_t>>> extract_debug_info_gen(
    Generator* top);

std::optional<std::pair<std::string, std::string>> get_target_var_name(const Var* var);

class UniqueGeneratorVisitor : public IRVisitor {
private:
    std::map<std::string, Generator*> generator_map_;

public:
    void visit(Generator* generator) override {
        if (generator_map_.find(generator->name) != generator_map_.end()) {
            return;
        }
        // a unique one
        if (!generator->external()) generator_map_.emplace(generator->name, generator);
    }
    const std::map<std::string, Generator*>& generator_map() const { return generator_map_; };
};

class MarkTrackedVisitor : public IRVisitor {
    void visit(Generator* generator) override {
        auto* context = generator->context();
        if (context) {
            track_lock_.lock();
            context->add_tracked_generator(generator);
            track_lock_.unlock();
        }
    }

    std::mutex track_lock_;
};

void track_generators(Generator* top) {
    // if we need to track if a generator has been touched for verilog
    if (top->context() && top->context()->track_generated()) {
        MarkTrackedVisitor track_visitor;
        track_visitor.visit_generator_root_p(top);
    }
}

std::map<std::string, std::string> generate_verilog(Generator* top) {
    // this pass assumes that all the generators has been uniquified
    std::map<std::string, std::string> result;
    // first get all the unique generators
    UniqueGeneratorVisitor unique_visitor;
    // this can be parallelized
    unique_visitor.visit_generator_root(top);
    auto const& generator_map = unique_visitor.generator_map();
    for (const auto& [module_name, module_gen] : generator_map) {
        SystemVerilogCodeGen codegen(module_gen);
        result.emplace(module_name, codegen.str());
    }
    track_generators(top);
    return result;
}

void generate_verilog(Generator* top, const std::string& output_dir,
                      const std::string& package_name, bool debug) {
    // input check
    if (package_name == top->name) {
        throw UserException(
            ::format("Package name cannot be the same as module name ({0}", top->name));
    }
    // this pass assumes that all the generators has been uniquified
    // first get all the unique generators
    UniqueGeneratorVisitor unique_visitor;
    // this can be parallelized
    unique_visitor.visit_generator_root_p(top);
    auto const& generator_map = unique_visitor.generator_map();
    track_generators(top);

    // we use header_name + ".svh"
    std::string header_filename = package_name + ".svh";
    std::map<std::string, std::string> result;
    for (const auto& [module_name, module_gen] : generator_map) {
        SystemVerilogCodeGen codegen(module_gen, package_name, header_filename);
        result.emplace(module_name, codegen.str());
    }
    // write out the content to the output_dir
    // we assume output_dir already exists
    // notice that if the content is the same, we don't override to avoid modifying the timestamps
    // this will help with incremental compile in the downstream tools, typically the commercial
    // ones
    // unfortunately verilator doesn't support incremental build. see
    // https://www.veripool.org/boards/2/topics/2822
    for (auto const& [module_name, src] : result) {
        auto path = kratos::fs::join(output_dir, module_name + ".sv");
        if (kratos::fs::exists(path)) {
            // load up the file
            std::ifstream in(path);
            std::stringstream content_stream;
            content_stream << in.rdbuf();
            std::string content = content_stream.str();
            if (content == src) continue;
        }
        // truncate mode
        std::ofstream out(path, std::ios::trunc);
        out << src;
        // tell the system where it went, if allowed
        auto gens = top->context()->get_generators_by_name(module_name);
        for (auto const& gen : gens) {
            if (gen->debug) gen->verilog_fn = path;
        }
    }
    // output debug info as well, if required
    if (debug) {
        for (const auto& [module_name, module_gen] : generator_map) {
            // use unique since we want to keep it close to where it's declared
            auto info = extract_debug_info_gen(module_gen);
            // a simple JSON writer
            std::stringstream json;
            json << "{" << std::endl;
            uint64_t count = 0;
            for (auto const& [line_num, lines] : info) {
                count++;
                json << "  \"" << line_num << "\": [";
                std::vector<std::string> entries;
                entries.reserve(lines.size());
                for (auto const& [f_name, f_ln] : lines) {
                    entries.emplace_back(::format("[\"{0}\", {1}]", f_name, f_ln));
                }
                json << string::join(entries.begin(), entries.end(), ", ") << "]";
                if (count != info.size())
                    json << "," << std::endl;
                else
                    json << std::endl;
            }
            json << "}" << std::endl;
            // just dump it since we don't care about incremental build for debug info
            auto debug_filename = kratos::fs::join(output_dir, module_name + ".sv.debug");
            std::ofstream debug_stream(debug_filename,
                                       std::ios::in | std::ios::out | std::ios::trunc);
            debug_stream << json.str();
        }
    }

    header_filename = kratos::fs::join(output_dir, header_filename);

    // compare it with the old one, if exists. this is for incremental build
    auto values = generate_sv_package_header(top, package_name, true);
    auto def_str = values.first;
    if (kratos::fs::exists(header_filename)) {
        std::ifstream in(header_filename);
        std::stringstream content_stream;
        content_stream << in.rdbuf();
        auto content = content_stream.str();
        if (content == def_str) {
            return;
        }
    }
    std::ofstream out(header_filename, std::ios::in | std::ios::out | std::ios::trunc);
    out << def_str;
}

void hash_generators(Generator* top, HashStrategy strategy) {
    // this is a helper function
    hash_generators_context(top->context(), top, strategy);
}

void uniquify_generators(Generator* top) {
    // we assume users has run the hash_generators function
    Context* context = top->context();
    auto const& names = context->get_generator_names();
    for (auto const& name : names) {
        auto const module_sets = context->get_generators_by_name(name);
        std::vector<Generator*> module_instances;
        module_instances.reserve(module_sets.size());
        for (auto const& m : module_sets) module_instances.emplace_back(m.get());
        // notice that since it is a set copied by value, it is fine to iterate through it
        if (module_instances.size() == 1)
            // only one module. we are good
            continue;
        // reordering based on whether it's being tracked
        if (context->track_generated()) {
            // O(n) algorithm. it does not need to be inplace
            uint64_t head = 0;
            for (uint64_t i = 0; i < module_instances.size(); i++) {
                if (context->is_generated_tracked(module_instances[i])) {
                    // swap
                    std::swap(module_instances[i], module_instances[head]);
                    head++;
                }
            }
        }
        std::unordered_map<uint64_t, Generator*> name_map;
        std::unordered_set<std::string> new_names;
        for (auto* const ptr : module_instances) {
            if (context->has_hash(ptr)) {
                uint64_t hash = context->get_hash(ptr);
                if (name_map.find(hash) == name_map.end()) {
                    // need to uniquify it
                    name_map.emplace(hash, ptr);
                    if (new_names.empty()) {
                        // use the original name
                        new_names.emplace(ptr->name);
                    } else {
                        // find a new one
                        uint32_t count = new_names.size() - 1;
                        while (true) {
                            const std::string new_name = ::format("{0}_unq{1}", name, count++);
                            if (!context->generator_name_exists(new_name)) {
                                context->change_generator_name(ptr, new_name);
                                break;
                            }
                        }
                        new_names.emplace(ptr->name);
                    }
                } else {
                    // re-use the old name
                    auto old_name = name_map.at(hash)->name;
                    context->change_generator_name(ptr, old_name);
                }
            }
        }
    }
}

void PassManager::register_pass(const std::string& name, std::function<void(Generator*)> fn) {
    if (has_pass(name))
        throw UserException(::format("{0} already exists in the pass manager", name));
    passes_.emplace(name, std::move(fn));
}

void PassManager::register_pass(const std::string& name, void(fn)(Generator*)) {
    if (has_pass(name))
        throw UserException(::format("{0} already exists in the pass manager", name));
    auto func = [=](Generator* generator) { (*fn)(generator); };
    passes_.emplace(name, func);
}

void PassManager::add_pass(const std::string& name) {
    if (!has_pass(name))
        throw UserException(::format("{0} doesn't exists in the pass manager", name));
    passes_order_.emplace_back(name);
}

void PassManager::run_passes(Generator* generator) {
    for (const auto& fn_name : passes_order_) {
        auto fn = passes_.at(fn_name);
        fn(generator);
    }
}

void PassManager::register_builtin_passes() {
    register_pass("remove_pass_through_modules", &remove_pass_through_modules);

    register_pass("transform_if_to_case", &transform_if_to_case);

    register_pass("fix_assignment_type", &fix_assignment_type);

    register_pass("zero_out_stubs", &zero_out_stubs);

    register_pass("remove_fanout_one_wires", &remove_fanout_one_wires);

    register_pass("decouple_generator_ports", &decouple_generator_ports);

    register_pass("remove_unused_vars", &remove_unused_vars);

    register_pass("remove_unused_stmts", &remove_unused_stmts);

    register_pass("verify_assignments", &verify_assignments);

    register_pass("verify_generator_connectivity", &verify_generator_connectivity);

    register_pass("check_mixed_assignment", &check_mixed_assignment);

    register_pass("merge_wire_assignments", &merge_wire_assignments);

    register_pass("merge_if_block", &merge_if_block);

    register_pass("zero_generator_inputs", &zero_generator_inputs);

    register_pass("change_port_bundle_struct", &change_port_bundle_struct);

    register_pass("realize_fsm", &realize_fsm);

    register_pass("check_function_return", &check_function_return);

    register_pass("sort_stmts", &sort_stmts);

    register_pass("check_active_high", &check_active_high);

    register_pass("check_non_synthesizable_content", &check_non_synthesizable_content);

    register_pass("inject_debug_break_points", &inject_debug_break_points);

    register_pass("inject_instance_ids", &inject_instance_ids);

    register_pass("insert_verilator_public", &insert_verilator_public);

    register_pass("remove_assertion", &remove_assertion);

    register_pass("check_always_sensitivity", &check_always_sensitivity);

    register_pass("check_inferred_latch", &check_inferred_latch);

    register_pass("check_multiple_driver", &check_multiple_driver);

    register_pass("check_combinational_loop", &check_combinational_loop);

    register_pass("check_flip_flop_always_ff", &check_flip_flop_always_ff);

    register_pass("propagate_scope_variable", &propagate_scope_variable);

    register_pass("change_property_into_stmt", &change_property_into_stmt);

    register_pass("merge_const_port_assignment", &merge_const_port_assignment);

    register_pass("remove_event_stmts", &remove_event_stmts);

    register_pass("lift_genvar_instances", &lift_genvar_instances);

    // TODO:
    //  add inline pass

    register_pass("hash_generators_parallel", &hash_generators_parallel);
    register_pass("hash_generators_sequential", &hash_generators_sequential);

    register_pass("uniquify_generators", &uniquify_generators);

    register_pass("create_module_instantiation", &create_module_instantiation);

    register_pass("create_interface_instantiation", &create_interface_instantiation);

    register_pass("insert_pipeline_stages", &insert_pipeline_stages);

    register_pass("auto_insert_clock_enable", &auto_insert_clock_enable);

    register_pass("auto_insert_sync_reset", &auto_insert_sync_reset);

    register_pass("ssa_transform_fix", &ssa_transform_fix);

    register_pass("port_legality_fix", &port_legality_fix);

    register_pass("dead_code_elimination", &dead_code_elimination);

    register_pass("inject_assertion_fail", &inject_assertion_fail);

    register_pass("sort_initial_stmts", &sort_initial_stmts);
}

}  // namespace kratos
