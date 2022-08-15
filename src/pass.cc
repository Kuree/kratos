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

class AssignmentTypeVisitor : public IRVisitor {
public:
    explicit AssignmentTypeVisitor(AssignmentType type, bool check_type = true)
        : type_(type), check_type_(check_type) {}
    void visit(AssignStmt* stmt) override {
        if (stmt->assign_type() == AssignmentType::Undefined) {
            stmt->set_assign_type(type_);
        } else if (check_type_ && stmt->assign_type() != type_) {
            throw VarException(
                ::format("mismatch in assignment type. should be {0}, got {1}",
                         assign_type_to_str(type_), assign_type_to_str(stmt->assign_type())),
                {stmt->left(), stmt->right()});
        }
    }

private:
    AssignmentType type_;
    bool check_type_;
};

class AssignmentTypeBlockVisitor : public IRVisitor {
    void visit(CombinationalStmtBlock* block) override {
        AssignmentTypeVisitor visitor(AssignmentType::Blocking, true);
        visitor.visit_root(block->ast_node());
    }
    void visit(SequentialStmtBlock* block) override {
        // attribute-based override
        auto const& attributes = block->get_attributes();
        for (auto const& attr : attributes) {
            if (attr->type_str == "check_assignment" && attr->value_str == "false") return;
        }
        AssignmentTypeVisitor visitor(AssignmentType::NonBlocking, true);
        visitor.visit_root(block->ast_node());
    }

    void visit(FunctionStmtBlock* block) override {
        AssignmentTypeVisitor visitor(AssignmentType::Blocking, true);
        visitor.visit_root(block->ast_node());
    }
};

void fix_assignment_type(Generator* top) {
    // first we fix all the block assignment
    AssignmentTypeBlockVisitor visitor;
    visitor.visit_root(top);
    visitor.visit_generator_root(top);

    // then we assign any existing assignment as blocking assignment
    AssignmentTypeVisitor final_visitor(AssignmentType::Blocking, false);
    final_visitor.visit_root(top->ast_node());
}

class ZeroGeneratorInputVisitor : public IRVisitor {
public:
    void visit(Generator* generator) override {
        // we only do that with generator that has attributes called "zero_inputs"
        // we don't care about the values
        auto attributes = generator->get_attributes();
        bool has_attribute = false;
        if (!attributes.empty()) {
            for (auto const& attr : attributes) {
                if (attr->type_str == "zero_inputs") {
                    has_attribute = true;
                    break;
                }
            }
        }
        if (has_attribute) {
            // compute unconnected
            // check each child generator
            auto children = generator->get_child_generators();
            for (auto const& gen : children) {
                auto port_names = gen->get_port_names();
                for (auto const& port_name : port_names) {
                    auto port = gen->get_port(port_name);
                    if (port->port_direction() == PortDirection::Out) continue;
                    std::unordered_set<uint32_t> bits;
                    bool is_connected = connected(port, bits);
                    if (!is_connected) {
                        // notice that we can two choices here:
                        // bit wiring and bulk wiring
                        // we will implement bulk wiring here since the merge wiring pass is not
                        // complete at the time of implementation
                        // compute the set difference
                        std::vector<uint32_t> diff_bits;
                        for (uint32_t i = 0; i < port->width(); i++) {
                            if (bits.find(i) == bits.end()) {
                                // no need to sort the bits since we're going in order
                                // so it's already sorted.
                                diff_bits.emplace_back(i);
                            }
                        }
                        // we will connect the size 1 easily
                        // however, if it's an array and sliced in a weird way, there is nothing
                        // easy we can do. for now we will throw an exception
                        // maximum the slices range
                        uint32_t low = diff_bits[0];
                        uint32_t high = low;
                        uint32_t pre_high = high;

                        // lambda functions to handle the situation
                        std::function<void(uint32_t, uint32_t)> wire_zero = [=](uint32_t h,
                                                                                uint32_t l) {
                            uint32_t ll, hh;
                            if (port->size().size() == 1 && port->size().front() == 1) {
                                ll = l;
                                hh = h;
                            } else {
                                if (l % port->var_width() || (h + 1) % port->var_width()) {
                                    // can't handle it right now
                                    auto stmts = std::vector<Stmt*>();
                                    stmts.reserve(port->sources().size());
                                    for (auto const& stmt : port->sources()) {
                                        stmts.emplace_back(stmt.get());
                                    }
                                    throw StmtException(
                                        "Cannot fix up unpacked array due to irregular slicing",
                                        stmts.begin(), stmts.end());
                                }
                                // compute the low and high
                                ll = l / port->var_width();
                                hh = h / port->var_width();
                            }
                            std::shared_ptr<AssignStmt> stmt;
                            // a special case is that the port is not connected at all!
                            if (ll == 0 && hh == (port->width() - 1)) {
                                stmt = port->assign(constant(0, port->width(), port->is_signed()));
                            } else {
                                auto& slice = port->operator[]({hh, ll});
                                stmt = slice.assign(constant(0, slice.width(), slice.is_signed()));
                            }
                            stmt->fn_name_ln.emplace_back(std::make_pair(__FILE__, __LINE__));
                            gen->add_stmt(stmt);
                        };

                        for (auto const bit : diff_bits) {
                            high = bit;
                            if (high - pre_high > 1) {
                                // there is a gap
                                wire_zero(pre_high, low);
                                low = high;
                                pre_high = low;
                            } else {
                                pre_high = high;
                            }
                        }
                        // the last bit
                        wire_zero(high, low);
                    }
                }
            }
        }
    }
};

void zero_generator_inputs(Generator* top) {
    ZeroGeneratorInputVisitor visitor;
    visitor.visit_generator_root_p(top);
}

class ModuleInstantiationVisitor : public IRVisitor {
public:
    void visit(Generator* generator) override {
        for (auto& child : generator->get_child_generators()) {
            // skip if already instantiated
            if (child->has_instantiated()) continue;
            // create instantiation statement
            auto stmt = std::make_shared<ModuleInstantiationStmt>(child.get(), generator);
            if (generator->debug) {
                // get the debug info from the add_generator, if possible
                auto debug_info = generator->children_debug();
                if (debug_info.find(child->instance_name) != debug_info.end()) {
                    auto info = debug_info.at(child->instance_name);
                    stmt->fn_name_ln.emplace_back(info);
                }
                stmt->fn_name_ln.emplace_back(std::make_pair(__FILE__, __LINE__));
            }
            auto comment = generator->get_child_comment(child->instance_name);
            if (!comment.empty()) stmt->comment = comment;
            generator->add_stmt(stmt);
            // remove the stmts that's fold into the instantiation statement
            for (auto const& st : stmt->connection_stmt()) {
                st->remove_from_parent();
            }
            child->set_instantiation_stmt(stmt.get());
        }
    }
};

void create_module_instantiation(Generator* top) {
    ModuleInstantiationVisitor visitor;
    visitor.visit_generator_root(top);
}

class InterfaceInstantiationVisitor : public IRVisitor {
public:
    void visit(Generator* generator) override {
        const auto& interfaces = generator->interfaces();
        for (auto const& [name, interface] : interfaces) {
            if (interface->has_instantiated()) continue;
            if (interface->is_port()) continue;
            auto stmt = std::make_shared<InterfaceInstantiationStmt>(generator, interface.get());
            generator->add_stmt(stmt);

            // remove the stmts that's fold into the instantiation statement
            for (auto const& st : stmt->connection_stmt()) {
                st->remove_from_parent();
            }
        }
    }
};

void create_interface_instantiation(Generator* top) {
    InterfaceInstantiationVisitor visitor;
    visitor.visit_generator_root_p(top);
}

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

class GeneratorPortVisitor : public IRVisitor {
public:
    void visit(Generator* generator) override {
        if (!generator->parent()) {
            // this is top level module, no need to worry about it
            return;
        }
        auto const& port_names = generator->get_port_names();

        for (auto const& port_name : port_names) {
            auto port = generator->get_port(port_name);
            process_port(generator, port.get(), port_name);
        }
        // for internal interface ports
        const auto& interfaces = generator->interfaces();
        for (auto const& iter : interfaces) {
            auto const& interface = iter.second;
            auto const& ports = interface->ports();
            for (auto const& [port_name, port] : ports) {
                process_port(generator, port, port_name);
            }
        }
    }

private:
    static inline bool correct_src_type(Var* src, Generator* generator) {
        return src->type() == VarType::Base || src->type() == VarType::ConstValue ||
               src->type() == VarType::Parameter ||
               (src->type() == VarType::PortIO && src->parent() == generator->parent());
    }

    static void process_port(Generator* generator, Port* port, const std::string& port_name) {
        auto const port_direction = port->port_direction();
        if (port_direction == PortDirection::In) {
            const auto& sources = port->sources();
            // unless it's driven by a single var or port, we need to duplicate
            // the variable
            if (sources.size() == 1) {
                const auto& stmt = *sources.begin();
                if (stmt->parent()->ir_node_kind() == IRNodeKind::GeneratorKind &&
                    stmt->left() == port) {
                    // the sink has to be it self
                    auto* src = stmt->right();
                    if (correct_src_type(src, generator) ||
                        // here we are okay with input sliced in
                        (src->type() == VarType::Slice &&
                         src->generator() == generator->parent())) {
                        // remove it from the parent generator
                        src->generator()->remove_stmt(stmt);
                        return;
                    }
                }
            }
            // create a new variable
            auto* ast_parent = generator->parent();
            if (!ast_parent)
                throw GeneratorException(
                    ::format("{0}'s parent is empty but it's not a top module", generator->name),
                    {generator});
            auto* parent = reinterpret_cast<Generator*>(ast_parent);
            auto new_name = parent->get_unique_variable_name(generator->instance_name, port_name);
            if (port->is_struct()) {
                auto packed = port->as<PortPackedStruct>();
                parent->var_packed(new_name, packed->packed_struct());
            } else {
                auto& v = parent->var(new_name, port->var_width(), port->size(), port->is_signed());
                v.set_is_packed(port->is_packed());
                v.set_explicit_array(port->explicit_array());
            }
            Var* var = parent->get_var(new_name).get();
            // be careful about the port type. if it's special type, it needs properly casted
            const static std::unordered_map<PortType, VarCastType> cast_maps = {
                {PortType::Clock, VarCastType::Clock},
                {PortType::AsyncReset, VarCastType::AsyncReset},
                {PortType::Reset, VarCastType::Reset},
                {PortType::ClockEnable, VarCastType::ClockEnable}};
            if (cast_maps.find(port->port_type()) != cast_maps.end()) {
                var = var->cast(cast_maps.at(port->port_type())).get();
            }
            if (parent->debug) {
                // need to copy over the changes over
                var->fn_name_ln = std::vector<std::pair<std::string, uint32_t>>(
                    port->fn_name_ln.begin(), port->fn_name_ln.end());
                var->fn_name_ln.emplace_back(std::make_pair(__FILE__, __LINE__));
            }
            // replace all the sources
            Var::move_src_to(port, var, parent, true);
        } else if (port_direction == PortDirection::Out) {
            // same logic as the port dir in
            // if we're connected to a base variable, we are good
            const auto& sinks_ = port->sinks();
            // we are only interested in parent level port connection
            std::unordered_set<std::shared_ptr<AssignStmt>> sinks;
            for (auto const& stmt : sinks_) {
                if (stmt->generator_parent() == port->generator()->parent_generator())
                    sinks.emplace(stmt);
            }
            if (sinks.empty()) {
                return;
            }
            // special case where if the sink is parent's port, this is fine
            if (sinks.size() == 1) {
                auto stmt = *(sinks.begin());
                auto* src = stmt->left();
                bool correct_src_type_;
                if (!src->is_interface()) {
                    // as long as it is not an expression, it is fine
                    correct_src_type_ = correct_src_type(src, generator);
                } else {
                    correct_src_type_ = true;
                }
                if (stmt->parent()->ir_node_kind() == IRNodeKind::GeneratorKind &&
                    correct_src_type_ && src->generator() == generator->parent() &&
                    stmt->right() == port) {
                    // remove it from the parent generator
                    stmt->remove_from_parent();
                    return;
                }
            }
            // create a new variable
            auto* ast_parent = generator->parent();
            if (!ast_parent)
                throw GeneratorException(
                    ::format("{0}'s parent is empty but it's not a top module", generator->name),
                    {generator});
            auto* parent = reinterpret_cast<Generator*>(ast_parent);
            auto new_name = parent->get_unique_variable_name(generator->instance_name, port_name);
            if (port->is_struct()) {
                auto packed = port->as<PortPackedStruct>();
                parent->var_packed(new_name, packed->packed_struct());
            } else {
                auto& v = parent->var(new_name, port->var_width(), port->size(), port->is_signed());
                v.set_is_packed(port->is_packed());
                v.set_explicit_array(port->explicit_array());
            }
            auto var = parent->get_var(new_name);
            if (parent->debug) {
                // need to copy over the changes over
                var->fn_name_ln = std::vector<std::pair<std::string, uint32_t>>(
                    port->fn_name_ln.begin(), port->fn_name_ln.end());
                var->fn_name_ln.emplace_back(std::make_pair(__FILE__, __LINE__));
            }
            // replace all the sources
            Var::move_sink_to(port, var.get(), parent, true);
        } else {
            throw InternalException("Not implement yet");
        }
    }
};

void decouple_generator_ports(Generator* top) {
    GeneratorPortVisitor visitor;
    visitor.visit_generator_root(top);
}

class StubGeneratorVisitor : public IRVisitor {
public:
    void visit(Generator* generator) override {
        if (!generator->is_stub()) return;
        // to be a stub, there shouldn't be any extra variables
        if (generator->stmts_count() > 0) {
            throw ::runtime_error(::format("{0} is marked as a stub but contains statements"));
        }

        // has to be the exact same number of ports and vars, otherwise it means there are
        // some variables being declared
        auto vars = generator->get_vars();
        auto ports = generator->get_port_names();
        if (!vars.empty()) {
            throw GeneratorException(
                fmt::format("{0} is declared as stub but has declared variables", generator->name),
                {generator});
        }

        for (auto const& port_name : ports) {
            auto port = generator->get_port(port_name);
            if (port->port_direction() == PortDirection::In) {
                if (!port->sinks().empty())
                    throw VarException(
                        fmt::format("{0}.{1} is driving a net, but {0} is declared as a stub",
                                    generator->name, port_name),
                        {port.get(), generator});
            } else {
                if (!port->sources().empty())
                    throw VarException(
                        fmt::format("{0}.{1} is driven by a net, but {0} is declared as a stub",
                                    generator->name, port_name),
                        {port.get(), generator});
                generator->add_stmt(port->assign(constant(0, port->width())));
            }
        }
    }
};

void zero_out_stubs(Generator* top) {
    StubGeneratorVisitor visitor;
    visitor.visit_generator_root_p(top);
}

// this is only for visiting the vars and assignments in the current generator
class DebugInfoVisitor : public IRVisitor {
public:
    void visit(Var* var) override { add_info(var); }
    void visit(Expr* expr) override { add_info(expr); }
    void visit(EnumVar* var) override { add_info(var); }
    void visit(EnumConst* var) override { add_info(var); }

    void inline visit(AssignStmt* stmt) override { add_info(stmt); }

    void visit(Port* var) override { add_info(var); }

    void visit(SwitchStmt* stmt) override { add_info(stmt); }

    void inline visit(SequentialStmtBlock* stmt) override { add_info(stmt); }

    void inline visit(CombinationalStmtBlock* stmt) override { add_info(stmt); }

    void inline visit(ModuleInstantiationStmt* stmt) override { add_info(stmt); }

    void inline visit(IfStmt* stmt) override { add_info(stmt); }

    void inline visit(FunctionCallStmt* stmt) override { add_info(stmt); }

    void inline visit(FunctionStmtBlock* stmt) override { add_info(stmt); }

    void inline visit(ReturnStmt* stmt) override { add_info(stmt); }

    std::map<uint32_t, std::vector<std::pair<std::string, uint32_t>>>& result() { return result_; }

private:
    void inline add_info(Stmt* stmt) {
        if (!stmt->fn_name_ln.empty() && stmt->verilog_ln != 0) {
            result_.emplace(stmt->verilog_ln, stmt->fn_name_ln);
        }
    }

    void inline add_info(Var* var) {
        if (!var->fn_name_ln.empty() && var->verilog_ln != 0 &&
            result_.find(var->verilog_ln) == result_.end()) {
            result_.emplace(var->verilog_ln, var->fn_name_ln);
        }
    }

    std::map<uint32_t, std::vector<std::pair<std::string, uint32_t>>> result_;
};

class GeneratorDebugVisitor : public IRVisitor {
public:
    void visit(Generator* generator) override {
        if (result_.find(generator->name) != result_.end()) return;
        if (!generator->fn_name_ln.empty()) {
            DebugInfoVisitor visitor;
            visitor.result().emplace(1, generator->fn_name_ln);
            visitor.visit_content(generator);
            result_.emplace(generator->name, visitor.result());
        }
    }

    const std::map<std::string, std::map<uint32_t, std::vector<std::pair<std::string, uint32_t>>>>&
    result() {
        return result_;
    }

private:
    std::map<std::string, std::map<uint32_t, std::vector<std::pair<std::string, uint32_t>>>>
        result_;
};

std::map<std::string, std::map<uint32_t, std::vector<std::pair<std::string, uint32_t>>>>
extract_debug_info(Generator* top) {
    GeneratorDebugVisitor visitor;
    visitor.visit_generator_root(top);
    return visitor.result();
}

std::map<uint32_t, std::vector<std::pair<std::string, uint32_t>>> extract_debug_info_gen(
    Generator* top) {
    GeneratorDebugVisitor visitor;
    visitor.visit_content(top);
    auto result = visitor.result();
    if (result.size() != 1) {
        throw InternalException(
            ::format("Unable to extract debug info from the particular generator {0}", top->name));
    }
    auto entry = result.begin();
    return (*entry).second;
}

class PortBundleVisitor : public IRVisitor {
public:
    void visit(Generator* generator) override {
        auto const& mappings = generator->port_bundle_mapping();
        for (auto const& [entry_name, ref] : mappings) {
            const auto& mapping = ref->name_mappings();
            PortDirection dir = PortDirection::InOut;
            bool initialized = false;
            bool same_direction = true;
            for (auto const& iter : mapping) {
                auto port_name = iter.second;
                auto port = generator->get_port(port_name);
                // all the ports have to have the same direction
                if (!initialized) {
                    initialized = true;
                    dir = port->port_direction();
                } else {
                    if (dir != port->port_direction()) {
                        same_direction = false;
                        break;
                    }
                }
                if (port->size().size() != 1 || port->size().front() > 1) {
                    // TODO: upgrade packed struct to support array
                    same_direction = false;
                    break;
                }
            }
            if (same_direction && dir != PortDirection::InOut && !mapping.empty()) {
                // this is the one we need to convert
                auto bundle_name = ref->def_name();
                bundle_mapping_[bundle_name].emplace_back(std::make_pair(entry_name, generator));
            }
        }
    }

    const std::map<std::string, std::vector<std::pair<std::string, Generator*>>>& bundle_mapping() {
        return bundle_mapping_;
    }

private:
    std::map<std::string, std::vector<std::pair<std::string, Generator*>>> bundle_mapping_;
};

void merge_bundle_mapping(
    const std::map<std::string, std::vector<std::pair<std::string, Generator*>>>& old_mapping) {
    for (auto const& [bundle_name, generators] : old_mapping) {
        std::map<Generator*, uint64_t> bundle_hashs;
        std::shared_ptr<PortBundleRef> ref_port_ref;
        Generator* ref_generator = nullptr;
        for (auto const& [entry_name, generator] : generators) {
            auto ref = generator->get_bundle_ref(entry_name);
            auto mappings = ref->name_mappings();
            std::vector<std::string> ports;
            ports.reserve(mappings.size());
            for (auto const& iter : mappings) {
                ports.emplace_back(iter.first);
            }
            std::sort(ports.begin(), ports.end());
            std::string base_str;
            for (auto const& port_name : ports) {
                auto port = generator->get_port(mappings.at(port_name));
                base_str.append(::format("{0}{1}{2}{3}", port->var_width(), port->width(),
                                         port->is_signed(), port_name));
            }
            uint64_t hash = hash_64_fnv1a(base_str.c_str(), base_str.size());
            if (bundle_hashs.find(generator) != bundle_hashs.end()) {
                if (bundle_hashs.at(generator) != hash)
                    throw UserException(::format(
                        "Port bundle with same name {0} have different definition", bundle_name));
            }
            bundle_hashs.emplace(generator, hash);

            ref_generator = generator;
            ref_port_ref = ref;
        }
        // for now we require the naming of the bundle has to be the same
        bool initialized = false;
        uint64_t base_hash = 0;
        for (auto const& iter : bundle_hashs) {
            uint64_t hash = iter.second;
            if (!initialized) {
                initialized = true;
                base_hash = hash;
            } else {
                if (base_hash != hash) {
                    throw UserException(::format(
                        "Port bundle with same name {0} have different definition", bundle_name));
                }
            }
        }
        if (!ref_generator) throw InternalException("ref generator cannot be null");
        // create a packed struct
        std::vector<std::tuple<std::string, uint32_t, bool>> def;
        auto const& mapping = ref_port_ref->name_mappings();
        for (auto const& [var_name, real_name] : mapping) {
            auto port = ref_generator->get_port(real_name);
            def.emplace_back(std::make_tuple(var_name, port->width(), port->is_signed()));
        }
        auto struct_ = std::make_shared<PackedStruct>(bundle_name, def);
        for (auto const& [entry_name, generator] : generators) {
            auto* p = dynamic_cast<Generator*>(generator->parent());
            // move sources around the ports
            auto ref = generator->get_bundle_ref(entry_name);
            auto const& m = ref->name_mappings();
            auto dir = generator->get_port(m.begin()->second)->port_direction();
            auto& packed = generator->port_packed(dir, entry_name, struct_);

            for (auto const& [attr, real_name] : m) {
                auto target = generator->get_port(real_name);
                auto& slice = packed[attr];
                if (dir != target->port_direction())
                    throw InternalException("Direction doesn't match");
                // depends on the direction, the parent can change;
                if (dir == PortDirection::In) {
                    if (p) {
                        Var::move_src_to(target.get(), &slice, p, false);
                    }
                    Var::move_sink_to(target.get(), &slice, generator, false);
                } else {
                    Var::move_src_to(target.get(), &slice, generator, false);
                    if (p) {
                        Var::move_sink_to(target.get(), &slice, p, false);
                    }
                }
                // remove target
                generator->remove_port(real_name);
            }
            // remove bundle info
            generator->remove_bundle_port_ref(entry_name);
        }
    }
}

void change_port_bundle_struct(Generator* top) {
    // pass to extract all the bundles
    PortBundleVisitor b_visitor;
    // this cannot be parallelized if we don't use a lock
    b_visitor.visit_generator_root(top);
    merge_bundle_mapping(b_visitor.bundle_mapping());
}

class FSMVisitor : public IRVisitor {
public:
    void visit(Generator* generator) override {
        if (generator->is_cloned()) return;
        for (auto const& iter : generator->fsms()) {
            if (!iter.second->realized() && !iter.second->parent_fsm()) iter.second->realize();
        }
    }
};

void realize_fsm(Generator* top) {
    FSMVisitor visitor;
    visitor.visit_generator_root_p(top);
}

class SortStmtVisitor : public IRVisitor {
public:
    void visit(Generator* top) override {
        auto stmts = top->get_all_stmts();
        std::vector<std::shared_ptr<Stmt>> var_assignments;
        std::vector<std::shared_ptr<Stmt>> module_inst_assignments;
        std::vector<std::shared_ptr<Stmt>> combinational_assignments;
        std::vector<std::shared_ptr<Stmt>> sequential_assignments;
        std::vector<std::shared_ptr<Stmt>> latch_assignments;
        auto lists = {&var_assignments, &module_inst_assignments, &latch_assignments,
                      &combinational_assignments, &sequential_assignments};
        for (auto* assign : lists) assign->reserve(stmts.size());

        for (auto const& stmt : stmts) {
            if (stmt->type() == StatementType::Assign) {
                var_assignments.emplace_back(stmt);
            } else if (stmt->type() == StatementType::Block) {
                auto block = stmt->as<StmtBlock>();
                if (block->block_type() == StatementBlockType::Combinational) {
                    combinational_assignments.emplace_back(stmt);
                } else if (block->block_type() == StatementBlockType::Sequential) {
                    sequential_assignments.emplace_back(stmt);
                } else if (block->block_type() == StatementBlockType::Latch) {
                    latch_assignments.emplace_back(stmt);
                } else {
                    throw StmtException("Unrecognized statement block in top level", {stmt.get()});
                }
            } else if (stmt->type() == StatementType::ModuleInstantiation) {
                module_inst_assignments.emplace_back(stmt);
            } else {
                throw StmtException("Statement cannot be in the top level", {stmt.get()});
            }
        }

        uint64_t size = std::accumulate(lists.begin(), lists.end(), 0,
                                        [](uint64_t s, auto lst) { return s + lst->size(); });
        if (size != stmts.size()) throw InternalException("Unable to sort all the statements");
        std::vector<std::shared_ptr<Stmt>> result;
        result.reserve(stmts.size());
        for (auto* assign : lists) result.insert(result.end(), assign->begin(), assign->end());
        if (result.size() != stmts.size())
            throw InternalException("Unable to sort all the statements");
        top->set_stmts(result);
    }
};

void sort_stmts(Generator* top) {
    SortStmtVisitor visitor;
    visitor.visit_generator_root_p(top);
}

class TriggerConditionVisitor : public IRVisitor {
public:
    void visit(Var* var) override {
        auto base_name = var->get_var_root_parent()->base_name();
        values.emplace(base_name);
    }

    std::unordered_set<std::string> values;
};

std::string get_trigger_attribute(const std::shared_ptr<StmtBlock>& blk) {
    TriggerConditionVisitor visitor;
    visitor.visit_root(blk.get());
    auto const& values = visitor.values;
    if (values.empty()) return "";
    return string::join(values.begin(), values.end(), " ");
}

class SSATransformFixVisitor : public IRVisitor {
public:
    void visit(Generator* gen) override {
        auto stmts = gen->get_all_stmts();
        for (auto const& stmt : stmts) {
            if (stmt->type() == StatementType::Block && stmt->has_attribute("ssa")) {
                auto blk_stmt = stmt->as<StmtBlock>();
                if (blk_stmt->block_type() == StatementBlockType::Combinational) {
                    process_always_comb(blk_stmt);
                }
            }
        }
    }

private:
    static void process_always_comb(const std::shared_ptr<StmtBlock>& blk) {
        // also need to fix the scope variables
        // we assume that every statement here has been SSA transformed
        using SymbolMapping = std::unordered_map<std::string, std::string>;
        uint64_t current_scope = 1;
        std::unordered_map<uint64_t, SymbolMapping> symbol_mappings = {{current_scope, {}}};
        std::unordered_set<Stmt*> stmts;
        auto trigger_str = get_trigger_attribute(blk);
        for (auto const& stmt : *blk) {
            if (stmt->type() != StatementType::Assign)
                throw StmtException("Invalid SSA transform", {stmt.get()});
            auto assign_stmt = stmt->as<AssignStmt>();
            auto* left = assign_stmt->left();
            auto scope_id = get_target_scope(left);
            if (scope_id) {
                // detect when to start a new scope
                if (current_scope != *scope_id) {
                    // copy current scope to the new one
                    auto const& current_mapping = symbol_mappings.at(current_scope);
                    symbol_mappings[*scope_id] = {};
                    for (auto const& iter : current_mapping) {
                        symbol_mappings[*scope_id].emplace(iter);
                    }
                }
                current_scope = *scope_id;
            }
            auto& symbol_mapping = symbol_mappings.at(current_scope);
            // every statement is assign, and every variable should have been SSA transformed
            auto parse_result = get_target_var_name(left);
            if (!parse_result) throw StmtException("Invalid SSA transform", {stmt.get()});
            auto const& [target_scope_name, target_var_name] = *parse_result;
            // look into its scope variables
            auto const& scope = stmt->scope_context();
            std::map<std::string, std::pair<bool, std::string>> new_scope;
            for (auto const& [name, var_map] : scope) {
                auto const& [is_var, var_name] = var_map;
                if (is_var && symbol_mapping.find(name) != symbol_mapping.end()) {
                    new_scope.emplace(name, std::make_pair(true, symbol_mapping.at(name)));
                } else {
                    // just put it in the new scope
                    new_scope.emplace(name, var_map);
                }
            }
            stmt->set_scope_context(new_scope);

            // just update the table name
            // update symbol after the scope since the left side hasn't showed up in scope yet
            symbol_mapping[target_scope_name] = left->to_string();

            // set the trigger property
            auto trigger_attribute = std::make_shared<Attribute>();
            trigger_attribute->type_str = "ssa-trigger";
            trigger_attribute->value_str = trigger_str;
            stmt->add_attribute(trigger_attribute);
        }
    }

    static std::optional<uint64_t> get_target_scope(const Var* var) {
        auto const& attrs = var->get_attributes();
        for (auto const& attr : attrs) {
            auto const& value_str = attr->value_str;
            auto pos = value_str.rfind("ssa-scope=");
            if (pos == 0) {
                auto v = value_str.substr(10);
                return std::stoul(v);
            }
        }
        return std::nullopt;
    }
};

void ssa_transform_fix(Generator* top) {
    SSATransformFixVisitor visitor;
    visitor.visit_root(top);
}

class GeneratorPropertyVisitor : public IRVisitor {
public:
    void visit(Generator* generator) override {
        auto const& properties = generator->properties();
        for (auto const& iter : properties) {
            auto stmt = std::make_shared<AssertPropertyStmt>(iter.second);
            generator->add_stmt(stmt);
            stmt->set_parent(generator);
        }
    }
};

void change_property_into_stmt(Generator* top) {
    GeneratorPropertyVisitor visitor;
    visitor.visit_generator_root_p(top);
}

class LiftGenVarInstanceVisitor : public IRVisitor {
public:
    void visit(Generator* top) override {
        // we are only interested in generator instances that shares the same name
        // and has the same hash
        std::unordered_map<uint64_t, std::vector<ModuleInstantiationStmt*>> generator_map;
        // we use the hash value. I'm pretty sure that this won't catch all the corner cases
        // but it's good enough for now
        auto const* context = top->context();
        // we assume the module instantiation is done
        for (auto const& stmt : top->get_all_stmts()) {
            if (stmt->type() == StatementType::ModuleInstantiation) {
                auto* inst = reinterpret_cast<ModuleInstantiationStmt*>(stmt.get());
                auto const* gen = inst->target();

                if (!context->has_hash(gen)) {
                    throw UserException("Cannot find hash for generator");
                }
                auto hash = context->get_hash(gen);
                generator_map[hash].emplace_back(inst);
            }
        }

        // only interested in entries that has more than 1 entries
        for (auto const& [hash, generators] : generator_map) {
            if (generators.size() <= 1) continue;
            std::unordered_map<std::string, PortInfo> port_mapping;
            bool check = check_child_instance(generators, port_mapping);
            if (check) {
                // change it to a loop structure
                create_gen_var_instance(generators, port_mapping);
            }
        }
    }

private:
    using PortInfo = std::unordered_map<std::string, std::unordered_set<uint64_t>>;
    // NOLINTNEXTLINE
    bool static check_child_instance(const std::vector<ModuleInstantiationStmt*>& generators,
                                     std::unordered_map<std::string, PortInfo>& port_mapping) {
        // check if all the ports are connected to the same variable and index
        for (auto const* inst : generators) {
            auto const* gen = inst->target();
            for (auto const& port_name : gen->get_port_names()) {
                auto const& port = gen->get_port(port_name);
                // get connected net
                // we assume the port connections are already checked
                Var* net;
                if (port->port_direction() == PortDirection::In) {
                    auto const& stmt = *port->sources().begin();
                    net = stmt->right();
                } else {
                    auto const& stmt = *port->sinks().begin();
                    net = stmt->left();
                    // if it's a fanout to a sliced net
                    if (net->sinks().size() == 1) {
                        auto const& next_stmt = *net->sinks().begin();
                        auto* n = next_stmt->left();
                        if (n->type() == VarType::Slice) {
                            net = n;
                        }
                    }
                }
                if (net->type() == VarType::Slice) {
                    auto* slice = reinterpret_cast<VarSlice*>(net);
                    auto* parent = slice->parent_var;
                    if (slice->high != slice->low) {
                        // ranged slice not allowed
                        return false;
                    }
                    port_mapping[port_name][parent->to_string()].emplace(slice->high);
                } else {
                    port_mapping[port_name][net->to_string()] = {};
                }
            }
        }

        // make sure all the array match
        return std::all_of(port_mapping.begin(), port_mapping.end(),
                           [&generators](auto const& iter) -> bool {
                               auto const& [port_name, info] = iter;
                               // has to have one parent
                               if (info.size() != 1) {
                                   return false;
                               }
                               // if it's array slicing
                               auto const& links = info.begin()->second;
                               if (!links.empty()) {
                                   // has to match with the array size
                                   if (links.size() != generators.size()) {
                                       return false;
                                   }
                                   for (uint64_t i = 0; i < generators.size(); i++) {
                                       if (links.find(i) == links.end()) {
                                           return false;
                                       }
                                   }
                               }
                               return true;
                           });
    }

    static void create_gen_var_instance(
        const std::vector<ModuleInstantiationStmt*>& generators,
        const std::unordered_map<std::string, PortInfo>& port_mapping) {
        auto* gen = generators[0]->generator_parent();
        // need to allocate a var name
        auto const new_var = gen->get_unique_variable_name("", "i");
        // need to create a for loop with genvar loop variable
        auto for_stmt = std::make_shared<ForStmt>(new_var, 0, generators.size(), 1);
        // set it to gen var
        auto const& iter = for_stmt->get_iter_var();
        iter->set_is_gen_gar();
        gen->add_stmt(for_stmt);
        auto blk_name = find_common_instance_name(generators);
        gen->add_named_block(blk_name, for_stmt->get_loop_body());
        for (auto* inst : generators) {
            // remove statement first
            // const cast
            auto* s = const_cast<ModuleInstantiationStmt*>(inst);
            for_stmt->add_genvar_stmt(s->shared_from_this());
            gen->remove_stmt(s->shared_from_this());
            s->set_parent(for_stmt.get());
            auto const* child = inst->target();
            // need to rewrite all the connections
            // first we remove all of the connections
            // remote_stmt will take care of the connection if it doesn't exist
            for (auto const& [port_name, info] : port_mapping) {
                auto port = child->get_port(port_name);
                // get the target_var
                auto mapping = *info.begin();
                auto const& target_name = mapping.first;
                auto const& target_var_base = gen->get_var(target_name);
                std::shared_ptr<Var> target_var;
                if (mapping.second.empty()) {
                    target_var = target_var_base;
                } else {
                    target_var = target_var_base->operator[](iter).shared_from_this();
                }
                if (port->port_direction() == PortDirection::In) {
                    auto const& source_stmt = *port->sources().begin();
                    gen->remove_stmt(source_stmt);
                    port->clear_sources(false);
                    port->add_source(port->assign(target_var));
                } else {
                    auto const& sink_stmt = *port->sinks().begin();
                    gen->remove_stmt(sink_stmt);
                    port->add_sink(target_var->assign(port));
                    port->clear_sinks(false);
                }
                inst->set_mapping(port.get(), target_var.get());
            }
            // only need one instance
            if (for_stmt->get_loop_body()->empty()) {
                for_stmt->get_loop_body()->add_stmt(inst->shared_from_this());
            }

            // name all the instance name to inst
            // remove const cast hack
            auto* target_inst = const_cast<Generator*>(s->target());
            target_inst->instance_name = "inst";
        }
    }

    static std::string find_common_instance_name(
        const std::vector<ModuleInstantiationStmt*>& generators) {
        std::stringstream gen_inst_name;
        auto const& inst_ref = generators[0]->target()->instance_name;
        for (uint64_t s = 0; s < inst_ref.size(); s++) {
            bool diff = false;
            for (uint64_t i = 1; i < generators.size(); i++) {
                auto const& c = generators[i]->target()->instance_name[s];
                if (c != inst_ref[s]) {
                    diff = true;
                    break;
                }
            }
            if (diff) {
                break;
            } else {
                gen_inst_name << inst_ref[s];
            }
        }
        auto str = gen_inst_name.str();
        // remote _ at the end
        while (str[str.size() - 1] == '_') {
            str = str.substr(0, str.size() - 1);
        }
        // if it's empty, use gen_blk and the definition name
        if (str.empty()) {
            str = "genblk_" + generators[0]->target()->name;
        }
        return str;
    }
};

void lift_genvar_instances(Generator* top) {
    LiftGenVarInstanceVisitor visitor;
    // only local to the current generator so we can run it in parallel
    visitor.visit_generator_root(top);
}

void change_var_expr(const std::shared_ptr<Expr>& expr, Var* target, Var* new_var, bool move_link);

class PortLegalityFixVisitor : public IRVisitor {
public:
    void visit(Generator* gen) override {
        auto const* parent_gen = gen->parent_generator();
        auto port_names = gen->get_port_names();
        for (auto const& port_name : port_names) {
            auto const& port = gen->get_port(port_name);
            if (port->port_direction() != PortDirection::In) continue;
            auto sinks = std::unordered_set(port->sinks().begin(), port->sinks().end());
            for (auto const& stmt : sinks) {
                if (stmt->generator_parent() != parent_gen) continue;
                // if we have any sinks that's in the parent scope, it's an illegal assignment
                // we have to figure out the source
                auto const& sources = port->sources();
                if (sources.empty()) continue;
                auto const& src = (*sources.begin())->right()->shared_from_this();
                if (src->generator() != parent_gen)
                    throw InternalException("Invalid src generator");
                // replace the source with this src
                // depends on the context, it could be an auxiliary stmt
                if (port->generator()->is_auxiliary_var(stmt->left()->shared_from_this())) {
                    auto* parent_stmt = reinterpret_cast<Stmt*>(stmt->parent());
                    if (parent_stmt->type() == StatementType::If) {
                        auto if_ = parent_stmt->as<IfStmt>();
                        if (if_->predicate()->type() == VarType::Expression) {
                            auto expr = if_->predicate()->as<Expr>();
                            change_var_expr(expr, port.get(), src.get(), false);
                        } else {
                            if_->set_predicate(src);
                        }
                    } else {
                        // case statement
                        auto case_ = parent_stmt->as<SwitchStmt>();
                        if (case_->target()->type() == VarType::Expression) {
                            auto expr = case_->target()->as<Expr>();
                            change_var_expr(expr, port.get(), src.get(), false);
                        } else {
                            case_->set_target(src);
                        }
                    }
                } else {
                    auto* right = stmt->right();
                    if (right->type() == VarType::Expression) {
                        auto expr = right->as<Expr>();
                        change_var_expr(expr, port.get(), src.get(), false);
                    } else {
                        stmt->right() = src.get();
                    }
                }
            }
        }
    }
};

void port_legality_fix(Generator* top) {
    // notice that we're only interested in input ports since the output ports are handled
    // properly in the decouple fix
    PortLegalityFixVisitor visitor;
    visitor.visit_generator_root_p(top);
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
}

}  // namespace kratos
