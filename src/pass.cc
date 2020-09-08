#include "pass.hh"

#include <cassert>
#include <fstream>
#include <functional>
#include <iostream>
#include <mutex>
#include <numeric>

#include "codegen.hh"
#include "debug.hh"
#include "except.hh"
#include "fmt/format.h"
#include "fsm.hh"
#include "generator.hh"
#include "graph.hh"
#include "interface.hh"
#include "port.hh"
#include "syntax.hh"
#include "tb.hh"
#include "util.hh"

using fmt::format;
using std::runtime_error;

namespace kratos {

std::map<uint32_t, std::vector<std::pair<std::string, uint32_t>>> extract_debug_info_gen(
    Generator* top);

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

class VerifyAssignmentVisitor : public IRVisitor {
public:
    void visit(AssignStmt* stmt) override {
        auto* const left = stmt->left();
        auto* right = stmt->right();
        // if the right hand side is a const and it's safe to do so, we will let it happen
        if (left->width() != right->width()) {
            if (right->type() == VarType::ConstValue) {
                auto old_value = right->as<Const>();
                try {
                    auto& new_const =
                        constant(old_value->value(), left->width(), old_value->is_signed());
                    stmt->set_right(new_const.shared_from_this());
                    right = &new_const;
                } catch (::runtime_error&) {
                    std::cerr << "Failed to convert constants. Expect an exception" << std::endl;
                }
            }
        }
        if (left->width() != right->width())
            throw StmtException(
                ::format("assignment width doesn't match. left ({0}): {1} right ({2}): {3}",
                         left->to_string(), left->width(), right->to_string(), right->width()),
                {stmt, left, right, left->param(), right->param()});
        if (left->is_signed() != right->is_signed())
            throw StmtException(
                ::format("assignment sign doesn't match. left ({0}): {1} right ({2}): {3}",
                         left->to_string(), left->is_signed(), right->to_string(),
                         right->is_signed()),
                {stmt, left, right, left->param(), right->param()});
        check_expr(right, stmt);
    }

    void visit(Generator* generator) override {
        auto vars = generator->get_all_var_names();
        for (auto const& var_name : vars) {
            auto var = generator->get_var(var_name);
            check_var(var.get());
        }
    }

private:
    void inline static check_var(Var* var) {
        bool is_top_level = false;
        auto const& sources = var->sources();
        for (auto const& stmt : sources) {
            if (stmt->parent()->ir_node_kind() == IRNodeKind::GeneratorKind) {
                is_top_level = true;
                break;
            }
        }

        // second pass the check all the assignments
        bool has_error = false;
        if (is_top_level) {
            for (auto const& stmt : sources) {
                if (stmt->parent()->ir_node_kind() != IRNodeKind::GeneratorKind) {
                    has_error = true;
                    break;
                }
            }
        }

        if (has_error) {
            std::vector<Stmt*> stmt_list;
            stmt_list.reserve(sources.size());
            // prepare the error
            for (auto const& stmt : sources) {
                stmt_list.emplace_back(stmt.get());
            }
            throw StmtException(::format("{0} has wire assignment yet is also used in always block",
                                         var->to_string()),
                                stmt_list.begin(), stmt_list.end());
        }
    }

    void static inline check_expr(Var* var, Stmt* stmt) {
        if (var->type() == VarType::Expression) {
            auto* expr = reinterpret_cast<Expr*>(var);
            auto* left = expr->left;
            auto* right = expr->right;
            auto width = var->width();
            bool is_relational = is_relational_op(expr->op);
            bool is_reduction = is_reduction_op(expr->op);
            bool is_expand = is_expand_op(expr->op);
            if (!is_relational && !is_reduction && left->width() != width && !is_expand) {
                throw VarException(::format("{0}'s width should be {1} but used as {2}",
                                            left->to_string(), left->width(), width),
                                   {var, left, stmt, left->param()});
            }
            if (!is_relational && !is_reduction && right && right->width() != width && !is_expand) {
                throw VarException(::format("{0}'s width should be {1} but used as {2}",
                                            right->to_string(), right->width(), width),
                                   {var, right, stmt, right->param()});
            }
            if (left->type() == VarType::Expression) {
                check_expr(left, stmt);
            }
            if (right && right->type() == VarType::Expression) {
                check_expr(right, stmt);
            }
        }
    }
};

void verify_assignments(Generator* top) {
    // verify the assignment width match, and sign as well
    VerifyAssignmentVisitor visitor;
    visitor.visit_root(top);
}

class VarUnusedVisitor : public IRVisitor {
public:
    void visit(Generator* generator) override {
        std::set<std::string> vars_to_remove;
        auto vars = generator->vars();
        for (auto const& [var_name, var] : vars) {
            if (var->type() != VarType::Base || var->is_interface()) continue;
            if (var->sinks().empty()) {
                if (var->sources().empty() && !var->is_interface()) {
                    vars_to_remove.emplace(var_name);
                } else {
                    // print out warnings
                    error_mutex_.lock();
                    std::cerr << "Variable: " << var->to_string() << " has no sink" << std::endl;
                    print_ast_node(var.get());
                    error_mutex_.unlock();
                }
            }
        }

        // remove unused vars
        for (auto const& var_name : vars_to_remove) {
            generator->remove_var(var_name);
        }
    }

private:
    std::mutex error_mutex_;
};

void remove_unused_vars(Generator* top) {
    VarUnusedVisitor visitor;
    visitor.visit_generator_root_p(top);
}

class UnusedTopBlockVisitor : public IRVisitor {
    void visit(Generator* generator) override {
        std::set<std::shared_ptr<Stmt>> blocks_to_remove = {};
        uint64_t stmt_count = generator->stmts_count();
        for (uint64_t i = 0; i < stmt_count; i++) {
            auto stmt = generator->get_stmt(i);
            if (stmt->type() == StatementType::Block) {
                auto* block = dynamic_cast<StmtBlock*>(stmt.get());
                if (block->empty()) blocks_to_remove.emplace(stmt);
            }
        }

        for (auto const& stmt : blocks_to_remove) {
            generator->remove_stmt(stmt);
        }
    }
};

void remove_unused_stmts(Generator* top) {
    // for now we'll just remove the top level unused blocks
    // ideally this should be done through multiple rounds to avoid circular reference,
    // removed dead stmts and other problems. It should also remove all the other empty statements
    UnusedTopBlockVisitor visitor;
    visitor.visit_generator_root(top);
}

bool connected(const std::shared_ptr<Port>& port, std::unordered_set<uint32_t>& bits) {
    bool result = false;
    bits.reserve(port->width());
    if (!port->sources().empty()) {
        // it has been assigned. need to compute all the slices
        auto sources = port->sources();
        for (const auto& stmt : sources) {
            auto* src = stmt->left();
            if (src->type() == VarType::Slice) {
                auto ptr = src->as<VarSlice>();
                auto* ptr_parent = ptr->get_var_root_parent();
                uint32_t high, low;
                if (ptr_parent != port.get()) {
                    // it got be a sliced by var
                    if (!ptr->sliced_by_var())
                        throw VarException("Internal error. Variable has un-related sources",
                                           {port.get()});
                    // it's actually not driven by the current net
                    continue;
                } else {
                    if (ptr->sliced_by_var()) {
                        // possibly to hit all bits
                        low = 0;
                        high = port->width() - 1;
                    } else {
                        low = ptr->var_low();
                        high = ptr->var_high();
                    }
                }
                for (uint32_t i = low; i <= high; i++) {
                    bits.emplace(i);
                }
            } else {
                result = true;
                for (uint32_t i = 0; i < port->width(); i++) bits.emplace(i);
                break;
            }
        }
    }
    if (result && bits.size() != port->width()) result = false;
    return result;
}

class GeneratorConnectivityVisitor : public IRVisitor {
public:
    GeneratorConnectivityVisitor() = default;

    void visit(Generator* generator) override {
        // skip if it's an external module or stub module
        if (generator->external() || generator->is_stub()) return;
        const auto& port_names = generator->get_port_names();
        for (const auto& port_name : port_names) {
            auto const& port = generator->get_port(port_name);

            // based on whether it's an input or output
            // for inputs, if it's not top generator, we need to check if
            // something is driving it
            if (port->port_direction() == PortDirection::In) {
                if (is_top_level_) continue;
            }

            std::unordered_set<uint32_t> bits;
            bool has_error = !connected(port, bits);

            if (has_error) {
                std::vector<Stmt*> stmt_list;
                for (auto const& stmt : port->sources()) {
                    stmt_list.emplace_back(stmt.get());
                }
                for (uint32_t i = 0; i < port->width(); i++) {
                    if (bits.find(i) == bits.end()) {
                        throw StmtException(
                            ::format("{0}[{1}] is a floating net. Please check your connections",
                                     port->handle_name(), i),
                            stmt_list.begin(), stmt_list.end());
                    }
                }
            }
        }

        is_top_level_ = false;
    }

private:
    bool is_top_level_ = true;
};

void verify_generator_connectivity(Generator* top) {
    GeneratorConnectivityVisitor visitor;
    visitor.visit_generator_root(top);
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
        if (context) context->add_tracked_generator(generator);
    }
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
        for (auto *const ptr : module_instances) {
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
                if (stmt->left() == port) {
                    // the sink has to be it self
                    auto src = stmt->right();
                    if (correct_src_type(src, generator) ||
                        // here we are okay with input sliced in
                        (src->type() == VarType::Slice && src->parent() == generator->parent())) {
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
            if (port->port_type() == PortType::Clock) {
                var = var->cast(VarCastType::Clock).get();
            } else if (port->port_type() == PortType::AsyncReset) {
                var = var->cast(VarCastType::AsyncReset).get();
            } else if (port->port_type() == PortType::Reset) {
                var = var->cast(VarCastType::Reset).get();
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
                if (correct_src_type_ && src->generator() == generator->parent() &&
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

class MixedAssignmentVisitor : public IRVisitor {
public:
    void visit(Generator* generator) override {
        auto const vars = generator->get_vars();
        auto const ports = generator->get_port_names();
        for (const auto& var_name : vars) {
            checkout_assignment(generator, var_name);
        }
        for (const auto& port_name : ports) {
            checkout_assignment(generator, port_name);
        }
    }

private:
    static void checkout_assignment(Generator* generator, const std::string& name) {
        auto const& var = generator->get_var(name);
        AssignmentType type = AssignmentType::Undefined;
        for (auto const& stmt : var->sources()) {
            if (stmt->left()->get_var_root_parent() != var.get()) continue;
            if (type == AssignmentType ::Undefined)
                type = stmt->assign_type();
            else if (type != stmt->assign_type()) {
                std::vector<Stmt*> stmt_list;
                stmt_list.reserve(var->sources().size());
                for (const auto& st : var->sources()) stmt_list.emplace_back(st.get());
                throw StmtException(::format("Mixed assignment detected for variable {0}.{1}",
                                             generator->name, name),
                                    stmt_list.begin(), stmt_list.end());
            }
            // check assignment
            check_var_parent(generator, stmt->left(), stmt->right(), stmt.get());
        }
    }

    static bool has_non_port(Generator* context, Var* var) {
        if (!var) return false;
        if (var->type() == VarType::Expression) {
            auto* expr = dynamic_cast<Expr*>(var);
            return has_non_port(context, expr->left) || has_non_port(context, expr->right);
        } else if (var->type() == VarType::Slice) {
            auto* slice = dynamic_cast<VarSlice*>(var);
            return has_non_port(context, slice->parent_var);
        } else {
            return var->generator() != context && var->type() != VarType::PortIO &&
                   var->type() != VarType ::ConstValue;
        }
    }

    static void check_var_parent(Generator* generator, Var* dst_var, Var* var, Stmt* stmt) {
        auto* gen = var->generator();
        if (gen == Const::const_gen()) return;
        if (var->type() == VarType::ConstValue && var->generator() != generator) {
            var->set_generator(gen);
            return;
        }
        if (generator != gen) {
            // if it's an input port, the parent context is different
            if (dst_var->type() == VarType::Slice) {
                auto* slice = dynamic_cast<VarSlice*>(dst_var);
                dst_var = const_cast<Var*>(slice->get_var_root_parent());
            }
            if (dst_var->type() == VarType::PortIO) {
                auto* port = dynamic_cast<Port*>(dst_var);
                if (port->port_direction() == PortDirection::In) {
                    auto* context_g = dst_var->generator()->parent();
                    if (gen != context_g && gen->parent() != context_g &&
                        gen->parent() != context_g) {
                        throw VarException(
                            ::format("{0}.{1} cannot be wired to {2}.{3} because {0} is "
                                     "not a child generator of {2}",
                                     generator->instance_name, dst_var->to_string(),
                                     gen->instance_name, var->to_string()),
                            {generator, gen, dst_var, var});
                    }
                    return;
                }
            }
            if ((gen->parent() != generator && gen->parent() != generator->parent()) ||
                has_non_port(generator, var)) {
                throw VarException(::format("{0}.{1} cannot be wired to {2}.{3} because {2} is "
                                            "not a child generator of {0}",
                                            generator->instance_name, dst_var->to_string(),
                                            gen->instance_name, var->to_string()),
                                   {generator, gen, dst_var, var, stmt});
            }
        }
    }
};

void check_mixed_assignment(Generator* top) {
    MixedAssignmentVisitor visitor;
    visitor.visit_generator_root(top);
}

class SynthesizableVisitor : public IRVisitor {
public:
    void visit(AssignStmt* stmt) override {
        if (stmt->get_delay() >= 0) {
            nodes_.emplace_back(stmt);
        }
    }

    void visit(FunctionCallVar* var) override {
        auto* const def = var->func();
        if (def->is_dpi()) {
            nodes_.emplace_back(var);
        }
    }

    void visit(FunctionCallStmt* stmt) override {
        auto const& def = stmt->func();
        if (def->is_dpi()) {
            nodes_.emplace_back(stmt);
        }
    }

    const std::vector<IRNode*>& nodes() const { return nodes_; }

private:
    std::vector<IRNode*> nodes_;
};

void check_non_synthesizable_content(Generator* top) {
    SynthesizableVisitor visitor;
    visitor.visit_root(top);
    auto const& nodes = visitor.nodes();
    if (!nodes.empty()) {
        print_nodes(nodes);
        throw UserException(
            "Non-synthesizable content detected. Please see the revelent lines "
            "output above (after using debug mode)");
    }
}

class ActiveVisitor : public IRVisitor {
    // we can be very clever about how to detect the wrong negative
    // 1. we determine the activate low or high from the sequential conditions
    // 2. whenever we meet a if reset statement, we check it against it
    //    because if the async reset is used properly, we will determine the port type first first
    //    if the port is used as an sync reset, the port active type will be undefined.
public:
    void visit(IfStmt* stmt) override {
        auto predicate = stmt->predicate();
        // notice this just catch some simple mistakes
        // thus is designed to be zero false negative
        if (predicate->type() == VarType::PortIO) {
            auto port_s = predicate->as<Port>();
            auto* port = port_s.get();
            if (port->port_type() == PortType::AsyncReset) {
                if (reset_map_.find(port) == reset_map_.end()) {
                    // it's used as a sync reset
                    throw VarException(
                        ::format("{0} is used has a synchronous reset", port->to_string()),
                        {port, stmt});
                }
                bool reset_high = reset_map_.at(port);
                if (!reset_high)
                    throw VarException("Active low signal used as active high", {port, stmt});
            } else if (port->port_type() == PortType::Reset) {
                if (reset_map_.find(port) != reset_map_.end()) {
                    throw VarException(::format("{0} is synchronous reset but used as async reset",
                                                port->to_string()),
                                       {port, stmt, get_reset_stmt(port)});
                }
            }
        } else if (predicate->type() == VarType::Expression) {
            auto expr = predicate->as<Expr>();
            if (expr->op == ExprOp::UNot || expr->op == ExprOp::UInvert) {
                auto var = expr->left->as<Var>();
                if (var->type() == VarType::PortIO) {
                    auto port = var->as<Port>();
                    if (port->port_type() == PortType::AsyncReset) {
                        if (reset_map_.find(port.get()) == reset_map_.end()) {
                            // it's used as a sync reset
                            throw VarException(
                                ::format("{0} is used has a synchronous reset", port->to_string()),
                                {port.get(), stmt});
                        }
                        bool reset_high = reset_map_.at(port.get());
                        if (reset_high) {
                            throw VarException("Active high signal used as active low",
                                               {port.get(), stmt});
                        }
                    } else if (port->port_type() == PortType::Reset) {
                        if (reset_map_.find(port.get()) != reset_map_.end()) {
                            throw VarException(
                                ::format("{0} is synchronous reset but used as async reset",
                                         port->to_string()),
                                {port.get(), stmt, get_reset_stmt(port.get())});
                        }
                    }
                }
            }
        }
    }

    void visit(SequentialStmtBlock* stmt) override {
        auto const& sensitivity = stmt->get_conditions();
        for (auto const& [t, v] : sensitivity) {
            if (v->type() == VarType::PortIO) {
                auto port_s = v->as<Port>();
                auto* port = port_s.get();
                if (port->port_type() == PortType::AsyncReset) {
                    auto reset_high = t == BlockEdgeType::Posedge;
                    // check if we have reset edge set
                    if (port->active_high()) {
                        if (reset_high != (*port->active_high())) {
                            throw VarException(
                                ::format("{0} is declared reset {1} but is used as reset {2}",
                                         port->to_string(), reset_high ? "high" : "low",
                                         reset_high ? "high" : "low"),
                                {port, stmt});
                        }
                    }
                    if (reset_map_.find(port) != reset_map_.end()) {
                        // check consistency
                        if (reset_map_.at(port) != reset_high) {
                            throw VarException(
                                ::format("Inconsistent active low/high usage for {0}",
                                         port->to_string()),
                                {port, stmt, get_reset_stmt(port)});
                        }
                    } else {
                        reset_map_.emplace(std::make_pair(port, reset_high));
                        reset_map_.emplace(std::make_pair(port, stmt));
                    }
                } else if (port->port_type() == PortType::Reset) {
                    throw VarException(
                        ::format("{0} is used as async reset but is declared synchronous",
                                 port->to_string()),
                        {port, stmt});
                }
            }
        }
    }

private:
    std::unordered_map<Port*, bool> reset_map_;
    std::unordered_map<Port*, Stmt*> reset_stmt_;

    Stmt* get_reset_stmt(Port* port) const {
        if (reset_stmt_.find(port) != reset_stmt_.end()) return reset_stmt_.at(port);
        return nullptr;
    }
};

void check_active_high(Generator* top) {
    ActiveVisitor visitor;
    visitor.visit_root(top);
}

class TransformIfCase : public IRVisitor {
public:
    void visit(CombinationalStmtBlock* stmts) override { transform_block(stmts); }
    void visit(SequentialStmtBlock* stmts) override { transform_block(stmts); }
    void visit(ScopedStmtBlock* stmts) override { transform_block(stmts); }

private:
    void static transform_block(StmtBlock* stmts) {
        auto const stmt_count = stmts->size();
        for (uint64_t i = 0; i < stmt_count; i++) {
            auto* stmt = stmts->get_stmt(i).get();
            Var* target = nullptr;
            std::vector<std::shared_ptr<IfStmt>> if_stmts;
            if (has_target_if(stmt, target, if_stmts) && target) {
                uint64_t cases = if_stmts.size();
                uint64_t expected_case = 1u << target->width();
                bool has_else = !(if_stmts.back()->else_body()->empty());
                if (expected_case > 1 && (cases >= expected_case || has_else)) {
                    auto switch_stmt = change_if_to_switch(stmt->as<IfStmt>(), if_stmts);
                    stmts->set_child(i, switch_stmt);
                }
            }
        }
    }
    bool static has_target_if(Stmt* stmt, Var*& var,
                              std::vector<std::shared_ptr<IfStmt>>& if_stmts) {
        // keep track of which statement are used later to transform into switch statement
        if (stmt->type() != StatementType::If && if_stmts.size() <= 1)
            return false;
        else if (stmt->type() != StatementType::If) {
            // we have reach the end of the if-else chain
            return true;
        }
        auto if_ = stmt->as<IfStmt>();
        auto predicate = if_->predicate();
        // predicate has to be a expression with equal comparison
        if (predicate->type() != VarType::Expression) return false;
        auto expr = predicate->as<Expr>();
        if (expr->op != ExprOp::Eq) return false;
        // has to be the same variable
        if (var == nullptr) {
            var = expr->left;
        } else {
            if (var != expr->left) return false;
        }
        if ((expr->right->type() != VarType::ConstValue) &&
            (expr->right->type() != VarType::Parameter))
            return false;
        if (if_->else_body()->size() > 1) return false;

        if_stmts.emplace_back(if_);
        if (if_->else_body()->empty()) {
            return true;
        } else {
            return has_target_if((*if_->else_body())[0].get(), var, if_stmts);
        }
    }

    std::shared_ptr<SwitchStmt> static change_if_to_switch(
        std::shared_ptr<IfStmt> stmt, const std::vector<std::shared_ptr<IfStmt>>& if_stmts) {
        auto expr = stmt->predicate()->as<Expr>();
        // we assume that this is a valid case (see has_target_if)
        auto* target = expr->left;
        std::shared_ptr<SwitchStmt> switch_ =
            std::make_shared<SwitchStmt>(target->shared_from_this());
        if (target->generator()->debug) {
            switch_->fn_name_ln = std::vector<std::pair<std::string, uint32_t>>(
                stmt->fn_name_ln.begin(), stmt->fn_name_ln.end());
            switch_->fn_name_ln.emplace_back(std::make_pair(__FILE__, __LINE__));
        }

        while (std::find(if_stmts.begin(), if_stmts.end(), stmt) != if_stmts.end()) {
            auto condition = expr->right->as<Const>();
            switch_->add_switch_case(condition, stmt->then_body());
            if (!stmt->else_body()->empty() &&
                std::find(if_stmts.begin(), if_stmts.end(), (*stmt->else_body())[0]) ==
                    if_stmts.end()) {
                // we have reached the end
                // add default statement
                switch_->add_switch_case(nullptr, stmt->else_body());
                break;
            } else if (!stmt->else_body()->empty()) {
                // switch to the else case
                stmt = (*stmt->else_body())[0]->as<IfStmt>();
                expr = stmt->predicate()->as<Expr>();
            } else {
                break;
            }
        }

        return switch_;
    }
};

void transform_if_to_case(Generator* top) {
    TransformIfCase visitor;
    visitor.visit_root(top);
}

class MergeIfVisitor : public IRVisitor {
public:
    void visit(CombinationalStmtBlock* stmts) override { transform_block(stmts); }
    void visit(SequentialStmtBlock* stmts) override { transform_block(stmts); }
    void visit(ScopedStmtBlock* stmts) override { transform_block(stmts); }

private:
    using IfStmtType = std::pair<std::shared_ptr<IfStmt>, std::shared_ptr<Const>>;
    // The if statements has to satisfy the following requirements in order to merge
    // in the same block
    // if target is the same
    // all equality comparison and against an constant
    void static transform_block(StmtBlock* block) {
        // only run marked ones
        if (!block->has_attribute("merge_if_block")) return;
        std::map<Var*, std::vector<IfStmtType>> result;
        get_targeted_if(block, result);
        std::unordered_set<IfStmt*> merged_if;
        for (auto const& iter : result) {
            auto stmts = iter.second;
            if (stmts.size() > 1) {
                // we have stmts to merge
                auto top_if = stmts[0].first;
                // first pass to merge the if statements with the same constant value
                // build index on the const values
                std::unordered_map<int64_t, IfStmt*> mapping;
                for (const auto& [stmt, const_] : stmts) {
                    auto const_value = const_->value();
                    if (mapping.find(const_value) == mapping.end()) {
                        mapping.emplace(const_value, stmt.get());
                    } else {
                        // merge the current one into the one we already have
                        auto* if_ = mapping.at(const_value);
                        auto const& then = stmt->then_body();
                        for (auto const& st : *then) {
                            if_->add_then_stmt(st);
                        }
                        auto const& else_ = stmt->else_body();
                        for (auto const& st : *else_) {
                            if_->add_else_stmt(st);
                        }
                        merged_if.emplace(stmt.get());
                    }
                }

                // second pass to nest the if statement
                for (uint64_t i = 1; i < stmts.size(); i++) {
                    auto const& stmt = stmts[i].first;
                    if (merged_if.find(stmt.get()) != merged_if.end()) {
                        continue;
                    }
                    // put the one in the top if
                    top_if->add_else_stmt(stmt);
                    merged_if.emplace(stmt.get());
                }
            }
        }
        // remove merged if
        for (auto const& stmt : merged_if) {
            block->remove_stmt(stmt->shared_from_this());
        }
    }

    void static get_targeted_if(StmtBlock* block, std::map<Var*, std::vector<IfStmtType>>& result) {
        for (auto const& stmt : *block) {
            if (stmt->type() == StatementType::If) {
                auto if_ = stmt->as<IfStmt>();
                auto predicate = if_->predicate();
                if (predicate->type() == VarType::Expression) {
                    auto expr = predicate->as<Expr>();
                    if (expr->op == ExprOp::Eq && expr->right &&
                        expr->right->type() == VarType::ConstValue) {
                        // this is what we want
                        auto* target_var = expr->left;
                        result[target_var].emplace_back(
                            std::make_pair(if_, expr->right->as<Const>()));
                    }
                }
            }
        }
    }
};

void merge_if_block(Generator* top) {
    MergeIfVisitor visitor;
    visitor.visit_root(top);
}

class VarFanOutVisitor : public IRVisitor {
public:
    void visit(Generator* generator) override {
        auto var_names = generator->get_all_var_names();
        for (auto const& var_name : var_names) {
            auto var = generator->get_var(var_name);
            std::vector<std::pair<std::shared_ptr<Var>, std::shared_ptr<AssignStmt>>> chain;
            compute_assign_chain(var, chain);
            if (chain.size() <= 2) continue;  // nothing to be done

            std::vector<std::pair<std::string, uint32_t>> debug_info;

            for (uint64_t i = 0; i < chain.size() - 1; i++) {
                auto& [pre, stmt] = chain[i];
                auto next = chain[i + 1].first;

                // insert debug info
                if (generator->debug) {
                    debug_info.insert(debug_info.end(), stmt->fn_name_ln.begin(),
                                      stmt->fn_name_ln.end());
                }

                next->unassign(stmt);
            }

            auto dst = chain.back().first;
            Var::move_src_to(var.get(), dst.get(), generator, false);
            // if both of them are ports, we need to add a statement
            if (var->type() == VarType::PortIO && dst->type() == VarType::PortIO) {
                // need to add a top assign statement
                auto stmt = dst->assign(var, AssignmentType::Blocking);
                if (generator->debug) {
                    // copy every vars definition over
                    stmt->fn_name_ln = debug_info;
                    stmt->fn_name_ln.emplace_back(__FILE__, __LINE__);
                }
                generator->add_stmt(stmt);
            }
        }
    }

    void static compute_assign_chain(
        const std::shared_ptr<Var>& var,
        std::vector<std::pair<std::shared_ptr<Var>, std::shared_ptr<AssignStmt>>>& queue) {
        if (var->sinks().size() == 1) {
            auto const& stmt = *(var->sinks().begin());
            if (!stmt->parent()) return;
            if (stmt->parent()->ir_node_kind() == IRNodeKind::GeneratorKind) {
                auto* sink_var = stmt->left();
                if (sink_var->parent() != var->parent() || sink_var->is_interface()) {
                    // not the same parent
                    return;
                }
                // FIXME: need to re-work on fanout one wire removal
                //  For now disable the expression based search
                if (stmt->right() != var.get()) {
                    // expr based
                    return;
                }
                queue.emplace_back(std::make_pair(var, stmt));
                compute_assign_chain(sink_var->shared_from_this(), queue);
            }
        } else {
            queue.emplace_back(std::make_pair(var, nullptr));
        }
    }
};

void remove_fanout_one_wires(Generator* top) {
    VarFanOutVisitor visitor;
    visitor.visit_generator_root_p(top);
}

class RemovePassThroughVisitor : public IRVisitor {
public:
    void visit(Generator* generator) override {
        const auto& children = generator->get_child_generators();
        std::vector<std::shared_ptr<Generator>> child_to_remove;
        for (auto const& child : children) {
            if (is_pass_through(child.get())) {
                // need to remove it
                child_to_remove.emplace_back(child);
                // add it to the set
                if (!child->is_cloned()) pass_through_.emplace(child.get());
            }
        }

        for (auto const& child : child_to_remove) {
            // we move the src and sinks around
            const auto& port_names = child->get_port_names();
            for (auto const& port_name : port_names) {
                auto port = child->get_port(port_name);
                if (port->port_direction() == PortDirection::In) {
                    // move the src to whatever it's connected to
                    // basically compress the module into a variable
                    // we will let the later downstream passes to remove the extra wiring
                    auto* next_port = (*(port->sinks().begin()))->left();
                    auto var_name =
                        generator->get_unique_variable_name(child->instance_name, port->name);
                    auto& new_var = generator->var(var_name, port->var_width(), port->size(),
                                                   port->is_signed());
                    if (generator->debug) {
                        // need to copy the changes over
                        new_var.fn_name_ln = std::vector<std::pair<std::string, uint32_t>>(
                            child->fn_name_ln.begin(), child->fn_name_ln.end());
                        new_var.fn_name_ln.emplace_back(__FILE__, __LINE__);
                    }
                    Var::move_src_to(port.get(), &new_var, generator, false);
                    // move the sinks over
                    Var::move_sink_to(next_port, &new_var, generator, false);
                }
            }
            // remove it from the generator children
            generator->remove_child_generator(child->shared_from_this());
        }
    }

private:
    bool is_pass_through(Generator* generator) {
        if (generator->is_cloned()) {
            auto* ref_gen = generator->def_instance();
            if (!ref_gen) {
                throw GeneratorException(::format("{0} is cloned but doesn't have def instance",
                                                  generator->instance_name),
                                         {generator});
            }
            return pass_through_.find(ref_gen) != pass_through_.end();
        }
        const auto vars = generator->get_vars();
        // has to be empty
        if (!vars.empty()) return false;
        // has to have exact number of assignments as ports
        // ports has to be an even number, i.e. one in to one out
        // maybe we can relax this restriction later
        auto const port_names = generator->get_port_names();
        if (port_names.size() % 2) return false;
        if (generator->stmts_count() != port_names.size() / 2) return false;

        for (const auto& port_name : port_names) {
            auto const port = generator->get_port(port_name);
            if (port->port_direction() == PortDirection::In) {
                auto sinks = port->sinks();
                if (sinks.size() != 1) return false;
            } else {
                auto const& sources = port->sources();
                if (sources.size() != 1) return false;
                // maybe some add stuff
                auto stmt = *(sources.begin());
                auto* src = stmt->right();
                if (src->type() != VarType::PortIO) return false;
            }
        }
        return true;
    }

    std::unordered_set<Generator*> pass_through_;
};

void remove_pass_through_modules(Generator* top) {
    RemovePassThroughVisitor visitor;
    visitor.visit_generator_root(top);
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

class PortPackedVisitor : public IRVisitor {
public:
    void visit(Generator* generator) override {
        auto const& var_names = generator->get_all_var_names();
        for (auto const& var_name : var_names) {
            auto var = generator->get_var(var_name);
            if (var->is_struct()) {
                PackedStruct struct_def("", std::vector<std::tuple<std::string, uint32_t>>());
                if (var->type() == VarType::PortIO) {
                    auto ptr = var->as<PortPackedStruct>();
                    struct_def = ptr->packed_struct();
                } else {
                    auto ptr = var->as<VarPackedStruct>();
                    struct_def = ptr->packed_struct();
                }
                if (struct_def.external) continue;
                if (structs_.find(struct_def.struct_name) != structs_.end()) {
                    // do some checking
                    auto struct_ = structs_.at(struct_def.struct_name);
                    if (struct_.attributes.size() != struct_def.attributes.size())
                        throw VarException(::format("redefinition of different packed struct {0}",
                                                    struct_def.struct_name),
                                           {var.get(), struct_ports_.at(struct_def.struct_name)});
                    for (uint64_t i = 0; i < struct_def.attributes.size(); i++) {
                        auto const& [name1, width1, signed_1] = struct_.attributes[i];
                        auto const& [name2, width2, signed_2] = struct_def.attributes[i];
                        if (name1 != name2 || width1 != width2 || signed_1 != signed_2)
                            throw VarException(
                                ::format("redefinition of different packed struct {0}",
                                         struct_def.struct_name),
                                {var.get(), struct_ports_.at(struct_def.struct_name)});
                    }
                } else {
                    structs_.emplace(struct_def.struct_name, struct_def);
                    struct_ports_.emplace(struct_def.struct_name, var.get());
                }
            }
        }
    }

    const std::map<std::string, PackedStruct>& structs() const { return structs_; }

private:
    std::map<std::string, PackedStruct> structs_;
    std::map<std::string, Var*> struct_ports_;
};

std::map<std::string, std::string> extract_struct_info(Generator* top) {
    PortPackedVisitor visitor;
    visitor.visit_generator_root(top);

    // convert the definition into
    std::map<std::string, std::string> result;
    auto const& structs = visitor.structs();
    for (auto const& [name, struct_] : structs) {
        // TODO:
        //  Use Stream class in the codegen instead to track the debugging info
        //  Share the same code gen logic with Stream
        std::string entry;
        entry.append("typedef struct packed {\n");

        for (auto const& [attribute_name, width, is_signed] : struct_.attributes) {
            std::vector<std::string> str = {"    logic"};
            if (width > 1) str.emplace_back(::format("[{0}:0]", width - 1));
            if (is_signed) str.emplace_back("signed");
            str.emplace_back(attribute_name);
            auto entry_str = string::join(str.begin(), str.end(), " ");
            entry.append(entry_str + ";\n");
        }
        entry.append(::format("}} {0};\n", name));
        result.emplace(name, entry);
    }
    return result;
}

class DPIVisitor : public IRVisitor {
public:
    void visit(FunctionStmtBlock* stmt) override {
        if (!stmt->is_dpi()) return;
        // collect all the dpi information and then make sure they are declared in the same
        // name and spec
        // this can be an issue if the files are going to split into multiple files
        auto const& func_name = stmt->function_name();
        if (dpi_funcs_.find(func_name) == dpi_funcs_.end()) {
            // new one
            dpi_funcs_.emplace(func_name, dynamic_cast<DPIFunctionStmtBlock*>(stmt));
        } else {
            auto* ref_stmt = dpi_funcs_.at(func_name);
            auto const& ref_ports = ref_stmt->ports();
            auto const& ports = stmt->ports();
            if (ref_ports.size() != ports.size())
                throw StmtException("DPI function " + func_name + " has different interface",
                                    {stmt, ref_stmt});
            // check the return width
            auto* dpi_stmt = dynamic_cast<DPIFunctionStmtBlock*>(stmt);
            if (dpi_stmt->return_width() != ref_stmt->return_width()) {
                if (ref_ports.size() != ports.size())
                    throw StmtException("DPI function " + func_name + " has different interface",
                                        {stmt, ref_stmt});
            }
            for (auto const& [port_name, port_ref] : ref_ports) {
                if (ports.find(port_name) == ports.end()) {
                    throw VarException(
                        ::format("DPI function with the same name ({0}) have different interface",
                                 func_name),
                        {port_ref.get()});
                }
                auto const& port = ports.at(port_name);
                if (port->size() != port_ref->size() ||
                    port->is_signed() != port_ref->is_signed() ||
                    port->port_direction() != port_ref->port_direction()) {
                    throw VarException(
                        ::format("DPI function with the same name ({0}) have different interface",
                                 func_name),
                        {port_ref.get(), port.get()});
                }
            }
            if (dpi_stmt->is_context() != ref_stmt->is_context() ||
                dpi_stmt->is_pure() != ref_stmt->is_pure())
                throw StmtException(
                    "DPI function " + func_name + " has different attribute (pure/context)",
                    {stmt, ref_stmt});
        }
    }

    const std::map<std::string, DPIFunctionStmtBlock*>& dpi_funcs() { return dpi_funcs_; }

private:
    std::map<std::string, DPIFunctionStmtBlock*> dpi_funcs_;
};

std::map<std::string, std::string> extract_dpi_function(Generator* top, bool int_interface) {
    DPIVisitor visitor;
    visitor.visit_root(top);
    // code gen these dpi info
    std::map<std::string, std::string> result;
    auto const& dpi_funcs = visitor.dpi_funcs();
    for (auto const& [func_name, stmt] : dpi_funcs) {
        std::stringstream stream;
        // dpi-c
        std::string dpi_type;
        if (stmt->is_pure())
            dpi_type = " pure";
        else if (stmt->is_context())
            dpi_type = " context";
        stream << "import \"DPI-C\"" << dpi_type << " function ";
        // based on the return width, we choose the closest one
        if (stmt->return_width() == 0) {
            stream << "void ";
        } else if (stmt->return_width() == 1) {
            stream << "bit ";
        } else if (stmt->return_width() <= 8) {
            stream << "byte ";
        } else if (stmt->return_width() <= 16) {
            stream << "shortint ";
        } else if (stmt->return_width() <= 32) {
            stream << "int ";
        } else {
            stream << "longint ";
        }
        stream << stmt->function_name() << "(";
        auto ports = stmt->ports();
        std::vector<std::string> port_str;
        port_str.reserve(ports.size());
        std::vector<std::string> port_names;
        port_names.reserve(ports.size());
        for (auto const& iter : ports) port_names.emplace_back(iter.first);

        // sort based on ordering
        auto const& ordering = stmt->port_ordering();
        std::sort(port_names.begin(), port_names.end(), [&](const auto& lhs, const auto& rhs) {
            return ordering.at(lhs) < ordering.at(rhs);
        });

        for (auto const& port_name : port_names) {
            if (int_interface) {
                auto port = ports.at(port_name);
                // compute the closest width
                std::string type_str;
                if (port->width() <= 8) {
                    type_str = "byte";
                } else if (port->width() <= 16) {
                    type_str = "shortint";
                } else if (port->width() <= 32) {
                    type_str = "int";
                } else {
                    type_str = "longint";
                }
                std::vector<std::string> strs{
                    port->port_direction() == PortDirection::In ? "input" : "output", type_str};
                if (port->is_signed()) strs.emplace_back("signed");
                strs.emplace_back(port_name);
                port_str.emplace_back(string::join(strs.begin(), strs.end(), " "));
            } else {
                port_str.emplace_back(
                    SystemVerilogCodeGen::get_port_str(ports.at(port_name).get()));
            }
        }
        stream << string::join(port_str.begin(), port_str.end(), ", ");
        stream << ");";

        result.emplace(func_name, stream.str());
    }
    return result;
}

std::map<std::string, std::string> extract_enum_info(Generator* top) {
    auto const& enum_defs = top->context()->enum_defs();

    std::map<std::string, std::string> result;
    for (auto const& [enum_name, def] : enum_defs) {
        if (def->external) continue;
        auto str = SystemVerilogCodeGen::enum_code(def.get());
        result.emplace(enum_name, str);
    }

    return result;
}

class MergeWireAssignmentsVisitor : public IRVisitor {
public:
    void visit(ScopedStmtBlock* block) override { process_stmt_block(block); }

    void visit(SequentialStmtBlock* block) override { process_stmt_block(block); }

    void visit(CombinationalStmtBlock* block) override { process_stmt_block(block); }

    void visit(Generator* generator) override {
        std::set<std::shared_ptr<Stmt>> stmts_to_remove;

        // first filter out sliced assignments
        std::set<std::shared_ptr<AssignStmt>> sliced_stmts;
        extract_sliced_stmts(generator, sliced_stmts);
        get_stmts_to_remove(generator, stmts_to_remove, sliced_stmts);

        // remove them
        for (auto const& stmt : stmts_to_remove) {
            generator->remove_stmt(stmt);
        }
    }

private:
    void process_stmt_block(StmtBlock* block) {
        std::set<std::shared_ptr<Stmt>> stmts_to_remove;

        // first filter out sliced assignments
        std::set<std::shared_ptr<AssignStmt>> sliced_stmts;
        extract_sliced_stmts(block, sliced_stmts);
        get_stmts_to_remove(block, stmts_to_remove, sliced_stmts);
        for (auto const& stmt : stmts_to_remove) block->remove_stmt(stmt);
    }

    static void extract_sliced_stmts(Generator* generator,
                                     std::set<std::shared_ptr<AssignStmt>>& sliced_stmts) {
        uint64_t stmt_count = generator->stmts_count();
        for (uint64_t i = 0; i < stmt_count; i++) {
            auto stmt = generator->get_stmt(i);
            if (stmt->type() == StatementType::Assign) {
                auto assign_stmt = stmt->as<AssignStmt>();
                if (assign_stmt->left()->type() == VarType::Slice &&
                    assign_stmt->right()->type() == VarType::Slice) {
                    sliced_stmts.emplace(assign_stmt);
                }
            }
        }
    }

    static void extract_sliced_stmts(StmtBlock* block,
                                     std::set<std::shared_ptr<AssignStmt>>& sliced_stmts) {
        for (auto const& stmt : *block) {
            if (stmt->type() == StatementType ::Assign) {
                auto assign_stmt = stmt->as<AssignStmt>();
                if (assign_stmt->left()->type() == VarType::Slice &&
                    assign_stmt->right()->type() == VarType::Slice) {
                    sliced_stmts.emplace(assign_stmt);
                }
            }
        }
    }

    template <typename T>
    void get_stmts_to_remove(T* generator, std::set<std::shared_ptr<Stmt>>& stmts_to_remove,
                             const std::set<std::shared_ptr<AssignStmt>>& sliced_stmts) const {
        // group the assignments together
        using AssignPair = std::pair<Var*, Var*>;
        std::map<AssignPair, std::vector<std::shared_ptr<AssignStmt>>> slice_vars;
        for (auto const& assign_stmt : sliced_stmts) {
            auto left_slice = assign_stmt->left()->as<VarSlice>();
            auto right_slice = assign_stmt->right()->as<VarSlice>();
            Var* left_parent = left_slice->parent_var;
            Var* right_parent = right_slice->parent_var;
            // only deal with 1D for now
            if (left_parent->type() == VarType::Slice) continue;
            if (right_parent->type() == VarType::Slice) continue;
            if (left_parent->width() != right_parent->width()) continue;

            slice_vars[{left_parent, right_parent}].emplace_back(assign_stmt);
        }

        // merge the assignments
        for (auto const& [vars, stmts] : slice_vars) {
            const auto& [left, right] = vars;

            // NOTE:
            // we assume that at this stage we've passed the connectivity check
            if (stmts.size() != left->width()) continue;

            // remove left's sources and right's sink
            // also add it to the statements to remove
            for (auto const& stmt : stmts) {
                left->remove_source(stmt);
                right->remove_sink(stmt);
                stmts_to_remove.emplace(stmt);
            }
            // make new assignment
            create_new_assignment(generator, stmts, left, right);
        }
    }
    void static create_new_assignment(Generator* generator,
                                      const std::vector<std::shared_ptr<AssignStmt>>& stmts,
                                      Var* const left, Var* const right) {
        if (stmts.empty()) return;
        auto new_stmt = left->assign(right->shared_from_this(), AssignmentType::Blocking);
        generator->add_stmt(new_stmt);
        if (generator->debug) {
            // merge all the statements
            for (auto const& stmt : stmts) {
                new_stmt->fn_name_ln.insert(new_stmt->fn_name_ln.end(), stmt->fn_name_ln.begin(),
                                            stmt->fn_name_ln.end());
            }
            new_stmt->fn_name_ln.emplace_back(std::make_pair(__FILE__, __LINE__));
        }
    }

    static void create_new_assignment(StmtBlock* block,
                                      const std::vector<std::shared_ptr<AssignStmt>>& stmts,
                                      Var* const left, Var* const right) {
        if (stmts.empty()) return;
        // use the first assignment type. assume all the assignment has passed the
        // mixed assignment check
        auto new_stmt = left->assign(right->shared_from_this(), stmts[0]->assign_type());
        block->add_stmt(new_stmt);
        auto* generator = get_parent(block);
        if (generator->debug) {
            // merge all the statements
            for (auto const& stmt : stmts) {
                new_stmt->fn_name_ln.insert(new_stmt->fn_name_ln.end(), stmt->fn_name_ln.begin(),
                                            stmt->fn_name_ln.end());
            }
            new_stmt->fn_name_ln.emplace_back(std::make_pair(__FILE__, __LINE__));
        }
    }

    static Generator* get_parent(StmtBlock* block) {
        Generator* result = nullptr;
        IRNode* node = block;
        for (uint32_t i = 0; i < 10000u; i++) {
            auto* p = node->parent();
            if (p->ir_node_kind() == IRNodeKind::GeneratorKind) {
                result = dynamic_cast<Generator*>(p);
                break;
            }
            node = p;
        }
        if (!result) {
            throw StmtException("Cannot find parent for the statement block", {block});
        }
        return result;
    }
};

void merge_wire_assignments(Generator* top) {
    // for now we only merge generator-level assignments
    MergeWireAssignmentsVisitor visitor;
    visitor.visit_root(top);
}

class SensitivityVisitor : public IRVisitor {
    void visit(SequentialStmtBlock* stmt) override {
        auto const& sensitivity_list = stmt->get_conditions();
        for (auto const& iter : sensitivity_list) {
            auto const& var = iter.second;
            // check type
            if (var->type() == VarType::PortIO) {
                // it's a port
                auto port = var->as<Port>();
                if (port->port_type() != PortType::Clock &&
                    port->port_type() != PortType::AsyncReset) {
                    // only clock and async reset allowed
                    throw StmtException(
                        ::format("Only Clock and AsyncReset allowed in "
                                 "sensitivity list. {0} is {1}",
                                 var->to_string(), port_type_to_str(port->port_type())),
                        {stmt, var.get()});
                }
            } else if (var->type() == VarType::BaseCasted) {
                auto var_casted = var->as<VarCasted>();
                if (var_casted->cast_type() != VarCastType::Clock &&
                    var_casted->cast_type() != VarCastType::AsyncReset) {
                    throw StmtException(::format("Only Clock and AsyncReset allowed in "
                                                 "sensitivity list. Please use cast() to cast {0}}",
                                                 var->to_string()),
                                        {stmt, var.get()});
                }
            } else {
                throw StmtException(::format("Only variable type of Clock and "
                                             "AsyncReset allowed in sensitivity list, got {0}",
                                             var->to_string()),
                                    {stmt, var.get()});
            }
        }
    }
};

void check_always_sensitivity(Generator* top) {
    SensitivityVisitor visitor;
    visitor.visit_root(top);
}

class PipelineInsertionVisitor : public IRVisitor {
public:
    void visit(Generator* generator) override {
        // only if the generator has attribute of "pipeline" and the value string is the
        // number of pipeline stages will do
        bool has_attribute = false;
        std::string clock_name;
        auto attributes = generator->get_attributes();
        uint32_t num_stages = 0;
        for (auto const& attr : attributes) {
            if (attr->type_str == "pipeline") {
                try {
                    int i = std::stoi(attr->value_str);
                    if (i > 0) {
                        num_stages = static_cast<uint32_t>(i);
                        has_attribute = true;
                    }
                } catch (std::invalid_argument const&) {
                    throw std::runtime_error(
                        ::format("Unable to get value string from generator {0}", generator->name));
                }
            } else if (attr->type_str == "pipeline_clk") {
                clock_name = attr->value_str;
            }
        }
        if (has_attribute) {
            auto port_names = generator->get_port_names();
            // get the clock name, if it's empty
            if (clock_name.empty()) {
                // pick the first one
                auto clock_names = generator->get_ports(PortType::Clock);
                if (!clock_names.empty()) clock_name = clock_names[0];
            }
            if (clock_name.empty()) {
                throw GeneratorException(
                    ::format("Unable to find clock signal for generator {0}", generator->name),
                    {generator});
            }
            auto clock_port = generator->get_port(clock_name);
            // we need to create all the registers based on the posedge of the clock
            std::vector<std::shared_ptr<SequentialStmtBlock>> blocks;
            blocks.resize(num_stages);
            for (uint32_t i = 0; i < num_stages; i++) {
                blocks[i] = std::make_shared<SequentialStmtBlock>();
                generator->add_stmt(blocks[i]);
                blocks[i]->add_condition({BlockEdgeType::Posedge, clock_port});
                if (generator->debug)
                    blocks[i]->fn_name_ln.emplace_back(std::make_pair(__FILE__, __LINE__));
            }
            // get all the outputs
            for (auto const& port_name : port_names) {
                auto port = generator->get_port(port_name);
                if (port->port_direction() == PortDirection::In) {
                    continue;
                }
                std::vector<std::shared_ptr<Var>> vars;
                vars.resize(num_stages);
                for (uint32_t i = 0; i < num_stages; i++) {
                    auto new_name =
                        generator->get_unique_variable_name(port_name, ::format("stage_{0}", i));
                    auto& var = generator->var(new_name, port->var_width(), port->size(),
                                               port->is_signed());
                    if (generator->debug)
                        var.fn_name_ln.emplace_back(std::make_pair(__FILE__, __LINE__));
                    vars[i] = var.shared_from_this();
                }
                // move the source to the first stage
                Var::move_src_to(port.get(), vars[0].get(), generator, false);
                // connect the stages together
                for (uint32_t i = 0; i < num_stages - 1; i++) {
                    auto pre_stage = vars[i];
                    auto next_stage = vars[i + 1];
                    blocks[i]->add_stmt(next_stage->assign(pre_stage, AssignmentType::NonBlocking));
                }
                // last stage
                blocks[num_stages - 1]->add_stmt(
                    port->assign(vars[num_stages - 1], AssignmentType::NonBlocking));
            }
        }
    }
};

void insert_pipeline_stages(Generator* top) {
    PipelineInsertionVisitor visitor;
    visitor.visit_generator_root_p(top);
}

bool static has_port_type(Var* var, PortType type) {
    if (var->type() == VarType::Expression) {
        auto* expr = reinterpret_cast<Expr*>(var);
        auto l = has_port_type(expr->left, type);
        if (expr->right) {
            auto r = has_port_type(expr->right, type);
            return l && r;
        }
        return l;
    }
    if (var->type() == VarType::PortIO) {
        auto* p = reinterpret_cast<Port*>(var);
        return p->port_type() == type;
    } else if (var->type() == VarType::BaseCasted) {
        auto* casted = reinterpret_cast<VarCasted*>(var);
        if (type == PortType::AsyncReset)
            return casted->cast_type() == VarCastType::AsyncReset;
        else if (type == PortType::ClockEnable)
            return casted->cast_type() == VarCastType::ClockEnable;
        else if (type == PortType::Clock)
            return casted->cast_type() == VarCastType::Clock;
    }
    return false;
}

static std::shared_ptr<IfStmt> create_if_stmt_wrapper(StmtBlock* block, Port& port,
                                                      bool clone = false) {
    auto if_ = std::make_shared<IfStmt>(port);
    std::vector<std::shared_ptr<Stmt>> stmts;
    for (auto const& stmt : *block) {
        stmts.emplace_back(clone ? stmt->clone() : stmt);
    }
    if (!clone) block->clear();
    for (auto& stmt : stmts) {
        if (!clone) stmt->remove_from_parent();
        if_->add_then_stmt(stmt);
    }
    return if_;
}

class InsertClockIRVisitor : public IRVisitor {
public:
    explicit InsertClockIRVisitor(Generator* top) : top_(top) {
        // find out the top clock enable signal
        auto ports = top->get_ports(PortType::ClockEnable);
        // LCOV_EXCL_START
        if (ports.empty()) {
            clk_en_ = nullptr;
        } else if (ports.size() > 1) {
            throw UserException("Current the pass only support one clock enable signal in top");
        } else {
            // LCOV_EXCL_STOP
            clk_en_name_ = ports[0];
            clk_en_ = top->get_port(clk_en_name_).get();
        }
    }

    void visit(Generator* gen) override {
        if (!clk_en_) return;
        if (gen->external() || gen->is_stub()) return;
        auto* parent = gen->parent_generator();
        if (!parent || gen == top_) return;

        Port* clk_en;
        if (!gen->has_port(clk_en_name_)) {
            clk_en = &gen->port(*clk_en_);
            if (clk_en->port_type() != PortType::ClockEnable)
                clk_en->set_port_type(PortType::ClockEnable);
        } else {
            clk_en = gen->get_port(clk_en_name_).get();
            // notice that if it's being wired to a constant, we need to disconnect it
            auto const& sources = clk_en->sources();
            if (!sources.empty()) {
                if ((*(sources.begin()))->right()->type() == VarType::ConstValue) {
                    auto stmt = *(sources.begin());
                    clk_en->clear_sources(true);
                } else {
                    // no need to wire
                    return;
                }
            }
        }
        // wire to the top
        auto parent_port = parent->get_port(clk_en_name_);
        assert(parent_port);
        parent->wire(*clk_en, *parent_port);
    }

    void visit(SequentialStmtBlock* block) override {
        if (!clk_en_) return;
        auto num_stmts = block->size();
        auto* generator = block->generator_parent();
        auto clk_en = generator->get_port(clk_en_name_);
        if (num_stmts > 0) {
            // we need to be careful about async reset logic
            auto first_stmt = block->get_stmt(0);
            if (num_stmts == 1 && first_stmt->type() == StatementType::If) {
                // async reset?
                auto if_ = first_stmt->as<IfStmt>();
                auto cond = if_->predicate();
                if (has_port_type(cond.get(), PortType::AsyncReset) ||
                    has_port_type(cond.get(), PortType::Reset)) {
                    if (!has_clk_en_stmt(if_->else_body().get())) {
                        auto new_if = create_if_stmt_wrapper(if_->else_body().get(), *clk_en, true);
                        if_->else_body()->clear();
                        if_->add_else_stmt(new_if);
                    }
                    return;
                }
            }
            // put everything into one block
            // if not clk enabled already
            if (!has_clk_en_stmt(block)) {
                auto if_ = create_if_stmt_wrapper(block, *clk_en, true);
                block->clear();
                block->add_stmt(if_);
            }
        }
    }

private:
    std::string clk_en_name_;
    Port* clk_en_;
    Generator* top_;

    bool has_clk_en_stmt(StmtBlock* block) const {
        if (!block->empty()) {
            auto stmt = block->get_stmt(0);
            if (stmt->type() == StatementType::If) {
                auto if_ = stmt->as<IfStmt>();
                auto cond = if_->predicate();
                if (cond->type() == VarType::PortIO) {
                    auto p = cond->as<Port>();
                    if (p->port_type() == PortType::ClockEnable) {
                        return true;
                    }
                } else if (cond->type() == VarType::BaseCasted) {
                    auto casted = cond->as<VarCasted>();
                    return casted->cast_type() == VarCastType::ClockEnable;
                } else if (cond->name == clk_en_name_) {
                    return true;
                }
            }
        }
        return false;
    }
};

void auto_insert_clock_enable(Generator* top) {
    InsertClockIRVisitor visitor(top);
    visitor.visit_root(top);
}

class InsertSyncReset : public IRVisitor {
public:
    explicit InsertSyncReset(Generator* gen) {
        auto const& attributes = gen->get_attributes();
        for (auto const& attr : attributes) {
            auto const& value = attr->value_str;
            if (value.size() > sync_reset_name.size()) {
                if (value.substr(0, sync_reset_name.size()) == sync_reset_name) {
                    // get reset_name
                    auto tokens = string::get_tokens(value, ";");
                    auto first_token = tokens[0];
                    {
                        auto token_values = string::get_tokens(first_token, "=");
                        if (token_values.size() == 2) {
                            auto var_name = token_values[1];
                            if (is_valid_variable_name(var_name)) {
                                run_pass_ = true;
                                reset_name_ = var_name;
                            }
                        }
                    }
                    if (tokens.size() == 2) {
                        auto param_value = tokens[1];
                        auto token_values = string::get_tokens(param_value, "=");
                        if (token_values.size() == 2 && token_values[0] == "over_clk_en") {
                            if (token_values[1] == "true" || token_values[1] == "1") {
                                over_clk_en_ = true;
                            }
                        }
                    }
                }
            }
        }
    }

    void visit(Generator* generator) override {
        if (generator->external() || generator->is_stub()) return;
        if (!run_pass_) return;
        Port* port;
        if (generator->has_port(reset_name_)) {
            port = generator->get_port(reset_name_).get();
            if (port->port_type() != PortType::Reset) {
                port->set_port_type(PortType::Reset);
            }
        } else {
            // create a synchronous reset port
            port = &generator->port(PortDirection::In, reset_name_, 1, PortType::Reset);
            // look through each sequential block
            auto stmts_count = generator->stmts_count();
            for (uint64_t i = 0; i < stmts_count; i++) {
                auto stmt = generator->get_stmt(i);
                if (stmt->type() == StatementType::Block) {
                    auto blk = stmt->as<StmtBlock>();
                    if (blk->block_type() == StatementBlockType::Sequential) {
                        auto seq = blk->as<SequentialStmtBlock>();
                        inject_reset_logic(seq.get(), port);
                    }
                }
            }
        }

        // wire the children. we do in this order since this pass is run in parallel from bottom
        // up
        for (auto const& child : generator->get_child_generators()) {
            if (child->has_port(reset_name_)) {
                auto child_port = child->get_port(reset_name_);
                auto sources = child_port->sources();
                if (sources.size() > 1) continue;
                if (sources.size() == 1) {
                    auto right = (*sources.begin())->right();
                    if (right->type() == VarType::ConstValue) {
                        child_port->clear_sources(true);
                    }
                }
                generator->wire(*child_port, *port);
            }
        }
    }

private:
    bool run_pass_ = false;
    bool over_clk_en_ = false;
    std::string reset_name_;
    const std::string sync_reset_name = "sync-reset";

    void inject_reset_logic(SequentialStmtBlock* block, Port* port) const {
        // only inject when there is a async reset logic
        auto stmts_count = block->size();
        if (stmts_count != 1) return;
        auto stmt = block->get_stmt(0);
        if (stmt->type() != StatementType::If) return;
        auto if_ = stmt->as<IfStmt>();
        auto const& cond = if_->predicate();
        // if it doesn't have async reset logic, or it already has sync reset logic
        // quit
        if (!has_port_type(cond.get(), PortType::AsyncReset) ||
            has_port_type(cond.get(), PortType::Reset))
            return;
        auto* reset_stmt = if_->then_body().get();
        // okay we have reset now. now we need to detect if it has clock enable
        // logic or not
        // we need to detect the clock enable logic and make sure that the ordering is what
        // specified in the
        auto else_body = if_->else_body();
        // detect if clock enable have been in place
        if (else_body->size() == 1) {
            auto then_stmt = else_body->get_stmt(0);
            if (then_stmt->type() == StatementType::If) {
                auto if_then = then_stmt->as<IfStmt>();
                auto target = if_then->predicate();
                if (has_port_type(target.get(), PortType::ClockEnable) && !over_clk_en_) {
                    // insert inside the clock enable body
                    auto body = if_then->then_body()->clone()->as<ScopedStmtBlock>();
                    // need to duplicate the logic in reset
                    auto sync_reset = create_if_stmt_wrapper(reset_stmt, *port, true);
                    sync_reset->set_else(body);
                    if_then->then_body()->clear();
                    if_then->add_then_stmt(sync_reset);
                    return;
                }
            }
        }
        auto sync_reset = create_if_stmt_wrapper(reset_stmt, *port, true);
        auto body = else_body->clone()->as<ScopedStmtBlock>();
        sync_reset->set_else(body);
        else_body->clear();
        else_body->add_stmt(sync_reset);
    }
};

void auto_insert_sync_reset(Generator* top) {
    InsertSyncReset visitor(top);
    visitor.visit_generator_root_p(top);
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
        PackedStruct struct_(bundle_name, def);
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

bool check_stmt_condition(Stmt* stmt, const std::function<bool(Stmt*)>& cond,
                          bool check_unreachable = false, bool full_branch = true) {
    if (cond(stmt)) {
        return true;
    } else if (stmt->type() == StatementType::Block) {
        // it has to be the last block
        uint64_t index;
        bool found = false;
        auto* block = dynamic_cast<StmtBlock*>(stmt);
        if (!block)
            throw InternalException("Statement is not block but is marked as StatementType::Block");
        auto stmt_count = block->size();
        for (index = 0; index < stmt_count; index++) {
            auto* s = block->get_stmt(index).get();
            if (check_stmt_condition(s, cond, check_unreachable, full_branch)) {
                found = true;
                break;
            }
        }
        if (found && check_unreachable) {
            if (index != block->size() - 1) {
                // we have unreachable state
                std::vector<Stmt*> stmts;
                for (uint64_t i = index + 1; i < block->size(); i++)
                    stmts.emplace_back(block->get_stmt(i).get());
                throw StmtException("Unreachable code block", stmts.begin(), stmts.end());
            }
        }
        return found;
    } else if (stmt->type() == StatementType::Switch) {
        auto* stmt_ = dynamic_cast<SwitchStmt*>(stmt);
        if (!stmt_)
            throw InternalException(
                "Statement is not switch but is marked as StatementType::Switch");
        auto cases = stmt_->body();
        if (cases.empty()) return false;
        uint32_t found_case = 0;
        for (auto const& iter : cases) {
            auto* scope_stmt = iter.second.get();
            if (check_stmt_condition(scope_stmt, cond, check_unreachable, full_branch))
                found_case++;
            else if (full_branch)
                return false;
        }
        // make sure default case is covered
        // if there is no default case, all the cases have to be covered
        // the only exception is that if the target is an enum and we've covered all it's enum case
        uint32_t targeted_cases;
        if (stmt_->target()->is_enum()) {
            auto* enum_var = dynamic_cast<EnumType*>(stmt_->target().get());
            if (!enum_var) throw InternalException("Unable to resolve enum type");
            auto* enum_def = enum_var->enum_type();
            targeted_cases = enum_def->values.size();
        } else {
            targeted_cases = 1u << stmt_->target()->width();
        }
        if (full_branch) {
            return cases.find(nullptr) != cases.end() || found_case == targeted_cases;
        } else {
            return found_case > 0;
        }
    } else if (stmt->type() == StatementType::If) {
        auto* stmt_ = dynamic_cast<IfStmt*>(stmt);
        if (!stmt_)
            throw InternalException("Statement is not if but is marked as StatementType::If");
        auto const& then = stmt_->then_body();
        auto const& else_ = stmt_->else_body();
        if (full_branch) {
            return check_stmt_condition(then.get(), cond, check_unreachable, full_branch) &&
                   check_stmt_condition(else_.get(), cond, check_unreachable, full_branch);
        } else {
            return check_stmt_condition(then.get(), cond, check_unreachable, full_branch) ||
                   check_stmt_condition(else_.get(), cond, check_unreachable, full_branch);
        }
    } else if (stmt->type() == StatementType::For) {
        auto* stmt_ = dynamic_cast<ForStmt*>(stmt);
        if (!stmt_)
            throw InternalException("Statement is not if but is marked as StatementType::For");
        auto body = stmt_->get_loop_body();
        return check_stmt_condition(body.get(), cond, check_unreachable, full_branch);
    }
    return false;
}

class FunctionReturnVisitor : public IRVisitor {
public:
    void visit(Generator* generator) override {
        // check all the function definitions
        auto functions = generator->functions();
        for (auto const& iter : functions) {
            auto func = iter.second;
            // check if the function has a return
            if (!func->has_return_value()) continue;
            // build statement graph
            bool has_return = check_stmt_condition(
                func.get(),
                [](Stmt* stmt) -> bool { return stmt->type() == StatementType::Return; }, true);
            if (!has_return) {
                std::vector<Stmt*> stmts;
                stmts.reserve(func->size());
                for (uint64_t i = 0; i < func->size(); i++) {
                    stmts.emplace_back(func->get_stmt(i).get());
                }
                throw StmtException(
                    ::format("{0} does not have return statement in all control flows",
                             func->function_name()),
                    stmts.begin(), stmts.end());
            }
        }
    }
};

void check_function_return(Generator* top) {
    FunctionReturnVisitor visitor;
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

class LatchVisitor : public IRVisitor {
public:
    void visit(Generator* generator) override {
        uint64_t stmt_count = generator->stmts_count();
        for (uint64_t i = 0; i < stmt_count; i++) {
            auto stmt = generator->get_stmt(i);
            if (stmt->type() == StatementType::Block) {
                auto blk = stmt->as<StmtBlock>();
                if (blk->block_type() == StatementBlockType::Combinational) {
                    // multiple passes to extract assigned variables
                    auto stmt_ = blk->as<CombinationalStmtBlock>();
                    check_combinational(stmt_.get());
                } else if (blk->block_type() == StatementBlockType::Sequential) {
                    // multiple passes to extract assigned variables
                    auto stmt_ = blk->as<SequentialStmtBlock>();
                    check_sequential(stmt_.get());
                }
            }
        }
    }

private:
    bool static check_stmt_block(StmtBlock* stmt, Var* var, bool full_branch) {
        return check_stmt_condition(
            stmt,
            [=](Stmt* s) -> bool {
                if (s->type() == StatementType::Assign) {
                    auto assign = s->as<AssignStmt>();
                    return assign->left() == var;
                }
                return false;
            },
            false, full_branch);
    }

    static void check_stmt_block(StmtBlock* stmt, Var* var, const std::vector<Stmt*>& stmts,
                                 bool full_branch) {
        auto check = [=](Stmt* s) -> bool {
            if (s->type() == StatementType::Assign) {
                auto* assign = reinterpret_cast<AssignStmt*>(s);
                auto* left = assign->left();
                if (left->type() == VarType::Slice) {
                    auto* slice = reinterpret_cast<VarSlice*>(left);
                    left = const_cast<Var*>(slice->get_var_root_parent());
                }
                return left == var;
            } else if (s->type() == StatementType::Block) {
                auto* block = reinterpret_cast<StmtBlock*>(s);
                if (block->block_type() == StatementBlockType::Function) {
                    // function call to set the variable
                    return check_stmt_block(block, var, full_branch);
                }
            }
            return false;
        };
        if (!check_stmt_condition(stmt, check, false, full_branch)) {
            // things goes wrong
            // need to recover all the statements
            throw StmtException(::format("{0} will be inferred as latch", var->to_string()),
                                stmts.begin(), stmts.end());
        }
    }

    void static check_combinational(CombinationalStmtBlock* stmt) {
        AssignedVarVisitor visitor;
        visitor.visit_root(stmt);
        const auto& vars = visitor.assigned_vars();
        for (auto const& iter : vars) {
            check_stmt_block(stmt, iter.first, iter.second, true);
        }
    }

    void static check_sequential(SequentialStmtBlock* stmt) {
        auto const& conditions = stmt->get_conditions();
        // we care about non-clock
        for (auto const& iter : conditions) {
            auto* var = iter.second.get();
            if (var->type() == VarType::PortIO) {
                auto* port = reinterpret_cast<Port*>(var);
                if (port->port_type() == PortType::Clock) continue;
            }
            // check every if statement that's targeted by that variable
            IfVisitor visitor(var);
            visitor.visit_root(stmt);
            auto ifs = visitor.ifs();
            // derive the variables to check
            for (auto const& if_ : ifs) {
                AssignedVarVisitor a_v;
                a_v.visit_root(if_->then_body().get());
                auto vars = a_v.assigned_vars();
                for (auto const& [var, stmts] : vars) {
                    check_stmt_block(if_->else_body().get(), var, stmts, false);
                }
            }
        }
    }

    class IfVisitor : public IRVisitor {
    public:
        explicit IfVisitor(Var* var) : var_(var) {}
        void visit(IfStmt* stmt) override {
            if (has_var(stmt->predicate().get(), var_)) ifs_.emplace(stmt);
        }
        const std::unordered_set<IfStmt*>& ifs() const { return ifs_; }

    private:
        Var* var_;
        std::unordered_set<IfStmt*> ifs_;

        bool static has_var(Var* var, Var* target) {
            if (var->type() == VarType::Expression) {
                auto* expr = var->as<Expr>().get();
                bool left = has_var(expr->left, target);
                bool right = expr->right ? has_var(expr->right, target) : false;
                return left || right;
            } else {
                if (var->type() == VarType::Slice) {
                    auto* slice = reinterpret_cast<VarSlice*>(var);
                    var = const_cast<Var*>(slice->get_var_root_parent());
                }
                return var == target;
            }
        }
    };

    class AssignedVarVisitor : public IRVisitor {
    public:
        void visit(AssignStmt* stmt) override {
            auto* left = stmt->left();
            if (left->type() == VarType::Slice) {
                auto* slice = reinterpret_cast<VarSlice*>(left);
                if (slice->sliced_by_var()) {
                    return;
                }
                left = const_cast<Var*>(slice->get_var_root_parent());
            }
            assigned_vars_[left].emplace_back(stmt);
        }
        const std::unordered_map<Var*, std::vector<Stmt*>>& assigned_vars() const {
            return assigned_vars_;
        }

    private:
        std::unordered_map<Var*, std::vector<Stmt*>> assigned_vars_;
    };
};

void check_inferred_latch(Generator* top) {
    LatchVisitor visitor;
    visitor.visit_generator_root_p(top);
}

class MultipleDriverVisitor : public IRVisitor {
public:
    void visit(Var* var) override { check_var(var); }
    void visit(Port* port) override { check_var(port); }

private:
    static bool share_root(IRNode* node1, IRNode* node2) {
        std::set<IRNode*> nodes1;
        std::set<IRNode*> nodes2;
        while (node1->parent() && node1->parent()->ir_node_kind() == IRNodeKind::StmtKind) {
            nodes1.emplace(node1);
            node1 = node1->parent();
        }
        while (node2->parent() && node2->parent()->ir_node_kind() == IRNodeKind::StmtKind) {
            nodes2.emplace(node2);
            node2 = node2->parent();
        }
        std::set<IRNode*> diff;
        std::set_intersection(nodes1.begin(), nodes1.end(), nodes2.begin(), nodes2.end(),
                              std::inserter(diff, diff.begin()));
        return !diff.empty();
    }

    static bool has_for_loop(Stmt* stmt) {
        if (stmt->type() == StatementType::For) {
            return true;
        } else {
            auto* p = stmt->parent();
            if (p && p->ir_node_kind() == IRNodeKind::StmtKind) {
                return has_for_loop(reinterpret_cast<Stmt*>(p));
            }
        }
        return false;
    }

    static void check_var(Var* var) {
        std::unordered_map<uint32_t, std::pair<IRNode*, Stmt*>> parents;
        for (auto const& stmt : var->sources()) {
            // TODO: FIX THIS
            //  This is a hack to bypass the check if there is a for loop
            if (has_for_loop(stmt.get())) continue;
            auto* v = stmt->left();
            if (v->get_var_root_parent() != var) continue;
            uint32_t var_low = v->var_low();
            uint32_t var_high = v->var_high();
            for (uint32_t i = var_low; i <= var_high; i++) {
                if (parents.find(i) != parents.end()) {
                    auto* parent = stmt->parent();
                    auto* stmt_parent = non_gen_root_parent(stmt.get());
                    auto const& [ref_parent, ref_stmt_parent] = parents.at(i);
                    // the purpose of the following statement is to make sure that there is no
                    // other assignment that's assigning the same var slice in the same scope
                    // it cannot be driven through different blocks, either.
                    // notice that there is a caveat. in combinational block, as long as the
                    // they are in the same stmt parent, they can have different scope, since
                    // having different scope implies priority. as a result, we need to filter
                    // this case out
                    bool has_multiple_driver = stmt_parent != ref_stmt_parent;
                    if (!has_multiple_driver) {
                        // skip the special case
                        if (parent == ref_parent) {
                            has_multiple_driver = true;
                            if (stmt_parent->ir_node_kind() == IRNodeKind::StmtKind) {
                                auto* st = dynamic_cast<Stmt*>(stmt_parent);
                                if (st && st->type() == StatementType::Block) {
                                    auto* block = dynamic_cast<StmtBlock*>(st);
                                    if (block->block_type() == StatementBlockType::Combinational ||
                                        block->block_type() == StatementBlockType::Latch) {
                                        has_multiple_driver = false;
                                    }
                                }
                            }
                        } else {
                            if (stmt_parent->ir_node_kind() == IRNodeKind::StmtKind) {
                                auto* st = dynamic_cast<Stmt*>(stmt_parent);
                                if (st && st->type() == StatementType::Block) {
                                    auto* block = dynamic_cast<StmtBlock*>(st);
                                    if (block->block_type() == StatementBlockType::Sequential) {
                                        // TODO: this algorithm is not perfect as it only
                                        //  accounts for standalone assignments
                                        has_multiple_driver = !share_root(parent, ref_parent);
                                    }
                                }
                            }
                        }
                    }
                    if (has_multiple_driver) {
                        throw StmtException(::format("{0} has multiple driver in the same scope",
                                                     var->handle_name()),
                                            {var, parent, stmt.get()});
                    }
                } else {
                    parents.emplace(
                        i, std::make_pair(stmt->parent(), non_gen_root_parent(stmt.get())));
                }
            }
        }
    }

    static Stmt* non_gen_root_parent(Stmt* stmt) {
        // this is just to get the root stmt parent that's holding given stmt
        IRNode* parent = stmt;
        uint32_t count = 0;
        while (parent->parent() && parent->parent()->ir_node_kind() == IRNodeKind::StmtKind) {
            parent = parent->parent();
            // this is to prevent infinite loop
            if (count++ > 10000) {
                throw InternalException(::format("Unable to find parent for statement"));
            }
        }
        return reinterpret_cast<Stmt*>(parent);
    }
};

void check_multiple_driver(Generator* top) {
    MultipleDriverVisitor visitor;
    visitor.visit_content(top);
}

class CombinationalLoopVisitor : public IRVisitor {
public:
    void visit(Port* port) override { check_var(port); }
    void visit(Var* var) override { check_var(var); }

private:
    static void check_var(Var* var) {
        // get all the sources
        auto const& sources = var->sources();
        for (auto const& stmt : sources) {
            if (stmt->assign_type() == AssignmentType::Blocking && has_var(stmt->right(), var)) {
                throw StmtException(::format("Combinational loop detected at {0} <- {1}",
                                             stmt->left()->to_string(), stmt->right()->to_string()),
                                    {stmt.get(), var});
            }
        }
    }

    static bool has_var(Var* var, Var* target) {
        if (!var) return false;
        if (var == target) return true;
        if (var->type() == VarType::Expression) {
            auto* expr = reinterpret_cast<Expr*>(var);
            return has_var(expr->left, target) || has_var(expr->right, target);
        }
        return false;
    }
};

void check_combinational_loop(Generator* top) {
    CombinationalLoopVisitor visitor;
    visitor.visit_root(top);
}

class CheckFlipFlopAlwaysFFVisitor : public IRVisitor {
public:
    void visit(Generator* gen) override {
        uint64_t stmt_count = gen->stmts_count();
        for (uint64_t i = 0; i < stmt_count; i++) {
            auto stmt = gen->get_stmt(i);
            if (stmt->type() == StatementType::Block) {
                auto block = stmt->as<StmtBlock>();
                if (block->block_type() == StatementBlockType::Sequential) {
                    check_always_ff(block->as<SequentialStmtBlock>().get());
                }
            }
        }
    }

private:
    void static check_always_ff(SequentialStmtBlock* stmt) {
        // first pass to determine if there is any if statement in top level
        bool has_if = false;
        uint64_t i = 0;
        uint64_t stmt_count = stmt->size();
        while ((!has_if) && (i < stmt_count)) {
            auto s = stmt->get_stmt(i);
            if (s->type() == StatementType::If) has_if = true;
            i++;
        }
        if (has_if && stmt->size() > 1) {
            // DC cannot infer as a D-flip-flop
            // error message copied from DC
            throw StmtException(
                "The statements in this 'always' block are outside the "
                "scope of the synthesis policy. Only an ’if’ statement "
                "is allowed at the top level in this ’always’ block. (ELAB-302)",
                {stmt});
        }
    }
};

void check_flip_flop_always_ff(Generator* top) {
    CheckFlipFlopAlwaysFFVisitor visitor;
    visitor.visit_generator_root_p(top);
}

void sort_stmts(Generator* top) {
    SortStmtVisitor visitor;
    visitor.visit_generator_root_p(top);
}

class RemoveEmptyBlockVisitor : public IRVisitor {
public:
    void visit(Generator* top) override {
        auto stmt_count = top->stmts_count();
        std::vector<std::shared_ptr<Stmt>> stmts_to_remove;
        for (uint64_t i = 0; i < stmt_count; i++) {
            auto stmt = top->get_stmt(i);
            if (!dispatch_node(stmt)) stmts_to_remove.emplace_back(stmt);
        }
        for (auto const& stmt : stmts_to_remove) {
            top->remove_stmt(stmt);
        }
    }

private:
    std::shared_ptr<IfStmt> process(std::shared_ptr<IfStmt> stmt) {
        auto then_ = stmt->then_body();
        auto then_body = process(then_);
        auto else_body = process(stmt->else_body());
        if (!then_body) {
            // then is empty
            if (else_body->empty()) {
                return nullptr;
            } else {
                // invert the condition and make else then
                auto cond = stmt->predicate();
                auto& new_cond = ~(*cond);
                stmt->set_predicate(new_cond.shared_from_this());
                stmt->set_then(else_body->as<ScopedStmtBlock>());
                stmt->set_else(std::make_shared<ScopedStmtBlock>());
                return stmt;
            }
        }
        stmt->set_then(then_body->as<ScopedStmtBlock>());
        return stmt;
    }

    std::shared_ptr<StmtBlock> process(std::shared_ptr<StmtBlock> stmt) {
        auto stmt_count = stmt->size();
        std::vector<std::shared_ptr<Stmt>> stmts_to_remove;
        for (uint64_t i = 0; i < stmt_count; i++) {
            auto st = stmt->get_stmt(i);
            auto r = dispatch_node(st);
            if (!r) {
                stmts_to_remove.emplace_back(st);
                continue;
            }
            stmt->set_child(i, r);
        }
        for (auto const& st : stmts_to_remove) {
            stmt->remove_stmt(st);
        }
        if (stmt->empty())
            return nullptr;
        else
            return stmt;
    }

    std::shared_ptr<SwitchStmt> process(std::shared_ptr<SwitchStmt> stmt) {
        std::map<std::shared_ptr<Const>, std::shared_ptr<ScopedStmtBlock>> new_body;
        auto const& body = stmt->body();
        for (const auto& [cond, block] : body) {
            auto r = process(block);
            if (r) {
                new_body.emplace(cond, r->as<ScopedStmtBlock>());
            }
        }
        if (new_body.empty()) return nullptr;
        stmt->set_body(new_body);
        return stmt;
    }

    std::shared_ptr<Stmt> dispatch_node(std::shared_ptr<Stmt> stmt) {
        if (stmt->type() == StatementType::If) {
            return process(std::static_pointer_cast<IfStmt>(stmt));
        } else if (stmt->type() == StatementType::Switch) {
            return process(std::static_pointer_cast<SwitchStmt>(stmt));
        } else if (stmt->type() == StatementType::Block) {
            return process(std::static_pointer_cast<ScopedStmtBlock>(stmt));
        } else {
            return stmt;
        }
    }
};

void remove_empty_block(Generator* top) {
    RemoveEmptyBlockVisitor visitor;
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

class GeneratorVarVisitor : public IRVisitor {
public:
    explicit GeneratorVarVisitor(bool registers_only) : registers_only_(registers_only) {}

    void visit(Generator* generator) override {
        auto vars = generator->get_all_var_names();
        for (auto const& var_name : vars) {
            auto const& var = generator->get_var(var_name);
            if (!var)
                throw InternalException(
                    ::format("Cannot get {0} from {1}", var_name, generator->name));
            // detect if it has any non-blocking assignment
            auto const& sources = var->sources();
            if (registers_only_) {
                if (sources.empty()) continue;
                auto const& stmt = *(sources.begin());
                // only if a variable has non-blocking assignment
                // we assume that at this state we have already have all the assignment checked and
                // fixed
                if (stmt->assign_type() == AssignmentType::NonBlocking)
                    names_.emplace_back(var->handle_name());
            } else {
                names_.emplace_back(var->handle_name());
            }
        }
    }

    const std::vector<std::string>& names() const { return names_; }

private:
    bool registers_only_;
    std::vector<std::string> names_;
};

std::vector<std::string> extract_register_names(Generator* top) {
    // first fix the assignment types
    fix_assignment_type(top);
    // this pass extract the absolute handle name for each generator accessible from the top
    // no need for parallel version since the pass is so simple, otherwise we have to use mutex
    // lock on names
    GeneratorVarVisitor visitor(true);
    visitor.visit_generator_root(top);
    return visitor.names();
}

std::vector<std::string> extract_var_names(Generator* top) {
    GeneratorVarVisitor visitor(false);
    visitor.visit_generator_root(top);
    return visitor.names();
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

    register_pass("inject_clock_break_points", &inject_clock_break_points);

    register_pass("inject_assert_fail_exception", &inject_assert_fail_exception);

    register_pass("insert_verilator_public", &insert_verilator_public);

    register_pass("remove_assertion", &remove_assertion);

    register_pass("check_always_sensitivity", &check_always_sensitivity);

    register_pass("check_inferred_latch", &check_inferred_latch);

    register_pass("check_multiple_driver", &check_multiple_driver);

    register_pass("check_combinational_loop", &check_combinational_loop);

    register_pass("check_flip_flop_always_ff", &check_flip_flop_always_ff);

    register_pass("convert_continuous_stmt", &convert_continuous_stmt);

    register_pass("propagate_scope_variable", &propagate_scope_variable);

    register_pass("change_property_into_stmt", &change_property_into_stmt);

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
}

}  // namespace kratos
