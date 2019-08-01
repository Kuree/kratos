#include "generator.hh"
#include <fstream>
#include <iostream>
#include <streambuf>
#include <unordered_set>
#include "except.hh"
#include "fmt/format.h"
#include "stmt.hh"
#include "util.hh"

using fmt::format;
using std::runtime_error;
using std::string;
using std::vector;

namespace kratos {

Generator Generator::from_verilog(Context *context, const std::string &src_file,
                                  const std::string &top_name,
                                  const std::vector<std::string> &lib_files,
                                  const std::map<std::string, PortType> &port_types) {
    if (!fs::exists(src_file)) throw ::runtime_error(::format("{0} does not exist", src_file));

    Generator mod(context, top_name);
    // the src file will be treated a a lib file as well
    mod.lib_files_.reserve(1 + lib_files.size());
    mod.lib_files_.emplace_back(src_file);

    std::ifstream f(src_file);
    ::string src;
    // pre-allocate the size
    f.seekg(0, std::ios::end);
    src.reserve(f.tellg());
    f.seekg(0, std::ios::beg);
    src.assign(std::istreambuf_iterator<char>(f), std::istreambuf_iterator<char>());

    mod.lib_files_.insert(mod.lib_files_.end(), lib_files.begin(), lib_files.end());
    // const auto &ports = ;
    const auto ports = get_port_from_verilog(&mod, src, top_name);
    for (auto const &[port_name, port] : ports) {
        mod.ports_.emplace(port_name);
        mod.vars_.emplace(port_name, port);
    }
    // verify the existence of each lib files
    for (auto const &filename : mod.lib_files_) {
        if (!fs::exists(filename)) throw ::runtime_error(::format("{0} does not exist", filename));
    }

    // assign port types
    for (auto const &[port_name, port_type] : port_types) {
        if (mod.ports_.find(port_name) == mod.ports_.end())
            throw ::runtime_error(::format("unable to find port {0}", port_name));
        std::shared_ptr<Var> &var_p = mod.vars_.at(port_name);
        std::shared_ptr<Port> port_p = std::static_pointer_cast<Port>(var_p);
        port_p->set_port_type(port_type);
    }

    return mod;
}

Var &Generator::var(const std::string &var_name, uint32_t width, uint32_t size) {
    return var(var_name, width, size, false);
}

Var &Generator::var(const std::string &var_name, uint32_t width, uint32_t size, bool is_signed) {
    if (vars_.find(var_name) != vars_.end()) {
        auto v_p = get_var(var_name);
        if (v_p->width != width || v_p->is_signed != is_signed)
            throw std::runtime_error(
                ::format("redefinition of {0} with different width/sign", var_name));
        return *v_p;
    }
    auto p = std::make_shared<Var>(this, var_name, width, size, is_signed);
    vars_.emplace(var_name, p);
    return *p;
}

std::shared_ptr<Var> Generator::get_var(const std::string &var_name) {
    if (vars_.find(var_name) == vars_.end()) return nullptr;
    return vars_.at(var_name);
}

Port &Generator::port(PortDirection direction, const std::string &port_name, uint32_t width,
                      uint32_t size) {
    return port(direction, port_name, width, size, PortType::Data, false);
}

Port &Generator::port(PortDirection direction, const std::string &port_name, uint32_t width,
                      uint32_t size, PortType type, bool is_signed) {
    if (ports_.find(port_name) != ports_.end())
        throw ::runtime_error(::format("{0} already exists in {1}", port_name, name));
    auto p = std::make_shared<Port>(this, direction, port_name, width, size, type, is_signed);
    vars_.emplace(port_name, p);
    ports_.emplace(port_name);
    return *p;
}

std::shared_ptr<Port> Generator::get_port(const std::string &port_name) const {
    if (ports_.find(port_name) == ports_.end()) return nullptr;
    auto var_p = vars_.at(port_name);
    return std::static_pointer_cast<Port>(var_p);
}

Expr &Generator::expr(ExprOp op, const std::shared_ptr<Var> &left,
                      const std::shared_ptr<Var> &right) {
    auto expr = std::make_shared<Expr>(op, left, right);
    exprs_.emplace(expr);
    return *expr;
}

Const &Generator::constant(int64_t value, uint32_t width) { return constant(value, width, false); }

Const &Generator::constant(int64_t value, uint32_t width, bool is_signed) {
    auto ptr = std::make_shared<Const>(this, value, width, is_signed);
    consts_.emplace(ptr);
    return *ptr;
}

Param &Generator::parameter(const std::string &parameter_name, uint32_t width) {
    return parameter(parameter_name, width, false);
}

Param &Generator::parameter(const std::string &parameter_name, uint32_t width, bool is_signed) {
    if (params_.find(parameter_name) != params_.end())
        throw runtime_error(::format("parameter {0} already exists", parameter_name));
    auto ptr = std::make_shared<Param>(this, parameter_name, width, is_signed);
    params_.emplace(parameter_name, ptr);
    return *ptr;
}

IRNode *Generator::get_child(uint64_t index) {
    if (index < stmts_count()) {
        return stmts_[index].get();
    } else if (index < stmts_count() + get_child_generator_size()) {
        auto n = child_names_[index - stmts_count()];
        return children_.at(n).get();
    } else {
        return nullptr;
    }
}

void Generator::add_child_generator(const std::string &instance_name_,
                                    const std::shared_ptr<Generator> &child) {
    child->instance_name = instance_name_;
    if (children_.find(child->instance_name) == children_.end()) {
        children_.emplace(child->instance_name, child);
        child->parent_generator_ = this;
        child_names_.emplace_back(child->instance_name);
    } else {
        throw std::runtime_error(
            ::format("{0} already exists  in {1}", child->instance_name, instance_name));
    }
}

void Generator::add_child_generator(const std::string &instance_name_,
                                    const std::shared_ptr<Generator> &child,
                                    const std::pair<std::string, uint32_t> &debug_info) {
    if (debug) {
        children_debug_.emplace(instance_name_, debug_info);
    }
    add_child_generator(instance_name_, child);
}

void Generator::remove_child_generator(const std::shared_ptr<Generator> &child) {
    auto child_name = child->instance_name;
    auto pos = std::find(child_names_.begin(), child_names_.end(), child_name);
    if (pos != child_names_.end()) {
        child_names_.erase(pos);
        children_.erase(child_name);
        // need to remove every connected ports
        auto port_names = child->get_port_names();
        for (auto const &port_name : port_names) {
            auto port = child->get_port(port_name);
            if (port->port_direction() == PortDirection::In) {
                // do a copy
                auto srcs = std::unordered_set<std::shared_ptr<AssignStmt>>(port->sources().begin(),
                                                                            port->sources().end());
                for (auto const &stmt : srcs) {
                    auto sink = stmt->right();
                    sink->unassign(stmt);
                    remove_stmt_from_parent(stmt);
                }
            } else {
                auto sinks = std::unordered_set<std::shared_ptr<AssignStmt>>(port->sinks().begin(),
                                                                             port->sinks().end());
                for (auto const &stmt : sinks) {
                    port->unassign(stmt);
                    remove_stmt_from_parent(stmt);
                }
            }
        }
    }
}

std::vector<std::shared_ptr<Generator>> Generator::get_child_generators() {
    std::vector<std::shared_ptr<Generator>> result;
    result.reserve(children_.size());
    for (auto const &n : child_names_) {
        result.emplace_back(children_.at(n));
    }
    return result;
}

bool Generator::has_child_generator(const std::shared_ptr<Generator> &child) {
    return children_.find(child->instance_name) != children_.end();
}

std::set<std::string> Generator::get_vars() {
    std::set<std::string> result;
    for (auto const &[name, ptr] : vars_) {
        if (ptr->type() == VarType::Base) {
            result.emplace(name);
        }
    }
    return result;
}

std::set<std::string> Generator::get_all_var_names() {
    std::set<std::string> result;
    for (auto const &[name, ptr] : vars_) result.emplace(name);
    return result;
}

void Generator::add_stmt(std::shared_ptr<Stmt> stmt) {
    stmt->set_parent(this);
    stmts_.emplace_back(std::move(stmt));
}

std::string Generator::get_unique_variable_name(const std::string &prefix,
                                                const std::string &var_name) {
    // NOTE: this is not thread-safe!
    uint32_t count = 0;
    std::string result_name;
    // maybe we're lucky and not need to prefix the count
    if (prefix.empty()) {
        result_name = var_name;
    } else {
        result_name = ::format("{0}_{1}", prefix, var_name);
    }
    if (!get_var(result_name)) return result_name;

    while (true) {
        if (prefix.empty()) {
            result_name = ::format("{0}_{1}", var_name, count);
        } else {
            result_name = ::format("{0}_{1}_{2}", prefix, var_name, count);
        }
        if (!get_var(result_name)) {
            break;
        } else {
            count++;
        }
    }
    return result_name;
}

void Generator::remove_port(const std::string &port_name) {
    if (has_port(port_name)) {
        ports_.erase(port_name);
        remove_var(port_name);
    }
}

void Generator::rename_var(const std::string &old_name, const std::string &new_name) {
    auto var = get_var(old_name);
    if (!var) return;
    // Using C++17 to replace the key
    vars_.extract(old_name).key() = new_name;
    // rename the var
    var->name = new_name;
}

std::shared_ptr<Param> Generator::get_param(const std::string &param_name) const {
    if (params_.find(param_name) == params_.end()) return nullptr;
    return params_.at(param_name);
}

void Generator::remove_stmt(const std::shared_ptr<Stmt> &stmt) {
    auto pos = std::find(stmts_.begin(), stmts_.end(), stmt);
    if (pos != stmts_.end()) {
        stmts_.erase(pos);
    }
}

std::shared_ptr<SequentialStmtBlock> Generator::sequential() {
    auto stmt = std::make_shared<SequentialStmtBlock>();
    add_stmt(stmt);
    return stmt;
}

std::shared_ptr<CombinationalStmtBlock> Generator::combinational() {
    auto stmt = std::make_shared<CombinationalStmtBlock>();
    add_stmt(stmt);
    return stmt;
}

void Generator::replace_child_generator(const std::shared_ptr<Generator> &target,
                                        const std::shared_ptr<Generator> &new_generator) {
    auto parent = target->parent();
    if (parent->ir_node_kind() != IRNodeKind::GeneratorKind)
        throw ::runtime_error(::format("{0} is a top level module and thus cannot be replaced",
                                       target->instance_name));
    auto parent_generator = reinterpret_cast<Generator *>(parent);
    if (parent_generator != this)
        throw ::runtime_error(::format("{0} is not in {1}", target->instance_name, instance_name));
    if (!has_child_generator(target))
        throw ::runtime_error(
            ::format("{0} doesn't belong to {1}", target->instance_name, instance_name));
    // checking for the same interface, for now
    auto target_port_names = target->get_port_names();
    auto new_port_names = target->get_port_names();
    if (target_port_names.size() != new_port_names.size())
        throw ::runtime_error(
            ::format("{0}'s number of ports don't match with {1}'s. Got {2}, need {3}",
                     new_generator->instance_name, target->instance_name, new_port_names.size(),
                     target_port_names.size()));
    // checking
    for (auto const &port_name : target_port_names) {
        auto target_port = target->get_port(port_name);
        auto new_port = new_generator->get_port(port_name);
        if (!new_port) {
            throw ::runtime_error(::format("Could not find {0} from {1}, which is required by {2}",
                                           port_name, new_generator->instance_name,
                                           target->instance_name));
        }
        if (target_port->width != new_port->width)
            throw ::runtime_error(
                ::format("{0}'s port ({1}) width doesn't match with {2}. Got {3}, need {4}",
                         new_generator->instance_name, port_name, target->instance_name,
                         new_port->width, target_port->width));
        if (target_port->is_signed != new_port->is_signed)
            throw ::runtime_error(
                ::format("{0}'s port ({1}) sign doesn't match with {2}. Got {3}, need {4}",
                         new_generator->instance_name, port_name, target->instance_name,
                         new_port->is_signed, target_port->is_signed));
        if (target_port->port_type() != new_port->port_type())
            throw ::runtime_error(
                ::format("{0}'s port ({1}) type doesn't match with {2}. Got {3}, need {4}",
                         new_generator->instance_name, port_name, target->instance_name,
                         port_type_to_str(new_port->port_type()),
                         port_type_to_str(target_port->port_type())));
        if (target_port->port_direction() != new_port->port_direction())
            throw ::runtime_error(
                ::format("{0}'s port ({1}) direction doesn't match with {2}. Got {3}, need {4}",
                         new_generator->instance_name, port_name, target->instance_name,
                         port_dir_to_str(new_port->port_direction()),
                         port_dir_to_str(target_port->port_direction())));
        // the actual replacement
        if (target_port->port_direction() == PortDirection::In) {
            Var::move_src_to(target_port.get(), new_port.get(), parent_generator, false);
        } else {
            Var::move_sink_to(target_port.get(), new_port.get(), parent_generator, false);
        }
    }

    if (!parent_generator->has_child_generator(new_generator))
        parent_generator->add_child_generator(new_generator->instance_name, new_generator);
    parent_generator->remove_child_generator(target);
}

void inline check_direction(const std::shared_ptr<Port> &port1, const std::shared_ptr<Port> &port2,
                            bool same_direction = false) {
    auto port1_dir = port1->port_direction();
    PortDirection correct_dir;
    if (same_direction)
        correct_dir = port1_dir;
    else if (port1_dir == PortDirection::In)
        correct_dir = PortDirection ::Out;
    else
        correct_dir = PortDirection ::In;
    if (port2->port_direction() != correct_dir) {
        throw ::runtime_error(::format("Port {0} and port {1} doesn't match port direction",
                                       port1->to_string(), port2->to_string()));
    }
}

std::shared_ptr<Stmt> Generator::wire_ports(std::shared_ptr<Port> &port1,
                                            std::shared_ptr<Port> &port2) {
    auto parent1 = port1->generator;
    auto parent2 = port2->generator;
    std::shared_ptr<Stmt> stmt;
    if (parent1 == parent2 && parent1 == this) {
        // it's the same module
        check_direction(port1, port2);
        if (port1->port_direction() == PortDirection::In) {
            stmt = port2->assign(port1);
        } else {
            stmt = port1->assign(port2);
        }
    } else {
        if (parent1 == this && has_child_generator(parent2->shared_from_this())) {
            check_direction(port1, port2, true);
            if (port1->port_direction() == PortDirection::In)
                stmt = port2->assign(port1);
            else
                stmt = port1->assign(port2);
        } else if (parent2 == this && has_child_generator(parent1->shared_from_this())) {
            check_direction(port1, port2, true);
            if (port1->port_direction() == PortDirection::In)
                stmt = port1->assign(port2);
            else
                stmt = port2->assign(port1);
        } else {
            throw ::runtime_error(
                ::format("Cannot wire {0} and {1}. Please make sure they belong to the same module "
                         "or parent",
                         port1->to_string(), port2->to_string()));
        }
    }

    add_stmt(stmt);
    return stmt;
}

std::shared_ptr<Generator> Generator::clone() {
    auto generator = std::make_shared<Generator>(context_, name);
    auto port_names = get_port_names();
    for (auto const &port_name : port_names) {
        auto port = get_port(port_name);
        generator->port(port->port_direction(), port_name, port->width, port->size,
                        port->port_type(), port->is_signed);
    }
    // also parameters
    for (auto const &[param_name, param] : params_) {
        generator->parameter(param_name, param->width, param->is_signed);
    }
    if (!fn_name_ln.empty()) {
        generator->fn_name_ln.insert(generator->fn_name_ln.end(), fn_name_ln.begin(),
                                     fn_name_ln.end());
    }
    // we won't bother checking stuff
    generator->set_external(true);
    generator->is_cloned_ = true;
    return generator;
}

void Generator::accept(IRVisitor *visitor) {
    if (!external()) visitor->visit(this);
}

PortPacked &Generator::port_packed(PortDirection direction, const std::string &port_name,
                                   const PackedStruct &packed_struct_) {
    if (ports_.find(port_name) != ports_.end())
        throw ::runtime_error(::format("{0} already exists in {1}", port_name, name));
    auto p = std::make_shared<PortPacked>(this, direction, port_name, packed_struct_);
    vars_.emplace(port_name, p);
    ports_.emplace(port_name);
    return *p;
}

VarPacked& Generator::var_packed(const std::string &var_name,
                                 const kratos::PackedStruct &packed_struct_) {
    if (vars_.find(var_name) != vars_.end())
        throw ::runtime_error(::format("{0} already exists in {1}", var_name, name));
    auto v = std::make_shared<VarPacked>(this, var_name, packed_struct_);
    vars_.emplace(var_name, v);
    return *v;
}

void Generator::replace(const std::string &child_name,
                        const std::shared_ptr<Generator> &new_child) {
    // obtained the generator
    if (children_.find(child_name) == children_.end()) {
        throw ::runtime_error(::format("Unable to find {0} from {1}", child_name, instance_name));
    }
    auto old_child = children_.at(child_name);
    new_child->instance_name = child_name;
    // first we need to make sure that the interfaces are the same
    auto old_port_names = old_child->get_port_names();
    auto new_port_names = new_child->get_port_names();
    if (old_port_names.size() != new_port_names.size()) {
        // doesn't match
        // show all the port definitions
        std::vector<const Var *> ports;
        ports.reserve(old_port_names.size() + new_port_names.size());
        for (auto const &port_name : old_port_names) {
            ports.emplace_back(old_child->get_port(port_name).get());
        }
        for (auto const &port_name : new_port_names) {
            ports.emplace_back(new_child->get_port(port_name).get());
        }
        throw VarException(::format("{0}'s port interface doesn't match with {1}", old_child->name,
                                    new_child->name),
                           ports);
    }
    // check the name, type, and size
    for (const auto &port_name : old_port_names) {
        if (new_port_names.find(port_name) == new_port_names.end()) {
            // doesn't have the port
            throw VarException(::format("{0} doesn't have port {1}", new_child->name, port_name),
                               {old_child->get_port(port_name).get()});
        }
        auto old_port = old_child->get_port(port_name);
        auto new_port = new_child->get_port(port_name);
        // type checking
        if (old_port->size != new_port->size || old_port->width != new_port->width) {
            throw VarException(::format("{0}'s port {1} has different width than {2}'s",
                                        old_child->name, port_name, new_child->name),
                               {old_port.get(), new_port.get()});
        }
        if (old_port->is_signed != new_port->is_signed) {
            throw VarException(::format("{0}'s port {1} has different sign than {2}'s",
                                        old_child->name, port_name, new_child->name),
                               {old_port.get(), new_port.get()});
        }
        if (old_port->port_type() != new_port->port_type()) {
            throw VarException(::format("{0}'s port {1} has different port type than {2}'s",
                                        old_child->name, port_name, new_child->name),
                               {old_port.get(), new_port.get()});
        }
        if (old_port->port_direction() != new_port->port_direction()) {
            throw VarException(::format("{0}'s port {1} has different port direction than {2}'s",
                                        old_child->name, port_name, new_child->name),
                               {old_port.get(), new_port.get()});
        }

        // all passed, now replace the port!
        if (old_port->port_direction() == PortDirection::In) {
            // move the src
            Var::move_src_to(old_port.get(), new_port.get(), this, false);
        } else if (old_port->port_direction() == PortDirection::Out) {
            // move the sinks
            Var::move_sink_to(old_port.get(), new_port.get(), this, false);
        } else {
            // inout, move both source and sinks
            Var::move_src_to(old_port.get(), new_port.get(), this, false);
            Var::move_sink_to(old_port.get(), new_port.get(), this, false);
        }
    }

    // update other meta data info
    children_[child_name] = new_child;
    children_debug_.erase(child_name);
}

void Generator::replace(const std::string &child_name, const std::shared_ptr<Generator> &new_child,
                        const std::pair<std::string, uint32_t> &debug_info) {
    replace(child_name, new_child);
    children_debug_.emplace(child_name, debug_info);
}

std::vector<std::string> Generator::get_ports(kratos::PortType type) const {
    std::vector<std::string> result;
    auto port_names = get_port_names();
    for (auto const &port_name : port_names) {
        auto port = get_port(port_name);
        if (port->port_type() == type) result.emplace_back(port_name);
    }
    return result;
}

std::shared_ptr<PortBundleRef> Generator::add_bundle_port_def(const std::string &port_name,
                                    const std::shared_ptr<PortBundleDefinition> &def) {
    if (port_bundle_mapping_.find(port_name) != port_bundle_mapping_.end())
        throw ::runtime_error(::format("{0} already exists in {1}", port_name, name));
    auto definition = def->definition();
    auto ref = std::make_shared<PortBundleRef>(this, def);
    auto const &debug_info = def->debug_info();
    for (auto const &[name, bundle] : definition) {
        auto const &[width, size, is_signed, direction, port_type] = bundle;
        auto var_name = get_unique_variable_name(port_name, name);
        auto &p = port(direction, var_name, width, size, port_type, is_signed);
        // add to the ref mapping as well
        ref->add_name_mapping(name, var_name);
        if (debug && debug_info.find(name) != debug_info.end()) {
            p.fn_name_ln.emplace_back(debug_info.at(name));
        }
    }
    // add to the bundle mapping
    port_bundle_mapping_.emplace(port_name, ref);

    return ref;
}

std::shared_ptr<PortBundleRef> Generator::add_bundle_port_def(
    const std::string &port_name, const std::shared_ptr<PortBundleDefinition> &def,
    const std::pair<std::string, uint32_t> &debug_info) {
    auto ref = add_bundle_port_def(port_name, def);
    auto definition = def->definition();
    for (auto const &iter: definition) {
        auto base_name = iter.first;
        auto &port = ref->get_port(base_name);
        port.fn_name_ln.emplace_back(debug_info);
    }
    return ref;
}

std::shared_ptr<PortBundleRef> Generator::get_bundle_ref(const std::string &port_name) {
    if (!has_port_bundle(port_name)) {
        throw ::runtime_error(port_name + " not found in " + name);
    }
    return port_bundle_mapping_.at(port_name);
}

void Generator::remove_var(const std::string &var_name) {
    if (vars_.find(var_name) == vars_.end()) {
        throw ::runtime_error(::format("Cannot find {0} from {1}", var_name, name));
    }
    auto var = vars_.at(var_name);
    if (!var->sources().empty()) {
        throw ::runtime_error(::format("{0} still has source connection(s)"));
    }
    if (!var->sinks().empty()) {
        throw ::runtime_error(::format("{0} still has sink connection(s)"));
    }

    vars_.erase(var_name);
}

}