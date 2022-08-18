#include "debug.hh"

#include <mutex>

#include "except.hh"
#include "fmt/format.h"
#include "generator.hh"
#include "graph.hh"
#include "json.hh"
#include "pass.hh"
#include "tb.hh"
#include "util.hh"

using fmt::format;

namespace kratos {

class DebugBreakInjectVisitor : public IRVisitor {
public:
    explicit DebugBreakInjectVisitor(Context *context) : context_(context) {}

    void visit(CombinationalStmtBlock *stmt) override { insert_statements(stmt); }

    void visit(SequentialStmtBlock *stmt) override { insert_statements(stmt); }

    void visit(InitialStmtBlock *stmt) override { insert_statements(stmt); }

    void visit(ScopedStmtBlock *stmt) override { insert_statements(stmt); }

    void visit(AssignStmt *stmt) override {
        auto const *parent = stmt->parent();
        if (parent->ir_node_kind() == IRNodeKind::GeneratorKind) {
            auto const *p = reinterpret_cast<const Generator *>(parent);
            if (p->debug) {
                process_stmt(stmt);
            }
        }
    }

private:
    void insert_statements(StmtBlock *block) {
        auto *parent = block->generator_parent();
        if (!parent->debug)
            // we only insert statements to the ones that has debug turned on
            return;

        for (auto const &stmt : *block) {
            process_stmt(stmt.get());
        }
    }

    void process_stmt(Stmt *stmt) {
        uint32_t stmt_id = context_->max_stmt_id()++;
        // set stmt id
        stmt->set_stmt_id(stmt_id);
    }

    Context *context_;
};

void inject_debug_break_points(Generator *top) {
    DebugBreakInjectVisitor visitor(top->context());
    visitor.visit_root(top);
}

class InstanceIdVisitor : public IRVisitor {
public:
    explicit InstanceIdVisitor(Context *context) : context_(context) {}

    void visit(Generator *gen) override {
        if (gen->generator_id < 0) {
            mutex_.lock();
            auto id = context_->max_instance_id()++;
            mutex_.unlock();
            gen->generator_id = id;
        }
    }

private:
    Context *context_;
    std::mutex mutex_;
};

void inject_instance_ids(Generator *top) {
    // this can be done in parallel
    InstanceIdVisitor visitor(top->context());
    visitor.visit_generator_root_p(top);
}

class ExtractDebugVisitor : public IRVisitor {
public:
    void visit(AssignStmt *stmt) override { extract_stmt_id(stmt); }
    void visit(ScopedStmtBlock *stmt) override { extract_stmt_id(stmt); }
    void visit(IfStmt *stmt) override { extract_stmt_id(stmt); }
    void visit(SwitchStmt *stmt) override { extract_stmt_id(stmt); }
    void visit(FunctionCallStmt *stmt) override { extract_stmt_id(stmt); }
    void visit(ReturnStmt *stmt) override { extract_stmt_id(stmt); }
    void visit(AssertBase *stmt) override { extract_stmt_id(stmt); }
    void visit(AuxiliaryStmt *stmt) override { extract_stmt_id(stmt); }

    const std::map<Stmt *, uint32_t> &map() const { return map_; }

private:
    void extract_stmt_id(Stmt *stmt) {
        int id = stmt->stmt_id();
        if (id >= 0) {
            map_.emplace(stmt, id);
        }
    }

    std::map<Stmt *, uint32_t> map_;
};

std::map<Stmt *, uint32_t> extract_debug_break_points(Generator *top) {
    ExtractDebugVisitor visitor;
    visitor.visit_root(top);
    return visitor.map();
}

class InsertVerilatorPublic : public IRVisitor {
public:
    void visit(Generator *generator) override {
        auto vars = generator->get_all_var_names();
        for (auto const &var_name : vars) {
            auto var = generator->get_var(var_name);
            insert_str(var.get());
        }
    }

private:
    void static insert_str(Var *var) { var->set_after_var_str_(" /*verilator public*/"); }
};

void insert_verilator_public(Generator *top) {
    InsertVerilatorPublic visitor;
    visitor.visit_generator_root_p(top);
}

class VarSourceVisitor : public IRVisitor {
public:
    void visit(Var *var) override {
        if (map_.find(var) != map_.end()) return;
        auto const &sources = var->sources();
        for (auto const &stmt : sources) {
            auto *right = stmt->right();
            get_source_var(right, map_[var]);
        }
    }

    const std::unordered_map<Var *, std::unordered_set<Var *>> &map() const { return map_; }

private:
    std::unordered_map<Var *, std::unordered_set<Var *>> map_;

    class VarComponentVisitor : public IRVisitor {
    public:
        std::unordered_set<Var *> &vars() { return vars_; };
        void visit(Var *var) override {
            if (var->type() == VarType::Base) {
                vars_.emplace(var);
            }
        }

    private:
        std::unordered_set<Var *> vars_;
    };

    void static get_source_var(const Var *var, std::unordered_set<Var *> &set) {
        if (var->type() == VarType::ConstValue || var->type() == VarType::Parameter) return;
        VarComponentVisitor visitor;
        visitor.visit_root(const_cast<Var *>(var));
        set.merge(visitor.vars());
    }
};

std::unordered_map<Var *, std::unordered_set<Var *>> find_driver_signal(Generator *top) {
    VarSourceVisitor visitor;
    visitor.visit_root(top);
    return visitor.map();
}

class PropagateScopeVisitor : public IRVisitor {
public:
    void visit(IfStmt *stmt) override {
        auto variables = stmt->scope_context();
        for (auto const &[name, var] : variables) {
            stmt->then_body()->add_scope_variable(name, var.second, var.first, false);
            stmt->else_body()->add_scope_variable(name, var.second, var.first, false);
        }
    }

    void visit(SwitchStmt *stmt) override {
        auto variables = stmt->scope_context();
        for (auto const &[name, var] : variables) {
            auto cases = stmt->body();
            for (auto &iter : cases) {
                auto case_ = iter.second;
                case_->add_scope_variable(name, var.second, var.first, false);
            }
        }
    }
};

void propagate_scope_variable(Generator *top) {
    PropagateScopeVisitor visitor;
    visitor.visit_root(top);
}

void mock_hierarchy(Generator *top, const std::string &top_name) {
    // can only perform on the top layer
    auto instance_name = top->instance_name;
    if (instance_name.find('.') == std::string::npos) {
        return;
    }
    // need to tokenize based on the instance names
    auto names = string::get_tokens(instance_name, ".");
    if (names.size() < 2) throw InternalException("Cannot tokenize string " + instance_name);
    Context *context = top->context();
    top->instance_name = names.back();
    int start_index = static_cast<int>(names.size() - 2);
    Generator *pre = top;
    for (int i = start_index; i >= 0; i--) {
        // create a new generator
        std::string name = names[i];
        if (i == 0 && !top_name.empty()) name = top_name;
        Generator *gen;
        if (context->generator_name_exists(name)) {
            gen = (*(context->get_generators_by_name(name).begin())).get();
        } else {
            gen = &context->generator(name);
        }
        gen->add_child_generator(pre->instance_name, pre->shared_from_this());
        pre = gen;
    }
}

void DebugDatabase::compute_generators(Generator *top) {
    top_ = top;
    GeneratorGraph g(top);
    auto generators = g.get_sorted_nodes();
    for (auto *gen : generators) {
        generators_.emplace(gen);
    }
}

void DebugDatabase::set_break_points(Generator *top) { set_break_points(top, ".py"); }

void DebugDatabase::set_break_points(Generator *top, const std::string &ext) {
    // set the break points
    break_points_ = extract_debug_break_points(top);

    // index all the front-end code
    // we are only interested in the files that has the extension
    for (auto const &[stmt, id] : break_points_) {
        auto fn_ln = stmt->fn_name_ln;
        for (auto const &[fn, ln] : fn_ln) {
            auto fn_ext = fs::get_ext(fn);
            if (fn_ext == ext) {
                // this is the one we need
                stmt_mapping_.emplace(stmt, std::make_pair(fn, ln));
                break;
            }
        }
    }
    // set generators
    compute_generators(top);
}

void DebugDatabase::set_variable_mapping(
    const std::map<Generator *, std::map<std::string, Var *>> &mapping) {
    for (auto const &[gen, map] : mapping) {
        for (auto const &[front_var_name, var] : map) {
            variable_mapping_[gen].emplace(front_var_name, var->to_string());
        }
    }
}

void DebugDatabase::set_variable_mapping(
    const std::map<Generator *, std::map<std::string, std::string>> &mapping) {
    for (auto const &[gen, map] : mapping) {
        for (auto const &[front_var_name, var_name] : map) {
            variable_mapping_[gen].emplace(front_var_name, var_name);
        }
    }
}

std::optional<std::pair<std::string, std::string>> get_target_var_name(const Var *var) {
    auto const &attrs = var->get_attributes();
    for (auto const &attr : attrs) {
        auto const &value_str = attr->value_str;
        if (value_str.rfind("ssa=") == 0) {
            auto pos = value_str.rfind(':');
            auto scope_name = value_str.substr(4, pos - 4);
            auto var_name = value_str.substr(pos + 1);
            return std::make_pair(scope_name, var_name);
        }
    }
    return std::nullopt;
}

using VarCondition = std::pair<hgdb::json::Variable, std::string>;

std::vector<VarCondition> create_variables(const Var *var, const std::string &name) {
    std::vector<VarCondition> result;
    const static std::string empty;
    if (var->size().size() > 1 || var->size().front() > 1) {
        // it's an array. need to flatten it
        auto slices = get_flatten_slices(var);
        for (auto const &slice : slices) {
            std::string new_name = name;
            hgdb::json::Variable v;
            for (auto const &s : slice) new_name = ::format("{0}.{1}", new_name, s);
            std::string value = var->to_string();
            for (auto const &s : slice) value = ::format("{0}[{1}]", value, s);
            v.value = value;
            v.name = new_name;
            v.rtl = true;
            result.emplace_back(std::make_pair(v, empty));
        }
    } else if (var->is_struct()) {
        // it's a packed array
        if (var->type() == VarType::PortIO) {
            auto const *p = reinterpret_cast<const PortPackedStruct *>(var);
            auto const &def = p->packed_struct();
            for (auto const &iter : def->attributes) {
                auto const &attr_name = iter.name;
                // we need to store lots of them
                std::string new_name = ::format("{0}.{1}", name, attr_name);
                hgdb::json::Variable v;
                v.value = ::format("{0}.{1}", var->to_string(), attr_name);
                v.name = new_name;
                v.rtl = true;
                result.emplace_back(std::make_pair(v, empty));
            }
        } else if (var->type() == VarType::Base) {
            auto const *p = reinterpret_cast<const VarPackedStruct *>(var);
            auto const &def = p->packed_struct();
            for (auto const &iter : def->attributes) {
                auto const &attr_name = iter.name;
                // we need to store lots of them
                std::string new_name = ::format("{0}.{1}", name, attr_name);
                hgdb::json::Variable v;
                v.value = ::format("{0}.{1}", var->to_string(), attr_name);
                v.name = new_name;
                v.rtl = true;
                result.emplace_back(std::make_pair(v, empty));
            }
        }
    } else if (var->type() == VarType::Slice &&
               reinterpret_cast<const VarSlice *>(var)->sliced_by_var()) {
        auto const *var_var_slice = reinterpret_cast<const VarVarSlice *>(var);
        // for now, we flatten out the access and only one-level of slicing
        auto const &size = var_var_slice->parent_var->size().front();
        auto select_name = var_var_slice->sliced_var()->to_string();
        auto base_name = var_var_slice->parent_var->to_string();
        // need to get the actual name. notice that we might get to_string() name,
        // in this case it might be wrong
        auto names = string::get_tokens(name, "[].");
        auto const &new_name = names[0];
        for (auto i = 0u; i < size; i++) {
            auto transformed_name = fmt::format("{0}[{1}]", base_name, i);
            auto new_name_transformed = fmt::format("{0}.{1}", new_name, i);
            auto cond = fmt::format("{0} == {1}", select_name, i);
            // the usage is setting var[10] as a watch point
            hgdb::json::Variable v;
            v.name = new_name_transformed;
            v.value = transformed_name;
            v.rtl = true;
            result.emplace_back(std::make_pair(v, cond));
        }
    } else {
        // the normal one
        hgdb::json::Variable v;
        v.value = var->to_string();
        v.name = name;
        v.rtl = true;
        result.emplace_back(std::make_pair(v, empty));
    }
    return result;
}

void add_generator_static_value(hgdb::json::Module &m, const std::string &name,
                                const std::string &value) {
    hgdb::json::Variable v{.name = name, .value = value, .rtl = false, .id = std::nullopt};
    m.add_variable(v);
}

class StmtFileNameVisitor : public IRVisitor {
public:
    explicit StmtFileNameVisitor(
        const std::map<Stmt *, std::pair<std::string, uint32_t>> &stmt_fn_ln)
        : stmt_fn_ln_(stmt_fn_ln) {}
    void visit(AssignStmt *stmt) override {
        if (stmt_fn_ln_.find(stmt) != stmt_fn_ln_.end()) {
            std::tie(filename, ln) = stmt_fn_ln_.at(stmt);
        }
    }

    std::string filename;
    uint32_t ln = 0;

private:
    const std::map<Stmt *, std::pair<std::string, uint32_t>> &stmt_fn_ln_;
};

class StmtScopeVisitor : public IRVisitor {
public:
    StmtScopeVisitor(hgdb::json::Module &module, const Generator *gen,
                     const std::map<Stmt *, std::pair<std::string, uint32_t>> &stmt_fn_ln,
                     const std::unordered_map<Stmt *, std::string> &enable_conditions)
        : module_(module),
          gen_(gen),
          stmt_fn_ln_(stmt_fn_ln),
          enable_conditions_(enable_conditions) {}
    void visit(AssignStmt *stmt) override { handle_stmt(stmt); }
    void visit(ScopedStmtBlock *stmt) override { handle_stmt(stmt); }
    void visit(IfStmt *stmt) override { handle_stmt(stmt); }
    void visit(SwitchStmt *stmt) override { handle_stmt(stmt); }
    void visit(FunctionCallStmt *stmt) override { handle_stmt(stmt); }
    void visit(ReturnStmt *stmt) override { handle_stmt(stmt); }
    void visit(AssertBase *stmt) override { handle_stmt(stmt); }
    void visit(AuxiliaryStmt *stmt) override { handle_stmt(stmt); }
    void visit(CombinationalStmtBlock *stmt) override { handle_stmt(stmt); }
    void visit(SequentialStmtBlock *stmt) override { handle_stmt(stmt); }
    void visit(LatchStmtBlock *stmt) override { handle_stmt(stmt); }

private:
    void handle_stmt(Stmt *stmt) {
        std::string filename;
        uint32_t ln = 0;

        if (stmt->has_attribute("debug-ignore")) return;

        if (stmt_fn_ln_.find(stmt) != stmt_fn_ln_.end()) {
            std::tie(filename, ln) = stmt_fn_ln_.at(stmt);
        }

        using namespace hgdb::json;
        auto *parent = stmt->parent();
        hgdb::json::Scope<> *parent_scope;
        if (parent->ir_node_kind() == IRNodeKind::GeneratorKind) {
            // this is top level
            auto *scope = module_.create_scope<Scope<>>();
            if (filename.empty()) {
                StmtFileNameVisitor v(stmt_fn_ln_);
                v.visit_root(stmt);
                filename = v.filename;
                ln = v.ln;
            }
            scope->filename = filename;
            parent_scope = scope;
            stmt_scope_mapping_.emplace(stmt, scope);

            if (stmt->type() != StatementType::Assign) {
                // only top level assign, i.e. continuous assignment can
                // have useful scope
                return;
            }

        } else {
            auto *parent_stmt = reinterpret_cast<Stmt *>(parent);
            if (stmt_scope_mapping_.find(parent_stmt) == stmt_scope_mapping_.end()) {
                throw InternalException("Scope not properly created");
            }
            parent_scope = stmt_scope_mapping_.at(parent_stmt);
        }

        // store all the context variables
        // TODO: use stack address as a way to determine the actual scope
        //  for now we flatten everything
        for (auto const &[name, value_pair] : stmt->scope_context()) {
            auto const &[rtl, value] = value_pair;
            // we don't put line number down for static variables
            // since we can't obtain them from Python
            auto *var_stmt = add_variable<true>(parent_scope, name, value, rtl);
            if (var_stmt && enable_conditions_.find(stmt) != enable_conditions_.end()) {
                var_stmt->condition = enable_conditions_.at(stmt);
            }
        }
        // add itself
        auto *stmt_scope = add_stmt(parent_scope, stmt, filename, ln);
        if (stmt_scope) {
            stmt_scope_mapping_.emplace(stmt, stmt_scope);
        }
    }

    template <bool is_assign>
    hgdb::json::VarStmt *add_variable(hgdb::json::Scope<> *scope, const std::string &name,
                                      const std::string &value, bool rtl) {
        using namespace hgdb::json;
        // depends on whether we have already declared it or not
        Variable v{.name = name, .value = value, .rtl = rtl, .id = std::nullopt};
        // if this is a generator variable, and we happen to know where it's declared, we're good
        uint64_t ln = 0;
        if (rtl) {
            auto const &vars = gen_->vars();
            if (vars.find(value) != vars.end()) {
                auto const &var = vars.at(value);
                if (!var->fn_name_ln.empty()) {
                    auto [_, ln_] = var->fn_name_ln[0];
                    ln = ln_;
                }
            }
        }

        auto stmt = VarStmt(v, ln, is_assign);
        if (SymbolTable::has_same_var(scope, stmt)) {
            // we don't add it since it has already been declared
            return nullptr;
        }

        return scope->template create_scope<VarStmt>(v, ln, is_assign);
    }

    hgdb::json::Scope<> *add_stmt(hgdb::json::Scope<> *scope, Stmt *stmt,
                                  const std::string &filename, uint32_t ln) {
        hgdb::json::Scope<> *res = nullptr;
        if (stmt->type() == StatementType::Assign) {
            auto *assign = reinterpret_cast<AssignStmt *>(stmt);
            auto const *left = assign->left();
            auto front_name = get_front_name(left);
            auto const &vars = create_variables(left, front_name);
            for (auto const &[v, cond] : vars) {
                auto *s = scope->create_scope<hgdb::json::VarStmt>(v, ln, false);
                s->filename = filename;
                s->condition = cond;
                if (enable_conditions_.find(stmt) != enable_conditions_.end()) {
                    auto const &stmt_cond = enable_conditions_.at(stmt);
                    if (s->condition.empty()) {
                        s->condition = stmt_cond;
                    } else if (!stmt_cond.empty()) {
                        s->condition = fmt::format("({0}) && ({1})", s->condition, stmt_cond);
                    }
                }
            }
        } else {
            res = scope->create_scope<hgdb::json::Scope<>>();
            if (ln > 0) res->line_num = ln;
            res->filename = filename;

            if (enable_conditions_.find(stmt) != enable_conditions_.end()) {
                res->condition = enable_conditions_.at(stmt);
            }
        }

        return res;
    }

    static std::string get_front_name(const Var *var) {
        auto mapping = get_target_var_name(var);
        if (mapping) {
            return mapping->first;
        }
        return var->to_string();
    }

    hgdb::json::Module &module_;
    const Generator *gen_;
    std::unordered_map<const Stmt *, hgdb::json::Scope<> *> stmt_scope_mapping_;
    const std::map<Stmt *, std::pair<std::string, uint32_t>> &stmt_fn_ln_;
    const std::unordered_map<Stmt *, std::string> &enable_conditions_;
};

void DebugDatabase::save_database(const std::string &filename, bool override) {
    if (override) {
        if (fs::exists(filename)) {
            fs::remove(filename);
        }
    }

    // compute breakpoint conditions
    auto breakpoint_conditions = compute_enable_condition(top_);
    auto table = hgdb::json::SymbolTable("kratos");

    std::unordered_map<Generator *, hgdb::json::Module *> gen_mod_map;

    // first pass to create modules
    for (auto *gen : generators_) {
        auto *mod = table.add_module(gen->name);
        gen_mod_map.emplace(gen, mod);
    }
    // second pass to add instances
    for (auto *gen : generators_) {
        auto *mod = gen_mod_map.at(gen);
        auto children = gen->get_child_generators();
        for (auto const &child : children) {
            if (gen_mod_map.find(child.get()) == gen_mod_map.end()) continue;
            auto *child_mod = gen_mod_map.at(child.get());
            mod->add_instance(child->instance_name, child_mod);
        }
    }

    // now add generator variables
    for (auto *gen : generators_) {
        if (variable_mapping_.find(gen) == variable_mapping_.end()) continue;
        auto *mod = gen_mod_map.at(gen);
        auto const &var_names = variable_mapping_.at(gen);
        for (auto const &[front_name, back_name] : var_names) {
            auto var = gen->get_var(back_name);
            if (var && (var->type() == VarType::Base || var->type() == VarType::PortIO)) {
                auto vars = create_variables(var.get(), front_name);
                for (auto const &v : vars) {
                    mod->add_variable(v.first);
                }
            } else if (!var) {
                add_generator_static_value(*mod, front_name, back_name);
            }
        }
    }

    // now deal with scopes
    std::unordered_set<Generator *> visited_gens;
    for (auto &[stmt, id] : break_points_) {
        auto *gen = stmt->generator_parent();
        if (!gen || visited_gens.find(gen) != visited_gens.end()) continue;
        if (gen_mod_map.find(gen) == gen_mod_map.end()) continue;
        visited_gens.emplace(gen);
        auto *mod = gen_mod_map.at(gen);
        StmtScopeVisitor v(*mod, gen, stmt_mapping_, breakpoint_conditions);
        v.visit_content(gen);
    }

    // compress the table
    table.compress();

    // setting attributes
    table.disable_reorder();

    std::ofstream stream;
    stream.open(filename);
    stream << table.output();
    stream.close();
}

// TODO: implement transformer visitor
class AssertionRemoval : public IRVisitor {
public:
    void visit(Generator *gen) override {
        auto stmt_count = gen->stmts_count();
        std::vector<std::shared_ptr<Stmt>> stmts_to_remove;
        for (uint64_t i = 0; i < stmt_count; i++) {
            auto stmt = gen->get_stmt(i);
            if (stmt->type() == StatementType::Assert) stmts_to_remove.emplace_back(stmt);
        }
        for (auto const &stmt : stmts_to_remove) {
            gen->remove_stmt(stmt);
        }
    }

    void visit(ScopedStmtBlock *block) override { process_block(block); }
    void visit(SequentialStmtBlock *block) override { process_block(block); }
    void visit(CombinationalStmtBlock *block) override { process_block(block); }

    static void process_block(StmtBlock *block) {
        auto stmt_count = block->child_count();
        std::vector<std::shared_ptr<Stmt>> stmts_to_remove;
        for (uint64_t i = 0; i < stmt_count; i++) {
            auto *stmt = reinterpret_cast<Stmt *>(block->get_child(i));
            if (stmt->type() == StatementType::Assert)
                stmts_to_remove.emplace_back(stmt->shared_from_this());
        }
        for (auto const &stmt : stmts_to_remove) {
            block->remove_stmt(stmt);
        }
    }
};

void remove_assertion(Generator *top) {
    AssertionRemoval visitor;
    visitor.visit_root(top);
    // then remove empty block
    remove_empty_block(top);
}

class TriggerConditionVisitor : public IRVisitor {
public:
    void visit(Var *var) override {
        auto base_name = var->get_var_root_parent()->base_name();
        values.emplace(base_name);
    }

    std::unordered_set<std::string> values;
};

std::string get_trigger_attribute(const std::shared_ptr<StmtBlock> &blk) {
    TriggerConditionVisitor visitor;
    visitor.visit_root(blk.get());
    auto const &values = visitor.values;
    if (values.empty()) return "";
    return string::join(values.begin(), values.end(), " ");
}

class SSATransformFixVisitor : public IRVisitor {
public:
    void visit(Generator *gen) override {
        auto stmts = gen->get_all_stmts();
        for (auto const &stmt : stmts) {
            if (stmt->type() == StatementType::Block && stmt->has_attribute("ssa")) {
                auto blk_stmt = stmt->as<StmtBlock>();
                if (blk_stmt->block_type() == StatementBlockType::Combinational) {
                    process_always_comb(blk_stmt);
                }
            }
        }
    }

private:
    static void process_always_comb(const std::shared_ptr<StmtBlock> &blk) {
        // also need to fix the scope variables
        // we assume that every statement here has been SSA transformed
        using SymbolMapping = std::unordered_map<std::string, std::string>;
        uint64_t current_scope = 1;
        std::unordered_map<uint64_t, SymbolMapping> symbol_mappings = {{current_scope, {}}};
        std::unordered_set<Stmt *> stmts;
        auto trigger_str = get_trigger_attribute(blk);
        for (auto const &stmt : *blk) {
            if (stmt->type() != StatementType::Assign)
                throw StmtException("Invalid SSA transform", {stmt.get()});
            auto assign_stmt = stmt->as<AssignStmt>();
            auto *left = assign_stmt->left();
            auto scope_id = get_target_scope(left);
            if (scope_id) {
                // detect when to start a new scope
                if (current_scope != *scope_id) {
                    // copy current scope to the new one
                    auto const &current_mapping = symbol_mappings.at(current_scope);
                    symbol_mappings[*scope_id] = {};
                    for (auto const &iter : current_mapping) {
                        symbol_mappings[*scope_id].emplace(iter);
                    }
                }
                current_scope = *scope_id;
            }
            auto &symbol_mapping = symbol_mappings.at(current_scope);
            // every statement is assign, and every variable should have been SSA transformed
            auto parse_result = get_target_var_name(left);
            if (!parse_result) throw StmtException("Invalid SSA transform", {stmt.get()});
            auto const &[target_scope_name, target_var_name] = *parse_result;
            // look into its scope variables
            auto const &scope = stmt->scope_context();
            std::map<std::string, std::pair<bool, std::string>> new_scope;
            for (auto const &[name, var_map] : scope) {
                auto const &[is_var, var_name] = var_map;
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

    static std::optional<uint64_t> get_target_scope(const Var *var) {
        auto const &attrs = var->get_attributes();
        for (auto const &attr : attrs) {
            auto const &value_str = attr->value_str;
            auto pos = value_str.rfind("ssa-scope=");
            if (pos == 0) {
                auto v = value_str.substr(10);
                return std::stoul(v);
            }
        }
        return std::nullopt;
    }
};

void ssa_transform_fix(Generator *top) {
    SSATransformFixVisitor visitor;
    visitor.visit_root(top);
}

// this is only for visiting the vars and assignments in the current generator
class DebugInfoVisitor : public IRVisitor {
public:
    void visit(Var *var) override { add_info(var); }
    void visit(Expr *expr) override { add_info(expr); }
    void visit(EnumVar *var) override { add_info(var); }
    void visit(EnumConst *var) override { add_info(var); }

    void inline visit(AssignStmt *stmt) override { add_info(stmt); }

    void visit(Port *var) override { add_info(var); }

    void visit(SwitchStmt *stmt) override { add_info(stmt); }

    void inline visit(SequentialStmtBlock *stmt) override { add_info(stmt); }

    void inline visit(CombinationalStmtBlock *stmt) override { add_info(stmt); }

    void inline visit(ModuleInstantiationStmt *stmt) override { add_info(stmt); }

    void inline visit(IfStmt *stmt) override { add_info(stmt); }

    void inline visit(FunctionCallStmt *stmt) override { add_info(stmt); }

    void inline visit(FunctionStmtBlock *stmt) override { add_info(stmt); }

    void inline visit(ReturnStmt *stmt) override { add_info(stmt); }

    std::map<uint32_t, std::vector<std::pair<std::string, uint32_t>>> &result() { return result_; }

private:
    void inline add_info(Stmt *stmt) {
        if (!stmt->fn_name_ln.empty() && stmt->verilog_ln != 0) {
            result_.emplace(stmt->verilog_ln, stmt->fn_name_ln);
        }
    }

    void inline add_info(Var *var) {
        if (!var->fn_name_ln.empty() && var->verilog_ln != 0 &&
            result_.find(var->verilog_ln) == result_.end()) {
            result_.emplace(var->verilog_ln, var->fn_name_ln);
        }
    }

    std::map<uint32_t, std::vector<std::pair<std::string, uint32_t>>> result_;
};

class GeneratorDebugVisitor : public IRVisitor {
public:
    void visit(Generator *generator) override {
        if (result_.find(generator->name) != result_.end()) return;
        if (!generator->fn_name_ln.empty()) {
            DebugInfoVisitor visitor;
            visitor.result().emplace(1, generator->fn_name_ln);
            visitor.visit_content(generator);
            result_.emplace(generator->name, visitor.result());
        }
    }

    const std::map<std::string, std::map<uint32_t, std::vector<std::pair<std::string, uint32_t>>>>
        &result() {
        return result_;
    }

private:
    std::map<std::string, std::map<uint32_t, std::vector<std::pair<std::string, uint32_t>>>>
        result_;
};

std::map<std::string, std::map<uint32_t, std::vector<std::pair<std::string, uint32_t>>>>
extract_debug_info(Generator *top) {
    GeneratorDebugVisitor visitor;
    visitor.visit_generator_root(top);
    return visitor.result();
}

std::map<uint32_t, std::vector<std::pair<std::string, uint32_t>>> extract_debug_info_gen(
    Generator *top) {
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

static const std::string hgdb_assert_fail = "hgdb_assert_fail";

class AssertionVisitor : public IRVisitor {
public:
    void visit(AssertBase *stmt) override {
        if (stmt->fn_name_ln.empty()) return;
        auto *generator = stmt->generator_parent();
        auto const &[filename, line_num] = stmt->fn_name_ln[0];
        auto filename_var = Const::constant(filename, filename.size() * 8).shared_from_this();
        auto line_num_var =
            Const::constant(static_cast<int64_t>(line_num), 32, false).shared_from_this();
        auto gen_var = std::make_shared<GeneratorConst>(*generator);
        auto else_call = stmt->generator_parent()
                             ->call(hgdb_assert_fail, {gen_var, filename_var, line_num_var})
                             .as<FunctionCallVar>();
        auto else_stmt = std::make_shared<FunctionCallStmt>(else_call);
        if (stmt->assert_type() == AssertType::AssertValue) {
            auto *st = reinterpret_cast<AssertValueStmt *>(stmt);
            st->set_else(else_stmt);
        } else {
            auto st = stmt->as<AssertPropertyStmt>();
            auto *prop = st->property();
            if (prop->action() == PropertyAction::Assert) {
                st->set_else(else_stmt);
            }
        }
    }

private:
};

void inject_assertion_fail(Generator *top) {
    AssertionVisitor visitor;
    visitor.visit_root(top);
}

}  // namespace kratos
