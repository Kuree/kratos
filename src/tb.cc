#include "tb.hh"
#include <fmt/format.h>
#include "codegen.hh"
#include "except.hh"
#include "pass.hh"
#include "util.hh"

using fmt::format;

namespace kratos {

AssertValueStmt::AssertValueStmt(const std::shared_ptr<Var> &expr) : assert_var_(expr.get()) {
    // making sure that the expression has to be width 1
    if (expr->width() != 1) throw VarException("Assert variable has to be width 1", {expr.get()});
}

AssertPropertyStmt::AssertPropertyStmt(const std::shared_ptr<Property> &property)
    : property_(property.get()) {}

Sequence *Sequence::imply(const std::shared_ptr<Var> &var) {
    next_ = std::make_shared<Sequence>(var);
    next_->parent_ = this;
    return next_.get();
}

std::string Sequence::wait_to_str() const {
    if (wait_low_ == 0 && wait_high_ == 0)
        return "";
    else if (wait_low_ == wait_high_)
        return ::format("##{0}", wait_low_);
    else
        return ::format("##[{0}:{1}]", wait_low_, wait_high_);
}

std::string Sequence::to_string() const {
    auto wait_str = wait_to_str();
    std::string seq;
    if (wait_str.empty())
        seq = var_->handle_name(true);
    else
        seq = ::format("{0} {1}", wait_str, var_->handle_name(true));
    if (next_) {
        auto next = next_->to_string();
        seq = ::format("{0} |-> {1}", seq, next);
    }
    return seq;
}

Sequence *Sequence::wait(uint32_t from_num_clk, uint32_t to_num_clk) {
    wait_low_ = from_num_clk;
    wait_high_ = to_num_clk;
    return this;
}

Property::Property(std::string property_name, std::shared_ptr<Sequence> sequence)
    : property_name_(std::move(property_name)), sequence_(std::move(sequence)) {}

void Property::edge(kratos::BlockEdgeType type, const std::shared_ptr<Var> &var) {
    if (var->width() != 1) throw VarException("{0} should be width 1", {var.get()});
    edge_ = {var.get(), type};
}

TestBench::TestBench(Context *context, const std::string &top_name) {
    auto &gen = context->generator(top_name);
    top_ = &gen;
}

std::shared_ptr<Property> TestBench::property(const std::string &property_name,
                                              const std::shared_ptr<Sequence> &sequence) {
    if (properties_.find(property_name) != properties_.end())
        throw UserException(
            ::format("Property {0} already exists in {1}", property_name, top_->name));
    auto prop = std::make_shared<Property>(property_name, sequence);
    properties_.emplace(property_name, prop);
    return prop;
}

void TestBench::wire(const std::shared_ptr<Var> &var, const std::shared_ptr<Port> &port) {
    top_->add_stmt(var->assign(port));
}

void TestBench::wire(std::shared_ptr<Port> &port1, std::shared_ptr<Port> &port2) {
    top_->wire_ports(port1, port2);
}

void TestBench::wire(const std::shared_ptr<Var> &src, const std::shared_ptr<Var> &sink) {
    top_->add_stmt(src->assign(sink));
}

class TestBenchCodeGen : public SystemVerilogCodeGen {
public:
    explicit TestBenchCodeGen(Generator *top) : SystemVerilogCodeGen(top), top_(top) {}

private:
    Generator *top_;
    // override the default behavior
    void dispatch_node(IRNode *node) override {
        if (node->ir_node_kind() != IRNodeKind::StmtKind)
            throw StmtException(::format("Cannot codegen non-statement node. Got {0}",
                                         ast_type_to_string(node->ir_node_kind())),
                                {node});
        auto stmt_ptr = reinterpret_cast<Stmt *>(node);
        if (stmt_ptr->type() == StatementType::Assert) {
            auto assert_base = reinterpret_cast<AssertBase *>(stmt_ptr);
            switch (assert_base->assert_type()) {
                case AssertType::AssertValue:
                    stmt_code(reinterpret_cast<AssertValueStmt *>(stmt_ptr));
                    break;
                case AssertType::AssertProperty:
                    stmt_code(reinterpret_cast<AssertPropertyStmt *>(stmt_ptr));
                    break;
            }
        } else {
            SystemVerilogCodeGen::dispatch_node(node);
        }
    }

    std::string var_name(Var *var) {
        if (var->parent() == top_ || var->parent() == Const::const_gen())
            return var->to_string();
        else
            return var->handle_name(true);
    }

protected:
    void stmt_code(AssertValueStmt *stmt) {
        stream_ << indent() << "assert (" << stmt->value()->handle_name(true) << ");"
                << stream_.endl();
    }

    void stmt_code(AssertPropertyStmt *stmt) {
        auto property = stmt->property();
        stream_ << indent() << "property " << property->property_name() << ";" << stream_.endl();
        increase_indent();
        auto edge = property->edge();
        auto seq = property->sequence();
        // automatically determine the clock, only if it's safe to do so (only one clock in the
        // design
        if (!edge.first && seq->next()) {
            // try to determine the clock
            // it's concurrent property, we have to have a clock
            auto generator = stmt->generator_parent();
            // because it's a test bench, the variable doesn't have type
            // we need to source for connected modules to see what they are connected to
            auto children = generator->get_child_generators();
            std::vector<Var *> clk_vars;
            for (auto const &gen : children) {
                auto clks = gen->get_ports(PortType::Clock);
                for (auto const &clk_name : clks) {
                    auto clk = gen->get_port(clk_name);
                    auto source = clk->sources();
                    for (auto const &assign : source) {
                        auto src_var = assign->right();
                        if (src_var->generator == generator && src_var->type() == VarType::Base) {
                            clk_vars.emplace_back(src_var.get());
                        }
                    }
                }
            }
            if (clk_vars.size() == 1) {
                edge.first = clk_vars[0];
                edge.second = Posedge;
            } else {
                // next is not null but edge is not set
                throw StmtException(
                    ::format("Clock edge not set for sequence {0}", seq->to_string()), {stmt});
            }
        }
        if (edge.first) {
            auto const &[var, type] = edge;
            stream_ << indent()
                    << ::format("@({0} {1}) ", type == Posedge ? "posedge" : "negedge",
                                var->handle_name(true));
        }
        stream_ << seq->to_string() << ";" << stream_.endl();
        decrease_indent();
        stream_ << indent() << "endproperty" << stream_.endl();

        // put assert here
        stream_ << indent() << "assert property (" << property->property_name() << ");"
                << stream_.endl();
    }

    void stmt_code(AssignStmt *stmt) override {
        if (stmt->assign_type() != Blocking) {
            throw StmtException("Test bench assignment as to be blocking", {stmt});
        }
        if ((stmt->left()->type() == VarType::PortIO && stmt->left()->generator != top_) ||
            (stmt->right()->type() == VarType::PortIO && stmt->right()->generator != top_))
            return;
        std::string delay_str;
        if (stmt->get_delay() > 0) {
            int delay = stmt->get_delay();
            delay_str = ::format("#{0} ", delay);
        }
        stream_ << indent() << delay_str << var_name(stmt->left().get()) << " = "
                << var_name(stmt->right().get()) << ";" << stream_.endl();
    }
};

uint32_t get_order(const std::shared_ptr<Stmt> &stmt) {
    if (stmt->type() != StatementType::Block) return 0;
    auto block = stmt->as<StmtBlock>();
    if (block->block_type() != StatementBlockType::Initial) return 0;
    return 1;
}

void sort_initials(Generator *top) {
    auto const &stmts = top->get_all_stmts();
    auto new_stmts = std::vector<std::shared_ptr<Stmt>>(stmts.begin(), stmts.end());

    // move initialize to the last
    std::sort(new_stmts.begin(), new_stmts.end(), [](const auto &left, const auto &right) {
        return get_order(left) < get_order(right);
    });

    top->set_stmts(new_stmts);
}

std::string TestBench::codegen() {
    // fix connections
    fix_assignment_type(top_);
    create_module_instantiation(top_);
    verify_generator_connectivity(top_);

    // sort initials in case we need to access internal signals
    sort_initials(top_);

    // need to convert properties into properties statement
    for (auto const &iter : properties_) {
        auto stmt = std::make_shared<AssertPropertyStmt>(iter.second);
        top_->add_stmt(stmt);
    }

    // code gen the module top
    TestBenchCodeGen code_gen(top_);
    return code_gen.str();
}

}