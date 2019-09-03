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
    if (expr->width != 1) throw VarException("Assert variable has to be width 1", {expr.get()});
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

void Sequence::wait(uint32_t from_num_clk, uint32_t to_num_clk) {
    wait_low_ = from_num_clk;
    wait_high_ = to_num_clk;
}

Property::Property(std::string property_name, std::shared_ptr<Sequence> sequence)
    : property_name_(std::move(property_name)), sequence_(std::move(sequence)) {}

void Property::edge(kratos::BlockEdgeType type, std::shared_ptr<Var> &var) {
    if (var->width != 1) throw VarException("{0} should be width 1", {var.get()});
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
            return var->handle_name(false);
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
        auto const edge = property->edge();
        if (edge.first) {
            auto const &[var, type] = edge;
            stream_ << indent()
                    << ::format("@({0} {1}) ", type == Posedge ? "posedge" : "negedge",
                                var->handle_name(true));
        }
        stream_ << indent() << property->sequence()->to_string() << ";" << stream_.endl();
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
        stream_ << indent() << stmt->left()->handle_name() << " = " << stmt->right()->handle_name()
                << ";" << stream_.endl();
    }
};

std::string TestBench::codegen() {
    // fix connections
    fix_assignment_type(top_);
    create_module_instantiation(top_);
    verify_generator_connectivity(top_);

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