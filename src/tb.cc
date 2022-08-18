#include "tb.hh"

#include <fmt/format.h>

#include "codegen.hh"
#include "except.hh"
#include "pass.hh"
#include "util.hh"

using fmt::format;

namespace kratos {

AssertValueStmt::AssertValueStmt(std::shared_ptr<Var> expr) : assert_var_(std::move(expr)) {
    // making sure that the expression has to be width 1
    if (assert_var_->width() != 1)
        throw VarException("Assert variable has to be width 1", {assert_var_.get()});
}

AssertValueStmt::AssertValueStmt() : AssertValueStmt(constant(0, 1).as<Const>()) {}

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
    auto func = [](Var *v) { return v->handle_name(true); };
    return to_string(func);
}

std::string Sequence::to_string(const std::function<std::string(Var *)> &var_str) const {
    auto wait_str = wait_to_str();
    std::string seq;
    if (wait_str.empty())
        seq = var_->handle_name(true);
    else
        seq = ::format("{0} {1}", wait_str, var_str(var_));
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

void Property::edge(kratos::EventEdgeType type, const std::shared_ptr<Var> &var) {
    if (var->width() != 1) throw VarException("{0} should be width 1", {var.get()});
    edge_ = EventControl(type, *var);
}

TestBench::TestBench(kratos::Context *context, const std::string &top_name)
    : Generator(context, top_name) {}

void TestBench::add_port_name(const std::string &name) {
    throw UserException("Top-level testbench not allowed to have port " + name);
}

}  // namespace kratos