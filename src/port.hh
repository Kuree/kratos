#ifndef KRATOS_PORT_HH
#define KRATOS_PORT_HH

#include <set>
#include <string>
#include <tuple>
#include <vector>

#include "expr.hh"

namespace kratos {

enum class PortDirection { In, Out, InOut };

enum class PortType { Data, Clock, AsyncReset, Reset, ClockEnable };

struct PortPackedSlice;

struct Port : public Var {
public:
    Port(Generator *module, PortDirection direction, const std::string &name, uint32_t width,
         PortType type, bool is_signed);

    PortDirection port_direction() const { return direction_; }
    PortType port_type() const { return type_; }

    virtual void set_port_type(PortType type);
    virtual bool inline is_packed() { return false; }

    // AST stuff
    void accept(IRVisitor *visitor) override { visitor->visit(this); }
    uint64_t child_count() override { return 0; }
    IRNode *get_child(uint64_t) override { return nullptr; }

private:
    PortDirection direction_;
    PortType type_;
};

struct PackedStruct {
public:
    std::string struct_name;
    std::vector<std::tuple<std::string, uint32_t, bool>> attributes;

    PackedStruct(std::string struct_name,
                 std::vector<std::tuple<std::string, uint32_t, bool>> attributes);
};

struct PortPacked : public Port {
public:
    PortPacked(Generator *module, PortDirection direction, const std::string &name,
               PackedStruct packed_struct_);

    void set_port_type(PortType type) override;

    const PackedStruct &packed_struct() const { return struct_; }

    PortPackedSlice &operator[](const std::string &member_name);

    // necessary to make pybind happy due to complex inheritance
    VarSlice inline &operator[](std::pair<uint32_t, uint32_t> slice) override {
        return Var::operator[](slice);
    }
    VarSlice inline &operator[](uint32_t idx) override { return Var::operator[](idx); }

    bool is_packed() override { return true; }

private:
    PackedStruct struct_;

    std::unordered_map<std::string, std::shared_ptr<PortPackedSlice>> members_;
};

struct PortPackedSlice : public VarSlice {
public:
    PortPackedSlice(PortPacked *parent, const std::string &member_name);

    std::string to_string() const override;

private:
    std::string member_name_;
};

}  // namespace kratos

#endif  // KRATOS_PORT_HH
