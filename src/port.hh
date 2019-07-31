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
         uint32_t size, PortType type, bool is_signed);

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

struct PortBundleDefinition : public std::enable_shared_from_this<PortBundleDefinition> {
public:
    using PortDef = std::tuple<uint32_t, uint32_t, bool, PortDirection, PortType>;

    void add_definition(const std::string &name, uint32_t width, uint32_t size, bool is_signed,
                        PortDirection direction, PortType type);

    [[nodiscard]] const std::map<std::string, PortDef> &definition() const { return definitions_; }
    [[nodiscard]] const std::map<std::string, std::pair<std::string, uint32_t>> &debug_info()
        const {
        return debug_info_;
    }

    void add_debug_info(const std::string &name, const std::pair<std::string, uint32_t> &info) {
        debug_info_.emplace(name, info);
    }

    std::shared_ptr<PortBundleDefinition> flip();

private:
    std::map<std::string, PortDef> definitions_;
    // this is for performance reason, we don't want to flip all the time
    // so flip().flip() should return to the same one
    std::shared_ptr<PortBundleDefinition> flipped_ = nullptr;
    std::map<std::string, PortDef> flipped_definitions_;
    std::map<std::string, std::pair<std::string, uint32_t>> debug_info_;
};

struct PortBundleRef {
public:
    PortBundleRef(Generator *generator, std::shared_ptr<PortBundleDefinition> def)
        : generator(generator), definition_(std::move(def)) {}

    Port &get_port(const std::string &name);
    void add_name_mapping(const std::string &port_name, const std::string &real_name) {
        name_mappings_.emplace(port_name, real_name);
    }

    void assign(const std::shared_ptr<PortBundleRef> &other, Generator *parent,
                const std::vector<std::pair<std::string, uint32_t>> &debug_info);

private:
    Generator *generator;
    const std::shared_ptr<PortBundleDefinition> definition_;
    std::map<std::string, std::string> name_mappings_;
};

}  // namespace kratos

#endif  // KRATOS_PORT_HH
