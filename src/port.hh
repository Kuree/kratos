#ifndef KRATOS_PORT_HH
#define KRATOS_PORT_HH

#include <optional>
#include <set>
#include <string>
#include <tuple>
#include <vector>
#include "expr.hh"

namespace kratos {

enum class PortDirection { In, Out, InOut };

enum class PortType { Data, Clock, AsyncReset, Reset, ClockEnable };

struct PackedSlice;

struct Port : public Var {
public:
    Port(Generator *module, PortDirection direction, const std::string &name, uint32_t width,
         uint32_t size, PortType type, bool is_signed);

    Port(Generator *module, PortDirection direction, const std::string &name, uint32_t width,
         const std::vector<uint32_t> &size, PortType type, bool is_signed);

    PortDirection port_direction() const { return direction_; }
    PortType port_type() const { return type_; }

    virtual void set_port_type(PortType type);

    // AST stuff
    void accept(IRVisitor *visitor) override { visitor->visit(this); }
    uint64_t child_count() override { return 0; }
    IRNode *get_child(uint64_t) override { return nullptr; }

    // coding convention, only valid for width 1 signal
    std::optional<bool> active_high() const { return active_high_; }
    void set_active_high(bool value);

private:
    PortDirection direction_;
    PortType type_;

    std::optional<bool> active_high_ = std::nullopt;
};

// diamond virtual inheritance is close to impossible in pybind. duplicate the logic here
struct EnumPort : public Port, public EnumType {
public:
    bool inline is_enum() const override { return true; }

    EnumPort(Generator *m, PortDirection direction, const std::string &name,
             const std::shared_ptr<Enum> &enum_type);

    std::shared_ptr<AssignStmt> assign(const std::shared_ptr<Var> &var,
                                       AssignmentType type) override;

    const inline Enum *enum_type() const override { return enum_type_; }
    void accept(IRVisitor *visitor) override { visitor->visit(this); }

private:
    Enum *enum_type_;
};

struct PortPackedStruct : public Port, public PackedInterface {
public:
    PortPackedStruct(Generator *module, PortDirection direction, const std::string &name,
                     PackedStruct packed_struct_);

    void set_port_type(PortType type) override;

    const PackedStruct &packed_struct() const { return struct_; }

    PackedSlice &operator[](const std::string &member_name);

    // necessary to make pybind happy due to complex inheritance
    VarSlice inline &operator[](std::pair<uint32_t, uint32_t> slice) override {
        return Var::operator[](slice);
    }
    VarSlice inline &operator[](uint32_t idx) override { return Var::operator[](idx); }

    bool is_struct() const override { return true; }

    std::set<std::string> member_names() const override;

    // struct is always packed
    bool is_packed() const override { return true; }
    void set_is_packed(bool value) override;

private:
    PackedStruct struct_;
};

struct PortBundleDefinition {
public:
    using PortDef = std::tuple<uint32_t, uint32_t, bool, PortDirection, PortType>;

    void add_definition(const std::string &name, uint32_t width, uint32_t size, bool is_signed,
                        PortDirection direction, PortType type);

    explicit PortBundleDefinition(std::string name) : name_(std::move(name)) {}

    [[nodiscard]] const std::map<std::string, PortDef> &definition() const { return definitions_; }
    [[nodiscard]] const std::map<std::string, std::pair<std::string, uint32_t>> &debug_info()
        const {
        return debug_info_;
    }

    void add_debug_info(const std::string &name, const std::pair<std::string, uint32_t> &info) {
        debug_info_.emplace(name, info);
    }

    void set_name(const std::string &name) { name_ = name; }
    [[nodiscard]] const std::string &get_name() const { return name_; }

    PortBundleDefinition flip();

private:
    std::string name_;
    std::map<std::string, PortDef> definitions_;
    std::map<std::string, PortDef> flipped_definitions_;
    std::map<std::string, std::pair<std::string, uint32_t>> debug_info_;

    PortBundleDefinition() = default;
};

struct PortBundleRef : public PackedInterface {
public:
    PortBundleRef(Generator *generator, PortBundleDefinition def)
        : generator(generator), definition_(std::move(def)) {}

    Port &get_port(const std::string &name);
    void add_name_mapping(const std::string &port_name, const std::string &real_name) {
        name_mappings_.emplace(port_name, real_name);
    }
    [[nodiscard]] const std::map<std::string, std::string> &name_mappings() const {
        return name_mappings_;
    }

    void assign(const std::shared_ptr<PortBundleRef> &other, Generator *parent,
                const std::vector<std::pair<std::string, uint32_t>> &debug_info);

    [[nodiscard]] const std::string &def_name() const { return definition_.get_name(); }

    [[nodiscard]] std::set<std::string> member_names() const override;

private:
    Generator *generator;
    const PortBundleDefinition definition_;
    std::map<std::string, std::string> name_mappings_;
};

struct InterfaceVarMapping {
public:
    // var mapping
    void set_var(const std::string &name, Var *var);
    [[nodiscard]] Var *get_var(const std::string &name) const;

    [[nodiscard]] virtual std::string to_string() const = 0;

private:
    std::map<std::string, Var *> gen_vars_;
};

struct InterfaceModPortDefinition;
struct InterfaceDefinition : public InterfaceVarMapping {
public:
    using InterfacePortDef = std::tuple<uint32_t, uint32_t, PortDirection>;

    std::shared_ptr<InterfaceModPortDefinition> create_modport_def(const std::string &name);

    void port(const std::string &name, uint32_t width, uint32_t size, PortDirection dir);
    void input(const std::string &name, uint32_t width, uint32_t size);
    void output(const std::string &name, uint32_t width, uint32_t size);
    void var(const std::string &name, uint32_t width, uint32_t size);

    [[nodiscard]] bool has_port(const std::string &name) const;
    [[nodiscard]] bool has_var(const std::string &name) const;

    [[nodiscard]] InterfacePortDef port(const std::string &name) const;
    [[nodiscard]] std::pair<uint32_t, uint32_t> var(const std::string &name) const;

    [[nodiscard]] const std::map<std::string, InterfacePortDef> &ports() const { return ports_; };
    [[nodiscard]] const std::map<std::string, std::pair<uint32_t, uint32_t>> &vars() const {
        return vars_;
    };

    [[nodiscard]]
    std::string to_string() const override { return name_; }

private:
    std::string name_;
    std::map<std::string, InterfacePortDef> ports_;
    std::map<std::string, std::pair<uint32_t, uint32_t>> vars_;
    std::map<std::string, std::shared_ptr<InterfaceModPortDefinition>> mod_ports_;
};

struct InterfaceModPortDefinition : public InterfaceVarMapping {
public:
    InterfaceModPortDefinition(InterfaceDefinition *def, std::string name);
    void input(const std::string &name);
    void output(const std::string &name);

    [[nodiscard]] std::string to_string() const override;

private:
    InterfaceDefinition *def_;
    std::string name_;

    std::set<std::string> inputs_;
    std::set<std::string> outputs_;
};

}  // namespace kratos

#endif  // KRATOS_PORT_HH
