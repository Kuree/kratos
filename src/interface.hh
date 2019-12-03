#ifndef KRATOS_INTERFACE_HH
#define KRATOS_INTERFACE_HH

#include "expr.hh"
#include "port.hh"

namespace kratos {
struct InterfaceDefinition {
public:
    using InterfacePortDef = std::tuple<uint32_t, std::vector<uint32_t>, PortDirection>;
    using InterfaceVarDef = std::pair<uint32_t, std::vector<uint32_t>>;

    std::shared_ptr<InterfaceModPortDefinition> create_modport_def(const std::string &name);

    void port(const std::string &name, uint32_t width, uint32_t size, PortDirection dir);
    void input(const std::string &name, uint32_t width, uint32_t size);
    void output(const std::string &name, uint32_t width, uint32_t size);
    void var(const std::string &name, uint32_t width, uint32_t size);

    [[nodiscard]] bool has_port(const std::string &name) const;
    [[nodiscard]] bool has_var(const std::string &name) const;

    [[nodiscard]] InterfacePortDef port(const std::string &name) const;
    [[nodiscard]] InterfaceVarDef var(const std::string &name) const;

    [[nodiscard]] const std::map<std::string, InterfacePortDef> &ports() const { return ports_; };
    [[nodiscard]] const std::map<std::string, InterfaceVarDef> &vars() const { return vars_; };

    [[nodiscard]] virtual std::string name() const { return name_; }

private:
    std::string name_;
    std::map<std::string, InterfacePortDef> ports_;
    std::map<std::string, InterfaceVarDef> vars_;
    std::map<std::string, std::shared_ptr<InterfaceModPortDefinition>> mod_ports_;
};

struct InterfaceModPortDefinition {
public:
    InterfaceModPortDefinition(InterfaceDefinition *def, std::string name);
    void input(const std::string &name);
    void output(const std::string &name);

    [[nodiscard]] std::string name() const;
    [[nodiscard]] const std::set<std::string> &inputs() const { return inputs_; }
    [[nodiscard]] const std::set<std::string> &outputs() const { return outputs_; }

    [[nodiscard]] const InterfaceDefinition *def() const { return def_; }

private:
    InterfaceDefinition *def_;
    std::string name_;

    std::set<std::string> inputs_;
    std::set<std::string> outputs_;
};

struct InterfaceInstance {
    // also wraps around the interface and mod port interface
public:
    explicit InterfaceInstance(std::string inst_name) : inst_name_(std::move(inst_name)) {}
    [[nodiscard]] virtual std::string def_name() const = 0;
    [[nodiscard]] std::string inst_name() const { return inst_name_; }

    [[nodiscard]] virtual std::map<std::string, InterfaceDefinition::InterfacePortDef> ports()
        const = 0;
    [[nodiscard]] virtual std::map<std::string, InterfaceDefinition::InterfaceVarDef> vars()
        const = 0;

private:
    std::string inst_name_;
};

struct InterfaceInterfaceInstance : public InterfaceInstance {
public:
    InterfaceInterfaceInstance(InterfaceDefinition *def, const std::string &name)
        : InterfaceInstance(name), def_(def) {}

    [[nodiscard]] std::map<std::string, InterfaceDefinition::InterfacePortDef> ports()
        const override {
        return def_->ports();
    }

    [[nodiscard]] std::map<std::string, InterfaceDefinition::InterfaceVarDef> vars()
        const override {
        return def_->vars();
    }

private:
    InterfaceDefinition *def_;
};

struct ModPortInterfaceInstance : public InterfaceInstance {
public:
    ModPortInterfaceInstance(InterfaceModPortDefinition *def, const std::string &name)
        : InterfaceInstance(name), def_(def) {}

    [[nodiscard]] std::map<std::string, InterfaceDefinition::InterfacePortDef> ports()
        const override;

    [[nodiscard]] std::map<std::string, InterfaceDefinition::InterfaceVarDef> vars()
        const override {
        return {};
    }

private:
    InterfaceModPortDefinition *def_;
};

struct InterfaceRef {
public:
    explicit InterfaceRef(std::shared_ptr<InterfaceInstance> instance)
        : instance_(std::move(instance)) {}
    Var &var(const std::string &name) const;
    Port &port(const std::string &name) const;
    void var(const std::string &name, Var *var) { vars_.emplace(name, var); }
    void port(const std::string &name, Port *port) { ports_.emplace(name, port); }

    [[nodiscard]] inline bool has_var(const std::string &name) const {
        return vars_.find(name) != vars_.end();
    }
    [[nodiscard]] inline bool has_port(const std::string &name) const {
        return ports_.find(name) != ports_.end();
    }

    bool &is_port() { return is_port_; }
    bool is_port() const { return is_port_; }

private:
    std::shared_ptr<InterfaceInstance> instance_;
    std::unordered_map<std::string, Var *> vars_;
    std::unordered_map<std::string, Port *> ports_;

    bool is_port_ = false;
};

}  // namespace kratos

#endif  // KRATOS_INTERFACE_HH
