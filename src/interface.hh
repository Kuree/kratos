#ifndef KRATOS_INTERFACE_HH
#define KRATOS_INTERFACE_HH

#include "expr.hh"
#include "port.hh"

namespace kratos {

struct IDefinition {
public:
    using InterfacePortDef = std::tuple<uint32_t, std::vector<uint32_t>, PortDirection>;
    using InterfaceVarDef = std::pair<uint32_t, std::vector<uint32_t>>;
    [[nodiscard]] virtual bool has_port(const std::string &name) const = 0;
    [[nodiscard]] virtual bool has_var(const std::string &name) const = 0;

    [[nodiscard]] virtual IDefinition::InterfacePortDef port(const std::string &name) const = 0;
    [[nodiscard]] virtual IDefinition::InterfaceVarDef var(const std::string &name) const = 0;

    [[nodiscard]] virtual std::set<std::string> ports() const = 0;
    [[nodiscard]] virtual std::set<std::string> vars() const = 0;

    [[nodiscard]] virtual const std::string &name() const = 0;
};

struct InterfaceDefinition : public IDefinition {
public:
    explicit InterfaceDefinition(std::string name) : name_(std::move(name)) {}

    std::shared_ptr<InterfaceModPortDefinition> create_modport_def(const std::string &name);

    void port(const std::string &name, uint32_t width, uint32_t size, PortDirection dir);
    void port(const std::string &name, uint32_t width, const std::vector<uint32_t> &size,
              PortDirection dir);
    void input(const std::string &name, uint32_t width, uint32_t size);
    void output(const std::string &name, uint32_t width, uint32_t size);
    void var(const std::string &name, uint32_t width, uint32_t size);
    void var(const std::string &name, uint32_t width, const std::vector<uint32_t> &size);

    [[nodiscard]] bool has_port(const std::string &name) const override;
    [[nodiscard]] bool has_var(const std::string &name) const override;

    [[nodiscard]] IDefinition::InterfacePortDef port(const std::string &name) const override;
    [[nodiscard]] IDefinition::InterfaceVarDef var(const std::string &name) const override;

    [[nodiscard]] std::set<std::string> ports() const override;
    [[nodiscard]] std::set<std::string> vars() const override;

    [[nodiscard]] const std::string &name() const override { return name_; }

private:
    std::string name_;
    std::map<std::string, IDefinition::InterfacePortDef> ports_;
    std::map<std::string, IDefinition::InterfaceVarDef> vars_;
    std::map<std::string, std::shared_ptr<InterfaceModPortDefinition>> mod_ports_;
};

struct InterfaceModPortDefinition : public IDefinition {
public:
    InterfaceModPortDefinition(InterfaceDefinition *def, std::string name);
    void set_input(const std::string &name);
    void set_output(const std::string &name);

    [[nodiscard]] bool has_port(const std::string &name) const override {
        return inputs_.find(name) != inputs_.end() || outputs_.find(name) != outputs_.end();
    }
    [[nodiscard]] bool has_var(const std::string &) const override { return false; }

    [[nodiscard]] IDefinition::InterfacePortDef port(const std::string &name) const override;
    [[nodiscard]] IDefinition::InterfaceVarDef var(const std::string &name) const override;

    [[nodiscard]] std::set<std::string> ports() const override;
    [[nodiscard]] std::set<std::string> vars() const override;

    [[nodiscard]] const std::set<std::string> &inputs() const { return inputs_; }
    [[nodiscard]] const std::set<std::string> &outputs() const { return outputs_; }

    [[nodiscard]] const InterfaceDefinition *def() const { return def_; }
    [[nodiscard]] const std::string &name() const override { return name_; }

private:
    InterfaceDefinition *def_;
    std::string name_;

    std::set<std::string> inputs_;
    std::set<std::string> outputs_;
};

struct InterfaceRef {
public:
    explicit InterfaceRef(std::shared_ptr<IDefinition> instance, Generator *gen, std::string name)
        : definition_(std::move(instance)), gen_(gen), name_(std::move(name)) {}
    Var &var(const std::string &name) const;
    Port &port(const std::string &name) const;
    void var(const std::string &name, Var *var) { vars_.emplace(name, var); }
    void port(const std::string &name, Port *port) { ports_.emplace(name, port); }
    [[nodiscard]] const std::unordered_map<std::string, Var *> &vars() const { return vars_; }
    [[nodiscard]] const std::unordered_map<std::string, Port *> &ports() const { return ports_; }

    [[nodiscard]] inline bool has_var(const std::string &name) const {
        return vars_.find(name) != vars_.end();
    }
    [[nodiscard]] inline bool has_port(const std::string &name) const {
        return ports_.find(name) != ports_.end();
    }

    bool &is_port() { return is_port_; }
    bool is_port() const { return is_port_; }

    [[nodiscard]] Generator *gen() const { return gen_; }
    [[nodiscard]] const std::string &name() const { return name_; }

private:
    std::shared_ptr<IDefinition> definition_;
    std::unordered_map<std::string, Var *> vars_;
    std::unordered_map<std::string, Port *> ports_;

    bool is_port_ = false;
    Generator *gen_;
    std::string name_;
};

}  // namespace kratos

#endif  // KRATOS_INTERFACE_HH
