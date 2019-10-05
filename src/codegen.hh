#ifndef KRATOS_CODEGEN_HH
#define KRATOS_CODEGEN_HH

#include <sstream>
#include "context.hh"
#include "ir.hh"
#include "pass.hh"

namespace kratos {

class SystemVerilogCodeGen;

using DebugInfo = std::map<uint32_t, std::vector<std::pair<std::string, uint32_t>>>;

class VerilogModule {
public:
    explicit VerilogModule(Generator* generator) : generator_(generator) {
        manager_.register_builtin_passes();
    }

    void run_passes();

    [[nodiscard]] std::map<std::string, std::string> verilog_src();
    inline PassManager& pass_manager() { return manager_; }

private:
    Generator* generator_;

    PassManager manager_;
};

class Stream : public std::stringstream {
public:
    explicit Stream(Generator* generator, SystemVerilogCodeGen* codegen);
    Stream& operator<<(AssignStmt* stmt);
    Stream& operator<<(const std::pair<Port*, std::string>& port);
    Stream& operator<<(const std::shared_ptr<Var>& var);

    inline char endl() {
        line_no_++;
        return '\n';
    }

    inline uint32_t line_no() const { return line_no_; }

private:
    Generator* generator_;
    SystemVerilogCodeGen* codegen_;
    uint64_t line_no_;
};

class SystemVerilogCodeGen {
public:
    explicit SystemVerilogCodeGen(Generator* generator);
    SystemVerilogCodeGen(Generator* generator, std::string package_name, std::string header_name);

    inline std::string str() {
        output_module_def(generator_);
        return stream_.str();
    }

    uint32_t indent_size = 2;

    std::string indent();
    void increase_indent() { indent_++; }
    void decrease_indent() { indent_--; }

    // helper function
    std::string static get_port_str(Port* port);
    static std::string get_var_width_str(const Var* var);

private:
    uint32_t indent_ = 0;
    Generator* generator_;
    bool skip_indent_ = false;
    std::unordered_map<StmtBlock*, std::string> label_index_;
    std::string package_name_;
    std::string header_include_name_;

protected:
    Stream stream_;
    void generate_ports(Generator* generator);
    void generate_variables(Generator* generator);
    void generate_parameters(Generator* generator);
    void generate_enums(Generator* generator);
    void generate_functions(Generator* generator);

    virtual void dispatch_node(IRNode* node);

    virtual void stmt_code(AssignStmt* stmt);

    void stmt_code(ReturnStmt* stmt);

    void stmt_code(StmtBlock* stmt);

    void stmt_code(SequentialStmtBlock* stmt);

    void stmt_code(CombinationalStmtBlock* stmt);

    void stmt_code(ScopedStmtBlock* stmt);

    void stmt_code(IfStmt* stmt);

    void stmt_code(ModuleInstantiationStmt* stmt);

    void stmt_code(SwitchStmt* stmt);

    void stmt_code(FunctionStmtBlock* stmt);

    void stmt_code(InitialStmtBlock* stmt);

    void stmt_code(FunctionCallStmt* stmt);

    void enum_code(Enum* enum_);

    // reverse indexing the named blocks
    std::unordered_map<StmtBlock*, std::string> index_named_block();
    std::string block_label(StmtBlock* stmt);

    // the actual code gen part
    void output_module_def(Generator* generator);
};

}  // namespace kratos
#endif  // KRATOS_CODEGEN_HH
