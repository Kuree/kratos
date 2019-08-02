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

    [[nodiscard]]
    std::map<std::string, std::string> verilog_src();
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
    std::string str() { return stream_.str(); }

    uint32_t indent_size = 2;

    std::string indent();

    // helper function
    std::string static get_port_str(Port* port);
    static std::string get_var_width_str(const Var* var);

private:
    uint32_t indent_ = 0;
    Stream stream_;
    Generator* generator_;
    bool skip_indent_ = false;
    std::unordered_map<StmtBlock*, std::string> label_index_;

    void generate_ports(Generator* generator);
    void generate_variables(Generator* generator);
    void generate_parameters(Generator* generator);
    void generate_enums(Generator* generator);

    void dispatch_node(IRNode* node);

    void stmt_code(AssignStmt* stmt);

    void stmt_code(StmtBlock* stmt);

    void stmt_code(SequentialStmtBlock* stmt);

    void stmt_code(CombinationalStmtBlock* stmt);

    void stmt_code(ScopedStmtBlock* stmt);

    void stmt_code(IfStmt* stmt);

    void stmt_code(ModuleInstantiationStmt* stmt);

    void stmt_code(SwitchStmt* stmt);

    void enum_code(Enum* enum_);

    // reverse indexing the named blocks
    std::unordered_map<StmtBlock*, std::string> index_named_block();
    std::string block_label(StmtBlock *stmt);
};

}  // namespace kratos
#endif  // KRATOS_CODEGEN_HH
