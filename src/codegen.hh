#ifndef KRATOS_CODEGEN_HH
#define KRATOS_CODEGEN_HH

#include <sstream>
#include "ir.hh"
#include "context.hh"
#include "pass.hh"

class SystemVerilogCodeGen;

using DebugInfo = std::map<uint32_t, std::vector<std::pair<std::string, uint32_t>>>;

class VerilogModule {
public:
    explicit VerilogModule(Generator* generator) : generator_(generator) {}

    void run_passes(bool use_parallel, bool run_if_to_case_pass, bool remove_passthrough,
                    bool run_fanout_one_pass);

    const inline std::map<std::string, std::string>& verilog_src() const { return verilog_src_; }
    const inline std::map<std::string, DebugInfo>& debug_info() const { return debug_info_; }
    inline PassManager& pass_manager() { return manager_; }

private:
    std::map<std::string, std::string> verilog_src_;
    std::map<std::string, DebugInfo> debug_info_;
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
    const std::string str() { return stream_.str(); }

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

    void generate_ports(Generator* generator);
    void generate_variables(Generator* generator);
    void generate_parameters(Generator* generator);

    void dispatch_node(IRNode* node);

    void stmt_code(AssignStmt* stmt);

    void stmt_code(StmtBlock* stmt);

    void stmt_code(SequentialStmtBlock* stmt);

    void stmt_code(CombinationalStmtBlock* stmt);

    void stmt_code(IfStmt* stmt);

    void stmt_code(ModuleInstantiationStmt* stmt);

    void stmt_code(SwitchStmt* stmt);

    template <typename Iter>
    std::string static join(Iter begin, Iter end, const std::string& sep) {
        std::stringstream stream;
        for (auto it = begin; it != end; it++) {
            if (it != begin) stream << sep;
            stream << *it;
        }
        return stream.str();
    }
};

#endif  // KRATOS_CODEGEN_HH
