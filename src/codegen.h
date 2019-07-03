#ifndef KRATOS_CODEGEN_H
#define KRATOS_CODEGEN_H

#include <sstream>
#include "ast.hh"
#include "context.hh"

class SystemVerilogCodeGen;

using DebugInfo = std::map<uint32_t, std::vector<std::pair<std::string, uint32_t>>>;

class VerilogModule {
public:
    explicit VerilogModule(Generator* generator) : generator_(generator) {}

    void run_passes(bool run_if_to_case_pass, bool remove_passthrough, bool run_fanout_one_pass);

    const inline std::map<std::string, std::string>& verilog_src() const { return verilog_src_; }
    const inline std::map<std::string, DebugInfo>& debug_info() const { return debug_info_; }

private:
    std::map<std::string, std::string> verilog_src_;
    std::map<std::string, DebugInfo> debug_info_;
    Generator* generator_;
};

class Stream : public std::stringstream {
public:
    explicit Stream(Generator* generator, SystemVerilogCodeGen* codegen);
    Stream& operator<<(AssignStmt* stmt);

    inline char endl() {
        line_no_++;
        return '\n';
    }

    const inline std::map<AssignStmt*, std::vector<std::pair<std::string, uint32_t>>>&
    stmt_mapping() const {
        return stmt_mapping_;
    }
    const inline std::map<AssignStmt*, uint32_t>& verilog_mapping() const {
        return verilog_mapping_;
    }

private:
    Generator* generator_;
    SystemVerilogCodeGen* codegen_;
    uint64_t line_no_;
    std::map<AssignStmt*, std::vector<std::pair<std::string, uint32_t>>> stmt_mapping_;
    std::map<AssignStmt*, uint32_t> verilog_mapping_;
};

class SystemVerilogCodeGen {
public:
    explicit SystemVerilogCodeGen(Generator* generator);
    const std::string str() { return stream_.str(); }

    uint32_t indent_size = 2;

    std::string indent();

    std::map<uint32_t, std::vector<std::pair<std::string, uint32_t>>> stmt_mapping() const;

private:
    uint32_t indent_ = 0;
    Stream stream_;
    Generator* generator_;
    bool skip_indent_ = false;

    static std::string get_var_width_str(const Var* var);
    void generate_ports(Generator* generator);
    void generate_variables(Generator* generator);
    std::string get_port_str(Port* port);

    void dispatch_node(ASTNode* node);

    void stmt_code(AssignStmt* stmt);

    void stmt_code(StmtBlock* stmt);

    void stmt_code(SequentialStmtBlock* stmt);

    void stmt_code(CombinationalStmtBlock* stmt);

    void stmt_code(IfStmt* stmt);

    void stmt_code(ModuleInstantiationStmt* stmt);

    void stmt_code(SwitchStmt* stmt);

    template <typename Iter>
    std::string join(Iter begin, Iter end, const std::string& sep) {
        std::stringstream stream;
        for (auto it = begin; it != end; it++) {
            if (it != begin) stream << sep;
            stream << *it;
        }
        return stream.str();
    }
};

#endif  // KRATOS_CODEGEN_H
