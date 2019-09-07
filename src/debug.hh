#ifndef KRATOS_DEBUG_HH
#define KRATOS_DEBUG_HH

#include "stmt.hh"

namespace kratos {

std::unordered_map<Stmt *, uint32_t> inject_debug_break_points(Generator *top);

void insert_debugger_setup(Generator *top);

class DebugDatabase {
    using VarMapping = std::unordered_map<std::string, Var *>;

public:
    DebugDatabase() = default;
    explicit DebugDatabase(std::string top_name) : top_name_(std::move(top_name)) {}

    void set_break_points(const std::unordered_map<Stmt *, uint32_t> &break_points);
    void set_break_points(const std::unordered_map<Stmt *, uint32_t> &break_points,
                          const std::string &ext);

    void set_variable_mapping(const std::unordered_map<Generator*, VarMapping> &variable_mapping);

    void save_database(const std::string &filename);

private:
    std::unordered_map<Stmt *, uint32_t> break_points_;
    std::unordered_map<Stmt *, std::pair<std::string, uint32_t>> stmt_mapping_;
    std::unordered_map<Generator *, VarMapping> variable_mapping_;

    std::string top_name_ = "TOP";
};

}  // namespace kratos
#endif  // KRATOS_DEBUG_HH
