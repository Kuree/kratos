#ifndef KRATOS_DEBUG_HH
#define KRATOS_DEBUG_HH

#include "stmt.hh"

namespace kratos {

constexpr char break_point_func_name[] = "breakpoint_trace";
constexpr char break_point_func_arg[] = "stmt_id";

void inject_debug_break_points(Generator *top);
std::map<Stmt *, uint32_t> extract_debug_break_points(Generator *top);

// for verilator
void insert_verilator_public(Generator *top);

class DebugDatabase {
public:
    DebugDatabase() = default;
    explicit DebugDatabase(std::string top_name) : top_name_(std::move(top_name)) {}

    void set_break_points(Generator *top);
    void set_break_points(Generator *top, const std::string &ext);

    void set_variable_mapping(const std::map<Generator *, std::map<std::string, Var *>> &mapping);

    void save_database(const std::string &filename);

private:
    std::map<Stmt *, uint32_t> break_points_;
    std::unordered_map<Generator *, std::set<uint32_t>> generator_break_points_;
    std::map<Stmt *, std::pair<std::string, uint32_t>> stmt_mapping_;
    std::unordered_map<std::string, std::pair<Generator *, std::map<std::string, std::string>>>
        variable_mapping_;

    std::string top_name_ = "TOP";
};

}  // namespace kratos
#endif  // KRATOS_DEBUG_HH
