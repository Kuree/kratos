#ifndef KRATOS_DEBUG_HH
#define KRATOS_DEBUG_HH

#include "stmt.hh"

namespace kratos {

constexpr char break_point_func_name[] = "breakpoint_trace";
constexpr char break_point_clock_func_name[] = "breakpoint_clock";
constexpr char break_point_func_arg[] = "stmt_id";

void inject_debug_break_points(Generator *top);
std::map<Stmt *, uint32_t> extract_debug_break_points(Generator *top);
void inject_clock_break_points(Generator *top);
void inject_clock_break_points(Generator *top, const std::string &clk_name);
void inject_clock_break_points(Generator *top, const std::shared_ptr<Port> &port);

// for verilator
void insert_verilator_public(Generator *top);

class DebugDatabase {
public:
    using ConnectionMap =
        std::map<std::pair<std::string, std::string>, std::pair<std::string, std::string>>;

    DebugDatabase() = default;
    explicit DebugDatabase(std::string top_name) : top_name_(std::move(top_name)) {}

    void set_break_points(Generator *top);
    void set_break_points(Generator *top, const std::string &ext);

    // these have to be called after unification happens
    void set_generator_connection(Generator *top);
    void set_generator_hierarchy(Generator *top);

    void set_variable_mapping(const std::map<Generator *, std::map<std::string, Var *>> &mapping);
    void set_generator_variable(
        const std::map<Generator *, std::map<std::string, std::string>> &values);
    void set_stmt_context(Generator *top);

    void save_database(const std::string &filename);

private:
    std::map<Stmt *, uint32_t> break_points_;
    std::unordered_map<Generator *, std::set<uint32_t>> generator_break_points_;
    std::map<Stmt *, std::pair<std::string, uint32_t>> stmt_mapping_;
    std::unordered_map<std::string, std::pair<Generator *, std::map<std::string, std::string>>>
        variable_mapping_;
    std::unordered_map<std::string, std::map<std::string, std::string>> generator_values_;
    ConnectionMap connection_map_;
    std::vector<std::pair<std::string, std::string>> hierarchy_;
    std::map<Stmt *, std::map<std::string, std::pair<bool, std::string>>> stmt_context_;

    std::string top_name_ = "TOP";
};

}  // namespace kratos
#endif  // KRATOS_DEBUG_HH
