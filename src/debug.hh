#ifndef KRATOS_DEBUG_HH
#define KRATOS_DEBUG_HH

#include "stmt.hh"

namespace kratos {

constexpr char break_point_func_name[] = "breakpoint_trace";
constexpr char break_point_clock_func_name[] = "breakpoint_clock";
constexpr char exception_func_name[] = "exception";
constexpr char break_point_func_arg[] = "stmt_id";
constexpr char break_point_param_name[] = "KRATOS_INSTANCE_ID";
constexpr char break_point_instance_id_arg[] = "instance_id";

void inject_debug_break_points(Generator *top);
void inject_instance_ids(Generator *top);
std::map<Stmt *, uint32_t> extract_debug_break_points(Generator *top);
void inject_clock_break_points(Generator *top);
void inject_clock_break_points(Generator *top, const std::string &clk_name);
void inject_clock_break_points(Generator *top, const std::shared_ptr<Port> &port);
void inject_assert_fail_exception(Generator *top);
void remove_assertion(Generator *top);
void convert_continuous_stmt(Generator *top);
void propagate_scope_variable(Generator *top);
std::unordered_map<Var *, std::unordered_set<Var *>> find_driver_signal(Generator *top);
// this is a pass for systems that don't fully integrate kratos as their backend but only
// want to partially use Kratos' debuggability
// it will fake a hierarchy
void mock_hierarchy(Generator *top, const std::string &top_name = "");

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
    void set_variable_mapping(
        const std::map<Generator *, std::map<std::string, std::string>> &mapping);
    void set_stmt_context(Generator *top);

    void save_database(const std::string &filename, bool override);
    void save_database(const std::string &filename) { save_database(filename, true); }

private:
    std::map<Stmt *, uint32_t> break_points_;
    std::unordered_map<Generator *, std::set<uint32_t>> generator_break_points_;
    std::map<Stmt *, std::pair<std::string, uint32_t>> stmt_mapping_;
    std::unordered_map<std::string, std::pair<Generator *, std::map<std::string, std::string>>>
        variable_mapping_;
    ConnectionMap connection_map_;
    std::vector<std::pair<std::string, Generator *>> hierarchy_;
    std::map<Stmt *, std::map<std::string, std::pair<bool, std::string>>> stmt_context_;
    std::unordered_set<Generator *> generators_;

    std::string top_name_ = "TOP";
    Context *context_ = nullptr;
};

}  // namespace kratos
#endif  // KRATOS_DEBUG_HH
