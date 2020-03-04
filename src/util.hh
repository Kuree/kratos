#ifndef KRATOS_UTIL_HH
#define KRATOS_UTIL_HH

#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <regex>
#include <sstream>
#include <thread>

#include "except.hh"
#include "expr.hh"
#include "fmt/format.h"
#include "generator.hh"
#include "port.hh"
#include "stmt.hh"

namespace kratos {

uint32_t get_num_cpus();
void set_num_cpus(int num_cpu);

std::string ExprOpStr(ExprOp op);

// may need to look at this https://stackoverflow.com/q/28828957
std::string var_type_to_string(VarType type);

std::string ast_type_to_string(IRNodeKind kind);

std::string assign_type_to_str(AssignmentType type);

std::string port_dir_to_str(PortDirection direction);

std::string port_type_to_str(PortType type);

std::string strip_newline(std::string &str);

bool is_valid_verilog(const std::string &src);

bool is_valid_verilog(const std::map<std::string, std::string> &src);

void remove_stmt_from_parent(const std::shared_ptr<Stmt> &stmt);

uint32_t clog2(uint32_t value);

std::pair<uint32_t, uint32_t> compute_var_high_low(
    const Var *root, const std::vector<std::pair<uint32_t, uint32_t>> &index);

std::vector<std::string> get_tokens(const std::string &line, const std::string &delimiter);

std::vector<std::vector<uint32_t>> get_flatten_slices(Var *var);

std::map<std::string, std::shared_ptr<Port>> get_port_from_verilog(Generator *generator,
                                                                   const std::string &src,
                                                                   const std::string &top_name);

bool inline is_2_power(uint64_t num) { return (num && (!(num & (num - 1)))); }

std::vector<std::string> line_wrap(const std::string &text, uint32_t line_width);

namespace color {
struct Color {
    unsigned char R;
    unsigned char G;
    unsigned char B;
};

Color hsv_to_rgb(double h, double s, double v);

}  // namespace color

namespace fs {
std::string join(const std::string &path1, const std::string &path2);
std::string which(const std::string &name);
bool exists(const std::string &filename);
bool remove(const std::string &filename);
std::string temp_directory_path();
std::string get_ext(const std::string &filename);
std::string abspath(const std::string &filename);
std::string basename(const std::string &filename);
char separator();
}  // namespace fs

namespace string {
template <typename Iter>
std::string static join(Iter begin, Iter end, const std::string &sep) {
    std::stringstream stream;
    for (auto it = begin; it != end; it++) {
        if (it != begin) stream << sep;
        stream << *it;
    }
    return stream.str();
}
void trim(std::string &str);
std::vector<std::string> get_tokens(const std::string &line, const std::string &delimiter);
}  // namespace string

}  // namespace kratos

#endif  // KRATOS_UTIL_HH
