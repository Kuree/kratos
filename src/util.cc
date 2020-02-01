#include "util.hh"

#include <cstdlib>
#ifdef INCLUDE_FILESYSTEM
#include <filesystem>
#endif
#include <fstream>
#include <regex>
#include <thread>

#include "except.hh"
#include "expr.hh"
#include "fmt/format.h"
#include "generator.hh"
#include "port.hh"
#include "stmt.hh"

using fmt::format;

namespace kratos {

static int _num_cpu = -1;

uint32_t get_num_cpus() {
    if (_num_cpu < 0) {
        // compute the number of CPUs being used
        uint32_t num_cpus = std::thread::hardware_concurrency();
        _num_cpu = static_cast<int>(std::max(1u, num_cpus / 2));
    }
    return static_cast<uint32_t>(_num_cpu);
}
void set_num_cpus(int num_cpu) { _num_cpu = num_cpu; }

std::string ExprOpStr(ExprOp op) {
    switch (op) {
        case ExprOp::UInvert:
            return "~";
        case ExprOp::UNot:
            return "!";
        case ExprOp::UMinus:
        case ExprOp::Minus:
            return "-";
        case ExprOp::UPlus:
        case ExprOp::Add:
            return "+";
        case ExprOp::Divide:
            return "/";
        case ExprOp::Multiply:
            return "*";
        case ExprOp::Mod:
            return "%";
        case ExprOp::LogicalShiftRight:
            return ">>";
        case ExprOp::SignedShiftRight:
            return ">>>";
        case ExprOp::ShiftLeft:
            return "<<";
        case ExprOp::UOr:
        case ExprOp::Or:
            return "|";
        case ExprOp::UAnd:
        case ExprOp::And:
            return "&";
        case ExprOp::UXor:
        case ExprOp::Xor:
            return "^";
        case ExprOp::LessThan:
            return "<";
        case ExprOp::GreaterThan:
            return ">";
        case ExprOp::LessEqThan:
            return "<=";
        case ExprOp::GreaterEqThan:
            return ">=";
        case ExprOp::Eq:
            return "==";
        case ExprOp::Neq:
            return "!=";
        case ExprOp::Conditional:
            return ":";
        case ExprOp::Concat:
            return ",";
        case ExprOp::LAnd:
            return "&&";
        case ExprOp::LOr:
            return "||";
        default:
            throw std::runtime_error("unable to find op");
    }
}

std::string var_type_to_string(VarType type) {
    if (type == VarType::Base)
        return "Base";
    else if (type == VarType::PortIO)
        return "Port";
    else if (type == VarType::Expression)
        return "Expression";
    else if (type == VarType::ConstValue)
        return "Const";
    else
        return "Slice";
}

std::string ast_type_to_string(IRNodeKind kind) {
    if (kind == IRNodeKind::StmtKind)
        return "Statement";
    else if (kind == IRNodeKind::VarKind)
        return "Variable";
    else
        return "Generator";
}

std::string assign_type_to_str(AssignmentType type) {
    if (type == AssignmentType::Blocking)
        return "blocking";
    else if (type == AssignmentType::NonBlocking)
        return "non-blocking";
    else
        return "undefined";
}

std::string port_dir_to_str(PortDirection direction) {
    if (direction == PortDirection::In) {
        return "input";
    } else if (direction == PortDirection::Out) {
        return "output";
    } else {
        return "inout";
    }
}

bool is_valid_verilog(const std::string &src) {
    // we first output to a temp src
    std::string pathname = fs::temp_directory_path();
    std::string filename = fs::join(pathname, "src.sv");
    if (filename.empty()) throw std::runtime_error("unable to create temp file");
    std::ofstream f(filename);
    f << src;
    f.close();

    int status;

    // choose which parser to use
    // we use verilator first
    std::string verilator = fs::which("verilator");
    if (!verilator.empty()) {
        status =
            std::system(::format("{0} {1} --lint-only -Wno-fatal", verilator, filename).c_str());
        fs::remove(filename);
        return status == 0;
    }

    std::string iverilog = fs::which("iverilog");
    if (!iverilog.empty()) {
        std::string output_filename = fs::join(pathname, "out.a");
        status =
            std::system(::format("{0} {1} -o {2}", iverilog, filename, output_filename).c_str());
        fs::remove(filename);
        return status == 0;
    }

    fs::remove(filename);
    throw std::runtime_error("iverilog and verilator not found in the system");
}

bool is_valid_verilog(const std::map<std::string, std::string> &src) {
    std::string final_src;
    for (auto const &iter : src) {
        final_src.append(iter.second);
        final_src.append("\n");
    }
    return is_valid_verilog(final_src);
}

std::pair<uint32_t, uint32_t> compute_var_high_low(
    Var *root, const std::vector<std::pair<uint32_t, uint32_t>> &index) {
    // outer to inner
    // flatten the index
    auto const &var_sizes = root->size();
    std::vector<uint32_t> bases(var_sizes.size());
    uint32_t base = 1;
    for (int i = static_cast<int>(var_sizes.size()) - 1; i >= 0; i--) {
        bases[i] = base * root->var_width();
        base *= var_sizes[i];
    }

    uint32_t var_low = 0;
    uint32_t var_high = 0;
    uint32_t index_to_size = 0;
    uint64_t i = 0;
    while (i < index.size()) {
        auto const &[slice_high, slice_low] = index[i];
        if (slice_high > slice_low) {
            var_low += slice_low * bases[index_to_size] * root->var_width();
            var_high = var_low +
                       (slice_high - slice_low + 1) * bases[index_to_size] * root->var_width() - 1;
        } else if (slice_high == slice_low && index_to_size < var_sizes.size() &&
                   var_sizes[index_to_size] > 1) {
            var_low += slice_low * bases[index_to_size];
            var_high = var_low + (slice_high - slice_low + 1) * bases[index_to_size] - 1;
            index_to_size++;
        } else {
            break;
        }
        i++;
    }

    if (i < index.size()) {
        for (; i < index.size(); i++) {
            auto const &[slice_high, slice_low] = index[i];
            var_low += slice_low;
            var_high = var_low + (slice_high - slice_low);
        }
    }

    return {var_high, var_low};
}

std::string port_type_to_str(PortType type) {
    switch (type) {
        case PortType::Reset:
            return "reset";
        case PortType::Data:
            return "data";
        case PortType ::ClockEnable:
            return "clk_en";
        case PortType ::Clock:
            return "clk";
        case PortType ::AsyncReset:
            return "async_reset";
        default:
            throw std::runtime_error("unknown port type");
    }
}

std::string strip_newline(std::string &str) {
    std::string::size_type pos = 0;
    while ((pos = str.find('\n', pos) != std::string::npos)) str.erase(pos, 1);
    return str;
}

void remove_stmt_from_parent(const std::shared_ptr<Stmt> &stmt) {
    auto parent = stmt->parent();
    if (!parent) return;
    if (parent->ir_node_kind() == IRNodeKind::GeneratorKind) {
        auto p = dynamic_cast<Generator *>(parent);
        p->remove_stmt(stmt);
    } else {
        if (parent->ir_node_kind() != IRNodeKind::StmtKind) {
            throw StmtException("Internal error", {stmt.get()});
        }
        auto p_stmt = dynamic_cast<Stmt *>(parent);
        if (p_stmt->type() == StatementType::Switch) {
            auto p = dynamic_cast<SwitchStmt *>(p_stmt);
            if (!p)
                throw InternalException(
                    "stmt is not switch but is marked as StatementType::Switch");
            p->remove_stmt(stmt);
        } else if (p_stmt->type() == StatementType::If) {
            auto p = dynamic_cast<IfStmt *>(p_stmt);
            if (!p) throw InternalException("stmt is not if but is marked as StatementType::If");
            p->remove_stmt(stmt);
        } else {
            if (p_stmt->type() != StatementType::Block) {
                throw StmtException("Internal error", {stmt.get()});
            }
            auto p = dynamic_cast<StmtBlock *>(p_stmt);
            if (!p)
                throw InternalException(
                    "stmt is not block but is marked as StatementType::StatementType::Block");
            p->remove_stmt(stmt);
        }
    }
}

std::map<std::string, std::shared_ptr<Port>> get_port_from_mod_def(Generator *generator,
                                                                   const std::string &mod_def) {
    std::map<std::string, std::shared_ptr<Port>> result;
    std::unordered_set<std::string> ignore_list = {"logic", "reg", "wire"};
    std::regex re("(input|output)\\s?([\\w,\\s_$\\[\\]:])+", std::regex::ECMAScript);  // NOLINT
    std::smatch match;
    std::string::const_iterator iter = mod_def.cbegin();
    while (std::regex_search(iter, mod_def.end(), match, re)) {
        if (match.size() > 1) {
            std::string port_declaration = std::string(match[0].first, match[0].second);
            std::vector<std::string> const tokens = string::get_tokens(port_declaration, ", ");
            // the first one has to be either input or output
            if (tokens.size() < 2)
                throw std::runtime_error(::format("unable to parse {}", port_declaration));
            std::string input_type = tokens[0];
            PortDirection direction;
            if (input_type == "input")
                direction = PortDirection::In;
            else if (input_type == "output")
                direction = PortDirection::Out;
            else
                throw std::runtime_error(
                    ::format("{} has to be either input or output", input_type));
            // determine the reset
            uint32_t i = 1;
            uint32_t high = 0;
            uint32_t low = 0;
            while (i < tokens.size()) {
                auto token = tokens[i];
                if (token.empty()) {
                    i++;
                    continue;
                }
                if (token[0] == '[' && token[token.size() - 1] != ']') {
                    token.append(tokens[++i]);
                }
                if (token[0] == '[' && token[token.size() - 1] == ']') {
                    // determine the size
                    std::vector<std::string> size_tokens = string::get_tokens(token, "[:] ");
                    if (size_tokens.size() != 2)
                        throw std::runtime_error(::format("unable to parse {}", token));
                    high = std::stoi(size_tokens[0]);
                    low = std::stoi(size_tokens[1]);
                    if (high < low)
                        throw std::runtime_error(
                            ::format("only [hi:lo] is supported, got [{}:{}]", high, low));
                } else {
                    if (token[0] == '[')
                        throw std::runtime_error(::format("unable to parse {}", port_declaration));
                    if (token == "input") {
                        direction = PortDirection::In;
                        i++;
                        continue;
                    } else if (token == "output") {
                        direction = PortDirection::Out;
                        i++;
                        continue;
                    } else if (token == "inout") {
                        direction = PortDirection ::InOut;
                        i++;
                        continue;
                    }
                    const auto &port_name = token;
                    uint32_t width = high - low + 1;
                    auto p = std::make_shared<Port>(generator, direction, port_name, width, 1,
                                                    PortType::Data, false);
                    result.emplace(port_name, p);
                }

                i++;
            }
        }
        iter = match[0].second;
    }
    return result;
}


std::vector<std::vector<uint32_t>> get_flatten_slices(Var *var, bool ignore_size_1) {
    uint32_t num_slices = var->width() / var->var_width();
    if (num_slices == 1 && ignore_size_1) return {};
    std::vector<std::vector<uint32_t>> result;

    std::vector<uint32_t> sizes = std::vector<uint32_t>(var->size().begin(), var->size().end());
    std::reverse(sizes.begin(), sizes.end());
    for (uint32_t i = 0; i < num_slices; i++) {
        std::vector<uint32_t> slice;
        slice.reserve(sizes.size());
        uint32_t value = i;
        for (auto l: sizes) {
            slice.emplace_back(value % l);
            value /= l;
        }
        std::reverse(slice.begin(), slice.end());
        result.emplace_back(slice);
    }
    return result;
}

std::map<std::string, std::shared_ptr<Port>> get_port_from_verilog(Generator *generator,
                                                                   const std::string &src,
                                                                   const std::string &top_name) {
    std::regex re("module\\s+([\\w_$]+)[\\w\\W]*?endmodule", std::regex::ECMAScript);  // NOLINT
    std::smatch match;
    std::string::const_iterator iter = src.cbegin();
    std::string module_def;
    while (std::regex_search(iter, src.end(), match, re)) {
        if (match.size() > 1) {
            std::string module_name = std::string(match[1].first, match[1].second);
            if (module_name == top_name) {
                module_def = std::string(match[0].first, match[0].second);
                break;
            }
        }
        iter = match[0].second;
    }
    if (module_def.empty())
        throw std::runtime_error(::format("Unable to find {} definition", top_name));
    return get_port_from_mod_def(generator, module_def);
}

std::vector<std::string> line_wrap(const std::string &text, uint32_t line_width) {
    // adapted from https://www.rosettacode.org/wiki/Word_wrap#C.2B.2B
    std::istringstream words(text);
    std::vector<std::string> result;
    std::string word;
    std::string line;

    if (words >> word) {
        line.append(word);
        size_t space_left = line_width - word.length();
        while (words >> word) {
            if (space_left < word.length() + 1) {
                result.emplace_back(line);
                line = word;
                space_left = line_width - word.length();
            } else {
                line.append(" ").append(word);
                space_left -= word.length() + 1;
            }
        }
    }
    result.emplace_back(line);
    return result;
}

// not interested in this coverage since it's just color conversion
// LCOV_EXCL_START
namespace color {
Color hsv_to_rgb(double h, double s, double v) {
    auto h_i = static_cast<int>(h * 6);
    auto f = h * 6 - h_i;
    auto p = v * (1 - s);
    auto q = v * (1 - f * s);
    auto t = v * (1 - (1 - f) * s);
    double r_, g_, b_;

    switch (h_i) {
        case 0: {
            r_ = v;
            g_ = t;
            b_ = p;
            break;
        }
        case 1: {
            r_ = q;
            g_ = v;
            b_ = p;
            break;
        }
        case 2: {
            r_ = p;
            g_ = v;
            b_ = t;
            break;
        }
        case 3: {
            r_ = p;
            g_ = q;
            b_ = v;
            break;
        }
        case 4: {
            r_ = t;
            g_ = p;
            b_ = v;
            break;
        }
        case 5: {
            r_ = v;
            g_ = p;
            b_ = q;
            break;
        }
        default:
            throw std::runtime_error("HSV H is larger than 1");
    }
    auto r = static_cast<unsigned char>(r_ * 255);
    auto g = static_cast<unsigned char>(g_ * 255);
    auto b = static_cast<unsigned char>(b_ * 255);
    return {r, g, b};
}
}  // namespace color
// LCOV_EXCL_STOP

namespace fs {
std::string which(const std::string &name) {
    // windows is more picky
    std::string env_path;
#ifdef _WIN32
    char *path_var;
    size_t len;
    auto err = _dupenv_s(&path_var, &len, "PATH");
    if (err) {
        env_path = "";
    }
    env_path = std::string(path_var);
    free(path_var);
    path_var = nullptr;
#else
    env_path = std::getenv("PATH");
#endif
    // tokenize it base on either : or ;
    auto tokens = string::get_tokens(env_path, ";:");
    for (auto const &dir : tokens) {
        auto new_path = fs::join(dir, name);
        if (exists(new_path)) {
            return new_path;
        }
    }
    return "";
}

bool exists(const std::string &filename) {
#if defined(INCLUDE_FILESYSTEM)
    namespace fs = std::filesystem;
    return fs::exists(filename);
#else
    std::ifstream in(filename);
    return in.good();
#endif
}

std::string join(const std::string &path1, const std::string &path2) {
#if defined(INCLUDE_FILESYSTEM)
    namespace fs = std::filesystem;
    fs::path p1 = path1;
    fs::path p2 = path2;
    return p1 / p2;
#else
    return path1 + "/" + path2;
#endif
}

bool remove(const std::string &filename) {
#if defined(INCLUDE_FILESYSTEM)
    namespace fs = std::filesystem;
    return fs::remove(filename);
#else
    return std::remove(filename.c_str());
#endif
}

std::string temp_directory_path() {
#if defined(INCLUDE_FILESYSTEM)
    namespace fs = std::filesystem;
    return fs::temp_directory_path();
#else
    return "/tmp";
#endif
}

std::string get_ext(const std::string &filename) {
#if defined(INCLUDE_FILESYSTEM)
    std::filesystem::path path(filename);
    return path.extension().string();
#else
    auto idx = filename.rfind('.');
    if (idx != std::string::npos)
        return filename.substr(idx);
    else
        return "";
#endif
}

std::string abspath(const std::string &filename) {
#if defined(INCLUDE_FILESYSTEM)
    return std::filesystem::absolute(filename);
#else
#if defined(NO_FS_HAS_REALPATH)
    auto path = realpath(filename.c_str(), nullptr);
#else
    auto path = _fullpath(NULL, filename.c_str(), 120);
#endif
    return std::string(path);
#endif
}

std::string basename(const std::string &filename) {
#if defined(INCLUDE_FILESYSTEM)
    std::filesystem::path path(filename);
    return path.filename();
#else
    auto tokens = string::get_tokens(filename, "/\\");
    return tokens.back();
#endif
}

char separator() {
#ifdef _WIN32
    return '\\';
#else
    return '/';
#endif
}

}  // namespace fs

namespace string {
// trim function copied from https://stackoverflow.com/a/217605
// trim from start (in place)
static inline void ltrim(std::string &s) {
    s.erase(s.begin(), std::find_if(s.begin(), s.end(), [](int ch) { return !std::isspace(ch); }));
}

// trim from end (in place)
static inline void rtrim(std::string &s) {
    s.erase(std::find_if(s.rbegin(), s.rend(), [](int ch) { return !std::isspace(ch); }).base(),
            s.end());
}

// trim from both ends (in place)
void trim(std::string &s) {
    ltrim(s);
    rtrim(s);
}

std::vector<std::string> get_tokens(const std::string &line, const std::string &delimiter) {
    std::vector<std::string> tokens;
    size_t prev = 0, pos = 0;
    std::string token;
    // copied from https://stackoverflow.com/a/7621814
    while ((pos = line.find_first_of(delimiter, prev)) != std::string::npos) {
        if (pos > prev) {
            tokens.emplace_back(line.substr(prev, pos - prev));
        }
        prev = pos + 1;
    }
    if (prev < line.length()) tokens.emplace_back(line.substr(prev, std::string::npos));
    // remove empty ones
    std::vector<std::string> result;
    result.reserve(tokens.size());
    for (auto const &t : tokens)
        if (!t.empty()) result.emplace_back(t);
    return result;
}

}  // namespace string

}  // namespace kratos
