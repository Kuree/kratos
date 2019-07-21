#include "except.hh"
#include <cstring>
#include <fstream>
#include <iostream>
#include "expr.hh"
#include "stmt.hh"
#include "util.hh"

constexpr char RED[] = "\033[91m";
constexpr char GREEN[] = "\033[92m";
constexpr char BLUE[] = "\033[94m";
constexpr char ENDC[] = "\033[0m";
constexpr uint32_t CODE_RANGE = 2;
constexpr uint32_t LINE_WIDTH = 80;

namespace kratos {

std::string inline blue_line() {
    std::string result;
    result.append(BLUE);

    for (uint32_t i = 0; i < LINE_WIDTH; i++) result.append("-");

    result.append(ENDC);
    return result;
}

void inline print_ast_node(const IRNode* node) {
    // we only support unix for now
#ifdef __unix__
    if (!node->fn_name_ln.empty()) {
        // print out a blue line
        for (auto const& [filename, line_number] : node->fn_name_ln) {
            if (fs::exists(filename)) {
                uint32_t line_count = 0;
                std::string line;
                std::cerr << filename << std::endl;
                std::ifstream file(filename);
                std::cerr << blue_line() << std::endl;
                while (std::getline(file, line)) {
                    line_count++;
                    if (line_count == line_number) {
                        std::cerr << RED << ">" << line << ENDC << std::endl;
                    } else if (line_count >= line_number - CODE_RANGE &&
                               line_count <= line_number + CODE_RANGE) {
                        std::cerr << GREEN << " " << line << ENDC << std::endl;
                    }
                }
                std::cerr << blue_line() << std::endl;
            }
        }
    }
#else
    (void)(node);
    (void)(RED);
    (void)(GREEN);
    (void)(CODE_RANGE);
#endif
}

VarException::VarException(const std::string& message, const std::vector<Var*>& vars) noexcept
    : std::runtime_error(message) {
    for (auto const& var : vars) {
        print_ast_node(var);
    }
}

StmtException::StmtException(const std::string& message, const std::vector<Stmt*>& stmts) noexcept
    : std::runtime_error(message) {
    for (auto const& stmt : stmts) {
        print_ast_node(stmt);
    }
}

}