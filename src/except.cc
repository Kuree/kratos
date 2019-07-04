#include "except.hh"
#include <filesystem>
#include <fstream>
#include <iostream>
#include "expr.hh"

constexpr char RED[] = "\033[91m";
constexpr char GREEN[] = "\033[92m";
constexpr char ENDC[] = "\033[0m";
constexpr uint32_t CODE_RANGE = 2;

namespace fs = std::filesystem;

VarException::VarException(const std::string& message, const std::vector<Var*>& vars) noexcept
    : std::runtime_error(message) {
    // we only support linux for now
#ifdef __linux__
    for (auto const& var : vars) {
        if (!var->fn_name_ln.empty()) {
            for (auto const& [filename, line_number] : var->fn_name_ln) {
                if (fs::exists(filename)) {
                    uint32_t line_count = 0;
                    std::string line;
                    std::cerr << filename << std::endl;
                    std::ifstream file(filename);
                    while (std::getline(file, line)) {
                        line_count++;
                        if (line_count == line_number) {
                            std::cerr << RED << ">" << line << ENDC << std::endl;
                        } else if (line_count >= line_number - CODE_RANGE &&
                                   line_count <= line_number + CODE_RANGE) {
                            std::cerr << GREEN << " " << line << ENDC << std::endl;
                        }
                    }
                }
            }
        }
    }
#endif
}
