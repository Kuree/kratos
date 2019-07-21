#include <regex>
#include "except.hh"
#include "expr.hh"
#include "fmt/format.h"
#include "generator.hh"
#include "port.hh"
#include "stmt.hh"

#include "slang/compilation/Compilation.h"
#include "slang/syntax/SyntaxTree.h"
#include "slang/text/SourceManager.h"

using fmt::format;

namespace kratos {

std::string ExprOpStr(ExprOp op) {
    switch (op) {
        case UInvert:
            return "~";
        case UMinus:
        case Minus:
            return "-";
        case UPlus:
        case Add:
            return "+";
        case Divide:
            return "/";
        case Multiply:
            return "*";
        case Mod:
            return "%";
        case LogicalShiftRight:
            return ">>";
        case SignedShiftRight:
            return ">>>";
        case ShiftLeft:
            return "<<";
        case Or:
            return "|";
        case And:
            return "&";
        case Xor:
            return "^";
        case LessThan:
            return "<";
        case GreaterThan:
            return ">";
        case LessEqThan:
            return "<=";
        case GreaterEqThan:
            return ">=";
        case Eq:
            return "==";
        case Neq:
            return "!=";
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
    slang::SourceManager source_manager;
    slang::Compilation compilation;
    auto tree = slang::SyntaxTree::fromText(src, source_manager);
    compilation.addSyntaxTree(tree);
    auto &diagnostics = compilation.getParseDiagnostics();
    return diagnostics.empty();
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
            p->remove_stmt(stmt);
        } else if (p_stmt->type() == StatementType::If) {
            auto p = dynamic_cast<IfStmt *>(p_stmt);
            p->remove_stmt(stmt);
        } else {
            if (p_stmt->type() != StatementType::Block) {
                throw StmtException("Internal error", {stmt.get()});
            }
            auto p = dynamic_cast<StmtBlock *>(p_stmt);
            p->remove_stmt(stmt);
        }
    }
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

std::map<std::string, std::shared_ptr<Port>> get_port_from_mod_def(Generator *generator,
                                                                   const std::string &mod_def) {
    std::map<std::string, std::shared_ptr<Port>> result;
    std::unordered_set<std::string> ignore_list = {"logic", "reg", "wire"};
    std::regex re("(input|output)\\s?([\\w,\\s_$\\[\\]:])+", std::regex::ECMAScript);  // NOLINT
    std::smatch match;
    ::string::const_iterator iter = mod_def.cbegin();
    while (std::regex_search(iter, mod_def.end(), match, re)) {
        if (match.size() > 1) {
            std::string port_declaration = std::string(match[0].first, match[0].second);
            std::vector<std::string> const tokens = get_tokens(port_declaration, ", ");
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
                    std::vector<std::string> size_tokens = get_tokens(token, "[:] ");
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
                    const auto &port_name = token;
                    uint32_t width = high - low + 1;
                    auto p = std::make_shared<Port>(generator, direction, port_name, width,
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

}