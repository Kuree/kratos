#ifndef KRATOS_EXCEPT_HH
#define KRATOS_EXCEPT_HH

#include <vector>
#include "context.hh"

namespace kratos {

class VarException : public std::runtime_error {
public:
    VarException(const std::string &message, const std::vector<const IRNode *> &nodes) noexcept;
    // avoid implicit conversion
    VarException(const std::string &message, std::vector<const Var *>::iterator begin,
                 std::vector<const Var *>::iterator end) noexcept;
};

class StmtException : public std::runtime_error {
public:
    StmtException(const std::string &message, const std::vector<IRNode *> &nodes) noexcept;
    StmtException(const std::string &message, const std::vector<Stmt*>::const_iterator &begin,
        const std::vector<Stmt*>::const_iterator &end) noexcept;
private:
    template <class T>
    void print_nodes(T begin, T end) noexcept;
};

class GeneratorException : public std::runtime_error {
public:
    GeneratorException(const std::string &message, const std::vector<IRNode *> &nodes) noexcept;
};

class InternalException : public std::runtime_error {
public:
    explicit InternalException(const std::string &message) noexcept;
};

class UserException : public std::runtime_error {
public:
    explicit UserException(const std::string &message) noexcept;
};

void print_ast_node(const IRNode *node);

template <typename T>
void print_nodes(const std::vector<T> &nodes) {
    for (auto const &node : nodes) {
        if (node)
            print_ast_node(node);
    }
}

}  // namespace kratos

#endif  // KRATOS_EXCEPT_HH
