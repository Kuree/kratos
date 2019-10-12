#ifndef KRATOS_DB_HH
#define KRATOS_DB_HH

#include "sqlite_orm/sqlite_orm.h"

namespace kratos {

// table row definitions
struct MetaData {
    std::string name;
    std::string value;
};

struct BreakPoint {
    uint32_t id;
    std::string filename;
    uint32_t line_num;
    std::unique_ptr<int> handle;
};

struct Variable {
    int id;
    std::unique_ptr<int> handle;
    std::string value;
    std::string name;
    bool is_var;
    bool is_context = false;
};

struct Connection {
    std::unique_ptr<int> handle_from;
    std::string var_from;
    std::unique_ptr<int> handle_to;
    std::string var_to;
};

struct Hierarchy {
    std::unique_ptr<int> parent_handle;
    std::string child;
};

struct ContextVariable {
    std::unique_ptr<uint32_t> breakpoint_id;
    std::unique_ptr<int> variable_id;
    std::string name;
};

struct Instance {
    int id;
    std::string handle_name;
};

// initialize the database
auto inline init_storage(const std::string &filename) {
    using namespace sqlite_orm;
    auto storage = make_storage(
        filename,
        make_table("metadata", make_column("name", &MetaData::name),
                   make_column("value", &MetaData::value)),
        make_table("breakpoint", make_column("id", &BreakPoint::id, primary_key()),
                   make_column("filename", &BreakPoint::filename),
                   make_column("line_num", &BreakPoint::line_num),
                   make_column("handle", &BreakPoint::handle),
                   foreign_key(&BreakPoint::handle).references(&Instance::id)),
        make_table("variable", make_column("id", &Variable::id, primary_key()),
                   make_column("handle", &Variable::handle), make_column("value", &Variable::value),
                   make_column("name", &Variable::name),
                   make_column("is_var", &Variable::is_var),
                   make_column("is_context", &Variable::is_context),
                   foreign_key(&Variable::handle).references(&Instance::id)),
        make_table("connection", make_column("handle_from", &Connection::handle_from),
                   make_column("var_from", &Connection::var_from),
                   make_column("handle_to", &Connection::handle_to),
                   make_column("var_to", &Connection::var_to),
                   foreign_key(&Connection::handle_from).references(&Instance::id),
                   foreign_key(&Connection::handle_to).references(&Instance::id)),
        make_table("hierarchy", make_column("parent_handle", &Hierarchy::parent_handle),
                   make_column("child", &Hierarchy::child),
                   foreign_key(&Hierarchy::parent_handle).references(&Instance::id)),
        make_table("context", make_column("variable_id", &ContextVariable::variable_id),
                   make_column("breakpoint_id", &ContextVariable::breakpoint_id),
                   make_column("name", &ContextVariable::name),
                   foreign_key(&ContextVariable::variable_id).references(&Variable::id),
                   foreign_key(&ContextVariable::breakpoint_id).references(&BreakPoint::id)),
        make_table("instance", make_column("id", &Instance::id, primary_key()),
                   make_column("handle_name", &Instance::handle_name)));
    return storage;
}

}  // namespace kratos

#endif  // KRATOS_DB_HH
