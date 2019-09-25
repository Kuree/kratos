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
    std::string handle;
};

struct Variable {
    std::string handle;
    std::string var;
    std::string front_var;
    uint32_t array_size;
    uint32_t type;
    bool is_var;
};

struct Connection {
    std::string handle_from;
    std::string var_from;
    std::string handle_to;
    std::string var_to;
};

struct Hierarchy {
    std::string parent_handle;
    std::string child;
};

struct ContextVariable {
    std::string name;
    std::string value;
    bool is_var;
    uint32_t id;
};

// this is the database schema
// TABLE metadata
// NAME, VALUE
// this is essentially a key-value storage
// TABLE breakpoint
// BREAK_POINT_ID filename, line_number, handle
// this is mapping a breakpoint id to a line in the front-end code
// TABLE variables
// generator_handle, var, front_var, array_size, type
// generator_handle + var is the var handle name, front_var comes from the variable name
// array_size and type will be used later to visualize the array

// TABLE connection
// all the variables are the in the RTL form. You can cross search the variable
// to find out the python variable name, if any

// TABLE hierarchy. the parent uses full handle name, the child is the instance name
// you can make parent_handle.child to obtain the child handle name

// initialize the database
auto inline init_storage(const std::string &filename) {
    using namespace sqlite_orm;
    auto storage = make_storage(
        filename,
        make_table("metadata", make_column("name", &MetaData::name),
                   make_column("value", &MetaData::value)),
        make_table("breakpoint", make_column("id", &BreakPoint::id),
                   make_column("filename", &BreakPoint::filename),
                   make_column("line_num", &BreakPoint::line_num),
                   make_column("handle", &BreakPoint::handle)),
        make_table("variable", make_column("handle", &Variable::handle),
                   make_column("var", &Variable::var),
                   make_column("front_var", &Variable::front_var),
                   make_column("array_size", &Variable::array_size),
                   make_column("type", &Variable::type),
                   make_column("is_var", &Variable::is_var)),
        make_table("connection", make_column("handle_from", &Connection::handle_from),
                   make_column("var_from", &Connection::var_from),
                   make_column("handle_to", &Connection::handle_to),
                   make_column("var_to", &Connection::var_to)),
        make_table("hierarchy", make_column("parent_handle", &Hierarchy::parent_handle),
                   make_column("child", &Hierarchy::child)),
        make_table("context", make_column("name", &ContextVariable::name),
                   make_column("value", &ContextVariable::value),
                   make_column("is_var", &ContextVariable::is_var),
                   make_column("id", &ContextVariable::id)));
    return storage;
}

}  // namespace kratos

#endif  // KRATOS_DB_HH
