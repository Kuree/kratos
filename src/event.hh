#ifndef KRATOS_EVENT_HH
#define KRATOS_EVENT_HH

#include "stmt.hh"

namespace kratos {

class Transaction {
public:
    // basically a wrapper around string
    // the tracker stuff is done in the generated SV or done in hgdb
    std::string name;

    explicit Transaction(std::string name) : name(std::move(name)) {}
};

class Event {
public:
    explicit Event(std::string event_name) : event_name_(std::move(event_name)) {}
    std::shared_ptr<EventTracingStmt> fire(
        const std::map<std::string, std::shared_ptr<Var>> &fields);

private:
    std::string event_name_;
};

// actual information used for codegen and other debug info
struct EventInfo {
    std::string name;
    std::string transaction;
    bool combinational;
    EventActionType type;
    std::map<std::string, std::shared_ptr<Var>> fields;
    // keep the raw stmt here in case we need to extract more
    // information
    std::shared_ptr<EventTracingStmt> stmt;
};

std::vector<EventInfo> extract_event_info(Generator *top);

void remove_event_stmts(Generator *top);

}  // namespace kratos

#endif  // KRATOS_EVENT_HH
