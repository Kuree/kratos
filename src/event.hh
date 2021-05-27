#ifndef KRATOS_EVENT_HH
#define KRATOS_EVENT_HH

#include "stmt.hh"

namespace kratos {

class Event {
public:
    explicit Event(std::string event_name) : event_name_(std::move(event_name)) {}
    std::shared_ptr<EventTracingStmt> fire(
        const std::map<std::string, std::shared_ptr<Var>> &fields);

private:
    std::string event_name_;
};

std::unordered_map<std::shared_ptr<EventTracingStmt>, std::shared_ptr<Var>>
extract_event_fire_condition(Generator *top);

void remove_event_stmts(Generator *top);

}  // namespace kratos

#endif  // KRATOS_EVENT_HH
