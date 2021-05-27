#ifndef KRATOS_EVENT_HH
#define KRATOS_EVENT_HH

#include "stmt.hh"

namespace kratos {

enum class EventActionType : uint64_t { none = 0, start = 1 << 0, end = 1 << 1 };
inline EventActionType operator|=(EventActionType lhs, EventActionType rhs) {
    return static_cast<EventActionType>(
        static_cast<std::underlying_type<EventActionType>::type>(lhs) |
        static_cast<std::underlying_type<EventActionType>::type>(rhs));
}

// we add wrappers around the event statement
class EventTracingStmtWrapper : public EventTracingStmt {
public:
    using EventTracingStmt::EventTracingStmt;

    // other useful methods related to transaction events etc
    inline std::shared_ptr<EventTracingStmtWrapper> terminates() {
        action_type_ |= EventActionType::end;
        return as<EventTracingStmtWrapper>();
    }
    inline std::shared_ptr<EventTracingStmtWrapper> belongs(const std::string &transaction_name) {
        transaction_ = transaction_name;
        return as<EventTracingStmtWrapper>();
    }
    inline std::shared_ptr<EventTracingStmtWrapper> starts() {
        action_type_ |= EventActionType::start;
        return as<EventTracingStmtWrapper>();
    }

private:
    std::string transaction_;
    EventActionType action_type_ = EventActionType::none;
};

class Event {
    explicit Event(std::string event_name) : event_name_(std::move(event_name)) {}
    std::shared_ptr<EventTracingStmtWrapper> fire(
        const std::map<std::string, const Var *> &fields);

private:
    std::string event_name_;
};

std::unordered_map<std::shared_ptr<EventTracingStmt>, std::shared_ptr<Var>>
extract_event_fire_condition(Generator *top);

void remove_event_stmts(Generator *top);

}  // namespace kratos

#endif  // KRATOS_EVENT_HH
