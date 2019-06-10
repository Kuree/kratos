#ifndef DUSK_PORT_HH
#define DUSK_PORT_HH

#include <set>
#include <string>
#include <vector>

// forward declaration
struct PortSlice;

// undefined port direction will be determined at run time
enum class PortDirection { In, Out, Undefined };

enum class PortType { Data, Clock, AsyncReset, Reset, ClockEnable, Const };

struct Port {
public:
    PortDirection direction;
    PortType type;

    std::string name;

    uint32_t width;

    Port(PortDirection direction, std::string name, uint32_t width)
        : direction(direction), type(PortType::Data), name(std::move(name)), width(width) {}

    Port(PortDirection direction, std::string name, uint32_t width, PortType type);

    PortSlice operator[](std::tuple<uint32_t, uint32_t> slice);
    PortSlice operator[](uint32_t bit);

    friend bool operator<(const Port &left, const Port &right);
};

struct ConstPort : public Port {
public:
    uint64_t value;
    ConstPort(uint64_t value, uint32_t width);

    ConstPort(PortDirection, std::string, uint32_t) = delete;
    ConstPort(PortDirection, std::string, uint32_t, PortType) = delete;
};

struct PortSlice {
public:
    Port *parent = nullptr;
    uint32_t low = 0;
    uint32_t high = 0;
};

#endif  // DUSK_PORT_HH
