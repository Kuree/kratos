#include "lib.hh"

#include <fmt/format.h>

#include <cmath>

#include "except.hh"
#include "stmt.hh"
#include "util.hh"

using fmt::format;

namespace kratos::asic {

SRAM::SRAM(Context *context, const std::string &sram_name) : Generator(context, sram_name) {
    init_clock();
}

SRAM::SRAM(kratos::Context *context, const std::string &sram_name, uint16_t addr_width,
           uint16_t data_width)
    : Generator(context, sram_name), addr_width_(addr_width), data_width_(data_width) {
    init_sram();
}

uint32_t SRAM::capacity() const { return (1u << addr_width_) * data_width_; }

void SRAM::init_clock() {
    // clock
    clk_ = port(PortDirection::In, clock_name_, 1, 1, PortType::Clock, false).as<Port>();
}

void SRAM::init_sram() {
    init_clock();
    // register array
    data_ = var("data_array", data_width(), 1u << addr_width(), false).shared_from_this();
    data_->set_is_packed(false);
}

SinglePortSRAM::SinglePortSRAM(kratos::Context *context, const std::string &stub_name,
                               uint16_t addr_width, uint16_t data_width, bool partial_write)
    : SRAM(context, stub_name, addr_width, data_width), partial_write_(partial_write) {
    // generate ports
    output_data_ = port(PortDirection::Out, output_data_name_, data_width).as<Port>();
    chip_enable_ = port(PortDirection::In, chip_enable_name_, 1).as<Port>();
    write_enable_ = port(PortDirection::In, write_enable_name_, 1).as<Port>();
    addr_ = port(PortDirection::In, addr_name_, addr_width_).as<Port>();
    input_data_ = port(PortDirection::In, input_data_name_, data_width_).as<Port>();

    // optional partial write
    if (partial_write_) {
        partial_write_mask_ =
            port(PortDirection::In, partial_write_mask_name_, data_width_).as<Port>();
    }

    // generating the actual logic
    auto block = sequential();
    // no assignment type check here
    auto attr = std::make_shared<Attribute>();
    attr->type_str = "check_assignment";
    attr->value_str = "false";
    block->add_attribute(attr);
    block->add_condition({BlockEdgeType::Posedge, clk_});
    // active low for now
    auto chip_en_if = std::make_shared<IfStmt>(chip_enable_->r_not());
    // get data out
    chip_en_if->add_then_stmt(output_data_->assign((*data_)[addr_], AssignmentType::Blocking));
    // write enable
    // active low as well
    auto web_if = std::make_shared<IfStmt>(write_enable_->r_not());
    // partial write
    if (partial_write_) {
        for (uint32_t index = 0; index < data_width; index++) {
            // the mask is flipped as well
            auto set_if = std::make_shared<IfStmt>((*partial_write_mask_)[index].r_not());
            set_if->add_then_stmt(
                (*data_)[addr_][index].assign((*input_data_)[index], AssignmentType::Blocking));
            web_if->add_then_stmt(set_if);
        }
    } else {
        web_if->add_then_stmt((*data_)[addr_].assign(input_data_, AssignmentType::Blocking));
    }
    chip_en_if->add_then_stmt(web_if);
    block->add_stmt(chip_en_if);
}

SinglePortSRAM::SinglePortSRAM(kratos::Context *context, const std::string &stub_name,
                               uint32_t capacity, std::shared_ptr<SinglePortSRAM> &basis)
    : SRAM(context, stub_name), partial_write_(basis->partial_write_) {
    // compute the number of sram needed
    uint32_t basic_capacity = basis->capacity();
    if (capacity % basic_capacity) {
        throw UserException(
            ::format("Desired capacity {0} is not divisible by {1}", capacity, basic_capacity));
    }
    uint32_t num_sram = capacity / basic_capacity;
    uint32_t additional_addr_bits = std::ceil(std::log2(num_sram));
    addr_width_ = basis->addr_width_ + additional_addr_bits;
    data_width_ = basis->data_width_;
    set_clock_name(basis->clock_name());

    // copy the name from the basis
    // generate ports
    output_data_ =
        port(PortDirection::Out, basis->output_data_name(), basis->data_width()).as<Port>();
    chip_enable_ = port(PortDirection::In, basis->chip_enable_name(), 1).as<Port>();
    write_enable_ = port(PortDirection::In, basis->write_enable_name(), 1).as<Port>();
    addr_ = port(PortDirection::In, basis->addr_name(), addr_width_).as<Port>();
    input_data_ = port(PortDirection::In, basis->input_data_name(), data_width_).as<Port>();

    // optional partial write
    if (partial_write_) {
        partial_write_mask_ =
            port(PortDirection::In, partial_write_mask_name_, data_width_).as<Port>();
    }

    // memory select logic
    auto &mem_select = var("memory_select", additional_addr_bits);
    auto &addr_to_mem = var("addr_to_mem", basis->addr_width_);
    add_stmt(mem_select.assign((*addr_)[{addr_width_ - 1, basis->addr_width_}]));
    add_stmt(addr_to_mem.assign((*addr_)[{basis->addr_width_ - 1, 0}]));

    // one hot encoding for memory write enable array
    auto &web_array = var("WEB_array", num_sram);
    add_stmt(web_array.assign(util::mux(~(*write_enable_),
                                        ~(constant(1, num_sram) << mem_select.extend(num_sram)),
                                        ~(constant(0, num_sram)))));

    auto &output_select = var("output_select", additional_addr_bits);
    auto seq = sequential();
    seq->add_condition({BlockEdgeType::Posedge, clock()});
    auto ceb_if = std::make_shared<IfStmt>(chip_enable_->r_not());
    auto web_if = std::make_shared<IfStmt>(write_enable_);
    web_if->add_then_stmt(output_select.assign(mem_select));
    ceb_if->add_then_stmt(web_if);
    seq->add_stmt(ceb_if);

    // output array
    // num_sram array seems to be wrong
    auto &Q_array = var("Q_array", data_width_, num_sram);
    Q_array.set_is_packed(false);
    add_stmt(output_data_->assign(Q_array[output_select.shared_from_this()]));

    // generate a list of srams
    for (uint32_t i = 0; i < num_sram; i++) {
        // if it's the first one, use the basis, the rest can use the clone
        auto gen = i ? basis->clone() : basis;
        add_child_generator(::format("SRAM_{0}", i), gen);
        // wiring ports
        auto clk = gen->get_port(basis->clock()->name);
        add_stmt(clk->assign(clk_));
        add_stmt(gen->get_port(basis->addr_name())->assign(addr_to_mem));
        add_stmt(gen->get_port(basis->chip_enable_name())->assign(chip_enable_));
        add_stmt(gen->get_port(basis->write_enable_name())->assign(web_array[i]));
        add_stmt(gen->get_port(basis->input_data_name())->assign(input_data_));
        add_stmt(Q_array[i].assign(gen->get_port(basis->output_data_name())));
        if (partial_write_) {
            add_stmt(gen->get_port(partial_write_mask_name())->assign(partial_write_mask_));
        }
    }
}
}  // namespace kratos::asic