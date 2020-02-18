#ifndef KRATOS_LIB_HH
#define KRATOS_LIB_HH

#include "generator.hh"

namespace kratos::asic {

class SRAM: public std::enable_shared_from_this<SRAM> {
public:
    SRAM(Context *, const std::string &sram_name);
    SRAM(Context *, const std::string &sram_name, uint16_t addr_width, uint16_t data_width);

    virtual uint32_t num_ports() { return 0; };

    std::shared_ptr<Port> clock() { return clk_; }
    uint16_t addr_width() { return addr_width_; };
    uint16_t data_width() { return data_width_; }

    std::string clock_name() const { return clk_->name; }
    void set_clock_name(const std::string &name) { clk_->name = name; }

    Generator* generator() const { return generator_; }

    [[nodiscard]] uint32_t capacity() const;

protected:
    std::shared_ptr<Port> clk_ = nullptr;
    std::shared_ptr<Var> data_ = nullptr;
    uint16_t addr_width_ = 11;
    uint16_t data_width_ = 64;

    Generator *generator_;

private:
    void init_sram();
    void init_clock();

    std::string clock_name_ = "CLK";
};

class SinglePortSRAM : public SRAM {
public:
    SinglePortSRAM(Context *context, const std::string &stub_name, uint16_t addr_width,
                   uint16_t data_width, bool partial_write);

    SinglePortSRAM(Context *context, const std::string &stub_name, uint32_t capacity,
                   std::shared_ptr<SinglePortSRAM> &basis);

    uint32_t num_ports() override { return 1; };

    std::shared_ptr<Port> output_data() { return output_data_; }
    std::shared_ptr<Port> chip_enable() { return chip_enable_; }
    std::shared_ptr<Port> write_enable() { return write_enable_; }
    std::shared_ptr<Port> addr() { return addr_; }
    std::shared_ptr<Port> input_data() { return input_data_; }
    std::shared_ptr<Port> partial_write_mask() { return partial_write_mask_; }

    // get names

    std::string output_data_name() const { return output_data_->name; }
    std::string chip_enable_name() const { return chip_enable_->name; }
    std::string write_enable_name() const { return write_enable_->name; }
    std::string addr_name() const { return addr_->name; }
    std::string input_data_name() const { return input_data_->name; }
    std::string partial_write_mask_name() const {
        return partial_write_ ? partial_write_mask_->name : "";
    }

    // set names
    void set_output_data_name(const std::string &name) { output_data_->name = name; }
    void set_chip_enable_name(const std::string &name) { chip_enable_->name = name; }
    void set_write_enable_name(const std::string &name) { write_enable_->name = name; }
    void set_addr_name(const std::string &name) { addr_->name = name; }
    void set_input_data_name(const std::string &name) { input_data_->name = name; }
    void set_partial_write_mask_name(const std::string &name) {
        if (partial_write_mask_) partial_write_mask_->name = name;
    }

    bool partial_write() const { return partial_write_; }

private:
    // defaults
    const std::string clock_name_ = "CLK";
    const std::string output_data_name_ = "Q";
    const std::string chip_enable_name_ = "CEB";
    const std::string write_enable_name_ = "WEB";
    const std::string addr_name_ = "A";
    const std::string input_data_name_ = "D";
    const std::string partial_write_mask_name_ = "BWEB";

    bool partial_write_;

    // ports
    std::shared_ptr<Port> output_data_;
    std::shared_ptr<Port> chip_enable_;
    std::shared_ptr<Port> write_enable_;
    std::shared_ptr<Port> addr_;
    std::shared_ptr<Port> input_data_;
    std::shared_ptr<Port> partial_write_mask_;
};

}  // namespace kratos

#endif  // KRATOS_LIB_HH
