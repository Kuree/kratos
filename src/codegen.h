#ifndef KRATOS_CODEGEN_H
#define KRATOS_CODEGEN_H

#include "context.hh"

class VerilogModule {
public:
    explicit VerilogModule(Generator *generator);

    const std::map<std::string, std::string> &verilog_src() const { return verilog_src_; }

private:
    std::map<std::string, std::string> verilog_src_;
};

#endif  //KRATOS_CODEGEN_H
