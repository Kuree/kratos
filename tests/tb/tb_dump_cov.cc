// verilator -cc --exe --coverage mod.sv tb_dump_cov.cc
#include "Vmod.h"
#include "verilated.h"

int main(int argc, char **argv) {
    Vmod tb;

    tb.clk = 0;
    tb.eval();

    for (int i = 0; i < 4; i++) {
        tb.in = i;
        tb.clk = 1;
        tb.eval();
        tb.clk = 0;
        tb.eval();
    }
    tb.final();
    VerilatedCov::write("cov.dat");

    exit(EXIT_SUCCESS);
}
