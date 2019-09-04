module TOP (
);

logic   clk;
logic   in;
logic   out;
mod dut (
  .in(in),
  .out(out)
);

property test_out;
  @(posedge clk) in == 1'h1 |-> ##1 out == 1'h1 |-> out == 1'h0;
endproperty
assert property (test_out);
endmodule   // TOP
