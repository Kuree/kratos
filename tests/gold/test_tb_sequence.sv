module TOP (
);

logic clk;
logic in;
logic out;
property test_out;
  @(posedge clk) in == 1'h1 |-> ##1 out == 1'h1 |-> out == 1'h0;
endproperty
assert property (test_out);
mod dut (
  .clk(clk),
  .in(in),
  .out(out)
);

endmodule   // TOP

module mod (
  input logic clk,
  input logic in,
  output logic out
);

logic val;
assign out = in;
assign val = in;
endmodule   // mod

