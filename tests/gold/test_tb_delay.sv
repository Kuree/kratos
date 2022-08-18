module TOP (
);

logic in;
logic out;
mod dut (
  .in(in),
  .out(out)
);

initial begin
  #1 in = 1'h1;
end
endmodule   // TOP

module mod (
  input logic in,
  output logic out
);

logic val;
assign out = in;
assign val = in;
endmodule   // mod

