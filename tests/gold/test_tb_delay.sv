module TOP (
);

logic   in;
logic   out;
mod dut (
  .in(in),
  .out(out)
);

initial begin
  #1 in = 1'h1;
end
endmodule   // TOP
