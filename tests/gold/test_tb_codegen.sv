module TOP (
);

logic   in;
logic   out;
mod dut (
  .in(in),
  .out(out)
);

initial begin
  in = 1'h1;
  assert (out == 1'h1);
  assert (dut.val == 1'h1);
end
endmodule   // TOP
