module test (
  input logic  in,
  output logic  out
);

assign out = in;
endmodule   // test

module top (
  input logic  in,
  output logic  out
);

test pass (
  .in(in),
  .out(out)
);

endmodule   // top

