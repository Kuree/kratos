module mod1 (
  input logic in,
  output logic out
);

assign out = in;
endmodule   // mod1

module top (
  input logic in,
  output logic out
);

mod1 pass (
  .in(in),
  .out(out)
);

endmodule   // top

