module mod (
  // Input port
  input logic  in,
  output logic  out,
  output logic  out2
);

// variable comment
logic   v;
assign out2 = v;
// This is a comment
mod1 child (
  .in(in),
  .out(out)
);

endmodule   // mod

module mod1 (
  input logic  in,
  output logic  out
);

assign out = in;
endmodule   // mod1

