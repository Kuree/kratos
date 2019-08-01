module mod (
  input logic  in,
  output logic [1:0] out
);

logic   child_out;
assign out[0] = child_out;
assign out[1] = in;
mod1 child (
  .in(1'h0),
  .out(child_out)
);

endmodule   // mod

module mod1 (
  input logic  in,
  output logic  out
);

assign out = in;
endmodule   // mod1

