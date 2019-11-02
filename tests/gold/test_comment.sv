module mod (
  // Input port
  input logic in,
  output logic out,
  output logic out2,
  output logic out3
);

// variable comment
logic v;
assign out2 = v;
always_comb begin
  // Another comment
  out3 = in;
end
// This is a comment
mod1 child (
  .in(in),
  .out(out)
);

endmodule   // mod

module mod1 (
  input logic in,
  output logic out
);

assign out = in;
endmodule   // mod1

