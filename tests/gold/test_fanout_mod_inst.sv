module mod1 (
  input logic in,
  output logic out
);

assign out = in;
endmodule   // mod1

module mod2 (
  input logic in,
  output logic out
);

logic mod1_out;
logic mod3_out;
always_comb begin
  out = mod1_out + mod3_out;
end
mod1 mod1 (
  .in(in),
  .out(mod1_out)
);

mod1 mod3 (
  .in(in),
  .out(mod3_out)
);

endmodule   // mod2

