module mod2 (
  input logic  in,
  output logic  out
);

logic   mod1_in;
logic   mod3_in;
assign mod1_in = in;
assign mod3_in = in;
always_comb begin
  out = mod1_in + mod3_in;
end
endmodule   // mod2

