module child #(parameter P2 = 4'h2)
(
  input logic [P2-1:0] in,
  output logic [P2-1:0] out
);

assign out = in;
endmodule   // child

module parent #(parameter P = 4'h2)
(
);

logic  [P-1:0] in;
logic  [P-1:0] mod_out;
logic  [P-1:0] out;
assign out = mod_out;
child #(
  .P2(P)) mod (
  .in(in),
  .out(mod_out)
);

endmodule   // parent

