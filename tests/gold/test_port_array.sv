module mod (
  input logic [1:0] in [1:0],
  output logic [1:0] out1 [1:0],
  output logic [1:0] out2 [1:0]
);

assign out1 = in;
assign out2[0][0] = in[0][1];
assign out2[0][1] = in[0][0];
assign out2[1] = in[1];
endmodule   // mod

