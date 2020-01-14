module mod (
  input logic [3:0] a [2:0][1:0],
  output logic [3:0] b [2:0][1:0]
);

assign b = a;
endmodule   // mod

module wrapper (
  input logic [3:0] a_0_0,
  input logic [3:0] a_0_1,
  input logic [3:0] a_1_0,
  input logic [3:0] a_1_1,
  input logic [3:0] a_2_0,
  input logic [3:0] a_2_1,
  output logic [3:0] b_0_0,
  output logic [3:0] b_0_1,
  output logic [3:0] b_1_0,
  output logic [3:0] b_1_1,
  output logic [3:0] b_2_0,
  output logic [3:0] b_2_1
);

logic [3:0] mod_a [2:0][1:0];
logic [3:0] mod_b [2:0][1:0];
assign mod_a[0][0] = a_0_0;
assign mod_a[0][1] = a_0_1;
assign mod_a[1][0] = a_1_0;
assign mod_a[1][1] = a_1_1;
assign mod_a[2][0] = a_2_0;
assign mod_a[2][1] = a_2_1;
assign b_0_0 = mod_b[0][0];
assign b_0_1 = mod_b[0][1];
assign b_1_0 = mod_b[1][0];
assign b_1_1 = mod_b[1][1];
assign b_2_0 = mod_b[2][0];
assign b_2_1 = mod_b[2][1];
mod mod (
  .a(mod_a),
  .b(mod_b)
);

endmodule   // wrapper

