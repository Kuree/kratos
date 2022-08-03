module mod (
  output logic [3:0] c
);

logic [3:0] a;
logic [3:0] a_0;
logic [3:0] a_1;
logic [3:0] a_2;
logic [3:0] a_3;
logic [3:0] a_4;
logic [3:0] a_5;
logic [3:0] a_6;
logic [3:0] b;
logic [3:0] b_0;
logic [3:0] b_1;
logic [3:0] b_2;
logic [3:0] b_3;
logic [3:0] b_4;
logic [3:0] c_0;
assign a = a_6;
assign b = b_4;
assign c = c_0;
always_comb begin
  a_0 = 4'h1;
  a_1 = 4'h2;
  a_2 = b + a_1;
  a_3 = (a_1 == 4'h2) ? a_2: a_1;
  b_0 = 4'h2;
  b_1 = 4'h3;
  b_2 = 4'h4;
  a_4 = 4'h5;
  b_3 = (a_3 == 4'h4) ? b_1: b_2;
  a_5 = (a_3 == 4'h4) ? a_3: a_4;
  b_4 = (a_3 == 4'h3) ? b_0: b_3;
  a_6 = (a_3 == 4'h3) ? a_3: a_5;
  c_0 = a_6;
end
endmodule   // mod

