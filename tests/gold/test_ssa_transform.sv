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
assign a_0 = 4'h1;
assign a_1 = 4'h2;
assign a_2 = b + a_1;
assign a_3 = (a_1 == 4'h2) ? a_2: a_1;
assign b_0 = 4'h2;
assign b_1 = 4'h3;
assign b_2 = 4'h4;
assign a_4 = 4'h5;
assign b_3 = (a_3 == 4'h4) ? b_1: b_2;
assign a_5 = (a_3 == 4'h4) ? a_3: a_4;
assign b_4 = (a_3 == 4'h3) ? b_0: b_3;
assign a_6 = (a_3 == 4'h3) ? a_3: a_5;
assign c_0 = a_6;
endmodule   // mod

