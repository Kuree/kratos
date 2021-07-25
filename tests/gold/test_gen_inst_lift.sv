module child (
  input logic a,
  input logic clk,
  output logic b
);

assign b = a;
endmodule   // child

module parent (
  input logic clk
);

logic a [3:0];
logic b [3:0];
logic child_0_b;
logic child_1_b;
logic child_2_b;
logic child_3_b;
assign b[0] = child_0_b;
assign b[1] = child_1_b;
assign b[2] = child_2_b;
assign b[3] = child_3_b;
for (genvar i = 0; i < 4; i += 1) begin :child
  child inst (
    .a(a[2'(i)]),
    .clk(clk),
    .b(b[2'(i)])
  );

end :child
endmodule   // parent

