module mod (
  input logic a,
  input logic clk,
  output logic b
);

logic a_tmp;

always_ff @(posedge clk) begin
  if ((a == 1'h1) & (~a_tmp)) begin
    b <= 1'h0;
    a_tmp <= 1'h1;
  end
  else if (a_tmp) begin
    b <= 1'h1;
  end
end
property rule1;
  @(posedge clk) a == 1'h1 |-> ##1 b == 1'h0 |-> b == 1'h1;
endproperty
assert property (rule1);
property rule2;
  @(posedge clk) a == 1'h1 |-> ##1 b == 1'h0 |-> b == 1'h1;
endproperty
assume property (rule2);
property rule3;
  @(posedge clk) a == 1'h1 |-> ##1 b == 1'h0 |-> b == 1'h1;
endproperty
cover property (rule3);
endmodule   // mod

