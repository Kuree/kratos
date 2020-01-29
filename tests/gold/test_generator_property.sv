module mod (
  input logic a,
  output logic b,
  input logic clk
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
endmodule   // mod

