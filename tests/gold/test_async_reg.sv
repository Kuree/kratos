module register (
  input logic  clk,
  input logic [15:0] in,
  output logic [15:0] out,
  input logic  rst
);

logic  [15:0] val;

always_ff @(posedge clk, posedge rst) begin
  if (~rst) begin
    val <= 16'h0;
  end
  else val <= in;
end
always_comb begin
  out = val;
end
endmodule   // register

