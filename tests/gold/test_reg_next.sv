module test (
  input logic  clk,
  input logic  in,
  output logic  out
);

logic   a;
logic   b;

always_ff @(posedge clk) begin
  a <= in;
  b <= a;
end
assign out = b;
endmodule   // test

