module test (
  input logic  clk,
  input logic  en,
  input logic  in,
  output logic  out
);

logic   a;
logic   b;

always_ff @(posedge clk) begin
  if (en) begin
    a <= in;
    b <= a;
  end
end
assign out = b;
endmodule   // test

