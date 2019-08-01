module test (
  input logic  clk,
  input logic  in,
  output logic  out
);


always @(posedge clk) begin
  if (clk) begin
    out <= in;
  end
end
endmodule   // test

