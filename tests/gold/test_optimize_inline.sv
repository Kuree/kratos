module parent (
  input logic clk
);

logic b;
logic v1;

always_ff @(posedge clk) begin
  if (v1) begin
    b <= 1'h1;
  end
  else b <= 1'h0;
end
endmodule   // parent

