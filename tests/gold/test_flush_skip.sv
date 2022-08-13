module parent (
  input logic clk,
  input logic flush,
  input logic rst_n
);

logic a;
logic b;

always_ff @(posedge clk, negedge rst_n) begin
  if (~rst_n) begin
    b <= 1'h0;
  end
  else if (flush) begin
    b <= 1'h0;
  end
  else b <= ~b;
end

always_ff @(posedge clk, negedge rst_n) begin
  if (~rst_n) begin
    a <= 1'h0;
  end
  else if (flush) begin
    a <= 1'h1;
  end
  else a <= ~a;
end
endmodule   // parent

