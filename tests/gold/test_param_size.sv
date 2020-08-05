module mod #(
  parameter ADDR_WIDTH = 16'h8,
  parameter WIDTH = 16'h8
)
(
  input logic [ADDR_WIDTH-1:0] addr,
  input logic clk,
  input logic [WIDTH-1:0] data_in
);

logic [WIDTH-1:0] data [(16'h2 ** ADDR_WIDTH)-1:0];

always_ff @(posedge clk) begin
  data[addr] <= data_in;
end
endmodule   // mod

