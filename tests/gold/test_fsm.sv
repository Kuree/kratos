module mod (
  input logic  clk,
  input logic [1:0] in,
  output logic [1:0] out,
  input logic  rst
);

logic   Color_current_state;
logic   Color_next_state;
enum {
  Blue = 1'h0,
  Red = 1'h1
} Color_state;

always @(posedge clk, posedge rst) begin
  if (rst) begin
    Color_current_state <= Red;
  end
  else Color_current_state <= Color_next_state;
end
always_comb begin
  unique case (Color_current_state)
    Blue: if (in == 2'h1) begin
      Color_next_state = Red;
    end
    Red: if (in == 2'h1) begin
      Color_next_state = Blue;
    end
    else if (in == 2'h0) begin
      Color_next_state = Red;
    end
  endcase
end
always_comb begin
  unique case (Color_current_state)
    Blue: out = 2'h1;
    Red: out = 2'h2;
  endcase
end
endmodule   // mod

