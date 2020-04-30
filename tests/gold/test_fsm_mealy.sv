module mod (
  input logic clk,
  input logic [1:0] in,
  output logic [1:0] out,
  input logic rst
);

typedef enum logic {
  Blue = 1'h0,
  Red = 1'h1
} Color_state;
Color_state Color_current_state;
Color_state Color_next_state;
function void Color_output(
  input logic [1:0] out_value
);
begin
  out = out_value;
end
endfunction

always_ff @(posedge clk, posedge rst) begin
  if (rst) begin
    Color_current_state <= Red;
  end
  else Color_current_state <= Color_next_state;
end
always_comb begin
  Color_next_state = Color_current_state;
  unique case (Color_current_state)
    Blue: if (in == 2'h1) begin
      Color_next_state = Red;
      Color_output (2'h2);
    end
    Red: if (in == 2'h1) begin
      Color_next_state = Blue;
      Color_output (2'h1);
    end
    else if (in == 2'h0) begin
      Color_next_state = Red;
      Color_output (2'h2);
    end
  endcase
end
endmodule   // mod

