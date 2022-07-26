module mod (
  input logic clk,
  input logic [1:0] in,
  input logic rst,
  output logic [1:0] out
);

typedef enum logic {
  Blue = 1'h0,
  Red = 1'h1
} Color_state;
Color_state Color_current_state;
Color_state Color_next_state;

always_ff @(posedge clk, posedge rst) begin
  if (rst) begin
    Color_current_state <= Red;
  end
  else Color_current_state <= Color_next_state;
end
always_comb begin
  Color_next_state = Color_current_state;
  unique case (Color_current_state)
    Blue: begin
        if (in == 2'h1) begin
          Color_next_state = Red;
        end
      end
    Red: begin
        if (in == 2'h0) begin
          Color_next_state = Red;
        end
        else if (in == 2'h1) begin
          Color_next_state = Blue;
        end
      end
    default: begin end
  endcase
end
always_comb begin
  unique case (Color_current_state)
    Blue: begin :Color_Blue_Output
        out = 2'h1;
      end :Color_Blue_Output
    Red: begin :Color_Red_Output
        out = 2'h2;
      end :Color_Red_Output
    default: begin end
  endcase
end
endmodule   // mod

