module mod (
  input logic in,
  output logic out
);

typedef enum logic[1:0] {
  red = 2'h1,
  green = 2'h2
} color;
assign out = in;
endmodule   // mod

