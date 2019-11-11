typedef enum logic[1:0] {
  green = 2'h2,
  red = 2'h1
} color;

module mod (
  input logic in,
  output logic out
);

assign out = in;
endmodule   // mod

