module mod (
  input logic  in
);

typedef enum logic[1:0] {
  green = 2'h2,
  red = 2'h1
} color;
logic   out;
assign out = in;
endmodule   // mod

