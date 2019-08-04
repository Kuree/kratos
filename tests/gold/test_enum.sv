module mod (
  input logic  in
);

typedef enum {
  green = 2'h2,
  red = 2'h1
} color;
logic   out;
assign out = in;
endmodule   // mod

