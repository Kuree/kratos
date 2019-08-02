module mod (
  input logic  in
);

logic   out;
enum {
  green = 2'h2,
  red = 2'h1
} color;
assign out = in;
endmodule   // mod

