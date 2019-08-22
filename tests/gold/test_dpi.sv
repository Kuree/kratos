import "DPI-C" function logic [1:0] add(input logic [1:0] arg0, input logic [1:0] arg1);
module mod (
  input logic [1:0] in,
  output logic [1:0] out
);

always_comb begin
  out = add (in, 2'h1);
end
endmodule   // mod

