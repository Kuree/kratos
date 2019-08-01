module mod1 (
  input logic [1:0] in,
  output logic [1:0] out
);

always_comb begin
  if (in < 2'h1) begin
    if (in < 2'h2) begin
      out = 2'h1;
    end
    else out = 2'h3;
  end
  else out = 2'h2;
end
endmodule   // mod1

