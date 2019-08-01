module mod1 (
  input logic  in,
  output logic  out
);

always_comb begin
  if (in == 1'h0) begin
    out = 1'h0;
  end
  else out = 1'h1;
end
endmodule   // mod1

