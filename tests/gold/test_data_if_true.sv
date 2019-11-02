module mod1 (
  input logic in,
  output logic out
);

always_comb begin
  if (in == 1'h1) begin
    out = 1'h1;
  end
  else out = 1'h0;
end
endmodule   // mod1

