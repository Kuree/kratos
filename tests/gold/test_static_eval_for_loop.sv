module mod1 (
  input logic in,
  output logic [3:0] out
);

always_comb begin
  if (in == 1'h1) begin
    out[0] = 1'h1;
    out[1] = 1'h1;
    out[2] = 1'h1;
    out[3] = 1'h1;
  end
  else begin
    out[0] = 1'h0;
    out[1] = 1'h0;
    out[2] = 1'h0;
    out[3] = 1'h0;
  end
end
endmodule   // mod1

