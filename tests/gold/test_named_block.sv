module mod (
  input logic in,
  output logic out
);

always_comb begin
  if (in == 1'h1) begin :TEST
    out = 1'h0;
  end :TEST
  else out = 1'h1;
end
always_comb begin :TEST2
  out = 1'h1;
end :TEST2
endmodule   // mod

