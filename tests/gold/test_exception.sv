module mod (
  input logic in
);

always_comb begin
  if (in == 1'h1) begin
    assert (1'h0);
  end
end
endmodule   // mod

