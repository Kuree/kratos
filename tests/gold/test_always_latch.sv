module mod (
  input logic a,
  output logic b
);

always_latch begin
  if (a) begin
    b = 1'h1;
  end
end
endmodule   // mod

