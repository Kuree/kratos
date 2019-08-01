module elseif (
  input logic  in0,
  input logic  in1,
  output logic  out
);

always_comb begin
  if (in0 == 1'h1) begin
    out = 1'h1;
  end
  else if (in1 == 1'h1) begin
    out = 1'h0;
  end
  else out = 1'h1;
end
endmodule   // elseif

