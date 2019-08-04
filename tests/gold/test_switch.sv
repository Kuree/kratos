module switch_test (
  input logic [2:0] in,
  output logic [2:0] out
);

always_comb begin
  unique case (in)
    3'h0: out = 3'h0;
    3'h1: out = 3'h1;
    default: out = 3'h2;
  endcase
end
endmodule   // switch_test

