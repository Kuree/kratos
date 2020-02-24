module mod (
  output logic [3:0] out [3:0]
);

always_comb begin
  for (int unsigned i = 0; i < 4; i += 1) begin
      out[2'(i)] = 4'(i);
    end
end
endmodule   // mod

