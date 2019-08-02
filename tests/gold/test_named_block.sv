module mod (
  input logic  in
);

logic   out;
always_comb begin
  if (in == 1'h1) begin :TEST
    out = 1'h0;
  end
  else out = 1'h1;
end
endmodule   // mod

