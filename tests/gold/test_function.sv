module mod (
  input logic [1:0] in,
  output logic [1:0] out,
  output logic [1:0] out2
);

function update_out(
  input logic [1:0] value,
  input logic  predicate
);
begin
  out2 = value;
  if (predicate) begin
    update_out = value + in;
  end
  else update_out = value;
end
endfunction
always_comb begin
  out = update_out (in, 1'h1);
end
endmodule   // mod

