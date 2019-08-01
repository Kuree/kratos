module mod (
  input logic  in0,
  input logic  in1,
  input logic  in2,
  input logic  in3,
  output logic [3:0] out
);

always_comb begin
  out[0] = in0;
  out[1] = in1;
  out[2] = in2;
  out[3] = in3;
end
endmodule   // mod

