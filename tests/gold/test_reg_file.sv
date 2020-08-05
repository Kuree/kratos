module mod (
  input logic [3:0] in,
  input logic [1:0] raddr,
  input logic [1:0] warr,
  output logic [3:0] out
);

logic [3:0] reg_file [3:0];
always_comb begin
  reg_file[warr] = in;
  out = reg_file[raddr];
end
endmodule   // mod

