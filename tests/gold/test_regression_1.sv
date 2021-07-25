module Top (
  input logic [1:0] i_data_in,
  output logic [1:0] o_data_out
);

logic child1_out;
logic child2_out;
assign o_data_out[0] = child1_out;
assign o_data_out[1] = child2_out;
mod1 child1 (
  .in(i_data_in[0]),
  .out(child1_out)
);

mod1 child2 (
  .in(i_data_in[1]),
  .out(child2_out)
);

endmodule   // Top

module mod1 (
  input logic in,
  output logic out
);

assign out = in;
endmodule   // mod1

