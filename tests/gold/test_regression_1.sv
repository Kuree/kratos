module Top (
  input logic [1:0] i_data_in,
  output logic [1:0] o_data_out
);

logic   child1_in;
logic   child1_out;
logic   child2_in;
logic   child2_out;
assign child1_in = i_data_in[0];
assign o_data_out[0] = child1_out;
assign child2_in = i_data_in[1];
assign o_data_out[1] = child2_out;
mod1 child1 (
  .in(child1_in),
  .out(child1_out)
);

mod1 child2 (
  .in(child2_in),
  .out(child2_out)
);

endmodule   // Top

module mod1 (
  input logic  in,
  output logic  out
);

assign out = in;
endmodule   // mod1

