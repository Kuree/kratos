module mod (
  output logic [5:0] out,
  input logic  this_is_a_long_name
);

assign out = {this_is_a_long_name, this_is_a_long_name, this_is_a_long_name,
    this_is_a_long_name, this_is_a_long_name, this_is_a_long_name};
endmodule   // mod

