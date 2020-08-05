module mod (
  input logic this_is_a_long_name,
  output logic [5:0] out
);

assign out = {this_is_a_long_name, this_is_a_long_name, this_is_a_long_name,
    this_is_a_long_name, this_is_a_long_name, this_is_a_long_name};
endmodule   // mod

