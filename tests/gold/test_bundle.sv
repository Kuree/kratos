module test_bundle (
  input logic in_port_a,
  input logic out_port_b,
  output logic in_port_b,
  output logic out_port_a
);

assign out_port_a = in_port_a;
assign in_port_b = out_port_b;
endmodule   // test_bundle

