module test (
  input logic in1,
  input logic in2,
  input logic in3,
  output logic out
);

assign out = in1 ? in2: in3;
endmodule   // test

