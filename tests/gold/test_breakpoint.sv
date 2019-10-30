import "DPI-C" function void breakpoint_trace(input int  instance_id, input int  stmt_id);
module mod #(parameter KRATOS_INSTANCE_ID = 32'h0)
(
  input logic  in,
  output logic  out
);

logic   val;
always_comb begin
  breakpoint_trace (32'h0, 32'h0);
  out = in;
  breakpoint_trace (32'h0, 32'h1);
  val = in;
end
endmodule   // mod

