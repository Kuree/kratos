import "DPI-C" context function void breakpoint_trace(input int  stmt_id);
import "DPI-C" context function void setup_debugger();
module mod (
  input logic  in,
  output logic  out
);

logic   val;
always_comb begin
  breakpoint_trace (32'h0);
  out = in;
  breakpoint_trace (32'h1);
  val = in;
end
initial begin
  setup_debugger ();
end
endmodule   // mod

