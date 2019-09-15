module mod1 (
  input logic  clk,
  input logic  in,
  output logic  out
);

logic   out_stage_0;
logic   out_stage_1;
assign out_stage_0 = in;

always_ff @(posedge clk) begin
  out_stage_1 <= out_stage_0;
end

always_ff @(posedge clk) begin
  out <= out_stage_1;
end
endmodule   // mod1

