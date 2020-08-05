module SRAM_MACRO (
  input logic [9:0] A,
  input logic CEB,
  input logic CLK,
  input logic [15:0] D,
  input logic WEB,
  output logic [15:0] Q
);

logic [15:0] data_array [1023:0];

always_ff @(posedge CLK) begin
  if (!CEB) begin
    Q = data_array[A];
    if (!WEB) begin
      data_array[A] = D;
    end
  end
end
endmodule   // SRAM_MACRO

