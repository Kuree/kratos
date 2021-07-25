module Memory (
  input logic [12:0] A,
  input logic CEB,
  input logic CLK,
  input logic [15:0] D,
  input logic WEB,
  output logic [15:0] Q
);

logic [15:0] Q_array [5:0];
logic [15:0] SRAM_0_Q;
logic [15:0] SRAM_1_Q;
logic [15:0] SRAM_2_Q;
logic [15:0] SRAM_3_Q;
logic [15:0] SRAM_4_Q;
logic [15:0] SRAM_5_Q;
logic [5:0] WEB_array;
logic [9:0] addr_to_mem;
logic [2:0] memory_select;
logic [2:0] output_select;
assign memory_select = A[12:10];
assign addr_to_mem = A[9:0];
assign WEB_array = (~WEB) ? ~(6'h1 << 6'(memory_select)): ~6'h0;

always_ff @(posedge CLK) begin
  if (!CEB) begin
    if (WEB) begin
      output_select <= memory_select;
    end
  end
end
assign Q = Q_array[output_select];
assign Q_array[0] = SRAM_0_Q;
assign Q_array[1] = SRAM_1_Q;
assign Q_array[2] = SRAM_2_Q;
assign Q_array[3] = SRAM_3_Q;
assign Q_array[4] = SRAM_4_Q;
assign Q_array[5] = SRAM_5_Q;
SRAM_MACRO SRAM_0 (
  .A(addr_to_mem),
  .CEB(CEB),
  .CLK(CLK),
  .D(D),
  .WEB(WEB_array[0]),
  .Q(SRAM_0_Q)
);

SRAM_MACRO SRAM_1 (
  .A(addr_to_mem),
  .CEB(CEB),
  .CLK(CLK),
  .D(D),
  .WEB(WEB_array[1]),
  .Q(SRAM_1_Q)
);

SRAM_MACRO SRAM_2 (
  .A(addr_to_mem),
  .CEB(CEB),
  .CLK(CLK),
  .D(D),
  .WEB(WEB_array[2]),
  .Q(SRAM_2_Q)
);

SRAM_MACRO SRAM_3 (
  .A(addr_to_mem),
  .CEB(CEB),
  .CLK(CLK),
  .D(D),
  .WEB(WEB_array[3]),
  .Q(SRAM_3_Q)
);

SRAM_MACRO SRAM_4 (
  .A(addr_to_mem),
  .CEB(CEB),
  .CLK(CLK),
  .D(D),
  .WEB(WEB_array[4]),
  .Q(SRAM_4_Q)
);

SRAM_MACRO SRAM_5 (
  .A(addr_to_mem),
  .CEB(CEB),
  .CLK(CLK),
  .D(D),
  .WEB(WEB_array[5]),
  .Q(SRAM_5_Q)
);

endmodule   // Memory

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

