typedef struct packed {
    logic [15:0] read;
    logic [15:0] write;
} bus;

module mod #(
  parameter P = 32'h2A
)
(
  output bus [P-1:0] out
);

bus [P-1:0] v;
assign out = v;
endmodule   // mod

