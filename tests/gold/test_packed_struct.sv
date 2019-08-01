typedef struct packed {
    logic [15:0]  read;
    logic [15:0]  data;
} config_data;

module mod (
  input config_data in,
  output config_data out
);

assign out = in;
endmodule   // mod

