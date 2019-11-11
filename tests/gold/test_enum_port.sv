typedef enum logic {
  IDLE = 1'h0,
  WAIT = 1'h1
} State;

module mod (
  input State in,
  output State out
);

assign out = in;
endmodule   // mod

