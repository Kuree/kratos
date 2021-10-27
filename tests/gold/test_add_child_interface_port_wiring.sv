interface Config(
  input logic read,
  output logic write
);
endinterface

module child (
  Config bus2
);

assign bus2.write = bus2.read;
endmodule   // child

module mod (
);

logic read;
logic write;
Config bus (
  .read(read),
  .write(write)
);

child child (
  .bus2(bus)
);

endmodule   // mod

