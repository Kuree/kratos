interface Config;
  logic read;
  logic write;
  modport Slave(input read, output write);
endinterface

module child (
  Config.Slave bus_s
);

assign bus_s.write = bus_s.read;
endmodule   // child

module mod (
);

Config bus();
child child (
  .bus_s(bus.Slave)
);

endmodule   // mod

