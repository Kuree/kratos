interface Config(
  input logic clk
);
  logic r_en;
  logic [7:0] read_data;
  logic w_en;
  logic [7:0] write_data;
  modport Master(input clk, input read_data, output r_en, output w_en, output write_data);
  modport Slave(input clk, input r_en, input w_en, input write_data, output read_data);
endinterface

module Master (
  Config.Master bus
);

logic [7:0] counter;
assign bus.write_data = counter;

always_ff @(posedge bus.clk) begin
  if ((counter % 8'h4) == 8'h0) begin
    bus.r_en <= 1'h1;
    bus.w_en <= 1'h0;
  end
  else if ((counter % 8'h4) == 8'h1) begin
    bus.r_en <= 1'h0;
    bus.w_en <= 1'h1;
  end
  else begin
    bus.r_en <= 1'h0;
    bus.w_en <= 1'h0;
  end
  counter <= counter + 8'h1;
end
endmodule   // Master

module Slave (
  Config.Slave bus
);

logic [7:0] value;

always_ff @(posedge bus.clk) begin
  if (bus.w_en) begin
    value <= bus.write_data;
  end
  else if (bus.w_en) begin
    bus.read_data <= value;
  end
end
endmodule   // Slave

module Top (
  input logic clk
);

Config bus_top (
  .clk(clk)
);

Master master (
  .bus(bus_top.Master)
);

Slave slave (
  .bus(bus_top.Slave)
);

endmodule   // Top

