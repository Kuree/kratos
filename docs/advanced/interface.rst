.. _interface-label:

Interfacce
##########

Kratos supports full features of SystemVerilog ``interface``, includes
``modport``. You can create an interface class and use standard OOP techniques
available in Python.

Create an interface
===================
First, you need to define an interface class definition. Image we have a bus\
where master and slave communicated to each other: he master needs to
write/read configuration data from the slave. To define the bus, we have

.. code-block:: Python

    class ConfigInterface(Interface):
        def __init__(self):
            Interface.__init__(self, "Config")
            width = 8
            # local variables
            read = self.var("read_data", width)
            write = self.var("write_data", width)
            r_en = self.var("read_en", 1)
            w_en = self.var("write_en", 1)
            # common ports
            clk = self.clock("clk")

            # define master -> slave ports
            # and slave -> master ports
            m_to_s= [write, r_en, w_en]
            s_to_m = [read]

            # define master and slave
            self.master = self.modport("Master")
            self.slave = self.modport("Slave")
            for port in m_to_s:
                self.master.set_output(port)
                self.slave.set_input(port)
            for port in s_to_m:
                self.master.set_input(port)
                self.slave.set_output(port)

            # both of them need clock
            self.master.set_input(clk)
            self.slave.set_input(clk)


In the example above, we have ``Master`` and ``Slave`` connected via a bus
using ``modport``. To save our efforts of typing, we group ports together
into ``m_to_s`` and ``s_to_m``. This also allows better introspection for
application-level passes.

To use them, we need some implementation for both master and slave. We will
use some dummy logic to illustrate how to use the interface and interact
with our logic. To instantiate an interface, you need the following function
call from the generator object:

.. code-block:: Python

    def interface(self, interface, name, is_port: bool = False):

By default the interface bus will be instantiated as local variable, you can
set ``is_port`` to ``True`` to make it a port.s

Here is the code for the master:

.. code-block:: Python

    class Master(Generator):
        def __init__(self):
            Generator.__init__(self, "Master")

            # instantiate the interface
            self.bus = self.interface(config.master, "bus",
                                      is_port=True)

            # some logic to loop the read and write
            # cycle
            self.counter = self.var("counter", 8)

            # we wire counter value to the write data
            self.wire(self.bus.write_data, self.counter)

            # always_ff on the posedge of clock from the interface
            @always_ff((posedge, self.bus.clk))
            def logic():
                if self.counter % 4 == 0:
                    self.bus.r_en = 1
                    self.bus.w_en = 0
                elif self.counter % 4 == 1:
                    self.bus.r_en = 0
                    self.bus.w_en = 1
                else:
                    self.bus.r_en = 0
                    self.bus.w_en = 0
                self.counter = self.counter + 1

            self.add_always(logic)

Notice that we use a counter to control the read and write enable signal,
as well as the write data. Here is the generated SystemVerilog if we call
``verilog(Master(), filename="master.sv")``.

.. code-block:: SystemVerilog:

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

.. note::

    Notice that Kratos will not generate interface if it is used as a modport.
    This is by design so that we can re-use the interface designed elsewhere
    such as UVM test files. However, Kratos will generate the interface
    definition if the entire interface is being used, as we shall see later.


Here is the Python code for the slave:

.. code-block:: Python

    class Slave(Generator):
        def __init__(self):
            Generator.__init__(self, "Slave")

            # instantiate the interface
            self.bus = self.interface(config.slave, "bus",
                                      is_port=True)

            self.value = self.var("value", 8)

            # just read and write out
            @always_ff((posedge, self.bus.clk))
            def logic():
                if self.bus.w_en:
                    self.value = self.bus.write_data
                elif self.bus.w_en:
                    self.bus.read_data = self.value

            self.add_always(logic)


Here is generated the SystemVerilog for slave by calling
``verilog(Slave(), "slave.sv")``:

.. code-block:: SystemVerilog

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

Now let's see how we can connect these two generators together:

.. code-block:: Python

    class Top(Generator):
        def __init__(self):
            Generator.__init__(self, "Top")

            # instantiate master and slave
            self.master = Master()
            self.slave = Slave()
            self.add_child("master", self.master)
            self.add_child("slave", self.slave)

            # clock will be from outside
            clk = self.clock("clk")

            # instantiate the interface bus
            # notice that we're using config, not the modport
            # version such as config.master
            bus = self.interface(config, "bus_top")

            # just need to wire things up
            self.wire(bus.clk, clk)
            self.wire(self.master.bus, bus)
            self.wire(self.slave.bus, bus)
            # the following also works
            # self.wire(self.master.bus, bus.Master)
            # self.wire(self.slave.bus, bus.Slave)

Notice that we instantiate the top level interface bus here as
``bus = self.interface(config, "bus_top")``. Since it's top-level, it is not
a port (default is not). When wiring with the child instances, we can just
call ``self.wire(self.master.bus, bus)``. Kratos is smart enough to figure
out you're wiring modport interface. If you want consistence semantics as
the one from SystemVerilog, you can also do
``self.wire(self.master.bus, bus.Master)``, which also works.
Since the interface takes ``clk`` as an input, we need to wire the signal from
the top level, i.e., ``self.wire(bus.clk, clk)``. Kratos will figure out the
proper port directions.

Here is the generated SystemVerilog. Since we are generating interface at the
top level, the interface definition will be generated:

.. code-block:: SystemVerilog

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

  // Master and Slave module definition omitted

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
