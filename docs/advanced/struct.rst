Packed Struct in SystemVerilog
##############################

kratos allows to use packed struct in a limited ways. For now you can only
use it in ports declaration.

To create a packed struct, simply do by calling ``kratos.PackedStruct``
constructor. For instance, if you want to create a struct called
"config_data" which has two members (16-bit wide and unsigned), you
can do

.. code-block:: Python

    struct = PackedStruct("config_data", [("read", 16, False),
                                          ("data", 16, False)])

To use it in your generator, you can pass the definition into the
helper call ``[gen].port_packed()``. You can then use the name
to directly refer the members. For instance, to use the ``config_data``
we defined above, we can do something like below, where we create
a module to slice the ``"data"`` from the input port.

.. code-block:: Python

    class Mod(Generator):
        def __init__(self):
            super().__init__("mod")
            self.port_packed("in", PortDirection.In, struct)
            self.port("out", 16, PortDirection.Out)
            self.wire(self.ports["out"], self.ports["in"]["data"])

To generate the packed struct information, you can pass in
``extract_struct=True`` in the ``verilog`` function call.

.. code-block:: Python

    mod = Mod()
    mod_src, struct_def = verilog(mod, extra_struct=True)
