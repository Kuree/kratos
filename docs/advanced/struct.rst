Packed Struct and Bundles
#########################

Packed Struct
=============

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
normal call ``[gen].input()`` or ``[gen].output``. You can then use the name
to directly refer the members. For instance, to use the ``config_data``
we defined above, we can do something like below, where we create
a module to slice the ``"data"`` from the input port.

.. code-block:: Python

    class Mod(Generator):
        def __init__(self):
            super().__init__("mod")
            self.input("in", struct)
            self.output("out", 16)
            self.wire(self.ports["out"], self.ports["in"]["data"])

To generate the packed struct information, you can pass in
``extract_struct=True`` in the ``verilog`` function call.

.. code-block:: Python

    mod = Mod()
    mod_src, struct_def = verilog(mod, extra_struct=True)


Port Bundles
============
Similar to pymtl and Chisel, kratos allows you to create arbitrary port
bundles with arbitrary direction within it. To create a bundle definition,
you need to subclass the ``PortBundle`` class like the following:

.. code-block:: Python

    class Test(PortBundle):
        def __init__(self):
            super().__init__()
            self.input("a", 1)
            self.output("b", 1)

The ``input()`` and ``ouput()`` interfaces are the same as that of
``Generator``. To add a port bundle to the generator, you can do

.. code-block:: Python

    self.port_bundle("in_port", Test())

where ``"in_port"`` is the bundle port name. Notice that we need to instantiate
the object. You can also call ``flip`` to flip the port direction in place.
For instance, you can do something like this:

.. code-block:: Python

    p = self.port_bundle("out_port", Test().flip())

The wiring process is the same as as the packed struct. To access a
port bundle member, you can either access via ``[]``, ``.``
(such as ``p.a``), or through ``[gen].ports.p.a``


When to use packed sturct and when to use port bundles
======================================================
Keep in mind that in SystemVerilog there is no correspondence of a port
bundle. That means the port bundle will be flattened into normal ports
(the Python front-end does the job for you). As a result, the generated
SystemVerilog code may not be that readable. The naming scheme is
``{bundle_name}_{member_name}``.

The rule of thumb is that if you want to have a mixture of input and output
in your struct, use port bundle, otherwise use packed struct.

If you want better generated SystemVerilog while using port bundles, it
is highly recommended to use ``interface`` instead. It will be compiled to
SystemVerilog ``interface`` instead, which offers better functionality
than port bundles. You can check out more details, see :ref:`interface-label`.

.. note::

    There is a pass called ``change_port_bundle_struct`` that can convert
    port bundles into a packed struct. The only condition is that all the
    ports in the bundle have to be the same direction.
