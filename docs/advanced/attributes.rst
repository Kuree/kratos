Attributes in Kratos's IR
#########################

User annotated attributes is very helper to feed additional
information to the passes, allowing more complex passes. Kratos
allows you to embedded a ``string`` as an attribute to any IR
nodes. Here is an example how to create an ``Attribute`` and
then annotate the structural wire assignment.


Generator definition:

.. code-block:: Python

    class PassThroughMod(Generator):
        def __init__(self, is_clone: bool = False):
            super().__init__("mod1", True, is_clone)
            self.in_ = self.port("in", 1, PortDirection.In)
            self.out_ = self.port("out", 1, PortDirection.Out)
            self.wire(self.out_, self.in_)

Annotation class and testing:

.. code-block:: Python

    mod = PassThroughTop()
    stmt = mod.get_stmt_by_index(0)

    class TestAttribute(Attribute):
        def __init__(self):
            Attribute.__init__(self)
            self.value = "42"

    stmt.add_attribute(TestAttribute())

    assert len(mod.get_stmt_by_index(0).get_attributes()) > 0
    assert mod.get_stmt_by_index(0).get_attributes()[0].value == "42"

You will also have access to the ``value`` and ``get_attributes()`` in
custom passes.

.. note::

    - Due to the limitation of ``pybind`` and Python, you are required
      to use ``Base().__init__(self, *args, **kargs)`` to initialize
      the Attribute class.
    - You can only pass information to ``value`` as a string to the
      backend. It is because the up casting doesn't work well in Python.
