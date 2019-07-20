Attributes in Kratos's IR
#########################

User annotated attributes is very helper to feed additional
information to the passes, allowing more complex passes. Kratos
allows you to embedded a ``string`` as an attribute to any IR
nodes. Here is an example how to create an ``Attribute`` and
then annotate the structural wire assignment.


Attributes in Python
====================

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
            super().__init__()
            self.value = 42

    stmt.add_attribute(TestAttribute())

    assert len(mod.get_stmt_by_index(0).get_attributes()) > 0
    attr = mod.get_stmt_by_index(0).get_attributes()[0].get()
    assert attr.value == 42

Notice that ``get()`` call is necessary to obtain the Python object.

Attributes in C++
=================

The C++ ``Attribute`` object has a generic pointer you can use to
retrieve your custom data. You're responsible for the life-cycle of
that custom data. To help you facilitate the type casting, you
can set the type string in ``type_str`` and use that to indicate
what custom type it's holding. If the attribute comes from Python,
``type_str`` will be ``"python"``.

.. note::

    Due to the language different between C++ and Python, there are
    some limitation on how they should be used.

    1. All attributes are written in C++: you're safe as long as
       you follow the usage of C++ attributes.
    2. All attributes are written in Python: you're safe as long
       as you follow the usage of Python attributes.
    3. Attributes written in Python and consumed in C++ or verse
       versa: because Python and C++'s objects have different memory
       layout, it is very dangerous to communicate. To work around this,
       all the Attribute object have ``value_str`` attribute as string,
       you can use that to communicate between Python and C++. For
       instance. You can have

       .. code-block:: Python

           class TestAttribute(Attribute):
               def __init__(self):
                   super().__init__()
                   self.value_str = "42"
