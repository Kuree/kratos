DPI in Kratos
=============

Direct Programming Interface (DPI) is an very powerful tool that allows
foreign Programming languages to be run in the simulator. DPI has been
used for rapid prototyping and debugging. Kratos supports DPI in two
ways:

1. C/C++. This is the default functionality shipped with kratos.
2. Python code. This can be installed from `kratos-dpi <https://github.com/Kuree/kratos-dpi>`__.
   You can run any arbitrary Python code in lieu of native C/C++ code.

C/C++ Interface
---------------
You can declare a function declaration in the following way:

.. code-block:: Python

    from kratos.func import dpi_function

     @dpi_function(2)
     def add(arg0, arg1):
         pass

``@dpi_function(width)` denotes the return size. Notice that the ``width``
support is still experimental due to the inconsistency between verilator
and commercial simulators.

After declaration, you can use it in any always block, as a normal function
call, as shown below:

.. code-block:: Python

     class Mod(Generator):
         def __init__(self):
             super().__init__("mod", debug=True)
             self._in = self.input("in", 2)
             self._out = self.output("out", 2)

             self.add_code(self.code)

         def code(self):
             # because the types are inferred
             # implicit const conversion doesn't work here
             self._out = add(self._in, const(1, 2))

You have to make sure to implement the function in C/C++ with the following
function signature:

.. code-block:: C

    int add(int arg0, int arg1);

If you are using C++, ``extern`` is required.

Python Interface
----------------

Once you've installed kratos-dpi, you can run any arbitrary Python function
with DPI, as shown below:

.. code-block:: Python

    from kratos_dpi import dpi_python

    @dpi_python(16)
    def test_a(a, b):
        return a + b

Again, you can use it in any always block as a function call. However,
kratos-dpi needs to compile your Python code into a shared library. You
need to call ``dpi_compile`` to compile all your Python DPI functions
into a shared object, such as:

.. code-block:: Python

  lib_path = dpi_compile("add_dpi", "output_dir")

You need to provide a working directory for kratos-dpi to compile objects.
The function call returns the path for the shared object.


SystemVerilog Types
-------------------

Kratos follows the SystemVerilog spec about the types. Currently it offers
two different ways to deal with function argument types:

1. Logic based type interface.
2. Native C types.

You can choose which one to have by using ``int_dpi_interface=True`` in
``verilog()`` function. If the option is set to ``True``, native C types
will be used. It will perform a ceiling on each argument and output
``char``, ``short int``, ``int``, and ``long int`` as the C interface.
If the option is set to ``False``, ``logic`` will be used and users are
responsible to handle the ``svLogic`` type conversion by themselves.
You can refer to ``svdpi.h`` header to see how to conversion works.

.. note::

    If you are using Python interface, you're required to use
    ``int_dpi_interface=True``.


Work in Progress
----------------

1. Integrate with simulators to load the shared library.
