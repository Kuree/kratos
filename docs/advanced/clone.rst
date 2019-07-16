Efficient Generator Clones
##########################

kratos has provided an efficient way to clone generators and modify the clones.
Similar to the "copy-on-write", the Python front-end allows users to create
explicit copies and allow them to be initialized later for further editing.

Design Philosophy on CoW
========================

The CoW mechanism is still work-in-progress, so the interface may subject to
change.

  - We want each clones have unique generator information. Since kratos is
    embedded into the Python language, we can leveraging the
    Object-Oriented-Programming in Python. This requires every non-verilog
    information has to be properly initialized during the clone process.
  - Since kratos is the generator of generators, we allow user to edit
    cloned generators. This requires the circuit definition to be initialized
    prior to the editing, hence the "copy" part.

How to implement Generator Clones
=================================
To avoid excessive computation in kratos' CoW mechanism, your
generators have to meet the following requirements:

1. Every argument to the ``Generator`` has to be hashable. For custom
   classes, you need to override ``__hash__`` function.
2. Your custom generator ``__init__`` function takes ``is_clone`` as an
   argument and passes it to the base class generator ``init`` call. For
   instance, you need something like:

   .. code-block:: Python

    class Mod(Generator):
        def __init__(self, width, is_clone=False):
            super().__init__(f"mod_{width}", is_clone=is_clone)
3. You have to call ``[Generator_Name].create()`` for every generator
   instantiation, where ``[Generator_Name]`` is your generator class
   name. You have to use named arguments for all your ``__init__``
   arguments. For instance, to create an instance of the ``Mod`` class,
   we can call

   .. code-block:: Python

       mod1 = Mod.create(width=1)
       mod2 = Mod.create(width=1)

   ``mod1`` and ``mod2`` will share the same generator definition.

4. If you want to make edits to the generators, you need to call
   ``initialize_clone`` on that particular instance. This function
   call ensures the full-instantiation of the generator definition,
   i.e. the "copy" part in CoW.
