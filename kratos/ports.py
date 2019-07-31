from .util import get_fn_ln


class PortBundleRef:
    def __init__(self, bundle, generator):
        self.bundle = bundle
        self.generator = generator

    def __getattr__(self, name):
        return self.bundle.port(name)

    def __getitem__(self, name):
        return self.bundle.port(name)

    def assign(self, other: "PortBundleRef"):
        assert isinstance(other, PortBundleRef)
        port_names = self.bundle.ports()
        for port_name in port_names:
            stmt = self.generator.internal_generator.wire_ports(
                self.bundle.port(port_name), other.bundle.port(port_name))
            if self.generator.debug:
                stmt.add_fn_ln(get_fn_ln(3))


# a helper class to deal with port interface
class PortBundle:
    def __init__(self):
        self.__inputs = {}
        self.__outputs = {}

    def input(self, name, width, is_signed=False, size=1):
        assert name not in self.__inputs
        assert name not in self.__outputs
        self.__inputs[name] = {"name": name, "width": width,
                               "is_signed": is_signed, "size": size}

    def output(self, name, width, is_signed=False, size=1):
        assert name not in self.__inputs
        assert name not in self.__outputs
        self.__outputs[name] = {"name": name, "width": width,
                                "is_signed": is_signed, "size": size}

    def port(self, name):
        if name in self.__inputs:
            return self.__inputs[name]
        else:
            assert name in self.__outputs
            return self.__outputs[name]

    def ports(self):
        lst = list(self.__inputs.keys()) + list(self.__outputs.keys())
        # to be deterministic
        lst.sort()
        return lst

    def flip(self):
        # pythonic way
        self.__inputs, self.__outputs = self.__outputs, self.__inputs
        return self

    def add_to_generator(self, bundle_name: str, generator):
        assert self.__class__ != PortBundle.__class__, \
            "Must inherit from {0}".format(PortBundle.__name__)
        inputs = {}
        for name, values in self.__inputs.items():
            # we change the name using underscore
            values["name"] = "{0}_{1}".format(bundle_name, name)
            port = generator.input(**values)
            if generator.debug:
                port.add_fn_ln(get_fn_ln(3))
            inputs[name] = port
        outputs = {}
        for name, values in self.__outputs.items():
            # we change the name using underscore
            values["name"] = "{0}_{1}".format(bundle_name, name)
            port = generator.output(**values)
            if generator.debug:
                port.add_fn_ln(get_fn_ln(3))
            outputs[name] = port
        self.__inputs, self.__outputs = inputs, outputs

        return bundle_name, PortBundleRef(self, generator)
