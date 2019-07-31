from _kratos import PortBundleDefinition, PortType, PortDirection


# a helper class to deal with port interface
class PortBundle(PortBundleDefinition):
    def __init__(self):
        self.definition = PortBundleDefinition()

    def input(self, name, width, is_signed=False, size=1,
              port_type=PortType.Data):
        self.definition.add_definition(name, width, size, is_signed,
                                       PortDirection.In, port_type)

    def output(self, name, width, is_signed=False, size=1,
               port_type=PortType.Data):
        self.definition.add_definition(name, width, size, is_signed,
                                       PortDirection.Out, port_type)

    def flip(self):
        bundle = PortBundle()
        bundle.definition = self.definition.flip()
        return bundle
