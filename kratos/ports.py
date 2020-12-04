from _kratos import PortBundleDefinition, PortType, PortDirection, \
    get_fn_ln


# a helper class to deal with port interface
class PortBundle:
    def __init__(self, debug=False):
        self.definition = PortBundleDefinition(self.__class__.__name__)
        self.debug = debug

    def input(self, name, width, is_signed=False, size=1,
              port_type=PortType.Data):
        self.definition.add_definition(name, width, size, is_signed,
                                       PortDirection.In, port_type)
        if self.debug:
            self.definition.add_debug_info(name, get_fn_ln())

    def output(self, name, width, is_signed=False, size=1,
               port_type=PortType.Data):
        self.definition.add_definition(name, width, size, is_signed,
                                       PortDirection.Out, port_type)
        if self.debug:
            self.definition.add_debug_info(name, get_fn_ln())

    def clock(self, name, is_input=True):
        if is_input:
            self.input(name, 1, port_type=PortType.Clock)
        else:
            self.output(name, 1, port_type=PortType.Clock)

    def reset(self, name, is_input=True):
        if is_input:
            self.input(name, 1, port_type=PortType.AsyncReset)
        else:
            self.output(name, 1, port_type=PortType.AsyncReset)

    def flip(self):
        bundle = PortBundle()
        bundle.definition = self.definition.flip()
        bundle.debug = self.debug
        bundle.definition.name = self.definition.name
        return bundle
