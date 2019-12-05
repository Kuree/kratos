from typing import List, Union


class InterfaceWrapper:
    """Interface wrapper"""
    def __init__(self, interface):
        self._i = interface

    def input(self, name: str, width: int, size: Union[int, List[int]] = 1):
        return self._i.input(name, width, size)

    def output(self, name: str, width: int, size: Union[int, List[int]] = 1):
        return self._i.output(name, width, size)

    def var(self, name: str, width: int, size: Union[int, List[int]] = 1):
        return self._i.var(name, width, size)

    def __getitem__(self, item):
        if self._i.has_modport(item):
            return self._i.get_modport_ref(item)
        elif item in self._i:
            return self._i[item]
        raise AttributeError

    def __getattr__(self, item):
        return self[item]

    @property
    def internal_interface(self):
        return self._i
