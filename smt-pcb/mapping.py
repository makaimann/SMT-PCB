# Temporary home for code to read out pin mappings from schematic symbols

from skidl import Part


class PinMapping(object):
    def __init__(self, lib, name):
        self.lib = lib
        self.name = name
        self.part = Part(lib, name)
        self.build_alias_table()
        print lib, name, self.alias_table

    def __getitem__(self, key):
        return self.alias_table[key]

    def __setitem__(self, key, val):
        self.alias_table[key] = val

    def __contains__(self, item):
        return item in self.alias_table

    def items(self):
        return self.alias_table.items()

    def build_alias_table(self):
        self.alias_table = {}
        for pin in self.part.pins:
            if pin.name not in self:
                self[pin.name] = pin.num
            elif not isinstance(self[pin.name], list):
                self[pin.name] = [self[pin.name], pin.num]
            else:
                self[pin.name].append(pin.num)
