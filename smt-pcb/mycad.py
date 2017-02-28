# Steven Herbst
# sherbst@stanford.edu
#
# CS448H Winter 2017

# Library enables user to instantiate new modules from KiCAD library

import os
import re
import random
from kicad.pcbnew.module import Module
from kicad.pcbnew.board import Board 
import pcbnew
import math
from skidl import Part
from pcbparser import PcbParser

class PinMapping(object):
    def __init__(self, lib, name):
        self.lib = lib
        self.name = name
        self.part = Part(lib, name)
        self.build_alias_table()

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
            self[pin.name] = pin.num

class BoardTools(object):
    @staticmethod
    def add_nets(pcb_dict, infile, outfile):
        # storage for modified text of the kicad_pcb file
        lines = []
    
        # status variables to keep track of where we are in the file
        inmodule = False
        innetclass = False
    
        # String containing name of the current module reference
        refdes = None
    
        # Integer containing number of the current pad
        pad_name = None
    
        # Create a dictionary mapping each unique net to an ID number
        net_dict = BoardTools.build_net_dict(pcb_dict)
 
        # Parse the exisiting PCB file
        tree = PcbParser.read_pcb_file(infile)
    
        # add nets to PCB file
        PcbParser.add_net_count(tree, net_dict)
        PcbParser.add_net_decls(tree, net_dict)
        PcbParser.populate_netclass(tree, net_dict)
        PcbParser.add_nets_to_modules(tree, pcb_dict, net_dict)

        # Write updated PCB information
        PcbParser.write_pcb_file(tree, outfile)
    
    @staticmethod
    def build_net_dict(pcb_dict):
        # build set of unique nets
        net_set = set()
        for mod_dict in pcb_dict.values():
            for net in mod_dict.values():
                net_set.add(net)
    
        # make a dictionary mapping each net to an id
        net_id = 1
        net_dict = {}
        for net in net_set:
            net_dict[net] = net_id
            net_id = net_id + 1
    
        return net_dict

class PcbDesign(object):
    def __init__(self, fname, dx=1.0, dy=1.0, width=25.0, height=25.0, 
                 smt_file_in='in.dict', refdes_max_count=1000):
        self.fname = fname
        self.comp_dict = {}
        self.dx = dx
        self.dy = dy
        self.width = width
        self.height = height
        self.smt_file_in = smt_file_in
        self.refdes_max_count = refdes_max_count

    def __contains__(self, item):
        return item in self.comp_dict

    def __iter__(self):
        for comp in self.comp_dict.values():
            yield comp
    
    def __setitem__(self, key, val):
        self.comp_dict[key] = val

    def __getitem__(self, key):
        return self.comp_dict[key]

    def add(self, component):
        component.parent = self
        component.name = self.nextRefdes(component.prefix)
        self[component.name] = component

    def nextRefdes(self, prefix):
        for count in range(1, self.refdes_max_count+1):
            name = prefix + str(count)
            if name not in self:
                break
        return name

    def wire(self, net_name, *args):
        for arg in args:
            arg.wire(net_name)

    def compile(self, critical_nets=None):
        # Create empty PCB
        pcb = Board()

        # add all components to the board
        for comp in self:
            pcb.add(comp.module) 

        # save PCB file without connectivity information
        pcb.save(self.fname)

        # add all net connections to the board, since this cannot 
        # be accomplished through pcbnew at present
        BoardTools.add_nets(self.get_design_dict(), self.fname, self.fname)
        
        # write input file for SMT solver
        self.write_smt_input(critical_nets)

    def get_design_dict(self):
        design_dict = {}
        for comp in self:
            if comp.name not in design_dict:
                design_dict[comp.name] = {}
            for pad in comp:
                if pad.net_name is not None:
                    design_dict[comp.name][pad.name] = pad.net_name
        return design_dict

    def get_module_dict(self):
        module_dict = {}

        for comp in self:
            module_dict[comp.name] = {}
            
            # set fixed rotation if provided
            if comp.rotation is not None:
                module_dict[comp.name]['rotation'] = comp.rotation
                comp.set_rotation(comp.rotation)
            else:
                module_dict[comp.name]['rotation'] = None
        
            # set fixed position if provided
            if comp.position is not None:
                # TODO: use Point object
                module_dict[comp.name]['x'] = comp.position[0]
                module_dict[comp.name]['y'] = comp.position[1]
            else:
                module_dict[comp.name]['x'] = None
                module_dict[comp.name]['y'] = None

            # add size information
            module_dict[comp.name]['width'] = comp.width
            module_dict[comp.name]['height'] = comp.height

        return module_dict

    def write_smt_input(self, critical_nets):
        smt_input = {}
        smt_input['dx'] = self.dx
        smt_input['dy'] = self.dy
        smt_input['width'] = self.width
        smt_input['height'] = self.height
        smt_input['module_dict'] = self.get_module_dict()
        smt_input['critical_nets'] = critical_nets
        with open(self.smt_file_in, 'w') as f:
            f.write(repr(smt_input)+'\n')

class PcbPad(object):
    def __init__(self, pad):
        self.pad = pad
        self.net_name = None

    def wire(self, net_name):
        self.net_name = net_name

    @property
    def name(self):
        return self.pad.name

class PcbComponent(object):
    def __init__(self, lib, part, position=None, rotation=None):
        # instantiate the part
        self.load_module(lib, part)

        # set the position and rotation
        self.position = position
        self.rotation = rotation

        # fill up the dictionary defining component pads
        self.pad_dict = {}
        self.populate_pads()

    def load_module(self, lib, part):
        KICAD_PATH = os.environ['KICAD_PATH']
        file_ext = 'pretty'

        src_libpath = os.path.join(KICAD_PATH, 'modules', lib + '.' + file_ext)
        src_type = pcbnew.IO_MGR.GuessPluginTypeFromLibPath(src_libpath)
        src_plugin = pcbnew.IO_MGR.PluginFind(src_type)

        self.module = Module.wrap(src_plugin.FootprintLoad(src_libpath, part))

    def populate_pads(self):
        for pad in self.module.pads:
            self[pad.name] = PcbPad(pad)
            self[pad.name].parent = self

    def __contains__(self, item):
        return item in self.pad_dict

    def __iter__(self):
        for pad in self.pad_dict.values():
            yield pad 

    def __setitem__(self, key, val):
        self.pad_dict[key] = val

    def __getitem__(self, key):
        return self.pad_dict[key]

    @property
    def width(self):
        return self.module.boundingBox.width

    @property
    def height(self):
        return self.module.boundingBox.height

    @property
    def pads(self):
        for pad in self.pad_dict.values():
            yield pad

    @property 
    def name(self):
        return self.module.reference

    @name.setter
    def name(self, value):
        self.module.reference = value

    def set_rotation(self, value):
        self.module.rotation = value

    @property
    def boundingBox(self):
        return self.module.boundingBox
