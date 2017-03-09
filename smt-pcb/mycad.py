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
from kicad.point import Point
from datetime import date
import pcbnew
import math
import json
from pcbparser import PcbParser

class BoardTools(object):
    @staticmethod
    def add_nets(pcb_dict, net_class_list, infile, outfile):
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
        PcbParser.add_nets_to_modules(tree, pcb_dict, net_dict)

        # add net classes to PCB file
        PcbParser.populate_net_classes(tree, net_class_list)

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
    def __init__(self, fname, dx=1.0, dy=1.0, refdes_max_count=1000):
        self.fname = fname
        self.comp_dict = {}
        self.net_class_list = []
        self.dx = dx
        self.dy = dy
        self.refdes_max_count = refdes_max_count
        self.refdes_set = set()
        self.keepouts = []
        self.vias = []

        self.comments = None
        self.title = None
        self.revision = None
        self.company = None
        self.date = date.today()

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
        if isinstance(component, PcbComponent):
            component.parent = self
            component.name = self.nextRefdes(component.prefix)
            self[component.name] = component
        elif isinstance(component, PcbVia):
            component.name = self.nextRefdes(component.prefix)
            self.vias.append(component)
        elif isinstance(component, PcbKeepout):
            component.name = self.nextRefdes(component.prefix)
            self.keepouts.append(component)
        else:
            raise Exception('Component type not handled.')

    def add_net_class(self, net_class):
        self.net_class_list.append(net_class)

    def nextRefdes(self, prefix):
        for count in range(1, self.refdes_max_count+1):
            name = unicode(prefix + str(count))
            if name not in self.refdes_set:
                break
        self.refdes_set.add(name)
        return name

    def wire(self, net_name, *args):
        for arg in args:
            arg.wire(net_name)

    def compile(self, smt_file_in=None):
        # Create empty PCB
        pcb = Board()

        # add all components to the board
        for comp in self:
            pcb.add(comp.module) 

        # make title block
        if self.comments:
            pcb.comments = self.comments
        if self.title:
            pcb.title = self.title
        if self.revision:
            pcb.revision = self.revision
        if self.company:
            pcb.company = self.company
        if self.date:
            pcb.date = self.date

        # save PCB file without connectivity information
        pcb.save(self.fname)

        # write input file for SMT solver
        self.write_smt_input(smt_file_in)

    def get_design_dict(self):
        design_dict = {}
        for comp in self:
            if comp.name not in design_dict:
                design_dict[comp.name] = {}
            for pad in comp:
                if pad.net_name is not None:
                    design_dict[comp.name][pad.name] = pad.net_name
        for via in self.vias:
            design_dict[via.name] = {}
        for keepout in self.keepouts:
            design_dict[keepout.name] = {}
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
                if comp.mode.lower() == 'ul':
                    ul_relative = Point(0,0)
                elif comp.mode.lower() == 'pin1':
                    # Compute the position of the upper-left corner of the device
                    # relative to PIN1
                    ul_relative = comp.boundingBox.ul - comp['1'].pad.center
                elif comp.mode.lower() == 'center':
                    comp_center = Point.wrap(comp.module._obj.GetCenter())
                    ul_relative = comp.boundingBox.ul - comp_center
                else:
                    raise Exception('Unimplemented positioning mode.')
                
                # compute fixed position of upper-left corner of device
                fixed_pos = comp.position + ul_relative
    
                # store result in SMT input dictionary
                module_dict[comp.name]['x'] = fixed_pos.x
                module_dict[comp.name]['y'] = fixed_pos.y
                module_dict[comp.name]['fixed'] = True
            else:
                module_dict[comp.name]['x'] = None
                module_dict[comp.name]['y'] = None
                module_dict[comp.name]['fixed'] = False

            # add size information
            module_dict[comp.name]['width'] = comp.width
            module_dict[comp.name]['height'] = comp.height
    
            # add type information
            module_dict[comp.name]['type'] = 'comp'

        for via in self.vias:
            module_dict[via.name] = {}
            module_dict[via.name]['x'] = via.position.x - via.size/2.0
            module_dict[via.name]['y'] = via.position.y - via.size/2.0
            module_dict[via.name]['width'] = via.size
            module_dict[via.name]['height'] = via.size
            module_dict[via.name]['fixed'] = True
            module_dict[via.name]['type'] = 'via'

            # extra information needed to produce the via
            module_dict[via.name]['xc'] = via.position.x
            module_dict[via.name]['yc'] = via.position.y
            module_dict[via.name]['drill'] = via.drill
            module_dict[via.name]['size'] = via.size 
        
        for keepout in self.keepouts:
            module_dict[keepout.name] = {}
            module_dict[keepout.name]['x'] = keepout.position.x
            module_dict[keepout.name]['y'] = keepout.position.y
            module_dict[keepout.name]['width'] = keepout.width
            module_dict[keepout.name]['height'] = keepout.height
            module_dict[keepout.name]['fixed'] = True
            module_dict[keepout.name]['type'] = 'keepout'

        return module_dict

    @property 
    def edge(self):
        return self.edge_points

    @edge.setter
    def edge(self, value):
        self.edge_points = value
        self.width = max([point[0] for point in self.edge_points])
        self.height = max([point[1] for point in self.edge_points])
        print 'Detected PCB width=%0.3fmm, height=%0.3fmm' % (self.width, self.height)

    def write_smt_input(self, smt_file_in):
        smt_input = {}
        smt_input['dx'] = self.dx
        smt_input['dy'] = self.dy
        smt_input['width'] = self.width
        smt_input['height'] = self.height
        smt_input['module_dict'] = self.get_module_dict()
        smt_input['routing_list'] = self.routing_list
        smt_input['design_dict'] = self.get_design_dict()

        # add net class list information since this will have to
        # added as the last step
        net_class_list = [net_class.list_form() for 
                          net_class in self.net_class_list]
        smt_input['net_class_list'] = net_class_list

        # add the board edge definition
        smt_input['board_edge'] = [(p.x, p.y) for p in self.edge]

        with open(smt_file_in, 'w') as f:
            json.dump(smt_input, f)

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
    def __init__(self, lib, part, position=None, rotation=None, mode=None):
        # instantiate the part
        self.load_module(lib, part)

        # set the position and rotation
        self.position = position
        if position is not None:
            if rotation is None:
                self.rotation = 0.0
            else:
                self.rotation = rotation
            if mode is None:
                self.mode = 'UL'
            else:
                self.mode = mode
        else:
            self.position = position
            self.rotation = rotation
            self.mode = mode

        # fill up the dictionary defining component pads
        self.pad_dict = {}
        self.populate_pads()

    def load_module(self, lib, part):
        # determine path to KICAD libraries
        KICAD_PATH = os.environ['KICAD_PATH']
        file_ext = 'pretty'

        # determine the appropriate plugin to use for loading the module
        src_libpath = os.path.join(KICAD_PATH, 'modules', lib + '.' + file_ext)
        src_type = pcbnew.IO_MGR.GuessPluginTypeFromLibPath(src_libpath)
        src_plugin = pcbnew.IO_MGR.PluginFind(src_type)

        # load footprint, wrap using kicad-python
        footprint = src_plugin.FootprintLoad(src_libpath, part)
        self.module = Module.wrap(footprint)

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

class NetClass(object):
    def __init__(self, name, description="", clearance=0.2, trace_width=0.25, 
                 via_dia=0.8, via_drill=0.4, uvia_dia=0.3, uvia_drill=0.1):

        if name=='Default':
            raise Exception('Naming a NetClass "Default" is not allowed.')

        self.name = name
        self.description = description
        self.clearance = clearance
        self.trace_width = trace_width
        self.via_dia = via_dia
        self.via_drill = via_drill
        self.uvia_dia = uvia_dia
        self.uvia_drill = uvia_drill

        self.nets = []

    def add(self, net_or_nets):
        if isinstance(net_or_nets, list):
            self.nets.extend(net_or_nets)
        else:
            self.nets.append(net_or_nets)

    def list_form(self):
        # Populate net class options
        cmd = ['net_class', self.name, '"'+self.description+'"',
            ['clearance', str(self.clearance)],
            ['trace_width', str(self.trace_width)],
            ['via_dia', str(self.via_dia)],
            ['via_drill', str(self.via_drill)],
            ['uvia_dia', str(self.uvia_dia)],
            ['uvia_drill', str(self.uvia_drill)]]    
        
        # Add connected nets to command
        for net in self.nets:
            cmd.append(['add_net', net])

        # Return the full command
        return cmd

class PcbVia(object):
    def __init__(self, position, size, drill):
        self.position = position
        self.size = size
        self.drill = drill
        self.prefix = 'V'

class PcbKeepout(object):
    def __init__(self, position, width, height):
        self.position = position
        self.width = width
        self.height = height
        self.prefix = 'K'
