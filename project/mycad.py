# Steven Herbst
# sherbst@stanford.edu
#
# CS448H Winter 2017

# Library enables user to instantiate new modules from KiCAD library

import os
import re
import random
from pyparsing import OneOrMore, nestedExpr
from kicad.pcbnew.module import Module
from kicad.pcbnew.board import Board 
import pcbnew
import math

class PcbParser(object):
    @staticmethod
    def formatFlat(s):
        s = ' '.join(s)
        return '(' + s + ')'

    @staticmethod
    def format(s,level=0):
        # set the indent level for readability
        indent = ' '*level

        if isinstance(s,str):
            return indent + s + '\n'
        elif all(isinstance(x,str) for x in s):
            return indent + PcbParser.formatFlat(s) + '\n'
        else:
            out = indent + '(' + s[0] + '\n'
            for e in s[1:]:
                out = out + PcbParser.format(e, level+1)
            out = out + indent + ')\n'
            return out

    @staticmethod
    def read_pcb_file(infile):
        # read the *.kicad_pcb file
        text = open(infile, 'r').read()
        
        # replace newlines with spaces
        text = text.replace('\n', ' ') 

        # parse Lisp-like syntax
        # http://stackoverflow.com/questions/14058985/parsing-a-lisp-file-with-python
        tree = OneOrMore(nestedExpr()).parseString(text)[0]
    
        return tree

    @staticmethod
    def write_pcb_file(tree, outfile):
        formatted = PcbParser.format(tree)
        open(outfile,'w').write(formatted)

    @staticmethod
    def get_cmd_index(tree, cmd):
        return [x[0] for x in tree].index(cmd)

    @staticmethod
    def get_cmd(tree, cmd):
        return next(x for x in tree if x[0]==cmd)

    @staticmethod
    def add_net_count(tree, net_dict):
        general_cmd = PcbParser.get_cmd(tree, 'general')
        net_cmd = PcbParser.get_cmd(general_cmd, 'nets')
        net_cmd[1] = str(1+len(net_dict))

    @staticmethod
    def add_net_decls(tree, net_dict):
        # build net declarations
        net_decls = []
        for net_name, net_id in net_dict.items():
            net_decls.append(['net', str(net_id), net_name])

        # add them to the PCB file at the right position
        net_cmd_index = PcbParser.get_cmd_index(tree, 'net')
        tree[(net_cmd_index+1):(net_cmd_index+1)] = net_decls

    @staticmethod
    def populate_netclass(tree, net_dict):
        net_class_cmd = PcbParser.get_cmd(tree, 'net_class')
        for net_name in net_dict:
            net_class_cmd.append(['add_net', net_name])
 
    @staticmethod
    def add_nets_to_modules(tree, pcb_dict, net_dict):
        for val in tree:
            if val[0] == 'module':
                PcbParser.add_nets_to_module(val, pcb_dict, net_dict)

    @staticmethod
    def add_nets_to_module(mod, pcb_dict, net_dict):
        for val in mod:
            if val[0:2] == ['fp_text', 'reference']:
                refdes = val[2]
                if refdes not in pcb_dict:
                    return
            elif val[0] == 'pad':
                pad_name = val[1]
                if pad_name in pcb_dict[refdes]:
                    net_name = pcb_dict[refdes][pad_name]
                    net_id = net_dict[net_name]
                    val.append(['net', str(net_id), net_name])
       
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
    def __init__(self, fname, dx=2.5, dy=2.5, width=25.0, height=25.0, smt_file_in='in.dict'):
        self.fname = fname
        self.comp_dict = {}
        self.design_dict = {}
        self.net_dict = {}
        self.dx = dx
        self.dy = dy
        self.width = width
        self.height = height
        self.smt_file_in = smt_file_in

    def add(self, component):
        self.comp_dict[component.name] = component
        self.design_dict[component.name] = {}
        component.parent = self

    def wire(self, net_name, *args):
        if net_name not in self.net_dict:
            self.net_dict[net_name] = set()
        for arg in args:
            arg.wire(net_name)

    def compile(self):
        # add all components to the board and save the result
        pcb = Board()
        for comp in self.comp_dict.values():
            pcb.add(comp.module) 
        pcb.save(self.fname)

        # add all net connections to the board, since this cannot 
        # be accomplished through pcbnew at present
        BoardTools.add_nets(self.design_dict, self.fname, self.fname)
        
        # write input file for SMT solver
        self.write_smt_input()

    def get_graph_struct(self):
        # create a list of lists of connected components
        adj_list = []
        for net_name, comp_set in self.net_dict.items():
            adj_list.append([])
            for comp_name in comp_set:
                adj_list[-1].append(comp_name)
        
        # generate graph_struct needed by SMT solver
        graph_struct = {}
        for adj in adj_list:
            first = adj[0]
            rest = [(x,1) for x in adj[1:]]
            if first not in graph_struct:
                graph_struct[first] = rest
            else:
                graph_struct[first].extend(rest)

        return graph_struct

    def get_place_dict(self):
        place_dict = {}
        for comp_name, comp in self.comp_dict.items():
            width = int(math.ceil(float(comp.width)/self.dx))
            height = int(math.ceil(float(comp.height)/self.dy))
            place_dict[comp_name] = [(width,height), (None, None)]
        return place_dict

    @property 
    def place_dims(self):
        width = int(math.ceil(float(self.width)/self.dx))
        height = int(math.ceil(float(self.height)/self.dy))
        return (width, height)

    def write_smt_input(self):
        with open(self.smt_file_in, 'w') as f:
            f.write(repr(self.place_dims)+'\n')
            f.write(repr(self.get_graph_struct())+'\n')
            f.write(repr(self.get_place_dict())+'\n')
            f.write(repr((self.dx, self.dy))+'\n')

class PcbPad(object):
    def __init__(self, pad):
        self.pad = pad
        self.name = self.pad.name

    def wire(self, net_name):
        comp = self.parent
        pcb = comp.parent
        pcb.design_dict[comp.name][self.name] = net_name
        pcb.net_dict[net_name].add(comp.name)

class PcbComponent(object):
    def __init__(self, name, lib, part):
        # instantiate the part
        self.load_module(lib, part)

        # name the part
        self.name = name
        self.module.reference = name
        
        # fill up the dictionary defining component pads
        self.pad_dict = {}
        self.populate_pads()

    def load_module(self, lib, part):
        KISYSMOD = os.environ['KISYSMOD']
        file_ext = 'pretty'

        src_libpath = os.path.join(KISYSMOD, lib + '.' + file_ext)
        src_type = pcbnew.IO_MGR.GuessPluginTypeFromLibPath(src_libpath)
        src_plugin = pcbnew.IO_MGR.PluginFind(src_type)

        self.module = Module.wrap(src_plugin.FootprintLoad(src_libpath, part))

    def populate_pads(self):
        for pad in self.module.pads:
            self.pad_dict[pad.name] = PcbPad(pad)
            self.pad_dict[pad.name].parent = self

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

