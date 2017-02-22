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
import pcbnew

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

class Footprint(object):
    @staticmethod
    def load(lib, part):
        KISYSMOD = os.environ['KISYSMOD']
        file_ext = 'pretty'

        src_libpath = os.path.join(KISYSMOD, lib + '.' + file_ext)
        src_type = pcbnew.IO_MGR.GuessPluginTypeFromLibPath(src_libpath)
        src_plugin = pcbnew.IO_MGR.PluginFind(src_type)

        return Module.wrap(src_plugin.FootprintLoad(src_libpath, part))

    @staticmethod
    def random():
        KISYSMOD = os.environ['KISYSMOD']
        
        mod_list = ['Capacitors_THT.pretty',
                    'Diodes_THT.pretty', 
                    'Inductors_THT.pretty',
                    'Resistors_THT.pretty']

        lib = random.choice(mod_list)
        lib_full = os.path.join(KISYSMOD, lib)
        part = random.choice(os.listdir(lib_full))

        lib = os.path.splitext(lib)[0]
        part = os.path.splitext(part)[0]

        return Footprint.load(lib, part)
