#!/usr/bin/env python3

# Steven Herbst
# sherbst@stanford.edu

# Library enables user to parse kicad_pcb file

import re
import argparse
import json

import numpy as np

from tinytree import Tree
from math import radians
from itertools import chain

from pcbgeom import *
from pcblib import *

def main():
    # Parse command-line arguments
    parser = argparse.ArgumentParser(description='Convert kicad_pcb to JSON.')
    parser.add_argument('infile')
    parser.add_argument('outfile', nargs='?', default='out.json')
    args = parser.parse_args()

    # Parse file
    pcb = PcbParser(args.infile)

    # Parse module information
    modules = parseModules(pcb.tree)

    # Parse border information
    bbox = parseBorder(pcb.tree)
        
    # Shift all parts to be relative to the lower left corner of the board
    for mod in modules:
        mod.pos -= bbox.ll

    # Create dictionary for storing the design information
    border = Border(bbox.width, bbox.height)
    design = Design(modules, border)

    # Print design information to JSON file
    with open(args.outfile, 'w') as f:
        json.dump(design.toDict(), f, indent=2, sort_keys=True)

def parseModule(mcmd):
    mod = Module()

    # add reference designator
    mod.reference = mcmd.findCmd('fp_text', 'reference').children[2].value

    # indicate placement side
    side = mcmd.findCmd('layer').children[1].value
    if side.lower().startswith('f') or \
       side.lower().startswith('t') or \
       side.lower().startswith('v'):
        mod.mirror = False
    elif side.lower().startswith('b') or \
         side.lower().startswith('h'):
        mod.mirror = True
    else:
        raise Exception('Unknown board side: ' + side)

    # parse X,Y location
    at = mcmd.findCmd('at').children
    mod.pos = cmd2p(at)

    # parse rotation
    if 3 < len(at):
        mod.theta = radians(float(at[3].value))
    else:
        mod.theta = 0

    return mod

def parseFpCmd(fpcmd, mod=None):
    # parse the type of command
    fp_type = fpcmd.children[0].value

    # parse the layer
    layer = fpcmd.findCmd('layer').children[1].value

    # read all points in command
    if fp_type == 'fp_circle':
        entries = [fpcmd.findCmd('center').children, fpcmd.findCmd('end').children]
    elif fp_type == 'fp_poly':
        entries = [xy.children for xy in fpcmd.findCmd('pts').findCmdAll('xy')]
    elif fp_type in ['gr_line', 'fp_line', 'fp_arc']:
        entries = [fpcmd.findCmd('start').children, fpcmd.findCmd('end').children]
    else:
        raise Exception('Unsupported FP command.')
    
    # parse points
    points = [cmd2p(entry) for entry in entries]
    points = np.hstack(points)

    # mirror points if necessary
    if mod is not None and mod.mirror:
        points = invertY(points)

    # if a circle, compute the lower left and upper right corners of the bounding box
    if fp_type == 'fp_circle':
        center = points[:, 0]
        end = points[:, 1]
        r = distPoints(center, end)
        points = formRect(2*r, 2*r) - xy2p(r, r) + center

    return FpCmd(points, layer)

def parsePad(pcmd, mod):
    pad = Pad()

    # read out pad name
    pad.padname = pcmd.children[1].value

    # read out pad type
    ptype = pcmd.children[2].value
    pad.through = (ptype == 'thru_hole')

    # read out pad center
    at = pcmd.findCmd('at').children
    pad.pos = cmd2p(at)

    # mirror if necessary
    if mod.mirror:
        pad.pos = invertY(pad.pos)

    # read out pad rotation
    if 3 < len(at):
        pad.theta = radians(float(at[3].value))
    else:
        pad.theta = 0
    pad.theta -= mod.theta

    # read out pad size
    size = pcmd.findCmd('size').children
    w = float(size[1].value)
    h = float(size[2].value)

    # form bounding pad rectangle
    pad.rect = formRect(w, h) - xy2p(w/2.0, h/2.0)
    pad.rect = rotate(pad.rect, pad.theta)
    pad.rect = pad.rect + pad.pos
    pad.bbox = BoundingBox(pad.rect)

    # generate lower left and upper left corners
    pad.pos= pad.bbox.ll
    pad.width = pad.bbox.width
    pad.height = pad.bbox.height

    # read out net name
    net = pcmd.findCmd('net')
    if net:
        pad.netname = net.children[2].value
    else:
        pad.netname = None

    return pad

def parseModules(tree):
    modules = []

    for mcmd in tree.findCmdAll('module'):
        # create new module and add to the toplevel dictionary
        mod = parseModule(mcmd)

        # create the bounding box to store component extents
        mbox = BoundingBox()

        # parse lines, arcs, and circles
        for fp_type in ['fp_line', 'fp_arc', 'fp_circle', 'fp_poly']:
            for fpcmd in mcmd.findCmdAll(fp_type):
                fp = parseFpCmd(fpcmd, mod)

                # skip FP commands on the border layer since they will be handled separately
                if fp.layer == 'Edge.Cuts':
                    continue

                # Add points to the bounding box of the part 
                mbox.add(fp.points)
            
        # parse pads
        mod.pads = []
        for pcmd in mcmd.findCmdAll('pad'):
            pad = parsePad(pcmd, mod)
            mod.pads.append(pad)
            mbox.add(pad.rect)

        # Don't add an empty component to the modules list
        if mbox.empty:
            continue
        else:
            modules.append(mod)

        # update pad positions to be relative to the lower left corner
        for pad in mod.pads:
            pad.pos -= mbox.ll
        
        # define location of lower left corner (after rotation and mirroring, if desired)
        mod.pos = transform(mbox.ll, mod.theta, mod.mirror, mod.pos)

        # write extents
        mod.width = mbox.width
        mod.height = mbox.height

    return modules

def parseBorder(tree):

    bbox = BoundingBox()

    # look for all fp commands on Edge.Cuts
    for m in tree.findCmdAll('module'):
        for fp_type in ['fp_line', 'fp_arc', 'fp_circle', 'fp_poly']:
            for fpcmd in m.findCmdAll(fp_type):
                fp = parseFpCmd(fpcmd)

                if fp.layer != 'Edge.Cuts':
                    continue

                mod = parseModule(fpcmd.parent)
                fp.points = rotate(fp.points, mod.theta) + mod.pos
                bbox.add(fp.points)

    # look for all gr_lines on Edge.Cuts
    for grcmd in tree.findCmdAll('gr_line'):
        gr = parseFpCmd(grcmd)

        if gr.layer != 'Edge.Cuts':
            continue

        bbox.add(gr.points)

    return bbox

def cmd2p(cmd):
    return xy2p(float(cmd[1].value), -float(cmd[2].value))

class PcbParser:

    def __init__(self, infile):
        self.infile = infile
        self.tree = PcbParser.read_pcb_file(self.infile)

    @staticmethod
    def read_pcb_file(infile):
        # parse Lisp-like syntax
        # modified from: http://norvig.com/lispy2.html

        # read the *.kicad_pcb file token by token
        with open(infile, 'r') as f:
            inport = InPort(f)

            # Read the first token to start parsing
            token1 = inport.next_token()
    
            # Create new tree
            if token1 is None:
                return None
            if token1 is not None:
                return PcbParser.parse_recursive(inport, token1, None)

    @staticmethod
    def parse_recursive(inport, token, parent):
        # If the current token is a left parenthesis,
        # start building a new sub-list
        if token == '(':
            node = PcbTree()
            if parent is not None:
                parent.addChild(node)
            while True:
                token = inport.next_token()
                if token == ')':
                    return node
                else:
                    PcbParser.parse_recursive(inport, token, node)
        # Otherwise the token must be an atom,
        # unless there is a syntax error
        elif token == ')':
            raise Exception('Unexpected )')
        elif token is None:
            raise Exception('Unexpected EOF')
        else:
            node = PcbTree()
            node.value = token
            parent.addChild(node)

class InPort:
    # class used to parse Lisp-like syntax
    # modified from: http://norvig.com/lispy2.html

    # Tokenizer splits on parentheses but respects double-quoted strings
    # TODO: handle multi-line quotes
    tokenizer = r'''\s*([()]|"[^"]*"|[^\s(")]*)(.*)'''

    def __init__(self, file):
        self.file = file
        self.line = ''

    def next_token(self):
        while True:
            if self.line == '':
                self.line = self.file.readline()
            if self.line == '':
                return None
            token, self.line = re.match(InPort.tokenizer, self.line).groups()
            if token != '':
                return token

class PcbTree(Tree):
    # findAll modified slightly from tinytree
    # to produce an iterator
    def findAll(self, *func, **kwargs):
        for i in self.children:
            if kwargs:
                kwpass = False
                for k, v in list(kwargs.items()):
                    if hasattr(i, k):
                        if not getattr(i, k) == v:
                            break
                    else:
                        break
                else:
                    kwpass = True
            else:
                kwpass = True
            if kwpass:
                if all([x(i) for x in func]):
                    yield i

    def find(self, *func, **kwargs):
        return next(self.findAll(*func, **kwargs), None)

    def findCmdAll(self, *args):
        def key(tree):
            if tree.children and len(tree.children) >= len(args):
                for child, arg in zip(tree.children, args):
                    if not hasattr(child, 'value') or child.value != arg:
                        return False
                return True
            else:
                return False 

        return self.findAll(key)

    def findCmd(self, *args):
        return next(self.findCmdAll(*args), None)

    def __str__(self):
        return PcbTree.to_str(self, level=0)

    @staticmethod
    def to_str(node, level):
        # set the indent level for readability
        indent = ' ' * level
        
        if hasattr(node, 'value'):
            return indent + node.value + '\n'
        else:
            out = indent + '(\n'
            for e in node.children:
                out = out + PcbTree.to_str(e, level + 1)
            out = out + indent + ')\n'
            return out

class FpCmd:
    def __init__(self, points, layer):
        self.points = points
        self.layer = layer

if __name__ == '__main__':
    main()
