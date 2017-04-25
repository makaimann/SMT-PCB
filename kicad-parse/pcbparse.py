#!/usr/bin/env python3

# Steven Herbst
# sherbst@stanford.edu

# Library enables user to parse kicad_pcb file

import re
import argparse
import json

from tinytree import Tree
from math import radians
from itertools import chain

from pcbgeom import *

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

def parse_modules(tree):
    modules = []

    for m in tree.findCmdAll('module'):
        # create new module and add to the toplevel dictionary
        module = {}
        modules.append(module)

        # add reference designator
        reference = m.findCmd('fp_text', 'reference').children[2].value
        module['reference'] = reference

        # indicate placement side
        side = m.findCmd('layer').children[1].value
        if side == 'F.Cu':
            mirror = False
        else:
            mirror = True
        module['mirror'] = mirror

        # parse X,Y location
        cmd = m.findCmd('at').children
        x0 = float(cmd[1].value)
        y0 = -float(cmd[2].value)

        # parse rotation
        if 3 < len(cmd):
            theta = radians(float(cmd[3].value))
        else:
            theta = 0
        module['theta'] = theta

        # create the bounding box to store component extents
        box = BoundingBox()

        # parse lines, arcs, and circles
        for fp_type in ['fp_line', 'fp_arc', 'fp_circle']:
            for cmd in m.findCmdAll(fp_type):
                # read two points
                if fp_type == 'fp_circle':
                    points = [cmd.findCmd('center').children, cmd.findCmd('end').children]
                else:
                    points = [cmd.findCmd('start').children, cmd.findCmd('end').children]
                
                # parse points
                points = [(float(entry[1].value), -float(entry[2].value)) for entry in points]

                # mirror points if needed
                if mirror:
                    points = [invertY(point) for point in points]

                # if a circle, compute the lower left and upper right corners of the bounding box
                if fp_type == 'fp_circle':
                    center = points[0]
                    end = points[1]
                    r = distPoints(center, end)
                    points = [(center[0]-r, center[1]-r), (center[0]+r, center[1]+r)]
                
                # add points to bounding box
                for point in points:
                    box.add(*point)
            
        # parse pads
        module['pads'] = []
        for cmd in m.findCmdAll('pad'):
            # read out pad center
            point = cmd.findCmd('at').children
            point = (float(point[1].value), -float(point[2].value))
            if mirror:
                point = invertY(point)

            # read out net name
            net = cmd.findCmd('net')
            if net:
                netname = net.children[2].value
            else:
                netname = None

            # create entry for module
            module['pads'].append({'netname': netname, 'x': point[0], 'y': point[1]})

            # add pad to the bounding box
            box.add(*point)

        # find lower left corner of part with respect to original component center
        llx = box.xmin
        lly = box.ymin
        
        # update pad positions to be relative to the lower left corner
        for pad in module['pads']:
            pad['x'] -= llx
            pad['y'] -= lly
        
        # define location of lower left corner (after rotation and mirroring, if desired)
        ll = (llx, lly)
        ll = transform(ll, theta, mirror, x0, y0)
        module['x'], module['y'] = ll[0], ll[1]

        # write extents
        module['width'] = box.width
        module['height'] = box.height

    return modules

def parse_border(tree):

    box = BoundingBox()
    for line in tree.findCmdAll('gr_line'):
        # Check that this line is on the Edge.Cuts layer
        layer = line.findCmd('layer')
        if layer:
            layer = layer.children
            if layer[1].value != 'Edge.Cuts':
                continue

        # Store details
        start = line.findCmd('start').children
        box.add(float(start[1].value), -float(start[2].value))
        end = line.findCmd('end').children
        box.add(float(end[1].value), -float(end[2].value))

    return box

def main():
    # Parse command-line arguments
    parser = argparse.ArgumentParser(description='Convert kicad_pcb to JSON.')
    parser.add_argument('infile')
    parser.add_argument('outfile', nargs='?', default='out.json')
    args = parser.parse_args()

    # Parse file
    pcb = PcbParser(args.infile)

    # Parse module information
    modules = parse_modules(pcb.tree)

    # Parse border information
    box = parse_border(pcb.tree)
    
    # Shift all parts to be relative to the lower left corner of the board
    for module in modules:
        module['x'] -= box.xmin
        module['y'] -= box.ymin

    # Create dictionary for storing the design information
    json_dict = {}
    json_dict['modules'] = modules
    json_dict['border'] = {'width': box.width, 'height': box.height}

    # Print design information to JSON file
    with open(args.outfile, 'w') as f:
        json.dump(json_dict, f, indent=2, sort_keys=True)

if __name__ == '__main__':
    main()
