#!/usr/bin/env python3

# Steven Herbst
# sherbst@stanford.edu

# Library enables user to parse kicad_pcb file

import re
import argparse
import json
from tinytree import Tree
from math import hypot, radians

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

class BoundingBox:
    def __init__(self):
        inf = float('inf')
        self.xmin = inf
        self.xmax = -inf
        self.ymin = inf
        self.ymax = -inf

    def add(self, x, y):
        if x < self.xmin:
            self.xmin = x
        if x > self.xmax:
            self.xmax = x
        if y < self.ymin:   
            self.ymin = y
        if y > self.ymax:
            self.ymax = y

    @property
    def width(self):
        return self.xmax - self.xmin

    @property
    def height(self):
        return self.ymax - self.ymin

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

        # create the bounding box to store component extents
        box = BoundingBox()
 
        # parse X,Y location
        cmd = m.findCmd('at').children
        module['x0'] = float(cmd[1].value)
        module['y0'] = float(cmd[2].value)

        # parse rotation
        if len(cmd) >= 4:
            # note the minus sign. the convention used in the JSON
            # format is that positive rotation is counterclockwise
            # this is opposite of KiCAD
            theta = -radians(float(cmd[3].value))
        else:
            theta = 0
        module['theta'] = theta

        # parse boundary lines
        for cmd in m.findCmdAll('fp_line'):
            start = cmd.findCmd('start').children
            box.add(float(start[1].value), float(start[2].value))
            end = cmd.findCmd('end').children
            box.add(float(end[1].value), float(end[2].value))

        # parse boundary arcs
        for cmd in m.findCmdAll('fp_arc'):
            start = cmd.findCmd('start').children
            box.add(float(start[1].value), float(start[2].value))
            end = cmd.findCmd('end').children
            box.add(float(end[1].value), float(end[2].value))

        # parse boundary circles
        for cmd in m.findCmdAll('fp_circle'):
            center = cmd.findCmd('center').children
            cx, cy = float(center[1].value), float(center[2].value)
            end = cmd.findCmd('end').children
            ex, ey = float(end[1].value), float(end[2].value)
            r = hypot(ex-cx, ey-cy)
            box.add(cx-r, cy-r)
            box.add(cx+r, cy-r)
            box.add(cx+r, cy+r)
            box.add(cx-r, cy+r)

        # parse pads
        module['pads'] = []
        for cmd in m.findCmdAll('pad'):
            center = cmd.findCmd('at').children
            x = float(center[1].value)
            y = float(center[2].value)
            box.add(x, y)
            net = cmd.findCmd('net')
            if net:
                netname = net.children[2].value
            else:
                netname = None

            module['pads'].append({'netname': netname, 'x': x, 'y': y})

        # write extents
        module['xmin'] = box.xmin
        module['ymin'] = box.ymin
        module['xmax'] = box.xmax
        module['ymax'] = box.ymax

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
        box.add(float(start[1].value), float(start[2].value))
        end = line.findCmd('end').children
        box.add(float(end[1].value), float(end[2].value))

    border = {}
    border['xmin'] = box.xmin
    border['ymin'] = box.ymin
    border['xmax'] = box.xmax
    border['ymax'] = box.ymax

    return border

def main():
    # Parse command-line arguments
    parser = argparse.ArgumentParser(description='Convert kicad_pcb to JSON.')
    parser.add_argument('infile')
    parser.add_argument('outfile', nargs='?', default='out.json')
    args = parser.parse_args()

    # Parse file
    pcb = PcbParser(args.infile)

    # Create dictionary for storing the design information
    json_dict = {}

    # Parse module information
    json_dict['modules'] = parse_modules(pcb.tree)

    # Parse border information
    json_dict['border'] = parse_border(pcb.tree)

    # Print design information to JSON file
    with open(args.outfile, 'w') as f:
        json.dump(json_dict, f, indent=2, sort_keys=True)

if __name__ == '__main__':
    main()
