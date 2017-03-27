#!/usr/bin/env python2

import subprocess
import argparse
import os
import os.path
import time

from pcbparser import PcbParser
from kicad.pcbnew.board import Board
from kicad.point import Point

def main():
    # load command-line arguments
    parser = argparse.ArgumentParser()
    parser.add_argument('--pcb')
    parser.add_argument('--ses')
    args = parser.parse_args()

    # parse the session file
    tree = PcbParser.read_pcb_file(args.ses)
    routes = next(val for val in tree if val[0] == 'routes')
    out = next(val for val in routes if val[0] == 'network_out')
    
    # load board
    print 'Loading PCB file.'
    pcb = Board.load(args.pcb)

    # create nets
    make_nets(pcb, out)

    # save board
    print 'Saving PCB file.'
    pcb.save()

def make_nets(pcb, out):
    out = [x for x in out[1:] if x[0]=='net']
    for entry in out:
        net = entry[1]
        wires = [x for x in entry[2:] if x[0]=='wire']
        for wire in wires:
            paths = [x for x in wire[1:] if x[0]=='path']
            for path in paths:
                layer = path[1]
                width = float(path[2])/1e4
                coords = [Point(sesx(x),sesy(y)) for x,y in chunks(path[3:], 2)]
                pcb.add_track(coords, layer, width, net)
              
def chunks(l, n=2):
    """
    Yield successive n-sized chunks from l.
    http://stackoverflow.com/questions/312443/how-do-you-split-a-list-into-evenly-sized-chunks
    """
    for i in range(0, len(l), n):
        yield l[i:i + n]

def sesx(x):
    return float(x)/1e4
def sesy(y):
    return -float(y)/1e4

if __name__ == '__main__':
    main()
