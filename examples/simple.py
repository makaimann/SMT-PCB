#!/usr/bin/env python2

# Steven Herbst
# sherbst@stanford.edu
#
# CS448H Winter 2017

# Demo code to generate Arduino Uno Rev3

# general imports
import argparse

# SMT-PCB specific imports
from kicad.point import Point
from mycad import PcbDesign
from parts import *


def main():
    # load command-line arguments
    parser = argparse.ArgumentParser()
    parser.add_argument('--json')
    parser.add_argument('--pcb')
    parser.add_argument('--fast', action='store_true')
    parser.add_argument('--dx', type=float, default=0.1)
    parser.add_argument('--dy', type=float, default=0.1)
    args = parser.parse_args()

    # build Arduino design
    simple = Simple(args)
    simple.compile()


class Simple:

    def __init__(self, args):
        # Files used for I/O
        self.json_fname = args.json
        self.pcb_fname = args.pcb

        # Create PCB
        if args.fast:
            self.pcb = PcbDesign(self.pcb_fname, dx=args.dx, dy=args.dy, 
                                 def_route_constr=1.0, use_def_constr=False)
        else:
            self.pcb = PcbDesign(self.pcb_fname, dx=args.dx, dy=args.dy, 
                                 def_route_constr=0.5, use_def_constr=True)

        # Create the title block
        self.pcb.title = 'SMT-PCB Simple'
        self.pcb.comments = ['Authors:',
                             'Steven Herbst <sherbst@stanford.edu>',
                             'Makai Mann <makaim@stanford.edu>']
        self.pcb.company = 'Stanford University'
        self.pcb.revision = '1'

    def compile(self):

        print 'Adding components'
        r1 = Resistor('VDD', 'V1')
        r2 = Resistor('V1', 'V2')
        r3 = Resistor('V2', 'V3')
        r4 = Resistor('V3', 'GND')
        self.pcb.add(r1, r2, r3, r4)

        width = 20.0
        height = 20.0
        print 'Defining the board edge'
        self.pcb.edge = [
            Point(
                0, 0), Point(
                width, 0), Point(
                width, height), Point(
                    0, height), Point(
                        0, 0)]

        print 'Compiling PCB'
        self.pcb.compile(json_file=self.json_fname)


if __name__ == '__main__':
    main()
