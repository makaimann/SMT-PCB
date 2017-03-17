#!/usr/bin/env python

# Steven Herbst
# sherbst@stanford.edu
#
# CS448H Winter 2017

# Demo code to generate Arduino Uno Rev3

# SMT-PCB specific imports
from kicad.point import Point
from mycad import PcbDesign, PcbVia
from parts import *
import sys


def main():
    # read command-line arguments
    json_fname = sys.argv[1]
    pcb_fname = sys.argv[2]

    # build Arduino design
    simple = Simple(json_fname, pcb_fname)
    simple.compile()


class Simple:

    def __init__(self, json_fname, pcb_fname):
        # Files used for I/O
        self.json_fname = json_fname
        self.pcb_fname = pcb_fname

        # Create PCB
        self.pcb = PcbDesign(pcb_fname, dx=0.1, dy=0.1, def_route_const=0.5)
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

        print 'Adding mounting holes'
        drill = 1
        size = 2
        width = 20
        height = 20
        self.pcb.add(
            PcbVia(
                position=Point(
                    size,
                    size),
                size=size,
                drill=drill))
        self.pcb.add(
            PcbVia(
                position=Point(
                    width - size,
                    size),
                size=size,
                drill=drill))
        self.pcb.add(
            PcbVia(
                position=Point(
                    size,
                    height -
                    size),
                size=size,
                drill=drill))
        self.pcb.add(
            PcbVia(
                position=Point(
                    width - size,
                    height - size),
                size=size,
                drill=drill))

        print 'Defining the board edge'
        self.pcb.edge = [
            Point(
                0, 0), Point(
                width, 0), Point(
                width, height), Point(
                    0, height), Point(
                        0, 0)]

        print 'Defining routing constraint'
        #self.pcb.add_pad_constr(r1['2'], r2['1'], 5)

        print 'Compiling PCB'
        self.pcb.compile(smt_file_in=self.json_fname)


if __name__ == '__main__':
    main()
