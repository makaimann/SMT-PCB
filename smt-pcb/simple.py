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
        self.pcb = PcbDesign(pcb_fname, dx=1, dy=1)
        self.pcb.title = 'SMT-PCB Simple'
        self.pcb.comments = ['Authors:', 'Steven Herbst <sherbst@stanford.edu>', 'Makai Mann <makaim@stanford.edu>']
        self.pcb.company = 'Stanford University'
        self.pcb.revision = '1'
 
    def compile(self):   

        print 'Adding components'
        self.pcb.add(Resistor('VDD', 'V1'))
        self.pcb.add(Resistor('V1', 'V2'))
        self.pcb.add(Resistor('V2', 'V3'))
        self.pcb.add(Resistor('V3', 'GND'))

        print 'Adding mounting holes'
        drill = 1
        size = 2
        self.pcb.add(PcbVia(position=Point(2, 2), size=size, drill=drill))
        self.pcb.add(PcbVia(position=Point(12, 2), size=size, drill=drill))
        self.pcb.add(PcbVia(position=Point(2, 12), size=size, drill=drill))
        self.pcb.add(PcbVia(position=Point(12, 12), size=size, drill=drill))

        print 'Defining the board edge'
        self.pcb.edge = [Point(0,0), Point(14,0), Point(14,14), Point(0,14), Point(0,0)]

        print 'Compiling PCB'
        self.pcb.routing_list = []
        self.pcb.compile(smt_file_in=self.json_fname)

if __name__=='__main__':
    main()
