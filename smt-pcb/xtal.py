#!/usr/bin/env python

# Steven Herbst
# sherbst@stanford.edu
#
# CS448H Winter 2017

# Demo code to generate Arduino Uno Rev3

# SMT-PCB specific imports
from kicad.point import Point
from mycad import PcbDesign
from parts import *
import sys


def main():
    # read command-line arguments
    json_fname = sys.argv[1]
    pcb_fname = sys.argv[2]

    # build Arduino design
    uno = ArduinoUno(json_fname, pcb_fname)
    uno.compile()


class ArduinoUno:

    def __init__(self, json_fname, pcb_fname):
        # Files used for I/O
        self.json_fname = json_fname
        self.pcb_fname = pcb_fname

        # Convenience variable, stores the top of the board in mils
        # using the coordinate system of the mechanical drawing
        self.top = 2100

        # Create PCB
        self.pcb = PcbDesign(pcb_fname, dx=1, dy=1)
        self.pcb.title = 'SMT-PCB Arduino Uno'
        self.pcb.comments = ['Authors:',
                             'Steven Herbst <sherbst@stanford.edu>',
                             'Makai Mann <makaim@stanford.edu>']
        self.pcb.company = 'Stanford University'
        self.pcb.revision = '1'

    def compile(self):

        # ATMEGA328P, main microcontroller
        print 'Instantiating ATMEGA328P'
        self.inst_atmega328p()

        # Define the board edge
        print 'Defining the board edge'
        self.define_edge()

        # put the parts on the board and save
        print 'Compiling PCB'
        self.pcb.compile(smt_file_in=self.json_fname)

    def inst_atmega328p(self):
        # Main microcontroller
        atmega328 = ATMEGA328P()
        self.pcb.add(atmega328)

        # Crystal circuit
        # Note: this differs from the official schematic,
        # which uses a non-standard footprint
        atmega328.wire_xtal('XTAL1', 'XTAL2')
        xtal = Crystal('XTAL1', 'XTAL2')
        self.pcb.add(xtal)
        self.pcb.add_constr(atmega328['9'], xtal['1'], length=6)
        self.pcb.add_constr(atmega328['10'], xtal['2'], length=6)

    def define_edge(self):
        # create list of points representing the board edge
        points = [(0, 0), (0, 2100), (2540, 2100), (2600, 2040), (2600, 1590),
                  (2700, 1490), (2700, 200), (2600, 100), (2600, 0), (0, 0)]
        points = [Point(x, self.top - y, 'mils') for x, y in points]
        self.pcb.edge = points

        # TODO: automatically determine keepouts
        self.pcb.add(
            PcbKeepout(
                width=mil_to_mm(
                    2700 - 2540),
                height=mil_to_mm(
                    2100 - 1490),
                position=Point(
                    2540,
                    self.top - 2100,
                    'mils')))
        self.pcb.add(
            PcbKeepout(
                width=mil_to_mm(
                    2700 - 2600),
                height=mil_to_mm(
                    200 - 0),
                position=Point(
                    2600,
                    self.top - 200,
                    'mils')))


if __name__ == '__main__':
    main()
