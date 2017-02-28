#!/usr/bin/env python

# Steven Herbst
# sherbst@stanford.edu
#
# CS448H Winter 2017

# Demo code to generate Arduino Uno Rev3

# SMT-PCB specific imports
from mycad import PcbDesign, NetClass
from parts import *
from math import pi

def main():
    # create object to hold PCB design
    pcb = PcbDesign('test.kicad_pcb', width=10, height=10, dx=1, dy=1)
    
    # LEDs
    pcb.add(Resistor('+5V', 'TXLED_R'))
    pcb.add(Resistor('+5V', 'RXLED_R'))
    pcb.add(LED('TXLED_R', 'TXLED'))
    pcb.add(LED('RXLED_R', 'RXLED'))

    # put the parts on the board and save
    pcb.compile(critical_nets=['+5V'])

if __name__=='__main__':
    main()
