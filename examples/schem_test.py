#!/usr/bin/env python

# Steven Herbst
# sherbst@stanford.edu
#
# CS448H Winter 2017

# Demo code to generate a random network of resistor connections

# general imports
from random import randint, randrange

# SMT-PCB specific imports
from mycad import PcbDesign
from parts import RandomComponent

# parameters of the random netlist generation
Ncomp = 5
Nnet = Ncomp
MaxConn = 4

# create object to hold PCB design
pcb = PcbDesign('test.kicad_pcb')

# create devices
pads = []
count = 1
while count < Ncomp:
    # try to create the component, repeating until it
    # fits the size constraints
    name = 'U' + str(count)
    comp = RandomComponent(name)
    if comp.width > 10 or comp.height > 10:
        continue

    # add to the design
    pcb.add(comp)

    # add all pads to the list for random selection
    for pad in comp.pads:
        pads.append(pad)

    # increment device counter
    count = count + 1

# algorithm to connect random numbers of nets together
for net_count in range(1, Nnet + 1):
    # can't make another net if there are 0 or 1 pads remaining...
    if len(pads) < 2:
        break

    # name the net
    net_name = 'V' + str(net_count)

    # decide how many pads we're wiring up
    max_pads = min(MaxConn, len(pads))
    pad_count = randint(2, max_pads)

    # generate sample
    pad_sample = []
    for k in range(pad_count):
        pad = pads.pop(randrange(len(pads)))
        pcb.wire(net_name, pad)

# put the parts on the board and save
pcb.compile()
