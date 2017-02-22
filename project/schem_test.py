#!/usr/bin/env python

# Steven Herbst
# sherbst@stanford.edu
#
# CS448H Winter 2017

# Demo code to generate a random network of resistor connections

import math
from os.path import splitext
from random import randint, randrange, choice
from mycad import BoardTools, Footprint
from kicad.pcbnew.board import Board

Ndev = 20
Nnet = Ndev
MaxConn = 4

# create devices
pads = []
mod_dict = {}
count = 1
while count < Ndev:
    part = Footprint.random()
    if part.boundingBox.width > 15 or part.boundingBox.height > 15:
        continue
    name = 'U'+str(count)
    count = count+1
    mod_dict[name] = part
    for pad in part.pads:
        pads.append((name,pad.name))

# algorithm to connect random numbers of nets together
pcb_dict = {}
adj_list = []
for net_count in range(1,Nnet+1):
    # can't make another net if there are 0 or 1 pads remaining...
    if len(pads)<2:
        break

    # name the net
    net_name = 'V'+str(net_count)
    
    # decide how many pads we're wiring up
    max_pads = min(MaxConn,len(pads))
    pad_count = randint(2,max_pads)

    # generate sample
    pad_sample = []
    for k in range(pad_count):
        pad_sample.append(pads.pop(randrange(len(pads))))

    # add to pcb_dict
    for name, pin in pad_sample:
        if name not in pcb_dict:
            pcb_dict[name] = {}
        pcb_dict[name][pin] = net_name

    # add to adj_list
    adj_list.append([])
    for name, _ in pad_sample:
        adj_list[-1].append(name)

# generate graph_struct needed by SMT solver
graph_struct = {}
for adj in adj_list:
    first = adj[0]
    rest = [(x,1) for x in adj[1:]]
    if first not in graph_struct:
        graph_struct[first] = rest
    else:
        graph_struct[first].extend(rest)

# generate component size dictionary
comp_dict = {}
dx = 2.5
dy = 2.5
for key,val in mod_dict.items():
    width = int(math.ceil(float(val.boundingBox.width) / dx))
    height = int(math.ceil(float(val.boundingBox.height) / dy))
    comp_dict[key] = [(width,height), (None, None)]

# determine board dimensions
width = int(math.ceil(50.0/dx))
height = int(math.ceil(50.0/dy))
dims = (width, height)

# print structure for SMT-PNR
with open('in.dict', 'w') as f:
    f.write(repr(dims)+'\n')
    f.write(repr(graph_struct)+'\n')
    f.write(repr(comp_dict)+'\n')
    f.write(repr((dx,dy))+'\n')

# put the parts on the board and save
fname = 'test.kicad_pcb'
pcb = Board()
for name in pcb_dict:
    part = mod_dict[name]
    part.reference = name
    pcb.add(part) 
pcb.save(fname)

# add net information to kicad_pcb file
BoardTools.add_nets(pcb_dict, fname, fname)
