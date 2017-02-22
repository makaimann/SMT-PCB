#!/usr/bin/env python

# Steven Herbst
# sherbst@stanford.edu
#
# CS448H Winter 2017

# Demo code to automatically place components based on input from SMT-PNR

from mycad import BoardTools
from kicad.pcbnew.board import Board
from kicad.point import Point
from ast import literal_eval
import uuid

#TODO: figure out how to import from NetClass
trace_gap = 0.2
trace_width = 0.25
via_dia = 0.8

# gap between placed parts
part_gap = 1.0

# from SMT-PNR
width, height, mesh = literal_eval(open('out.dict','r').read())
# load board
pcb = Board.load('test.kicad_pcb')

# TODO: don't make dx and dy hard-coded
dx = 2.5
dy = 2.5

# try to center components on board
xmid = 0.5*dx*width
x0 = 150.0-xmid
ymid = 0.5*dy*height
y0 = 100.0-ymid

# place all components
for key,val in mesh.items():
    x,y = key
    mod = pcb.modules[val]
    mod.position = mod.position + Point(x*dx+x0, y*dy+y0) - mod.boundingBox.ul

# draw the edge
pcb_bbox = pcb.boundingBox
edge = [pcb_bbox.ll, pcb_bbox.ul, pcb_bbox.ur, pcb_bbox.lr, pcb_bbox.ll]
pcb.add_polyline(edge, layer='Edge.Cuts')

# save board
pcb.save()

# create a dictionary in which each net name maps to a list of pads
# the bounds of each pad are relative to its center
net_dict = {}
for module in pcb.modules:
    for pad in module.pads:
        netname = pad.net.name
        pad_bbox = pad.boundingBox
        
        # compute relative positions of the bounding box corners
        center = pad_bbox.center - pcb_bbox.ul
        ll = pad_bbox.ll - pad_bbox.center
        ul = pad_bbox.ul - pad_bbox.center
        ur = pad_bbox.ur - pad_bbox.center
        lr = pad_bbox.lr - pad_bbox.center

        # store in the format accepted by autorouter
        edgelist = [ll,ul,ur,lr,ll]
        edgelist = [(val.x,val.y) for val in edgelist]
        padval=(0, pad.clearance, (center.x, center.y, 0), edgelist)

        # add netname to dictionary for autorouter
        if str(netname) != '':
            if netname not in net_dict:
                net_dict[netname] = []
            net_dict[netname].append(padval)
        else:
            net_dict[uuid.uuid4()] = [padval]

# write net_dict to file for autorouter
with open('netlist.pcb', 'w') as f:
    f.write(repr([int(pcb_bbox.width),int(pcb_bbox.height),2])+'\n')
    for net,pad_list in net_dict.items():
        line = [trace_width/2.0,via_dia/2.0,trace_gap,[]]
        for pad in pad_list:
            line[-1].append(pad)
        f.write(repr(line)+'\n')
