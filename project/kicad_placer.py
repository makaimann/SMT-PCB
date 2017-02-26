#!/usr/bin/env python

# Steven Herbst
# sherbst@stanford.edu
#
# CS448H Winter 2017

# Code to automatically place components based on input from SMT-PNR

from kicad.pcbnew.board import Board
from kicad.point import Point
from ast import literal_eval

# title block center
# TODO: read this from the title block object
disp_center_x = 150.0
disp_center_y = 100.0

# read board placement from SMT-PCB
width, height, mesh = literal_eval(open('out.dict','r').read())

# load board
pcb = Board.load('test.kicad_pcb')

# TODO: clean up interface for reading dx and dy variables
line4 = open('in.dict').read().split('\n')[3]
dx, dy = literal_eval(line4)

# try to center components on board
xmid = 0.5*dx*(width-1)
x0 = disp_center_x - xmid
ymid = 0.5*dy*(height-1)
y0 = disp_center_y - ymid

# place all components
for key,val in mesh.items():
    x,y = key
    mod = pcb.modules[val]
    mod.position = mod.position + Point(x*dx+x0, y*dy+y0) - mod.boundingBox.ul

# save board
pcb.save()
