#!/usr/bin/env python

# Steven Herbst
# sherbst@stanford.edu
#
# CS448H Winter 2017

# Code to automatically place components based on input from SMT-PNR

# general imports
from ast import literal_eval

# project imports
from kicad.pcbnew.board import Board
from kicad.point import Point
from mycad import BoardTools

# title block center
# TODO: read this from the title block object
disp_center_x = 150.0
disp_center_y = 100.0

# read board placement from SMT-PCB
smt_output = literal_eval(open('out.dict','r').read())

# load board
fname = 'test.kicad_pcb'
pcb = Board.load(fname)

# try to center components on board
xmid = 0.5*smt_output['width']
x0 = disp_center_x - xmid
ymid = 0.5*smt_output['height']
y0 = disp_center_y - ymid

# place all components
for name, module in smt_output['module_dict'].items():
    # determine rotation
    if module['rotation'] is not None:
        pcb.modules[name].rotation = module['rotation']
    if module['x'] is not None and module['y'] is not None:
        pcb.modules[name].position =                \
            pcb.modules[name].position              \
            + Point(x0+module['x'], y0+module['y']) \
            - pcb.modules[name].boundingBox.ul

# save board
pcb.save()

# add net classes due to a bug in the KiCAD Save() routing
BoardTools.add_net_classes(smt_output['net_class_list'], fname, fname)
