#!/usr/bin/env python

# Steven Herbst
# sherbst@stanford.edu
#
# CS448H Winter 2017

# Code to automatically place components based on input from SMT-PNR

# general imports
from ast import literal_eval
import sys
import json
import math

# project imports
from kicad.pcbnew.board import Board
from kicad.pcbnew.via import Via
from kicad.point import Point
from mycad import BoardTools

def main():
    # read command-line arguments
    json_fname = sys.argv[1]
    pcb_fname = sys.argv[2]

    # read board placement from SMT-PCB
    print "Reading output from SMT engine."
    with open(json_fname, 'r') as f:
        smt_output = json.load(f)

    # load board
    pcb = Board.load(pcb_fname)
   
    # title block center (assuming A4 paper)
    # TODO: handle paper sizes other than A4
    disp_center_x = 297/2.0
    disp_center_y = 210/2.0
    
    # try to center components on board
    xmid = 0.5*smt_output['width']
    x0 = disp_center_x - xmid
    ymid = 0.5*smt_output['height']
    y0 = disp_center_y - ymid

    # coordinate of board upper left
    BoardUpperLeft = Point(x0, y0)
    
    # place all components
    print "Placing all components."
    for name, module in smt_output['module_dict'].items():
        if module['type'] == 'comp':
            # set rotation
            rot = module['rotation']
            pcb.modules[name].rotation = rot

            # make the buffer vector
            if isclose(rot, 0) or isclose(rot, math.pi):
                BufferSpace = Point(module['bufx'], module['bufy'])
            elif isclose(rot, math.pi/2) or isclose(rot, 3*math.pi/2):
                BufferSpace = Point(module['bufy'], module['bufx'])
            else:
                raise Exception("Can't determine rotation.")

            # set position
            pcb.modules[name].position =                \
                pcb.modules[name].position              \
                + Point(module['x'], module['y'])       \
                + BufferSpace                           \
                + BoardUpperLeft                        \
                - pcb.modules[name].boundingBox.ul
        elif module['type'] == 'via':
            coord = Point(module['xc'], module['yc']) + BoardUpperLeft
            via = Via(coord=coord, diameter=module['size'], drill=module['drill'])
            pcb.add(via)
        elif module['type'] == 'keepout':
            pass
        else:
            raise Exception('Unimplemented component type.')
 
    # draw the board edge
    edge = [Point(x,y)+BoardUpperLeft for x,y in smt_output['board_edge']]
    pcb.add_polyline(edge, layer='Edge.Cuts')
            
    # save board
    print "Saving PCB file."
    pcb.save()
    
    # add nets and net classes to PCB design
    print "Adding nets and net classes to the PCB design"
    BoardTools.add_nets(smt_output['design_dict'], smt_output['net_class_list'], pcb_fname, pcb_fname)

def isclose(a, b, tol=1e-3):
    return abs(a-b) <= tol

if __name__=='__main__':
    main()
