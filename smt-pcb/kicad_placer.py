#!/usr/bin/env python

# Steven Herbst
# sherbst@stanford.edu
#
# CS448H Winter 2017

# Code to automatically place components based on input from SMT-PNR

# general imports
from ast import literal_eval
import sys

# project imports
from kicad.pcbnew.board import Board
from kicad.point import Point
from mycad import BoardTools

def main():
    # read command-line arguments
    dict_fname = sys.argv[1]
    pcb_fname = sys.argv[2]

    # title block center
    # TODO: read this from the title block object
    disp_center_x = 150.0
    disp_center_y = 100.0
    
    # read board placement from SMT-PCB
    print "Reading output from SMT engine."
    with open(dict_fname, 'r') as f:
        smt_output = literal_eval(f.read())
    
    # load board
    pcb = Board.load(pcb_fname)
    
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
            # determine rotation
            if module['rotation'] is not None:
                pcb.modules[name].rotation = module['rotation']
            if module['x'] is not None and module['y'] is not None:
                pcb.modules[name].position =                \
                    pcb.modules[name].position              \
                    + Point(module['x'], module['y'])       \
                    + BoardUpperLeft                        \
                    - pcb.modules[name].boundingBox.ul
        elif module['type'] == 'via':
            pass
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

if __name__=='__main__':
    main()
