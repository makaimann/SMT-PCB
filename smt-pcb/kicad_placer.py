#!/usr/bin/env python2

# Steven Herbst
# sherbst@stanford.edu
#
# CS448H Winter 2017

# Code to automatically place components based on input from SMT-PNR

# general imports
import json
import argparse
from math import degrees

# project imports
from kicad.pcbnew.board import Board
from kicad.point import Point
from board_tools import BoardTools


def main():
    # load command-line arguments
    parser = argparse.ArgumentParser()
    parser.add_argument('--json')
    parser.add_argument('--pcb')
    args = parser.parse_args()

    # read board placement from SMT-PCB
    print "Reading output from SMT engine."
    with open(args.json, 'r') as f:
        json_dict = json.load(f)

    # load board
    print 'Loading PCB file.'
    pcb = Board.load(args.pcb)

    # move parts to specified locations
    print 'Placing all components.'
    place_parts(json_dict, pcb)

    # draw board edge
    print 'Drawing board edge.'
    draw_board_edge(json_dict, pcb)

    # save board
    print 'Saving PCB file.'
    pcb.save()

    # add net and net class information
    print 'Adding nets and net classes to the PCB design.'
    BoardTools.add_nets(
        json_dict['design_dict'],
        json_dict['net_class_list'],
        args.pcb,
        args.pcb)


def place_parts(json_dict, pcb):
    # compute upper left corner of board
    board_ul = Point(*BoardTools.get_board_ul(json_dict['board_edge']))

    # place all components
    for name, module in json_dict['module_dict'].items():
        if module['type'] == 'comp':
            # set rotation
            rot = module['rotation']
            pcb.modules[name].rotation = rot

            # make the buffer vector
            if round(degrees(rot)) in [0, 180]:
                buf_space = Point(module['bufx'], module['bufy'])
            elif round(degrees(rot)) in [90, 270]:
                buf_space = Point(module['bufy'], module['bufx'])
            else:
                raise Exception("Can't determine rotation.")

            # set position
            pcb.modules[name].position =          \
                pcb.modules[name].position        \
                + Point(module['x'], module['y']) \
                + buf_space                       \
                + board_ul                        \
                - pcb.modules[name].boundingBox.ul

        elif module['type'] == 'keepout':
            pass
        else:
            raise Exception('Unimplemented component type: ' +
                            str(module['type']))


def draw_board_edge(json_dict, pcb):
    # compute upper left corner of board
    board_ul = Point(*BoardTools.get_board_ul(json_dict['board_edge']))

    # draw edge
    edge = [Point(x, y) + board_ul for x, y in json_dict['board_edge']]
    pcb.add_polyline(edge, layer='Edge.Cuts')


if __name__ == '__main__':
    main()
