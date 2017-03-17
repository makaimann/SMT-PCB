#!/usr/bin/env python

# Steven Herbst
# sherbst@stanford.edu
#
# CS448H Winter 2017

# Demo code to generate Freeduino

# SMT-PCB specific imports
from kicad.point import Point

# general imports
import json

# project imports
from kicad.pcbnew.board import Board


def main():
    # load board
    pcb = Board.load('freeduino_edited.kicad_pcb')

    # read board placement from SMT-PCB
    print "Reading output from SMT engine."
    with open('freeduino.json', 'r') as f:
        smt_output = json.load(f)

    # title block center (assuming A4 paper)
    # TODO: handle paper sizes other than A4
    disp_center_x = 297 / 2.0
    disp_center_y = 210 / 2.0

    # try to center components on board
    xmid = 0.5 * smt_output['width']
    x0 = disp_center_x - xmid
    ymid = 0.5 * smt_output['height']
    y0 = disp_center_y - ymid

    # coordinate of board upper left
    board_ul = Point(x0, y0)

    # draw the board edge
    width = smt_output['width']
    height = smt_output['height']
    cx = width / 2
    cy = height / 2

    bufx = 0.5
    bufy = 0.5

    edge = []
    for x, y in smt_output['board_edge']:
        if x < cx:
            x = x - bufx
        else:
            x = x + bufx
        if y < cy:
            y = y - bufy
        else:
            y = y + bufy

        edge.append(Point(x, y) + board_ul)

    print edge

    pcb.add_polyline(edge, layer='Edge.Cuts')

    pcb.save('freeduino_final.kicad_pcb')


if __name__ == '__main__':
    main()
