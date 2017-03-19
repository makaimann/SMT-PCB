#!/usr/bin/env python2

# Steven Herbst
# sherbst@stanford.edu
#
# CS448H Winter 2017

# Code to expand the board edge by a certain amount

# general imports
import json
import argparse

# project imports
from kicad.pcbnew.board import Board
from kicad.point import Point
from board_tools import BoardTools


def main():
    # load command-line arguments
    parser = argparse.ArgumentParser()
    parser.add_argument('--json')
    parser.add_argument('--pcb')
    parser.add_argument('--bufx', type=float, default=0.5)
    parser.add_argument('--bufy', type=float, default=0.5)
    args = parser.parse_args()

    # read board placement from SMT-PCB
    print "Reading output from SMT engine."
    with open(args.json, 'r') as f:
        json_dict = json.load(f)

    # get the board edge
    board_edge = json_dict['board_edge']
    board_ul = Point(*BoardTools.get_board_ul(board_edge))

    # compute board center
    cx, cy = BoardTools.get_board_center(board_edge)

    edge = []
    for idx, (x, y) in enumerate(board_edge):
        if x < cx:
            px = x - args.bufx
        else:
            px = x + args.bufx
        if y < cy:
            py = y - args.bufy
        else:
            py = y + args.bufy

        board_edge[idx] = (px, py)

    # write change to board
    pcb = Board.load(args.pcb)
    pcb.clearLayer('Edge.Cuts')
    edge = [Point(x, y) + board_ul for x, y in board_edge]
    pcb.add_polyline(edge, layer='Edge.Cuts')
    pcb.save()


if __name__ == '__main__':
    main()
