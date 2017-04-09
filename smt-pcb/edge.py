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
    parser.add_argument('--fill_top', default='GND')
    parser.add_argument('--fill_bot', default='GND')
    parser.add_argument('--bufx', type=float, default=0.5)
    parser.add_argument('--bufy', type=float, default=0.5)
    args = parser.parse_args()

    # read board placement from SMT-PCB
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

    # write board edge back
    with open(args.json, 'w') as f:
        json.dump(json_dict, f, indent=2, sort_keys=True)

    # create the new board edge
    edge = [Point(x, y) + board_ul for x, y in board_edge]

    # create zone outline for copper pours
    minx = min([p.x for p in edge])
    maxx = max([p.x for p in edge])
    miny = min([p.y for p in edge])
    maxy = max([p.y for p in edge])
    ul = Point(minx, miny)
    ur = Point(maxx, miny)
    lr = Point(maxx, maxy)
    ll = Point(minx, maxy)
    outline = [ul, ur, lr, ll]

    # write changes to board
    pcb = Board.load(args.pcb)

    # write edge
    pcb.clearLayer('Edge.Cuts')
    pcb.add_polyline(edge, layer='Edge.Cuts')

    # write zones
    #clearance = max(args.bufx, args.bufy)
    #pcb.add_zone(outline, args.fill_top, 'F.Cu', clearance)
    #pcb.add_zone(outline, args.fill_bot, 'B.Cu', clearance)

    pcb.save()


if __name__ == '__main__':
    main()
