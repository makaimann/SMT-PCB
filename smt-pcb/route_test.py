#!/usr/bin/env python

# Steven Herbst
# sherbst@stanford.edu
#
# CS448H Winter 2017

# Demo code to automatically place components based on input from SMT-PNR

from itertools import izip, islice
from kicad.pcbnew.board import Board
from kicad.point import Point
from ast import literal_eval


def main():
    # via drill size isn't included in the routing file,
    # so we have to specify it here
    via_drill = 0.4

    # load board
    pcb = Board.load('test.kicad_pcb')
    pcb_ul = pcb.boundingBox.ul

    # from Python-PCB
    with open('out.pcb', 'r') as f:
        lines = f.readlines()
        lines = lines[:-1]  # remove the last []

        for line in reversed(lines):
            track = literal_eval(line.strip())
            if track == []:
                break

            radius, via, gap, terminals, paths = track
            paths = split_paths(paths)

            # determine trace width
            trace_width = 2.0 * radius
            [trace_width]

            # determine via diameter
            via_dia = 2.0 * via

            # implement each path
            for path in paths:
                if path[0][2] == path[-1][2]:
                    draw_path(pcb, trace_width, pcb_ul, path)
                if path[0][2] != path[-1][2]:
                    draw_via(pcb, via_dia, via_drill, pcb_ul, path[0])

    # save board
    pcb.save()


def draw_path(pcb, trace_width, pcb_ul, path):
    coords = [Point(coord[0], coord[1]) + pcb_ul for coord in path]
    trace_layer = get_layer(path[0][2])
    pcb.add_track(coords, layer=trace_layer, width=trace_width)


def draw_via(pcb, via_dia, via_drill, pcb_ul, point):
    point = Point(point[0], point[1]) + pcb_ul
    pcb.add_via(point, size=via_dia, drill=via_drill)


def get_layer(depth):
    if depth == 0:
        return 'F.Cu'
    elif depth == 1:
        return 'B.Cu'
    else:
        raise Exception('Invalid layer.')

# split_paths taken from Python-PCB


def split_paths(paths):
    new_paths = []
    for path in paths:
        new_path = []
        for a, b in izip(path, islice(path, 1, None)):
            _, _, za = a
            _, _, zb = b
            if za != zb:
                if new_path:
                    new_path.append(a)
                    new_paths.append(new_path)
                new_paths.append([a, b])
                new_path = []
            else:
                new_path.append(a)
        if new_path:
            new_path.append(path[-1])
            new_paths.append(new_path)
    return new_paths


if __name__ == '__main__':
    main()
