#!/usr/bin/env python3

# Makai Mann (makaim@stanford.edu)
# Steven Herbst (sherbst@stanford.edu)

# CS448H Winter 2017

# Interface code to read in PCB placement problem descriptions, invoke
# the SMT placer, and write out placements

# general imports
import math
import time
import json
import argparse

# SMT-PCB specific imports
import z3
import solvers
import design
import position
import constraints
from board_tools import BoardTools


def main():
    # load command-line arguments
    parser = argparse.ArgumentParser()
    parser.add_argument('--json')
    parser.add_argument('--optimize', action='store_true')
    parser.add_argument('--dout')
    parser.add_argument('--dx', type=float, default=0.1)
    parser.add_argument('--dy', type=float, default=0.1)
    parser.add_argument('--solver', default='Z3')
    parser.add_argument('--logic', default='Int')
    args = parser.parse_args()

    # determine the placement
    design, solver = place_rects(args)

    # write the placement to file
    write_placement(design, solver, args)


def place_rects(args):
    # read in SMT input
    with open(args.json, 'r') as f:
        json_dict = json.load(f)

    # create the solver
    if args.optimize:
        s = z3.Optimize()
    else:
        s = eval('solvers.{}Solver()'.format(args.solver))
        if args.solver == 'CVC4':
            s.set_logic('QF_{}DL'.format(args.logic[0]))
            s.set_option('produce-models', 'true')

    print('Using solver: {}'.format(args.solver))
    print('With logic: {}'.format(args.logic))

    # create the placer grid
    width, height = BoardTools.get_board_dims(json_dict['board_edge'])
    grid = PlaceGrid(width=width, height=height, dx=args.dx, dy=args.dy)
    fab = design.Fabric(grid.place_dims)

    # Create the design
    comps_list = grid.make_comps_list(json_dict['module_dict'])
    routing_list = grid.make_routing_list(json_dict['routing_list'])
    d = design.Design(comps_list, routing_list, fab, eval('position.Rot{}XY'.format(args.logic)), s)

    # Add constraints
    d.add_constraint_generator('no_overlap', constraints.no_overlap)
    d.add_pad_cg('max_dist', constraints.pad_max_dists)

    # add the constraints to the solver
    s.Assert(d.constraints)

    # set up the optimization, if desired
    if args.optimize:
        # d.add_pad_opt('min_total_dist', constraints.pad_dists)
        for func in d.r_opt_param:
            s.minimize(func)

    # not supported by solver agnostic solvers yet
    #with open('freeduino.smt', 'w') as f:
    #    f.write(s.to_smt2())
    # run the placement
    start = time.time()
    result = s.check_sat()
    end = time.time()
    place_time = end - start
    print('Placement took', place_time, 'seconds.')
    if args.dout:
        with open(args.dout, 'a+') as f:
            f.write(str(place_time) + '\n')

    if not result:
        raise Exception('Problem is unsat.')

    return d, s


def write_placement(design, solver, args):
    # read in SMT input
    with open(args.json, 'r') as f:
        json_dict = json.load(f)

    # update components in json_dict
    for comp in design.components:
        # get the reference to the current module from the SMT input dictionary
        name = comp.name
        mod = json_dict['module_dict'][name]

        # if this module has a fixed position, skip it
        if mod['fixed']:
            continue

        # get the x, y position of the component as placed
        (x, y) = comp.pos.get_coordinates()
        mod['x'] = x * args.dx
        mod['y'] = y * args.dy

        # get the rotation
        mod['rotation'] = comp.pos.get_rotation()

    with open(args.json, 'w') as f:
        json.dump(json_dict, f, indent=2, sort_keys=True)


class PlaceGrid(object):
    def __init__(self, width, height, dx, dy):
        self.width = width
        self.height = height
        self.dx = dx
        self.dy = dy

    def round_x(self, x):
        return round(float(x) / self.dx)

    def round_y(self, y):
        return round(float(y) / self.dy)

    def snap_up_y(self, y):
        return int(math.floor(float(y) / self.dy))

    def snap_down_y(self, y):
        return int(math.ceil(float(y) / self.dy))

    def snap_left_x(self, x):
        return int(math.floor(float(x) / self.dx))

    def snap_right_x(self, x):
        return int(math.ceil(float(x) / self.dx))

    @property
    def board_width_snapped(self):
        return self.snap_left_x(self.width)

    @property
    def board_height_snapped(self):
        return self.snap_up_y(self.height)

    def make_comps_list(self, module_dict):
        comps_list = []
        for name, module in module_dict.items():
            comps_list.append(self.make_comp(name, module))
        return comps_list

    def make_routing_list(self, raw_routing_list):
        routing_list = []
        for req in raw_routing_list:
            routing_list.append(self.make_constraint(req))
        return routing_list

    def make_comp(self, name, module):
        if module['fixed']:
            return self.fix_pos(
                name=name,
                width=module['width'],
                height=module['height'],
                x=module['x'],
                y=module['y'])
        else:
            return self.free_pos(
                name=name,
                width=module['width'],
                height=module['height'])

    def fix_pos(self, name, x, y, width, height):
        # snap component to grid conservatively
        ulx = self.snap_left_x(x)
        uly = self.snap_up_y(y)
        lrx = self.snap_right_x(x + width)
        lry = self.snap_down_y(y + height)

        # return dictionary representing component
        return {'name': name,
                'width': lrx - ulx,
                'height': lry - uly,
                'x': ulx,
                'y': uly}

    def free_pos(self, name, width, height):
        # snap component dimensions to grid conservatively
        snapped_width = self.snap_right_x(width)
        snapped_height = self.snap_down_y(height)

        # return dicionary representing component
        return {'name': name,
                'width': snapped_width,
                'height': snapped_height,
                'x': None,
                'y': None}

    def make_constraint(self, req):

        # component 1 description
        comp1 = req['comp1']
        pad1x = self.round_x(req['pad1x'])
        pad1y = self.round_y(req['pad1y'])

        # component 2 description
        comp2 = req['comp2']
        pad2x = self.round_x(req['pad2x'])
        pad2y = self.round_y(req['pad2y'])

        # snap the max length to the grid
        # note that only dx is used for this computation
        max_length = self.round_x(req['max_length'])

        return {'comp1': comp1,
                'comp2': comp2,
                'pad1x': pad1x,
                'pad1y': pad1y,
                'pad2x': pad2x,
                'pad2y': pad2y,
                'max_length': max_length}

    @property
    def place_dims(self):
        return {'height': self.board_height_snapped,
                'width': self.board_width_snapped}


if __name__ == '__main__':
    main()
