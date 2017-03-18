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
import design
import position
import constraints


def main():
    # load command-line arguments
    parser = argparse.ArgumentParser()
    parser.add_argument('--json')
    args = parser.parse_args()

    # read in SMT input
    with open(args.json, 'r') as f:
        json_dict = json.load(f)

    design, model, json_dict = place_rects(
        json_dict=json_dict, optimize=False)
    write_placement(design, model, json_dict, json_file=args.json)


def place_rects(json_dict, optimize=False):
    # TODO: add documentation for function

    # create the placer grid
    grid = PlaceGrid(width=json_dict['width'], height=json_dict['height'],
                     dx=json_dict['dx'], dy=json_dict['dy'])

    # create the component list
    comps_list = []
    for name, module in json_dict['module_dict'].items():
        comps_list.append(grid.make_comp(name, module))

    # create the routing list
    routing_list = []
    for req in json_dict['routing_list']:
        routing_list.append(grid.make_constraint(req))

    # create the placement fabric
    fab = design.Fabric(grid.place_dims)

    # create the problem
    d = design.Design(comps_list, routing_list, fab, position.RotIntXY)
    d.add_constraint_generator('no_overlap', constraints.no_overlap)
    d.add_pad_cg('max_dist', constraints.pad_max_dists)

    if optimize:
        d.add_pad_opt('min_total_dist', constraints.pad_dists)

    # create the solver
    if optimize:
        s = z3.Optimize()
    else:
        s = z3.Solver()

    # add the constraints to the solver
    s.add(d.constraints)

    # set up the optimization, if desired
    if optimize:
        for func in d.r_opt_param:
            s.minimize(func)

    # run the placement
    start = time.time()
    result = s.check()
    end = time.time()
    print('Placement took', end - start, 'seconds.')

    if result == z3.unsat:
        raise Exception('Problem is unsat.')

    # create the model
    model = s.model()

    return d, model, json_dict


def write_placement(design, model, json_dict, json_file):
    # writes the 2D placement information to a file
    dx = json_dict['dx']
    dy = json_dict['dy']

    # update components in json_dict
    for comp in design.components:
        # get the reference to the current module from the SMT input dictionary
        name = comp.name
        mod = json_dict['module_dict'][name]

        # if this module has a fixed position, skip it
        if mod['fixed']:
            continue

        # get the x, y position of the component as placed
        (x, y) = comp.pos.get_coordinates(model)
        mod['x'] = x * dx
        mod['y'] = y * dy

        # get the rotation
        mod['rotation'] = comp.pos.get_rotation(model)

    with open(json_file, 'w') as f:
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
