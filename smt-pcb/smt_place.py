# Makai Mann (makaim@stanford.edu)
# Steven Herbst (sherbst@stanford.edu)

# CS448H Winter 2017

# Interface code to read in PCB placement problem descriptions, invoke 
# the SMT placer, and write out placements

# general imports
from collections import defaultdict
from ast import literal_eval
import math
import sys
import time
import json

# SMT-PCB specific imports
import z3
import design
import position
import constraints

def main():
    # read command-line arguments
    json_fname = sys.argv[1]

    design, model, smt_dict = place_rects(smt_file_in=json_fname)
#    print_mesh(model, design)
    write_placement(design, model, smt_dict, smt_file_out=json_fname)

def place_rects(smt_file_in):
    ''' 
        place devices on a fabric, treating them as rectangles with varying sizes.

    Format:
        adj = {'comp_name' : [('comp_name2', wire_width), ...]} note: wire_width currently not used
        comps_data = {'comp_name' : [(width, height), (x position, y position)]}  --set x/y position to None if free component
    '''

    # read in SMT input
    with open(smt_file_in, 'r') as f:
        smt_dict = json.load(f)

    # create the placer grid
    grid = PlaceGrid(width=smt_dict['width'], height=smt_dict['height'],
                     dx=smt_dict['dx'], dy=smt_dict['dy'])

    # create the component list
    comps_list = []
    for name, module in smt_dict['module_dict'].items():
        comps_list.append(grid.make_comp(name, module))

    # create the routing list
    routing_list = []
    for req in smt_dict['routing_list']:
        routing_list.append(grid.make_constraint(req))

    # create the placement fabric
    fab = design.Fabric(grid.place_dims)
    
    # create the problem
    d = design.Design(comps_list, routing_list, fab, position.RotIntXY)
    d.add_constraint_generator('no_overlap', constraints.no_overlap)
    d.add_pad_cg('max_dist', constraints.pad_max_dists)
    
    # create the solver
    s = z3.Solver()
    s.add(d.constraints)

    # run the solver
    start = time.time()
    result = s.check()
    end = time.time()
    print('Placing took', end-start, 'seconds.')

    if not result:
        raise Exception('Problem is unsat.')

    # create the model
    model = s.model()

    return d, model, smt_dict

# def print_mesh(model, design):
#     # prints the 2D placement to the console for debugging purposes
#     mesh = defaultdict(lambda: '-')
#     for c in design.components:
#         (x, y) = c.pos.get_coordinates(model)
#         mesh[(x,y)] = c.name
#     
#     width = 2 + max(len(n) for n in mesh.values())
#     s = []
#     for y in range(design.fabric.dims[1]):
#         ss = []
#         for x in range(design.fabric.dims[0]):
#             name = get_refdes(mesh[(x,y)])
#             ss.append('{c: ^{w}}'.format(c=name, w=width))
#         s.append(ss)
#     s = map(' '.join, s)
#     s = '\n'.join(s)
#     print(s)

def write_placement(design, model, smt_dict, smt_file_out):
    # writes the 2D placement information to a file
    dx = smt_dict['dx']
    dy = smt_dict['dy']
    grid = PlaceGrid(width=smt_dict['width'], height=smt_dict['height'],
                     dx=smt_dict['dx'], dy=smt_dict['dy'])

    # update components in smt_dict
    for comp in design.components:
        # get the reference to the current module from the SMT input dictionary
        name = comp.name
        mod = smt_dict['module_dict'][name]
 
        # if this module has a fixed position, skip it
        if mod['fixed']:
            continue

        # get the x, y position of the component as placed
        (x, y) = comp.pos.get_coordinates(model)
        mod['x'] = x*dx 
        mod['y'] = y*dy 

        # get the rotation
        mod['rotation'] = comp.pos.get_rotation(model)

    with open(smt_file_out, 'w') as f:
        json.dump(smt_dict, f)

class PlaceGrid(object):
    def __init__(self, width, height, dx, dy):
        self.width = width
        self.height = height
        self.dx = dx
        self.dy = dy

    def round_x(self, x):
        return int(math.round(float(x)/self.dx))

    def round_y(self, y):
        return int(math.round(float(y)/self.dy))

    def snap_up_y(self, y):
        return int(math.floor(float(y)/self.dy))

    def snap_down_y(self, y):
        return int(math.ceil(float(y)/self.dy))

    def snap_left_x(self, x):
        return int(math.floor(float(x)/self.dx))

    def snap_right_x(self, x):
        return int(math.ceil(float(x)/self.dx))

    @property
    def board_width_snapped(self):
        return self.snap_left_x(self.width)

    @property
    def board_height_snapped(self):
        return self.snap_up_y(self.height)

    def make_comp(self, name, module):
        if module['fixed']:
            return self.fix_pos(name=name, width=module['width'], 
                                height=module['height'], x=module['x'], y=module['y'])
        else:
            return self.free_pos(name=name, width=module['width'], height=module['height'])
    
    def fix_pos(self, name, x, y, width, height):
        # snap component to grid conservatively
        ulx = self.snap_left_x(x)
        uly = self.snap_up_y(y)
        lrx = self.snap_right_x(x + width)
        lry = self.snap_down_y(y + height)
        
        # return dictionary representing component
        return {'name' : name, 
                'width' : lrx-ulx, 
                'height' : lry-uly, 
                'x' : ulx, 
                'y' : uly}

    def free_pos(self, name, width, height):
        # snap component dimensions to grid conservatively
        snapped_width = self.snap_right_x(width)
        snapped_height = self.snap_down_y(height)

        # return dicionary representing component
        return {'name' : name, 
                'width' : snapped_width, 
                'height' : snapped_height, 
                'x' : None, 
                'y' : None}

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

        return {'comp1' : 'n1', 
                'comp2' : 'n2', 
                'pad1x' : pad1x, 
                'pad1y' : pad1y, 
                'pad2x' : pad2x, 
                'pad2y' : pad2y, 
                'max_length' : max_length}

    @property
    def place_dims(self):
        return {'height': self.board_height_snapped, 
                'width': self.board_width_snapped}

if __name__ == '__main__':
    main()
