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

# SMT-PCB specific imports
from design import Design, Fabric
import placer

def main():
    # read command-line arguments
    dict_fname = sys.argv[1]

    model, design, smt_dict = place_rects(smt_file_in=dict_fname)
    #print_mesh(model, design)
    write_placement(model, design, smt_dict, smt_file_out=dict_fname)

def place_rects(smt_file_in):
    ''' 
        place devices on a fabric, treating them as rectangles with varying sizes.

    Format:
        adj = {'comp_name' : [('comp_name2', wire_width), ...]} note: wire_width currently not used
        comps_data = {'comp_name' : [(width, height), (x position, y position)]}  --set x/y position to None if free component
    '''

    # read in SMT input
    with open(smt_file_in, 'r') as f:
        smt_dict = literal_eval(f.read())

    # create the placer grid
    grid = PlaceGrid(width=smt_dict['width'], height=smt_dict['height'],
                     dx=smt_dict['dx'], dy=smt_dict['dy'])

    # create the placement dictionary
    place_dict = {}
    for name, module in smt_dict['module_dict'].items():
        place_dict[name] = grid.place_entry(module)

    # read in the adjacency matrix
    graph_struct = get_graph_struct(critical_nets=smt_dict['critical_nets'],
                                    design_dict=smt_dict['design_dict'])

    # create a fabric for placing devices    
    fab = Fabric(grid.place_dims, wire_lengths={1})

    # place the devices
    p = placer.Placer(fab)

    #from each component, can retrieve a horizontal and vertical distance that
    #specifies the rotation
    print('Running SMT placement algorithm.')
    start = time.time()
    model, design = p.place(graph_struct, place_dict, 25)
    end = time.time()
    print('Placing took', end-start, 'seconds.')

    return model, design, smt_dict

def print_mesh(model, design):
    # prints the 2D placement to the console for debugging purposes
    mesh = defaultdict(lambda: '-')
    for c in design.components:
        (x, y) = c.pos.get_coordinates(model)
        mesh[(x,y)] = c.name
    
    width = 2 + max(len(n) for n in mesh.values())
    s = []
    for y in range(design.fabric.dims[1]):
        ss = []
        for x in range(design.fabric.dims[0]):
            name = get_refdes(mesh[(x,y)])
            ss.append('{c: ^{w}}'.format(c=name, w=width))
        s.append(ss)
    s = map(' '.join, s)
    s = '\n'.join(s)
    print(s)

def write_placement(model, design, smt_dict, smt_file_out):
    # writes the 2D placement information to a file
    dx = smt_dict['dx']
    dy = smt_dict['dy']
    grid = PlaceGrid(width=smt_dict['width'], height=smt_dict['height'],
                     dx=smt_dict['dx'], dy=smt_dict['dy'])

    # writes the snapped width and height of the board
    smt_dict['edge_lr_x'] = (grid.board_width_snapped+1)*dx
    smt_dict['edge_lr_y'] = (grid.board_height_snapped+1)*dy
    
    mesh = {}
    for c in design.components:
        # get the reference to the current module from the SMT input dictionary
        name = get_refdes(c.name)
        mod = smt_dict['module_dict'][name]
        
        # if this module has a fixed position, skip it
        if mod['fixed']:
            continue

        # get the x, y position of the component as placed
        (x, y) = c.pos.get_coordinates(model)
        mod['x'] = x*dx 
        mod['y'] = y*dy 

        # determine height and width of component as placed
        (placed_height, placed_width) = c.pos.get_vh(model)
    
        # determine height and width of component before placement
        snapped_width = grid.snap_right_x(mod['width'])
        snapped_height = grid.snap_down_y(mod['height'])

        # determine rotation
        if placed_width == snapped_width and placed_height == snapped_height:
                mod['rotation'] = 0.0
        elif placed_width == snapped_height and placed_height == snapped_width:
                mod['rotation'] = -math.pi/2
        else:
            raise Exception('Unimplemented rotation')

    with open(smt_file_out, 'w') as f:
        f.write(repr(smt_dict))

def get_refdes(s):
    # removes the underscore and extra text that
    # gets appended onto the refdes
    return s.split('_')[0]

def process_design_dict(critical_nets, design_dict):
    modules = design_dict.keys()
    net_dict = {}
    
    for module_name, pad_dict in design_dict.items():
        for pad_name, net_name in pad_dict.items():
            if net_name in critical_nets:
                if net_name not in net_dict:
                    net_dict[net_name] = set()
                net_dict[net_name].add(module_name)

    return modules, net_dict

def get_graph_struct(critical_nets, design_dict):
    # generate dictionary mapping each net to a set of connected components
    modules, net_dict = process_design_dict(critical_nets, design_dict)

    # create a list of lists of connected components
    adj_list = []
    for comp_set in net_dict.values():
        adj_list.append(list(comp_set))

    # generate graph_struct needed by SMT solver
    graph_struct = {}
    included_comps = set()
    for adj in adj_list:
        first = adj[0]
        rest = [(x,1) for x in adj[1:]]
        for x in adj:
            included_comps.add(x)
        if first not in graph_struct:
            graph_struct[first] = rest
        else:
            graph_struct[first].extend(rest)

    # add back components not included earlier
    for comp in (modules-included_comps):
        graph_struct[comp]= []

    return graph_struct

class PlaceGrid(object):
    def __init__(self, width, height, dx, dy):
        self.width = width
        self.height = height
        self.dx = dx
        self.dy = dy

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
        return self.snap_left_x(self.width)-1

    @property
    def board_height_snapped(self):
        return self.snap_up_y(self.height)-1

    def place_entry(self, module):
        if module['x'] is not None and module['y'] is not None:
            return self.fix_pos(width=module['width'], height=module['height'],
                                x=module['x'], y=module['y'])
        else:
            return self.free_pos(width=module['width'], height=module['height'])
    
    def fix_pos(self, x, y, width, height):
        ulx = self.snap_left_x(x)
        uly = self.snap_up_y(y)
        lrx = self.snap_right_x(x + width)
        lry = self.snap_down_y(y + height)
        ulx = max(ulx, 0)
        uly = max(uly, 0)
        lrx = min(lrx, self.board_width_snapped-1)
        lry = min(lry, self.board_height_snapped-1)
        return [(lrx-ulx,lry-uly), (ulx,uly)]

    def free_pos(self, width, height):
        snapped_width = self.snap_right_x(width)
        snapped_height = self.snap_down_y(height)
        return [(snapped_width, snapped_height), (None, None)]

    @property
    def place_dims(self):
        return (self.board_height_snapped, self.board_width_snapped)

if __name__ == '__main__':
    main()
