# Makai Mann (makaim@stanford.edu)
# Steven Herbst (sherbst@stanford.edu)

# CS448H Winter 2017

# Interface code to read in PCB placement problem descriptions, invoke 
# the SMT placer, and write out placements

# general imports
from collections import defaultdict
from ast import literal_eval
import math

# SMT-PCB specific imports
from pcbparser import PcbParser
from design import Design, Fabric
import placer

def main():
    model, design, smt_input = place_rects()
#    print_mesh(model, design)
    write_placement(model, design, smt_input)

def place_rects(pcb='test.kicad_pcb', smt_input='in.dict'):
    ''' 
        place devices on a fabric, treating them as rectangles with varying sizes.

    Format:
        adj = {'comp_name' : [('comp_name2', wire_width), ...]} note: wire_width currently not used
        comps_data = {'comp_name' : [(width, height), (x position, y position)]}  --set x/y position to None if free component
    '''

    # read in SMT input
    smt_input = literal_eval(open('in.dict','r').read())

    # create the placer grid
    grid = PlaceGrid(width=smt_input['width'], height=smt_input['height'],
                     dx=smt_input['dx'], dy=smt_input['dy'])

    # create the placement dictionary
    place_dict = {}
    for name, module in smt_input['module_dict'].items():
        place_dict[name] = grid.place_entry(module)

    # read in the adjacency matrix
    graph_struct = get_graph_struct(critical_nets=smt_input['critical_nets'],
                                    tree=PcbParser.read_pcb_file(pcb))

    # create a fabric for placing devices    
    fab = Fabric(grid.place_dims, wire_lengths={1})

    # place the devices
    p = placer.Placer(fab)
    #min_area -- tries to place all components in the smallest synthetic fabric
    #while keeping each connection within a certain neighborhood
    #from each component, can retrieve a horizontal and vertical distance that
    #specifies the rotation
    #place -- finds satisfying placement within a given neighborhood for each connection
    model, design = p.min_area(graph_struct, place_dict)

    return model, design, smt_input

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

def write_placement(model, design, smt_input, outfile='out.dict'):
    # writes the 2D placement information to a file
    dx = smt_input['dx']
    dy = smt_input['dy']
    mesh = {}
    for c in design.components:
        name = get_refdes(c.name)
        mod = smt_input['module_dict'][name]
        if mod['x'] is None or mod['y'] is None:
            (x, y) = c.pos.get_coordinates(model)
            mod['x'] = x*dx
            mod['y'] = y*dy
        if mod['rotation'] is None:
            mod['rotation'] = 0.0

    open(outfile,'w').write(repr(smt_input))

def get_refdes(s):
    # removes the underscore and extra text that
    # gets appended onto the refdes
    return s.split('_')[0]

# TODO: clean up net_dict code
def parse_pcb_tree(critical_nets, tree):
    modules = set()
    net_dict = {}
    for arg in tree:
        if arg[0] == 'module':
            for val in arg:
                if val[0:2] == ['fp_text', 'reference']:
                    refdes = val[2]
                    modules.add(refdes) 
                    break
        for val in arg:
            if val[0]=='pad':
                for cmd in val:
                    if cmd[0] == 'net':
                        net = cmd[2]
                        if net in critical_nets:
                            if net not in net_dict:
                                net_dict[net] = set()
                            net_dict[net].add(refdes)
    return modules, net_dict

def get_graph_struct(critical_nets, tree):
    # generate dictionary mapping each net to a set of connected components
    modules, net_dict = parse_pcb_tree(critical_nets, tree)

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
        return self.snap_right_x(self.width)

    @property
    def board_height_snapped(self):
        return self.snap_down_y(self.height)

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
