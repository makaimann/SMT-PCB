# Makai Mann (makaim@stanford.edu)
# Steven Herbst (sherbst@stanford.edu)

# CS448H Winter 2017

# Interface code to read in PCB placement problem descriptions, invoke 
# the SMT placer, and write out placements

# general imports
from collections import defaultdict
from ast import literal_eval

# SMT-PCB specific imports
from design import Design, Fabric
import placer

def main():
    model, design = place_rects()
    print_mesh(model, design)
    write_placement(model, design)

def place_rects(dims=(20,20), infile='in.dict'):
    ''' 
        place devices on a fabric, treating them as rectangles with varying sizes.

    Format:
        adj = {'comp_name' : [('comp_name2', wire_width), ...]} note: wire_width currently not used
        comps_data = {'comp_name' : [(width, height), (x position, y position)]}  --set x/y position to None if free component
    '''

    # read in the adjacency matrix
    adj_dict = get_adj_dict(infile)

    # determine the set of unique devices
    dev_set = get_dev_set(adj_dict)
    dev_count = len(dev_set)

    # read in component size dictionary
    comps_data = get_comp_dict(infile)

    # create a fabric for placing devices    
    fab = Fabric(dims, wire_lengths={1})

    # place the devices
    p = placer.Placer(fab)
    model, design = p.place(adj_dict, comps_data)

    return model, design

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

def write_placement(model, design, outfile='out.dict'):
    # writes the 2D placement information to a file
    width = design.fabric.dims[0]
    height = design.fabric.dims[1]
    mesh = {}
    for c in design.components:
        (x, y) = c.pos.get_coordinates(model)
        name = get_refdes(c.name)
        mesh[(x,y)] = name
    open(outfile,'w').write(repr([width,height,mesh]))

def get_adj_dict(infile):
    # reads a dictionary of component connections from a file
    lines = open(infile, 'r').read().split('\n')
    adj_dict = literal_eval(lines[0])
    return adj_dict

def get_comp_dict(infile):
    # reads a dictionary of component sizes from a file
    lines = open(infile, 'r').read().split('\n')
    comp_dict = literal_eval(lines[1])
    return comp_dict

def get_dev_set(adj_dict):
    # figure out how many devices there are
    dev_set = set()
    for key,val in adj_dict.items():
        dev_set.add(key)
        for dev,_ in val:
            dev_set.add(dev)
    return dev_set

def get_refdes(s):
    # removes the underscore and extra text that
    # gets appended onto the refdes
    return s.split('_')[0]

if __name__ == '__main__':
    main()
