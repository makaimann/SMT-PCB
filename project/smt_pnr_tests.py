import z3
import z3util as zu
import constraints
import math
from design import Design, Fabric
import position
from collections import defaultdict
from ast import literal_eval
import placer

def main():
    des, model = tiny_rect_test(True)
    coord_writer(model, des)
    model_printer(model, des)

def get_adj_dict(infile):
    lines = open(infile, 'r').read().split('\n')
    adj_dict = literal_eval(lines[0])
    return adj_dict

def get_comp_dict(infile):
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

def tiny_test(debug_prints=True, infile='in.dict'):
    ''' 
        Place some nodes representing PCB pads
    '''

    # read in the adjacency matrix
    adj_dict = get_adj_dict(infile)

    # determine the set of unique devices
    dev_set = get_dev_set(adj_dict)
    dev_count = len(dev_set)

    # figure out how big to make the grid
    edge = int(math.ceil(math.sqrt(dev_count)))+1

    # create the matrix
    fab = Fabric((edge,edge), wire_lengths={0,1,2})

    des = Design(adj_dict, fab, position.Unpacked2H)
    des.add_constraint_generator('nearest_neighbor', constraints.nearest_neighbor_fast)
    des.add_constraint_generator('distinct', constraints.distinct)

    sol = run_test(des, debug_prints)
    return des, fab, sol

def tiny_rect_test(dims=(3,3), debug_prints=True, infile='in.dict'):
    ''' 
        place 4 nodes on a 3x3 fabric [with length 1 wires] 

    Format:
        adj = {'comp_name' : [('comp_name2', wire_width), ...]} note: wire_width currently not used
        comps_data = {'comp_name' : [(width, height), (x position, y position)]}  --set x/y position to None if free component
    '''
    # read in the adjacency matrix
    adj_dict = get_adj_dict(infile)

    # determine the set of unique devices
    dev_set = get_dev_set(adj_dict)
    dev_count = len(dev_set)

    # figure out how big to make the grid
    dims = (20,20)

    # read in component size dictionary
    comps_data = get_comp_dict(infile)
    
    fab = Fabric(dims, wire_lengths={1})
    p = placer.Placer(fab)

    model, des = p.place(adj_dict, comps_data)

    return des, model

def tiny_opt_test(dims=(4,4), debug_prints=True):
    ''' 
        place 4 nodes on a 3x3 fabric [with length 1 wires] 
    '''
    adj = {'n1' : [('n2', 1),('n3',1)], 'n2' : [('n4',1)], 'n3' : [('n4',1)], 'n4' : {}}
    fab = Fabric(dims, wire_lengths={1})

    des = Design(adj, fab, position.BVXY)
    des.add_optimizer('min_L1', constraints.min_L1, True)
    des.add_constraint_generator('distinct', constraints.opt_distinct)

    sol = run_opt_test(des, debug_prints)
    return des, fab, sol

def small_test(dims=(8,8), debug_prints=True):
    '''
        place a depth 5 binary tree on a 8 by 8 with wire lengths of 1 or 2 
    ''' 
    adj = {'n{}'.format(i) : frozenset((('n{}'.format(2*i), 1), ('n{}'.format(2*i+1), 1))) for i in range(1,2**4)}
    fab = Fabric(dims, wire_lengths={1,2})
    des = Design(adj, fab, position.Packed2H) 
    des.add_constraint_generator('neighborhood', constraints.in_neighborhood(2))
    des.add_constraint_generator('distinct', constraints.distinct)
    sol = run_test(des, debug_prints)
    return des, fab, sol

def unsat_test(debug_prints=True):
    adj = {'n1' : {'n2','n3','n4','n5','n6'}}

    fab = Fabric((3,3), wire_lengths={1})
    des = Design(adj, fab, position.Packed2H)  
    des.add_constraint_generator('nearest_neighbor', constraints.nearest_neighbor_var)
    des.add_constraint_generator('distinct', constraints.distinct)
    sol = run_test(des, debug_prints)
    return des, fab, sol


def run_test(design, debug_prints):
    if debug_prints: print('running test')
    s = z3.Solver()
    
    s.add(design.constraints)

    if debug_prints:
        if s.check() != z3.sat:
            print('test is unsat')
        else:
            print('test is sat')
            model_printer(s.model(), design)
            coord_writer(s.model(), design)
    else:
        s.check()

    return s

def run_opt_test(design, debug_prints):
    if debug_prints: print('running test')
    
    s = z3.Optimize()
    s.add(design.constraints)
    for param, min in design.opt_parameters:
        if min:
            s.minimize(param)
        else:
            s.maximize(param)

    if debug_prints:
        if s.check() != z3.sat:
            print('test is unsat')
        else:
            print('test is sat')
            model_printer(s.model(), design)
    else:
        s.check()

    return s

def model_printer(model, design):
    mesh = defaultdict(lambda: '-')
    for c in design.components:
        (x, y) = c.pos.get_coordinates(model)
        mesh[(x,y)] = c.name
    
    width = 2 + max(len(n) for n in mesh.values())
    s = []
    for y in range(design.fabric.dims[1]):
        ss = []
        for x in range(design.fabric.dims[0]):
            name = mesh[(x,y)].split('_')[0]
            ss.append('{c: ^{w}}'.format(c=name, w=width))
        s.append(ss)
    s = map(' '.join, s)
    s = '\n'.join(s)
    print(s)

def coord_writer(model, design):
    width = design.fabric.dims[0]
    height = design.fabric.dims[1]
    mesh = {}
    for c in design.components:
        (x, y) = c.pos.get_coordinates(model)
        name = c.name.split('_')[0]
        mesh[(x,y)] = name
    open('out.dict','w').write(repr([width,height,mesh]))

if __name__ == '__main__':
    main()
