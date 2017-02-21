import z3
import z3util as zu
import constraints
from design import Design, Fabric
import position
from collections import defaultdict
import placer

def tiny_test(dims=(3,3), debug_prints=True):
    ''' 
        place 4 nodes on a 3x3 fabric [with length 1 wires] 
    '''
    adj = {'n1' : [('n2', 1),('n3',1)], 'n2' : [('n4',1)], 'n3' : [('n4',1)], 'n4' : {}}
    comps_data = {'n1' : [(1,2), (None,None)], 'n2' : [(1,1), (None,None)], 'n3' : [(1,1), (None,None)], 'n4' : [(1,1), (None, None)]}
    fab = Fabric(dims, wire_lengths={1})

    des = Design(adj, fab, position.Unpacked2H)
    des.add_constraint_generator('nearest_neighbor', constraints.nearest_neighbor_fast)
    des.add_constraint_generator('distinct', constraints.distinct)

    sol = run_test(des, debug_prints)
    return des, fab, sol

def tiny_rect_test(dims=(3,3), debug_prints=True):
    ''' 
        place 4 nodes on a 3x3 fabric [with length 1 wires] 

    Format:
        adj = {'comp_name' : [('comp_name2', wire_width), ...]} note: wire_width currently not used
        comps_data = {'comp_name' : [(width, height), (x position, y position)]}  --set x/y position to None if free component
    '''
    adj = {'n1' : [('n2', 1),('n3',1)], 'n2' : [('n4',1)], 'n3' : [('n4',1)], 'n4' : {}}
    comps_data = {'n1' : [(1,2), (None,None)], 'n2' : [(1,1), (None,None)], 'n3' : [(1,1), (None,None)], 'n4' : [(1,1), (None, None)]}
    
    fab = Fabric(dims, wire_lengths={1})

    p = placer.Placer(fab)

    model, des = p.place(adj, comps_data)

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
            ss.append('{c: ^{w}}'.format(c=mesh[(x, y)], w=width))
        s.append(ss)
    s = map(' '.join, s)
    s = '\n'.join(s)
    print(s)

