#!/usr/bin/env python

import z3
import design
import position
import constraints

place_dims = {'height' : 4, 'width' : 4}
comps_list = [{'name' : 'n1', 'width' : 2, 'height' : 1, 'x' : 0, 'y' : 0},
                         {'name' : 'n2', 'width' : 2, 'height' : 1, 'x' : None, 'y' : None}]
routing_list = [{'comp1' : 'n1', 'comp2' : 'n2', 'pad1x' : 2, 'pad1y' : 0, 'pad2x' : 0, 'pad2y' : 0, 'max_length' : 1}]

fab = design.Fabric(place_dims)

d = design.Design(comps_list, routing_list, fab, position.RotIntXY)
d.add_constraint_generator('no_overlap', constraints.no_overlap)
d.add_pad_cg('max_dist', constraints.pad_max_dists)

s = z3.Solver()

s.add(d.constraints)

result = s.check()

if result:
    print('SAT')
    for comp in d.components:
        loc = comp.pos.get_coordinates(s.model())
        rad = comp.pos.get_rotation(s.model())
        print('{} x = {} y = {} rot = {}'.format(comp.name, loc[0], loc[1], rad))
else:
    print('UNSAT')
