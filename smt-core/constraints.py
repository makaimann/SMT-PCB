'''
Constraint and optimizer functions
'''

import functions
import solverutil as su

# useful functions
And = functions.And()
Or = functions.Or()



def in_neighborhood(num_hops):
    '''
    in_neighborhood(1) should equal nearest_neighbor_fast
    '''

    if num_hops < 1:
        raise ValueError('num_hops must be >= 1, recieved {}'.format(num_hops))

    def _get_pairs(wire_lengths, n):
        if n == 1:
            s = set()
            for wl in wire_lengths:
                s.add((0, wl))
                s.add((wl, 0))
        elif n > 1:
            s = _get_pairs(wire_lengths, n-1)
            s2 = set()
            for p in s:
                for wl in wire_lengths:
                    s2.add((p[0], p[1]+wl))
                    s2.add((p[0]+wl, p[1]))
            s = s.union(s2)
        else:
            raise ValueError('n must be >= 1, recieved {}'.format(n))
        return s

    def neighborhood(components, wires, fabric):
        distances = _get_pairs(fabric.wire_lengths, num_hops)
        constraints = []
        for w in wires:
            src = w.src
            dst = w.dst

            delta_x = src.pos.delta_x_fun(dst.pos)
            delta_y = src.pos.delta_y_fun(dst.pos)

            c = []
            for dx, dy in distances:
                c.append(And(delta_x(dx), delta_y(dy)))

            constraints.append(Or(c))
        return And(constraints)
    return neighborhood


def rect_neighborhood(num_hops):
    '''
    in_neighborhood(1) should equal nearest_neighbor_fast
    '''

    if num_hops < 1:
        raise ValueError('num_hops must be >= 1, recieved {}'.format(num_hops))

    def neighborhood(components, wires, fabric):
        constraints = []
        for w in wires:
            src = w.src
            dst = w.dst

            delta_x = src.pos.delta_x_fun(dst.pos)
            delta_y = src.pos.delta_y_fun(dst.pos)
            
            constraints.append(delta_x(num_hops))
            constraints.append(delta_y(num_hops))
        return And(constraints)
    return neighborhood

# not being used currently -- no solver agnostic support for distinct yet
#def distinct(components, wires, fabric):
#   return z3.Distinct(*(c.pos.flat for c in components))

# not being used currently
#def opt_distinct(components, wires, fabric):
#    ''' Distinct for Optimizer -- because needs to be simplified for z3.Optimize()'''
#    return z3.simplify(z3.Distinct(*(c.pos.flat for c in components)), ':blast-distinct', True)

def no_overlap(components, wires, fabric):
    comps = list(components)
    c = []
    for i in range(0, len(comps)):
        for j in range(i+1, len(comps)):
            if not comps[i].is_fixed or not comps[j].is_fixed:
                c.append(Or(comps[i].pos.x - comps[j].pos.x >= comps[j].pos._horiz_var,
                               comps[j].pos.x - comps[i].pos.x >= comps[i].pos._horiz_var,
                               comps[i].pos.y - comps[j].pos.y >= comps[j].pos._vert_var,
                               comps[j].pos.y - comps[i].pos.y >= comps[i].pos._vert_var))
    return And(c)


def pad_max_dists(comps, routing_list):
    constraints = []
    for connection in routing_list:
        comp1name = connection['comp1']
        comp2name = connection['comp2']
        pad1x = connection['pad1x']
        pad1y = connection['pad1y']
        pad2x = connection['pad2x']
        pad2y = connection['pad2y']
        max_length = connection['max_length']
        comp1 = comps[comp1name]
        comp2 = comps[comp2name]
        constraints.append(
            comp1.pos.pad_dist_lt(pad1x, pad1y, comp2.pos, pad2x, pad2y, max_length))

    return And(constraints)

def pad_dists(comps, routing_list):
    dist = 0
    for connection in routing_list:
        comp1name = connection['comp1']
        comp2name = connection['comp2']
        pad1x = connection['pad1x']
        pad1y = connection['pad1y']
        pad2x = connection['pad2x']
        pad2y = connection['pad2y']
        max_length = connection['max_length']
        comp1 = comps[comp1name]
        comp2 = comps[comp2name]
        dist = dist + su.Abs(comp1.pos.pad_delta_x(pad1x, pad1y, comp2.pos, pad2x ,pad2y)) + \
               su.Abs(comp1.pos.pad_delta_y(pad1x, pad1y, comp2.pos, pad2x, pad2y))

    return dist
        
