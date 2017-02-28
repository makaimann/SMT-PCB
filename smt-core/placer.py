import math
import os
import constraints
import design
import position
import dot2smt
import z3
import tests
import z3util as zu


class Placer:
    #TODO handle different types
    def __init__(self, fabric):
        self.fabric = fabric

    def parse_file(self, filepath):
        '''
        Parses the provided file using dot2smt
        '''
        filename, file_extension = os.path.splitext(filepath)
        if file_extension == '.dot':
            return dot2smt.from_file(filepath)
        else:
            raise NotImplementedError('Parsing {} files is not yet supported'.format(file_extension))

    def min_area(self, adj, pinned_comps=None):
        print('Creating design...')
        d = design.Design(adj, self.fabric, position.IntXY, pinned_comps, 'Design1')
        neighborhood = int(math.ceil(d.max_degree/4)) + 1
        print('Trying with neighborhood = {}'.format(neighborhood))
        d.add_constraint_generator('rect_neighborhood', constraints.rect_neighborhood(neighborhood))
        d.add_constraint_generator('distinct', constraints.no_overlap)
        opt = z3.Optimize()
        opt.add(d.constraints)
        opt.add(self.fabric.syn_rows <= self.fabric.rows)
        opt.add(self.fabric.syn_cols <= self.fabric.cols)
        opt.minimize(self.fabric.syn_cols)
        opt.minimize(self.fabric.syn_rows)
        if opt.check() == z3.sat:
            print('Found optimal placement')
            return opt.model(), d

    def place(self, adj, pinned_comps=None, neighborhood=None, limit=5):
        print('Creating design...')
        d = design.Design(adj, self.fabric, position.IntXY, pinned_comps, 'Design1')
        if not neighborhood:
            neighborhood = int(math.ceil(d.max_degree/4))
        print('Design has max degree = {}'.format(d.max_degree))
        d.add_constraint_generator('neighborhood', constraints.rect_neighborhood(neighborhood))
        d.add_constraint_generator('distinct', constraints.no_overlap)
        print('Initializing solver and adding constraints...')
        solver = z3.Solver()
        solver.add(d.constraints)
        counter = 0
        print('Finding satisfying model with neighborhood = {}'.format(neighborhood))
        result = solver.check()
        while result != z3.sat and counter < limit:
            print('Placement with neighborhood = {} is unsat.'.format(neighborhood))
            neighborhood += 1
            print('Resetting and trying with neighborhood = {}'.format(neighborhood))
            solver.reset()
            d.remove_constraint_generator('neighborhood')
            d.add_constraint_generator('neighborhood', constraints.rect_neighborhood(neighborhood))
            solver.add(d.constraints)
            counter += 1
            result = solver.check()

        if result == z3.sat:
            print('Found satisfying placement')
            #tests.model_printer(solver.model(), d)
            return solver.model(), d
