'''
    Classes for represtenting designs and various constructors
'''

from collections import Iterable
import sorts
import functions
import traceback
from classutil import IDObject, NamedIDObject, ValidContainer

# useful functions
And = functions.And()
Or = functions.Or()
Not = functions.Not()


class Fabric:
    def __init__(self, place_dims, wire_lengths={1}, W=2, Fc=None, Fs=None, node_masks=None, model = None):
        '''
            dims := The dimensions of the fabric
            wire_lengths := the length of wires between switch boxes
            All other operands are unimplemented
        '''
        #super().__init__()
        #if not isinstance(dims, Iterable):
        #    raise TypeError('dims must be iterable, recieved type {}'.format(type(dims)))
        #dims = tuple(dims)

        #if len(dims) != 2:
        #    raise ValueError('dims must be of length 2, received object of length {}'.format(len(dims)))

        if 'height' not in place_dims or 'width' not in place_dims:
            raise ValueError('place_dims must contain a height and a width')

        self._dims = (place_dims['height'], place_dims['width'])
        #self._syn_dims = (z3.Int('rows'), z3.Int('cols'))
        self._wire_lengths = set(wire_lengths)
        self._W = W
        self._Fc = Fc
        self._Fs = Fs
        self._model = model


    def update_wire_lengths(self, n=2):
        for i in range(n):
            self._wire_lengths.add(max(self._wire_lengths) + 1)

    @property
    def dims(self):
        return self._dims

    @property
    def rows(self):
        return self._dims[0]

    @property
    def cols(self):
        return self._dims[1]

    #@property
    #def syn_rows(self):
    #    return self._syn_dims[0]

    #@property
    #def syn_cols(self):
    #    return self._syn_dims[1]

    @property
    def wire_lengths(self):
        return self._wire_lengths

    @property
    def W(self):
        return self._W

    @property
    def Fc(self):
        raise NotImplementedError('This feature is not supported')

    @property
    def Fs(self):
        raise NotImplementedError('This feature is not supported')


class Component():
    def __init__(self, name, fixed_flag, width=1, height=1, x=None, y=None, inputs=(), outputs=(), pos=None):
        self._name = name
        self._pos = pos
        self._inputs = set(inputs)
        self._outputs = set(outputs)
        #outputs as list allows multiple edges between two components
        #used for routing
        self._outputs_list = list(outputs)
        self._in_degree = 0
        self._out_degree = 0
        self._degree = 0
        self._width = width
        self._height = height
        self._fixed = fixed_flag
        self._x = x
        self._y = y


    @property
    def name(self):
        '''
            returns the component's name
        '''
        return self._name

    @property
    def inputs(self):
        '''
            returns a iterator over Wires
        '''
        return iter(self._inputs)

    @property
    def outputs(self):
        '''
            returns a iterator over Wires
        '''
        return iter(self._outputs)

    @property
    def outputs_list(self):
        '''
           returns a list of Wires
        '''
        return self._outputs_list

    @property
    def pos(self):
        return self._pos

    @property
    def width(self):
        return self._width

    @property
    def height(self):
        return self._height

    @property
    def is_fixed(self):
        return self._fixed

    @property
    def in_degree(self):
        return self._in_degree

    @property
    def out_degree(self):
        return self._out_degree

    @property
    def degree(self):
        return self._degree

    @property
    def x(self):
        return self._x

    @property
    def y(self):
        return self._y

    @pos.setter
    def pos(self, p):
        self._pos = p

    def _add_input(self, src):
        self._inputs.add(src)
        self._in_degree += 1
        self._degree += 1

    def _add_output(self, dst):
        self._outputs.add(dst)
        self._outputs_list.append(dst)
        self._out_degree += 1
        self._degree += 1

    def __repr__(self):
        return 'name: {}, inputs: {}, outputs: {}'.format(self.name, {x.src.name for x in self.inputs}, {x.dst.name for x in self.outputs})

class Wire(IDObject):
    def __init__(self, src, dst, width=1):
        super().__init__()
        self._src = src
        self._dst = dst
        src._add_output(self)
        dst._add_input(self)

    @property
    def src(self):
        return self._src

    @property
    def dst(self):
        return self._dst

    def __repr__(self):
        return '{} -[{}]-> {}'.format(self.src.name, self.width, self.dst.name)

class Design(NamedIDObject):
    def __init__(self, comp_list, routing_list, fabric, position_type, solver, name='', constraint_generators=(), optimizers=()):
        '''
        adj_dict :: {str : [(str, int)]}
        adj_dict[x] := out edges of x with the their width
        fabric :: Fabric
        position_type ::  str -> Fabric -> PositionBase

        constraints_gen :: [([Component] -> [Wire] -> fabric -> z3.Bool)]
        constraint_generators := an iterable of keys, functions that generate hard
            constraints

        optimizers :: [([Component] -> [Wire] -> fabric -> (z3.Bool, z3.Object), bool)]
        optimizers := [k, f, b]
            where
                k is the key
                f(components, wires) := an Iterable of functions that
                    generate hard constraint / optimizing parameters pairs,
                b := a bool which indicating whether Optimizing parameter is minimized or maximized
        '''

        super().__init__(name)
        self._fabric = fabric
        self._position_type = position_type
        self._solver = solver

        self._comp_list = comp_list #is kinda redundant to keep this around but it might be useful
        self._routing_list = routing_list

        self._comps = dict()
        self._wires = dict()

        self._p_constraints = ValidContainer()
        self._cg = dict()
        self._opt = dict()
        self._pinned_comps = []

        self._r_constraints = ValidContainer()
        self._rcg = dict()
        self._ropt = dict()

        self._max_degree = 0

        for k,f in constraint_generators:
            self.add_constraint_generator(k,f)

        for k,f,b in optimizers:
            self.add_optimizer(k,f,b)

        #build graph
        self._gen_graph()

    def _gen_graph(self):
        #reset constraints
        self._reset_constraints()

        for comp_dict in self._comp_list:
            name = comp_dict['name']
            width = comp_dict['width']
            height = comp_dict['height']
            if comp_dict['x'] is not None and comp_dict['y'] is not None:
                self._comps[name] = Component(name, True, width, height, comp_dict['x'], comp_dict['y'])
                self._pinned_comps.append(name)
            else:
                self._comps[name] = Component(name, False, width, height)

        #need to generate positons for each component
        self._gen_pos()
        

    def _gen_pos(self):
        #reset constraints
        self._reset_constraints()
        for c in self.components:
            if c.width and c.height:
                c.pos = self._position_type(c.name, self.fabric, c.width, c.height, self._solver)
            else:
                c.pos = self._position_type(c.name, self.fabric, self._solver)
            # also find maximum (in or out) degree
            if self._max_degree < c.degree:
                self._max_degree = c.degree

    def get_sorted_components(self, descend):
        '''returns components sorted by their degree in descending order if descend = True'''
        return sorted(list(self._comps.values()), key = lambda c: c.degree, reverse=descend)

    @property
    def components(self):
        return iter(self._comps.values())

    @property
    def wires(self):
        return iter(self._wires.values())

    @property
    def fabric(self):
        return self._fabric

    @fabric.setter
    def fabric(self, fabric):
        if self.fabric != fabirc:
            self._fabric = fabric
            #position representation is dependent on fabric
            self._gen_pos()

    @property
    def constraints(self):
        '''returns all hard constraints'''
        if self._pinned_comps:
            return self._solver.apply_fun(And, self.p_constraints, self.g_constraints, self.o_constraints, self.r_constraints, self.pinned_constraints)
        else:
            return self._solver.apply_fun(And, self.p_constraints, self.g_constraints, self.o_constraints, self.r_constraints)

    @property
    def max_degree(self):
        return self._max_degree

    def _reset_constraints(self):
        self._reset_p_constraints()
        self._reset_g_constraints()
        self._reset_o_constraints()

    '''
        -----------------------------------------------------------------------
        Position Related Stuff
        -----------------------------------------------------------------------
    '''

    @property
    def position_type(self):
        return self._position_type

    @position_type.setter
    def position_type(self, position_type):
        if position_type != self.position_type:
            self._position_type = position_type
            #regenerate positions for each node
            self._gen_pos()

    @property
    def p_constraints(self):
        if not self._p_constraints.valid:
            cl = []
            for c in self.components:
                if not c.is_fixed:
                    cl.append(c.pos.invariants)
            self._p_constraints.data = And(*cl)

        return self._p_constraints.data

    def _reset_p_constraints(self):
        self._p_constraints.mark_invalid()

    @property
    def pinned_constraints(self):
        if self._pinned_comps:
            c = []
            for src_name in self._pinned_comps:
                comp = self._comps[src_name]
                cx = self._solver.theory_const(eval('sorts.{}()'.format(comp.pos.x.sort)), comp.x)
                cy = self._solver.theory_const(eval('sorts.{}()'.format(comp.pos.y.sort)), comp.y)
                width = self._solver.theory_const(eval('sorts.{}()'.format(comp.pos.horiz_var.sort)), comp.pos.width)
                height = self._solver.theory_const(eval('sorts.{}()'.format(comp.pos.vert_var.sort)), comp.pos.height)
                c.append(comp.pos.x == cx)
                c.append(comp.pos.y == cy)
                c.append(comp.pos.horiz_var == width)
                c.append(comp.pos.vert_var == height)
                c.append(And(comp.pos._d0,
                             Not(comp.pos._d90),
                             Not(comp.pos._d180),
                             Not(comp.pos._d270)))
            return And(c)
            
    '''
        -----------------------------------------------------------------------
        General constraints related stuff
        -----------------------------------------------------------------------
    '''
    @property
    def constraint_generators(self):
        return set((k, f) for k,(f,_) in self._cg.items())

    def add_constraint_generator(self, k, f):
        self._cg[k] = (f, ValidContainer())

    def remove_constraint_generator(self, k):
        del self._cg[k]

    @property
    def g_constraints(self):
        cl = []
        for k,(f, c) in self._cg.items():
            if not c.valid:
                c.data = f(self.components, self.wires, self.fabric)
            cl.append(c.data)
        return And(cl)

    def _reset_g_constraints(self):
        for _,c in self._cg.values():
            c.mark_invalid()

    '''
        -----------------------------------------------------------------------
        Optimization Related Stuff
        -----------------------------------------------------------------------
    '''

    @property
    def optimizers(self):
        return set((k, f, b) for k,(f,_,b) in self._cg.items())

    def add_optimizer(self, k, f, minimize):
        self._opt[k] = (f, ValidContainer(), minimize)

    def remove_optimizer(self, k):
        del self._opt[k]

    @property
    def o_constraints(self):
        cl = []
        for f,c,m in self._opt.values():
            # f := functiom
            # c := ValidContainer(constraints, parameter)
            # m := minimize flag
            if not c.valid:
                c.data = f(self.components, self.wires, self.fabric)
            if c.data[0]:
                #check that list nonempty to avoid appending an empty list
                cl.append(c.data[0])
        return And(cl)

    @property
    def opt_parameters(self):
        cl = []
        for f,c,m in self._opt.values():
            # f := functiom
            # c := ValidContainer(constraints, parameter)
            # m := minimize flag
            if not c.valid:
                c.data = f(self.components, self.wires, self.fabric)
            cl.append((c.data[1], m))
        return cl

    def _reset_o_constraints(self):
        for _,c,_ in self._opt.values():
            c.mark_invalid()

    '''
        -----------------------------------------------------------------------
        Pad-Routing Related Stuff
        -----------------------------------------------------------------------
    '''

    
    @property
    def r_constraints(self):
        cl = []
        for k,(f, c) in self._rcg.items():
            if not c.valid:
                c.data = f(self._comps, self._routing_list)
            cl.append(c.data)
        return And(cl)
    
    def add_pad_cg(self, k, f):
        '''
            Adds a constraint generator for pad-level connectivity
        '''
        self._rcg[k] = (f, ValidContainer())


    def remove_pad_cg(self, k):
        del self._rcg[k]


    @property
    def r_opt_param(self):
        cl = []
        for k,(f, c) in self._ropt.items():
            if not c.valid:
                c.data = f(self._comps, self._routing_list)
            cl.append(c.data)
        return cl

    def add_pad_opt(self, k, f):
        '''
            Adds a constraint generator for pad-level connectivity
        '''
        self._ropt[k] = (f, ValidContainer())


    def remove_pad_opt(self, k):
        del self._ropt[k]
