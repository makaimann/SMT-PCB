from abc import ABCMeta, abstractmethod
from math import pi
import solverutil as su
from smt_switch import sorts
from smt_switch import functions

# Sorts
intsort = sorts.Int()
realsort = sorts.Real()
boolsort = sorts.Bool()

# functions
And = functions.And()
Or = functions.Or()
Ite = functions.Ite()
concat = functions.concat()
bvult = functions.bvult()
bvule = functions.bvule()
bvuge = functions.bvuge()


class PositionBase(metaclass=ABCMeta):
    def __init__(self, name, fabric, solver):
        self._name = name
        self._fabric = fabric
        self._solver = solver

    @property
    def name(self):
        return self._name

    @property
    def fabric(self):
        return self._fabric

    @property
    def solver(self):
        return self._solver

    @property
    @abstractmethod
    def flat(self):
        '''
        flat :: -> z3.BitVec | a.flat == b.flat => a.x == b.x and a.y == b.y

        Return (x, y) in some form that such that z3.distinct can be called on it
        '''
        pass

    @property
    @abstractmethod
    def x(self):
        '''
        x :: -> z3.BitVec
        '''
        pass

    @property
    @abstractmethod
    def y(self):
        '''
        y :: -> z3.BitVec
        '''
        pass

    @abstractmethod
    def delta_x(self, other):
        '''
        delta_x :: PositionBase -> (z3.Bool, z3.BitVec)
        '''
        pass

    @abstractmethod
    def delta_y(self, other):
        '''
        delta_y :: PositionBase -> (z3.Bool, z3.BitVec)
        '''
        pass

    @abstractmethod
    def delta_x_fun(self, other):
        '''
        delta_x :: PositionBase -> (int -> z3.Bool)
        builds a function f such that f(c) => delta_x == c
        '''
        pass

    @abstractmethod
    def delta_y_fun(self, other):
        '''
        delta_y :: PositionBase -> (int -> z3.Bool)
        builds a function f such that f(c) => delta_y == c
        '''
        pass

    @property
    @abstractmethod
    def invariants(self):
        '''
        invariants :: -> z3.Bool
        '''
        pass

    @abstractmethod
    def get_coordinates(self):
        '''
        get_coordinates :: z3.ModelRef -> (int, int)

        evaluates the model at self and returns 0 indexed x,y coardinates
        '''
        pass


class IntXY(PositionBase):
    def __init__(self, name, fabric, width, height, solver):
        super().__init__(name, fabric, solver)
        self._x = self.solver.declare_const(name + '_x', intsort)
        self._y = self.solver.declare_const(name + '_y', intsort)
        self._width = width
        self._height = height
        self._horiz_var = self.solver.declare_const(name + '_width', intsort)
        self._vert_var = self.solver.declare_const(name + '_height', intsort)

    @staticmethod
    def pos_repr(n):
        ''' returns the representation of an x or y coordinate in this encoding'''
        return n

    def delta_x(self, other):
        return [], self.x - other.x

    def delta_y(self, other):
        return [], self.y - other.y

    # Note: These delta's are NOT absolute value
    def delta_x_fun(self, other):
        def delta_fun(constant):
            return And(self.x - other.x < other._horiz_var + constant,
                       other.x - self.x < self._horiz_var + constant)
        return delta_fun

    def delta_y_fun(self, other):
        def delta_fun(constant):
            return And(self.y - other.y < other._vert_var + constant,
                       other.y - self.y < self._vert_var + constant)
        return delta_fun

    @property
    def flat(self):
        raise ValueError('flat does not make sense with position.IntXY')

    @property
    def x(self):
        return self._x

    @property
    def y(self):
        return self._y

    @property
    def width(self):
        return self._width

    @property
    def height(self):
        return self._height

    @property
    def horiz_var(self):
        return self._horiz_var

    @property
    def vert_var(self):
        return self._vert_var

    @property
    def invariants(self):
        cols = self.get_theory_const(self.fabric.cols)
        rows = self.get_theory_const(self.fabric.rows)
        height = self.get_theory_const(self._height)
        width = self.get_theory_const(self._width)
        return And(self._x >= 0, self._x + self._horiz_var <= cols,
                      self._y >= 0, self._y + self._vert_var <= rows,
                      Or(And(self._horiz_var == width, self._vert_var == height),
                         And(self._horiz_var == height, self._vert_var == width)))

    def get_coordinates(self):
        return (self.solver.get_value(self.x).as_int(), self.solver.get_value(self.y).as_int())

    def get_vh(self, model):
        ''' Returns a tuple containing the vertical and horizontal variables
             -- these can be negative which represents a rotation
        '''
        return (self.solver.get_value(self.vert_var).as_int(), self.solver.get_value(self.horiz_var).as_int())


class RotXYBase(PositionBase, metaclass=ABCMeta):
    @abstractmethod
    def __init__(self, name, fabric, width, height, solver):
        super().__init__(name, fabric, solver)
        self._width = width
        self._height = height
        self._d0 = self.solver.declare_const(name + '_d0', boolsort)
        self._d90 = self.solver.declare_const(name + '_d90', boolsort)
        self._d180 = self.solver.declare_const(name + '_d180', boolsort)
        self._d270 = self.solver.declare_const(name + '_d270', boolsort)

    @staticmethod
    def pos_repr(n):
        ''' returns the representation of an x or y coordinate in this encoding'''
        return n

    @abstractmethod
    def get_theory_const(self, value):
        ''' returns a theory constant specific to the solver and theory with the given value '''
        pass

    def delta_x(self, other):
        raise NotImplementedError()

    def delta_y(self, other):
        raise NotImplementedError()

    def padx_loc(self, pad1x, pad1y):
        pad1x = self.get_theory_const(pad1x)
        pad1y = self.get_theory_const(pad1y)
        height = self.get_theory_const(self._height)
        width = self.get_theory_const(self._width)
        return Ite(self._d0, self._x + pad1x,
                   Ite(self._d90, self._x + pad1y,
                       Ite(self._d180, self._x + width - pad1x,
                           self._x + height - pad1y)))

    def pady_loc(self, pad1x, pad1y):
        pad1x = self.get_theory_const(pad1x)
        pad1y = self.get_theory_const(pad1y)
        height = self.get_theory_const(self._height)
        width = self.get_theory_const(self._width)
        return Ite(self._d0, self._y + pad1y,
                   Ite(self._d90, self._y + width - pad1x,
                       Ite(self._d180, self._y + height - pad1y,
                       self._y + pad1x)))

    def pad_delta_x(self, pad1x, pad1y, other, pad2x, pad2y):
        return su.Abs(self.padx_loc(pad1x, pad1y) - other.padx_loc(pad2x, pad2y))

    def pad_delta_y(self, pad1x, pad1y, other, pad2x, pad2y):
        return su.Abs(self.pady_loc(pad1x, pad1y) - other.pady_loc(pad2x, pad2y))

    def pad_dist_lt(self, pad1x, pad1y, other, pad2x, pad2y, constant):
        constant = self.get_theory_const(constant)
        return self.pad_delta_x(pad1x, pad1y, other, pad2x, pad2y) \
            + self.pad_delta_y(pad1x, pad1y, other, pad2x, pad2y) \
            <= constant

    #Note: These delta's are NOT absolute value
    def delta_x_fun(self, other):
        def delta_fun(constant):
            constant = self.get_theory_const(constant)
            return And(self.x - other.x < other._horiz_var + constant,
                       other.x - self.x < self._horiz_var + constant)
        return delta_fun

    def delta_y_fun(self, other):
        def delta_fun(constant):
            constant = self.get_theory_const(constant)
            return And(self.y - other.y < other._vert_var + constant,
                       other.y - self.y < self._vert_var + constant)
        return delta_fun

    @property
    def flat(self):
        raise ValueError('flat does not make sense with position.IntXY')

    @property
    @abstractmethod
    def x(self):
        pass

    @property
    @abstractmethod
    def y(self):
        pass

    @property
    def width(self):
        return self._width

    @property
    def height(self):
        return self._height

    @property
    def horiz_var(self):
        return self._horiz_var

    @property
    def vert_var(self):
        return self._vert_var

    @property
    def invariants(self):
        height = self.get_theory_const(self._height)
        width = self.get_theory_const(self._width)
        cols = self.get_theory_const(self.fabric.cols)
        rows = self.get_theory_const(self.fabric.rows)
        zero = self.get_theory_const(0)
        one_rotation = su.exactly_one(self._d0, self._d90, self._d180, self._d270)
        states = Ite(Or(self._d0, self._d180),
                     And(self._horiz_var == width, self._vert_var == height),
                     And(self._horiz_var == height, self._vert_var == width))
        on_fab = And(self._x >= zero, self._x + self._horiz_var <= cols,
                     self._y >= zero, self._y + self._vert_var <= rows)
        return And(one_rotation, states, on_fab)

    def get_rotation(self):
        '''
        Returns rotation relative to input orientation
        '''
        d0 = self.solver.get_value(self._d0)
        d90 = self.solver.get_value(self._d90)
        d180 = self.solver.get_value(self._d180)
        d270 = self.solver.get_value(self._d270)
        if d0:
            return 0
        elif d90:
            return pi/2
        elif d180:
            return pi
        elif d270:
            return 3*pi/2
        else:
            raise ValueError('Solver produced invalid rotation!')


class RotIntXY(RotXYBase):
    def __init__(self, name, fabric, width, height, solver):
        super().__init__(name, fabric, width, height, solver)
        self._x = self.solver.declare_const(name + '_x', intsort)
        self._y = self.solver.declare_const(name + '_y', intsort)
        self._horiz_var = self.solver.declare_const(name + '_horiz', intsort)
        self._vert_var = self.solver.declare_const(name + '_vert', intsort)

    @property
    def x(self):
        return self._x

    @property
    def y(self):
        return self._y

    def get_theory_const(self, value):
        return self.solver.theory_const(intsort, value)

    def get_coordinates(self):
        return (self.solver.get_value(self.x).as_int(), self.solver.get_value(self.y).as_int())


class RotRealXY(RotXYBase):
    def __init__(self, name, fabric, width, height, solver):
        super().__init__(name, fabric, width, height, solver)
        self._x = self.solver.declare_const(name + '_x', realsort)
        self._y = self.solver.declare_const(name + '_y', realsort)
        self._horiz_var = self.solver.declare_const(name + '_horiz', realsort)
        self._vert_var = self.solver.declare_const(name + '_vert', realsort)


    @property
    def x(self):
        return self._x

    @property
    def y(self):
        return self._y

    def get_theory_const(self, value):
        return self.solver.theory_const(realsort, value)

    def get_coordinates(self):
        x = self.solver.get_value(self.x).as_double()
        y = self.solver.get_value(self.y).as_double()
        return (x, y)


class RotBVXY(RotXYBase):
    def __init__(self, name, fabric, width, height, solver):
        super().__init__(name, fabric, width, height, solver)
        #if 2**(self.fabric.cols.bit_length()-1) == self.fabric.cols:
            # adding extra bit to avoid overflow adjacency
        #    self._x_bits    = self.fabric.cols.bit_length()
        #    self._is_x_pow2 = True 
        #else:
        #    self._x_bits    = self.fabric.cols.bit_length()
        #    self._is_x_pow2 = False
        #if 2**(self.fabric.rows.bit_length()-1) == self.fabric.rows:
            # adding extra bit to avoid overflow adjacency
        #    self._y_bits    = self.fabric.rows.bit_length()
        #    self._is_y_pow2 = True
        #else:
        #    self._y_bits    = self.fabric.rows.bit_length()
        #    self._is_y_pow2 = False

        # using a standard (conservative) bit width
        self._bit_width = max(self.fabric.cols.bit_length(), self.fabric.rows.bit_length()) + 2

        # For now, easiest to just add extra bit so don't have to worry about overflow
        self._bvsort = sorts.BitVec(self._bit_width)
        self._x = solver.declare_const(self.name + '_x', self._bvsort)
        self._y = solver.declare_const(self.name + '_y', self._bvsort)
        self._horiz_var = self.solver.declare_const(name + '_horiz', self._bvsort)
        self._vert_var = self.solver.declare_const(name + '_vert', self._bvsort)

    def get_theory_const(self, value):
        # Can't determine bit width from passed value...not implementing
        return self._solver.theory_const(self._bvsort, value)

    def delta_x(self, other):
        return [], su.absolute_value(self.x - other.x)

    def delta_y(self, other):
        return [], su.absolute_value(self.y - other.y)

    def delta_x_fun(self, other):
        def delta_fun(constant):
            _, c = self.delta_x(other)
            return c == constant
        return delta_fun

    def delta_y_fun(self, other):
        def delta_fun(constant):
            _, c = self.delta_y(other)
            return c == constant
        return delta_fun

    def padx_loc(self, pad1x, pad1y):
        pad1x = self._solver.theory_const(self._bvsort, pad1x)
        pad1y = self._solver.theory_const(self._bvsort, pad1y)
        height = self.get_theory_const(self._height)
        width = self.get_theory_const(self._width)
        return Ite(self._d0, self._x + pad1x,
                   Ite(self._d90, self._x + pad1y,
                       Ite(self._d180, self._x + width - pad1x,
                           self._x + height - pad1y)))

    def pady_loc(self, pad1x, pad1y):
        pad1x = self._solver.theory_const(self._bvsort, pad1x)
        pad1y = self._solver.theory_const(self._bvsort, pad1y)
        height = self.get_theory_const(self._height)
        width = self.get_theory_const(self._width)
        return Ite(self._d0, self._y + pad1y,
                   Ite(self._d90, self._y + width - pad1x,
                       Ite(self._d180, self._y + height - pad1y,
                           self._y + pad1x)))

    def pad_delta_x(self, pad1x, pad1y, other, pad2x, pad2y):
        return su.absolute_value(self.padx_loc(pad1x, pad1y) - other.padx_loc(pad2x, pad2y))

    def pad_delta_y(self, pad1x, pad1y, other, pad2x, pad2y):
        return su.absolute_value(self.pady_loc(pad1x, pad1y) - other.pady_loc(pad2x, pad2y))

    def pad_dist_lt(self, pad1x, pad1y, other, pad2x, pad2y, constant):
        constant = self.get_theory_const(constant)
        return bvule(self.pad_delta_x(pad1x, pad1y, other, pad2x, pad2y)
                     + self.pad_delta_y(pad1x, pad1y, other, pad2x, pad2y),
                     constant)

    @property
    def flat(self):
        return concat(self.x, self.y)

    @property
    def x(self):
        return self._x

    @property
    def y(self):
        return self._y

    @property
    def invariants(self):
        # height = self.get_theory_const(self._height)
        # width = self.get_theory_const(self._width)
        extmsb = functions.extract(self._bvsort.width - 1, self._bvsort.width - 1)
        msb_0 = And(extmsb(self._x) == 0, extmsb(self._y) == 0)
        one_rotation = su.exactly_one(self._d0, self._d90, self._d180, self._d270)
        states = Ite(Or(self._d0, self._d180),
                     And(self._horiz_var == self._width, self._vert_var == self._height),
                     And(self._horiz_var == self._height, self._vert_var == self._width))
        on_fab = And(bvuge(self._x, 0), bvule(self._x + self._horiz_var, self.fabric.cols),
                     bvuge(self._y, 0), bvule(self._y + self._vert_var, self.fabric.rows),
                     bvule(self._x, self.fabric.cols), bvule(self._y, self.fabric.rows))
        # Note: Have to enforce that x/y don't go over fabric separately from x + horiz etc...
        # because otherwise can satisfy with overflow

        # For now we always have extra bits
        #if self._is_x_pow2:
        #    ix = self._x_bits - 1
        #    ext = functions.extract(ix, ix)
        #    constraint.append(ext(self.x) == 0)
        #else:
        #    constraint.append(bvult(self.x, self.fabric.cols))
        #if self._is_y_pow2:
        #    iy = self._y_bits - 1
        #    ext = functions.extract(iy, iy)
        #    constraint.append(ext(self.y) == 0)
        #else:
        #    constraint.append(bvult(self.y, self.fabric.rows))
        return And(msb_0, one_rotation, states, on_fab)

    def get_coordinates(self):
        return (self.solver.get_value(self.x).as_int(), self.solver.get_value(self.y).as_int())

    def encode(self, p):
        return self.encode_x(p[0]), self.encode_y(p[1])

    def encode_x(self, x):
        return self.solver.theory_const(sorts.BitVec(self._bit_width), x)

    def encode_y(self, y):
        return self.solver.theory_const(sorts.BitVec(self._bit_width), y)
