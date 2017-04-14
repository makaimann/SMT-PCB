from abc import ABCMeta, abstractmethod
from math import pi
import solverutil as su
import sorts
import functions

# Sorts
intsort = sorts.Int()
realsort = sorts.Real()
boolsort = sorts.Bool()

# functions
And = functions.And()
Or = functions.Or()
Ite = functions.Ite()


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
    def get_coordinates(self, model):
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
        return (int(self.solver.get_value(self.x)), int(self.solver.get_value(self.y)))

    def get_vh(self, model):
        ''' Returns a tuple containing the vertical and horizontal variables
             -- these can be negative which represents a rotation
        '''
        return (int(self.solver.get_value(self.vert_var)), int(self.solver.get_value(self.horiz_var)))


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
        self._horiz_var = self.solver.declare_const(name + '_horiz', intsort)
        self._vert_var = self.solver.declare_const(name + '_vert', intsort)

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
        d0 = self.solver.get_value(self._d0).lower()
        d90 = self.solver.get_value(self._d90).lower()
        d180 = self.solver.get_value(self._d180).lower()
        d270 = self.solver.get_value(self._d270).lower()
        if d0 == 'true':
            return 0
        elif d90 == 'true':
            return pi/2
        elif d180 == 'true':
            return pi
        elif d270 == 'true':
            return 3*pi/2
        else:
            raise ValueError('Solver produced invalid rotation!')


class RotIntXY(RotXYBase):
    def __init__(self, name, fabric, width, height, solver):
        super().__init__(name, fabric, width, height, solver)
        self._x = self.solver.declare_const(name + '_x', intsort)
        self._y = self.solver.declare_const(name + '_y', intsort)

    @property
    def x(self):
        return self._x

    @property
    def y(self):
        return self._y

    def get_theory_const(self, value):
        return self.solver.theory_const(intsort, value)

    def get_coordinates(self):
        return (int(self.solver.get_value(self.x)), int(self.solver.get_value(self.y)))


class RotRealXY(RotXYBase):
    def __init__(self, name, fabric, width, height, solver):
        super().__init__(name, fabric, width, height, solver)
        self._x = self.solver.declare_const(name + '_x', realsort)
        self._y = self.solver.declare_const(name + '_y', realsort)

    @property
    def x(self):
        return self._x

    @property
    def y(self):
        return self._y

    def get_theory_const(self, value):
        return self.solver.theory_const(realsort, value)

    def get_coordinates(self):
        # currently only support z3
        # model = self.solver.get_model()
        # xref = model.eval(self.x.solver_term)
        # yref = model.eval(self.y.solver_term)
        # x = xref.numerator_as_long()/xref.denominator_as_long()
        # y = yref.numerator_as_long()/yref.denominator_as_long()
        x = eval(self.solver.get_value(self.x))
        y = eval(self.solver.get_value(self.y))
        return (x, y)
