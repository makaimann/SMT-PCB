from abc import ABCMeta, abstractmethod
from math import log2, ceil, pi
import z3util as zu
import z3

class PositionBase(metaclass=ABCMeta):
    def __init__(self, name, fabric):
        self._name = name
        self._fabric = fabric

    @property
    def name(self):
        return self._name

    @property
    def fabric(self):
        return self._fabric

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
    def __init__(self, name, fabric, width, height):
        super().__init__(name, fabric)
        self._x = z3.Int(name + '_x')
        self._y = z3.Int(name + '_y')
        self._width = width
        self._height = height
        self._horiz_var = z3.Int(name + '_width')
        self._vert_var = z3.Int(name + '_height')

    @staticmethod
    def pos_repr(n):
        ''' returns the representation of an x or y coordinate in this encoding'''
        return n

    def delta_x(self, other):
        return [], self.x - other.x

    def delta_y(self, other):
        return [], self.y - other.y

    #Note: These delta's are NOT absolute value
    def delta_x_fun(self, other):
        def delta_fun(constant):
            return z3.And(self.x - other.x < other._horiz_var + constant,
                          other.x - self.x < self._horiz_var + constant)
        return delta_fun

    def delta_y_fun(self, other):
        def delta_fun(constant):
            return z3.And(self.y - other.y < other._vert_var + constant,
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
        return z3.And(self._x >= 0, self._x + self._horiz_var <= self.fabric.cols,
                      self._y >= 0, self._y + self._vert_var <= self.fabric.rows,
                      z3.Or(z3.And(self._horiz_var == self._width, self._vert_var == self._height),
                            z3.And(self._horiz_var == self._height, self._vert_var == self._width)))

    def get_coordinates(self, model):
        return (model.eval(self.x).as_long(), model.eval(self.y).as_long())

    def get_vh(self, model):
        ''' Returns a tuple containing the vertical and horizontal variables
             -- these can be negative which represents a rotation
        '''
        return (model.eval(self._vert_var).as_long(), model.eval(self._horiz_var).as_long())


class RotXYBase(PositionBase, metaclass=ABCMeta):
    @abstractmethod
    def __init__(self, name, fabric, width, height):
        super().__init__(name, fabric)
        self._width = width
        self._height = height
        self._d0 = z3.Bool(name + '_d0')
        self._d90 = z3.Bool(name + '_d90')
        self._d180 = z3.Bool(name + '_d180')
        self._d270 = z3.Bool(name + '_d270')
        self._horiz_var = z3.Int(name + '_horiz')
        self._vert_var = z3.Int(name + '_vert')

    @staticmethod
    def pos_repr(n):
        ''' returns the representation of an x or y coordinate in this encoding'''
        return n

    def delta_x(self, other):
        raise NotImplementedError()

    def delta_y(self, other):
        raise NotImplementedError()

    def padx_loc(self, pad1x, pad1y):
        return z3.If(self._d0, self._x + pad1x,
                     z3.If(self._d90, self._x + pad1y,
                           z3.If(self._d180, self._x + self._width - pad1x,
                                 self._x + self._height - pad1y)))

    def pady_loc(self, pad1x, pad1y):
        return z3.If(self._d0, self._y + pad1y,
                     z3.If(self._d90, self._y + self._width - pad1x,
                           z3.If(self._d180, self._y + self._height - pad1y,
                                 self._y + pad1x)))

    def pad_delta_x(self, pad1x, pad1y, other, pad2x, pad2y):
        return zu.z3abs(self.padx_loc(pad1x, pad1y) - other.padx_loc(pad2x, pad2y))

    def pad_delta_y(self, pad1x, pad1y, other, pad2x, pad2y):
        return zu.z3abs(self.pady_loc(pad1x, pad1y) - other.pady_loc(pad2x, pad2y))

    def pad_dist_lt(self, pad1x, pad1y, other, pad2x, pad2y, constant):
        return self.pad_delta_x(pad1x, pad1y, other, pad2x, pad2y) \
            + self.pad_delta_y(pad1x, pad1y, other, pad2x, pad2y) \
            <= constant

    #Note: These delta's are NOT absolute value
    def delta_x_fun(self, other):
        def delta_fun(constant):
            return z3.And(self.x - other.x < other._horiz_var + constant,
                          other.x - self.x < self._horiz_var + constant)
        return delta_fun

    def delta_y_fun(self, other):
        def delta_fun(constant):
            return z3.And(self.y - other.y < other._vert_var + constant,
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
        #TODO: Implement with rotation!
        one_rotation = zu.exactly_one(self._d0, self._d90, self._d180, self._d270)
        states = z3.If(z3.Or(self._d0, self._d180),
                       z3.And(self._horiz_var == self._width, self._vert_var == self._height),
                      z3.And(self._horiz_var == self._height, self._vert_var == self._width))
        on_fab = z3.And(self._x >= 0, self._x + self._horiz_var <= self.fabric.cols,
                        self._y >= 0, self._y + self._vert_var <= self.fabric.rows)
        return z3.And(one_rotation, states, on_fab)

    def get_rotation(self, model):
        '''
        Returns rotation relative to input orientation
        '''
        d0 =  model.eval(self._d0).sexpr()
        d90 =  model.eval(self._d90).sexpr()
        d180 =  model.eval(self._d180).sexpr()
        d270 =  model.eval(self._d270).sexpr()
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
    def __init__(self, name, fabric, width, height):
        super().__init__(name, fabric, width, height)
        self._x = z3.Int(name + '_x')
        self._y = z3.Int(name + '_y')

    @property
    def x(self):
        return self._x

    @property
    def y(self):
        return self._y

    def get_coordinates(self, model):
        return (model.eval(self.x).as_long(), model.eval(self.y).as_long())

    
class RotRealXY(RotXYBase):
    def __init__(self, name, fabric, width, height):
        super().__init__(name, fabric, width, height)
        self._x = z3.Real(name + '_x')
        self._y = z3.Real(name + '_y')

    @property
    def x(self):
        return self._x

    @property
    def y(self):
        return self._y

    def get_coordinates(self, model):
        xref = model.eval(self.x)
        yref = model.eval(self.y)
        x = xref.numerator_as_long()/xref.denominator_as_long()
        y = yref.numerator_as_long()/yref.denominator_as_long()
        return (x, y)
