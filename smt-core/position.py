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



class Base2H(PositionBase):
    '''
    Base class for 2 hot representations
    '''

    def __init__(self, name, fabric):
        super().__init__(name, fabric)

    @staticmethod
    def pos_repr(n):
        ''' returns the representation of an x or y coordinate in this encoding'''
        return 2**n
        

    def delta_x(self, other):
        delta_x = z3.BitVec(self.name+'-'+other.name+'_delta_x', self.fabric.cols)
        constraint = z3.Or(self.x == other.x << delta_x, other.x == self.x << delta_x)
        return constraint, delta_x

    def delta_y(self, other):
        delta_y = z3.BitVec(self.name+'-'+other.name+'_delta_y', self.fabric.rows)
        constraint = z3.Or(self.y == other.y << delta_y, other.y == self.y << delta_y)
        return constraint, delta_y

    def delta_x_fun(self, other):
        def delta_fun(constant):
            if constant == 0:
                return self.x == other.x
            else:
                return z3.Or(self.x == other.x << constant, other.x == self.x << constant)
        return delta_fun

    def delta_y_fun(self, other):
        def delta_fun(constant):
            if constant == 0:
                return self.y == other.y
            else:
                return z3.Or(self.y == other.y << constant, other.y == self.y << constant)
        return delta_fun

    @property
    def invariants(self):
        return z3.And(zu.hamming(self.x) == 1, zu.hamming(self.y) == 1)

    def get_coordinates(self, model):
        return (int(log2(model.eval(self.x).as_long())), int(log2(model.eval(self.y).as_long())))


class Packed2H(Base2H):
    '''
    2 Hot representation, packed into a single BitVec
    '''
    def __init__(self, name, fabric):
        super().__init__(name, fabric)
        self._flat = z3.BitVec(self.name + '_flat', self.fabric.rows + self.fabric.cols)

    @property
    def flat(self):
        return self._flat

    @property
    def x(self):
        return z3.Extract(self.fabric.rows + self.fabric.cols-1, self.fabric.rows, self.flat)

    @property
    def y(self):
        return z3.Extract(self.fabric.rows-1, 0, self.flat)

class Unpacked2H(Base2H):
    '''
    2 Host representation, x and y in seperate BitVec
    '''
    def __init__(self, name, fabric):
        super().__init__(name, fabric)
        self._x = z3.BitVec(self.name + '_x', self.fabric.cols)
        self._y = z3.BitVec(self.name + '_y', self.fabric.rows)

    @property
    def flat(self):
        return z3.Concat(self.x, self.y)

    @property
    def x(self):
        return self._x

    @property
    def y(self):
        return self._y


class BVXY(PositionBase):
    def __init__(self, name, fabric):
        super().__init__(name, fabric)
        if 2**(self.fabric.cols.bit_length()-1) == self.fabric.cols:
            #adding extra bit to avoid overflow adjacency
            self._x = z3.BitVec(self.name + '_x', 1+self.fabric.cols.bit_length())
            self._is_x_pow2 = True
        else:
            self._x = z3.BitVec(self.name + '_x', self.fabric.cols.bit_length())
            self._is_x_pow2 = False
        if 2**(self.fabric.rows.bit_length()-1) == self.fabric.rows:
            #adding extra bit to avoid overflow adjacency
            self._y = z3.BitVec(self.name + '_y', 1+self.fabric.rows.bit_length())
            self._is_y_pow2 = True
        else:
            self._y = z3.BitVec(self.name + '_y', self.fabric.rows.bit_length())
            self._is_y_pow2 = False

    @staticmethod
    def pos_repr(n):
        ''' returns the representation of an x or y coordinate in this encoding'''
        return n

    def delta_x(self, other):
        return [], zu.absolute_value(self.x - other.x)

    def delta_y(self, other):
        return [], zu.absolute_value(self.y - other.y)

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

    @property
    def flat(self):
        return z3.Concat(self.x, self.y)

    @property
    def x(self):
        return self._x

    @property
    def y(self):
        return self._y

    @property
    def invariants(self):
        constraint = []
        if self._is_x_pow2:
            ix = self.fabric.cols.bit_length()
            constraint.append(z3.Extract(ix, ix, self.x) == 0)
        else:
            constraint.append(z3.ULT(self.x, self.fabric.cols))
        if self._is_y_pow2:
            iy = self.fabric.rows.bit_length()
            constraint.append(z3.Extract(iy, iy, self.y) == 0)
        else:
            constraint.append(z3.ULT(self.y, self.fabric.rows))
        return z3.And(constraint)

    def get_coordinates(self, model):
        return (model.eval(self.x).as_long(), model.eval(self.y).as_long())


class IntXY(PositionBase):
    def __init__(self, name, fabric, dim1, dim2):
        super().__init__(name, fabric)
        self._x = z3.Int(name + '_x')
        self._y = z3.Int(name + '_y')
        self._dim1 = dim1
        self._dim2 = dim2
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
    def dim1(self):
        return self._dim1

    @property
    def dim2(self):
        return self._dim2

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
                      z3.Or(z3.And(self._horiz_var == self._dim1, self._vert_var == self._dim2),
                            z3.And(self._horiz_var == self._dim2, self._vert_var == self._dim1)))

    def get_coordinates(self, model):
        return (model.eval(self.x).as_long(), model.eval(self.y).as_long())

    def get_vh(self, model):
        ''' Returns a tuple containing the vertical and horizontal variables
             -- these can be negative which represents a rotation
        '''
        return (model.eval(self._vert_var).as_long(), model.eval(self._horiz_var).as_long())


class RotIntXY(PositionBase):
    def __init__(self, name, fabric, width, height):
        super().__init__(name, fabric)
        self._x = z3.Int(name + '_x')
        self._y = z3.Int(name + '_y')
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
        #TODO: Implement with rotation!
        #return [], self.x - other.x
        return self.padx_loc(pad1x, pad1y) - other.padx_loc(pad2x, pad2y)

    def pad_delta_y(self, pad1x, pad1y, other, pad2x, pad2y):
        #TODO: Implement with rotation!
        #return [], self.y - other.y
        return self.pady_loc(pad1x, pad1y) - other.pady_loc(pad2x, pad2y)

    def pad_dist_lt(self, pad1x, pad1y, other, pad2x, pad2y, constant):
        return zu.z3abs(self.pad_delta_x(pad1x, pad1y, other, pad2x, pad2y)) \
            + zu.z3abs(self.pad_delta_y(pad1x, pad1y, other, pad2x, pad2y)) \
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
        #TODO: Implement with rotation!
        one_rotation = zu.exactly_one(self._d0, self._d90, self._d180, self._d270)
        states = z3.If(z3.Or(self._d0, self._d180),
                       z3.And(self._horiz_var == self._width, self._vert_var == self._height),
                      z3.And(self._horiz_var == self._height, self._vert_var == self._width))
        on_fab = z3.And(self._x >= 0, self._x + self._horiz_var <= self.fabric.cols,
                        self._y >= 0, self._y + self._vert_var <= self.fabric.rows)
        #return z3.And(self._x >= 0, self._x + self._horiz_var <= self.fabric.cols,
        #              self._y >= 0, self._y + self._vert_var <= self.fabric.rows,
        #              z3.Or(z3.And(self._horiz_var == self._width, self._vert_var == self._height),
        #                   z3.And(self._horiz_var == self._height, self._vert_var == self._width)))
        return z3.And(one_rotation, states, on_fab)

    def get_coordinates(self, model):
        return (model.eval(self.x).as_long(), model.eval(self.y).as_long())

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
