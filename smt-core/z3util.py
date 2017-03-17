import z3
import operator
import functools as ft


def exactly_one(x, y, z, w):
    '''
    Takes four bools and returns a constraint that is true iff exactly 
    one of them is true
    '''

    return z3.Or(z3.And(z3.Not(x), z3.Not(y), z3.Not(z), w),
                 z3.And(z3.Not(x), z3.Not(y), z        , z3.Not(w)),
                 z3.And(z3.Not(x), y        , z3.Not(z), z3.Not(w)),
                 z3.And(x        , z3.Not(y), z3.Not(z), z3.Not(w)))



def absolute_value(bv):
    '''
    Based on: https://graphics.stanford.edu/~seander/bithacks.html#IntegerAbs

    Operation:
        Desired behavior is by definition (bv < 0) ? -bv : bv
        Now let mask := bv >> (bv.size() - 1)
        Note because of sign extension:
            bv >> (bv.size() - 1) == (bv < 0) ? -1 : 0

        Recall:
            -x == ~x + 1 => ~(x - 1) == -(x - 1) -1 == -x
            ~x == -1^x
             x ==  0^x

        now if bv < 0 then -bv == -1^(bv - 1) == mask ^ (bv + mask)
        else bv == 0^(bv + 0) == mask^(bv + mask)
        hence for all bv, absolute_value(bv) == mask ^ (bv + mask)
    '''
    mask = bv >> (bv.size() - 1)
    return mask ^ (bv + mask)


def z3abs(x):
    '''
    Absolute value for integer encoding
    '''
    return z3.If(x >= 0, x, -x)



