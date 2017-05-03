#!/usr/bin/env python3

# Steven Herbst
# sherbst@stanford.edu

# Place PCB using z3

import json
import argparse
import sys

import z3
import itertools

from math import radians, degrees

from pcbgeom import *
from pcblib import *

def main():
    # Parse command-line arguments
    parser = argparse.ArgumentParser(description='Place PCB design.')
    parser.add_argument('infile')
    parser.add_argument('--limit', type=float, default=None)
    args = parser.parse_args()

    # Parse file
    print('Reading design from file...')
    with open(args.infile, 'r') as f:
        design = Design.fromDict(json.load(f))

    s = z3.Solver()

    # Create design variables
    makeDesignVariables(s, design)

    # Constrain free components to be on the board
    print('Adding onBoard constraints...')
    for mod in design.modules:
        if not mod.fixed:
            s.add(onBoard(mod, design.border))

    # Constrain pairs of components no to overlap 
    print('Adding noOverlap constraints...')
    for mod1, mod2 in itertools.combinations(design.modules, 2):
        if mod1.fixed and mod2.fixed:
            continue
        s.add(noOverlap(mod1, mod2))

    # If desired, constrain the sum of net semiperimeters
    if args.limit is not None:
        print('Adding semiPerim constraint...')
        addSemiPerimConstr(s, design, args.limit)

    # Solve the placement problem
    print('Solving SMT problem...')
    result = s.check()
    if result == z3.unsat:
        raise Exception('Problem is not SAT.')
    else:
        print('Problem is SAT.')

    # Get the SMT solution model
    print('Getting SMT solution model...')
    model = s.model()

    # make design variables
    print('Updating module positions...')
    updateModsFromSMT(design, model)

    # Convert to design
    print('Writing design to file...')
    with open(args.infile, 'w') as f:
        json.dump(design.toDict(), f, indent=2, sort_keys=True)

def makeDesignVariables(s, design):
    """
    Create the SMT solver design variables for all modules in the design.
    """
    for mod in design.modules:
        mod.varX = z3.Real(mod.reference + '.x')
        mod.varY = z3.Real(mod.reference + '.y')
        mod.varRot90 = z3.Bool(mod.reference + '.rot90')
        mod.varRot180 = z3.Bool(mod.reference + '.rot180')

        # if the module is fixed, constrain its position and rotation
        if mod.fixed:
            s.add(mod.varX == getX(mod.pos))
            s.add(mod.varY == getY(mod.pos))

            itheta = round(degrees(mod.theta)/90.0)
            s.add(mod.varRot90  == bool((itheta >> 0) % 2))
            s.add(mod.varRot180 == bool((itheta >> 1) % 2))

def addSemiPerimConstr(s, design, limit):
    """
    Constrain the sum of net semiperimeters to be less than a target.
    """
    sbbList = []
    for netname, padList in design.buildNetDict().items():
        sbb = buildSBB(s, netname, padList)
        sbbList.append(sbb.width + sbb.height)
    s.add(z3.Sum(sbbList) <= limit)

def updateModsFromSMT(design, model):
    """
    Update module position and rotation based on the output of the SMT solver.
    """
    for mod in design.modules:
        # calculate module position
        mod.pos = xy2p(toFloat(model[mod.varX]), toFloat(model[mod.varY]))

        # calculate module rotation
        mod.theta = 0
        if z3.is_true(model[mod.varRot90]):
            mod.theta += 90.0
        if z3.is_true(model[mod.varRot180]):
            mod.theta += 180.0
        mod.theta = radians(mod.theta)

def onBoard(mod, border, bits=[]):
    """
    Constrain the given module to be on the board
    """
    if len(bits)==2:
        return onBoardDeg(mod, border, 180*bits[1] + 90*bits[0])
    else:
        var = {1: mod.varRot180, 0: mod.varRot90}[len(bits)]
        return z3.If(var, onBoard(mod, border, bits+[1]), onBoard(mod, border, bits+[0]))

def onBoardDeg(mod, border, deg):
    """
    Conditions for mod to be on the board when it has rotation deg.
    """
    rbb = rotBoundingBox(mod, deg)
    return z3.And(0 <= mod.varX+rbb.xmin, mod.varX+rbb.xmax <= border.width,
                  0 <= mod.varY+rbb.ymin, mod.varY+rbb.ymax <= border.height)

def noOverlap(mod1, mod2, bits=[]):
    """
    Constrain mod1 and mod2 not to overlap
    """
    if len(bits)==4:
        return noOverlapDeg(mod1, mod2, 180*bits[3] + 90*bits[2], 180*bits[1] + 90*bits[0])
    else:
        var = {3: mod1.varRot180, 2: mod1.varRot90, 1: mod2.varRot180, 0: mod2.varRot90}[len(bits)]
        return z3.If(var, noOverlap(mod1, mod2, bits+[1]), noOverlap(mod1, mod2, bits+[0]))

def noOverlapDeg(mod1, mod2, deg1, deg2):
    """
    Conditions for mod1 and mod2 not to overlap when mod1 has rotation deg1
    and mod2 has rotation deg2.
    """
    rbb1 = rotBoundingBox(mod1, deg1)
    rbb2 = rotBoundingBox(mod2, deg2)
    return z3.Or(mod1.varX+rbb1.xmax <= mod2.varX+rbb2.xmin,
                 mod2.varX+rbb2.xmax <= mod1.varX+rbb1.xmin,
                 mod1.varY+rbb1.ymax <= mod2.varY+rbb2.ymin,
                 mod2.varY+rbb2.ymax <= mod1.varY+rbb1.ymin)

def rotBoundingBox(mod, deg):
    """
    Returns the bounding box of mod after rotating by deg
    """
    return BoundingBox(rotate(mod.rect, radians(deg)))

class SmtBoundingBox:
    """
    Class used to store bounding box logic for computing net semiperimeters.
    """
    def __init__(self, netname):
        self.xmin = z3.Real(netname + '.xmin')
        self.xmax = z3.Real(netname + '.xmax')
        self.ymin = z3.Real(netname + '.ymin')
        self.ymax = z3.Real(netname + '.ymax')

    @property
    def width(self):
        return self.xmax - self.xmin

    @property
    def height(self):
        return self.ymax - self.ymin

def buildSBB(s, netname, padList):
    """
    Builds the logic for a bounding box of pads on a given net.
    """
    sbb = SmtBoundingBox(netname)
    for pad in padList:
        s.add(padInSBB(pad, sbb))
    return sbb

def padInSBB(pad, sbb, bits=[]):
    """
    Constrains the given pad to be in a bounding box.
    """
    if len(bits)==2:
        return padInSbbDeg(pad, sbb, 180*bits[1] + 90*bits[0])
    else:
        var = {1: pad.mod.varRot180, 0: pad.mod.varRot90}[len(bits)]
        return z3.If(var, padInSBB(pad, sbb, bits+[1]), padInSBB(pad, sbb, bits+[0]))

def padInSbbDeg(pad, sbb, deg):
    """
    Constraint for pad with a given rotation to be in a bounding box.
    """
    padCenter = rotate(BoundingBox(pad.rectInMod).center, radians(deg))
    padX = pad.mod.varX + getX(padCenter)
    padY = pad.mod.varY + getY(padCenter)
    return z3.And(sbb.xmin <= padX, padX <= sbb.xmax,
                  sbb.ymin <= padY, padY <= sbb.ymax)

# toFloat: converts the representation of Z3 Real as a rational number to a floating point number
# http://stackoverflow.com/questions/12598408/z3-python-getting-python-values-from-model
def toFloat(r):
    if z3.is_rational_value(r):
        num = r.numerator_as_long()
        den = r.denominator_as_long()
        return float(num)/float(den)
    else:
        raise Exception('toFloat: accepts rational value')

if __name__ == '__main__':
    main()
