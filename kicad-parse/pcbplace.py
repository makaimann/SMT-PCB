#!/usr/bin/env python3

# Steven Herbst
# sherbst@stanford.edu

# Place PCB using z3

import json
import argparse
import sys

import itertools

from math import radians, degrees

from pcbgeom import *
from pcblib import *

from pysmt.shortcuts import Symbol, And, Or, Plus, Minus, Equals, get_model 
from pysmt.shortcuts import Real, Bool, LE, Not, Ite, Solver
from pysmt.typing import REAL

def main():
    # Parse command-line arguments
    parser = argparse.ArgumentParser(description='Place PCB design.')
    parser.add_argument('infile')
    parser.add_argument('--limit', type=float, default=None)
    parser.add_argument('--solver', type=str, default='z3')
    args = parser.parse_args()

    # List of constraints to be AND'd together
    allConstr = []

    # Parse file
    print('Reading design from file...')
    with open(args.infile, 'r') as f:
        design = Design.fromDict(json.load(f))

    # Create design variables
    makeDesignVariables(allConstr, design)

    # Constrain free components to be on the board
    print('Adding onBoard constraints...')
    for mod in design.modules:
        if not mod.fixed:
            allConstr.append(onBoard(mod, design.border))

    # Constrain pairs of components no to overlap 
    print('Adding noOverlap constraints...')
    noOverlapConstr = []
    for mod1, mod2 in itertools.combinations(design.modules, 2):
        if mod1.fixed and mod2.fixed:
            continue
        allConstr.append(noOverlap(mod1, mod2))

    # If desired, constrain the sum of net semiperimeters
    if args.limit is not None:
        print('Adding semiPerim constraint...')
        addSemiPerimConstr(allConstr, design, args.limit)

    # And together top-level constraints
    print("Forming top-level constraints...")
    formula = And(allConstr)

    # Solve the placement problem
    print('Solving SMT problem...')

    with Solver(name=args.solver) as solver:
        solver.add_assertion(formula)
        if solver.solve():
            print('Problem is SAT.')
            print('Updating modules...')
            updateModsFromSMT(design, solver)
        else:
            print('No solution found.')

    # Convert to design
    print('Writing design to file...')
    with open(args.infile, 'w') as f:
        json.dump(design.toDict(), f, indent=2, sort_keys=True)

def makeDesignVariables(allConstr, design):
    """
    Create the SMT solver design variables for all modules in the design.
    """
    for mod in design.modules:
        mod.varX = Symbol(mod.reference + '.x', REAL)
        mod.varY = Symbol(mod.reference + '.y', REAL)
        mod.varRot90 = Symbol(mod.reference + '.rot90')
        mod.varRot180 = Symbol(mod.reference + '.rot180')

        # if the module is fixed, constrain its position and rotation
        if mod.fixed:
            # Constrain position
            allConstr.append(Equals(mod.varX, Real(getX(mod.pos))))
            allConstr.append(Equals(mod.varY, Real(getY(mod.pos))))

            # Round rotation to one of four options
            itheta = round(degrees(mod.theta)/90.0)

            # Constrain rot90
            rot90 = bool((itheta >> 0) % 2)
            if rot90:
                allConstr.append(mod.varRot90)
            else:
                allConstr.append(Not(mod.varRot90))

            # Constrain rot180
            rot180 = bool((itheta >> 1) % 2)    
            if rot180:
                allConstr.append(mod.varRot180)
            else:
                allConstr.append(Not(mod.varRot180))

def addSemiPerimConstr(allConstr, design, limit):
    """
    Constrain the sum of net semiperimeters to be less than a target.
    """
    sbbList = []
    for netname, padList in design.buildNetDict().items():
        sbb = buildSBB(allConstr, netname, padList)
        sbbList.append(Plus(sbb.width, sbb.height))
    allConstr.append(LE(Plus(sbbList), Real(limit)))

def updateModsFromSMT(design, solver):
    """
    Update module position and rotation based on the output of the SMT solver.
    """
    for mod in design.modules:
        # calculate module position
        x = float(solver.get_value(mod.varX).constant_value())
        y = float(solver.get_value(mod.varY).constant_value())
        mod.pos = xy2p(x, y)

        # calculate module rotation
        rot90  = solver.get_value(mod.varRot90).constant_value()
        rot180 = solver.get_value(mod.varRot180).constant_value()

        mod.theta = 0
        if rot90:
            mod.theta += 90.0
        if rot180:
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
        return Ite(var, onBoard(mod, border, bits+[1]), onBoard(mod, border, bits+[0]))

def onBoardDeg(mod, border, deg):
    """
    Conditions for mod to be on the board when it has rotation deg.
    """
    rbb = rotBoundingBox(mod, deg)
    return And(LE(Real(0), Plus(mod.varX, Real(rbb.xmin))), 
               LE(Plus(mod.varX, Real(rbb.xmax)), Real(border.width)),
               LE(Real(0), Plus(mod.varY, Real(rbb.ymin))),
               LE(Plus(mod.varY, Real(rbb.ymax)), Real(border.height)))

def noOverlap(mod1, mod2, bits=[]):
    """
    Constrain mod1 and mod2 not to overlap
    """
    if len(bits)==4:
        return noOverlapDeg(mod1, mod2, 180*bits[3] + 90*bits[2], 180*bits[1] + 90*bits[0])
    else:
        var = {3: mod1.varRot180, 2: mod1.varRot90, 1: mod2.varRot180, 0: mod2.varRot90}[len(bits)]
        return Ite(var, noOverlap(mod1, mod2, bits+[1]), noOverlap(mod1, mod2, bits+[0]))

def noOverlapDeg(mod1, mod2, deg1, deg2):
    """
    Conditions for mod1 and mod2 not to overlap when mod1 has rotation deg1
    and mod2 has rotation deg2.
    """
    rbb1 = rotBoundingBox(mod1, deg1)
    rbb2 = rotBoundingBox(mod2, deg2)
    return Or(LE(Plus(mod1.varX, Real(rbb1.xmax)), Plus(mod2.varX, Real(rbb2.xmin))),
              LE(Plus(mod2.varX, Real(rbb2.xmax)), Plus(mod1.varX, Real(rbb1.xmin))),
              LE(Plus(mod1.varY, Real(rbb1.ymax)), Plus(mod2.varY, Real(rbb2.ymin))),
              LE(Plus(mod2.varY, Real(rbb2.ymax)), Plus(mod1.varY, Real(rbb1.ymin))))

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
        self.xmin = Symbol(netname + '.xmin', REAL)
        self.xmax = Symbol(netname + '.xmax', REAL)
        self.ymin = Symbol(netname + '.ymin', REAL)
        self.ymax = Symbol(netname + '.ymax', REAL)

    @property
    def width(self):
        return Minus(self.xmax, self.xmin)

    @property
    def height(self):
        return Minus(self.ymax, self.ymin)

def buildSBB(allConstr, netname, padList):
    """
    Builds the logic for a bounding box of pads on a given net.
    """
    sbb = SmtBoundingBox(netname)
    for pad in padList:
        allConstr.append(padInSBB(pad, sbb))
    return sbb

def padInSBB(pad, sbb, bits=[]):
    """
    Constrains the given pad to be in a bounding box.
    """
    if len(bits)==2:
        return padInSbbDeg(pad, sbb, 180*bits[1] + 90*bits[0])
    else:
        var = {1: pad.mod.varRot180, 0: pad.mod.varRot90}[len(bits)]
        return Ite(var, padInSBB(pad, sbb, bits+[1]), padInSBB(pad, sbb, bits+[0]))

def padInSbbDeg(pad, sbb, deg):
    """
    Constraint for pad with a given rotation to be in a bounding box.
    """
    padCenter = rotate(BoundingBox(pad.rectInMod).center, radians(deg))
    padX = Plus(pad.mod.varX, Real(getX(padCenter)))
    padY = Plus(pad.mod.varY, Real(getY(padCenter)))
    return And(LE(sbb.xmin, padX),
               LE(padX, sbb.xmax),
               LE(sbb.ymin, padY),
               LE(padY, sbb.ymax))

if __name__ == '__main__':
    main()
