#!/usr/bin/env python3

# Steven Herbst
# sherbst@stanford.edu

# Place PCB using z3

import json
import argparse
import sys

import itertools
import random

from math import radians, degrees

from pcbgeom import *
from pcblib import *

from pulp import *

def main():
    # Parse command-line arguments
    parser = argparse.ArgumentParser(description='Place PCB design.')
    parser.add_argument('infile')
    parser.add_argument('--limit', type=float, default=None)
    args = parser.parse_args()

    # List of constraints to be AND'd together
    prob = LpProblem('pcbplace', LpMinimize)

    # feasibility problem
    prob += 0

    # Parse file
    print('Reading design from file...')
    with open(args.infile, 'r') as f:
        design = Design.fromDict(json.load(f))

    # Create design variables
    makeDesignVariables(prob, design)

    # Constrain free components to be on the board
    print('Adding onBoard constraints...')
    for mod in design.modules:
        if not mod.fixed:
            onBoard(prob, mod, design.border)

    # Constrain pairs of components no to overlap 
    print('Adding noOverlap constraints...')
    for idx, (mod1, mod2) in enumerate(itertools.combinations(design.modules, 2)):
        if mod1.fixed and mod2.fixed:
            continue
        noOverlap(prob, mod1, mod2, design.border)

    # Constrain total routing distance
    if args.limit:
        print('Adding semiperimeter constraint...')
        addSemiPerimConstr(prob, design, args.limit)

    # Solve the placement problem
    print('Solving MILP problem...')

    prob.solve(GUROBI());

    updateModsFromMILP(design)

    # Convert to design
    print('Writing design to file...')
    with open(args.infile, 'w') as f:
        json.dump(design.toDict(), f, indent=2, sort_keys=True)

def makeDesignVariables(prob, design):
    """
    Create the SMT solver design variables for all modules in the design.
    """
    for mod in design.modules:
        # X and Y degrees of freedom
        mod.varX = LpVariable(mod.reference + '.x')
        mod.varY = LpVariable(mod.reference + '.y')

        # four possible rotation states, encoded by four binary variables
        # exactly one must be set
        mod.varRot = [LpVariable(mod.reference + '.rot' + str(i), cat='Binary') for i in range(4)]
        prob += (lpSum(mod.varRot) == 1)

        # bounding box used to represent extents of the components
        mod.sbb = SmtBoundingBox(mod.reference)
        initModSbb(prob, mod)

        # if the module is fixed, constrain its position and rotation
        if mod.fixed:
            # Constrain position
            prob += (mod.varX == getX(mod.pos))
            prob += (mod.varY == getY(mod.pos))

            # Round rotation to one of four options
            itheta = round(degrees(mod.theta)/90.0)

            for i in range(4):
                if i == itheta:
                    prob += (mod.varRot[i] == 1)
                else:
                    prob += (mod.varRot[i] == 0)

def initModSbb(prob, mod):
    # update problem with constraints
    prob += (mod.sbb.xmin == (mod.varX + sbbExprRad(mod.rect, mod.varRot, 'xmin')))
    prob += (mod.sbb.xmax == (mod.varX + sbbExprRad(mod.rect, mod.varRot, 'xmax')))  
    prob += (mod.sbb.ymin == (mod.varY + sbbExprRad(mod.rect, mod.varRot, 'ymin')))
    prob += (mod.sbb.ymax == (mod.varY + sbbExprRad(mod.rect, mod.varRot, 'ymax')))

def onBoard(prob, mod, border):
    """
    Constrain the given module to be on the board
    """
    prob += (0 <= mod.sbb.xmin)
    prob += (mod.sbb.xmax <= border.width)
    prob += (0 <= mod.sbb.ymin)
    prob += (mod.sbb.ymax <= border.height)

def noOverlap(prob, mod1, mod2, border):
    """
    Constrain mod1 and mod2 not to overlap
    """
    bvars = [mod1.reference + '_' + mod2.reference + '_' + str(i) for i in range(4)]
    bvars = [LpVariable(name, cat='Binary') for name in bvars]

    prob += ((mod1.sbb.xmax - mod2.sbb.xmin) <= ( border.width*(1-bvars[0])))
    prob += ((mod2.sbb.xmax - mod1.sbb.xmin) <= ( border.width*(1-bvars[1])))
    prob += ((mod1.sbb.ymax - mod2.sbb.ymin) <= (border.height*(1-bvars[2])))
    prob += ((mod2.sbb.ymax - mod1.sbb.ymin) <= (border.height*(1-bvars[3])))

    # one or more of the inequalities must hold
    prob += (lpSum(bvars) >= 1)

def addSemiPerimConstr(prob, design, limit):
    """
    Constrain the sum of net semiperimeters to be less than a target.
    """
    addList = []
    for netname, padList in design.buildNetDict().items():
        sbb = buildSBB(prob, netname, padList)
        addList.append(sbb.width)
        addList.append(sbb.height)
    prob += (lpSum(addList) <= limit)

def buildSBB(prob, netname, padList):
    """
    Builds the logic for a bounding box of pads on a given net.
    """
    sbb = SmtBoundingBox(netname)
    for pad in padList:
        addPadInSBB(prob, pad, sbb)
    return sbb

def addPadInSBB(prob, pad, sbb):
    """
    Constrains the given pad to be in a bounding box.
    """
    
    padCenter = BoundingBox(pad.rectInMod).center

    prob += (sbb.xmin <= (pad.mod.varX + sbbExprRad(padCenter, pad.mod.varRot, 'xmin')))
    prob += (sbb.xmax >= (pad.mod.varX + sbbExprRad(padCenter, pad.mod.varRot, 'xmax')))
    prob += (sbb.ymin <= (pad.mod.varY + sbbExprRad(padCenter, pad.mod.varRot, 'ymin')))
    prob += (sbb.ymax >= (pad.mod.varY + sbbExprRad(padCenter, pad.mod.varRot, 'ymax')))

def updateModsFromMILP(design):
    """
    Update module position and rotation based on the output of the SMT solver.
    """
    for mod in design.modules:
        # calculate module position
        x = value(mod.varX)
        y = value(mod.varY)
        mod.pos = xy2p(x, y)

        # calculate module rotation
        itheta = [value(var) for var in mod.varRot].index(1)
        mod.theta = i2rad(itheta)

class SmtBoundingBox:
    """
    Class used to store bounding box logic for computing net semiperimeters.
    """
    def __init__(self, name):
        self.xmin = LpVariable(name + '.xmin')
        self.xmax = LpVariable(name + '.xmax')
        self.ymin = LpVariable(name + '.ymin')
        self.ymax = LpVariable(name + '.ymax')

    @property
    def width(self):
        return self.xmax - self.xmin

    @property
    def height(self):
        return self.ymax - self.ymin

def sbbExprRad(rect, varRot, attr):
    addList = []
    for itheta in range(4):
        rbb = BoundingBox(rotate(rect, i2rad(itheta)))
        addList.append(getattr(rbb, attr)*varRot[itheta])
    return lpSum(addList)

def i2rad(itheta):
    return radians(90*itheta)

if __name__ == '__main__':
    main()
