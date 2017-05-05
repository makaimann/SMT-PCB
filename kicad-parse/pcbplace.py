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
        noOverlap(prob, mod1, mod2, design.border, idx)

    # And together top-level constraints
    print("Forming top-level constraints...")

    # Solve the placement problem
    print('Solving MILP problem...')

    prob.solve();

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
    # define expressions
    constrList = [[] for i in range(4)]
    for itheta in range(4):
        sbbExpr = sbbExprRad(mod, itheta)
        for idx, constr in enumerate(sbbExpr):
            constrList[idx].append(constr)

    # update problem with constraints
    prob += (mod.sbb.xmin == (mod.varX + lpSum(constrList[0])))
    prob += (mod.sbb.xmax == (mod.varX + lpSum(constrList[1])))
    prob += (mod.sbb.ymin == (mod.varY + lpSum(constrList[2])))
    prob += (mod.sbb.ymax == (mod.varY + lpSum(constrList[3])))

def sbbExprRad(mod, itheta):
    rbb = BoundingBox(rotate(mod.rect, i2rad(itheta)))

    return [rbb.xmin*mod.varRot[itheta],
            rbb.xmax*mod.varRot[itheta],
            rbb.ymin*mod.varRot[itheta],
            rbb.ymax*mod.varRot[itheta]]

def onBoard(prob, mod, border):
    """
    Constrain the given module to be on the board
    """
    prob += (0 <= mod.sbb.xmin)
    prob += (mod.sbb.xmax <= border.width)
    prob += (0 <= mod.sbb.ymin)
    prob += (mod.sbb.ymax <= border.height)

def noOverlap(prob, mod1, mod2, border, idx):
    """
    Constrain mod1 and mod2 not to overlap
    """
    ovVars = [LpVariable('OV'+str(idx)+'.'+str(i), cat='Binary') for i in range(4)]

    prob += ((mod1.sbb.xmax - mod2.sbb.xmin) <= (border.width*ovVars[0]))
    prob += ((mod2.sbb.xmax - mod1.sbb.xmin) <= (border.width*ovVars[1]))
    prob += ((mod1.sbb.ymax - mod2.sbb.ymin) <= (border.height*ovVars[2]))
    prob += ((mod2.sbb.ymax - mod1.sbb.ymin) <= (border.height*ovVars[3]))
    
    # one or more of the ovVars must be zero
    prob += (lpSum(ovVars) <= (len(ovVars)-1))

def updateModsFromMILP(design):
    """
    Update module position and rotation based on the output of the SMT solver.
    """
    for mod in design.modules:
        # calculate module position
        x = value(mod.varX)
        y = value(mod.varY)
        print(x,y)
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

def i2rad(itheta):
    return radians(90*itheta)

if __name__ == '__main__':
    main()