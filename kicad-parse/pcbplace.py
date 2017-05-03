#!/usr/bin/env python3

# Steven Herbst
# sherbst@stanford.edu

# Place PCB using z3

import json
import argparse
import sys

import z3
import itertools

from math import radians

from pcbgeom import *
from pcblib import *

def main():
    # Parse command-line arguments
    parser = argparse.ArgumentParser(description='Place PCB design.')
    parser.add_argument('infile')
    args = parser.parse_args()

    # Parse file
    with open(args.infile, 'r') as f:
        design = Design.fromDict(json.load(f))

    s = z3.Solver()

    # make design variables
    for mod in design.modules:
        mod.varX = z3.Real(mod.reference + '.x')
        mod.varY = z3.Real(mod.reference + '.y')
        mod.varRot90 = z3.Bool(mod.reference + '.rot90')
        mod.varRot180 = z3.Bool(mod.reference + '.rot180')
        mod.varMirror = z3.Bool(mod.reference + '.mirror')

    # on board
    for mod in design.modules:
        s.add(onBoard(mod, design.border))

    # non-overlap
    for mod1, mod2 in itertools.combinations(design.modules, 2):
        s.add(noOverlap(mod1, mod2))

    print('***', s.check(), '***')
    model = s.model()

    # make design variables
    for mod in design.modules:
        mod.pos = xy2p(toFloat(model[mod.varX]), toFloat(model[mod.varY]))

        mod.theta = 0
        if z3.is_true(model[mod.varRot90]):
            mod.theta += 90.0
        if z3.is_true(model[mod.varRot180]):
            mod.theta += 180.0
        mod.theta = radians(mod.theta)

    # Convert to design
    with open(args.infile, 'w') as f:
        json.dump(design.toDict(), f, indent=2, sort_keys=True)

def onBoard(mod, border, bits=[]):
    if len(bits)==2:
        return onBoardDeg(mod, border, 180*bits[1] + 90*bits[0])
    else:
        var = {1: mod.varRot180, 0: mod.varRot90}[len(bits)]
        return z3.If(var, onBoard(mod, border, bits+[1]), onBoard(mod, border, bits+[0]))

def onBoardDeg(mod, border, deg):
    return z3.And(0 <= mod.varX-widthLeft(mod, deg),
                  mod.varX+widthRight(mod, deg) <= border.width,
                  0 <= mod.varY-heightBelow(mod, deg),
                  mod.varY+heightAbove(mod, deg) <= border.height)

def noOverlap(mod1, mod2, bits=[]):
    if len(bits)==4:
        return noOverlapDeg(mod1, mod2, 180*bits[3] + 90*bits[2], 180*bits[1] + 90*bits[0])
    else:
        var = {3: mod1.varRot180, 2: mod1.varRot90, 1: mod2.varRot180, 0: mod2.varRot90}[len(bits)]
        return z3.If(var, noOverlap(mod1, mod2, bits+[1]), noOverlap(mod1, mod2, bits+[0]))

def noOverlapDeg(mod1, mod2, deg1, deg2):
    return z3.Or(mod1.varX+widthRight(mod1, deg1) <= mod2.varX-widthLeft(mod2, deg2),
                 mod2.varX+widthRight(mod2, deg2) <= mod1.varX-widthLeft(mod1, deg1),
                 mod1.varY+heightAbove(mod1, deg1) <= mod2.varY-heightBelow(mod2, deg2),
                 mod2.varY+heightAbove(mod2, deg2) <= mod1.varY-heightBelow(mod1, deg1))

def widthLeft(mod, deg):
    return {0: 0, 90: mod.height, 180: mod.width, 270: 0}[deg]

def widthRight(mod, deg):
    return {0: mod.width, 90: 0, 180: 0, 270: mod.height}[deg]

def heightBelow(mod, deg):
    return {0: 0, 90: 0, 180: mod.height, 270: mod.width}[deg]

def heightAbove(mod, deg):
    return {0: mod.height, 90: mod.width, 180: 0, 270: 0}[deg]

# toFloat:
# see http://stackoverflow.com/questions/12598408/z3-python-getting-python-values-from-model
def toFloat(r):
    if z3.is_rational_value(r):
        num = r.numerator_as_long()
        den = r.denominator_as_long()
        return float(num)/float(den)
    else:
        raise Exception('toFloat: accepts rational value')

if __name__ == '__main__':
    main()
