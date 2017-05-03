#!/usr/bin/env python3

# Steven Herbst
# sherbst@stanford.edu

# Data structures for PCB

from pcbgeom import *

class Design:
    def __init__(self, modules, border):
        self.modules = modules
        self.border = border

    def toDict(self):
        d = {}

        d['modules'] = [mod.toDict() for mod in self.modules]
        d['border'] = self.border.toDict()

        return d

    @staticmethod
    def fromDict(d):

        modules = [Module.fromDict(m) for m in d['modules']]
        border = Border.fromDict(d['border'])

        return Design(modules, border)

    def buildNetDict(self):
        # find closest neighbor for each pad
        netDict = {}
        for mod in self.modules:
            for pad in mod.pads:
                if pad.netname is None:
                    continue
                if pad.netname not in netDict:
                    netDict[pad.netname] = []
                netDict[pad.netname].append(pad)

        return netDict

class Border:
    def __init__(self, width, height):
        self.width = width
        self.height = height

    @property
    def rect(self):
        return formRect(self.width, self.height)

    def disjointFromMod(self, mod):
        return BoundingBox(self.rect).disjointFrom(BoundingBox(mod.rectInBoard))

    def fullyContainsMod(self, mod):
        return BoundingBox(self.rect).fullyContains(BoundingBox(mod.rectInBoard))

    def partiallyOverlapsMod(self, mod):
        return not self.disjointFromMod(mod) and not self.fullyContainsMod(mod)

    def toDict(self):
        b = {}

        b['width'] = self.width
        b['height'] = self.height

        return b

    @staticmethod
    def fromDict(b):

        width = b['width']
        height = b['height']

        return Border(width, height)

class Module:
    def __init__(self):
        self.fixed = False

    def toDict(self):
        m = {}

        m['x'] = getX(self.pos)
        m['y'] = getY(self.pos)

        m['reference'] = self.reference
        m['theta'] = self.theta
        m['mirror'] = self.mirror
        m['width'] = self.width
        m['height'] = self.height
        m['fixed'] = self.fixed

        m['pads'] = [pad.toDict() for pad in self.pads]

        return m

    @staticmethod
    def fromDict(m):
        mod = Module()

        mod.pos = xy2p(m['x'], m['y'])

        mod.reference = m['reference']
        mod.theta = m['theta']
        mod.mirror = m['mirror']
        mod.width = m['width']
        mod.height = m['height']
        mod.fixed = m['fixed']

        mod.pads = [Pad.fromDict(p, mod) for p in m['pads']]

        return mod

    @property
    def rect(self):
        return formRect(self.width, self.height)

    @property
    def rectInBoard(self):
        return transform(self.rect, self.theta, self.mirror, self.pos)

class Pad:
    def __init__(self, mod):
        self.mod = mod

    def toDict(self):
        p = {}

        p['x'] = getX(self.pos)
        p['y'] = getY(self.pos)

        p['through'] = self.through
        p['width'] = self.width
        p['height'] = self.height
        p['netname'] = self.netname
        p['padname'] = self.padname

        return p

    @staticmethod
    def fromDict(p, mod):
        pad = Pad(mod)

        pad.pos = xy2p(p['x'], p['y'])
        
        pad.through = p['through']
        pad.width = p['width']
        pad.height = p['height']
        pad.netname = p['netname']
        pad.padname = p['padname']

        return pad

    @property
    def rect(self):
        return formRect(self.width, self.height)

    @property
    def rectInMod(self):
         return self.rect + self.pos

    @property
    def rectInBoard(self):
        return transform(self.rectInMod, self.mod.theta, self.mod.mirror, self.mod.pos)

    def disjointFromPad(self, other):
        return BoundingBox(self.rectInMod).disjointFrom(BoundingBox(other.rectInMod))

def buildDistMat(padList):
    N = len(padList)
    mat = [[0.0 for j in range(N)] for i in range(N)]
    for i in range(N):
        for j in range(i+1,N):
            pi = BoundingBox(padList[i].rectInBoard).center
            pj = BoundingBox(padList[j].rectInBoard).center
            mat[i][j] = distPoints(pi, pj)
            mat[j][i] = distPoints(pi, pj)
    return mat