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

class Border:
    def __init__(self, width, height):
        self.width = width
        self.height = height

        self.bbox = BoundingBox(formRect(self.width, self.height))

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

        # Compute coordinates of module
        mod.rect = formRect(mod.width, mod.height)
        mod.rect = transform(mod.rect, mod.theta, mod.mirror, mod.pos)
        mod.bbox = BoundingBox(mod.rect)

        mod.pads = [Pad.fromDict(p, mod) for p in m['pads']]

        return mod

class Pad:
    def __init__(self):
        pass

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
        pad = Pad()

        pad.pos = xy2p(p['x'], p['y'])
        
        pad.through = p['through']
        pad.width = p['width']
        pad.height = p['height']
        pad.netname = p['netname']
        pad.padname = p['padname']

        # Compute pad coordinates
        pad.rect = formRect(pad.width, pad.height)
        pad.rect = pad.rect + pad.pos
        pad.rect = transform(pad.rect, mod.theta, mod.mirror, mod.pos)
        pad.bbox = BoundingBox(pad.rect)

        return pad

def buildNetDict(mods):
    # find closest neighbor for each pad
    netDict = {}
    for mod in mods:
        for pad in mod.pads:
            if pad.netname is None:
                continue
            if pad.netname not in netDict:
                netDict[pad.netname] = []
            netDict[pad.netname].append(pad)

    return netDict