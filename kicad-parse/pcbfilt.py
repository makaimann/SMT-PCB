#!/usr/bin/env python3

# Steven Herbst
# sherbst@stanford.edu

# Produce a clean problem definition

import json
import argparse

from pcbgeom import *
from pcblib import *

def main():
    # Parse command-line arguments
    parser = argparse.ArgumentParser(description='Clean up PCB design.')
    parser.add_argument('infile')
    args = parser.parse_args()

    # Parse file
    with open(args.infile, 'r') as f:
        design = Design.fromDict(json.load(f))

    # remove all components that have no pads
    design.modules = [mod for mod in design.modules if mod.pads]

    # remove all components that are entirely off the border
    design.modules = [mod for mod in design.modules if not design.border.bbox.disjoint(mod.bbox)]        

    # remove all pads that have no connections (if they are surface mount)
    for mod in design.modules:
        mod.pads = [pad for pad in mod.pads if pad.through or pad.netname is not None]

    # mark all component that overlap the border as fixed
    for mod in design.modules:
        if mod.bbox.overlap(design.border.bbox):
            mod.fixed = True

    # combine overlapping pads with same name and pad type
    for mod in design.modules:
        combinePads(mod)

    # make names unique integers
    #uniquify(design)

    # Convert to design
    with open(args.infile, 'w') as f:
        json.dump(design.toDict(), f, indent=2, sort_keys=True)

def combinePads(mod):
    padDict = {}

    # separate pads by netname
    for pad in mod.pads:
        key = (pad.padname, pad.through)
        if key not in padDict:
            padDict[key] = []
        padDict[key].append(pad)

    # attempt to combine pads on the same net
    newPadList = []
    for padList in padDict.values():
        if len(padList) > 1:
            newPadList += combinePad(padList, mod)
        else:
            newPadList += padList

    mod.pads = newPadList

def combinePad(padList, mod):
    padGroups = []
    for pad in padList:
        done = False
        for group in padGroups:
            for other in group:
                if not pad.bbox.disjoint(other.bbox):
                    group.append(pad)
                    done = True
                    break
            if done:
                break
        if not done:
            padGroups.append([pad])

    newPads = []
    for group in padGroups:
        bbox = BoundingBox()
        for pad in group:
            bbox.add(formRect(pad.width, pad.height)+pad.pos)
        newPad = Pad()
        newPad.pos = bbox.ll
        newPad.through = group[0].through
        newPad.width = bbox.width
        newPad.height = bbox.height
        newPad.netname = group[0].netname
        newPad.padname = group[0].padname

        newPad.rect = formRect(newPad.width, newPad.height)
        newPad.rect = newPad.rect + newPad.pos
        newPad.rect = transform(newPad.rect, mod.theta, mod.mirror, mod.pos)
        newPad.bbox = BoundingBox(newPad.rect)

        newPads.append(newPad)

    return newPads

def uniquify(design):
    nets = {}
    for i, mod in enumerate(design.modules):
        # make module reference unique
        mod.reference = str(i)
        for j, pad in enumerate(mod.pads):
            # make pad name unique
            pad.padname = str(j)

            # make net name unique
            if pad.netname is None:
                continue
            if pad.netname not in nets:
                nets[pad.netname] = len(nets)
            pad.netname = str(nets[pad.netname])

if __name__ == '__main__':
    main()
