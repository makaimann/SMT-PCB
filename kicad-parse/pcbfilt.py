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
    design.modules = [mod for mod in design.modules if not design.border.disjointFromMod(mod)]        

    # remove all pads that have no connections (if they are surface mount)
    for mod in design.modules:
        mod.pads = [pad for pad in mod.pads if pad.through or pad.netname is not None]

    # mark all component that overlap the border as fixed
    for mod in design.modules:
        if design.border.partiallyOverlapsMod(mod):
            mod.fixed = True

    # combine overlapping pads with same name and pad type
    for mod in design.modules:
        combinePads(mod)

    # make names unique integers
    uniquify(design)

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
    numPads = len(padList)

    # create the adjacency matrix
    adj = [[False for j in range(numPads)] for i in range(numPads)]
    for i in range(numPads):
        adj[i][i] = True
        for j in range(i, numPads):
            isAdj = not padList[i].disjointFromPad(padList[j])
            adj[i][j] = isAdj
            adj[j][i] = isAdj

    # create connected subgroups
    padGroups = []
    visited = [False for i in range(numPads)]
    for i in range(numPads):
        # mark pad as visited
        if visited[i]:
            continue
        visited[i] = True

        # create new pad group
        padGroup = [i]
        padGroups.append(padGroup)
        
        # create list of immediately adjacent pads
        toVisit = [j for j in range(numPads) if adj[i][j] and not visited[j]]

        # walk through graph of adjacent pads
        while toVisit:
            # all of the pads to visit are adjacent, so add them to the pad group
            padGroup.extend(toVisit)

            # mark all of these pads as visited
            for k in toVisit:
                visited[k] = True

            # generate the next set of pads to visit
            nextVisit = []
            for k in toVisit:
                nextVisit.extend([j for j in range(numPads) if adj[k][j] and not visited[j]])

            # update toVisit
            toVisit[:] = nextVisit

    newPads = []
    for group in padGroups:
        bbox = BoundingBox()
        for padIndex in group:
            bbox.add(padList[padIndex].rectInMod)

        # use first pad in the group as a starting point
        newPad = padList[group[0]]
        newPad.pos = bbox.ll
        newPad.width = bbox.width
        newPad.height = bbox.height

        newPads.append(newPad)

    return newPads

def uniquify(design):
    # nets is a dictionary that maps an old net name
    # to a new net name
    nets = {}
    for i, mod in enumerate(design.modules):
        # make module reference unique
        mod.reference = 'U'+str(i)
        for j, pad in enumerate(mod.pads):
            # make pad name unique
            pad.padname = 'P'+str(j)

            # make net name unique
            if pad.netname is None:
                continue
            if pad.netname not in nets:
                nets[pad.netname] = 'N'+str(len(nets))
            pad.netname = nets[pad.netname]

if __name__ == '__main__':
    main()
