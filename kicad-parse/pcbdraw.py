#!/usr/bin/env python3

# Steven Herbst
# sherbst@stanford.edu

# Library enables user to draw a PCB file from JSON

import json
import argparse
import sys

import numpy as np
import matplotlib.pyplot as plt
import matplotlib
from matplotlib.patches import Polygon

from pcbgeom import *
from pcblib import *

def drawMod(ax, rect, color, alpha):
    ax.add_patch(Polygon(rect.T, closed=True, facecolor='none', edgecolor=color, alpha=alpha))

def drawPad(ax, pad, color, alpha):
    ax.add_patch(Polygon(pad.T, closed=True, facecolor=color, edgecolor='black', alpha=alpha))

def main():
    # Parse command-line arguments
    parser = argparse.ArgumentParser(description='Draw PCB design.')
    parser.add_argument('infile')
    parser.add_argument('--top', action='store_true')
    parser.add_argument('--bottom', action='store_true')
    parser.add_argument('--alpha', type=float, default=0.75)
    args = parser.parse_args()

    # If neither top nor bottom is specified, draw both
    if not args.top and not args.bottom:
        args.top = True
        args.bottom = True

    # Parse file
    with open(args.infile, 'r') as f:
        json_dict = json.load(f)

    fig, ax = plt.subplots()

    # Determine module outlines and pad locations
    padsByNet = {}
    for m in json_dict['modules']:

        mod = Module.fromDict(m)
    
        # Draw rectangle
        color = 'blue' if mirror else 'red'
        if (not mod.mirror and args.top) or (mod.mirror and args.bottom):
            drawMod(ax, mod.rect, color, args.alpha)

        # Draw pads
        for pad in mod.pads:

            color = 'blue' if mirror else 'red'
            if through or (not mod.mirror and args.top) or (mod.mirror and args.bottom):
                drawPad(ax, pad.rect, color, args.alpha)

            if pad.netname is None:
                continue

            # Add to list of pads, noting the side
            if pad.netname not in padsByNet:
                padsByNet[netname] = []

            # Update distances
            for other in padsByNet[netname]:
                dist = distPoints(pad.bbox.center, other.bbox.center)
                if dist < pad.minDist:
                    pad.minDist = dist
                    pad.minPad = other
                if dist < other.minDist:
                    other.minDist = dist
                    other.minPad = pad

    # Draw board edge
    border = json_dict['border']
    edge = formRect(border['width'], border['height'])
    ax.add_patch(Polygon(edge.T, closed=True, facecolor='none', edgecolor='green', alpha=args.alpha, lw=3))

    # Draw wires
    for padlist in padsByNet:
        for pad in padlist:
            if not pad.visited and pad.minPad is not None:
                pad.visited = True
                pad.minPad.visited = True

                c1 = pad.bbox.center
                c2 = pad.minPad.center
                ax.plot([getX(c1), getX(c2)], [getY(c1), getY(c2)], color='k', linestyle='-', linewidth=0.25)

    ax.autoscale(True)
    ax.set_aspect('equal')

    plt.show()                

if __name__ == '__main__':
    main()
