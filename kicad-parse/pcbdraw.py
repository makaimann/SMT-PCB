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

def drawModRect(ax, rect, color, alpha):
    ax.add_patch(Polygon(rect.T, closed=True, facecolor='none', edgecolor=color, alpha=alpha))

def drawPadRect(ax, pad, color, alpha):
    ax.add_patch(Polygon(pad.T, closed=True, facecolor=color, edgecolor='black', alpha=alpha))

def drawEdgeRect(ax, edge, alpha):
    ax.add_patch(Polygon(edge.T, closed=True, facecolor='none', edgecolor='green', alpha=alpha, lw=3))

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
        design = Design.fromDict(json.load(f))

    fig, ax = plt.subplots()

    # Determine module outlines and pad locations
    mods = design.modules

    # Draw modules and pads
    for mod in mods:
        if mod.fixed:
            color = 'purple'
        elif mod.mirror:
            color = 'blue'
        else:
            color = 'red'
        drawMod = (not mod.mirror and args.top) or (mod.mirror and args.bottom)
        if drawMod:
            drawModRect(ax, mod.rectInBoard, color, args.alpha)

        for pad in mod.pads:
            if pad.through or drawMod:
                drawPadRect(ax, pad.rectInBoard, color, args.alpha)

    # Draw board edge
    border = design.border
    edge = formRect(border.width, border.height)
    drawEdgeRect(ax, edge, args.alpha)

    ax.autoscale(True)
    ax.set_aspect('equal')

    plt.show()                

if __name__ == '__main__':
    main()
