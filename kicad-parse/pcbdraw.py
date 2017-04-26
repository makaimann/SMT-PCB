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

    # Determine module outlines and pad locations
    pads = []
    rects = []
    for mod in json_dict['modules']:
        mod_pos = xy2p(mod['x'], mod['y'])
        theta = mod['theta']
        mirror = mod['mirror']

        # add outlines
        rect = formRect(mod['width'], mod['height'])
        rect = transform(rect, theta, mirror, mod_pos)
    
        # Add to list of rectangles, noting the side
        rects.append((rect,mirror))

        # add pads
        for pad in mod['pads']:
            through = pad['through']
            pad_pos = xy2p(pad['x'], pad['y'])
            rect = formRect(pad['width'], pad['height'])
            rect = rect + pad_pos
            rect = transform(rect, theta, mirror, mod_pos)

            # Add to list of pads, noting the side
            pads.append((rect,mirror,through))

    # Determine the corners of the board
    border = json_dict['border']
    edge = formRect(border['width'], border['height'])
 
    fig, ax = plt.subplots()

    for rect, mirror in rects:
        color = 'blue' if mirror else 'red'
        draw = (not mirror and args.top) or (mirror and args.bottom)
        if draw:
            ax.add_patch(Polygon(rect.T, closed=True, facecolor='none', edgecolor=color, alpha=args.alpha))

    for pad, mirror, through in pads:
        color = 'blue' if mirror else 'red'
        draw = through or (not mirror and args.top) or (mirror and args.bottom)
        if draw:
            ax.add_patch(Polygon(pad.T, closed=True, facecolor=color, edgecolor='black', alpha=args.alpha))

    # draw the edge
    ax.add_patch(Polygon(edge.T, closed=True, facecolor='none', edgecolor='green', alpha=args.alpha, lw=3))

    ax.autoscale(True)
    ax.set_aspect('equal')

    plt.show()                

if __name__ == '__main__':
    main()
