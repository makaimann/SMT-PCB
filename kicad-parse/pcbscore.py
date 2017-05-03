#!/usr/bin/env python3

# Steven Herbst
# sherbst@stanford.edu

# Score PCB design based on distances between points

import json
import argparse
import sys

from pcbgeom import *
from pcblib import *

def main():
    # Parse command-line arguments
    parser = argparse.ArgumentParser(description='Score PCB design.')
    parser.add_argument('infile')
    args = parser.parse_args()

    # Parse file
    with open(args.infile, 'r') as f:
        design = Design.fromDict(json.load(f))

    # Determine module outlines and pad locations

    # Sum the semiperimeters
    score = 0
    netDict = design.buildNetDict()
    for padList in netDict.values():
        bbox = BoundingBox()
        for pad in padList:
            bbox.add(pad.rectInBoard)

        score += bbox.width + bbox.height

    print('Score: {:0.3f}'.format(score))

if __name__ == '__main__':
    main()
