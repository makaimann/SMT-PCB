#!/usr/bin/env python2

# Steven Herbst
# sherbst@stanford.edu
#
# CS448H Winter 2017

# Code to print a summary of the design

import argparse
import json
from board_tools import BoardTools


def main():
    # load command-line arguments
    parser = argparse.ArgumentParser()
    parser.add_argument('--json')
    parser.add_argument('--units', default='inch')
    args = parser.parse_args()

    # read board placement from SMT-PCB
    with open(args.json, 'r') as f:
        json_dict = json.load(f)

    board_edge = json_dict['board_edge'] 

    width, height = BoardTools.get_board_dims(board_edge)

    # define unit conversion
    if args.units.lower() in ['in', 'inch', 'inches']:
        conv = lambda x: 0.0393701*x
        area_str = 'in^2'
    if args.units.lower() in ['mm', 'mms', 'millimeters']:
        conv = lambda x: x
        area_str = 'mm^2'
    if args.units.lower() in ['mil', 'mils']:
        conv = lambda x: 39.3701*x
        area_str = 'mil^2'

    area = conv(width) * conv(height)
    
    # print summary
    print '############'
    print 'Summary'
    print 'Board area: %0.3f %s' %(area, area_str)
    print '############'

if __name__ == '__main__':
    main()
