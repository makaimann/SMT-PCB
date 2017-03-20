#!/usr/bin/env python2

# Steven Herbst
# sherbst@stanford.edu
#
# CS448H Winter 2017

# Code to expand generate a Digikey BOM

import argparse
import json
import collections


def main():
    # load command-line arguments
    parser = argparse.ArgumentParser()
    parser.add_argument('--json')
    parser.add_argument('--bom')
    parser.add_argument('--qty', type=int, default=1)
    args = parser.parse_args()

    # read board placement from SMT-PCB
    with open(args.json, 'r') as f:
        json_dict = json.load(f)

    # add quantity information
    json_dict['quantity'] = args.qty

    # write back updated JSON file
    with open(args.json, 'w') as f:
        json.dump(json_dict, f, indent=2, sort_keys=True)

    # count up the total number needed of each part
    module_dict = json_dict['module_dict']
    bom_dict = collections.defaultdict(lambda: 0)
    for name, module in module_dict.items():
        partnos = module['partno']
        for partno in prep(partnos):
            bom_dict[partno] = bom_dict[partno] + args.qty

    with open(args.bom, 'w') as f:
        for partno, count in bom_dict.items():
            f.write(partno + ', ' + str(count) + '\n')

def prep(val):
    # convert single value to length-1 list
    # then remove all None values
    if not isinstance(val, list):
        val = [val]
    return [x for x in val if x is not None]


if __name__ == '__main__':
    main()
