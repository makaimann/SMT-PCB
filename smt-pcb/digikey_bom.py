#!/usr/bin/env python2

# Steven Herbst
# sherbst@stanford.edu
#
# CS448H Winter 2017

# Code to expand generate a Digikey BOM

import argparse
import json

def main():
    # load command-line arguments
    parser = argparse.ArgumentParser()
    parser.add_argument('--json')
    parser.add_argument('--bom')
    args = parser.parse_args()

    # read board placement from SMT-PCB
    print "Reading output from SMT engine."
    with open(args.json, 'r') as f:
        json_dict = json.load(f)

    bom_dict = {}
    for name, module in json_dict['module_dict'].items():
        partnos = module['partno']
        if not isinstance(partnos, list):
            partnos = [partnos]
        for partno in partnos:
            if partno is None:
                continue
            if partno not in bom_dict:
                bom_dict[partno] = 0
            bom_dict[partno] = bom_dict[partno] + 1

    with open(args.bom, 'w') as f:
        for partno, count in bom_dict.items():
            f.write(partno + ', ' + str(count) + '\n')

if __name__ == '__main__':
    main()
