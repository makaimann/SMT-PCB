#!/usr/bin/env python2

# Steven Herbst
# sherbst@stanford.edu
#
# CS448H Winter 2017

# Code to expand generate a Digikey BOM

import argparse
import json
import collections
import requests
import re
from bs4 import BeautifulSoup

def main():
    # load command-line arguments
    parser = argparse.ArgumentParser()
    parser.add_argument('--json')
    parser.add_argument('--bom')
    args = parser.parse_args()

    # read board placement from SMT-PCB
    with open(args.json, 'r') as f:
        json_dict = json.load(f)

    # get module_dict from JSON file
    module_dict = json_dict['module_dict']

    # count up the total number needed of each part
    def def_dict_gen():
        return {'qty': 0, 'refset': set()}
    mpn_dict = collections.defaultdict(def_dict_gen)
    for name, module in module_dict.items():
        partnos = module['partno']
        if not partnos:
            continue
        if not isinstance(partnos[0], list):
            partnos = [partnos]
        for partno in partnos:
            partno = tuple(partno)
            mpn_dict[partno]['qty'] = mpn_dict[partno]['qty'] + 1
            mpn_dict[partno]['refset'].add(name)

    with open(args.bom, 'w') as f:
        header = ',Qty,Part Number,Reference,Description'
        f.write(header + '\n')
        for partno, val in mpn_dict.items():
            qty_str = str(val['qty'])
            mpn_str = partno[0]
            ref_str = '"' + ','.join(val['refset']) + '"'
            des_str = partno[1]
            row =   ',' + qty_str \
                  + ',' + mpn_str \
                  + ',' + ref_str \
                  + ',' + des_str 
            f.write(row + '\n')

if __name__ == '__main__':
    main()
