#!/usr/bin/env python2

import subprocess
import argparse
import os
import os.path
import time

from pcbparser import LispPrinter

def main():
    # load command-line arguments
    parser = argparse.ArgumentParser()
    parser.add_argument('--pcb')
    parser.add_argument('--dsn')
    args = parser.parse_args()

    # full file name to dsn
    dsn_fname = os.path.expanduser(args.dsn)
    dsn_fname = os.path.abspath(dsn_fname)

    dsn = ['pcb', '"'+dsn_fname+'"']
    dsn.append(header_info())

    # write to DSN
    with open(dsn_fname, 'w') as f:
        f.write(LispPrinter.format(dsn))

def header_info():
    # Define header information that is common for all designs
    host_version = 'no-vcs-found-c20cf4a~58~ubuntu16.04.1'
    info = [
                ['parser',
                    ['string_quote', '"'],
                    ['space_in_quoted_tokens', 'on'],
                    ['host_cad', '"KiCad\'s Pcbnew"'],
                    ['host_version', '"'+host_version+'"'],
                ],
                ['resolution', 'um', '10'],
                ['unit', 'um']
            ]

    # define board layers
    structure = ['structure']
    layers = {'F.Cu': 0, 'B.Cu': 1}
    for layer_name, layer_id in layers.items():
        layer = ['layer', layer_name,
                    ['type', 'signal'],
                    ['property', 
                            'index', str(layer_id)
                    ]
                ]

    info.append(structure)
    return structure

if __name__ == '__main__':
    main()
