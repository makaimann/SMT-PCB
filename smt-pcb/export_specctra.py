#!/usr/bin/env python2

import subprocess
import argparse
import os
import os.path
import time
import json
import re
from collections import defaultdict

from pcbparser import LispPrinter, PcbParser
from board_tools import BoardTools
from kicad.point import Point

def main():
    # load command-line arguments
    parser = argparse.ArgumentParser()
    parser.add_argument('--pcb')
    parser.add_argument('--json')
    parser.add_argument('--dsn')
    args = parser.parse_args()

    # read board placement from SMT-PCB
    print "Reading JSON dictionary."
    with open(args.json, 'r') as f:
        json_dict = json.load(f)
    edge = json_dict['board_edge']
    design = json_dict['design_dict']

    # read PCB file
    tree = PcbParser.read_pcb_file(args.pcb)
    mod_list = PcbParser.get_mod_list(tree)

    # full file name to dsn
    dsn_fname = os.path.expanduser(args.dsn)
    dsn_fname = os.path.abspath(dsn_fname)

    dsn = ['pcb', '"'+dsn_fname+'"']
    dsn = dsn + header()
    dsn.append(structure(edge))
    dsn.append(placement(mod_list))
    dsn.append(library(tree))
    dsn.append(network(design))
    dsn.append(wiring())

    # write to DSN
    with open(dsn_fname, 'w') as f:
        f.write(LispPrinter.format(dsn))

def header():
    # Define header information that is common for all designs
    host_version = 'no-vcs-found-c20cf4a~58~ubuntu16.04.1'
    header = [
                ['parser',
                    ['string_quote', '"'],
                    ['space_in_quoted_tokens', 'on'],
                    ['host_cad', '"KiCad\'s Pcbnew"'],
                    ['host_version', '"'+host_version+'"'],
                ],
                ['resolution', 'um', '10'],
                ['unit', 'um']
            ]
    return header

def structure(edge):
    structure = ['structure']
    structure = structure + layer_info()
    structure.append(boundary(edge))
    structure.append(via_info())
    structure.append(rules())

    return structure

def layer_info():
    info = []
    layers = {0: 'F.Cu', 1: 'B.Cu'}
    for layer_id in sorted(layers.keys()):
        layer = ['layer', layers[layer_id],
                    ['type', 'signal'],
                    ['property', 
                            'index', '%d' % layer_id
                    ]
                ]
        info.append(layer)

    return info
    
def boundary(edge):
    ul = Point(*BoardTools.get_board_ul(edge))
    edge = [ul+Point(x,y) for x,y in edge]
    # repeat the last point
    edge = edge + [edge[-1]]
    
    # add points to the edge
    path = ['path', 'pcb', '0']
    for point in edge:
        # convert points from mm to um
        # and negate y coordinate
        x = '%d' %  (point.x*1000)
        y = '%d' % (-point.y*1000)
        path = path[:] + [x, y]

    return ['boundary', path]

def via_info():
    return ['via', '"Via[0-1]_800:400_um"']

def rules():
    return ['rule', 
                ['width', '250'],
                ['clearance', '200.1'],
                ['clearance', '200.1', ['type', 'default_smd']],
                ['clearance', '50', ['type', 'smd_smd']]
            ]

def placement(mod_list):
    info = ['placement']

    # create dictionary of components
    comp_dict = defaultdict(lambda: [])
    for mod in mod_list:
        # interpret information from this module's entry
        pn = mod['name']
        refdes = mod['refdes']
        x = '%d' % ( mod['x']*1000)
        y = '%d' % (-mod['y']*1000)
        rot = '%d' % (mod['rot'])

        if mod['layer'] == 'F.Cu':
            side = 'front'
        elif mod['layer'] == 'B.Cu':
            side = 'back'
        else:
            raise Exception('Invalid component placement')

        place = ['place', refdes, x, y, side, rot, ['PN', pn]]
        comp_dict[mod['name']].append(place)

    # format placement
    for comp, comp_mods in comp_dict.items():
        info.append(['component', comp] + comp_mods)

    return info

def library(tree):
    info = ['library']

    # make a library entry for each unique type of component
    comp_set = set()
    pad_set = set()
    for entry in tree:
        if entry[0] == 'module':
            name = entry[1]
            if name not in comp_set:
                comp_set.add(name)
                comp, pads = make_comp(entry)
                info.append(comp)
                pad_set = pad_set.union(pads)
    
    # add default via to set of pads
    pad_set.add('"Via[0-1]_800:400_um"')

    # make a library entry for each unique type of pad
    for pad_name in pad_set:
        pad = make_pad(pad_name)
        info = info + [pad]

    return info

def network(design):
    network = ['network']

    # create dictionary mapping nets to lists of pins
    net_dict = defaultdict(lambda: [])
    for mod, mod_dict in design.items():
        for pad, net_name in mod_dict.items():
            full_name = mod + '-' + pad
            net_dict[net_name].append(full_name)

    # add each net to the network
    for net, pin_list in net_dict.items():
        pins = ['pins'] + pin_list
        entry = ['net', net, pins]
        network.append(entry)

    # add default routing rules
    rclass = ['kicad_default', '""'] + net_dict.keys()
    rclass.append(['circuit', ['use_via', 'Via[0-1]_800:400_um']])
    rclass.append(['rule', ['width', '250'], ['clearance', '200.1']])
    
    network.append(rclass)

    return network

def wiring():
    return ['wiring']

def make_comp(entry):
    comp = ['image', entry[1]]
    outline = []
    pins = []
    pad_set = set()
    for val in entry[2:]:
        if val[0] == 'fp_line':
            for arg in val:
                if arg[0] == 'start':
                    startx = '%d' % (int(1000*float(arg[1])))
                    starty = '%d' % (int(-1000*float(arg[2])))
                elif arg[0] == 'end':
                    endx = '%d' % (int(1000*float(arg[1])))
                    endy = '%d' % (int(-1000*float(arg[2])))
                elif arg[0] == 'width':
                    width = '%d' % (int(1000*float(arg[1])))
            line = ['outline', ['path', 'signal', width, startx, starty, endx, endy]]
            outline = outline + [line]
        elif val[0] == 'pad':
            pad_name = val[1]
            pad_type = val[3]
            for arg in val:
                if arg[0] == 'size':
                    pad_size = int(1000*float(arg[1]))
                if arg[0] == 'at':
                    x = '%d' % (int(1000*float(arg[1])))
                    y = '%d' % (int(-1000*float(arg[2])))
            fr_pad_name = make_pad_name(pad_type, pad_size)
            pad_set.add(fr_pad_name)
            pad = ['pin', fr_pad_name, pad_name, x, y]
            pins.append(pad)
    
    comp = comp + outline + pins
    return comp, pad_set

def make_pad_name(pad_type, pad_size):
    if pad_type == 'oval':
        return 'Oval[A]Pad_%dx%d_um' % (pad_size, pad_size)
    elif pad_type == 'circle':
        return 'Round[A]Pad_%d_um' % (pad_size)
    else:
        raise Exception('Unsupported pad type.')

def make_pad(name):
    types = '(Round\[A\]Pad|Oval\[A\]Pad|\"Via\[0-1\])'
    size = '([0-9]+)[_x:]'
    p = re.compile(types + '_' + size)
    m = p.match(name)
    if not m:
        raise Exception('Invalid pad name.')
    else:
        size_str = m.group(2)
        pad = ['padstack', name]
        if m.group(1).startswith('Round') or m.group(1).startswith('\"Via'):
            pad.append(['shape', ['circle', 'F.Cu', size_str]])
            pad.append(['shape', ['circle', 'B.Cu', size_str]])
        elif m.group(1).startswith('Oval'):
            pad.append(['shape', ['path', 'F.Cu', size_str, '0', '0', '0', '0']])
            pad.append(['shape', ['path', 'B.Cu', size_str, '0', '0', '0', '0']])
        else:
            raise Exception('Invalid pad type.')
        pad.append(['attach', 'off'])
        return pad

if __name__ == '__main__':
    main()
