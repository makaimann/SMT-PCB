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
        x = '%d' % dsnx(point.x)
        y = '%d' % dsny(point.y)
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
        x = '%d' % dsnx(mod['x'])
        y = '%d' % dsny(mod['y'])
        rot = '%d' % (mod['rot'])

        if mod['layer'] == 'F.Cu':
            side = 'front'
        elif mod['layer'] == 'B.Cu':
            side = 'back'
        else:
            raise Exception('Invalid component placement')

        place = ['place', refdes, x, y, side, rot, ['PN', dsns(pn)]]
        comp_dict[mod['name']].append(place)

    # format placement
    for comp, comp_mods in comp_dict.items():
        info.append(['component', dsns(comp)] + comp_mods)

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
    pad_set.add('Via[0-1]_800:400_um')

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
        entry = ['net', dsns(net), pins]
        network.append(entry)

    # add default routing rules
    all_nets = [dsns(x) for x in net_dict.keys()]
    rclass = ['kicad_default', '""'] + all_nets
    rclass.append(['circuit', ['use_via', 'Via[0-1]_800:400_um']])
    rclass.append(['rule', ['width', '250'], ['clearance', '200.1']])
    
    network.append(rclass)

    return network

def wiring():
    return ['wiring']

def make_comp(entry):
    comp = ['image', dsns(entry[1])]
    outline = []
    pins = []
    pad_set = set()
    for val in entry[2:]:
        if val[0] == 'fp_line':
            for arg in val:
                if arg[0] == 'start':
                    startx = '%d' % dsnx(arg[1])
                    starty = '%d' % dsny(arg[2])
                elif arg[0] == 'end':
                    endx = '%d' % dsnx(arg[1])
                    endy = '%d' % dsny(arg[2])
                elif arg[0] == 'width':
                    width = '%d' % scale(arg[1])
            line = ['outline', ['path', 'signal', width, startx, starty, endx, endy]]
            outline = outline + [line]
        elif val[0] == 'pad':
            pad_name = val[1]
            pad_type = val[3]
            for arg in val:
                if arg[0] == 'size':
                    pad_size = (scale(arg[1]), scale(arg[2]))
                elif arg[0] == 'at':
                    x = '%d' % dsnx(arg[1])
                    y = '%d' % dsny(arg[2])
                elif arg[0] == 'layers':
                    layers = arg[1:]
                    if '*.Cu' in layers:
                        pad_layer = 'A'
                    elif 'F.Cu' in layers:
                        pad_layer = 'T'
                    elif 'B.Cu' in layers:
                        pad_layer = 'B'
                    else:
                        raise Exception('Invalid pad layer')
            fr_pad_name = make_pad_name(pad_type, pad_layer, pad_size)
            pad_set.add(fr_pad_name)
            pad = ['pin', dsns(fr_pad_name), pad_name, x, y]
            pins.append(pad)
    
    comp = comp + outline + pins
    return comp, pad_set

def make_pad_name(pad_type, pad_layer, pad_size):
    if pad_type == 'oval':
        return 'Oval[%s]Pad_%dx%d_um' % (pad_layer, pad_size[0], pad_size[1])
    elif pad_type == 'rect':
        return 'Rect[%s]Pad_%dx%d_um' % (pad_layer, pad_size[0], pad_size[1])
    elif pad_type == 'circle':
        return 'Round[%s]Pad_%d_um' % (pad_layer, pad_size[0])
    else:
        raise Exception('Unsupported pad type.')

def make_pad(name):
    types = '(Round|Oval|Rect|Via)'
    layers = '\[([ATB]|0-1)\](Pad)?_'
    size = '(\\d+x\\d+|\\d+:\\d+|\\d+)'
    units = '_um'
    p = re.compile(types + layers + size + units)
    m = p.match(name)
    if not m:
        print p
        print name
        raise Exception('Invalid pad name.')
    else:
        pad = ['padstack', dsns(name)]
        if m.group(1) in ['Round']:
            size_str = m.group(4)
            def shape_gen(side):
                return ['shape', ['circle', side, size_str]]
        elif m.group(1) in ['Via']:
            dia, drill = m.group(4).split(':')
            dia, drill = int(dia), int(drill)
            size_str = '%d' % dia 
            def shape_gen(side):
                return ['shape', ['circle', side, size_str]]
        elif m.group(1) in ['Oval']:
            w, h = m.group(4).split('x')
            w, h = int(w), int(h)
            size_str = '%d' % w # TODO: are there any cases where w != h?
            def shape_gen(side):
                return ['shape', ['path', side, size_str, '0', '0', '0', '0']]
        elif m.group(1) in ['Rect']:
            w, h = m.group(4).split('x')
            w, h = int(w), int(h)
            llx = '%d' % (-w/2)
            lly = '%d' % (-h/2)
            urx = '%d' % (w/2)
            ury = '%d' % (h/2)
            def shape_gen(side):
                return ['shape', ['rect', side, llx, lly, urx, ury]]
        else:
            raise Exception('Invalid pad type.')
        if m.group(2) in ['T', 'A', '0-1']:
            pad.append(shape_gen('F.Cu'))
        if m.group(2) in ['B', 'A', '0-1']:
            pad.append(shape_gen('B.Cu'))
        pad.append(['attach', 'off'])
        return pad

def scale(val):
    return int(1000*float(val))

def dsnx(x):
    return scale(x)

def dsny(y):
    return -scale(y)

def dsns(val):
    val = val.replace('"', '')
    if '-' in val:
        return '"' + val + '"'
    else:
        return val

if __name__ == '__main__':
    main()
