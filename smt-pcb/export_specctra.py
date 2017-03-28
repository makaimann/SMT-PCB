#!/usr/bin/env python2

import subprocess
import argparse
import os
import os.path
import time
import json
import re
import math
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
    net_classes = json_dict['net_class_list']

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
    dsn.append(network(design, net_classes))
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

def network(design, net_classes):
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

    # add routing rules
    all_nets = set(net_dict.keys())
    classes = make_net_classes(all_nets, net_classes)
    network = network + classes

    return network

def make_net_classes(all_nets, net_classes):
    # Add nets to net classes as designated by the designer
    all_net_classes = []
    classy_nets = set()
    for net_class in net_classes:
        fr_net_class, net_set = make_net_class(net_class)
        all_net_classes.append(fr_net_class)

        # add the nets of this class to a running set of all nets
        # that are attached to net classes
        classy_nets = classy_nets | net_set
        
    # Add the rest of the nets to a default net class
    rest = all_nets - classy_nets
    rest = [dsns(x) for x in rest]
    rest.append('""')

    # TODO: read default net class information from kicad_pcb
    dia = 0.8
    drill = 0.4
    width = 0.25
    clearance = 0.2
    via = make_pad_name('via', '0-1', (scale(dia), scale(drill)))
    default = net_class_cmd('kicad_default', rest, via, width, clearance)
    all_net_classes.append(default)

    return all_net_classes

def make_net_class(net_class):
    net_set = set()
    name = net_class[1]
    for entry in net_class[3:]:
        if entry[0] == 'clearance':
            clearance = float(entry[1])
        elif entry[0] == 'trace_width':
            width = float(entry[1])
        elif entry[0] == 'via_dia':
            dia = float(entry[1])
        elif entry[0] == 'via_drill':
            drill = float(entry[1])
        elif entry[0] == 'add_net':
            net_set.add(entry[1]) 

    nets = [dsns(x) for x in net_set]
    via = make_pad_name('via', '0-1', (scale(dia), scale(drill)))
    cmd = net_class_cmd(name, nets, via, width, clearance)

    return cmd, net_set

def net_class_cmd(name, nets, via, width, clearance, buf=10e-3):
    # format width and clearance
    # an extra amount is added to the clearance to ensure
    # routing rules are met after taking into account rounding
    width = str(scale(width))
    clearance = str(scale(clearance+buf))

    # generate net class command
    cmd = ['class', name] + nets
    cmd.append(['circuit', ['use_via', via]])
    cmd.append(['rule', ['width', width], ['clearance', clearance]])

    return cmd

def wiring():
    return ['wiring']

def make_comp(entry):
    comp = ['image', dsns(entry[1])]
    outline = []
    pins = []
    pad_set = set()
    for val in entry[2:]:
        if val[0] == 'fp_line':
            outline.append(fp_line_to_path(val))
        elif val[0] == 'fp_circle':
            outline.append(fp_circle_to_path(val))
        elif val[0] == 'pad':
            p = get_pad_params(val)
            fr_pad_name = make_pad_name(p['type'], p['layer'], p['size'])
            pad_set.add(fr_pad_name)
            pad = ['pin', dsns(fr_pad_name), p['name'], p['x'], p['y']]
            pins.append(pad)

    # Libary entry is the composite of its outline and pins
    # It appears that the ouline is only used to make the graphical
    # display more readable, so it may be possible to omit it.    
    comp = comp + outline + pins

    return comp, pad_set

def fp_line_to_path(val):
    for arg in val:
        if arg[0] == 'start':
            startx = '%d' % dsnx(arg[1])
            starty = '%d' % dsny(arg[2])
        elif arg[0] == 'end':
            endx = '%d' % dsnx(arg[1])
            endy = '%d' % dsny(arg[2])
        elif arg[0] == 'width':
            width = '%d' % scale(arg[1])
    return ['outline', ['path', 'signal', width, startx, starty, endx, endy]]

def fp_circle_to_path(val, Nseg=20):
    # read in circle parameters
    for arg in val:
        if arg[0] == 'center':
            cx = float(arg[1])
            cy = float(arg[2])
        elif arg[0] == 'end':
            endx = float(arg[1])
            endy = float(arg[2])
        elif arg[0] == 'width':
            width = str(scale(arg[1]))

    # generate circle
    radius = math.hypot(cx-endx, cy-endy)
    segments = []
    for n in range(Nseg):
        angle = 2*math.pi*n/float(Nseg)
        x = cx + radius*math.cos(angle)
        y = cy + radius*math.sin(angle)
        segments.append(str(dsnx(x)))
        segments.append(str(dsny(y)))

    # return full command
    return ['outline', ['path', 'signal', width] + segments]

def get_pad_params(val):
    params = {}

    params['name'] = val[1]
    params['type'] = val[3]
    for arg in val:
        if arg[0] == 'size':
            params['size'] = (scale(arg[1]), scale(arg[2]))
        elif arg[0] == 'at':
            params['x'] = '%d' % dsnx(arg[1])
            params['y'] = '%d' % dsny(arg[2])
        elif arg[0] == 'layers':
            layers = arg[1:]
            if '*.Cu' in layers:
                params['layer'] = 'A'
            elif 'F.Cu' in layers:
                params['layer'] = 'T'
            elif 'B.Cu' in layers:
                params['layer'] = 'B'
            else:
                raise Exception('Invalid pad layer')

    return params

def make_pad_name(pad_type, pad_layer, pad_size):
    if pad_type == 'oval':
        return 'Oval[%s]Pad_%dx%d_um' % (pad_layer, pad_size[0], pad_size[1])
    elif pad_type == 'rect':
        return 'Rect[%s]Pad_%dx%d_um' % (pad_layer, pad_size[0], pad_size[1])
    elif pad_type == 'circle':
        return 'Round[%s]Pad_%d_um' % (pad_layer, pad_size[0])
    elif pad_type == 'via':
        return 'Via[%s]_%d:%d_um' % (pad_layer, pad_size[0], pad_size[1])
    else:
        raise Exception('Unsupported pad type.')

def make_pad(name):
    # Create a template for matching the pad name
    p = re.compile(r'(?P<type>Round|Oval|Rect|Via)'
                   r'\[(?P<layers>[ATB]|\d+-\d+)\](Pad)?_'
                   r'(?P<size>\d+x\d+|\d+:\d+|\d+)_um')

    # Match pad name to template
    m = p.match(name)
    if not m:
        raise Exception('Invalid pad name.')

    # read out the pad type, size, and layer
    ptype = m.group('type')
    players = m.group('layers')
    psize = m.group('size')

    # Declare new pad with given name
    pad = ['padstack', dsns(name)]

    # generate images of this pad on the appropriate layers
    images = []
    if players in ['T', 'A', '0-1']:
        images.append(get_pad_on_layer(ptype, 'F.Cu', psize))
    if players in ['B', 'A', '0-1']:
        images.append(get_pad_on_layer(ptype, 'B.Cu', psize))

    # add images to pad declaration
    if not images:
        raise Exception('Could not determine layer for pad.')
    pad = pad + images
    
    # Last option, unknown what this does
    pad.append(['attach', 'off'])

    return pad

def get_pad_on_layer(ptype, player, psize):
    if ptype == 'Round':
        return ['shape', ['circle', player, psize]]
    elif ptype == 'Via':
        dia, drill = psize.split(':')
        dia = str(int(dia))
        return ['shape', ['circle', player, dia]]
    elif ptype == 'Oval':
        w, h = psize.split('x')
        w = str(int(w))
        # TODO: what should be done if w != h?
        return ['shape', ['path', player,w, '0', '0', '0', '0']]
    elif ptype == 'Rect':
        w, h = psize.split('x')
        w, h = int(w), int(h)
        corners = [-w/2, -h/2, w/2, h/2]
        corners = [str(x) for x in corners]
        return ['shape', ['rect', player] + corners]
    else:
        raise Exception('Invalid pad type.')

def scale(val):
    # Scales a DSN coordinate to millimeters
    # DSN file is in micrometers, so the scale factor is 1000
    return int(1000*float(val))

def dsnx(x):
    return scale(x)

def dsny(y):
    # It appears that FreeRouting uses a upward y axis
    # while KiCAD uses a downward y axis
    return -scale(y)

def dsns(val):
    # It appears to be necessary to quote strings containing a hyphen
    # This function strips quotes from the string, then adds them 
    # back if there is a hyphen in the string.  In this way, repeated
    # calls to dsns produce the same result.
    val = val.replace('"', '')
    if '-' in val:
        return '"' + val + '"'
    else:
        return val

if __name__ == '__main__':
    main()
