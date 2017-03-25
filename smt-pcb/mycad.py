# Steven Herbst
# sherbst@stanford.edu
#
# CS448H Winter 2017

# Library enables user to instantiate new modules from KiCAD library

# general imports
import os
from datetime import date
import pcbnew
import json
import heapq

# project-specific
from kicad.pcbnew.module import Module
from kicad.pcbnew.board import Board
from kicad.point import Point


class PcbDesign(object):
    def __init__(
            self,
            fname,
            dx=1.0,
            dy=1.0,
            refdes_max_count=1000,
            def_route_constr=10,
            use_def_constr=True):

        self.fname = fname
        self.comp_dict = {}
        self.net_class_list = []
        self.routing_list = []
        self.net_constr_list = []
        self.dx = dx
        self.dy = dy
        self.refdes_max_count = refdes_max_count
        self.def_route_constr = def_route_constr
        self.refdes_set = set()
        self.keepouts = []
        self.use_def_constr = use_def_constr

        self.comments = None
        self.title = None
        self.revision = None
        self.company = None
        self.date = date.today()

        # Nets to be ignored when automatically generating constraints
        self.ignore_nets = ['GND', 'UGND', '+5V', '+3V3']

    def __contains__(self, item):
        return item in self.comp_dict

    def __iter__(self):
        for comp in self.comp_dict.values():
            yield comp

    def __setitem__(self, key, val):
        self.comp_dict[key] = val

    def __getitem__(self, key):
        return self.comp_dict[key]

    def add_pad_constr(self, pad1, pad2, length=None):
        # dictionary to hold the constraint
        req = {}

        # component 1 description
        req['comp1'] = pad1.parent.name
        pad1_center_rel = pad1.pad.center - pad1.parent.boundingBox.ul
        req['pad1x'] = pad1_center_rel.x + pad1.parent.bufx
        req['pad1y'] = pad1_center_rel.y + pad1.parent.bufy

        # component 2 description
        req['comp2'] = pad2.parent.name
        pad2_center_rel = pad2.pad.center - pad2.parent.boundingBox.ul
        req['pad2x'] = pad2_center_rel.x + pad2.parent.bufx
        req['pad2y'] = pad2_center_rel.y + pad2.parent.bufy

        # maximum length constraint
        if length is None:
            length = self.def_route_constr

        # always add minimum edge distances of each pad involved
        length = length + pad1.edgeDist + pad2.edgeDist
        req['max_length'] = length

        self.routing_list.append(req)

        # print constraint
        ineq = '|' + str(pad1) + ' - ' + str(pad2) + '| < %0.3fmm' % length
        print 'Added constraint: ' + ineq

    def add_net_constr(self, net, length=None):
        net_constr = {'net': net, 'length': length}
        self.net_constr_list.append(net_constr)

    def make_net_constraints(self):
        net_dict = self.get_net_dict()
        for net_constr in self.net_constr_list:
            pads = net_dict[net_constr['net']]
            for pad0, pad1 in zip(pads[:-1], pads[1:]):
                self.add_pad_constr(pad0, pad1, net_constr['length'])

    def add(self, *args):
        for arg in args:
            if isinstance(arg, PcbComponent):
                arg.parent = self
                arg.name = self.nextRefdes(arg.prefix)
                self[arg.name] = arg
            elif isinstance(arg, PcbKeepout):
                arg.name = self.nextRefdes(arg.prefix)
                self.keepouts.append(arg)
            else:
                raise Exception('Component type not handled.')

    def add_net_class(self, net_class):
        self.net_class_list.append(net_class)

    def nextRefdes(self, prefix):
        for count in range(1, self.refdes_max_count + 1):
            name = unicode(prefix + str(count))
            if name not in self.refdes_set:
                break
        self.refdes_set.add(name)
        return name

    def wire(self, net_name, *args):
        for arg in args:
            arg.wire(net_name)

    def add_keepouts(self, min_kw=1e-3, min_kh=1e-3):
        # TODO: handle more general cases

        # determine the board height from the edge
        ylist = [p.y for p in self.edge]
        height = max(ylist) - min(ylist)

        for p0, p1 in zip(self.edge[:-1], self.edge[1:]):
            x0, y0 = p0
            x1, y1 = p1

            if x1 > x0:
                # quadrants I and IV
                kw = x1 - x0
                kh = max(y0, y1)
                kx = x0
                ky = 0
            elif x0 > x1:
                # quadrants II and III
                kw = x0 - x1
                kh = height - min(y0, y1)
                kx = x1
                ky = min(y0, y1)
            else:
                continue

            if kw > min_kw and kh > min_kw:
                kpos = Point(kx, ky)
                self.add(PcbKeepout(width=kw, height=kh, position=kpos))

    def compile(self, json_file=None):
        # add keepouts based on the edge
        self.add_keepouts()

        # Create empty PCB
        pcb = Board()

        # add all components to the board
        for comp in self:
            pcb.add(comp.module)

        # make the title block
        self.make_title_block(pcb)

        # save PCB file without connectivity information
        pcb.save(self.fname)

        # write input file for SMT solver
        self.write_json_dict(json_file)

    def make_title_block(self, pcb):
        if self.comments:
            pcb.comments = self.comments
        if self.title:
            pcb.title = self.title
        if self.revision:
            pcb.revision = self.revision
        if self.company:
            pcb.company = self.company
        if self.date:
            pcb.date = self.date

    def get_design_dict(self):
        design_dict = {}
        for comp in self:
            if comp.name not in design_dict:
                design_dict[comp.name] = {}
            for pad in comp:
                if pad.net_name is not None:
                    design_dict[comp.name][pad.name] = pad.net_name
        for keepout in self.keepouts:
            design_dict[keepout.name] = {}
        return design_dict

    def get_net_dict(self):
        net_dict = {}
        for comp in self:
            for pad in comp:
                if pad.net_name not in net_dict:
                    net_dict[pad.net_name] = []
                net_dict[pad.net_name].append(pad)
        return net_dict

    def get_module_dict(self):
        module_dict = {}

        items = self.comp_dict.values() + self.keepouts

        for item in items:
            # add type information
            if isinstance(item, PcbComponent):
                type_str = 'comp'
            elif isinstance(item, PcbKeepout):
                type_str = 'keepout'
            else:
                raise Exception('Unsupported item type.')

            module_dict[item.name] = {}
            module_dict[item.name]['type'] = type_str

            # define rotation
            module_dict[item.name]['rotation'] = item.rotation

            # set fixed position if provided
            if item.position is not None:
                fixed_pos = item.get_fixed_pos()
                module_dict[item.name]['x'] = fixed_pos.x - item.bufx
                module_dict[item.name]['y'] = fixed_pos.y - item.bufy
                module_dict[item.name]['fixed'] = True
            else:
                module_dict[item.name]['x'] = None
                module_dict[item.name]['y'] = None
                module_dict[item.name]['fixed'] = False

            # add size information
            module_dict[item.name]['width'] = item.width + 2 * item.bufx
            module_dict[item.name]['height'] = item.height + 2 * item.bufy

            # add buffer information
            module_dict[item.name]['bufx'] = item.bufx
            module_dict[item.name]['bufy'] = item.bufy

            # add ordering information
            module_dict[item.name]['partno'] = item.partno

        return module_dict

    @property
    def edge(self):
        return self.edge_points

    @edge.setter
    def edge(self, value):
        self.edge_points = value

    def get_all_mods(self):
        # generate set of fixed modules
        all_mods = set()
        for comp in self:
            all_mods.add(comp.name)

        return all_mods

    def get_fixed_mods(self):
        # generate set of fixed modules
        fixed_mods = set()
        for comp in self:
            if comp.position is not None:
                fixed_mods.add(comp.name)

        return fixed_mods

    def get_constr_mods(self):
        # comps with routing_list constraints
        constr_mods = set()
        for req in self.routing_list:
            constr_mods.add(req['comp1'])
            constr_mods.add(req['comp2'])

        return constr_mods

    def get_conn_pads(self, pad):
        # skip certain nets that don't make for good constraints
        if pad.net_name in self.ignore_nets:
            return []

        # look for other pads that are connected to this one
        conn_pads = []
        for other_mod in self:
            if other_mod.name == pad.parent.name:
                continue
            for other_pad in other_mod:
                if other_pad.net_name == pad.net_name:
                    conn_pads.append(other_pad)

        return conn_pads

    def write_json_dict(self, json_file):
        json_dict = {}
        json_dict['module_dict'] = self.get_module_dict()
        json_dict['design_dict'] = self.get_design_dict()

        # add net class list information since this will have to
        # added as the last step
        net_class_list = [net_class.list_form() for
                          net_class in self.net_class_list]
        json_dict['net_class_list'] = net_class_list

        # add the board edge definition
        json_dict['board_edge'] = [(p.x, p.y) for p in self.edge]

        # add the list of pad placement constraints
        self.make_net_constraints()
        if self.use_def_constr:
            self.add_default_constr()
        print 'Number of pad-pad constraints:', len(self.routing_list)
        json_dict['routing_list'] = self.routing_list

        with open(json_file, 'w') as f:
            json.dump(json_dict, f, indent=2, sort_keys=True)

    def add_default_constr(self):

        # add parts in priority order
        pinned = self.get_fixed_mods()
        constr = self.get_constr_mods()
        unconstr = set()
        ps = PrioritySet()
        for mod in self:
            if mod.name in pinned:
                ps.add(mod.name, PrioritySet.PINNED)
            elif mod.name in constr:
                ps.add(mod.name, PrioritySet.CONSTR)
            else:
                ps.add(mod.name, PrioritySet.UNCONSTR)
                unconstr.add(mod.name)
        
        # Print the unconstrained modules
        print 'unconstr:', map(str, unconstr)

        while ps.set:
            comp = ps.get()
            self.constr_comp(comp, ps, unconstr)

    def constr_comp(self, comp, ps, unconstr):
        for pad1 in self[comp]:
            connected_pads = self.get_conn_pads(pad1)
            for pad2 in connected_pads:
                neighbor = pad2.parent.name
                if neighbor in unconstr:
                    ps.add(neighbor, PrioritySet.CONSTR)
                    unconstr.remove(neighbor)
                    if comp in unconstr:
                        unconstr.remove(comp)
                    self.add_pad_constr(pad1, pad2)

class PcbPad(object):
    def __init__(self, pad):
        self.pad = pad
        self.net_name = None

    def wire(self, net_name):
        self.net_name = net_name

    def __str__(self):
        return self.parent.name + '.' + self.name

    @property
    def name(self):
        return self.pad.name

    @property
    def edgeDist(self):
        bbox = self.parent.boundingBox
        bufx = self.parent.bufx
        bufy = self.parent.bufy
        center = self.pad.center
        return min(min(bbox.ll.y +
                       bufy -
                       center.y, center.y -
                       bbox.ul.y +
                       bufy), min(bbox.ur.x +
                                  bufx -
                                  center.x, center.x -
                                  bbox.ul.x +
                                  bufx))


class PcbComponent(object):
    def __init__(
            self,
            lib,
            part,
            partno=None,
            position=None,
            rotation=None,
            mode=None,
            bufx=0.4,
            bufy=0.4,
            **kwargs):

        # instantiate the part
        self.load_module(lib, part)

        # ordering information
        self.partno = partno

        # set the position and rotation
        self.position = position

        # if the part has a fixed location, set the
        # rotation and positioning mode
        if position is not None:
            if rotation is None:
                self.rotation = 0.0
            else:
                self.rotation = rotation

            if mode is None:
                self.mode = 'UL'
            else:
                self.mode = mode

        # set the buffer space around the part
        self.bufx = bufx
        self.bufy = bufy

        # fill up the dictionary defining component pads
        self.pad_dict = {}
        self.populate_pads()

    def load_module(self, lib, part):
        # determine path to KICAD libraries
        kicad_path = os.environ['KICAD_PATH']
        file_ext = 'pretty'

        # determine the appropriate plugin to use for loading the module
        src_libpath = os.path.join(kicad_path, 'modules', lib + '.' + file_ext)
        src_type = pcbnew.IO_MGR.GuessPluginTypeFromLibPath(src_libpath)
        src_plugin = pcbnew.IO_MGR.PluginFind(src_type)

        # load footprint, wrap using kicad-python
        footprint = src_plugin.FootprintLoad(src_libpath, part)
        self.module = Module.wrap(footprint)

    def populate_pads(self):
        for pad in self.module.pads:
            self[pad.name] = PcbPad(pad)
            self[pad.name].parent = self

    def get_pin(self, name):
        return self[self.mapping[name]]

    def get_pad_on_net(self, net_name):
        for pad in self:
            if pad.net_name == net_name:
                return pad
        return None

    def get_fixed_pos(self):
        if self.mode.lower() == 'ul':
            ul_relative = Point(0, 0)
        elif self.mode.lower() == 'pin1':
            ul_relative = self.boundingBox.ul - self['1'].pad.center
        elif self.mode.lower() == 'center':
            comp_center = Point.wrap(self.module._obj.GetCenter())
            ul_relative = self.boundingBox.ul - comp_center
        else:
            raise Exception('Unimplemented positioning mode.')

        return self.position + ul_relative

    def __contains__(self, item):
        return item in self.pad_dict

    def __iter__(self):
        for pad in self.pad_dict.values():
            yield pad

    def __setitem__(self, key, val):
        self.pad_dict[key] = val

    def __getitem__(self, key):
        return self.pad_dict[key]

    @property
    def width(self):
        return self.module.boundingBox.width

    @property
    def height(self):
        return self.module.boundingBox.height

    @property
    def pads(self):
        for pad in self.pad_dict.values():
            yield pad

    @property
    def name(self):
        return self.module.reference

    @name.setter
    def name(self, value):
        self.module.reference = value

    @property
    def rotation(self):
        return self.module.rotation

    @rotation.setter
    def rotation(self, value):
        self.module.rotation = value

    @property
    def boundingBox(self):
        return self.module.boundingBox


class NetClass(object):
    def __init__(self, name, description="", clearance=0.2, trace_width=0.4,
                 via_dia=0.8, via_drill=0.4, uvia_dia=0.3, uvia_drill=0.1):

        if name == 'Default':
            raise Exception('Naming a NetClass "Default" is not allowed.')

        self.name = name
        self.description = description
        self.clearance = clearance
        self.trace_width = trace_width
        self.via_dia = via_dia
        self.via_drill = via_drill
        self.uvia_dia = uvia_dia
        self.uvia_drill = uvia_drill

        self.nets = []

    def add(self, *args):
        if isinstance(args, list) or isinstance(args, tuple):
            print 'Adding list of nets:', args
            for net in args:
                self.nets.append(net)
        else:
            print 'Adding single net:', args
            self.nets.append(args)

    def list_form(self):
        # Populate net class options
        cmd = ['net_class', self.name, '"' + self.description + '"',
               ['clearance', str(self.clearance)],
               ['trace_width', str(self.trace_width)],
               ['via_dia', str(self.via_dia)],
               ['via_drill', str(self.via_drill)],
               ['uvia_dia', str(self.uvia_dia)],
               ['uvia_drill', str(self.uvia_drill)]]

        # Add connected nets to command
        for net in self.nets:
            cmd.append(['add_net', net])

        # Return the full command
        return cmd


class PcbKeepout(object):
    def __init__(self, position, width, height):
        self.rotation = 0.0
        self.position = position
        self.bufx = 0.0
        self.bufy = 0.0
        self.width = width
        self.height = height
        self.partno = None
        self.prefix = 'K'

    def get_fixed_pos(self):
        return self.position

class PrioritySet(object):
    PINNED = 0
    CONSTR = 1
    UNCONSTR = 2

    # reference: http://stackoverflow.com/questions/5997189/how-can-i-make-a-unique-value-priority-queue-in-python
    def __init__(self):
        self.heap = []
        self.set = set()

    def add(self, d, pri):
        if not d in self.set:
            heapq.heappush(self.heap, (pri, d))
            self.set.add(d)

    def get(self):
        pri, d = heapq.heappop(self.heap)
        self.set.remove(d)
        return d
