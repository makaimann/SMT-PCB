#  Copyright 2014 Piers Titus van der Torren <pierstitus@gmail.com>
#  Copyright 2015 Miguel Angel Ajo <miguelangel@ajo.es>
#
#  This program is free software; you can redistribute it and/or modify
#  it under the terms of the GNU General Public License as published by
#  the Free Software Foundation; either version 2 of the License, or
#  (at your option) any later version.
#
#  This program is distributed in the hope that it will be useful,
#  but WITHOUT ANY WARRANTY; without even the implied warranty of
#  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#  GNU General Public License for more details.
#
#  You should have received a copy of the GNU General Public License
#  along with this program; if not, write to the Free Software
#  Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston,
#  MA 02110-1301, USA.
#
pcbnew = __import__('pcbnew')


import kicad
from kicad.point import BoundingBox
from kicad.pcbnew import drawing
from kicad.pcbnew import module
from kicad.pcbnew.track import Track
from kicad.pcbnew.via import Via
from kicad.pcbnew.net import Net
from kicad import units

class _ModuleList(object):
    """Internal class to represent `Board.modules`"""
    def __init__(self, board):
        self._board = board

    def __getitem__(self, key):
        found = self._board._obj.FindModuleByReference(key)
        if found:
            return module.Module.wrap(found)
        else:
            raise KeyError("No module with reference: %s" % key)

    def __iter__(self):
        # Note: this behavior is inconsistent with python manuals
        # suggestion. Manual suggests that a mapping should iterate
        # over keys ('reference' in our case). See:
        # https://docs.python.org/2.7/reference/datamodel.html?emulating-container-types#object.__iter__
        # But in my opinion `_ModuleList` is a list then mapping.
        for m in self._board._obj.GetModules():
            yield module.Module.wrap(m)

    def __len__(self):
        return self._board._obj.GetModules().GetCount()

class _NetList(object):
    def __init__(self, board):
        self._board = board

    def __getitem__(self, key):
        nets = self._board._obj.GetNetsByName()
        found = nets.find(key).value()[1]
        if found:
            return Net.wrap(found)
        else:
            raise KeyError("No net with name: %s" % key)

    def __iter__(self):
        for netname, net in self._board._obj.GetNetsByName().items():
            yield Net.wrap(net)

    def __len__(self):
        return self._board._obj.GetNetCount()

class Board(object):
    def __init__(self, wrap=None):
        """Board object"""
        if wrap:
            self._obj = wrap
        else:
            self._obj = pcbnew.BOARD()

        self._modulelist = _ModuleList(self)
        self._netlist = _NetList(self)

    @property
    def native_obj(self):
        return self._obj

    @staticmethod
    def wrap(instance):
        """Wraps a C++/old api BOARD object, and returns a Board."""
        return Board(wrap=instance)

    def add(self, obj):
        """Adds an object to the Board.

        Tracks, Drawings, Modules, etc...
        """
        self._obj.Add(obj.native_obj)
        return obj

    def clearLayer(self, layer):
        """Removes all drawings from the specified layer"""
        for d in self._obj.GetDrawings():
            if d.GetLayerName() == layer:
                self._obj.Remove(d)

    @property
    def comments(self):
        titleBlock = self._obj.GetTitleBlock()
        comment4 = titleBlock.GetComment4()
        comment3 = titleBlock.GetComment3()
        comment2 = titleBlock.GetComment2()
        comment1 = titleBlock.GetComment1()
        return [comment4, comment3, comment2, comment1]

    @comments.setter
    def comments(self, value):
        # Pad comments with empty lines as necessary
        comments = value + ['']*(4-len(value))
        
        titleBlock = self._obj.GetTitleBlock()
        titleBlock.SetComment4(comments[0])
        titleBlock.SetComment3(comments[1])
        titleBlock.SetComment2(comments[2])
        titleBlock.SetComment1(comments[3])

    @property
    def date(self):
        return self._obj.GetTitleBlock().GetDate()

    @date.setter
    def date(self, value):
        return self._obj.GetTitleBlock().SetDate(value.ctime())

    @property
    def company(self):
        return self._obj.GetTitleBlock().GetCompany()

    @company.setter
    def company(self, value):
        return self._obj.GetTitleBlock().SetCompany(value)

    @property
    def revision(self):
        return self._obj.GetTitleBlock().GetRevision()

    @revision.setter
    def revision(self, value):
        return self._obj.GetTitleBlock().SetRevision(value)
    
    @property
    def title(self):
        return self._obj.GetTitleBlock().GetTitle()

    @title.setter
    def title(self, value):
        return self._obj.GetTitleBlock().SetTitle(value)

    @property
    def modules(self):
        """Provides an iterator over the board Module objects."""
        return self._modulelist

    @property
    def nets(self):
        """Provides an iterator over the board Net objects."""
        return self._netlist

    def moduleByRef(self, ref):
        """Returns the module that has the reference `ref`. Returns `None` if
        there is no such module."""
        found = self._obj.FindModuleByReference(ref)
        if found:
            return module.Module.wrap(found)

    @property
    def boundingBox(self):
        return BoundingBox.wrap(self._obj.ComputeBoundingBox())

    @property
    def vias(self):
        """An iterator over via objects"""
        for t in self._obj.GetTracks():
            if type(t) == pcbnew.VIA:
                yield Via.wrap(t)
            else:
                continue

    @property
    def tracks(self):
        """An iterator over track objects"""
        for t in self._obj.GetTracks():
            if type(t) == pcbnew.TRACK:
                yield Track.wrap(t)
            else:
                continue

    @staticmethod
    def from_editor():
        """Provides the board object from the editor."""
        return Board.wrap(pcbnew.GetBoard())

    @staticmethod
    def load(filename):
        """Loads a board file."""
        return Board.wrap(pcbnew.LoadBoard(filename))

    def save(self, filename=None):
        """Save the board to a file.

        filename should have .kicad_pcb extention.
        """
        if filename is None:
            filename = self._obj.GetFileName()
        self._obj.Save(filename)

    # TODO: add setter for Board.filename
    @property
    def filename(self):
        """Name of the board file."""
        return self._obj.GetFileName()

    def add_module(self, ref, pos=(0, 0)):
        """Create new module on the board"""
        return module.Module(ref, pos, board=self)

    @property
    def default_width(self, width=None):
        b = self._obj
        return (
            float(b.GetDesignSettings().GetCurrentTrackWidth()) /
            units.DEFAULT_UNIT_IUS)

    def add_track_segment(self, start, end, layer='F.Cu', width=None, net=None):
        """Create a track segment."""

        track = Track(width or self.default_width,
                      start, end, layer, board=self)
        self._obj.Add(track.native_obj)
        track.native_obj.SetNet(self.nets[net]._obj)
        return track

    def get_layer(self, name):
        return self._obj.GetLayerID(name)

    def add_track(self, coords, layer='F.Cu', width=None, net=None):
        """Create a track polyline.

        Create track segments from each coordinate to the next.
        """
        for n in range(len(coords) - 1):
            self.add_track_segment(coords[n], coords[n + 1],
                                   layer=layer, width=width, net=net)

    @property
    def default_via_size(self):
        return (float(self._obj.GetDesignSettings().GetCurrentViaSize()) /
                units.DEFAULT_UNIT_IUS)

    @property
    def default_via_drill(self):
        via_drill = self._obj.GetDesignSettings().GetCurrentViaDrill()
        if via_drill > 0:
            return (float(via_drill) / units.DEFAULT_UNIT_IUS)
        else:
            return 0.2

    def add_via(self, coord, layer_pair=('B.Cu', 'F.Cu'), size=None,
                drill=None, net=None):
        """Create a via on the board.

        :param coord: Position of the via.
        :param layer_pair: Tuple of the connected layers (for example
                           ('B.Cu', 'F.Cu')).
        :param size: size of via in mm, or None for current selection.
        :param drill: size of drill in mm, or None for current selection.
        :returns: the created Via
        """
        if size is None:
            size = self.default_via_size
        if drill is None:
            drill = self.default_via_drill

        via = Via(coord, diameter=size, drill=drill, board=self, layer_pair=layer_pair)
        self.add(via)

        if net is not None:
            via._obj.SetNet(self.nets[net]._obj)

        return via

    def add_line(self, start, end, layer='F.SilkS', width=0.15):
        """Create a graphic line on the board"""
        return self.add(
            drawing.Segment(start, end, layer, width, board=self))

    def add_polyline(self, coords, layer='F.SilkS', width=0.15):
        """Create a graphic polyline on the board"""
        for n in range(len(coords) - 1):
            self.add_line(coords[n], coords[n + 1], layer=layer, width=width)

    def add_circle(self, center, radius, layer='F.SilkS', width=0.15):
        """Create a graphic circle on the board"""
        return self.add(
            drawing.Circle(center, radius, layer, width, board=self))

    def add_arc(self, center, radius, start_angle, stop_angle,
                layer='F.SilkS', width=0.15):
        """Create a graphic arc on the board"""
        return self.add(
            drawing.Arc(center, radius, start_angle, stop_angle,
                        layer, width, board=self))

    def add_zone(self, outline, net, layer, clearance):
        # Create the new area
        net = self.nets[net].netcode
        layer = self.get_layer(layer)
        x0 = outline[0]._obj.x
        y0 = outline[0]._obj.y
        hatch = pcbnew.CPolyLine.DIAGONAL_EDGE
        area = self._obj.InsertArea(net, 0, layer, x0, y0, hatch)

        # Create the outline
        border = area.Outline()
        for point in outline[1:]:
            print dir(border)
            print type(border)
            border.append(point._obj)
        border.CloseLastContour()

        # Fill in the outline
        area.BuildFilledSolidAreasPolygons(self._obj)
