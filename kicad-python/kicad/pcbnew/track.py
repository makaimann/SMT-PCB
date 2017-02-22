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
from kicad.pcbnew import layer as pcbnew_layer
from kicad.point import Point
from kicad import units

class Track(object):
    def __init__(self, width, start, end, layer='F.Cu', board=None):
        self._track = pcbnew.TRACK(board and board.native_obj)
        self._track.SetWidth(int(width * units.DEFAULT_UNIT_IUS))
        if board:
            self._track.SetLayer(board.get_layer(layer))
        else:
            self._track.SetLayer(pcbnew_layer.get_std_layer(layer))
        self._track.SetStart(Point.native_from(start))
        self._track.SetEnd(Point.native_from(end))

    @property
    def native_obj(self):
        return self._track

    @staticmethod
    def wrap(instance):
        """Wraps a C++ api TRACK object, and returns a `Track`."""
        return kicad.new(Track, instance)

    @property
    def width(self):
        return float(self._obj.GetWidth()) / units.DEFAULT_UNIT_IUS

    @width.setter
    def width(self, value):
        self._obj.SetWidth(int(value * units.DEFAULT_UNIT_IUS))
