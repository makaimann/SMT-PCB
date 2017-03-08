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
from kicad.pcbnew import layer
from kicad.point import Point
from kicad import units
from kicad.pcbnew.item import HasPosition

class Via(HasPosition, object):
    def __init__(self, coord, diameter, drill, board=None, 
                 layer_pair=('F.Cu', 'B.Cu'), via_type='through'):
        self._obj = pcbnew.VIA(board and board.native_obj)

        # define the layers used
        if board:
            self._obj.SetLayerPair(board.get_layer(layer_pair[0]),
                                   board.get_layer(layer_pair[1]))
        else:
            self._obj.SetLayerPair(layer.get_std_layer(layer_pair[0]),
                                   layer.get_std_layer(layer_pair[1]))

        # define the position
        self._obj.SetPosition(coord.native_obj)

        # define the via type
        if via_type.lower() == 'through':
            self._obj.SetViaType(pcbnew.VIA_THROUGH)
        elif via_type.lower() == 'blind_buried':
            self._obj.SetViaType(pcbnew.VIA_BLIND_BURIED)
        elif via_type.lower() == 'microvia':
            self._obj.SetViaType(pcbnew.VIA_MICROVIA)
        else:
            raise Exception('Unimplemented via type.')

        # Define overall via diameter (drill + annular ring)
        self.diameter = diameter

        # Define the drill size
        self.drill = drill

    @property
    def native_obj(self):
        return self._obj

    @staticmethod
    def wrap(instance):
        """Wraps a C++ api VIA object, and returns a `Via`."""
        return kicad.new(Via, instance)

    @property
    def drill(self):
        """Via drill diameter"""
        return float(self._obj.GetDrill()) / units.DEFAULT_UNIT_IUS

    @drill.setter
    def drill(self, value):
        self._obj.SetDrill(int(value * units.DEFAULT_UNIT_IUS))

    @property
    def diameter(self):
        """Via diameter"""
        return float(self._obj.GetWidth()) / units.DEFAULT_UNIT_IUS

    @diameter.setter
    def diameter(self, value):
        self._obj.SetWidth(int(value * units.DEFAULT_UNIT_IUS))
