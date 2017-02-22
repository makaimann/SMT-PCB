import unittest

from kicad import *
from kicad.pcbnew.drawing import *
from kicad import obj


class TestPcbnewDrawing(unittest.TestCase):
    def test_segment_from_native(self):
        native_segment = Segment((0, 0), (1, 1))._obj
        new_segment = obj.wrap(native_segment)
        self.assertEqual(Segment, type(new_segment))

    def test_circle_from_native(self):
        native_circle = Circle((0, 0), 10.0)._obj
        new_circle = obj.wrap(native_circle)
        self.assertEqual(Circle, type(new_circle))

    def test_arc_from_native(self):
        native_arc = Arc((0, 0), 10.0, -90, 90)._obj
        new_arc = obj.wrap(native_arc)
        self.assertEqual(Arc, type(new_arc))
