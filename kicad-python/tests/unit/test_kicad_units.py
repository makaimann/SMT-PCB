import unittest

from kicad import *


class TestKicadUnits(unittest.TestCase):

    def test_converters(self):
        self.assertEqual(inch_to_mm(1), 25.4)
        self.assertEqual(mm_to_inch(25.4), 1.0)

    def test_converters_seq(self):
        self.assertEqual(inch_to_mm([1, 2]), [25.4, 50.8])
        self.assertEqual(mm_to_inch([25.4, 50.8]), [1.0, 2.0])

    def test_base_unit_tuple_mm(self):
        bunit = Point(1, 2)
        self.assertEqual(bunit.mm, (1.0, 2.0))

    def test_base_unit_tuple_inch(self):
        bunit = Point(1 * inch, 2 * inch)
        self.assertEqual(bunit.inch, (1.0, 2.0))

    def test_base_unit_tuple_mil(self):
        bunit = Point(1 * mil, 2 * mil)
        self.assertEqual(bunit.mil, (1.0, 2.0))

    def test_base_unit_tuple_nm(self):
        bunit = Point(1 * nm, 2 * nm)
        self.assertEqual(bunit.nm, (1, 2))
