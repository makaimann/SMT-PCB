# Steven Herbst
# sherbst@stanford.edu
#
# CS448H Winter 2017

# Library enables user to instantiate specific parts

import os
import random
from mycad import PcbDesign, PcbComponent, UniqueName

class UsbConnB(PcbComponent):
    def __init__(self, vdd, dm, dp, gnd, shield):
        super(UsbConnB, self).__init__(UniqueName('X'), 'Connectors', 'USB_B')
        self['1'].wire(vdd)
        self['2'].wire(dm)
        self['3'].wire(dp)
        self['4'].wire(gnd)
        self['5'].wire(shield)

class Varistor(PcbComponent):
    def __init__(self, p, n):
        super(Varistor, self).__init__(UniqueName('Z'), 'Varistors', 'RV_Disc_D12_W3.9_P7.5')
        self['1'].wire(p)
        self['2'].wire(n)

class Inductor(PcbComponent):
    def __init__(self, p, n):
        super(Inductor, self).__init__(UniqueName('L'), 'Inductors_SMD', 'L_0805')
        self['1'].wire(p)
        self['2'].wire(n)

class PTC(PcbComponent):
    def __init__(self, p, n):
        super(PTC, self).__init__(UniqueName('F'), 'SMD_Packages', 'Fuse_SMD')
        self['1'].wire(p)
        self['2'].wire(n)

class Resistor(PcbComponent):
    def __init__(self, p, n):
        super(Resistor, self).__init__(UniqueName('R'), 'Resistors_SMD', 'R_0603')
        self['1'].wire(p)
        self['2'].wire(n)

class Capacitor(PcbComponent):
    def __init__(self, p, n):
        super(Capacitor, self).__init__(UniqueName('C'), 'Capacitors_SMD', 'C_0603')
        self['1'].wire(p)
        self['2'].wire(n)

class ICSP(PcbComponent):
    def __init__(self, miso, sck, reset, vdd, mosi, gnd):
        super(ICSP, self).__init__(UniqueName('ICSP'), 'Pin_Headers', 'Pin_Header_Straight_2x03_Pitch2.54mm')
        self['1'].wire(miso)
        self['3'].wire(sck)
        self['5'].wire(reset)
        self['2'].wire(vdd)
        self['4'].wire(mosi)
        self['6'].wire(gnd)

class Header2x2(PcbComponent):
    def __init__(self, pin1, pin2, pin3, pin4): 
        super(Header2x2, self).__init__(UniqueName('JP'), 'Pin_Headers', 'Pin_Header_Straight_2x02_Pitch2.54mm')
        self['1'].wire(pin1)
        self['2'].wire(pin2)
        self['3'].wire(pin3)
        self['4'].wire(pin4)

class ATMEGA16U2(PcbComponent):
    def __init__(self):
        super(ATMEGA16U2, self).__init__(UniqueName('U'), 'Housings_DFN_QFN', 'QFN-32-1EP_5x5mm_Pitch0.5mm')

    def wire_usb(self, vdd, dm, dp, gnd):
        self['31'].wire(vdd)
        self['30'].wire(dm)
        self['29'].wire(dp)
        self['28'].wire(gnd)

    def wire_power(self, vdd, gnd):
        self['32'].wire(vdd)
        self['4'].wire(vdd)
        self['3'].wire(gnd)
        self['33'].wire(gnd)

    @property
    def PB(self):
        pb = {7: self['21'], 6: self['20'], 5: self['19'], 4: self['18'],
              3: self['17'], 2: self['16'], 1: self['15'], 0: self['14']}
        return pb

    @property
    def PD(self):
        pd = {7: self['13'], 6: self['12'], 5: self['11'], 4: self['10'],
              3: self['9'], 2: self['8'], 1: self['7'], 0: self['6']}
        return pd

class RandomComponent(PcbComponent):
    def __init__(self, name):
        lib, part = RandomComponent.rand_lib_part()
        super(RandomComponent, self).__init__(name, lib, part)

    @staticmethod
    def rand_lib_part():
        KISYSMOD = os.environ['KISYSMOD']
        
        mod_list = ['Capacitors_THT.pretty',
                    'Diodes_THT.pretty', 
                    'Inductors_THT.pretty',
                    'Resistors_THT.pretty',
                    'Capacitors_SMD.pretty',
                    'Capacitors_Tantalum_SMD.pretty',
                    'Choke_SMD.pretty',
                    'Diodes_SMD.pretty',
                    'Inductors_SMD.pretty',
                    'Resistors_SMD.pretty']

        lib = random.choice(mod_list)
        lib_full_path = os.path.join(KISYSMOD, lib)
        part = random.choice(os.listdir(lib_full_path))

        lib = os.path.splitext(lib)[0]
        part = os.path.splitext(part)[0]

        return lib, part
