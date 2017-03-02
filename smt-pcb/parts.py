# Steven Herbst
# sherbst@stanford.edu
#
# CS448H Winter 2017

# Library enables user to instantiate specific parts

import os
import random
import re
from mycad import PcbDesign, PcbComponent, PinMapping

class Resistor(PcbComponent):
    def __init__(self, p, n, size='0805', **kwargs):
        super(Resistor, self).__init__('Resistors_SMD', 'R_'+size, **kwargs)
        self.prefix = 'R'
        self['1'].wire(p)
        self['2'].wire(n)

class ResistorPack(PcbComponent):
    def __init__(self, p, n, size='1206', **kwargs):
        super(Resistor, self).__init__('Resistors_SMD', 'R_Array_Convex_4x'+size, **kwargs)
        self.prefix = 'RN'

class Inductor(PcbComponent):
    def __init__(self, p, n, size='0805', **kwargs):
        super(Inductor, self).__init__('Inductors_SMD', 'L_'+size, **kwargs)
        self.prefix = 'L'
        self['1'].wire(p)
        self['2'].wire(n)

class Capacitor(PcbComponent):
    def __init__(self, p, n, ctype='C', size=None, **kwargs):
        if ctype=='C':
            if size is None:
                size = '0805'
        elif ctype=='CP_Elec':
            if size is None:
                size = '5x5.3'
        super(Capacitor, self).__init__('Capacitors_SMD', ctype+'_'+size, **kwargs)
        self.prefix = 'C'
        self['1'].wire(p)
        self['2'].wire(n)

class PMOS(PcbComponent):
    def __init__(self, gate, drain, source, **kwargs):
        super(PMOS, self).__init__('TO_SOT_Packages_SMD', 'SOT-23', **kwargs)
        self.mapping = PinMapping('transistors', 'MMBF170')
        self.prefix = 'Q'
        self[self.mapping['G']].wire(gate)
        self[self.mapping['S']].wire(source)
        self[self.mapping['D']].wire(drain)

class LDO_3v3(PcbComponent):
    def __init__(self, vin, gnd, vout, on=None, **kwargs):
        super(LDO_3v3, self).__init__('TO_SOT_Packages_SMD', 'SOT-23-5', **kwargs)
        self.mapping = PinMapping('regul', 'LP2985LV')
        self.prefix = 'U'
        self[self.mapping['VIN']].wire(vin)
        self[self.mapping['GND']].wire(gnd)
        self[self.mapping['VOUT']].wire(vout)
        
        # By default, enable the LDO
        if on is None:
            on = vin 
        self[self.mapping['ON/OFF']].wire(on)

class LDO_5v0(PcbComponent):
    def __init__(self, vin, gnd, vout, **kwargs):
        super(LDO_5v0, self).__init__('TO_SOT_Packages_SMD', 'SOT-223', **kwargs)
        self.mapping = PinMapping('regul', 'LD1117S50TR')
        self.prefix = 'U'
        self[self.mapping['VI']].wire(vin)
        self[self.mapping['GND']].wire(gnd)
        self[self.mapping['VO']].wire(vout)

class BarrelJack(PcbComponent):
    def __init__(self, vdd, gnd, **kwargs):
        super(BarrelJack, self).__init__('Connectors', 'BARREL_JACK', **kwargs)
        self.prefix = 'X'
        self['1'].wire(vdd)
        self['2'].wire(gnd)
        self['3'].wire(gnd)

class SPST(PcbComponent):
    def __init__(self, p, n, **kwargs):
        super(SPST, self).__init__('Buttons_Switches_SMD', 'SW_SPST_EVQP0', **kwargs)
        self.prefix = 'SW'
        self['1'].wire(p)
        self['2'].wire(n)

class LED(PcbComponent):
    def __init__(self, p, n, size='0805', **kwargs):
        super(LED, self).__init__('LEDs', 'LED_'+size, **kwargs)
        self.prefix = 'D'
        self['1'].wire(p)
        self['2'].wire(n)

class Diode(PcbComponent):
    def __init__(self, p, n, package='1206', **kwargs):
        if package=='SMB':
            part_name = 'D_SMB_Standard'
        else:
            part_name = 'D_' + package
        super(Diode, self).__init__('Diodes_SMD', part_name, **kwargs)
        self.prefix = 'D'
        self['1'].wire(p)
        self['2'].wire(n)

class Crystal(PcbComponent):
    def __init__(self, p, n, **kwargs):
        super(Crystal, self).__init__('Crystals', 'Crystal_HC49-U_Vertical', **kwargs)
        self.prefix = 'X'
        self['1'].wire(p)
        self['2'].wire(n)

class Varistor(PcbComponent):
    def __init__(self, p, n, size='0805', **kwargs):
        super(Varistor, self).__init__('Resistors_SMD', 'R_'+size, **kwargs)
        self.prefix = 'VR'
        self['1'].wire(p)
        self['2'].wire(n)

class PTC(PcbComponent):
    def __init__(self, p, n, size='1812', **kwargs):
        super(PTC, self).__init__('Resistors_SMD', 'R_'+size, **kwargs)
        self.prefix='Z'
        self['1'].wire(p)
        self['2'].wire(n)

class ICSP(PcbComponent):
    def __init__(self, miso, sck, reset, vdd, mosi, gnd, **kwargs):
        super(ICSP, self).__init__('Pin_Headers', 'Pin_Header_Straight_2x03_Pitch2.54mm', **kwargs)
        self.prefix = 'ICSP'
        self['1'].wire(miso)
        self['3'].wire(sck)
        self['5'].wire(reset)
        self['2'].wire(vdd)
        self['4'].wire(mosi)
        self['6'].wire(gnd)

class Header2x2(PcbComponent):
    def __init__(self, pin1, pin2, pin3, pin4, **kwargs):
        super(Header2x2, self).__init__('Pin_Headers', 'Pin_Header_Straight_2x02_Pitch2.54mm', **kwargs)
        self.prefix = 'J'
        self['1'].wire(pin1)
        self['2'].wire(pin2)
        self['3'].wire(pin3)
        self['4'].wire(pin4)

class Header10x1(PcbComponent):
    def __init__(self, pin1, pin2, pin3, pin4, pin5, pin6, pin7, pin8, pin9, pin10, **kwargs): 
        super(Header10x1, self).__init__('Pin_Headers', 'Pin_Header_Straight_1x10_Pitch2.54mm', **kwargs)
        self.prefix = 'J'
        self['1'].wire(pin1)
        self['2'].wire(pin2)
        self['3'].wire(pin3)
        self['4'].wire(pin4)
        self['5'].wire(pin5)
        self['6'].wire(pin6)
        self['7'].wire(pin7)
        self['8'].wire(pin8)
        self['9'].wire(pin9)
        self['10'].wire(pin10)

class Header8x1(PcbComponent):
    def __init__(self, pin1, pin2, pin3, pin4, pin5, pin6, pin7, pin8, **kwargs): 
        super(Header8x1, self).__init__('Pin_Headers', 'Pin_Header_Straight_1x08_Pitch2.54mm', **kwargs)
        self.prefix = 'J'
        self['1'].wire(pin1)
        self['2'].wire(pin2)
        self['3'].wire(pin3)
        self['4'].wire(pin4)
        self['5'].wire(pin5)
        self['6'].wire(pin6)
        self['7'].wire(pin7)
        self['8'].wire(pin8)

class Header6x1(PcbComponent):
    def __init__(self, pin1, pin2, pin3, pin4, pin5, pin6, **kwargs): 
        super(Header6x1, self).__init__('Pin_Headers', 'Pin_Header_Straight_1x06_Pitch2.54mm', **kwargs)
        self.prefix = 'J'
        self['1'].wire(pin1)
        self['2'].wire(pin2)
        self['3'].wire(pin3)
        self['4'].wire(pin4)
        self['5'].wire(pin5)
        self['6'].wire(pin6)

class DualOpAmp(PcbComponent):
    def __init__(self, **kwargs):
        super(DualOpAmp, self).__init__('Housings_SSOP', 'TSSOP-8_4.4x3mm_Pitch0.65mm', **kwargs)
        self.mapping = PinMapping('linear', 'LMV358', **kwargs)
        self.prefix = 'U'

    def wire_power(self, vcc, gnd):
        self[self.mapping['V+']].wire(vcc)
        self[self.mapping['V-']].wire(gnd)

    def wire(self, vip, vin, vo, sub):
        if sub.lower() == 'a':
            self['1'].wire(vo)
            self['2'].wire(vin)
            self['3'].wire(vip)
        elif sub.lower() == 'b':
            self['7'].wire(vo)
            self['6'].wire(vin)
            self['5'].wire(vip)

class UsbConnB(PcbComponent):
    def __init__(self, vdd, dm, dp, gnd, shield, **kwargs):
        super(UsbConnB, self).__init__('Connectors', 'USB_B', **kwargs)
        self.mapping = PinMapping('conn', 'usb_b')
        self.prefix = 'J'
        self[self.mapping['VBUS']].wire(vdd)
        self[self.mapping['D-']].wire(dm)
        self[self.mapping['D+']].wire(dp)
        self[self.mapping['GND']].wire(gnd)
        self[self.mapping['Shield']].wire(shield)

class ATMEGA16U2(PcbComponent):
    def __init__(self, **kwargs):
        super(ATMEGA16U2, self).__init__('Housings_DFN_QFN', 'QFN-32-1EP_5x5mm_Pitch0.5mm', **kwargs)
        self.prefix = 'U'
        self.mapping = PinMapping('atmel', 'ATMEGA16U2-AU')

    def wire_xtal(self, xtal1, xtal2):
        self[self.mapping['XTAL1']].wire(xtal1)
        self[self.mapping['PC0(XTAL2)']].wire(xtal2)

    def wire_usb(self, vdd, dm, dp, gnd):
        self[self.mapping['UVCC']].wire(vdd)
        self[self.mapping['D-']].wire(dm)
        self[self.mapping['D+']].wire(dp)
        self[self.mapping['UGND']].wire(gnd)

    def wire_power(self, vdd, gnd):
        self[self.mapping['AVCC']].wire(vdd)
        self[self.mapping['VCC']].wire(vdd)
        self[self.mapping['GND']].wire(gnd)

    def port_gen(self, port_prefix):
        port = {}
        p = re.compile('\\(.*\\)'+port_prefix+'(\d+)')
        for alias, pin_number in self.mapping.items():
            m = p.match(alias)
            if m is not None:
                port_index = int(m.group(1))
                port[port_index] = self[pin_number]
        return port

    @property
    def ucap(self):
        return self[self.mapping['UCAP']]

    @property
    def reset(self):
        return self[self.mapping['PC1(~RESET~/dW)']]

    @property
    def PB(self):
        return self.port_gen('PB')

    @property
    def PD(self):
        return self.port_gen('PD')

class ATMEGA328P(PcbComponent):
    def __init__(self, **kwargs):
        super(ATMEGA328P, self).__init__('Housings_DIP', 'DIP-28_W7.62mm_Socket', **kwargs)
        self.prefix = 'U'
        self.mapping = PinMapping('atmel', 'ATMEGA328P-PU')

    def wire_xtal(self, xtal1, xtal2):
        self[self.mapping['(PCINT6/XTAL1/TOSC1)PB6']].wire(xtal1)
        self[self.mapping['(PCINT7/XTAL2/TOSC2)PB7']].wire(xtal2)

    def wire_power(self, vdd, gnd):
        self[self.mapping['AVCC']].wire(vdd)
        self[self.mapping['VCC']].wire(vdd)
        for pin_no in self.mapping['GND']:
            self[pin_no].wire(gnd)

    def port_gen(self, port_prefix):
        port = {}
        p = re.compile('\\(.*\\)'+port_prefix+'(\d+)')
        for alias, pin_number in self.mapping.items():
            m = p.match(alias)
            if m is not None:
                port_index = int(m.group(1))
                port[port_index] = self[pin_number]
        return port

    @property
    def aref(self):
        return self[self.mapping['AREF']]

    @property
    def reset(self):
        return self[self.mapping['(PCINT14/~RESET~)PC6']]

    @property
    def PB(self):
        return self.port_gen('PB')

    @property
    def PC(self):
        return self.port_gen('PC')

    @property
    def PD(self):
        return self.port_gen('PD')
    
class RandomComponent(PcbComponent):
    def __init__(self, name):
        lib, part = RandomComponent.rand_lib_part()
        super(RandomComponent, self).__init__(lib, part)
        self.prefix = 'U'

    @staticmethod
    def rand_lib_part():
        KICAD_PATH = os.environ['KICAD_PATH']
        
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
        lib_full_path = os.path.join(KICAD_PATH, 'modules', lib)
        part = random.choice(os.listdir(lib_full_path))

        lib = os.path.splitext(lib)[0]
        part = os.path.splitext(part)[0]

        return lib, part
