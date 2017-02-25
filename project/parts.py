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
    def __init__(self, p, n, size='0805'):
        super(Resistor, self).__init__('Resistors_SMD', 'R_'+size)
        self.prefix = 'R'
        self['1'].wire(p)
        self['2'].wire(n)

class Inductor(PcbComponent):
    def __init__(self, p, n, size='0805'):
        super(Inductor, self).__init__('Inductors_SMD', 'L_'+size)
        self.prefix = 'L'
        self['1'].wire(p)
        self['2'].wire(n)

class Capacitor(PcbComponent):
    def __init__(self, p, n, size='0805'):
        super(Capacitor, self).__init__('Capacitors_SMD', 'C_'+size)
        self.prefix = 'C'
        self['1'].wire(p)
        self['2'].wire(n)

class LED(PcbComponent):
    def __init__(self, p, n, size='0805'):
        super(LED, self).__init__('LEDs', 'LED_'+size)
        self.prefix = 'D'
        self['1'].wire(p)
        self['2'].wire(n)

class Diode(PcbComponent):
    def __init__(self, p, n, size='0805'):
        super(Diode, self).__init__('Diodes_SMD', 'D_'+size)
        self.prefix = 'D'
        self['1'].wire(p)
        self['2'].wire(n)

class Crystal(PcbComponent):
    def __init__(self, p, n):
        super(Crystal, self).__init__('Crystals', 'Crystal_HC49-U_Vertical')
        self.prefix = 'X'
        self['1'].wire(p)
        self['2'].wire(n)

class Varistor(PcbComponent):
    def __init__(self, p, n):
        super(Varistor, self).__init__('Resistors_SMD', 'R_0603')
        self.prefix = 'VR'
        self['1'].wire(p)
        self['2'].wire(n)

class PTC(PcbComponent):
    def __init__(self, p, n):
        super(PTC, self).__init__('Resistors_SMD', 'R_1812')
        self.prefix='Z'
        self['1'].wire(p)
        self['2'].wire(n)

class ICSP(PcbComponent):
    def __init__(self, miso, sck, reset, vdd, mosi, gnd):
        super(ICSP, self).__init__('Pin_Headers', 'Pin_Header_Straight_2x03_Pitch2.54mm')
        self.prefix = 'ICSP'
        self['1'].wire(miso)
        self['3'].wire(sck)
        self['5'].wire(reset)
        self['2'].wire(vdd)
        self['4'].wire(mosi)
        self['6'].wire(gnd)

class Header2x2(PcbComponent):
    def __init__(self, pin1, pin2, pin3, pin4):
        super(Header2x2, self).__init__('Pin_Headers', 'Pin_Header_Straight_2x02_Pitch2.54mm')
        self.prefix = 'J'
        self['1'].wire(pin1)
        self['2'].wire(pin2)
        self['3'].wire(pin3)
        self['4'].wire(pin4)

class Header10x1(PcbComponent):
    def __init__(self, pin1, pin2, pin3, pin4, pin5, pin6, pin7, pin8, pin9, pin10): 
        super(Header10x1, self).__init__('Pin_Headers', 'Pin_Header_Straight_1x10_Pitch2.54mm')
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
    def __init__(self, pin1, pin2, pin3, pin4, pin5, pin6, pin7, pin8): 
        super(Header8x1, self).__init__('Pin_Headers', 'Pin_Header_Straight_1x08_Pitch2.54mm')
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
    def __init__(self, pin1, pin2, pin3, pin4, pin5, pin6): 
        super(Header6x1, self).__init__('Pin_Headers', 'Pin_Header_Straight_1x06_Pitch2.54mm')
        self.prefix = 'J'
        self['1'].wire(pin1)
        self['2'].wire(pin2)
        self['3'].wire(pin3)
        self['4'].wire(pin4)
        self['5'].wire(pin5)
        self['6'].wire(pin6)

class DualOpAmp(PcbComponent):
    def __init__(self):
        super(DualOpAmp, self).__init__('Housings_SSOP', 'TSSOP-8_4.4x3mm_Pitch0.65mm')
        self.mapping = PinMapping('linear', 'LMV358')
        self.prefix = 'U'

    def wire_power(self, vcc, gnd):
        self[self.mapping['V+']].wire(vcc)
        self[self.mapping['V-']].wire(gnd)

    def wire_op_amp(self, vip, vin, vo):
        self[self.mapping['+']].wire(vip)
        self[self.mapping['-']].wire(vin)
        self[self.mapping['~']].wire(vo)

class UsbConnB(PcbComponent):
    def __init__(self, vdd, dm, dp, gnd, shield):
        super(UsbConnB, self).__init__('Connectors', 'USB_B')
        self.mapping = PinMapping('conn', 'usb_b')
        self.prefix = 'J'
        self[self.mapping['VBUS']].wire(vdd)
        self[self.mapping['D-']].wire(dm)
        self[self.mapping['D+']].wire(dp)
        self[self.mapping['GND']].wire(gnd)
        self[self.mapping['Shield']].wire(shield)

class ATMEGA16U2(PcbComponent):
    def __init__(self):
        super(ATMEGA16U2, self).__init__('Housings_DFN_QFN', 'QFN-32-1EP_5x5mm_Pitch0.5mm')
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
    def __init__(self):
        super(ATMEGA328P, self).__init__('Housings_DIP', 'DIP-28_W7.62mm_Socket')
        self.prefix = 'U'
        self.mapping = PinMapping('atmel', 'ATMEGA328P-PU')

    def wire_xtal(self, xtal1, xtal2):
        self[self.mapping['(PCINT6/XTAL1/TOSC1)PB6']].wire(xtal1)
        self[self.mapping['(PCINT7/XTAL2/TOSC2)PB7']].wire(xtal2)

    def wire_power(self, vdd, gnd):
        self[self.mapping['AVCC']].wire(vdd)
        self[self.mapping['VCC']].wire(vdd)
        # TODO: properly handle pins with the same alias
        # right now this will leave either pin 8 or 22 disconnected
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
        super(RandomComponent, self).__init__(name, lib, part)
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
