# Steven Herbst
# sherbst@stanford.edu
#
# CS448H Winter 2017

# Library enables user to instantiate specific parts

import os
import random
import re
from mycad import PcbComponent


class MountingHole(PcbComponent):
    def __init__(self, net=None, **kwargs):
        super(
            MountingHole,
            self).__init__(
            'Mounting_Holes',
            'MountingHole_125mil',
            **kwargs)
        self.prefix = 'H'
        if net is not None:
            self['1'].wire(net)


class Resistor(PcbComponent):
    def __init__(self, p, n, size='PTH', **kwargs):
        if size in ['0402', '0603', '0805', '1206', '1210']:
            super(
                Resistor,
                self).__init__(
                'Resistors_SMD',
                'R_' +
                size,
                **kwargs)
        elif size == 'PTH':
            super(
                Resistor,
                self).__init__(
                'Resistors_THT',
                'R_Axial_DIN0204_L3.6mm_D1.6mm_P7.62mm_Horizontal',
                **kwargs)

        self.prefix = 'R'
        self['1'].wire(p)
        self['2'].wire(n)


class Inductor(PcbComponent):
    def __init__(self, p, n, size='0805', **kwargs):
        super(Inductor, self).__init__('Inductors_SMD', 'L_' + size, **kwargs)
        self.prefix = 'L'
        self['1'].wire(p)
        self['2'].wire(n)


class Capacitor(PcbComponent):
    def __init__(self, p, n, value=100e-9, **kwargs):
        if value < 1e-9:
            mod = 'C_Disc_D3.8mm_W2.6mm_P2.50mm'
        elif value < 1e-6:
            mod = 'C_Disc_D3.8mm_W2.6mm_P2.50mm'
        else:
            mod = 'CP_Radial_D6.3mm_P2.50mm'
        super(Capacitor, self).__init__('Capacitors_THT', mod, **kwargs)
        self.prefix = 'C'
        self['1'].wire(p)
        self['2'].wire(n)


class PMOS(PcbComponent):
    def __init__(self, gate, drain, source, **kwargs):
        super(PMOS, self).__init__('TO_SOT_Packages_SMD', 'SOT-23', **kwargs)
        self.mapping = {'S': '2', 'D': '3', 'G': '1'}
        self.prefix = 'Q'
        self[self.mapping['G']].wire(gate)
        self[self.mapping['S']].wire(source)
        self[self.mapping['D']].wire(drain)


class LDO_3v3(PcbComponent):
    def __init__(self, vin, gnd, vout, on=None, **kwargs):
        super(
            LDO_3v3,
            self).__init__(
            'TO_SOT_Packages_SMD',
            'SOT-23-5',
            **kwargs)
        self.mapping = {
            'VOUT': '5',
            'ON/OFF': '3',
            'VIN': '1',
            'BYPASS': '4',
            'GND': '2'}
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
        super(
            LDO_5v0,
            self).__init__(
            'TO_SOT_Packages_THT',
            'TO-220_Horizontal',
            **kwargs)
        self.mapping = {'IN': '1', 'GND': '2', 'OUT': '3'}
        self.prefix = 'U'
        self.get_pin('IN').wire(vin)
        self.get_pin('GND').wire(gnd)
        self.get_pin('OUT').wire(vout)


class BarrelJack(PcbComponent):
    def __init__(self, vdd, gnd, **kwargs):
        super(BarrelJack, self).__init__('Connectors', 'BARREL_JACK', **kwargs)
        self.prefix = 'X'
        self['1'].wire(vdd)
        self['2'].wire(gnd)
        self['3'].wire(gnd)


class SPST(PcbComponent):
    def __init__(self, p, n, **kwargs):
        super(
            SPST,
            self).__init__(
            'Buttons_Switches_SMD',
            'SW_SPST_EVQP0',
            **kwargs)
        self.prefix = 'SW'
        self['1'].wire(p)
        self['2'].wire(n)


class LED(PcbComponent):
    def __init__(self, p, n, **kwargs):
        super(LED, self).__init__('LEDs', 'LED_D5.0mm', **kwargs)
        self.prefix = 'D'
        self['1'].wire(n)
        self['2'].wire(p)


class Diode(PcbComponent):
    def __init__(self, p, n, **kwargs):
        super(
            Diode,
            self).__init__(
            'Diodes_THT',
            'D_DO-41_SOD81_P7.62mm_Horizontal',
            **kwargs)
        self.prefix = 'D'
        self['1'].wire(n)
        self['2'].wire(p)


class Crystal(PcbComponent):
    def __init__(self, p, n, **kwargs):
        super(
            Crystal,
            self).__init__(
            'Crystals',
            'Crystal_HC49-U_Vertical',
            **kwargs)
        self.prefix = 'X'
        self['1'].wire(p)
        self['2'].wire(n)


class Varistor(PcbComponent):
    def __init__(self, p, n, size='0805', **kwargs):
        super(Varistor, self).__init__('Resistors_SMD', 'R_' + size, **kwargs)
        self.prefix = 'VR'
        self['1'].wire(p)
        self['2'].wire(n)


class PTC(PcbComponent):
    def __init__(self, p, n, **kwargs):
        super(
            PTC,
            self).__init__(
            'Resistors_SMD',
            'R_1812_HandSoldering',
            **kwargs)
        self.prefix = 'Z'
        self['1'].wire(p)
        self['2'].wire(n)


class ICSP(PcbComponent):
    def __init__(self, miso, sck, reset, vdd, mosi, gnd, **kwargs):
        super(
            ICSP,
            self).__init__(
            'Pin_Headers',
            'Pin_Header_Straight_2x03_Pitch2.54mm',
            **kwargs)
        self.prefix = 'ICSP'
        self['1'].wire(miso)
        self['3'].wire(sck)
        self['5'].wire(reset)
        self['2'].wire(vdd)
        self['4'].wire(mosi)
        self['6'].wire(gnd)


class Header2x2(PcbComponent):
    def __init__(self, pin1, pin2, pin3, pin4, **kwargs):
        super(
            Header2x2,
            self).__init__(
            'Pin_Headers',
            'Pin_Header_Straight_2x02_Pitch2.54mm',
            **kwargs)
        self.prefix = 'J'
        self['1'].wire(pin1)
        self['2'].wire(pin2)
        self['3'].wire(pin3)
        self['4'].wire(pin4)


class Header10x1(PcbComponent):
    def __init__(
            self,
            pin1,
            pin2,
            pin3,
            pin4,
            pin5,
            pin6,
            pin7,
            pin8,
            pin9,
            pin10,
            **kwargs):
        super(
            Header10x1,
            self).__init__(
            'Pin_Headers',
            'Pin_Header_Straight_1x10_Pitch2.54mm',
            **kwargs)
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
    def __init__(
            self,
            pin1,
            pin2,
            pin3,
            pin4,
            pin5,
            pin6,
            pin7,
            pin8,
            **kwargs):
        super(
            Header8x1,
            self).__init__(
            'Pin_Headers',
            'Pin_Header_Straight_1x08_Pitch2.54mm',
            **kwargs)
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
        super(
            Header6x1,
            self).__init__(
            'Pin_Headers',
            'Pin_Header_Straight_1x06_Pitch2.54mm',
            **kwargs)
        self.prefix = 'J'
        self['1'].wire(pin1)
        self['2'].wire(pin2)
        self['3'].wire(pin3)
        self['4'].wire(pin4)
        self['5'].wire(pin5)
        self['6'].wire(pin6)


class Header3x1(PcbComponent):
    def __init__(self, pin1, pin2, pin3, **kwargs):
        super(
            Header3x1,
            self).__init__(
            'Pin_Headers',
            'Pin_Header_Straight_1x03_Pitch2.54mm',
            **kwargs)
        self.prefix = 'J'
        self['1'].wire(pin1)
        self['2'].wire(pin2)
        self['3'].wire(pin3)


class DualOpAmp(PcbComponent):
    def __init__(self, **kwargs):
        super(
            DualOpAmp,
            self).__init__(
            'Housings_SSOP',
            'TSSOP-8_4.4x3mm_Pitch0.65mm',
            **kwargs)
        self.mapping = {'+': ['3', '5'], 'V+': '8',
                        '-': ['2', '6'], 'V-': '4', '~': ['1', '7']}
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
        self.mapping = {
            'VBUS': '1',
            'D-': '2',
            'D+': '3',
            'GND': '4',
            'Shield': '5'}
        self.prefix = 'J'
        self[self.mapping['VBUS']].wire(vdd)
        self[self.mapping['D-']].wire(dm)
        self[self.mapping['D+']].wire(dp)
        self[self.mapping['GND']].wire(gnd)
        self[self.mapping['Shield']].wire(shield)


class FTDI232(PcbComponent):
    def __init__(self, **kwargs):
        super(
            FTDI232,
            self).__init__(
            'Housings_SSOP',
            'SSOP-28_5.3x10.2mm_Pitch0.65mm',
            bufx=2,
            bufy=2,
            **kwargs)
        self.mapping = {
            'TXD': '1',
            'DTR': '2',
            'RTS': '3',
            'VCCIO': '4',
            'RXD': '5',
            'RI': '6',
            'GND': [
                '7',
                '18',
                '21'],
            'DCR': '9',
            'DCD': '10',
            'VCC': '20',
            'CTS': '11',
            'CBUS4': '12',
            'TXLED': '22',
            'CBUS2': '13',
            'RXLED': '23',
            'CBUS3': '14',
            'USBD+': '15',
            'AGND': '25',
            'USBD-': '16',
            'TEST': '26',
            '3V3OUT': '17',
            'OSCI': '27',
            'OSCO': '28',
            '~RESET~': '19'}
        self.prefix = 'U'

    def wire_power(self, vdd, gnd):
        self.get_pin('VCC').wire(vdd)
        self.get_pin('VCCIO').wire(vdd)
        self.get_pin('TEST').wire(gnd)
        self.get_pin('AGND').wire(gnd)
        for pin in self.mapping['GND']:
            self[pin].wire(gnd)

    def wire_usb(self, dp, dn):
        self.get_pin('USBD+').wire(dp)
        self.get_pin('USBD-').wire(dn)


class ATMEGA16U2(PcbComponent):
    def __init__(self, **kwargs):
        super(
            ATMEGA16U2,
            self).__init__(
            'Housings_DFN_QFN',
            'QFN-32-1EP_5x5mm_Pitch0.5mm',
            bufx=2,
            bufy=2,
            **kwargs)
        self.prefix = 'U'
        self.mapping = {
            '(OC.0B/INT0)PD0': '6',
            '(PCINT6)PB6': '20',
            'UCAP': '27',
            '(SCLK/PCINT1)PB1': '15',
            'GND': '3',
            'PC1(~RESET~/dW)': '24',
            'UVCC': '31',
            '(PCINT7/OC.0A/OC.1C)PB7': '21',
            '(PD0/MISO/PCINT3)PB3': '17',
            'XTAL1': '1',
            'UGND': '28',
            'AVCC': '32',
            '(PCINT5)PB5': '19',
            '(OC.1A/PCINT8)PC6': '23',
            '(PCINT11/AIN2)PC2': '5',
            '(PCINT10)PC4': '26',
            '(PDI/MOSI/PCINT2)PB2': '16',
            '(TXD1/INT3)PD3': '9',
            '(PCINT9/OC.1B)PC5': '25',
            'VCC': '4',
            '(~SS~/PCINT0)PB0': '14',
            '(RXD1/AIN1/INT2)PD2': '8',
            '(~CTS~/~HWB~/AIN6/T0/INT7)PD7': '13',
            'XTAL2': '2',
            '(XCK/AIN4/PCINT12)PD5': '11',
            '(T1/PCINT4)PB4': '18',
            'D-': '30',
            'D+': '29',
            '(INT5/AIN3)PD4': '10',
            '(AIN0/INT1)PD1': '7',
            '(INT4/ICP1/CLK0)PC7': '22',
            '(~RTS~/AIN5/INT6)PD6': '12'}

    def wire_xtal(self, xtal1, xtal2):
        self[self.mapping['XTAL1']].wire(xtal1)
        self[self.mapping['XTAL2']].wire(xtal2)

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
        p = re.compile('\\(.*\\)' + port_prefix + '(\d+)')
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
        super(
            ATMEGA328P,
            self).__init__(
            'Housings_DIP',
            'DIP-28_W7.62mm_Socket',
            bufx=1,
            bufy=1,
            **kwargs)
        self.prefix = 'U'
        self.mapping = {
            '(PCINT23/AIN1)PD7': '13',
            '(PCINT14/~RESET~)PC6': '1',
            '(PCINT1/OC1A)PB1': '15',
            '(PCINT10/ADC2)PC2': '25',
            'GND': [
                '8',
                '22'],
            '(PCINT18/INT0)PD2': '4',
            '(PCINT22/OC0A/AIN0)PD6': '12',
            'AREF': '21',
            'XTAL2': '10',
            '(PCINT11/ADC3)PC3': '26',
            '(PCINT21/OC0B/T1)PD5': '11',
            'AVCC': '20',
            'XTAL1': '9',
            '(PCINT16/RXD)PD0': '2',
            '(PCINT0/CLKO/ICP1)PB0': '14',
            '(PCINT19/OC2B/INT1)PD3': '5',
            '(PCINT5/SCK)PB5': '19',
            'VCC': '7',
            '(PCINT13/SCL/ADC5)PC5': '28',
            '(PCINT20/XCK/T0)PD4': '6',
            '(PCINT8/ADC0)PC0': '23',
            '(PCINT17/TXD)PD1': '3',
            '(PCINT12/SDA/ADC4)PC4': '27',
            '(PCINT2/OC1B/~SS~)PB2': '16',
            '(PCINT4/MISO)PB4': '18',
            '(PCINT9/ADC1)PC1': '24',
            '(PCINT3/OC2A/MOSI)PB3': '17'}

    def wire_xtal(self, xtal1, xtal2):
        self[self.mapping['XTAL1']].wire(xtal1)
        self[self.mapping['XTAL2']].wire(xtal2)

    def wire_power(self, vdd, gnd):
        self[self.mapping['AVCC']].wire(vdd)
        self[self.mapping['VCC']].wire(vdd)
        for pin_no in self.mapping['GND']:
            self[pin_no].wire(gnd)

    def port_gen(self, port_prefix):
        port = {}
        p = re.compile('\\(.*\\)' + port_prefix + '(\d+)')
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
