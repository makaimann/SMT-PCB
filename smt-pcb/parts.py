# Steven Herbst
# sherbst@stanford.edu
#
# CS448H Winter 2017

# Library enables user to instantiate specific parts

import math
import re
from mycad import PcbComponent


class MountingHole(PcbComponent):
    def __init__(self, net=None, **kwargs):
        lib = 'Mounting_Holes'
        mod = 'MountingHole_125mil'

        super(MountingHole, self).__init__(lib, mod, **kwargs)

        self.prefix = 'H'

        if net is not None:
            self['1'].wire(net)


class Resistor(PcbComponent):
    def __init__(self, p, n, value=1e3, **kwargs):
        lib = 'Resistors_THT'
        mod = 'R_Axial_DIN0204_L3.6mm_D1.6mm_P7.62mm_Horizontal'
        partno = self.get_partno(value)

        super(Resistor, self).__init__(lib, mod, partno, **kwargs)

        self.prefix = 'R'
        self['1'].wire(p)
        self['2'].wire(n)

    def get_partno(self, value, eps=1e-3):
        if value == 0:
            value_str = '0000'
        else:
            power = math.log(value)/math.log(10)
            power = math.floor(power+eps)
            mantissa = round(value / 10**(power-2))
            value_str = '%03d%01d' % (mantissa, power-2)
        
        return 'MBA02040C' + value_str + 'FCT00'


class Capacitor(PcbComponent):
    def __init__(self, p, n, value=100e-9, **kwargs):
        lib = 'Capacitors_THT'

        if value < 1e-9:
            mod = 'C_Disc_D3.8mm_W2.6mm_P2.50mm'
            partno = self.get_partno_small(value)
        elif value < 1e-6:
            mod = 'C_Disc_D3.8mm_W2.6mm_P2.50mm'
            partno = self.get_partno_medium(value)
        else:
            mod = 'CP_Radial_D6.3mm_P2.50mm'
            partno = self.get_partno_large(value)

        super(Capacitor, self).__init__(lib, mod, partno, **kwargs)

        self.prefix = 'C'

        self['1'].wire(p)
        self['2'].wire(n)

    def get_partno_small(self, value):
        power = math.log(value)/math.log(10)
        power = math.floor(power)
        mantissa = round(value / 10**(power-1))
        value_str = '%02d%01d' % (mantissa, power+11)
        
        return 'K' + value_str + 'J15C0GF5TL2'

    def get_partno_medium(self, value):
        power = math.log(value)/math.log(10)
        power = math.floor(power)
        mantissa = round(value / 10**(power-1))
        value_str = '%02d%01d' % (mantissa, power+11)

        return 'K' + value_str + 'K15X7RF5TL2'

    def get_partno_large(self, value):
        power = math.log(value)/math.log(10)
        power = math.floor(power)
        mantissa = round(value / 10**(power-1))
        value_str = '%02d%01d' % (mantissa, power+5)

        return 'ECE-A1EKA' + value_str

class LDO_5v0(PcbComponent):
    def __init__(self, vin, gnd, vout, **kwargs):
        lib = 'TO_SOT_Packages_THT'
        mod = 'TO-220_Horizontal'
        partno = 'L7805CV'

        super(LDO_5v0, self).__init__(lib, mod, partno, **kwargs)

        self.mapping = {'IN': '1', 'GND': '2', 'OUT': '3'}
        self.prefix = 'U'

        self.get_pin('IN').wire(vin)
        self.get_pin('GND').wire(gnd)
        self.get_pin('OUT').wire(vout)


class BarrelJack(PcbComponent):
    def __init__(self, vdd, gnd, **kwargs):
        lib = 'Connectors'
        mod = 'BARREL_JACK'
        partno = 'PJ-102AH'

        super(BarrelJack, self).__init__(lib, mod, partno, **kwargs)
        self.prefix = 'X'

        self['1'].wire(vdd)
        self['2'].wire(gnd)
        self['3'].wire(gnd)


class SPST(PcbComponent):
    def __init__(self, p, n, **kwargs):
        lib = 'Buttons_Switches_SMD'
        mod = 'SW_SPST_EVQP0'
        partno = 'EVQ-P0P02B'

        super(SPST, self).__init__(lib, mod, partno, **kwargs)
        self.prefix = 'SW'

        self['1'].wire(p)
        self['2'].wire(n)


class LED(PcbComponent):
    def __init__(self, p, n, color='red', **kwargs):
        lib = 'LEDs'
        mod = 'LED_D5.0mm'

        partno = self.get_partno(color)

        super(LED, self).__init__(lib, mod, partno, **kwargs)
        self.prefix = 'D'

        self['1'].wire(n)
        self['2'].wire(p)

    def get_partno(self, color):
        if color.lower() in ['r', 'red']:
            value_str = 'R'
        elif color.lower() in ['g', 'green']:
            value_str = 'G'
        elif color.lower() in ['y', 'yellow']:
            value_str = 'Y'
        else:
            raise Exception('LED color not supported.')

        return 'LTL2R3K' + value_str + 'D-EM'


class Diode(PcbComponent):
    def __init__(self, p, n, **kwargs):
        lib = 'Diodes_THT'
        mod = 'D_DO-41_SOD81_P7.62mm_Horizontal'
        partno = '1N4001-TP'

        super(Diode, self).__init__(lib, mod, partno, **kwargs)
        self.prefix = 'D'

        self['1'].wire(n)
        self['2'].wire(p)


class Crystal(PcbComponent):
    def __init__(self, p, n, **kwargs):
        lib = 'Crystals'
        mod = 'Crystal_HC49-U_Vertical'
        partno = 'ECS-160-20-4X'

        super(Crystal, self).__init__(lib, mod, partno, **kwargs)

        self.prefix = 'X'
        self['1'].wire(p)
        self['2'].wire(n)


class PTC(PcbComponent):
    def __init__(self, p, n, **kwargs):
        # define component footprint
        lib = 'Resistors_SMD'
        mod = 'R_1812_HandSoldering'
        partno = 'MF-MSMF050-2'

        super(PTC, self).__init__(lib, mod, partno, **kwargs)

        self.prefix = 'Z'
        self['1'].wire(p)
        self['2'].wire(n)


class ICSP(PcbComponent):
    def __init__(self, miso, sck, reset, vdd, mosi, gnd, **kwargs):
        # define component footprint
        lib = 'Pin_Headers'
        mod = 'Pin_Header_Straight_2x03_Pitch2.54mm'
        partno = '67996-406HLF'

        super(ICSP, self).__init__(lib, mod, partno, **kwargs)
        self.prefix = 'ICSP'

        # define the standard ICSP pinout
        # http://www.avrfreaks.net/sites/default/files/icsp_6pin.png
        self['1'].wire(miso)
        self['3'].wire(sck)
        self['5'].wire(reset)
        self['2'].wire(vdd)
        self['4'].wire(mosi)
        self['6'].wire(gnd)


class Header(PcbComponent):
    def __init__(self, *args, **kwargs):
        # set defaults
        if 'rows' not in kwargs:
            kwargs['rows'] = 1
        if 'cols' not in kwargs:
            if len(args) % kwargs['rows'] == 0:
                kwargs['cols'] = len(args) / kwargs['rows']
            else:
                raise Exception('Cannot automatically detect header size.')

        # assemble the component name
        config = '%dx%02d' % (kwargs['rows'], kwargs['cols'])
        pitch = '2.54mm'
        lib = 'Pin_Headers'
        mod = 'Pin_Header_Straight_' + config + '_Pitch' + pitch

        # determine part number table based on header type
        partno = self.get_partno(type=kwargs['type'], 
                                 rows=kwargs['rows'], 
                                 cols=kwargs['cols'])

        super(Header, self).__init__(lib, mod, partno, **kwargs)
        self.prefix = 'J'

        for idx, net in enumerate(args):
            self[str(idx + 1)].wire(net)

    def get_partno(self, type, rows, cols):
        if type.lower() in ['m', 'male']:
            if rows == 1:
                value_str = '%02d' % cols
                return '6130' + value_str + '11121'
            else:
                raise Exception('Unsupported number of header rows.')
        elif type.lower() in ['f', 'female']:
            number_pos = rows*cols
            value_str = '%02d%01d' % (number_pos, rows)
            return 'PPTC' + value_str + 'LFBN-RC'
        else:
            raise Exception('Unsupported header type.')

class UsbConnB(PcbComponent):
    def __init__(self, vdd, dm, dp, gnd, shield, **kwargs):
        lib = 'Connectors'
        mod = 'USB_B'
        partno = 'USB-B1HSW6'

        super(UsbConnB, self).__init__(lib, mod, partno, **kwargs)

        self.init_mapping()
        self.prefix = 'J'

        self.get_pin('VBUS').wire(vdd)
        self.get_pin('D-').wire(dm)
        self.get_pin('D+').wire(dp)
        self.get_pin('GND').wire(gnd)
        self.get_pin('Shield').wire(shield)

    def init_mapping(self):
        self.mapping = {
            'VBUS': '1',
            'D-': '2',
            'D+': '3',
            'GND': '4',
            'Shield': '5'}


class FTDI232(PcbComponent):
    def __init__(self, **kwargs):
        # define defaults
        if 'bufx' not in kwargs:
            kwargs['bufx'] = 2
        if 'bufy' not in kwargs:
            kwargs['bufy'] = 2

        lib = 'Housings_SSOP'
        mod = 'SSOP-28_5.3x10.2mm_Pitch0.65mm'
        partno = 'FT232RL-REEL'

        super(FTDI232, self).__init__(lib, mod, partno, **kwargs)

        self.init_mapping()
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

    def init_mapping(self):
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


class ATMEGA328P(PcbComponent):
    def __init__(self, **kwargs):
        # define defaults
        if 'bufx' not in kwargs:
            kwargs['bufx'] = 1
        if 'bufy' not in kwargs:
            kwargs['bufy'] = 1

        lib = 'Housings_DIP'
        mod = 'DIP-28_W7.62mm_Socket'
        partno = ['ED281DT', 'Arduino A000048']
        super(ATMEGA328P, self).__init__(lib, mod, partno, **kwargs)

        self.init_mapping()
        self.prefix = 'U'

    def wire_xtal(self, xtal1, xtal2):
        self.get_pin('XTAL1').wire(xtal1)
        self.get_pin('XTAL2').wire(xtal2)

    def wire_power(self, vdd, gnd):
        self.get_pin('AVCC').wire(vdd)
        self.get_pin('VCC').wire(vdd)
        for pin_no in self.mapping['GND']:
            self[pin_no].wire(gnd)

    def port_gen(self, port_prefix):
        port = {}
        p = re.compile(port_prefix + '(\d+)')
        for alias, pin_number in self.mapping.items():
            m = p.match(alias)
            if m is not None:
                port_index = int(m.group(1))
                port[port_index] = self[pin_number]
        return port

    @property
    def PB(self):
        return self.port_gen('PB')

    @property
    def PC(self):
        return self.port_gen('PC')

    @property
    def PD(self):
        return self.port_gen('PD')

    def init_mapping(self):
        self.mapping = {
            'PD7': '13',
            '~RESET~': '1',
            'PB1': '15',
            'PC2': '25',
            'GND': [
                '8',
                '22'],
            'PD2': '4',
            'PD6': '12',
            'AREF': '21',
            'XTAL2': '10',
            'PC3': '26',
            'PD5': '11',
            'AVCC': '20',
            'XTAL1': '9',
            'PD0': '2',
            'PB0': '14',
            'PD3': '5',
            'PB5': '19',
            'VCC': '7',
            'PC5': '28',
            'PD4': '6',
            'PC0': '23',
            'PD1': '3',
            'PC4': '27',
            'PB2': '16',
            'PB4': '18',
            'PC1': '24',
            'PB3': '17'}
