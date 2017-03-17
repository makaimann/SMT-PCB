#!/usr/bin/env python

# Steven Herbst
# sherbst@stanford.edu
#
# CS448H Winter 2017

# Demo code to generate Freeduino

# SMT-PCB specific imports
from kicad.units import mil_to_mm
from kicad.point import Point
from mycad import NetClass
from mycad import PcbDesign
from mycad import PcbKeepout
from parts import *
from math import pi
import sys


def main():
    # read command-line arguments
    json_fname = sys.argv[1]
    pcb_fname = sys.argv[2]

    # build Freeduino design
    uno = Freeduino(json_fname, pcb_fname)
    uno.compile()


class Freeduino:

    def __init__(self, json_fname, pcb_fname):
        # Files used for I/O
        self.json_fname = json_fname
        self.pcb_fname = pcb_fname

        # Convenience variable, stores the top of the board in mils
        # using the coordinate system of the mechanical drawing
        self.top = 2100

        # Create PCB
        self.pcb = PcbDesign(pcb_fname, dx=0.1, dy=0.1)
        self.pcb.title = 'SMT-PCB Freeduino'
        self.pcb.comments = ['Authors:',
                             'Steven Herbst <sherbst@stanford.edu>',
                             'Makai Mann <makaim@stanford.edu>']
        self.pcb.company = 'Stanford University'
        self.pcb.revision = '1'

    def compile(self):

        # USB connector and associated protection circuitry
        print 'Instantiating USB'
        self.inst_usb()

        # FTDI, handles USB communication
        print 'Instantiating FTDI232'
        self.inst_ftdi()

        # Reset capacitor between ATMEGA16 and ATMEGA328P
        self.pcb.add(Capacitor('DTR', 'RESET'))

        # UART resistors between ATMEGA16 and ATMEGA328P
        self.pcb.add(Resistor('M8RXD', 'IO0'))
        self.pcb.add(Resistor('M8TXD', 'IO1'))

        # ATMEGA328P, main microcontroller
        print 'Instantiating ATMEGA328P'
        self.inst_atmega328p()

        # Headers for power, analog, digital
        self.inst_headers()

        # Power LED
        self.pcb.add(Resistor('+5V', 'PWR_LED'))
        self.pcb.add(Resistor('+5V', 'PWR_LED'))
        self.pcb.add(LED('PWR_LED', 'GND'))

        # Power input and LDO
        print 'Instantiating LDO'
        self.inst_ldo()

        # IO13 LED
        self.pcb.add(Resistor('SCK', 'SCK_R'))
        self.pcb.add(LED('SCK_R', 'GND'))

        # Set up net classes
        print 'Building net classes'
        power_class = NetClass('Power', trace_width=1.0)
        power_class.add('PWRIN', 'USBVCC', 'VCC', 'XUSB', 'VIN')
        self.pcb.add_net_class(power_class)

        # Create mounting holes
        print 'Creating mounting holes'
        self.inst_mounting_holes()

        # Define the board edge
        print 'Defining the board edge'
        self.define_edge()

        # put the parts on the board and save
        print 'Compiling PCB'
        self.pcb.compile(smt_file_in=self.json_fname)

    def inst_usb(self):
        # USB B connector
        usb = UsbConnB(vdd='XUSB',
                       dm='D-',
                       dp='D+',
                       gnd='GND',
                       shield='GND',
                       position=Point(-250,
                                      self.top - 1725,
                                      'mils'),
                       rotation=pi,
                       mode='UL')
        self.pcb.add(usb)

        # Polyfuse to protect computer from shorts on the Freeduino board
        self.pcb.add(PTC('XUSB', 'USBVCC'))

        # USB bypass cap
        self.pcb.add(Capacitor('USBVCC', 'GND'))

        # Power header
        self.pcb.add(Header3x1('USBVCC', '+5V', 'VCC'))

    def inst_ftdi(self):
        # USB-serial bridge
        ftdi232 = FTDI232()
        self.pcb.add(ftdi232)

        # Power connections
        ftdi232.wire_power(vdd='+5V', gnd='GND')
        self.add_dcap(ftdi232.get_pin('VCC'))
        self.add_dcap(ftdi232.get_pin('VCCIO'))

        # 3V3 LDO
        ftdi232.get_pin('3V3OUT').wire('+3V3')
        self.add_dcap(ftdi232.get_pin('3V3OUT'))

        # Wire UART
        ftdi232.get_pin('TXD').wire('M8RXD')
        ftdi232.get_pin('RXD').wire('M8TXD')

        # Wire UART LEDs
        ftdi232.get_pin('TXLED').wire('TXLED')
        ftdi232.get_pin('RXLED').wire('RXLED')
        self.pcb.add(Resistor('TXLED', 'TXLED_R'))
        self.pcb.add(Resistor('RXLED', 'RXLED_R'))
        self.pcb.add(LED('+5V', 'TXLED_R'))
        self.pcb.add(LED('+5V', 'RXLED_R'))

        # USB connection
        ftdi232.wire_usb(dp='D+', dn='D-')
        self.pcb.add_net_constr('D+', length=4)
        self.pcb.add_net_constr('D-', length=4)

        # DTR connection
        ftdi232.get_pin('DTR').wire('DTR')

        # Reset connection
        ftdi232.get_pin('~RESET~').wire('+5V')

    def inst_atmega328p(self):
        # Main microcontroller
        atmega328 = ATMEGA328P()
        self.pcb.add(atmega328)

        # Power connections
        atmega328.wire_power(vdd='+5V', gnd='GND')
        self.add_dcap(atmega328.get_pin('VCC'))
        self.add_dcap(atmega328.get_pin('AVCC'))

        # Analog reference
        atmega328.aref.wire('AREF')
        self.add_dcap(atmega328.aref)

        # Crystal circuit
        atmega328.wire_xtal('XTAL1', 'XTAL2')

        # create parts
        xtal = Crystal('XTAL1', 'XTAL2')
        xcap1 = Capacitor('XTAL1', 'GND', value=22e-12)
        xcap2 = Capacitor('XTAL2', 'GND', value=22e-12)

        # add to board
        self.pcb.add(xtal, xcap1, xcap2)

        # create routing constraints
        self.pcb.add_pad_constr(xtal['1'], xcap1['1'], length=4)
        self.pcb.add_pad_constr(xtal['2'], xcap2['1'], length=4)
        self.pcb.add_pad_constr(
            xtal['1'],
            atmega328.get_pin('XTAL1'),
            length=4)
        self.pcb.add_pad_constr(
            xtal['2'],
            atmega328.get_pin('XTAL2'),
            length=4)

        # Reset circuit
        atmega328.reset.wire('RESET')
        self.pcb.add(Resistor('RESET', '+5V'))

        # Reset button
        self.pcb.add(SPST('RESET', 'GND'))

        # ICSP connector
        self.pcb.add(
            ICSP(
                miso='MISO',
                sck='SCK',
                reset='RESET',
                vdd='+5V',
                mosi='MOSI',
                gnd='GND',
                position=Point(
                    2505.512,
                    self.top -
                    1198.031,
                    'mils'),
                mode='PIN1'))

        # Wire Port B
        pb = atmega328.PB
        pb[5].wire('SCK')
        pb[4].wire('MISO')
        pb[3].wire('MOSI')
        pb[2].wire('SS')
        pb[1].wire('IO9')
        pb[0].wire('IO8')

        # Wire Port C
        pc = atmega328.PC
        pc[5].wire('AD5/SCL')
        pc[4].wire('AD4/SDA')
        pc[3].wire('AD3')
        pc[2].wire('AD2')
        pc[1].wire('AD1')
        pc[0].wire('AD0')

        # Wire Port D
        pd = atmega328.PD
        pd[7].wire('IO7')
        pd[6].wire('IO6')
        pd[5].wire('IO5')
        pd[4].wire('IO4')
        pd[3].wire('IO3')
        pd[2].wire('IO2')
        pd[1].wire('IO1')
        pd[0].wire('IO0')

    def inst_ldo(self):
        # Barrel jack for 7-12V supply
        jack_pos = Point(-75, self.top - 475, 'mils')
        jack = BarrelJack('PWRIN', 'GND', position=jack_pos, mode='UL')
        diode = Diode('PWRIN', 'VIN')
        self.pcb.add(jack, diode)

        # 5.0V LDO
        ldo_5v0 = LDO_5v0(vin='VIN', gnd='GND', vout='VCC')
        self.pcb.add(ldo_5v0)
        self.add_dcap(ldo_5v0.get_pin('IN'))
        self.add_dcap(ldo_5v0.get_pin('IN'), value=47e-6)
        self.add_dcap(ldo_5v0.get_pin('OUT'))
        self.add_dcap(ldo_5v0.get_pin('OUT'), value=47e-6)

    def inst_headers(self):
        # Digital 10-pin header
        self.pcb.add(
            Header10x1(
                'IO8',
                'IO9',
                'SS',
                'MOSI',
                'MISO',
                'SCK',
                'GND',
                'AREF',
                'AD4/SDA',
                'AD5/SCL',
                position=Point(
                    1640,
                    self.top - 2000,
                    'mils'),
                rotation=3 * pi / 2.0,
                mode='PIN1'))

        # Digital 8-pin header
        self.pcb.add(
            Header8x1(
                'IO0',
                'IO1',
                'IO2',
                'IO3',
                'IO4',
                'IO5',
                'IO6',
                'IO7',
                position=Point(
                    2500,
                    self.top - 2000,
                    'mils'),
                rotation=3 * pi / 2.0,
                mode='PIN1'))

        # Analog 6-pin header
        self.pcb.add(
            Header6x1(
                'AD0',
                'AD1',
                'AD2',
                'AD3',
                'AD4/SDA',
                'AD5/SCL',
                position=Point(
                    2000,
                    self.top - 100,
                    'mils'),
                rotation=pi / 2.0,
                mode='PIN1'))

        # Power header
        self.pcb.add(
            Header8x1(
                None,
                '+5V',
                'RESET',
                '+3V3',
                '+5V',
                'GND',
                'GND',
                'VIN',
                position=Point(
                    1100,
                    self.top - 100,
                    'mils'),
                rotation=pi / 2.0,
                mode='PIN1'))

    def inst_mounting_holes(self):
        self.pcb.add(
            MountingHole(
                position=Point(
                    600,
                    self.top -
                    2000,
                    'mils'),
                mode='CENTER'))
        self.pcb.add(
            MountingHole(
                position=Point(
                    550,
                    self.top - 100,
                    'mils'),
                mode='CENTER'))
        self.pcb.add(
            MountingHole(
                position=Point(
                    2600,
                    self.top -
                    1400,
                    'mils'),
                mode='CENTER'))
        self.pcb.add(
            MountingHole(
                position=Point(
                    2600,
                    self.top - 300,
                    'mils'),
                mode='CENTER'))

    def define_edge(self):
        # create list of points representing the board edge
        points = [(0, 0), (0, 2100), (2540, 2100), (2600, 2040), (2600, 1590),
                  (2700, 1490), (2700, 200), (2600, 100), (2600, 0), (0, 0)]
        points = [Point(x, self.top - y, 'mils') for x, y in points]
        self.pcb.edge = points

        # TODO: automatically determine keepouts
        self.pcb.add(
            PcbKeepout(
                width=mil_to_mm(
                    2700 - 2540),
                height=mil_to_mm(
                    2100 - 1490),
                position=Point(
                    2540,
                    self.top - 2100,
                    'mils')))
        self.pcb.add(
            PcbKeepout(
                width=mil_to_mm(
                    2700 - 2600),
                height=mil_to_mm(
                    200 - 0),
                position=Point(
                    2600,
                    self.top - 200,
                    'mils')))

    def add_dcap(self, pin, gnd=None, value=100e-9, length=4):
        if gnd is None:
            gnd = 'GND'
        cap = Capacitor(pin.net_name, gnd, value=value)
        self.pcb.add(cap)
        self.pcb.add_pad_constr(pin, cap['1'], length=length)


if __name__ == '__main__':
    main()
