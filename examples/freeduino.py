#!/usr/bin/env python2

# Steven Herbst
# sherbst@stanford.edu
#
# CS448H Winter 2017

# Demo code to generate Freeduino

# general imports
from math import pi
import argparse

# SMT-PCB specific imports
from kicad.point import Point
from mycad import NetClass
from mycad import PcbDesign
from parts import *


def main():
    # load command-line arguments
    parser = argparse.ArgumentParser()
    parser.add_argument('--json')
    parser.add_argument('--pcb')
    args = parser.parse_args()

    # build Freeduino design
    uno = Freeduino(args.json, args.pcb)
    uno.compile()


class Freeduino:

    def __init__(self, json_fname, pcb_fname):
        # Files used for I/O
        self.json_fname = json_fname
        self.pcb_fname = pcb_fname

        # Convenience variable, stores the top of the board in mils
        # using the coordinate system of the mechanical drawing
        # Reference: http://bit.ly/2mfbALQ
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

        # Reset capacitor between FT232RL and ATMEGA328P
        print 'Instantiating reset capacitor'
        self.pcb.add(Capacitor('DTR', 'RESET'))

        # UART resistors between FT232RL and ATMEGA328P
        print 'Wiring UART interface'
        self.pcb.add(Resistor('M8RXD', 'IO0', value=1e3))
        self.pcb.add(Resistor('M8TXD', 'IO1', value=1e3))

        # ATMEGA328P, main microcontroller
        print 'Instantiating ATMEGA328P'
        self.inst_atmega328p()

        # Headers for power, analog, digital
        print 'Instantiating headers'
        self.inst_headers()

        # Power LED
        print 'Instantiating power LED'
        self.pcb.add(Resistor('+5V', 'PWR_LED', value=330))
        self.pcb.add(LED('PWR_LED', 'GND', color='red'))

        # Power input and LDO
        print 'Instantiating LDO'
        self.inst_ldo()

        # IO13 LED
        print 'Instantiating IO13 LED'
        self.pcb.add(Resistor('IO13', 'IO13_R', value=1e3))
        self.pcb.add(LED('IO13_R', 'GND', color='yellow'))

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
        self.pcb.compile(json_file=self.json_fname)

    def inst_usb(self):
        # USB B connector
        usb_pos = Point(-250, self.top - 1725, 'mils')
        usb = UsbConnB(vdd='XUSB',
                       dm='D-',
                       dp='D+',
                       gnd='GND',
                       shield='GND',
                       position=usb_pos,
                       rotation=pi,
                       mode='UL')
        self.pcb.add(usb)

        # Polyfuse to protect computer from shorts on the Freeduino board
        self.pcb.add(PTC('XUSB', 'USBVCC'))

        # USB bypass cap
        self.pcb.add(Capacitor('USBVCC', 'GND'))

        # Power header
        self.pcb.add(Header('USBVCC', '+5V', 'VCC', type='male'))

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
        self.pcb.add(Resistor('TXLED', 'TXLED_R', value=1e3))
        self.pcb.add(Resistor('RXLED', 'RXLED_R', value=1e3))
        self.pcb.add(LED('+5V', 'TXLED_R', color='red'))
        self.pcb.add(LED('+5V', 'RXLED_R', color='red'))

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
        atmega328.get_pin('AREF').wire('AREF')
        self.add_dcap(atmega328.get_pin('AREF'))

        # Crystal circuit
        atmega328.wire_xtal('XTAL1', 'XTAL2')
        self.pcb.add(Crystal('XTAL1', 'XTAL2'))
        self.pcb.add(Capacitor('XTAL1', 'GND', value=22e-12))
        self.pcb.add(Capacitor('XTAL2', 'GND', value=22e-12))

        # Crystal routing constraints
        self.pcb.add_net_constr('XTAL1', length=4)
        self.pcb.add_net_constr('XTAL2', length=4)

        # Reset circuit
        atmega328.get_pin('~RESET~').wire('RESET')
        self.pcb.add(Resistor('RESET', '+5V', value=10e3))

        # Reset button
        self.pcb.add(SPST('RESET', 'GND'))

        # ICSP connector
        icsp_pos = Point(2505.512, self.top - 1198.031, 'mils')
        self.pcb.add(
            ICSP(
                sck='IO13',
                miso='IO12',
                mosi='IO11',
                reset='RESET',
                vdd='+5V',
                gnd='GND',
                position=icsp_pos,
                mode='PIN1'))

        # Wire Port B
        pb = atmega328.PB
        for idx in range(6):
            pb[idx].wire('IO' + str(idx + 8))

        # Wire Port C
        pc = atmega328.PC
        for idx in range(6):
            pc[idx].wire('AD' + str(idx))

        # Wire Port D
        pd = atmega328.PD
        for idx in range(8):
            pd[idx].wire('IO' + str(idx))

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
        header_pos = Point(1640, self.top - 2000, 'mils')
        header_rot = 3.0 * pi / 2.0
        self.pcb.add(
            Header(
                'IO8',
                'IO9',
                'IO10',
                'IO11',
                'IO12',
                'IO13',
                'GND',
                'AREF',
                'AD4',
                'AD5',
                type = 'female',
                position=header_pos,
                rotation=header_rot,
                mode='PIN1'))

        # Digital 8-pin header
        header_pos = Point(2500, self.top - 2000, 'mils')
        header_rot = 3.0 * pi / 2.0
        self.pcb.add(
            Header(
                'IO0',
                'IO1',
                'IO2',
                'IO3',
                'IO4',
                'IO5',
                'IO6',
                'IO7',
                type = 'female',
                position=header_pos,
                rotation=header_rot,
                mode='PIN1'))

        # Analog 6-pin header
        header_pos = Point(2000, self.top - 100, 'mils')
        header_rot = pi / 2.0
        self.pcb.add(
            Header(
                'AD0',
                'AD1',
                'AD2',
                'AD3',
                'AD4',
                'AD5',
                type = 'female',
                position=header_pos,
                rotation=header_rot,
                mode='PIN1'))

        # Power header
        header_pos = Point(1100, self.top - 100, 'mils')
        header_rot = pi / 2.0
        self.pcb.add(
            Header(
                None,
                '+5V',
                'RESET',
                '+3V3',
                '+5V',
                'GND',
                'GND',
                'VIN',
                type = 'female',
                position=header_pos,
                rotation=header_rot,
                mode='PIN1'))

    def inst_mounting_holes(self):
        coords = [(600, 2000), (550, 100), (2600, 1400), (2600, 300)]
        for coord in coords:
            hole_pos = Point(coord[0], self.top - coord[1], 'mils')
            hole = MountingHole(position=hole_pos, mode='CENTER')
            self.pcb.add(hole)

    def define_edge(self):
        # create list of points representing the board edge
        points = [(0, 0), (0, 2100), (2540, 2100), (2600, 2040), (2600, 1590),
                  (2700, 1490), (2700, 200), (2600, 100), (2600, 0), (0, 0)]
        points = [Point(x, self.top - y, 'mils') for x, y in points]
        self.pcb.edge = points

    def add_dcap(self, pin, gnd=None, value=100e-9, length=4):
        if gnd is None:
            gnd = 'GND'
        cap = Capacitor(pin.net_name, gnd, value=value)
        self.pcb.add(cap)
        self.pcb.add_pad_constr(pin, cap['1'], length=length)


if __name__ == '__main__':
    main()
