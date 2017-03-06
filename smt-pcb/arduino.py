#!/usr/bin/env python

# Steven Herbst
# sherbst@stanford.edu
#
# CS448H Winter 2017

# Demo code to generate Arduino Uno Rev3

# SMT-PCB specific imports
from kicad.units import mil_to_mm
from kicad.point import Point
from mycad import PcbDesign, NetClass, PcbVia, PcbKeepout
from parts import *
from math import pi
import sys

def main():
    # read command-line arguments
    dict_fname = sys.argv[1]
    pcb_fname = sys.argv[2]

    # build Arduino design
    uno = ArduinoUno(dict_fname, pcb_fname)
    uno.compile()

class ArduinoUno:
    
    def __init__(self, dict_fname, pcb_fname):
        self.dict_fname = dict_fname
        self.pcb_fname = pcb_fname
        self.pcb = PcbDesign(pcb_fname, width=mil_to_mm(2700), height=mil_to_mm(2100), dx=1, dy=1)
        self.top = 2100
 
    def compile(self):   

        # USB connector and associated protection circuitry    
        print 'Instantiating USB'
        self.inst_usb()

        # ATMEGA16U2, handles USB communication
        print 'Instantiating ATMEGA16U2'
        self.inst_atmega16u2()

        # Reset capacitor between ATMEGA16 and ATMEGA328P
        self.pcb.add(Capacitor('DTR', 'RESET', size='0603'))

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
 
        # Op amp control circuit
        print 'Instantiating op amps'
        self.inst_op_amps()
        
        # Power input and LDOs
        print 'Instantiating LDOs'
        self.inst_ldos()
 
        # Set up net classes
        print 'Building net classes'
        power_class = NetClass('Power', trace_width=1.0)
        power_class.add('PWRIN')
        self.pcb.add_net_class(power_class)

        # Define the mounting holes
        self.inst_mounting_holes()

        # Define the board edge
        print 'Defining the board edge'
        self.define_edge()

        # put the parts on the board and save
        print 'Compiling PCB'
        critical_nets = ['D+','D-']
        self.pcb.compile(critical_nets=critical_nets, smt_file_in=self.dict_fname)

    def inst_usb(self):
        # USB B connector
        self.pcb.add(UsbConnB(vdd='XUSB', dm='D-', dp='D+', gnd='UGND', shield='USHIELD', 
                     position=Point(-250, self.top-1725, 'mils'), rotation=pi, mode='UL'))
    
        # EMC components
        self.pcb.add(Varistor('D-', 'USHIELD', size='0603'))
        self.pcb.add(Varistor('D+', 'USHIELD', size='0603'))
        self.pcb.add(Inductor('USHIELD', 'UGND', size='0805'))
    
        # Polyfuse to protect computer from shorts on the Arduino board
        self.pcb.add(PTC('XUSB', 'USBVCC', size='1812'))
    
        # Series termination resistors
        self.pcb.add(Resistor('D-', 'RD-'))
        self.pcb.add(Resistor('D+', 'RD+'))
    
        # Short together UGND and GND nets
        self.pcb.add(Resistor('UGND', 'GND'))
    
    def inst_atmega16u2(self):
        # Microcontroller to handle USB communication
        atmega16 = ATMEGA16U2()
        self.pcb.add(atmega16)
    
        # Connector power the microcontroller
        atmega16.wire_power(vdd='+5V', gnd='GND')
        self.pcb.add(Capacitor('+5V', 'GND', size='0603'))
    
        # Connect USB interface to the microcontroller
        atmega16.wire_usb(vdd='USBVCC', dm='RD-', dp='RD+', gnd='UGND')
        atmega16.ucap.wire('TP_VUCAP')
        self.pcb.add(Capacitor('TP_VUCAP', 'UGND', size='0603'))
    
        # Connect 16MHz Crystal
        atmega16.wire_xtal('XT1', 'XT2')
        self.pcb.add(Crystal('XT1', 'XT2'))
        self.pcb.add(Resistor('XT1', 'XT2', size='0603'))
        self.pcb.add(Capacitor('XT1', 'GND', size='0603'))
        self.pcb.add(Capacitor('XT2', 'GND', size='0603'))
    
        # Reset circuit    
        self.pcb.add(Resistor('RESET2', '+5V'))
        self.pcb.add(Diode('RESET2', '+5V', package='1206'))
        atmega16.reset.wire('RESET2')
    
        # USB boot enable
        self.pcb.add(Resistor('DTR', 'GND'))
    
        # UART LEDs
        self.pcb.add(Resistor('+5V', 'TXLED_R'))
        self.pcb.add(Resistor('+5V', 'RXLED_R'))
        self.pcb.add(LED('TXLED_R', 'TXLED'))
        self.pcb.add(LED('RXLED_R', 'RXLED'))
    
        # ICSP connector
        self.pcb.add(ICSP(miso='MISO2', sck='SCK2', reset='RESET2', vdd='+5V', mosi='MOSI2', gnd='GND'))
    
        # Debug header
        self.pcb.add(Header2x2('PB4', 'PB6', 'PB5', 'PB7'))
     
        # Wire port B  
        pb = atmega16.PB
        pb[7].wire('PB7')
        pb[6].wire('PB6')
        pb[5].wire('PB5')
        pb[4].wire('PB4')
        pb[3].wire('MISO2')
        pb[2].wire('MOSI2')
        pb[1].wire('SCK2')
    
        # Wire port D
        pd = atmega16.PD
        pd[7].wire('DTR')
        pd[5].wire('TXLED')
        pd[4].wire('RXLED')
        pd[3].wire('M8RXD')
        pd[2].wire('M8TXD')
    
    def inst_atmega328p(self):
        # Main microcontroller
        atmega328 = ATMEGA328P()
        self.pcb.add(atmega328)
    
        # Power connections
        atmega328.wire_power(vdd='+5V', gnd='GND')
        self.pcb.add(Capacitor('+5V', 'GND', size='0603'))
        
        # Analog reference
        atmega328.aref.wire('AREF')
        self.pcb.add(Capacitor('AREF', 'GND', size='0603'))
    
        # Crystal circuit
        # Note: this differs from the official schematic,
        # which uses a non-standard footprint
        atmega328.wire_xtal('XTAL1', 'XTAL2')
        self.pcb.add(Crystal('XTAL1', 'XTAL2'))
        self.pcb.add(Resistor('XTAL1', 'XTAL2', size='0603'))
        self.pcb.add(Capacitor('XTAL1', 'GND', size='0603'))
        self.pcb.add(Capacitor('XTAL2', 'GND', size='0603'))
    
        # Reset circuit
        atmega328.reset.wire('RESET')
        self.pcb.add(Diode('RESET', '+5V', package='1206'))
        self.pcb.add(Resistor('RESET', '+5V'))
    
        # Reset button 
        self.pcb.add(SPST('RESET', 'GND'))
    
        # ICSP connector
        self.pcb.add(ICSP(miso='MISO', sck='SCK', reset='RESET', vdd='+5V', mosi='MOSI', gnd='GND',
                     position=Point(2505.512, self.top-1198.031, 'mils'), mode='PIN1'))
   
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
    
    def inst_op_amps(self):
        # Dual op amp for control
        dual_op_amp = DualOpAmp()
        self.pcb.add(dual_op_amp)
    
        # Power connections
        dual_op_amp.wire_power('+5V', 'GND')
        self.pcb.add(Capacitor('+5V', 'GND', size='0603'))
    
        # 0.5x resistor divider on VIN
        self.pcb.add(Resistor('VIN', 'CMP'))
        self.pcb.add(Resistor('CMP', 'GND'))
    
        # Comparator 1:
        # If VIN<6.6, connect USBVCC to +5V
        # Else disconnect USBVCC from +5V
        dual_op_amp.wire('CMP', '+3V3', 'GATE_CMD', sub='A')
    
        # Comparator 2:
        # Drive LED with buffered version of SCK
        dual_op_amp.wire('SCK', 'L13', 'L13', sub='B')
        self.pcb.add(Resistor('L13', 'L13_R'))
        self.pcb.add(LED('L13_R', 'GND'))
    
    def inst_ldos(self):
        # Barrel jack for 7-12V supply
        self.pcb.add(BarrelJack('PWRIN', 'GND', position=Point(-75, self.top-475, 'mils'), mode='UL'))
        self.pcb.add(Diode('PWRIN', 'VIN', package='SMB'))
        self.pcb.add(Capacitor('VIN', 'GND', ctype='CP_Elec', size='5x5.3'))
            
        # 5.0V LDO
        self.pcb.add(LDO_5v0(vin='VIN', gnd='GND', vout='+5V'))
        self.pcb.add(Capacitor('+5V', 'GND', ctype='CP_Elec', size='5x5.3'))
        self.pcb.add(Capacitor('+5V', 'GND', size='0603'))
    
        # 3.3V LDO
        self.pcb.add(PMOS(gate='GATE_CMD', source='+5V', drain='USBVCC'))
        self.pcb.add(LDO_3v3(vin='+5V', gnd='GND', vout='+3V3'))
        self.pcb.add(Capacitor('+3V3', 'GND', size='0603'))
    
    def inst_headers(self):
        # Digital 10-pin header 
        self.pcb.add(Header10x1('IO8', 'IO9', 'SS', 'MOSI', 'MISO', 'SCK', 'GND', 'AREF', 'AD4/SDA', 'AD5/SCL',
                     position=Point(740, self.top-2000, 'mils'), rotation=pi/2.0, mode='PIN1'))
    
        # Digital 8-pin header
        self.pcb.add(Header8x1('IO0', 'IO1', 'IO2', 'IO3', 'IO4', 'IO5', 'IO6', 'IO7',
                     position=Point(1800, self.top-2000, 'mils'), rotation=pi/2.0, mode='PIN1'))
    
        # Analog 6-pin header
        self.pcb.add(Header6x1('AD0', 'AD1', 'AD2', 'AD3', 'AD4/SDA', 'AD5/SCL',
                     position=Point(2000, self.top-100, 'mils'), rotation=pi/2.0, mode='PIN1'))
    
        # Power header
        self.pcb.add(Header8x1(None, '+5V', 'RESET', '+3V3', '+5V', 'GND', 'GND', 'VIN',
                     position=Point(1100, self.top-100, 'mils'), rotation=pi/2.0, mode='PIN1'))

    def inst_mounting_holes(self):
        # drill = mil_to_mm(125)
        # size = drill+mil_to_mm(8)
        # self.pcb.add(PcbVia(position=Point(600, self.top-2000, 'mils'), size=size, drill=drill))
        # self.pcb.add(PcbVia(position=Point(550, self.top-100, 'mils'), size=size, drill=drill))
        # self.pcb.add(PcbVia(position=Point(2600, self.top-1400, 'mils'), size=size, drill=drill))
        # self.pcb.add(PcbVia(position=Point(2600, self.top-300, 'mils'), size=size, drill=drill))
        pass
    
    def define_edge(self):
        # create list of points representing the board edge
        points = [(0, 0), (0, 2100), (2540, 2100), (2600, 2040), (2600, 1590), 
                  (2700, 1490), (2700, 200), (2600, 100), (2600, 0), (0, 0)]
        points = [Point(x, self.top-y, 'mils') for x,y in points]
        self.pcb.edge = points

        # block off the parts of the board that aren't allowed
        self.pcb.add(PcbKeepout(width=mil_to_mm(2700-2600), height=mil_to_mm(2100-1490),
                     position=Point(2600, self.top-2100, 'mils')))
        self.pcb.add(PcbKeepout(width=mil_to_mm(2700-2600), height=mil_to_mm(200-0),
                     position=Point(2600, self.top-200, 'mils')))

if __name__=='__main__':
    main()
