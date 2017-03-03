#!/usr/bin/env python

# Steven Herbst
# sherbst@stanford.edu
#
# CS448H Winter 2017

# Demo code to generate Arduino Uno Rev3

# SMT-PCB specific imports
from mycad import PcbDesign, NetClass
from parts import *
from math import pi
import sys

def main():
    # read command-line arguments
    dict_fname = sys.argv[1]
    pcb_fname = sys.argv[2]

    # Create object to hold PCB design
    pcb = PcbDesign(pcb_fname, width=68.6, height=53.3, dx=1, dy=1)

    # USB connector and associated protection circuitry    
    print 'Instantiating USB'
    inst_usb(pcb)

    # ATMEGA16U2, handles USB communication
    print 'Instantiating ATMEGA16U2'
    inst_atmega16u2(pcb)

    # Reset capacitor between ATMEGA16 and ATMEGA328P
    pcb.add(Capacitor('DTR', 'RESET', size='0603'))

    # UART resistors between ATMEGA16 and ATMEGA328P
    pcb.add(Resistor('M8RXD', 'IO0'))
    pcb.add(Resistor('M8TXD', 'IO1'))

    # ATMEGA328P, main microcontroller
    print 'Instantiating ATMEGA328P'
    inst_atmega328p(pcb)

    # Headers for power, analog, digital
    inst_headers(pcb)

    # Power LED
    pcb.add(Resistor('+5V', 'PWR_LED'))
    pcb.add(Resistor('+5V', 'PWR_LED'))
    pcb.add(LED('PWR_LED', 'GND'))
 
    # Op amp control circuit
    print 'Instantiating op amps'
    inst_op_amps(pcb)
    
    # Power input and LDOs
    print 'Instantiating LDOs'
    inst_ldos(pcb)
 
    # Set up net classes
    print 'Building net classes'
    power_class = NetClass('Power', trace_width=1.0)
    power_class.add('PWRIN')
    pcb.add_net_class(power_class)

    # put the parts on the board and save
    print 'Compiling PCB'
    pcb.compile(critical_nets=['D+','D-','RD+','RD-','XT1','XT2',
                'XTAL1','XTAL2'])

def inst_usb(pcb):
    # USB B connector
    pcb.add(UsbConnB(vdd='XUSB', dm='D-', dp='D+', gnd='UGND', shield='USHIELD', 
                     position=(-6, 10), rotation=pi))

    # EMC components
    pcb.add(Varistor('D-', 'USHIELD', size='0603'))
    pcb.add(Varistor('D+', 'USHIELD', size='0603'))
    pcb.add(Inductor('USHIELD', 'UGND', size='0805'))

    # Polyfuse to protect computer from shorts on the Arduino board
    pcb.add(PTC('XUSB', 'USBVCC', size='1812'))

    # Series termination resistors
    pcb.add(Resistor('D-', 'RD-'))
    pcb.add(Resistor('D+', 'RD+'))

    # Short together UGND and GND nets
    pcb.add(Resistor('UGND', 'GND'))

def inst_atmega16u2(pcb):
    # Microcontroller to handle USB communication
    atmega16 = ATMEGA16U2()
    pcb.add(atmega16)

    # Connector power the microcontroller
    atmega16.wire_power(vdd='+5V', gnd='GND')
    pcb.add(Capacitor('+5V', 'GND', size='0603'))

    # Connect USB interface to the microcontroller
    atmega16.wire_usb(vdd='USBVCC', dm='RD-', dp='RD+', gnd='UGND')
    atmega16.ucap.wire('TP_VUCAP')
    pcb.add(Capacitor('TP_VUCAP', 'UGND', size='0603'))

    # Connect 16MHz Crystal
    atmega16.wire_xtal('XT1', 'XT2')
    pcb.add(Crystal('XT1', 'XT2'))
    pcb.add(Resistor('XT1', 'XT2', size='0603'))
    pcb.add(Capacitor('XT1', 'GND', size='0603'))
    pcb.add(Capacitor('XT2', 'GND', size='0603'))

    # Reset circuit    
    pcb.add(Resistor('RESET2', '+5V'))
    pcb.add(Diode('RESET2', '+5V', package='1206'))
    atmega16.reset.wire('RESET2')

    # USB boot enable
    pcb.add(Resistor('DTR', 'GND'))

    # UART LEDs
    pcb.add(Resistor('+5V', 'TXLED_R'))
    pcb.add(Resistor('+5V', 'RXLED_R'))
    pcb.add(LED('TXLED_R', 'TXLED'))
    pcb.add(LED('RXLED_R', 'RXLED'))

    # ICSP connector
    pcb.add(ICSP(miso='MISO2', sck='SCK2', reset='RESET2', vdd='+5V', mosi='MOSI2', gnd='GND'))

    # Debug header
    pcb.add(Header2x2('PB4', 'PB6', 'PB5', 'PB7'))
 
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

def inst_atmega328p(pcb):
    # Main microcontroller
    atmega328 = ATMEGA328P()
    pcb.add(atmega328)

    # Power connections
    atmega328.wire_power(vdd='+5V', gnd='GND')
    pcb.add(Capacitor('+5V', 'GND', size='0603'))
    
    # Analog reference
    atmega328.aref.wire('AREF')
    pcb.add(Capacitor('AREF', 'GND', size='0603'))

    # Crystal circuit
    # Note: this differs from the official schematic,
    # which uses a non-standard footprint
    atmega328.wire_xtal('XTAL1', 'XTAL2')
    pcb.add(Crystal('XTAL1', 'XTAL2'))
    pcb.add(Resistor('XTAL1', 'XTAL2', size='0603'))
    pcb.add(Capacitor('XTAL1', 'GND', size='0603'))
    pcb.add(Capacitor('XTAL2', 'GND', size='0603'))

    # Reset circuit
    atmega328.reset.wire('RESET')
    pcb.add(Diode('RESET', '+5V', package='1206'))
    pcb.add(Resistor('RESET', '+5V'))

    # Reset button 
    pcb.add(SPST('RESET', 'GND', position=(3,2)))

    # ICSP connector
    pcb.add(ICSP(miso='MISO', sck='SCK', reset='RESET', vdd='+5V', mosi='MOSI', gnd='GND', position=(62,22)))

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

def inst_op_amps(pcb):
    # Dual op amp for control
    dual_op_amp = DualOpAmp()
    pcb.add(dual_op_amp)

    # Power connections
    dual_op_amp.wire_power('+5V', 'GND')
    pcb.add(Capacitor('+5V', 'GND', size='0603'))

    # 0.5x resistor divider on VIN
    pcb.add(Resistor('VIN', 'CMP'))
    pcb.add(Resistor('CMP', 'GND'))

    # Comparator 1:
    # If VIN<6.6, connect USBVCC to +5V
    # Else disconnect USBVCC from +5V
    dual_op_amp.wire('CMP', '+3V3', 'GATE_CMD', sub='A')

    # Comparator 2:
    # Drive LED with buffered version of SCK
    dual_op_amp.wire('SCK', 'L13', 'L13', sub='B')
    pcb.add(Resistor('L13', 'L13_R'))
    pcb.add(LED('L13_R', 'GND'))

def inst_ldos(pcb):
    # Barrel jack for 7-12V supply
    pcb.add(BarrelJack('PWRIN', 'GND', position=(-2,41)))
    pcb.add(Diode('PWRIN', 'VIN', package='SMB'))
    pcb.add(Capacitor('VIN', 'GND', ctype='CP_Elec', size='5x5.3'))
        
    # 5.0V LDO
    pcb.add(LDO_5v0(vin='VIN', gnd='GND', vout='+5V'))
    pcb.add(Capacitor('+5V', 'GND', ctype='CP_Elec', size='5x5.3'))
    pcb.add(Capacitor('+5V', 'GND', size='0603'))

    # 3.3V LDO
    pcb.add(PMOS(gate='GATE_CMD', source='+5V', drain='USBVCC'))
    pcb.add(LDO_3v3(vin='+5V', gnd='GND', vout='+3V3'))
    pcb.add(Capacitor('+3V3', 'GND', size='0603'))

def inst_headers(pcb):
    # Digital 10-pin header 
    pcb.add(Header10x1('IO8', 'IO9', 'SS', 'MOSI', 'MISO', 'SCK', 'GND', 'AREF', 'AD4/SDA', 'AD5/SCL',
                       position=(17,1), rotation=pi/2.0))

    # Digital 8-pin header
    pcb.add(Header8x1('IO0', 'IO1', 'IO2', 'IO3', 'IO4', 'IO5', 'IO6', 'IO7',
                      position=(44,1), rotation=pi/2.0))

    # Analog 6-pin header
    pcb.add(Header6x1('AD0', 'AD1', 'AD2', 'AD3', 'AD4/SDA', 'AD5/SCL',
                      position=(49,49), rotation=pi/2.0))

    # Power header
    pcb.add(Header8x1(None, '+5V', 'RESET', '+3V3', '+5V', 'GND', 'GND', 'VIN',
                      position=(26,49), rotation=pi/2.0))

if __name__=='__main__':
    main()
