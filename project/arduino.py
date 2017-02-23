#!/usr/bin/env python

# Steven Herbst
# sherbst@stanford.edu
#
# CS448H Winter 2017

# Demo code to generate Arduino Uno Rev3

# SMT-PCB specific imports
from mycad import PcbDesign
from parts import *

def main():
    # create object to hold PCB design
    pcb = PcbDesign('test.kicad_pcb', width=68.6, height=53.3)
    
    inst_usb()
    inst_atmega16u2()
    ICSP(miso='MISO2', sck='SCK2', reset='RESET2', vdd='+5V', mosi='MOSI2', gnd='GND')
    Header2x2('PB4', 'PB6', 'PB5', 'PB7')

    # put the parts on the board and save
    pcb.compile()

def inst_usb():
    UsbConnB(vdd='XUSB', dm='D-', dp='D+', gnd='UGND', shield='USHIELD')
    Varistor('D-', 'USHIELD')
    Varistor('D+', 'USHIELD')
    Inductor('USHIELD', 'UGND')
    PTC('XUSB', 'USBVCC')
    Resistor('D-', 'RD-')
    Resistor('D+', 'RD+')
    Resistor('UGND', 'GND')

def inst_atmega16u2():
    atmega16 = ATMEGA16U2()
    atmega16.wire_power(vdd='+5V', gnd='GND')
    atmega16.wire_usb(vdd='USBVCC', dm='RD-', dp='RD+', gnd='UGND')
    Capacitor('+5V', 'GND')
    
    pb = atmega16.PB
    pb[7].wire('PB7')
    pb[6].wire('PB6')
    pb[5].wire('PB5')
    pb[4].wire('PB4')
    pb[3].wire('MISO2')
    pb[2].wire('MOSI2')
    pb[1].wire('SCK2')

    pd = atmega16.PD
    pd[7].wire('DTR')
    pd[5].wire('TXLED')
    pd[4].wire('RXLED')
    pd[3].wire('M8RXD')
    pd[2].wire('M8TXD')

if __name__=='__main__':
    main()
