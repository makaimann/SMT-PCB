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
    
    inst_usb(pcb)
    inst_atmega16u2(pcb)
    pcb.add(Header2x2('PB4', 'PB6', 'PB5', 'PB7'))
    pcb.add(Capacitor('DTR', 'RESET'))
    pcb.add(Resistor('M8RXD', 'IO0'))
    pcb.add(Resistor('M8TXD', 'IO1'))

    # ICSP connector
    pcb.add(ICSP(miso='MISO2', sck='SCK2', reset='RESET2', vdd='+5V', mosi='MOSI2', gnd='GND'))
    pcb.add(Resistor('RESET2', '+5V'))
    pcb.add(Diode('RESET2', '+5V'))

    inst_atmega328p(pcb)
    pcb.add(SPST('RESET', 'GND'))

    # IO headers
    pcb.add(Header10x1('IO8', 'IO9', 'SS', 'MOSI', 'MISO', 'SCK',
                       'GND', 'AREF', 'AD4/SDA', 'AD5/SCL'))
    pcb.add(Header8x1('IO0', 'IO1', 'IO2', 'IO3',
                      'IO4', 'IO5', 'IO6', 'IO7'))
    pcb.add(Header6x1('AD0', 'AD1', 'AD2', 'AD3',
                      'AD4/SDA', 'AD5/SCL'))

    # Power header
    pcb.add(Header8x1(None, '+5V', 'RESET', '+3V3', 
                      '+5V', 'GND', 'GND', 'VIN'))

    # ICSP connector
    pcb.add(ICSP(miso='MISO', sck='SCK', reset='RESET', vdd='+5V', mosi='MOSI', gnd='GND'))
 
    # Power LED
    pcb.add(Resistor('+5V', 'PWR_LED'))
    pcb.add(Resistor('+5V', 'PWR_LED'))
    pcb.add(LED('PWR_LED', 'GND'))
 
    # Op amp control circuit
    inst_op_amps(pcb)
    
    # Power input and LDOs
    inst_ldos(pcb)
 
    # put the parts on the board and save
    pcb.compile(critical_nets=['D+','D-','RD+','RD-','XT1','XT2',
                'XTAL1','XTAL2'])

def inst_usb(pcb):
    pcb.add(UsbConnB(vdd='XUSB', dm='D-', dp='D+', gnd='UGND', shield='USHIELD'))
    pcb.add(Varistor('D-', 'USHIELD'))
    pcb.add(Varistor('D+', 'USHIELD'))
    pcb.add(Inductor('USHIELD', 'UGND'))
    pcb.add(PTC('XUSB', 'USBVCC'))
    pcb.add(Resistor('D-', 'RD-'))
    pcb.add(Resistor('D+', 'RD+'))
    pcb.add(Resistor('UGND', 'GND'))

def inst_atmega16u2(pcb):
    atmega16 = ATMEGA16U2()
    pcb.add(atmega16)

    atmega16.wire_power(vdd='+5V', gnd='GND')
    atmega16.wire_usb(vdd='USBVCC', dm='RD-', dp='RD+', gnd='UGND')
    pcb.add(Capacitor('+5V', 'GND'))

    atmega16.wire_xtal('XT1', 'XT2')
    pcb.add(Crystal('XT1', 'XT2'))
    pcb.add(Resistor('XT1', 'XT2'))
    pcb.add(Capacitor('XT1', 'GND'))
    pcb.add(Capacitor('XT2', 'GND'))

    atmega16.reset.wire('RESET2')
    atmega16.ucap.wire('TP_VUCAP')
    pcb.add(Capacitor('TP_VUCAP', 'UGND'))
   
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

    # USB boot enable
    pcb.add(Resistor('DTR', 'GND'))

    # LEDs
    pcb.add(Resistor('+5V', 'TXLED_R'))
    pcb.add(Resistor('+5V', 'RXLED_R'))
    pcb.add(LED('TXLED_R', 'TXLED'))
    pcb.add(LED('RXLED_R', 'RXLED'))

def inst_atmega328p(pcb):
    atmega328 = ATMEGA328P()
    pcb.add(atmega328)

    atmega328.wire_power(vdd='+5V', gnd='GND')
    pcb.add(Capacitor('+5V', 'GND'))

    atmega328.wire_xtal('XTAL1', 'XTAL2')
    pcb.add(Crystal('XTAL1', 'XTAL2'))
    pcb.add(Resistor('XTAL1', 'XTAL2'))
    pcb.add(Capacitor('XTAL1', 'GND'))
    pcb.add(Capacitor('XTAL2', 'GND'))

    atmega328.reset.wire('RESET')
    pcb.add(Diode('RESET', '+5V'))
    pcb.add(Resistor('RESET', '+5V'))

    atmega328.aref.wire('AREF')
    pcb.add(Capacitor('AREF', 'GND'))

    pb = atmega328.PB
    pb[5].wire('SCK')
    pb[4].wire('MISO')
    pb[3].wire('MOSI')
    pb[2].wire('SS')
    pb[1].wire('IO9')
    pb[0].wire('IO8')

    pc = atmega328.PC
    pc[5].wire('AD5/SCL')
    pc[4].wire('AD4/SDA')
    pc[3].wire('AD3')
    pc[2].wire('AD2')
    pc[1].wire('AD1')
    pc[0].wire('AD0')

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
    dual_op_amp = DualOpAmp()
    pcb.add(dual_op_amp)

    pcb.add(Resistor('+5V', 'CMP'))
    pcb.add(Resistor('CMP', 'GND'))

    dual_op_amp.wire_power('+5V', 'GND')
    pcb.add(Capacitor('+5V', 'GND'))

    dual_op_amp.wire_op_amp('CMP', '+3V3', 'GATE_CMD')

    dual_op_amp.wire_op_amp('SCK', 'L13', 'L13')
    pcb.add(Resistor('L13', 'L13_R'))
    pcb.add(LED('L13_R', 'GND'))

def inst_ldos(pcb):
    # input jack
    pcb.add(BarrelJack('PWRIN', 'GND'))
    pcb.add(Diode('PWRIN', 'VIN'))
    pcb.add(Capacitor('VIN', 'GND', 'CP_Elec'))
        
    # 5.0V LDO
    pcb.add(LDO_5v0(vin='VIN', gnd='GND', vout='+5V'))
    pcb.add(Capacitor('+5V', 'GND', 'CP_Elec'))
    pcb.add(Capacitor('+5V', 'GND'))

    # 3.3V LDO
    pcb.add(NMOS(gate='GATE_CMD', source='+5V', drain='USBVCC'))
    pcb.add(LDO_3v3(vin='+5V', gnd='GND', vout='+3V3'))
    pcb.add(Capacitor('+3V3', 'GND'))

if __name__=='__main__':
    main()
