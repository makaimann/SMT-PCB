#!/usr/bin/env python2

import pyautogui as gui
import time
import subprocess
import argparse

def main():
    # load command-line arguments
    parser = argparse.ArgumentParser()
    parser.add_argument('--pcb')
    args = parser.parse_args()

    gui.PAUSE = 0.75

    subprocess.Popen(['pcbnew', args.pcb])
    time.sleep(2)
    
    # click on FreeRouting button
    gui.click(989, 61)

    # back import specctra
    gui.hotkey('down')
    gui.hotkey('enter')

    # open file
    gui.hotkey('enter')

    # rebuild connectivity
    gui.hotkey('enter')

    # click OK button
    gui.hotkey('down')
    gui.hotkey('right')
    gui.hotkey('enter')

    # save
    gui.hotkey('ctrl', 's')

    # quit
    gui.hotkey('ctrl', 'q')

if __name__ == '__main__':
    main()
