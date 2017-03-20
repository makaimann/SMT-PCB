#!/usr/bin/env python2

import pyautogui as gui
import time
import subprocess
import argparse
import os
import os.path

from gui_tools import waitToClick, loc

def main():
    # load command-line arguments
    parser = argparse.ArgumentParser()
    parser.add_argument('--pcb')
    parser.add_argument('--ses')
    args = parser.parse_args()

    gui.PAUSE = 0.75

    subprocess.Popen(['pcbnew', args.pcb])
    
    # click on FreeRouting button
    waitToClick('freerouting')

    # back import specctra
    waitToClick('import_ses')

    # if there is no text bar to fill addresses, 
    # click the pencil icon to make it appear
    if not loc('location_field'):
        waitToClick('pencil_icon')

    # open file
    args.ses = os.path.expanduser(args.ses)
    args.ses = os.path.abspath(args.ses)
    gui.hotkey('ctrl', 'a')
    gui.hotkey('backspace')
    gui.typewrite(args.ses)
    waitToClick('open_button')

    # rebuild connectivity
    gui.hotkey('enter')

    # click OK button
    waitToClick('ok_button')

    # save
    gui.hotkey('ctrl', 's')

    # quit
    gui.hotkey('ctrl', 'q')

if __name__ == '__main__':
    main()
