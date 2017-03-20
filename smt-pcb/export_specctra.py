#!/usr/bin/env python2

import pyautogui as gui
import subprocess
import argparse
import os
import os.path

from gui_tools import waitToClick


def main():
    # load command-line arguments
    parser = argparse.ArgumentParser()
    parser.add_argument('--pcb')
    parser.add_argument('--dsn')
    args = parser.parse_args()

    gui.PAUSE = 0.75

    subprocess.Popen(['pcbnew', args.pcb])

    # click on FreeRouting button
    waitToClick('freerouting')

    # Export specctra
    waitToClick('export_dsn')

    # Save DSN file
    args.dsn = os.path.expanduser(args.dsn)
    args.dsn = os.path.abspath(args.dsn)
    gui.hotkey('ctrl', 'a')
    gui.hotkey('backspace')
    gui.typewrite(args.dsn)
    waitToClick('save_button')

    # Close the FreeRouting dialog
    waitToClick('ok_button')

    # Quit program
    gui.hotkey('ctrl', 'q')


if __name__ == '__main__':
    main()
