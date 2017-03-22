#!/usr/bin/env python2

import pyautogui as gui
import subprocess
import argparse
import os
import os.path
import time

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

    # open file
    args.ses = os.path.expanduser(args.ses)
    args.ses = os.path.abspath(args.ses)
    gui.hotkey('ctrl', 'a')
    gui.hotkey('backspace')
    gui.typewrite(args.ses)
    gui.hotkey('enter')

    # rebuild connectivity
    waitToClick('yes_button', timeout=3.0)

    # click OK button
    waitToClick('ok_button')

    # save
    gui.hotkey('ctrl', 's')

    # quit
    gui.hotkey('ctrl', 'q')


if __name__ == '__main__':
    main()
