#!/usr/bin/env python2

import pyautogui as gui
import subprocess
import argparse
import os
import os.path

from gui_tools import waitToClick, waitFor, getImagePath


def main():
    # load command-line arguments
    parser = argparse.ArgumentParser()
    parser.add_argument('--dsn')
    parser.add_argument('--route_dir')
    args = parser.parse_args()

    gui.PAUSE = 0.75

    # run FreeRouting in the correct directory
    args.route_dir = os.path.expanduser(args.route_dir)
    args.route_dir = os.path.abspath(args.route_dir)
    subprocess.Popen(['java', '-jar', 'FreeRouter.jar'], cwd=args.route_dir)

    # click on open design button
    waitToClick('open_design')

    # select folder
    args.dsn = os.path.expanduser(args.dsn)
    args.dsn = os.path.abspath(args.dsn)
    gui.typewrite(args.dsn)
    gui.hotkey('enter')

    # run autorouter
    waitFor('autorouter')
    gui.hotkey('enter')
    waitToClick('autorouter')

    # wait until routing finishes
    waitFor('trace_length')

    # click on center of screen
    width, height = gui.size()
    gui.click(width / 2, height / 2)

    # click on file menu
    waitToClick('file_menu')

    # click on export SES
    waitToClick('export_ses')
    waitToClick('yes_button_freeroute')

    # close window
    waitToClick('file_menu')
    waitToClick('cancel_and_exit')

    # close window
    im = getImagePath('freerouter_title_bar')
    title_bar = gui.locateOnScreen(im)
    waitToClick('close_button', region=title_bar)


if __name__ == '__main__':
    main()
