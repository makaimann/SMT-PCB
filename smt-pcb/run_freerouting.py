#!/usr/bin/env python2

import pyautogui as gui
import time
import subprocess
import argparse
import os
import os.path

def main():
    # load command-line arguments
    parser = argparse.ArgumentParser()
    parser.add_argument('--pcb')
    parser.add_argument('--route_dir')
    args = parser.parse_args()

    gui.PAUSE = 0.75

    args.route_dir = os.path.expanduser(args.route_dir)
    print args.route_dir
    subprocess.Popen(['java', '-jar', 'FreeRouter.jar'], cwd=args.route_dir)
    time.sleep(2)
    
    # click on open design button
    gui.click(181, 68)

    # select folder
    gui.click(513, 369)
    gui.hotkey('enter')

    # select file
    gui.click(513, 369)
    gui.hotkey('enter')
    time.sleep(3)

    # run autorouter
    gui.click(380, 84)

    # wait until routing finishes 
    mydir = os.path.dirname(os.path.abspath(__file__))
    im = os.path.join(mydir, 'images', 'trace_length.png')
    res = gui.locateOnScreen(im)
    while not res:
        time.sleep(1)
        res = gui.locateOnScreen(im)

    # click on center of screen
    gui.click(683, 508)

    # click on file menu
    gui.click(137, 58)

    # click on export SES
    gui.click(212, 212)
    gui.hotkey('enter')

    # close window
    gui.click(133, 34)
    gui.hotkey('enter')

    # close window
    gui.click(79, 35)   


if __name__ == '__main__':
    main()
