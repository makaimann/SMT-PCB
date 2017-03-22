import os
import os.path
import pyautogui as gui
import time


def getImagePath(name):
    mydir = os.path.dirname(os.path.abspath(__file__))
    im = os.path.join(mydir, 'images', name + '.png')
    return im


def waitToClick(name, delay=0.5, timeout=None, region=None):
    print 'Waiting to click: ', name

    if timeout is None:
        timeout = float('inf')
    start = time.time()

    wait = True
    while wait and (time.time()-start) < timeout:
        try:
            click(name, region)
            wait = False
        except BaseException:
            time.sleep(delay)


def waitFor(name, delay=0.5, timeout=None, region=None):
    print 'Waiting for:', name

    if timeout is None:
        timeout = float('inf')
    start = time.time()

    res = loc(name, region)
    while not res and (time.time() - start) < timeout:
        time.sleep(0.5)
        res = loc(name, region)


def click(name, region=None):
    res = loc(name, region)
    if res:
        gui.click(res[0], res[1])
    else:
        raise Exception('Button not found.')


def loc(name, region=None):
    im = getImagePath(name)
    if region:
        return gui.locateCenterOnScreen(im, region=region)
    else:
        return gui.locateCenterOnScreen(im)
