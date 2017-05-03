#!/usr/bin/env python3

# Steven Herbst
# sherbst@stanford.edu

# Library enables geometry operations for PCBs

import numpy as np
from math import cos, sin

def getX(p):
    return p.item(0)
    
def getY(p):
    return p.item(1)

def xy2p(x, y):
    return np.matrix([[x], [y]])

class BoundingBox:
    def __init__(self, initPoints=None):
        inf = float('inf')
        self.xmin = inf
        self.xmax = -inf
        self.ymin = inf
        self.ymax = -inf
        self.empty = True

        if initPoints is not None:
            self.add(initPoints)

    def add(self, p):
        self.empty = False

        xmin = np.min(p[0])
        if xmin < self.xmin:
            self.xmin = xmin

        xmax = np.max(p[0])
        if xmax > self.xmax:
            self.xmax = xmax

        ymin = np.min(p[1])
        if ymin < self.ymin:   
            self.ymin = ymin

        ymax = np.max(p[1])
        if ymax > self.ymax:
            self.ymax = ymax

    def disjointFrom(self, other):
        return (self.xmax < other.xmin or # left of 
                self.ymax < other.ymin or # below
                self.xmin > other.xmax or # right of
                self.ymin > other.ymax)   # above

    def fullyContains(self, other):
        return (self.xmin <= other.xmin and # left of left edge
                self.xmax >= other.xmax and # right of right edge
                self.ymin <= other.ymin and # below bottom edge
                self.ymax >= other.ymax)    # above top edge

    @property
    def width(self):
        return self.xmax - self.xmin

    @property
    def height(self):
        return self.ymax - self.ymin

    @property
    def center(self):
        x = (self.xmin + self.xmax)/2.0
        y = (self.ymin + self.ymax)/2.0
        return np.matrix([[x],[y]])

    @property
    def ll(self):
        return xy2p(self.xmin, self.ymin)

    @property
    def ul(self):
        return xy2p(self.xmin, self.ymax)

    @property
    def lr(self):
        return xy2p(self.xmax, self.ymin)

    @property
    def ur(self):
        return xy2p(self.xmax, self.ymax)

    @property
    def rect(self):
        return np.hstack([self.ll, self.ul, self.ur, self.lr])

def formRect(w, h):
    rect = np.matrix([[0, 0, w, w],
                      [0, h, h, 0]])
    return rect

def distPoints(a, b):
    return normPoints(a, b, 2)

def normPoints(a, b, n):
    return np.linalg.norm(a-b, n)    

def invertX(p):
    M = np.matrix([[ -1,  0],
                   [  0, +1]])
    return M*p

def invertY(p):
    M = np.matrix([[ +1,  0],
                   [  0, -1]])
    return M*p

def rotate(p, th):
    M = np.matrix([[ cos(th), -sin(th)],
                   [ sin(th),  cos(th)]])
    return M*p

def transform(p, th, mirror, offset):
    # invert Y coordinate if on the bottom
    if mirror:
        p = invertY(p)

    # rotate
    p = rotate(p, th)

    # translate by offset
    p = p + offset

    # return
    return p
