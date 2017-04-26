#!/usr/bin/env python3

# Steven Herbst
# sherbst@stanford.edu

# Library enables geometry operations for PCBs

from math import cos, sin, hypot

class BoundingBox:
    def __init__(self):
        inf = float('inf')
        self.xmin = inf
        self.xmax = -inf
        self.ymin = inf
        self.ymax = -inf

    def add(self, x, y):
        if x < self.xmin:
            self.xmin = x
        if x > self.xmax:
            self.xmax = x
        if y < self.ymin:   
            self.ymin = y
        if y > self.ymax:
            self.ymax = y

    @property
    def width(self):
        return self.xmax - self.xmin

    @property
    def height(self):
        return self.ymax - self.ymin

    @property
    def center(self):
        return (self.xmin + self.xmax)/2.0, (self.ymin + self.ymax)/2.0

def formRect(w, h):
    return [(0,0), (w,0), (w,h), (0,h)]

def distPoints(a, b):
    return hypot(a[0]-b[0], a[1]-b[1])

def mult(p, scale):
    return (scale*p[0], scale*p[1])

def invertY(p):
    return (+p[0], -p[1])

def invertX(p):
    return (-p[0], +p[1])

def translate(p, x, y):
    return (p[0]+x, p[1]+y)

def rotate(p, th):
    x = p[0]*cos(th) - p[1]*sin(th)
    y = p[0]*sin(th) + p[1]*cos(th)
    return (x, y)

def transform(point, th, mirror, x, y):
    # invert Y coordinate if on the bottom
    if mirror:
        point = invertY(point)

    # rotate
    point = rotate(point, th)

    # translate by offset
    point = translate(point, x, y)

    # return
    return point
