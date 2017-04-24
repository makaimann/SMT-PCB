#!/usr/bin/env python3

# Steven Herbst
# sherbst@stanford.edu

# Library enables user to draw a PCB file from JSON

import pygame
import json
import argparse
import sys
from math import cos, sin
from pcbparse import BoundingBox

def getCenter(bbox):
    cx = (bbox.xmin + bbox.xmax)/2
    cy = (bbox.ymin + bbox.ymax)/2
    return cx, cy

def scaleFactor(bbox, w, h, margin):
    scaleX = w*(1-margin)/bbox.width
    scaleY = h*(1-margin)/bbox.height
    return min(scaleX, scaleY)

def formRect(thing):
    w = thing['width']
    h = thing['height']
    return [(0,0), (w,0), (w,h), (0,h)]

def roundPoint(point):
    return (round(point[0]), round(point[1]))

def mult(point, scale):
    return (scale*point[0], scale*point[1])

def invertY(point):
    return (point[0], -point[1])

def translate(point, x, y):
    return (point[0]+x, point[1]+y)

def rotate(point, theta):
    x = point[0]*cos(theta) - point[1]*sin(theta)
    y = point[0]*sin(theta) + point[1]*cos(theta)
    return (x, y)

def transform(point, th, x, y):
    return translate(rotate(point, th), x, y)

def remap(items, bbox, scale, screenWidth, screenHeight, margin):
    # apply translation
    x0, y0 = getCenter(bbox)
    items = [translate(p, -x0, -y0) for p in items]

    # apply scale factor
    items = [mult(p, scale) for p in items]

    # invert Y value
    items = [invertY(p) for p in items]
    
    # apply translation
    items = [translate(p, screenWidth/2, screenHeight/2) for p in items]

    # round points
    items = [roundPoint(p) for p in items]
    
    return items

def main():
    # Parse command-line arguments
    parser = argparse.ArgumentParser(description='Draw PCB design.')
    parser.add_argument('infile')
    parser.add_argument('--width', type=int, default=400)
    parser.add_argument('--height', type=int, default=400)
    parser.add_argument('--margin', type=float, default=0.1)
    args = parser.parse_args()

    # Parse file
    with open(args.infile, 'r') as f:
        json_dict = json.load(f)

    # Bounding box to determine max extents of components and board
    bbox = BoundingBox()

    # Determine module outlines and pad locations
    pads = []
    rects = []
    for mod in json_dict['modules']:
        theta = mod['theta']
        x = mod['x']
        y = mod['y']

        # add outlines
        rect = formRect(mod)
        rect = [transform(point, theta, x, y) for point in rect] 
        rects.append(rect)
        for point in rect:
            bbox.add(*point)

        # add pads
        for pad in mod['pads']:
            point = (pad['x'], pad['y'])
            point = transform(point, theta, x, y)
            pads.append(point)
            bbox.add(*point)

    # Determine the corners of the board
    edge = formRect(json_dict['border'])
    for point in edge:
        bbox.add(*point)

    # resize screen to fit
    scale = scaleFactor(bbox, args.width, args.height, args.margin)
    screenWidth = round(scale*bbox.width/(1-args.margin))
    screenHeight = round(scale*bbox.height/(1-args.margin))

    # bake in remapping parameters
    remapc = lambda points: remap(points, bbox, scale, screenWidth, screenHeight, args.margin)

    # remap points to pixel space
    rects = [remapc(rect) for rect in rects]
    pads = remapc(pads)
    edge = remapc(edge)

    pygame.init()

    # Define the colors we will use in RGB format
    BLACK = (  0,   0,   0)
    WHITE = (255, 255, 255)
    BLUE =  (  0,   0, 255)
    GREEN = (  0, 255,   0)
    RED =   (255,   0,   0)

    # Set the height and width of the screen
    size = [screenWidth, screenHeight]
    screen = pygame.display.set_mode(size)
 
    pygame.display.set_caption("Example code for the draw module")

    #Loop until the user clicks the close button.
    done = False
    clock = pygame.time.Clock()
     
    while not done:
     
        # This limits the while loop to a max of 10 times per second.
        # Leave this out and we will use all CPU we can.
        clock.tick(10)

        for event in pygame.event.get(): # User did something
            if event.type == pygame.QUIT: # If user clicked close
                done=True # Flag that we are done so we exit this loop

        screen.fill(WHITE)

        for rect in rects:
            pygame.draw.lines(screen, BLACK, True, rect, 1)

        for pad in pads:
            pygame.draw.circle(screen, RED, pad, 1, 0)

        pygame.draw.lines(screen, GREEN, True, edge, 1)

        pygame.display.flip()

    pygame.quit()

if __name__ == '__main__':
    main()
