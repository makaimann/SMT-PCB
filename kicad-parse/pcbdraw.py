#!/usr/bin/env python3

# Steven Herbst
# sherbst@stanford.edu

# Library enables user to draw a PCB file from JSON

import pygame
import json
import argparse
import sys

from pcbgeom import *

def scaleFactor(bbox, w, h, margin):
    scaleX = w*(1-margin)/bbox.width
    scaleY = h*(1-margin)/bbox.height
    return min(scaleX, scaleY)

def remap(items, bbox, scale, screenWidth, screenHeight, margin):
    # apply translation
    x0, y0 = bbox.center
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
    parser.add_argument('--width', type=int, default=1280)
    parser.add_argument('--height', type=int, default=720)
    parser.add_argument('--margin', type=float, default=0.1)
    parser.add_argument('--top', action='store_true')
    parser.add_argument('--bottom', action='store_true')
    args = parser.parse_args()

    # If neither top nor bottom is specified, draw both
    if not args.top and not args.bottom:
        args.top = True
        args.bottom = True

    # Parse file
    with open(args.infile, 'r') as f:
        json_dict = json.load(f)

    # Bounding box to determine max extents of components and board
    bbox = BoundingBox()

    # Determine module outlines and pad locations
    pads = []
    rects = []
    for mod in json_dict['modules']:
        x = mod['x']
        y = mod['y']
        theta = mod['theta']
        mirror = mod['mirror']

        # add outlines
        rect = formRect(mod['width'], mod['height'])
        rect = [transform(point, theta, mirror, x, y) for point in rect] 
        for point in rect:
            bbox.add(*point)
    
        # Add to list of rectangles, noting the side
        rects.append((rect,mirror))

        # add pads
        for pad in mod['pads']:
            through = pad['through']
            rect = formRect(pad['width'], pad['height'])
            rect = [translate(point, pad['x'], pad['y']) for point in rect]
            rect = [transform(point, theta, mirror, x, y) for point in rect] 
            for point in rect:
                bbox.add(*point)

            # Add to list of pads, noting the side
            pads.append((rect,mirror,through))

    # Determine the corners of the board
    border = json_dict['border']
    edge = formRect(border['width'], border['height'])
    for point in edge:
        bbox.add(*point)
    
    # resize screen to fit
    scale = scaleFactor(bbox, args.width, args.height, args.margin)
    screenWidth = round(scale*bbox.width/(1-args.margin))
    screenHeight = round(scale*bbox.height/(1-args.margin))

    # bake in remapping parameters
    remapc = lambda points: remap(points, bbox, scale, screenWidth, screenHeight, args.margin)

    # remap points to pixel space
    rects = [(remapc(rect), mirror) for rect, mirror in rects]
    pads = [(remapc(rect), mirror, through) for rect, mirror, through in pads]
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
 
    pygame.display.set_caption("pcbdraw")

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

        for rect, mirror in rects:
            color = BLUE if mirror else RED
            draw = (not mirror and args.top) or (mirror and args.bottom)
            if draw:
                pygame.draw.lines(screen, color, True, rect, 1)

        for pad, mirror, through in pads:
            color = BLUE if mirror else RED
            draw = through or (not mirror and args.top) or (mirror and args.bottom)
            if draw:
                pygame.draw.lines(screen, color, True, pad, 1)
                
        pygame.draw.lines(screen, GREEN, True, edge, 1)

        pygame.display.flip()

    pygame.quit()

if __name__ == '__main__':
    main()
