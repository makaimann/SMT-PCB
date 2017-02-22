#!/opt/local/bin/python -tt
# -*- coding: utf-8 -*-
#Copyright (C) 2014 Chris Hinsley All Rights Reserved

import os, sys, argparse, select
from ast import literal_eval
from itertools import izip, islice, chain
from mymath import *

import matplotlib.pyplot as plt
import matplotlib.patches as patches
import matplotlib.path as path
import matplotlib.animation as animation
import pylab

MARGIN = 2

args = None

def split_paths(paths):
	new_paths = []
	for path in paths:
		new_path = []
		for a, b in izip(path, islice(path, 1, None)):
			_, _, za = a
			_, _, zb = b
			if za != zb:
				if new_path:
					new_path.append(a)
					new_paths.append(new_path)
				new_paths.append([a, b])
				new_path = []
			else:
				new_path.append(a)
		if new_path:
			new_path.append(path[-1])
			new_paths.append(new_path)
	return new_paths

def scale_and_split_tracks(tracks, scale):
	for track in tracks:
		track[0] *= scale
		track[1] *= scale
		track[2] *= scale
		track[4] = split_paths(track[4])
		for i in xrange(len(track[3])):
			r, g, (x, y, z), s = track[3][i]
			track[3][i] = r * scale, g * scale, ((x + MARGIN) * scale, (y + MARGIN) * scale, z), [(cx * scale, cy * scale) for cx, cy in s]
		for path in track[4]:
			for i in xrange(len(path)):
				x, y, z = path[i]
				path[i] = (x + MARGIN) * scale, (y + MARGIN) * scale, z

def get_tracks():
	tracks = []
	while True:
		line = args.infile.readline()
		if not line:
			tracks = []
			break
		track = literal_eval(line.strip())
		if not track:
			break
		tracks.append(track)
	return tracks

def doframe(frame_num, dimensions, poll, fig, ax):
	tracks = get_tracks()
	if poll:
		while poll.poll(1):
			new_tracks = get_tracks()
			if not new_tracks:
				break
			tracks = new_tracks
	if not tracks:
		return

	pcb_width, pcb_height, pcb_depth = dimensions
	scale = args.s[0]
	scale_and_split_tracks(tracks, scale)
	pcb_width += MARGIN * 2; pcb_height += MARGIN * 2
	img_width = int(pcb_width * scale)
	if args.o[0] == 0:
		img_height = int(pcb_height * scale)
	else:
		img_height = int(pcb_height * pcb_depth * scale)

	ax.clear()
	pylab.subplots_adjust(left = 0.0, right = 1.0, bottom = 0.0, top = 1.0)
	ax.set_xlim([0, img_width])
	ax.set_ylim([0, img_height][::-1])
	ax.set(aspect = 1)
	ax.axis('off')

	if args.o[0] == 0:
		colors = ['red', 'green', 'blue', 'yellow', 'fuchsia', 'aqua']
		for depth in xrange(pcb_depth - 1, -1, -1):
			brush = colors[depth % len(colors)]
			for track in tracks:
				radius, via, gap, terminals, paths = track
				for path in paths:
					if path[0][2] == path[-1][2] == depth:
						points = thicken_path_2d([(x, y) for x, y, _ in path], radius, 3, 2)
						poly = plt.Polygon(points, facecolor = brush, edgecolor = 'none', alpha = 0.5)
						ax.add_patch(poly)
		for track in tracks:
			radius, via, gap, terminals, paths = track
			for path in paths:
				if path[0][2] != path[-1][2]:
					x, y, _ = path[0]
					circ = plt.Circle((x, y), radius = via, color = 'white')
					ax.add_patch(circ)
			for r, g, (x, y, _), s in terminals:
				if not s:
					circ = plt.Circle((x, y), radius = r, color = 'white')
					ax.add_patch(circ)
				else:
					if r !=0:
						points = thicken_path_2d([(cx + x, cy + y) for cx, cy in s], r, 3, 2)
						poly = plt.Polygon(points, facecolor = 'white', edgecolor = 'none')
						ax.add_patch(poly)
					else:
						points = [(cx + x, cy + y) for cx, cy in s]
						poly = plt.Polygon(points, facecolor = 'white', edgecolor = 'none')
						ax.add_patch(poly)
	else:
		for depth in xrange(pcb_depth):
			for track in tracks:
				radius, via, gap, terminals, paths = track
				for path in paths:
					if path[0][2] == path[-1][2] == depth:
						points = thicken_path_2d([(x, y + depth * pcb_height * scale) for x, y, _ in path], radius + gap, 3, 2)
						poly = plt.Polygon(points, facecolor = 'white', edgecolor = 'none')
						ax.add_patch(poly)
			for track in tracks:
				radius, via, gap, terminals, paths = track
				for path in paths:
					if path[0][2] != path[-1][2]:
						x, y, _ = path[0]
						y += depth * pcb_height * scale
						circ = plt.Circle((x, y), radius = via + gap, color = 'white')
						ax.add_patch(circ)
				for r, g, (x, y, _), s in terminals:
					y += depth * pcb_height * scale
					if not s:
						circ = plt.Circle((x, y), radius = r + g, color = 'white')
						ax.add_patch(circ)
					else:
						points = thicken_path_2d([(cx + x, cy + y) for cx, cy in s], r + g, 3, 2)
						poly = plt.Polygon(points, facecolor = 'white', edgecolor = 'none')
						ax.add_patch(poly)
						if r ==0:
							points = [(cx + x, cy + y) for cx, cy in s]
							poly = plt.Polygon(points, facecolor = 'white', edgecolor = 'none')
							ax.add_patch(poly)
		for depth in xrange(pcb_depth):
			for track in tracks:
				radius, via, gap, terminals, paths = track
				for path in paths:
					if path[0][2] == path[-1][2] == depth:
						points = thicken_path_2d([(x, y + depth * pcb_height * scale) for x, y, _ in path], radius, 3, 2)
						poly = plt.Polygon(points, facecolor = 'black', edgecolor = 'none')
						ax.add_patch(poly)
			for track in tracks:
				radius, via, gap, terminals, paths = track
				for path in paths:
					if path[0][2] != path[-1][2]:
						x, y, _ = path[0]
						y += depth * pcb_height * scale
						circ = plt.Circle((x, y), radius = via, color = 'black')
						ax.add_patch(circ)
				for r, g, (x, y, _), s in terminals:
					y += depth * pcb_height * scale
					if not s:
						circ = plt.Circle((x, y), radius = r, color = 'black')
						ax.add_patch(circ)
					else:
						if r !=0:
							points = thicken_path_2d([(cx + x, cy + y) for cx, cy in s], r, 3, 2)
							poly = plt.Polygon(points, facecolor = 'black', edgecolor = 'none')
							ax.add_patch(poly)
						else:
							points = [(cx + x, cy + y) for cx, cy in s]
							poly = plt.Polygon(points, facecolor = 'black', edgecolor = 'none')
							ax.add_patch(poly)
	return []

def main():
	global args

	parser = argparse.ArgumentParser(description = 'Pcb layout viewer.')
	parser.add_argument('infile', nargs = '?', type = argparse.FileType('r'), default = sys.stdin, help = 'filename, default stdin')
	parser.add_argument('--s', nargs = 1, type = int, default = [9], help = 'scale factor, default 9')
	parser.add_argument('--f', nargs = 1, type = float, default = [100.0], help = 'framerate, default 100.0')
	parser.add_argument('--i', nargs = 1, default = ['pcb.png'], help = 'filename, default pcb.png')
	parser.add_argument('--o', nargs = 1, type = int, default = [0], choices=range(0, 2), help = 'overlay modes 0..1, default 0')
	args = parser.parse_args()

	poll = None
	if os.name != 'nt':
		if args.infile == sys.stdin:
			poll = select.poll()
			poll.register(args.infile, select.POLLIN)

	dimensions = literal_eval(args.infile.readline().strip())
	pcb_width, pcb_height, pcb_depth = dimensions
	pcb_width += MARGIN * 2; pcb_height += MARGIN * 2
	scale = args.s[0]
	pcb_width = int(pcb_width * scale)
	if args.o[0] == 0:
		pcb_height = int(pcb_height * scale)
	else:
		pcb_height = int(pcb_height * pcb_depth * scale)

	fig, ax = plt.subplots(frameon = True, facecolor = 'black')
	ani = animation.FuncAnimation(fig, doframe, fargs = (dimensions, poll, fig, ax), interval = 10, blit = False, repeat = True)
	plt.show()

if __name__ == '__main__':
	main()
