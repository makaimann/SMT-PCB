# -*- coding: utf-8 -*-
#Copyright (C) 2014 Chris Hinsley All Rights Reserved

import sys, time
from array import array
from itertools import islice, izip, groupby
from random import shuffle
from mymath import *
from layer import *

def shift(l, n):
	n = n % len(l)
	head = l[:n]
	del l[:n]
	l.extend(head)
	return l

class Pcb():
	def __init__(self, dimensions, routing_flood_vectors, routing_path_vectors, dfunc, resolution, verbosity, minz):
		self.dfunc = dfunc
		self.verbosity = verbosity
		self.routing_flood_vectors = routing_flood_vectors
		self.routing_path_vectors = routing_path_vectors
		self.layers = Layers(dimensions, 1.0 / resolution)
		self.width, self.height, self.depth = dimensions
		self.resolution = resolution
		self.minz = minz
		self.width *= resolution
		self.height *= resolution
		self.stride = self.width * self.height
		self.nodes = array('i', [0 for x in xrange(self.stride * self.depth)])
		self.netlist = []
		self.deform = {}

	def grid_to_space_point(self, node):
		if node in self.deform:
			return self.deform[node]
		return (float(node[0]), float(node[1]), float(node[2]))

	def set_node(self, node, value):
		self.nodes[(self.stride * node[2]) + (node[1] * self.width) + node[0]] = value

	def get_node(self, node):
		return self.nodes[(self.stride * node[2]) + (node[1] * self.width) + node[0]]

	def all_marked(self, vectors, node):
		x, y, z = node
		for dx, dy, dz in vectors[z % 2]:
			nx = x + dx; ny = y + dy; nz = z + dz
			if (0 <= nx < self.width) and (0 <= ny < self.height) and (0 <= nz < self.depth):
				mark = self.get_node((nx, ny, nz))
				if mark != 0:
					yield (mark, (nx, ny, nz))

	def all_not_marked(self, vectors, node):
		x, y, z = node
		for dx, dy, dz in vectors[z % 2]:
			nx = x + dx; ny = y + dy; nz = z + dz
			if (0 <= nx < self.width) and (0 <= ny < self.height) and (0 <= nz < self.depth):
				if self.get_node((nx, ny, nz)) == 0:
					yield (nx, ny, nz)

	def all_nearer_sorted(self, vectors, node, goal, func):
		distance = self.get_node(node)
		sgoal = self.grid_to_space_point(goal)
		nodes = [(func(self.grid_to_space_point(marked[1]), sgoal), marked[1]) \
					for marked in self.all_marked(vectors, node) \
					if (distance - marked[0]) > 0]
		nodes.sort()
		for node in nodes:
			yield node[1]

	def all_not_shorting(self, gather, params, node, radius, via, gap):
		np = self.grid_to_space_point(node)
		for new_node in gather(*params):
			nnp = self.grid_to_space_point(new_node)
			if node[2] != new_node[2]:
				if not self.layers.hit_line(np, nnp, via, gap):
					yield new_node
			else:
				if not self.layers.hit_line(np, nnp, radius, gap):
					yield new_node

	def mark_distances(self, vectors, radius, via, gap, starts, ends = []):
		distance = 1
		nodes = list(starts)
		for node in nodes:
			self.set_node(node, distance)
		while nodes:
			distance += 1
			new_nodes = []
			for node in nodes:
				for new_node in self.all_not_shorting(self.all_not_marked, (vectors, node), node, radius, via, gap):
					self.set_node(new_node, distance)
					new_nodes.append(new_node)
			nodes = new_nodes
			if 0 not in [self.get_node(node) for node in ends]:
				break

	def unmark_distances(self):
		self.nodes = array('i', [0 for x in xrange(self.stride * self.depth)])

	def add_track(self, track):
		radius, via, gap, net = track
		self.netlist.append(Net(net, radius, via, gap, self))

	def route(self, timeout):
		self.remove_netlist()
		self.unmark_distances()
		now = time.time()
		self.netlist.sort(key = lambda i: i.radius, reverse = True)
		index = 0
		while index < len(self.netlist):
			if self.netlist[index].route(self.minz):
				index += 1
			else:
				if index == 0:
					self.shuffle_netlist()
				else:
					self.netlist.insert(0, self.netlist.pop(index))
					while index != 0:
						self.netlist[index].remove()
						self.netlist[index].shuffle_topology()
						index -= 1
			if time.time() - now > timeout:
				return False
			if self.verbosity >= 1:
				self.print_netlist()
		return True

	def cost(self):
		return sum(len(path) for net in self.netlist for path in net.paths)

	def shuffle_netlist(self):
		for net in self.netlist:
			net.remove()
			net.shuffle_topology()
		shuffle(self.netlist)

	def remove_netlist(self):
		for net in self.netlist:
			net.remove()

	def print_netlist(self):
		for net in self.netlist:
			net.print_net()
		print []
		sys.stdout.flush()

	def print_pcb(self):
		scale = 1.0 / self.resolution
		print [self.width * scale, self.height * scale, self.depth]
		sys.stdout.flush()

	def print_stats(self):
		num_vias = 0
		num_terminals = 0
		num_nets = len(self.netlist)
		for net in self.netlist:
			num_terminals += len(net.terminals)
			for path in net.paths:
				for a, b in izip(path, islice(path, 1, None)):
					if a[2] != b[2]:
						num_vias += 1
		print >> sys.stderr, "Number of Terminals:", num_terminals
		print >> sys.stderr, "Number of Nets:", num_nets
		print >> sys.stderr, "Number of Vias:", num_vias

class Net():
	def __init__(self, terminals, radius, via, gap, pcb):
		self.pcb = pcb
		self.terminals = [(r * pcb.resolution, g * pcb.resolution, \
			 				(x * pcb.resolution, y * pcb.resolution, z), \
							[(cx * pcb.resolution, cy * pcb.resolution) for cx, cy in s]) \
						 	for r, g, (x, y, z), s in terminals]
		self.radius = radius * pcb.resolution
		self.via = via * pcb.resolution
		self.gap = gap * pcb.resolution
		self.paths = []
		self.remove()
		for term in self.terminals:
			for z in xrange(pcb.depth):
				pcb.deform[(int(term[2][0] + 0.5), int(term[2][1] + 0.5), z)] = (term[2][0], term[2][1], float(z))

	def optimise_paths(self, paths):
		opt_paths = []
		for path in paths:
			opt_path = []
			d = (0, 0, 0)
			for a, b in izip(path, islice(path, 1, None)):
				p0 = self.pcb.grid_to_space_point(a)
				p1 = self.pcb.grid_to_space_point(b)
				d1 = norm_3d(sub_3d(p1, p0))
				if d1 != d:
					opt_path.append(a)
					d = d1
			opt_path.append(path[-1])
			opt_paths.append(opt_path)
		return opt_paths

	def shuffle_topology(self):
		shuffle(self.terminals)

	def add_paths_collision_lines(self):
		for path in self.paths:
			for a, b in izip(path, islice(path, 1, None)):
				p0 = self.pcb.grid_to_space_point(a)
				p1 = self.pcb.grid_to_space_point(b)
				if a[2] != b[2]:
					self.pcb.layers.add_line(p0, p1, self.via, self.gap)
				else:
					self.pcb.layers.add_line(p0, p1, self.radius, self.gap)

	def sub_paths_collision_lines(self):
		for path in self.paths:
			for a, b in izip(path, islice(path, 1, None)):
				p0 = self.pcb.grid_to_space_point(a)
				p1 = self.pcb.grid_to_space_point(b)
				if a[2] != b[2]:
					self.pcb.layers.sub_line(p0, p1, self.via, self.gap)
				else:
					self.pcb.layers.sub_line(p0, p1, self.radius, self.gap)

	def add_terminal_collision_lines(self):
		for node in self.terminals:
			r, g, (x, y, _), s = node
			if not s:
				self.pcb.layers.add_line((x, y, 0), (x, y, self.pcb.depth - 1), r, g)
			else:
				for z in xrange(self.pcb.depth):
					for a, b in izip(s, islice(s, 1, None)):
						self.pcb.layers.add_line((x + a[0], y + a[1], z), (x + b[0], y + b[1], z), r, g)

	def sub_terminal_collision_lines(self):
		for node in self.terminals:
			r, g, (x, y, _), s = node
			if not s:
				self.pcb.layers.sub_line((x, y, 0), (x, y, self.pcb.depth - 1), r, g)
			else:
				for z in xrange(self.pcb.depth):
					for a, b in izip(s, islice(s, 1, None)):
						self.pcb.layers.sub_line((x + a[0], y + a[1], z), (x + b[0], y + b[1], z), r, g)

	def remove(self):
		self.sub_paths_collision_lines()
		self.sub_terminal_collision_lines()
		self.paths = []
		self.add_terminal_collision_lines()

	def route(self, minz):
		try:
			self.paths = []
			self.sub_terminal_collision_lines()
			visited = set()
			for index in xrange(1, len(self.terminals)):
				visited |= set([(int(self.terminals[index - 1][2][0]+0.5), int(self.terminals[index - 1][2][1]+0.5), z) for z in xrange(self.pcb.depth)])
				ends = [(int(self.terminals[index][2][0]+0.5), int(self.terminals[index][2][1]+0.5), z) for z in xrange(self.pcb.depth)]
				self.pcb.mark_distances(self.pcb.routing_flood_vectors, self.radius, self.via, self.gap, visited, ends)
				ends = [(self.pcb.get_node(node), node) for node in ends]
				ends.sort()
				_, end = ends[0]
				path = [end]
				while path[-1] not in visited:
					nearer_nodes = self.pcb.all_not_shorting(self.pcb.all_nearer_sorted, \
								(self.pcb.routing_path_vectors, path[-1], end, self.pcb.dfunc), path[-1], self.radius, self.via, self.gap)
					next_node = next(nearer_nodes)
					if minz:
						for node in nearer_nodes:
							if node[2] == path[-1][2]:
								next_node = node
								break
					path.append(next_node)
				visited |= set(path)
				self.paths.append(path)
				self.pcb.unmark_distances()
			self.paths = self.optimise_paths(self.paths)
			self.add_paths_collision_lines()
			self.add_terminal_collision_lines()
			return True
		except StopIteration:
			self.pcb.unmark_distances()
			self.remove()
			return False

	def print_net(self):
		scale = 1.0 / self.pcb.resolution
		spaths = []
		for path in self.paths:
			spath = []
			for node in path:
				spath += [self.pcb.grid_to_space_point(node)]
			spaths += [spath]
		print [self.radius * scale, self.via * scale, self.gap * scale, \
				[(r * scale, g * scale, (x * scale, y * scale, z), \
				[(cx * scale, cy * scale) for cx, cy in s]) for r, g, (x, y, z), s in self.terminals], \
				[[(x * scale, y * scale, z) for x, y, z in spath] for spath in spaths]]
