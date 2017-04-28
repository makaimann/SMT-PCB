#!/usr/bin/env python3

# Steven Herbst
# sherbst@stanford.edu

from cvxpy import *
import numpy

def isSAT(LAB, LAC, LBC, maxDist):

	A = 0
	B = 1
	C = 2

	x = Variable(3)
	w = [1, 1, 1]

	# nonoverlap constraints
	constraints = []
	if LAB:
		constraints.append(x[A]+w[A] <= x[B])
	else:
		constraints.append(x[B]+w[B] <= x[A])
	if LAC:
		constraints.append(x[A]+w[A] <= x[C])
	else:
		constraints.append(x[C]+w[C] <= x[A])
	if LBC:
		constraints.append(x[B]+w[B] <= x[C])
	else:
		constraints.append(x[C]+w[C] <= x[B])

	# maximum distance constraint
	mLAB = 1 if LAB else -1
	mLBC = 1 if LBC else -1
	constraints.append(mLAB*(x[B] + w[B]/2.0 - x[A] - w[A]/2.0) + 
		               mLBC*(x[C] + w[C]/2.0 - x[B] - w[B]/2.0) <= maxDist)

	# define feasibility problem
	objective = Minimize(0)

	# solve the problem
	prob = Problem(objective, constraints)
	result = prob.solve()
	
	# if status is not OPTIMAL, then the problem is infeasible
	return prob.status == OPTIMAL

def main():
	pass

if __name__ == '__main__':
	main()