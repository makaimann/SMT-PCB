#!/usr/bin/python3

from satispy import Variable, Cnf
from satispy.solver import Minisat
from functools import reduce
import cvxinterface


def interpret(solution, *args):
    assignment = []
    conflictexpr = Cnf()
    for arg in args:
        assignment.append(solution[arg])
        if solution[arg]:
            conflictexpr &= arg
        else:
            conflictexpr &= -arg

    conflictexpr = -(conflictexpr)

    return (assignment, conflictexpr)


if __name__ == "__main__":
    LAB = Variable('LAB')
    LAC = Variable('LAC')
    LBC = Variable('LBC')

    expr = (LAB | -LAB | LAC | -LAC | LBC | -LBC)

    solver = Minisat()
#    expr = Cnf()

    issat = False
    dist = 2

    while not issat:
        print('Solving in Minisat')
        print('Expr=', expr)
        solution = solver.solve(expr)
        assignment, conflictexpr = interpret(solution, LAB, LAC, LBC)
        print('Assignment =', assignment)
        print('Solving in CVX')
        cvxresult = cvxinterface.solve(*assignment, dist)
        expr = expr & conflictexpr
        print('CVX found feasible=:', cvxresult.feasible)
        issat = cvxresult.feasible

    if issat:
        print('Found satisfying assignment')
        print(cvxresult.optval)

