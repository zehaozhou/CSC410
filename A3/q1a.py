#!/usr/bin/env python3.7
# You cannot import any other modules. Put all your helper functions in this file
from z3 import *
import itertools

def encoding(pt_from, pt_to, grid):
    """
    The encoding function encodes the reachability problem in SAT and uses a solver to
    answer True if there is a path from pt_from to pt_to in grid, and False otherwise.
    pt_from -- a list of two integers, pt_from[0] is the row number of the starting point
               and pt_from[1] the column number.
    pt_to   -- a list of two integers, pt_to[0] is the row number of the end point, and
               and pt_to[1] the column number.
    grid    -- a list of lists of zeroes and ones, representing the grid, given row by row.
    """

    # You can assume that well_formed_problem(pt_from, pt_to, grid) returns True (see below)

    # TODO : implement this function!
    lits = []
    for i in range(len(grid)):
        lits.append([])
        for j in range(len(grid[0])):
            lits[i].append(Bool("b_%i_%i" % (i, j)))
    
    # assume the start cell is always reachable and the destination cell is never reachable
    and_clauses = [lits[pt_from[0]][pt_from[1]], Not(lits[pt_to[0]][pt_to[1]])]
    for i in range(len(grid)):
        for j in range(len(grid[0])):
            if grid[i][j] == 1:
                and_clauses += [Not(lits[i][j])]
            else:
                adj = valid(neighbours(i ,j), len(grid), len(grid[0]), grid)
                clauses = []
                # if a cell in the grid is reachable, then all adjacent cells except walls are reachable
                for cell in adj:
                    if grid[cell[0]][cell[1]] != 1:
                        clauses += [lits[cell[0]][cell[1]]]
                and_clauses += [Implies(lits[i][j], And(clauses))]

    s = Solver()
    for c in and_clauses:
        s.add(And(c))

    if str(s.check()) == 'sat':
        return False
    return True

def neighbours(x , y):
  # finds the 4 neighbours of the selected cell
  return [[x-1, y], [x, y-1], [x, y+1], [x+1, y]]

def valid(neighbour, h, w, grid):
  # removed the neighbours that are outside the border of the grid
  n = [i for i in filter((lambda cell: cell[0] >= 0 and cell[0] < h), neighbour)]
  n = [i for i in filter((lambda cell: cell[1] >= 0 and cell[1] < w), n)]
  return n

# ================================================================================
#  Do not modify below!
# ================================================================================
def well_formed_problem(pt_from, pt_to, grid):
    """
    Check if the problem defined by (pt_from, pt_to, grid) is a well formed problem:
    - the grid is not empty and every row has the same length,
    - starting and end points are different and both are in the grid.
    """
    n = len(grid[1])
    if n < 1:
        return False
    m = len(grid[0])
    for line in grid:
        if len(line) != m:
            return False
    i0, j0 = pt_from[0], pt_from[1]
    iEnd, jEnd = pt_to[0], pt_to[1]

    if i0 == iEnd and j0 == jEnd:
        return False

    return (0 <= i0 < n) and (0 <= iEnd < n) and (0 <= j0 < m) and (0 <= jEnd < m)


if __name__ == '__main__':

    if len(sys.argv) < 2:
        print("Usage: python q1a.py INPUT_FILE\n\tHint: test_input contains two valid input files.")
        exit(1)

    _grid = []
    with open(sys.argv[1], 'r') as input_grid:
        # The first line contains 4 ints separeted by spaces,
        _pts = [int(x) for x in input_grid.readline().strip().split(" ")]
        # the first two ints are the coordinates of the starting point,
        _pt_from = _pts[:2]
        # and the last to are the coordinates of the end point.
        _pt_to = _pts[2:]
        # Then, each new line is a line of the grid, starting from line 0.
        for line in input_grid.readlines():
            _grid.append([int(x) for x in line.split(" ")])

        if well_formed_problem(_pt_from, _pt_to, _grid):
            # Call the encoding function on the input.
            print(encoding(_pt_from, _pt_to, _grid))
            exit(0)
        else:
            print("The input file does not define a valid problem.")
            exit(1)
