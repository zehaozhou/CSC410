#!/usr/bin/env python3.7
# You cannot import any other modules. Put all your helper functions in this file.
from z3 import *
import itertools


def decode(model, lits, n):
    """
    This function is only a helper suggestion to transform a model (the output of
    the solver) to a list of moves.
    To decode the model, you can query the values of the variables you defined.
    For this example, all_my_vars is a dictionnary of the solver variables used
    in the encoding.
    """
    moves = []
    # for k, my_var in all_my_vars.items():
    #     if model.evaluate(my_var):
    #         # then my_var has been assigned to true,
    #         moves = []
    #     else:
    #         # then my_var has been assigned to false,
    #         moves = []
    for order in range(n * n + (n + 1) % 2 - 1):
        for i in range(n):
            for j in range(n):
                for i2 in range(n):
                    for j2 in range(n):
                        if model.evaluate(lits[i][j][order]) and model.evaluate(lits[i2][j2][order + 1]):
                            moves.append([[i, j], [i2, j2]])
    print(len(moves))
    return moves


def encoding(n):
    """
    encoding takes an integer n > 0 and returns a list of moves. A move is a pair
    of cells (rooms) in the grid, for example [0,0],[1,0] is a move from cell (0,0) to cell
    (1,0).
    - If the killer cannot take a path from cell (0,0) to cell (n,n), return an
    empty list.
    - If the killer can find a path, return a list of moves, for example:
      [[[0,0],[1,0]],[[1,0],[2,0]], ...]
    - The moves do not have to be sorted in the right order, but they have to define a path
    that the "killer" can follow.
    """

    lits = []
    x = n * n + (n + 1) % 2

    for i in range(n):
        lits += [[]]
        for j in range(n):
            lits[i] += [[]]
            for order in range(x):
                lits[i][j].append(Bool("b_%i_%i_%i" % (i, j, order)))

    and_clauses = [lits[0][0][0], lits[n - 1][n - 1][x - 1]]
    and_clauses += [Or(lits[0][1][1], lits[1][0][1])]
    and_clauses += [Or(lits[n - 1][n - 2][x - 2], lits[n - 2][n - 1][x - 2])]
    for i in range(n):
        for j in range(n):
            if (i, j) != (0, 0) and (i, j) != (n - 1, n - 1):
                adj = valid(neighbours(i, j), n)
                for order in range(1, x - 1):
                    next_clauses = []
                    prev_clauses = []
                    for cell in adj:
                        next_clauses += [lits[cell[0]][cell[1]][order + 1]]
                        prev_clauses += [lits[cell[0]][cell[1]][order - 1]]
                    and_clauses += [Implies(lits[i][j][order], And(Or(next_clauses), Or(prev_clauses)))]

    s = Solver()
    # for c in and_clauses:
    #     s.add(And(c))
    s.add(And(and_clauses))

    # only 1 possible value per cell
    for i in range(n):
        for j in range(n):
            if (i, j) != (0, 0):
                s.add(exactly_one(lits[i][j]))

            # only 1 possible value per order
    for order in range(x):
        cells = []
        for i in range(n):
            for j in range(n):
                cells += [lits[i][j][order]]
        s.add(exactly_one(cells))

    sat = str(s.check())
    if sat != 'sat':
        return []
    model = s.model()
    return decode(model, lits, n)


# helpers from q1a
def neighbours(x, y):
    # finds the 4 neighbours of the selected cell
    return [[x - 1, y], [x, y - 1], [x, y + 1], [x + 1, y]]


def valid(neighbour, n):
    # removed the neighbours that are outside the border of the grid
    res = [i for i in filter((lambda cell: cell[0] >= 0 and cell[0] < n), neighbour)]
    res = [i for i in filter((lambda cell: cell[1] >= 0 and cell[1] < n), res)]
    return res


# helper from sudoku
def exactly_one(literals):
    c = []
    for pair in itertools.combinations(literals, 2):
        a, b = pair[0], pair[1]
        c += [Or(Not(a), Not(b))]
        # at least one true
    c += [Or(literals)]
    return And(c)


# ================================================================================
#  Do not modify below!
# ================================================================================
if __name__ == '__main__':

    if len(sys.argv) < 2:
        print("Usage: python q1b.py GRID_SIZE\n\tWhere GRID_SIZE >= 2 is the size of the grid.")
        exit(1)

    N = int(sys.argv[1])
    if N < 2:
        print("Grid size should be at least 2.")
        exit(1)
    solution = encoding(N)
    if solution:
        print(solution)
    else:
        print("No solution.")