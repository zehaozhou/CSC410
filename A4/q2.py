#!/usr/bin/env python3.7
# You cannot import any other modules. Put all your helper functions in this file
from z3 import *
from itertools import combinations

def solve(grid):
    """
    This function solves the Hidato puzzle with the initial configuration stored in grid.
    You should ouput a grid in the same format, but where all the '-' have been replaced
    by numbers.
    """
    # TODO : solve the Hidato puzzle using Z3. grid[i][j] is either "-", "*" or an integer.
    # You can use SAT or SMT, but the latter is easier.

    lits = []
    or_clauses = []

    # calculate to total number of values
    count = 0
    for i in range(len(grid)):
        for j in range(len(grid[0])):
            if grid[i][j] != '*':
                count+=1

    # set up Bools for each cell
    for i in range(len(grid)):
        lits.append([])
        for j in range(len(grid[0])):
            lits[i].append([])
            if grid[i][j] != '*':
                for k in range(count):
                    lits[i][j].append(Bool("b_%i_%i_%i" % (i, j, k)))

    # all cells have one value
    for i in range(len(grid)):
        for j in range(len(grid[0])):
            if grid[i][j] != '*':
                or_clauses += exactly_one(lits[i][j])

    # all values are used once
    for k in range(count):
        c = []
        for i in range(len(grid)):
            for j in range(len(grid[0])):
                if grid[i][j] != '*':
                    c.append(lits[i][j][k])
        or_clauses += exactly_one(c)

    # for each cell, it's surrounding cells contains plus/minus 1 values
    for i in range(len(grid)):
        for j in range(len(grid[0])):
            if grid[i][j] != '*':
                for k in range(count):
                    neighbour = valid(neighbours(i ,j), len(grid), len(grid[0]), grid)
                    inc = []
                    dec = []
                    if k >= 1:
                        for cell in neighbour:
                            if grid[cell[0]][cell[1]] != '*':
                                dec.append(lits[cell[0]][cell[1]][k-1])
                        or_clauses.append(Implies(lits[i][j][k], Or(dec)))
                    if k < count - 1:
                        for cell in neighbour:
                            if grid[cell[0]][cell[1]] != '*':
                                inc.append(lits[cell[0]][cell[1]][k+1])
                        or_clauses.append(Implies(lits[i][j][k], Or(inc)))

    # set values in the given grid
    for i in range(len(grid)):
        for j in range(len(grid[0])):
            if grid[i][j] != '-' and grid[i][j] != '*':
                or_clauses += [[lits[i][j][grid[i][j]-1]]]

    s = Solver()

    for c in or_clauses:
        s.add(Or(c))

    # Return the completed grid if a solution exists. Otherwise, return None.
    if str(s.check()) == 'sat':
        model = s.model()
        return decode(model, lits, grid, count)
    else:
        return None

def decode(model, lits, grid, count):
    """
    This function is only a helper suggestion to transform a model (the output of
    the solver) to a list of moves.
    To decode the model, you can query the values of the variables you defined.
    For this example, all_my_vars is a dictionnary of the solver variables used
    in the encoding.
    """
    new_grid = []
    for i in range(len(grid)):
        new_grid.append([])
        for j in range(len(grid[0])):
            if grid[i][j] == '*':
                new_grid[i].append('*')
            else:
                for k in range(count):
                    if model.evaluate(lits[i][j][k]):
                        new_grid[i].append(lit_value(lits[i][j][k])+1)
    return new_grid

def lit_value(lit):
    return int(str(lit).split('_')[-1])

def possible_values(i, j, grid, count):
    if grid[i][j] != '-':
        return [grid[i][j]]

    values = []

    neighbour_cells = valid(neighbours(i ,j), len(grid), len(grid[0]), grid)
    neighbour_cells = [i for i in filter((lambda cell: grid[cell[0]][cell[1]] != '*' and grid[cell[0]][cell[1]] != '-'), neighbour_cells)]
    for cell in neighbour_cells:
        values += [grid[cell[0]][cell[1]]+1, grid[cell[0]][cell[1]]-1]
    values = [i for i in filter((lambda v: v in range(count)), values)]

    return list(set(values)) if len(values) != 0 else range(count)

def neighbours(x , y):
  # finds the 4 neighbours of the selected cell
  return [[x-1, y-1], [x-1, y], [x-1, y+1], [x, y-1], [x, y+1], [x+1, y-1], [x+1, y], [x+1, y+1]]

def valid(neighbour, h, w, grid):
  # removed the neighbours that are outside the border of the grid
  n = [i for i in filter((lambda cell: cell[0] >= 0 and cell[0] < h), neighbour)]
  n = [i for i in filter((lambda cell: cell[1] >= 0 and cell[1] < w), n)]
  return n

def exactly_one(literals):
    clauses = [literals]        # at least one of the literals is true
    # Now encode no more than one literal is true.
    # Hint: there is no pair of literals such that both are true.
    for comb in combinations(literals, 2):
        clauses += [[Not(comb[0]), Not(comb[1])]]
    return clauses


# ================================================================================
#  DO NOT MODIFY below!
# ================================================================================
def check(raw_grid):
    """
    Check that the grid is well defined.
    """
    n = len(raw_grid)
    assert n > 1
    m = len(raw_grid[0])
    assert m > 1

    grid = []
    for i in range(n):
        grid.append([])
        assert len(raw_grid[i]) == m

        for elt in raw_grid[i]:
            if elt == '*':
                grid[i].append(elt)
            elif elt == '-':
                grid[i].append(elt)
            else:
                try:
                    grid[i].append(int(elt))
                except:
                    return None

    return grid


def print_solution(grid):
    for line in grid:
        if '-' not in line:
            print(" ".join([str(x) for x in line]))
        else:
            print("Solution incomplete!")
            return


if __name__ == '__main__':

    if len(sys.argv) < 2:
        print("Usage: python q2.py INPUT_FILE")
        print("\tHint: test_input contains valid input files for Hidato.")
        exit(1)

    raw_grid = []
    with open(sys.argv[1], 'r') as input_grid:
        for line in input_grid.readlines():
            raw_grid.append(line.strip().split())

        grid = check(raw_grid)
        if grid:
            # Call the encoding function on the input.
            print_solution(solve(grid))
            exit(0)
        else:
            # Grid is none: this means there is no solution!
            print("The input file does not define a valid problem.")
            exit(1)