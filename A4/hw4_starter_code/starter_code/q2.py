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

    # Return the completed grid if a solution exists. Otherwise, return None.
    return grid


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
