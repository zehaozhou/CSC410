#!/usr/bin/env python3.7
# You cannot import any other modules. Put all your helper functions in this file
from z3 import *
from itertools import combinations


def solve(A, B):
    """
    This function should solve the stable marriages problem, with inputs A and B:
    - A lists the preferences of elements from 1 to len(A).
    - B lists the preferences of elements from len(A) + 1 to 2 * len(A).
      This means that B[i] is the preferences of element (i + 1 + len(A))!
    Returns a list of pairs of integers, such that the lists represents a stable
    matching for A, B. The first element of each pair is an element of [1, len(A)]
    and the second element of each pair is an element of [len(A) + 1, 2 * len(A)]
    """

    AB = A + B
    n = len(A)
    # Do not modify the name of these two lists. They are used
    # by a portion of the code you are not allowed to modify later in this function.
    constraints_matching = []
    minimization_objectives = []

    # In this problem, you have to express matching constraints, that ensure the result is a correct
    # matching. You can reuse the constraints of q1a, but do not reuse the constraints_stability!
    # Instead, create a list of minimization objectives that have to be minimized (the list can
    # have a single element).
    # REMARK: to add a maximixation objective, just add its opposite:
    # Maximize Q <-> Minimize - Q
    # TODO add the matching constraints and the optimization objectives.

    for comb in combinations(range(1, 2 * n + 1), 2):
        x, y = comb
        constraints_matching.append(iff_match(x, y))
        if x != y:
            # match() should be injective
            constraints_matching.append(match(x) != match(y))

    for i in range(1, n + 1):
        constraints_matching.append(match(i) >= n + 1)
        constraints_matching.append(match(i) <= 2 * n)
        # match() should be surjective
        constraints_matching.append(Or([match(p) == i for p in range(n + 1, 2 * n + 1)]))
    for i in range(n + 1, 2 * n + 1):
        constraints_matching.append(match(i) >= 1)
        constraints_matching.append(match(i) <= n)
        # match() should be surjective
        constraints_matching.append(Or([match(p) == i for p in range(1, n + 1)]))

    # minimization
    stable_ints = [[[[Int("index_%i_%i_%i_%i" % (b, c, e, f)) for e in range(1, n + 1)] for f in range(n + 1, 2 * n + 1)]
                      for b in range(1, n + 1)] for c in range(n + 1, 2 * n + 1)]

    for b in range(1, n + 1):
        for c in range(n + 1, 2 * n + 1):
            for e in range(1, n + 1):
                for f in range(n + 1, 2 * n + 1):
                    constraints_matching.append(Implies(And(e == match(c), f == match(b),
                                                        AB[c - 1].index(b) < AB[c - 1].index(e),
                                                            AB[b - 1].index(c) < AB[b - 1].index(f)),
                                                        stable_ints[c - n - 1][b - 1][f - n - 1][e - 1] == 1))
                    constraints_matching.append(Implies(Not(And(e == match(c), f == match(b),
                                                            AB[c - 1].index(b) < AB[c - 1].index(e),
                                                            AB[b - 1].index(c) < AB[b - 1].index(f))),
                                                        stable_ints[c - n - 1][b - 1][f - n - 1][e - 1] == 0))
    sum = 0
    for b in range(1, n + 1):
        for c in range(n + 1, 2 * n + 1):
            for e in range(1, n + 1):
                for f in range(n + 1, 2 * n + 1):
                    sum = sum + stable_ints[c - n - 1][b - 1][f - n - 1][e - 1]

    minimization_objectives.append(sum)

    # ==============================================================================================
    # DO NOT MODIFY.
    # This code adds the matching constraints to the solver, and the minimization objectives.
    s = Optimize()
    for cstr in constraints_matching:
        s.add(cstr)
    for opt in minimization_objectives:
        s.minimize(opt)

    assert str(s.check()) == 'sat'
    model = s.model()
    # ==============================================================================================

    if str(s.check()) == "sat":
        pairs = []
        for x in range(1, n + 1):
            pairs.append((x, model.evaluate(match(x))))
        return pairs
    else:
        return []


match = Function("match", IntSort(), IntSort())


def iff_match(i, j):
    return And([Implies(match(i) == j, match(j) == i),
                Implies(match(i) != j, match(j) != i)])


# ================================================================================
#  DO NOT MODIFY below!
# ================================================================================
def well_ranked(pref, imin, imax):
    for pid in pref:
        if pid > imax or pid < imin:
            return False
    return True


def well_formed_problem(prefs):
    """
    Check that everyone has ranked all the other persons.
    """
    n2 = len(prefs)
    A, B = prefs[: int(n2 / 2)], prefs[int(n2 / 2):]
    n = len(A)
    assert len(B) == n
    for pref in A:
        assert well_ranked(pref, n, 2 * n)
    for pref in B:
        assert well_ranked(pref, 1, n)
    return True


if __name__ == '__main__':

    if len(sys.argv) < 2:
        print("Usage: python q1b.py INPUT_FILE\n\tHint: test_input contains two valid input files.")
        exit(1)

    prefs = []
    with open(sys.argv[1], 'r') as input_grid:
        for line in input_grid.readlines():
            prefs.append([int(x) for x in line.strip().split()])

        if well_formed_problem(prefs):
            n2 = len(prefs)
            A, B = prefs[: int(n2 / 2)], prefs[int(n2 / 2):]
            print(solve(A, B))
            exit(0)
        else:
            print("The input file does not define a valid problem.")
            exit(1)