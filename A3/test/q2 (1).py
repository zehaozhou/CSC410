#!/usr/bin/env python3.7
# You cannot import any other modules. Put all your helper functions in this file
from z3 import *
import itertools


def naive(literals, k):
    """
    Design your naive encoding of the at-most-k constraint.
    You are not allowed to create new variables for this encoding.
    The function returns the list of clauses that encode the at-most-k contraint.
    """
    clauses = []

    for t in itertools.combinations(range(len(literals)), k + 1):
        clauses += [Or([Not(literals[i]) for i in t])]

    return clauses


def sequential_counter(literals, k):
    """
    Implement the sequential counter encoding of the at-most-k constraint.
    You have to create new variables for this encoding.
    The function returns the list of clauses that encode the at-most-k constraint.
    """
    clauses = []

    n = len(literals)

    if k == n:
        return []
    elif k == 0:
        return [And([Not(x) for x in literals])]

    if literals[0] == Bool("x0"):
        new_lits = [[Bool("r1_%i_%i" % (i, j)) for j in range(k)] for i in range(n - 1)]
    else:
        new_lits = [[Bool("r2_%i_%i" % (i, j)) for j in range(k)] for i in range(n - 1)]

    clauses += [Or([Not(literals[0]), new_lits[0][0]])]

    for j in range(1, k):
        clauses += [Not(new_lits[0][j])]

    for i in range(1, n - 1):
        clauses += [And([Or([Not(literals[i]), new_lits[i][0]]), Or([Not(new_lits[i - 1][0]), new_lits[i][0]])])]
        for j in range(1, k):
            clauses += [And([Or([Not(literals[i]), Not(new_lits[i - 1][j - 1]), new_lits[i][j]]),
                            Or([Not(new_lits[i - 1][j]), new_lits[i][j]])])]
        clauses += [Or([Not(literals[i]), Not(new_lits[i - 1][k - 1])])]

    clauses += [Or([Not(literals[n - 1]), Not(new_lits[n - 2][k - 1])])]

    return clauses

# Is the performance difference between the two encodings significant?

""" Five input sizes were tested based on the value of n, which were n = 4, n = 10, n = 30, n = 100, and n = 500.
Some of these n values were used in multiple tests for testing when k was near 0, near n/2, and near n. The results 
listed below are in the form <(n, k) input>: <naive method passing time in seconds>, <sequential counter passing time 
in seconds>. Tests that showed no results within 10 minutes of processing are indicated with "timed out".
 
(4, 3): 0.008861, 0.007662
(10, 5): 0.012327, 0.008996
(30, 5): 2.227717, 0.015625
(30, 15): timed out, 0.015627
(30, 25): 2.113523, 0.015630
(100, 5): timed out, 0.288163
(100, 50): timed out, 4.581375
(100, 95): timed out, 0.294499
(500, 5): timed out, 3.974702
(500, 250): timed out, timed out

The sequential counter performed better than the naive method in all cases, and the ratio of time for the sequential
method compared to the naive method decreases rapidly as n increases. On small inputs (n at most 10) however, there is 
little difference in the passing time between the two methods. Both the naive method and sequential counter do worse on 
larger inputs where k is close to n/2 compared with when k is close to 0 or close to n (e.g. (30, 5) vs (30, 15) vs 
(30, 25) for the naive method, (100, 5) vs (100, 50) vs (100, 95) for the sequential counter).
 """

# ================================================================================
#  Do not modify below!
# ================================================================================
import time

def test(encoding, n, k):
    """
    The following test encodes the constraint of having exactly k variables true by
    encoding at-most-k over (X_1, .., X_n) and at-least-k:
    - at-most-k is encoded by the encoding function given as argument.
    - at-least-k is encoded by encoding at-most-(n-k) on the negation of the variables.
    """
    X = []
    for i in range(n):
        X += [Bool("x%d" % i)]
    s = Solver()
    at_most_k = encoding(X, k)
    at_least_k = encoding([Not(x) for x in X], n - k)
    # Add all the clauses to the solver
    for clause in at_most_k + at_least_k:
        s.add(clause)
    # Should print sat
    start = time.time()
    resp = s.check()
    end = time.time()
    if str(resp) == "sat":
        m = s.model()
        count_true = 0
        for x in X:
            try:
                if m.evaluate(x):
                    count_true +=1
            except Z3Exception:
                pass
        if count_true == k:
            print("PASSED in %fs" % (end - start))
        else:
            print("FAILED")
    else:
        print("FAILED")


def usage():
    print("Usage: python q3.py E N K")
    print("      - E is 0 to use naive encoding or 1 to use sequential counter encoding.")
    print("      - K and N two integers such that N >= K > 2.")

if __name__ == '__main__':
    if len(sys.argv) < 4:
        usage()
        exit(1)
    e, n, k = int(sys.argv[1]) == 0, int(sys.argv[2]), int(sys.argv[3])
    if not (n >= k > 2):
        usage()
        exit(1)
    if e:
        test(naive, n, k)
    else:
        test(sequential_counter, n, k)
