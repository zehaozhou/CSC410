#!/usr/bin/env python3.7

import sys

def solve(x,y):
    if x == 0 or y == 0 or x == y:
        return "1"

    p2 = [(1,2),(2,1)]

    for i in range(x+1):
        for j in range(y+1):
            check = [reachable(i, j, cell[0], cell[1]) for cell in p2]
            if not any(check):
                p2.append((i,j))
    
    if (x, y) in p2:
        return "2"
    return "1"

def reachable(a, b, x, y):
    return a == x or b == y or a-x == b-y

if __name__ == '__main__':

    if len(sys.argv) < 3:
        exit(1)

    x = int(sys.argv[1])
    y = int(sys.argv[2])
    print(solve(x,y))

    # for x in range(60):
    #     for y in range(x):
    #         if solve(x,y) == "2":
    #             print((x,y))