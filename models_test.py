from models import *
from propagators import *

'''
Note: there could be more than one solution for the same board in these tests

Expectations:
Default BT:
The first two cases are expected to be solved in a few seconds
The last two cases are expected to be solved in a few minutes

With FC:
All cases are expected to be solved in a few seconds

With GAC:
All cases are expected to be solved in a few seconds but faster than FC

'''
small_boards = [
[[3],[11,12,2,2],[21,31,32,1,6],[13,33,22,23,1,7]],
[[4],[11,0,1],[12,21,22,31,2,2],[41,42,3,3],[32,23,33,43,1,11],[13,14,24,34,1,10],[44,0,2]],
[[4],[11,0,2],[12,13,3,4],[14,24,1,3],[21,22,23,31,33,1,11],[41,0,4],[32,42,43,2,1],[34,44,1,3]],
]

boards = [
    [[3],[11,12,2,2],[21,31,32,1,6],[13,33,22,23,1,7]],
    [[4], [11, 0, 1], [12, 21, 22, 31, 2, 2], [41, 42, 3, 3], [32, 23, 33, 43, 1, 11], [13, 14, 24, 34, 1, 10],
     [44, 0, 2]],
    [[5], [11, 21, 31, 32, 33, 1, 15], [12, 13, 14, 1, 9], [22, 0, 3], [23, 24, 25, 15, 2, 1], [41, 51, 52, 53, 1, 8],
     [42, 43, 44, 34, 54, 2, 2], [35, 45, 55, 3, 5]],
    [[5], [11, 12, 13, 23, 1, 12], [21, 22, 31, 41, 1, 16], [32, 42, 52, 51, 3, 3], [33, 43, 53, 54, 55, 45, 35, 1, 24],
     [24, 34, 44, 2, 2], [14, 15, 25, 3, 3]],
]

large_boards = [
    [[5], [11, 21, 31, 32, 33, 1, 15], [12, 13, 14, 1, 9], [22, 0, 3], [23, 24, 25, 15, 2, 1], [41, 51, 52, 53, 1, 8],
     [42, 43, 44, 34, 54, 2, 2], [35, 45, 55, 3, 5]],
    [[5], [11, 12, 13, 23, 1, 12], [21, 22, 31, 41, 1, 16], [32, 42, 52, 51, 3, 3], [33, 43, 53, 54, 55, 45, 35, 1, 24],
     [24, 34, 44, 2, 2], [14, 15, 25, 3, 3]],
    [[8], [11, 12, 22, 32, 2, 2], [21, 31, 41, 51, 1, 17], [61, 71, 81, 3, 7], [42, 43, 52, 62, 1, 17],
     [72, 82, 73, 83, 53, 63, 3, 6], [44, 0, 4],
     [13, 14, 23, 24, 25, 1, 24], [33, 34, 35, 36, 26, 1, 18], [54, 64, 74, 84, 2, 1], [15, 16, 17, 2, 1],
     [18, 28, 3, 6], [27, 37, 38, 48, 3, 6],
     [45, 46, 47, 55, 56, 65, 75, 1, 35], [57, 66, 67, 1, 12], [76, 77, 78, 68, 58, 2, 5], [85, 0, 4],
     [86, 87, 88, 3, 8]]
]

if __name__ == "__main__":
    print("Testing for warehouse_binary_ne_grid: ")
    for b in large_boards:
        print("Solving board...")

        csp, var_array = warehouse_binary_ne_grid(b)
        solver = BT(csp)
        print("\n")
        solver.bt_search(prop_BT)
        print("Solution:")

        for row in var_array:
            print([var.get_assigned_value() for var in row])
        print("\n")

    print("Testing for warehouse_nary_ad_grid: ")
    for b in small_boards:
        print("Solving board...")

        csp, var_array = warehouse_nary_ad_grid(b)
        solver = BT(csp)
        print("\n")
        solver.bt_search(prop_BT)
        print("Solution:")

        for row in var_array:
            print([var.get_assigned_value() for var in row])
        print("\n")

    for b in boards:
        print("Solving board...")

        csp, var_array = warehouse_full_model(b)
        solver = BT(csp)
        print("\n")

        # print("Back-Tracking Search (w/o constraint propagation)")
        # solver.bt_search(prop_BT)

        print("Back-Tracking Search (w/ forward checking)")
        solver.bt_search(prop_FC)

        # print("Back-Tracking Search (w/ generalized arc-consistency)")
        # solver.bt_search(prop_GAC)

        print("Solution:")

        for row in var_array:
            print([var.get_assigned_value() for var in row])
        print("\n")

    print("end")
