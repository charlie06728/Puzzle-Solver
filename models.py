'''
All models need to return a CSP object, and a list of lists of Variable objects
representing the board. The returned list of lists is used to access the
solution.

For example, after these three lines of code

    csp, var_array = warehouse_binary_ne_grid(board)
    solver = BT(csp)
    solver.bt_search(prop_FC, var_ord)

var_array[0][0].get_assigned_value() should be the correct value in the top left
cell of the warehouse.

The grid-only models do not need to encode the cage constraints.

1. warehouse_binary_ne_grid
    - A model of the warehouse problem w/o room constraints built using only
      binary not-equal constraints for the row/column constraints.

2. warehouse_nary_ad_grid
    - A model of the warehouse problem w/o room constraints built using only n-ary
      all-different constraints for the row/column constraints.

3. warehouse_full_model
    - A model of the warehouse problem built using either the binary not-equal or n-ary
      all-different constraints for the row/column constraints.
'''
from cspbase import *
from typing import *
import itertools

DEBUG = False

def warehouse_binary_ne_grid(warehouse_grid):
    csp = CSP("binary")
    n = warehouse_grid[0][0]
    var_array = init_board(n, csp)

    # Compute the satisfying tuples for binary constraints
    sat = []

    for x in range(1, n + 1):
        for y in range(1, n + 1):
            if x != y:
                sat.append([x, y])

    binary_constraint_generator(n, csp, var_array, sat)
    return csp, var_array


def warehouse_nary_ad_grid(warehouse_grid):
    csp = CSP("n_array")
    n = warehouse_grid[0][0]
    var_array = init_board(n, csp)

    temp = itertools.permutations([x for x in range(1, n + 1)])
    sat = []
    for item in temp:
        sat.append(list(item))

    n_ary_constraint_generator(n, csp, var_array, sat)
    return csp, var_array


def warehouse_full_model(warehouse_grid):
    csp, board = warehouse_binary_ne_grid(warehouse_grid)
    constraint_generator_for_building(csp, warehouse_grid[1:], board)
    # csp = csp_pruning(csp)

    if DEBUG:
        acc = 0
        for con in csp.get_all_cons():
            acc += len(con.sat_tuples)

    return csp, board_converter(board)


def constraint_generator_for_building(csp: CSP, grid: List[List], board: List[List]) -> None:
    """Generate constraint for buildings
    """
    n = len(board)
    for i in range(len(grid)):
        vars: List[Variable] = []
        for j in range(len(grid[i]) - 2):
            num = grid[i][j]
            temp = str(num)
            coord = coordinate_converter(int(temp[0]), int(temp[1]), n)
            vars.append(board[coord[0]][coord[1]])

        operator = grid[i][len(grid[i]) - 2]
        value = grid[i][len(grid[i]) - 1]
        sat = []

        # Generate constraint
        con = Constraint("c" + str(vars), vars)
        if operator == 1:
            # The sum of these variables should be equal to the given value
            lst = [var.domain() for var in vars]
            combinations = itertools.product(*lst)
            for item in combinations:
                if sum(item) == value:
                    sat.append(list(item))
        elif operator == 0:
            # The value in this grid must equal to the given value
            # if value == n:
            sat.append([value])
        elif operator == 2:
            # The min value in these grid must be greater or equal to the given value
            lst = [var.cur_domain() for var in vars]
            combinations = itertools.product(*lst)
            for item in combinations:
                if min(item) >= value:
                    sat.append(list(item))
        elif operator == 3:
            # The max value in these grid must be smaller or equal to the given value
            lst = [var.cur_domain() for var in vars]
            combinations = itertools.product(*lst)
            for item in combinations:
                if max(item) <= value:
                    sat.append(list(item))

        # add satisfiable values to the constraint
        con.add_satisfying_tuples(sat)
        csp.add_constraint(con)


def coordinate_converter(x: int, y: int, n: int) -> Tuple[int, int]:
    """Convert the coordinate from 1 base on top left corner to 0 base bottom left corner
    """
    new_x = n - x
    new_y = y - 1
    return (new_x, new_y)


def init_board(n: int, csp: CSP) -> List[List]:
    """initialize the board with variables instance
    """
    # Assign variables to the csp, variables' name correspond to coordinate
    var_array = []
    for _ in range(n):
        var_array.append([])

    dom = [x for x in range(1, n + 1)]

    for i in range(n):
        for j in range(n):
            v = Variable(str(n - i) + str(j + 1), dom)
            var_array[i].append(v)
            csp.add_var(v)
    return var_array


def n_ary_constraint_generator(n: int, csp: CSP, board: List[List[Variable]],
                               sat: List[List]) -> None:
    """Generate constraints for n array method
    """
    for row in range(n):
        con = Constraint("row" + str(row), board[row])
        con.add_satisfying_tuples(sat)
        csp.add_constraint(con)

    for column in range(n):
        col_elements = _get_column(column, board)
        con = Constraint("column" + str(column), col_elements)
        con.add_satisfying_tuples(sat)
        csp.add_constraint(con)


def _get_column(col: int, board: List[List]) -> List:
    res_col = []
    for i in range(len(board)):
        res_col.append(board[i][col])
    return res_col


def binary_constraint_generator(n: int, csp: CSP, board: List[List[Variable]],
                                sat: List[List]) -> None:
    """Generate binary constraint and add it to the CSP
    """
    for i in range(n):
        for j in range(n):
            _expand(csp, i, j, board, n, sat)


def _expand(csp: CSP, x: int, y: int, board: List[List[Variable]], n: int, sat: List[List]) -> None:
    """
    Only goes forward, that said goes from i to i + 1 and from j to j + 1

    All constraints have the same satisfying tuples
    """
    for i in range(x + 1, n):
        # fix y and change x
        con = Constraint(str(x) + str(y) + str(i) + str(y), [board[x][y], board[i][y]])
        con.add_satisfying_tuples(sat)
        csp.add_constraint(con)

    for i in range(y + 1, n):
        # fix x and change y
        con = Constraint(str(x) + str(y) + str(i) + str(y), [board[x][y], board[x][i]])
        con.add_satisfying_tuples(sat)
        csp.add_constraint(con)


def board_converter(board: List[List[Variable]]) -> List[List[Variable]]:
    """designed to catch up the revision made in handout that change the description of boards
    """
    n = len(board)
    new_boards = []

    for i in range(n):
        new_boards.append([])
        for j in range(n):
            new_boards[i].append(board[n - j - 1][n - i - 1])
    return new_boards

def csp_pruning(csp: CSP) -> CSP:
    """Simply the constraints in given csp and return a new csp
    """
    acc = 0
    new_csp = CSP("csp")
    old_cons: List[Constraint] = csp.get_all_cons()
    vars = csp.get_all_vars()
    for var in vars:
        new_csp.add_var(var)
    for con in old_cons:
        con_vars: List[Variable] = con.get_scope()
        new_con = Constraint(con.name, con_vars)
        new_csp.add_constraint(new_con)
        sat_tups = list(con.sat_tuples.keys())
        new_sats = []
        for curr_con in old_cons:
            var_lst = []
            for i in range(len(con_vars)):
                curr_var = con_vars[i]
                if curr_var in curr_con.get_scope():
                    var_lst.append((curr_var, i))
            if len(var_lst) == len(curr_con.get_scope()):
                # pruning
                for sat in sat_tups:
                    if curr_con.check([sat[t[1]] for t in var_lst]):
                        new_sats.append(list(sat))
                        acc += 1
        new_con.add_satisfying_tuples(new_sats)
    return new_csp


