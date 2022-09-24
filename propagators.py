from typing import *
from cspbase import Constraint, Variable
# Look for #IMPLEMENT tags in this file. These tags indicate what has
# to be implemented to complete problem solution.

'''This file will contain different constraint propagators to be used within
   bt_search.

A propagator is a function with the following template:
    propagator(csp, newly_instaniated_variable=None)
        ...
        returns (True/False, [(Variable, Value),(Variable,Value),...])

    csp is a CSP object, which the propagator can use to get access to
    the variables and constraints of the problem

    newly_instaniated_variable is an optional argument;
        if it is not None, then:
            newly_instaniated_variable is the most recently assigned variable
        else:
            the propagator was called before any assignment was made

    the prop returns True/False and a list of variable-value pairs;
        the former indicates whether a DWO did NOT occur,
        and the latter specifies each value that was pruned

The propagator SHOULD NOT prune a value that has already been pruned
or prune a value twice

In summary, this is what the propagator must do:

    If newly_instantiated_variable = None

        for plain backtracking;
            we do nothing...return true, []

        for forward checking;
            we check all unary constraints of the CSP

        for gac;
            we establish initial GAC by initializing the GAC queue
            with all constaints of the CSP


     If newly_instantiated_variable = a variable V

         for plain backtracking;
            we check all constraints with V that are fully assigned
            (use csp.get_cons_with_var)

         for forward checking;
            we check all constraints with V that have one unassigned variable

         for gac;
            we initialize the GAC queue with all constraints containing V
   '''


def prop_BT(csp, newVar=None):
    if not newVar:
        return True, []
    for c in csp.get_cons_with_var(newVar):
        if c.get_n_unasgn() == 0:
            vals = []
            vars = c.get_scope()
            for var in vars:
                vals.append(var.get_assigned_value())
            if not c.check(vals):
                return False, []
    return True, []


def prop_FC(csp, newVar=None):
    cons: List[Constraint] = csp.get_all_cons()
    lst = []
    prune_lst = []
    flag = False

    if not newVar:
        for con in cons:
            if len(con.get_scope()) == 1:
                # Under unary situation, check the values in variable's domain
                lst.append(con)
    else:
        # Initialize the que with constraints containing var
        temp = csp.get_cons_with_var(newVar)
        for con in temp:
            if con.get_n_unasgn() == 1:
                lst.append(con)

    # Propagate
    for con in lst:
        var: Variable = con.get_unasgn_vars()[0]
        for val in var.cur_domain():
            vals = []
            var.assign(val)
            for variable in con.get_scope():
                vals.append(variable.get_assigned_value())
            var.unassign()
            if not con.check(vals):
                var.prune_value(val)
                prune_lst.append((var, val))
            else:
                flag = True
        if not flag:
            return (False, prune_lst)
        else:
            flag = False
    return (True, prune_lst)


def prop_GAC(csp, newVar=None):
    prune_lst = []
    if not newVar:
        # Initialize the que with all the constraints in csp
        que = csp.get_all_cons()
    else:
        # Initialize the que with constraints containing V
        que = csp.get_cons_with_var(newVar)

    # Propagate
    while que != []:
        # pop a constraint into a variable
        curr = que.pop(0)

        for var in curr.get_scope():
            for val in var.cur_domain():
                if not curr.has_support(var, val):
                    var.prune_value(val)
                    prune_lst.append((var, val))

                    if var.cur_domain() == []:
                        # DWO
                        return (False, prune_lst)
                    else:
                        for con in csp.get_cons_with_var(var):
                            if con not in que:
                                que.append(con)
    return (True, prune_lst)






