"""
Global Z3 solver for use by other files.
"""

from contextlib import contextmanager
from z3 import Solver

global_solver = Solver()

class Solver(object):

    def __init__(self):
        self._solver = Solver()
        # TODO: Initialize datatypes here

    # TODO: Port the below functions to here as methods

def push():
    """Push solver state."""
    global_solver.push()

def pop():
    """Pop solver state."""
    global_solver.pop()

def add(assertion):
    """Add an assertion to the solver state.

    Arguments:
        assertion : Z3-friendly predicate or boolean
    """
    return global_solver.add(assertion)

def model():
    """Return a model for the current solver state.

    Returns:
        : Z3 model. TODO: Modify this all so that it returns sets, etc.
    """
    return global_solver.model()

def check():
    """Check satisfiability of current satisfiability state.

    Returns:
        : boolean -- True if sat, False if unsat
    """
    # check() returns either unsat or sat
    # sat.r is 1, unsat.r is -1
    return global_solver.check().r > 0

@contextmanager
def context():
    """To do something in between a push and a pop, use a `with context()`."""
    push()
    yield
    pop()

def quick_check(assertion):
    """Add an assertion only temporarily, and check sat."""
    with context():
        add(assertion)
        return check()
