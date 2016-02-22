"""
Global Z3 solver for use by other files.
"""

from contextlib import contextmanager
from z3 import Solver

global_solver = Solver()

def push():
    return global_solver.push()

def pop():
    return global_solver.pop()

def add(assertion):
    return global_solver.add(assertion)

def model():
    return global_solver.model()

def check():
    return global_solver.check()

@contextmanager
def context():
    push()
    yield
    pop()

def quick_check(assertion):
    with context():
        add(assertion)
        return check()
