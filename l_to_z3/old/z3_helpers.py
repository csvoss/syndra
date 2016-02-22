from z3 import *

# Helper functions not defined by Z3.

def Iff(a, b):
    return Not(Xor(a, b))

def Equals(a, b):
    return a == b
