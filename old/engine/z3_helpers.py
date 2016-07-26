import z3

# Helper functions not defined by Z3.

def Iff(a, b):
    return z3.Not(z3.Xor(a, b))

def Equals(a, b):
    return a == b
