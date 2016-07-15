"""
Global Z3 solver for use by other files.
"""
from contextlib import contextmanager
import z3

import predicate

class MySolver(object):
    def __init__(self):
        self._solver = z3.Solver()

    def push(self):
        """Push solver state."""
        self._solver.push()

    def pop(self):
        """Pop solver state."""
        self._solver.pop()

    def add(self, syndra_predicate):
        """Add an assertion to the solver state.

        Arguments:
            syndra_predicate : Syndra predicate, instance of predicate.Predicate
        """
        z3_predicate = syndra_predicate.get_predicate()
        self._solver.add(z3_predicate)

    def add_z3(self, z3_predicate):
        """Add an assertion to the solver state.

        Arguments:
            z3_predicate : Z3-friendly predicate or boolean
        """
        return self._solver.add(z3_predicate)

    def model(self):
        """Return a model for the current solver state.

        Returns:
            : Z3 model.
        """
        z3model = self._solver.model()
        return z3model

    def check(self):
        """Check satisfiability of current satisfiability state.

        Returns:
            : boolean -- True if sat, False if unsat
        """
        # check() returns either unsat or sat
        result = self._solver.check()
        # sat.r is 1, unsat.r is -1
        return result.r > 0

    @contextmanager
    def context(self):
        """To do something in between a push and a pop, use a `with context()`.
        This is especially useful for avoiding bugs caused by forgetting pop().
        """
        self.push()
        yield
        self.pop()

    def quick_check(self, syndra_predicate):
        """Add an assertion only temporarily, and check sat."""
        with self.context():
            self.add(syndra_predicate)
            return self.check()

    def quick_check_sat(self, syndra_predicate):
        return self.quick_check(syndra_predicate)

    def quick_check_valid(self, syndra_predicate):
        """Check that a predicate is valid - that its negation is unsat."""
        with self.context():
            if not self.check():
                return True # The predicate is implied by the unsat env
            self.add(predicate.Not(syndra_predicate))
            return not self.check() # if negation is unsat, then it's valid

solver = MySolver()
