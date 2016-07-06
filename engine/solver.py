"""
Global Z3 solver for use by other files.
"""
from contextlib import contextmanager
import z3

class MySolver(object):

    def __init__(self):
        self._solver = z3.Solver()
        self._model_cached = False
        # TODO: Initialize datatypes here

    # TODO: Port the below functions to here as methods

    def push(self):
        """Push solver state."""
        self._solver.push()

    def pop(self):
        """Pop solver state."""
        self._model_cached = False
        self._solver.pop()

    def add(self, assertion):
        """Add an assertion to the solver state.

        Arguments:
            assertion : Z3-friendly predicate or boolean
        """
        self._model_cached = False
        return self._solver.add(assertion)

    def model(self):
        """Return a model for the current solver state.

        Returns:
            : Z3 model. TODO: Modify this all so that it returns sets, etc.
        """
        if not self._model_cached:
            self.check()  # Must check in order to refresh model!
        z3model = self._solver.model()
        return z3model

    def check(self):
        """Check satisfiability of current satisfiability state.

        Returns:
            : boolean -- True if sat, False if unsat
        """
        # check() returns either unsat or sat
        result = self._solver.check()
        self._model_cached = True
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

    def quick_check(self, assertion):
        """Add an assertion only temporarily, and check sat."""
        with self.context():
            self.add(assertion)
            return self.check()

    def quick_check_implied(self, assertion):
        """Add an assertion only temporarily, and check that the assertion
        is valid -- that is, necessarily true -- given current state."""
        with self.context():
            # False implies anything, so return True if we start unsat.
            if not self.check():
                return True
            self.add(z3.Not(assertion))
            # If we're satisfiable after adding NOT(assertion), that means
            # the assertion was not implied.
            if self.check():
                return False   # satisfiable NOT(x) --> invalid x
            else:
                return True  # unsatisfiable NOT(x) --> valid x

solver = MySolver()
