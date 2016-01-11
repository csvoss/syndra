# This thing should be an interface implemented by a bunch of different
# subclasses; combine those subclasses together to make a predicate, and then
# allow the predicate to be executed / checked / model-got / whatever we want by
# Z3. This is one abstraction layer higher than the above Z3 definitions are.
# Probably the subclasses should only return Z3 formulae, not make any
# assertions; then, Predicate can manipulate those formulae into an assertion.

from model import Identifier, Pregraph, AtomicAction, Action, Postgraph, Model
from z3 import *
from z3_helpers import *

DEBUG = False

Variable = Datatype('Variable')
Variable.declare('variable', ('get_varname', IntSort()))
Variable = Variable.create()

class Predicate(object):
    """Parent class which all Predicates will subclass.

    Contains implementations of some z3-related functionality. Subclasses will
    override get_predicate."""

    def __init__(self, model):
        self.solver = Solver()
        self.model = model
        self.interpretation = Function('interpretation', Variable, Identifier)

        self._asserted_yet = False
        self.model.add_assertions(self.solver)

    def get_predicate(self):
        raise NotImplementedError("Implement get_predicate in subclasses.")

    def _assert_over(self):
        self.solver.add(self.get_predicate())

        self._asserted_yet = True

    def check_sat(self):
        if not self._asserted_yet:
            self._assert_over()

        output = self.solver.check()
        if DEBUG:
            print output
        return output

    def get_model(self):
        """Raises Z3Exception if the model is not available."""

        if not self._asserted_yet:
            self._assert_over()

        output = self.solver.model()
        if DEBUG:
            print output
        return output


    def get_models(self):
        if not self._asserted_yet:
            self._assert_over()

        # http://stackoverflow.com/questions/13395391/z3-finding-all
        # TODO.
        return ["Placeholder"]

class Top(Predicate):
    def get_predicate(self):
        return True

class Bottom(Predicate):
    def get_predicate(self):
        return False

class Equal(Predicate):
    """
    ; Equality of variables x and y.
    (declare-const x Variable)
    (declare-const y Variable)
    (assert (= (get-varname x) (get-varname y)))
    """

    def __init__(self, x, y, *args):
        # TODO: ensure that x and y are both of the right type (Variable)
        super(self, Predicate).__init__(self, *args)
        self.x = x
        self.y = y

    def get_predicate(self):
        # TODO: Can't find z3 'equals'
        return True

class Labeled(Predicate):
    """
    ; Variable has specific label.
    (declare-const x Variable)
    (declare-const Label Int)
    (assert (= (get-label (interpretation x)) Label))
    """

    def __init__(self, x):
        # TODO: ensure that x is of the right type (Variable)
        self.x = x

    def get_predicate(self):
        # TODO.
        return True


class PreParent(object):
    """
    ; Variable x has child y.
    (declare-const x Variable)
    (declare-const y Variable)
    (assert (graph-parents (interpretation x) (interpretation y)))
    """
    def __init__(self, x, y):
        pass

    def get_predicate(self):
        pass

class PostParent(object):
    """
    ; "Bar" of "Variable x has child y", which seems to indicate that x has
    ; child y only in the second graph produced by G combined with A.
    ; This is the postcondition!
    (declare-const x Variable)
    (declare-const y Variable)
    (assert (graph-2-parents (interpretation x) (interpretation y)))
    """
    def __init__(self, x, y):
        # TODO: ensure that x and y are both of the right type (Variable)
        self.x = x
        self.y = y

    def get_predicate(self):
        pass

class DoParent(object):
    """
    ; "Do" of "Variable x has child y".
    (declare-const x Variable)
    (declare-const y Variable)
    (assert (actions-has (parent-action (interpretation x) (interpretation y))))
    """
    def __init__(self, x, y):
        # TODO: ensure that x and y are both of the right type (Variable)
        self.x = x
        self.y = y

    def get_predicate(self):
        pass

class PreLink(object):
    """
    ; Variable x links to variable y.
    (declare-const x Variable)
    (declare-const y Variable)
    (assert (graph-links (interpretation x) (interpretation y)))
    """
    def __init__(self, x, y):
        # TODO: ensure that x and y are both of the right type (Variable)
        self.x = x
        self.y = y

    def get_predicate(self):
        pass

class PostLink(object):
    """
    ; "Bar" of Variable x links to variable y; Again a postcondition.
    (declare-const x Variable)
    (declare-const y Variable)
    (assert (graph-2-links (interpretation x) (interpretation y)))
    """
    def __init__(self, x, y):
        # TODO: ensure that x and y are both of the right type (Variable)
        self.x = x
        self.y = y

    def get_predicate(self):
        pass

class DoLink(object):
    """
    ; "Do" of "Variable x links to variable y".
    (declare-const x Variable)
    (declare-const y Variable)
    (assert (actions-has (link-action (interpretation x) (interpretation y))))
    """
    def __init__(self, x, y):
        # TODO: ensure that x and y are both of the right type (Variable)
        self.x = x
        self.y = y

    def get_predicate(self):
        pass

class DoUnlink(object):
    """
    ; "Do" of "Variable x unlinks to variable y".
    (declare-const x Variable)
    (declare-const y Variable)
    (assert (actions-has (unlink-action (interpretation x) (interpretation y))))
    """
    def __init__(self, x, y):
        # TODO: ensure that x and y are both of the right type (Variable)
        self.x = x
        self.y = y

    def get_predicate(self):
        pass

class PreHas(object):
    """
    ; "Has" of variable x.
    (declare-const x Variable)
    (assert (graph-has (interpretation x)))
    """
    def __init__(self, x):
        # TODO: ensure that x has the right type (Variable)
        self.x = x

    def get_predicate(self):
        pass

class PostHas(object):
    """
    ; "Bar" of "Has" of x. Again, a postcondition.
    (declare-const x Variable)
    (assert (graph-2-has (interpretation x)))
    """
    def __init__(self, x):
        # TODO: ensure that x has the right type (Variable)
        self.x = x

    def get_predicate(self):
        pass

class Add(object):
    """
    ; "Add" of variable x, and "Rem" of variable x. Given that these are
    ; preconditions, as written in the L paper, I'm not convinced that
    ; we gain anything by implementing them as opposed to using has(x) and !has(x).
    """
    def __init__(self, x):
        # TODO: ensure that x has the right type (Variable)
        self.x = x

    def get_predicate(self):
        pass
