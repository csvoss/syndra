# This thing should be an interface implemented by a bunch of different
# subclasses; combine those subclasses together to make a predicate, and then
# allow the predicate to be executed / checked / model-got / whatever we want by
# Z3. This is one abstraction layer higher than the above Z3 definitions are.
# Probably the subclasses should only return Z3 formulae, not make any
# assertions; then, Predicate can manipulate those formulae into an assertion.

"""
TODO: Variable, Interpretation.
(declare-datatypes () ((Variable (variable (get-varname Int)))))
(declare-fun interpretation (Variable) Identifier)
"""

class Predicate(object):
    """Parent class which all Predicates will subclass.

    Contains implementations of some z3-related functionality. Subclasses will
    override get_predicate."""

    def __init__(self):
        self.asserted_yet = False
        self.solver = z3.Solver()

    def get_predicate(self):
        raise NotImplementedError("Implement get_predicate in subclasses.")

    def assert_over(self, model):
        pass
        self.asserted_yet = True

    def check_sat(self, model):
        if not self.asserted_yet:
            self.assert_over(model)
        pass

    def get_model(self, model):
        if not self.asserted_yet:
            self.assert_over(model)
        pass

    def get_all_models(self, model):
        if not self.asserted_yet:
            self.assert_over(model)
        pass


class Top(Predicate):
    def __init__(self):
        pass

    def get_predicate(self, interpretation):
        return True

class Bottom(Predicate):
    def __init__(self):
        pass

    def get_predicate(self, interpretation):
        return False

class Equal(Predicate):
    """
    ; Equality of variables x and y.
    (declare-const x Variable)
    (declare-const y Variable)
    (assert (= (get-varname x) (get-varname y)))
    """

    def __init__(self, x, y):
        # TODO: ensure that x and y are both of the right type (Variable)
        self.x = x
        self.y = y

    def get_predicate(self, interpretation):
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

    def get_predicate(self, interpretation):
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

    def get_predicate(self, interpretation):
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

    def get_predicate(self, interpretation):
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

    def get_predicate(self, interpretation):
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

    def get_predicate(self, interpretation):
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

    def get_predicate(self, interpretation):
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

    def get_predicate(self, interpretation):
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

    def get_predicate(self, interpretation):
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

    def get_predicate(self, interpretation):
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

    def get_predicate(self, interpretation):
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

    def get_predicate(self, interpretation):
        pass
