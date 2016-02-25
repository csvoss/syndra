"""
L's atomic predicate: constrains graph-action pairs.

This thing should be an interface implemented by a bunch of different
subclasses; combine those subclasses together to make a predicate, and then
allow the predicate to be executed / checked / model-got / whatever we want by
Z3. This is one abstraction layer higher than the above Z3 definitions are.
Probably the subclasses should only return Z3 formulae, not make any assertions;
then, Predicate can manipulate those formulae into an assertion.

Refer to pg. 7 of the L description.
"""

class AtomicPredicate(object):
    """Parent class which all AtomicPredicates will subclass.

    Contains implementations of some z3-related functionality. Subclasses will
    override get_predicate.
    """

    def __init__(self):
        pass

    def _assert(self, submodel, interpretation):
        # submodel: representation of a set of graph, action pairs
        raise NotImplementedError("Implement _assert in subclasses.")


class Top(AtomicPredicate):
    def get_predicate():
        return True


class Bottom(AtomicPredicate):
    def get_predicate():
        return False


class Equal(AtomicPredicate):
    """
    ; Equality of variables x and y.
    (declare-const x Variable)
    (declare-const y Variable)
    (assert (= (get-varname x) (get-varname y)))
    """
    def __init__(self, x, y, *args):
        super(Equal, self).__init__(*args)
        ensure_variable(x)
        ensure_variable(y)
        self.x = x
        self.y = y

    def get_predicate():
        return (z3_accessor(Variable.get_varname, self.x) ==
                z3_accessor(Variable.get_varname, self.y))

class Labeled(AtomicPredicate):
    """
    ; Variable has specific label.
    (declare-const x Variable)
    (declare-const Label Int)
    (assert (= (get-label (interpretation x)) Label))
    """
    def __init__(self, x, label, *args):
        super(Labeled, self).__init__(*args)
        ensure_variable(x)
        self.label = label
        self.x = x


    def get_predicate():
        return (z3_accessor(Node.label, self.interpretation(self.x)) ==
                self.label)


class PreParent(AtomicPredicate):
    """
    ; Variable x has child y.
    (declare-const x Variable)
    (declare-const y Variable)
    (assert (graph-parents (interpretation x) (interpretation y)))
    """
    def __init__(self, x, y, *args):
        super(PreParent, self).__init__(*args)
        ensure_variable(x)
        ensure_variable(y)
        self.x = x
        self.y = y

    def get_predicate():
        return self.pregraph.parents(
            self.interpretation(self.x), self.interpretation(self.y))

class PostParent(AtomicPredicate):
    """
    ; "Bar" of "Variable x has child y", which seems to indicate that x has
    ; child y only in the second graph produced by G combined with A.
    ; This is the postcondition!
    (declare-const x Variable)
    (declare-const y Variable)
    (assert (graph-2-parents (interpretation x) (interpretation y)))
    """
    def __init__(self, x, y, *args):
        super(PostParent, self).__init__(*args)
        ensure_variable(x)
        ensure_variable(y)
        self.x = x
        self.y = y

    def get_predicate():
        return self.postgraph.parents(
            self.interpretation(self.x), self.interpretation(self.y))

class DoParent(AtomicPredicate):
    """
    ; "Do" of "Variable x has child y".
    (declare-const x Variable)
    (declare-const y Variable)
    (assert (actions-has (parent-action (interpretation x) (interpretation y))))
    """
    def __init__(self, x, y, *args):
        super(DoParent, self).__init__(*args)
        ensure_variable(x)
        ensure_variable(y)
        self.x = x
        self.y = y

    def get_predicate():
        return self.action.has(
            AtomicAction.parent_action(
                self.interpretation(self.x), self.interpretation(self.y)))

class PreLink(AtomicPredicate):
    """
    ; Variable x links to variable y.
    (declare-const x Variable)
    (declare-const y Variable)
    (assert (graph-links (interpretation x) (interpretation y)))
    """
    def __init__(self, x, y, *args):
        super(PreLink, self).__init__(*args)
        ensure_variable(x)
        ensure_variable(y)
        self.x = x
        self.y = y

    def get_predicate():
        return self.pregraph.links(
            self.interpretation(self.x), self.interpretation(self.y))

class PostLink(AtomicPredicate):
    """
    ; "Bar" of Variable x links to variable y; Again a postcondition.
    (declare-const x Variable)
    (declare-const y Variable)
    (assert (graph-2-links (interpretation x) (interpretation y)))
    """
    def __init__(self, x, y, *args):
        super(PostLink, self).__init__(*args)
        ensure_variable(x)
        ensure_variable(y)
        self.x = x
        self.y = y

    def get_predicate():
        return self.postgraph.links(
            self.interpretation(self.x), self.interpretation(self.y))

class DoLink(AtomicPredicate):
    """
    ; "Do" of "Variable x links to variable y".
    (declare-const x Variable)
    (declare-const y Variable)
    (assert (actions-has (link-action (interpretation x) (interpretation y))))
    """
    def __init__(self, x, y, *args):
        super(DoLink, self).__init__(*args)
        ensure_variable(x)
        ensure_variable(y)
        self.x = x
        self.y = y

    def get_predicate():
        return self.action.has(
            AtomicAction.link_action(
                self.interpretation(self.x), self.interpretation(self.y)))

class DoUnlink(AtomicPredicate):
    """
    ; "Do" of "Variable x unlinks to variable y".
    (declare-const x Variable)
    (declare-const y Variable)
    (assert (actions-has (unlink-action (interpretation x) (interpretation y))))
    """
    def __init__(self, x, y, *args):
        super(DoUnlink, self).__init__(*args)
        ensure_variable(x)
        ensure_variable(y)
        self.x = x
        self.y = y

    def get_predicate():
        return self.action.has(
            AtomicAction.unlink_action(
                self.interpretation(self.x), self.interpretation(self.y)))

class PreHas(AtomicPredicate):
    """
    ; "Has" of variable x.
    (declare-const x Variable)
    (assert (graph-has (interpretation x)))
    """
    def __init__(self, x, *args):
        super(PreHas, self).__init__(*args)
        ensure_variable(x)
        self.x = x

    def get_predicate():
        return self.pregraph.has(
            self.interpretation(self.x))

class PostHas(AtomicPredicate):
    """
    ; "Bar" of "Has" of x. Again, a postcondition.
    (declare-const x Variable)
    (assert (graph-2-has (interpretation x)))
    """
    def __init__(self, x, *args):
        super(PostHas, self).__init__(*args)
        ensure_variable(x)
        self.x = x

    def get_predicate():
        return self.postgraph.has(
            self.interpretation(self.x))


class Add(AtomicPredicate):
    """
    Add a node.
    """
    def __init__(self, x, *args):
        super(Add, self).__init__(*args)
        ensure_variable(x)
        self.x = x

    def get_predicate():
        return (self.action.has(AtomicAction.add_action(self.interpretation(x)))
            and not self.pregraph.has(self.interpretation(x)))

class Rem(AtomicPredicate):
    """
    Remove a node.
    """
    def __init__(self, x, *args):
        super(Rem, self).__init__(*args)
        ensure_variable(x)
        self.x = x

    def get_predicate():
        return (self.action.has(AtomicAction.rem_action(self.interpretation(x)))
            and self.pregraph.has(self.interpretation(x)))



# Helper functions.

def z3_accessor(func, item):
    """Apply func and read out the accessed value of a z3 datatype, if the
    value for that accessor was an IntSort().

    Arguments:
        func :: a z3 accessor function
        item :: a z3 datatype instance
    Returns:
        :: long - the accessed value
    """
    return func(item).children()[0].children()[0].as_long()

def ensure_variable(thing):
    """Raise ValueError if thing is not an instance of z3 Variable."""
    try:
        assert thing.sort() == Variable
    except (AttributeError, AssertionError):
        raise ValueError("Arguments must be z3 instances of Variable.")

def ensure_atomic_predicate(thing):
    """Raise ValueError if thing is not an instance of AtomicPredicate."""
    if not isinstance(thing, AtomicPredicate):
        raise ValueError("Arguments must be instances of AtomicPredicate.")
