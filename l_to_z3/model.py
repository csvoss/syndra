"""Z3 implementation of L - the meta-Kappa devised by Adrien Husson and Jean
Krivine - using the Python bindings for Z3.
"""

from z3 import *

# Helper function not defined by Z3.
def Iff(a, b):
    return Not(Xor(a, b))


# Identifier is a datatype representing a vertex or node in a Kappa graph.
Identifier = Datatype('Identifier')
Identifier.declare('none')
Identifier.declare('node', ('label', IntSort()))
Identifier = Identifier.create()

# Graph, before a rule or action has applied.
# class Pregraph(object):
#     def __init__(self):
#         self.has = Function('has', Identifier, BoolSort())
#         self.links = Function('links', Identifier, Identifier, BoolSort())
#         self.parents = Function('parents', Identifier, Identifier, BoolSort())

# Atomic action. An Action is comprised of a set of these.
AtomicAction = Datatype('AtomicAction')
AtomicAction.declare('id_action')
AtomicAction.declare('add_action', ('added', Identifier))
AtomicAction.declare('rem_action', ('removed', Identifier))
AtomicAction.declare('link_action',
    ('link1', Identifier), ('link2', Identifier))
AtomicAction.declare('unlink_action',
    ('unlink1', Identifier), ('unlink2', Identifier))
AtomicAction.declare('parent_action',
    ('parent1', Identifier), ('parent2', Identifier))
AtomicAction.declare('unparent_action',
    ('unparent1', Identifier), ('unparent2', Identifier))
AtomicAction = AtomicAction.create()

# Action: a set of atomic actions.
class Action(object):
    def __init__(self):
        self.has = Function('has', AtomicAction, BoolSort())

# Graph, after a rule or action has been applied.
class Postgraph(object):
    def __init__(self, graph, action):
        self.has = Function('has', Identifier, BoolSort())
        self.links = Function('links', Identifier, Identifier, BoolSort())
        self.parents = Function('parents', Identifier, Identifier, BoolSort())

        # Constrain the postgraph's nodes, links, and parent-child relationships
        # appropriately, according to what the graph and action contain. TODO.
        i = Const('i', Identifier)
        engine.z3_assert(ForAll(Const('i', Identifier),
                                Iff(self.has(i),
                                    Or(And(graph.has(i), Not(action.has(AtomicAction.rem_action(i)))),
                                       action.has(AtomicAction.add_action(i))))))
        engine.z3_assert(ForAll([Const('a', Identifier), Const('b', Identifier)],
            Iff(self.links(a, b),
                Or(
                    And(
                        And(
                            graph.links(a, b),
                            Not(action.has(AtomicAction.unlink_action(a, b)))),
                        And(
                            Not(action.has(AtomicAction.rem_action(a))),
                            Not(action.has(AtomicAction.rem_action(b))))),
                    action.has(AtomicAction.link_action(a, b))))))
        engine.z3_assert(ForAll([Const('a', Identifier), Const('b', Identifier)],
            Iff(self.parents(a, b),
                Or(
                    And(
                        And(
                            graph.parents(a, b),
                            Not(action.has(AtomicAction.unparent_action(a, b)))),
                        And(
                            Not(action.has(AtomicAction.rem_action(a))),
                            Not(action.has(AtomicAction.rem_action(b))))),
                        action.has(AtomicAction.parent_action(a, b))))))


# Model is Kappa's <graph, action> pair, but I've included the postgraph
# (i.e. the graph after applying the action), too, for convenience.
class Model(object):
    def __init__(self):
        self.pregraph = Pregraph()
        self.action = Action()
        self.postgraph = Postgraph(self.pregraph, self.action)



# TODO: implement Predicate. This thing should be an interface implemented by a
# bunch of different subclasses; combine those subclasses together to make a
# predicate, and then allow the predicate to be executed / checked / model-got /
# whatever we want by Z3. In fact, put Predicate stuff in a different file
# entirely. This is one abstraction layer higher than the above Z3 definitions
# are. Probably the subclasses should only return Z3 formulae, not make any
# assertions; then, Predicate can manipulate those formulae into an assertion.

class Predicate(object):
    """Parent class which all Predicates will subclass.

    Contains implementations of some z3-related functionality. Subclasses will
    override get_predicate."""

    def __init__(self):
        self.asserted_yet = False

    def get_predicate(self):
        raise NotImplementedError()

    def assert_over(self, model):
        pass
        self.asserted_yet = True

    def check_sat(self, model):
        pass

    def get_model(self, model):
        pass

    def get_all_models(self, model):
        pass


class Top(Predicate):
    def __init__(self):
        pass

    def get_predicate(self):
        pass

class Bottom(Predicate):
    def __init__(self):
        pass

    def get_predicate(self):
        pass

class Equal(Predicate):
    def __init__(self, x, y):
        # ensure that x and y are both of the right type (Variable)
        pass

    def get_predicate(self):
        pass

"""
; Postcondition graph: the graph created by the graph-action pair.
; The following code was created by consulting Definition 3 on page 5.
(declare-fun graph-2-has (Identifier) Bool)
(echo "")
(echo "Postcondition graph defined.")
(check-sat)

; Predicates over graphs and actions:
; see page 7 of L.pdf
; Make functions for each predicate.
; Assert implications: if the function is true, then some stuff about g,a holds.
; Then, later on, we can call those functions as shortcuts.

(declare-datatypes () ((Variable (variable (get-varname Int)))))
(declare-fun interpretation (Variable) Identifier)

; Equality of variables x and y.
(push)
(echo "")
(echo "x=y")
(declare-const x Variable)
(declare-const y Variable)
(assert (= (get-varname x) (get-varname y)))
(check-sat)
(get-model)
(pop)

; Variable has label from a specific subset of labels.
; (Not implementing; we can implement this with an OR of specific labels.)

; Variable has specific label.
(push)
(echo "")
(echo "Label(x)")
(declare-const x Variable)
(declare-const Label Int)
(assert (= (get-label (interpretation x)) Label))
(check-sat)
(get-model)
(pop)

; Variable x has child y.
(push)
(echo "")
(echo "x.y")
(declare-const x Variable)
(declare-const y Variable)
(assert (graph-parents (interpretation x) (interpretation y)))
(check-sat)
(get-model)
(pop)

; "Bar" of "Variable x has child y", which seems to indicate that x has
; child y only in the second graph produced by G combined with A.
; This is the postcondition!
(push)
(echo "")
(echo "bar x.y")
(declare-const x Variable)
(declare-const y Variable)
(assert (graph-2-parents (interpretation x) (interpretation y)))
(check-sat)
(get-model)
(pop)

; "Do" of "Variable x has child y".
(push)
(echo "")
(echo "do(x.y)")
(declare-const x Variable)
(declare-const y Variable)
(assert (actions-has (parent-action (interpretation x) (interpretation y))))
(check-sat)
(get-model)
(pop)

; Variable x links to variable y.
(push)
(echo "")
(echo "x^y")
(declare-const x Variable)
(declare-const y Variable)
(assert (graph-links (interpretation x) (interpretation y)))
(check-sat)
(get-model)
(pop)

; "Bar" of Variable x links to variable y; Again a postcondition.
(push)
(echo "")
(echo "bar x^y")
(declare-const x Variable)
(declare-const y Variable)
(assert (graph-2-links (interpretation x) (interpretation y)))
(check-sat)
(get-model)
(pop)

; "Do" of "Variable x links to variable y".
(push)
(echo "")
(echo "do(x^y)")
(declare-const x Variable)
(declare-const y Variable)
(assert (actions-has (link-action (interpretation x) (interpretation y))))
(check-sat)
(get-model)
(pop)

; "Do" of "Variable x unlinks to variable y".
(push)
(echo "")
(echo "do(x/^y)")
(declare-const x Variable)
(declare-const y Variable)
(assert (actions-has (unlink-action (interpretation x) (interpretation y))))
(check-sat)
(get-model)
(pop)

; "Has" of variable x.
(push)
(echo "")
(echo "has(x)")
(declare-const x Variable)
(assert (graph-has (interpretation x)))
(check-sat)
(get-model)
(pop)

; "Bar" of "Has" of x. Again, a postcondition.
(push)
(echo "")
(echo "bar has(x)")
(declare-const x Variable)
(assert (graph-2-has (interpretation x)))
(check-sat)
(get-model)
(pop)

; "Add" of variable x, and "Rem" of variable x. Given that these are
; preconditions, as written in the L paper, I'm not convinced that
; we gain anything by implementing them as opposed to using has(x) and !has(x).

; Examples:
; Kinase with two sites
; Prior knowledge about GTP-kinases, about kinases, ...
; Complexes
"""
