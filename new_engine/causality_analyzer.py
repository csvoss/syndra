from contextlib import contextmanager
import z3

from predicate import And, ModelHasRule, PostgraphHas, PregraphHas
from solver import MySolver
from structure import Agent, Label


@contextmanager
def context(solver):
    solver.push()
    yield
    solver.pop()

def check_sat(z3_predicate):
    """Add an assertion only temporarily, and check sat."""
    solver = z3.Solver()
    with context(solver):
        solver.add(z3_predicate)
        if result > 0:
            return True
        elif result < 0:
            return False
        else:
            raise Exception("z3 returned unknown")

def check_valid(z3_predicate):
    """Check that a predicate is valid - that its negation is unsat."""
    solver = z3.Solver()
    with context(solver):
        if not solver.check():
            return True # The predicate is implied by the unsat env
        solver.add(z3.Not(z3_predicate))
        result = solver.check().r
        if result > 0: # if negation is unsat, then it's valid
            return False
        elif result < 0:
            return True
        else:
            raise Exception("z3 returned unknown")



# Problem statement: given a list of predicates, determine whether one is
# unboxed (introduces ambiguity); isolate it and return it, else return None

# Furthermore, each unboxed predicate may permit one or more minimal
# modifications that unbox it. For example, "A indirectly increases B" permits
# "A->B" as its minimal modification, whereas something like "Given A->B->C, A
# indirectly increases D" permits all of "A->D", "B->D", and "C->D" as minimal
# modifications.

# A predicate P is ambiguous when you can get its model, then use the model to
# AND P with the predicate "The model will not have at least one of these rules"

def detect_ambiguous(*predicates):
    from datatypes import Rule, Graph, Node, Edge, Nodeset, Edgeset, Labelset, Labelmap
    pred = And(*predicates)
    model = pred.get_python_model()

    # TODO assert that the model is not true, etc etc

if __name__ == '__main__':
    print "---"
    kinase = Agent("kinase")
    # phosphate = Label("phosphate")
    # oxalate = Label("oxalate")
    substrate = Agent("substrate")
    print ModelHasRule(lambda r: And(
            PregraphHas(r, kinase.bound(substrate)),
            PostgraphHas(r, kinase),
    )).get_python_model()
    print "---"

    # RAF = Agent("RAF")
    # HRAS = Agent("HRAS")
    # MEK1 = Agent("MEK1")
    # ERK1 = Agent("ERK1")
    # SAF1 = Agent("SAF1")
    # gtp = Label("GTP")
    # phosphate = Label("phosphate")
    # print And(
    #     ModelHasRule(lambda r: And(
    #             PregraphHas(r, RAF.bound(HRAS.labeled(gtp))),
    #             PregraphHas(r, MEK1),
    #             PostgraphHas(r, MEK1.labeled(phosphate))
    #     )),
    #     ModelHasRule(lambda r: And(
    #             PregraphHas(r, MEK1.labeled(phosphate)),
    #             PregraphHas(r, ERK1),
    #             PostgraphHas(r, ERK1.labeled(phosphate))
    #     )),
    #     ModelHasRule(lambda r: And(
    #             PregraphHas(r, ERK1.labeled(phosphate)),
    #             PregraphHas(r, SAF1),
    #             PostgraphHas(r, SAF1.labeled(phosphate))
    #     ))
    # ).get_python_model()



# Problem statement: generalized causality, for candidate inferences
# Inputs: Context, New Statement, Candidate inference
# Output: Boolean for yes/no on whether Candidate Inference is an inference that
# we could make which, combined with the context, ensures that New Statement
# must be true.
# That is, the output = True if (Context /\ Candidate Inference /\ Not(New
# Statement)) is not satisfiable. Also, to avoid accepting False as a candidate
# inference, we must also verify that (Context /\ Candidate Inference /\ New
# Statement) is satisfiable. Also, we must not have "known" Candidate Inference
# before, so (Context /\ Not(Candidate Inference)) must be satisfiable.

def explains_statement(context, new_statement, inference):
    return check_valid(z3.Implies(z3.And(context, inference), new_statement))

def isnt_straight_up_false(context, new_statement, inference):
    return check_sat(z3.And(context, inference, new_statement))

def isnt_vacuously_true(context, new_statement, inference):
    return (check_sat(z3.And(context, z3.Not(inference))) and
            check_sat(z3.And(new_statement, z3.Not(inference))))

def is_candidate_inference(context, new_statement, inference):
    return (explains_statement(context, new_statement, inference) and
            isnt_straight_up_false(context, new_statement, inference) and
            isnt_vacuously_true(context, new_statement, inference))

# Problem statement: generalized causality, for candidate unique inferences
# Inputs: Context, New Statement, Candidate Unique Inference (CUI)
# Output: Boolean for yes/no on whether CUI is the only inference that we could
# make which, combined with the context, ensures that New Statement must be
# true.
# That is, the output = True if CUI passes all of my earlier checks for
# not-necessarily-unique inferences, AND if (Context /\ Not(CUI) /\ New
# Statement) is unsatisfiable.

def is_candidate_unique_inference(context, new_statement, inference):
    is_unique = z3.Implies(z3.And(context, new_statement), inference) # must be valid
    s = MySolver()
    return (check_valid(is_unique) and
            is_candidate_inference(context, new_statement, inference))
