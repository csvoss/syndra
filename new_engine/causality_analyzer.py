import z3

from solver import MySolver

solver = MySolver()


# Problem statement: generalized causality, for candidate inferences
# Inputs: Context, New Statement, Candidate inference
# Output: Boolean for yes/no on whether Candidate Inference is an inference that we could make which, combined with the context, ensures that New Statement must be true.
# That is, the output = True if (Context /\ Candidate Inference /\ Not(New Statement)) is not satisfiable. Also, to avoid accepting False as a candidate inference, we must also verify that (Context /\ Candidate Inference /\ New Statement) is satisfiable. Also, we must not have "known" Candidate Inference before, so (Context /\ Not(Candidate Inference)) must be satisfiable.

def explains_statement(context, new_statement, inference):
    return solver.quick_check_valid(z3.Implies(z3.And(context, inference), new_statement))

def isnt_straight_up_false(context, new_statement, inference):
    return solver.quick_check_sat(z3.And(context, inference, new_statement))

def isnt_vacuously_true(context, new_statement, inference):
    return (solver.quick_check_sat(z3.And(context, z3.Not(inference))) and
            solver.quick_check_sat(z3.And(new_statement, z3.Not(inference))))

def is_candidate_inference(context, new_statement, inference):
    return (explains_statement(context, new_statement, inference) and
            isnt_straight_up_false(context, new_statement, inference) and
            isnt_vacuously_true(context, new_statement, inference))

# Problem statement: generalized causality, for candidate unique inferences
# Inputs: Context, New Statement, Candidate Unique Inference (CUI)
# Output: Boolean for yes/no on whether CUI is the only inference that we could make which, combined with the context, ensures that New Statement must be true.
# That is, the output = True if CUI passes all of my earlier checks for not-necessarily-unique inferences, AND if (Context /\ Not(CUI) /\ New Statement) is unsatisfiable.

def is_candidate_unique_inference(context, new_statement, inference):
    is_unique = z3.Implies(z3.And(context, new_statement), inference) # must be valid
    s = MySolver()
    return (s.quick_check_valid(is_unique) and
            is_candidate_inference(context, new_statement, inference))
