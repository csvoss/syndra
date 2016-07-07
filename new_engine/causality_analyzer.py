import z3

from solver import MySolver

# Problem statement: generalized causality, for candidate inferences
# Inputs: Context, New Statement, Candidate inference
# Output: Boolean for yes/no on whether Candidate Inference is an inference that we could make which, combined with the context, ensures that New Statement must be true.
# That is, the output = True if (Context /\ Candidate Inference /\ Not(New Statement)) is not satisfiable. Also, to avoid accepting False as a candidate inference, we must also verify that (Context /\ Candidate Inference /\ New Statement) is satisfiable. Also, we must not have "known" Candidate Inference before, so (Context /\ Not(Candidate Inference)) must be satisfiable.

def is_candidate_inference(context, new_statement, inference):
    explains_statement = z3.Implies(z3.And(context, inference), new_statement)  # must be valid
    isnt_straight_up_false = z3.And(context, inference, new_statement) # must be satisfiable
    isnt_vacuously_true = z3.And(context, z3.Not(inference))

    s = MySolver()
    return (s.quick_check_valid(explains_statement) and
            s.quick_check_sat(isnt_straight_up_false) and
            s.quick_check_sat(isnt_vacuously_true))

# Problem statement: generalized causality, for candidate unique inferences
# Inputs: Context, New Statement, Candidate Unique Inference (CUI)
# Output: Boolean for yes/no on whether CUI is the only inference that we could make which, combined with the context, ensures that New Statement must be true.
# That is, the output = True if CUI passes all of my earlier checks for not-necessarily-unique inferences, AND if (Context /\ Not(CUI) /\ New Statement) is unsatisfiable.

def is_candidate_unique_inference(context, new_statement, inference):
    is_unique = z3.Implies(z3.And(context, new_statement), inference) # must be valid
    s = MySolver()
    return (s.quick_check_valid(is_unique) and
            is_candidate_inference(context, new_statement, inference))



if __name__ == '__main__':
    # Tests!

    # Examples -- I guess I can make these test cases:
    #
    # P := a * a == 4
    # Q := (a == -2) or (a == 2)
    # R := (a == -2)
    # S := (a == 2)
    # T := True
    # F := False

    a = z3.Int('a')
    p = (a * a == 4)
    q = z3.Or((a == -2), (a == 2))
    r = (a == -2)
    s = (a == 2)
    t = z3.And(True)
    f = z3.And(False)
    vars = {'p': p, 'q': q, 'r': r, 's': s, 't': t, 'f': f}

    # Context := T
    # New Statement := P
    # Q, R, and S are Candidate Inferences
    # Only Q is a Candidate Unique Inference

    context = t
    new_statement = p
    cis = ('q', 'r', 's')
    cuis = ('q',)

    for varname, var in vars.iteritems():
        if varname in cuis:
            assert is_candidate_unique_inference(context, new_statement, var), varname
        else:
            pass
            # assert not is_candidate_unique_inference(context, new_statement, var), varname
        if varname in cis:
            assert is_candidate_inference(context, new_statement, var), varname
        else:
            assert not is_candidate_inference(context, new_statement, var), varname

    # Context := P
    # New Statement := True
    # Nothing is a Candidate Inference
    # Nothing is a Candidate Unique Inference
    #
    # Context := P
    # New Statement := False
    # Nothing is a Candidate Inference
    # Nothing is a Candidate Unique Inference
    #
    # Context := P
    # New Statement := Q
    # Nothing is a Candidate Inference
    # Nothing is a Candidate Unique Inference
    #
    # Context := P
    # New Statement := S
    # Nothing is a Candidate Inference
    # Nothing is a Candidate Unique Inference
