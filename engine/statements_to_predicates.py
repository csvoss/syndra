import indra
import macros
import predicate
import z3

def make_predicate_many(statements):
    # TODO: Switch this back to using predicate.Top and predicate.And
    # once the macros are returning Predicate predicates instead of z3 predicates.
    if len(statements) == 0:
        return predicate.Top()
    elif len(statements) == 1:
        return make_predicate(statements[0])
    else:
        predicates = [make_predicate(statement) for statement in statements]
        return predicate.And(*predicates)

def make_predicate(statement):
    if isinstance(statement, indra.statements.Phosphorylation):
        # <enzyme> phosphorylates <substrate>
        # str() because sometimes these are Unicode
        enzyme = str(statement.enz.name)
        substrate = str(statement.sub.name)
        return macros.directly_phosphorylates(enzyme, substrate)
    elif isinstance(statement, indra.statements.ActivityActivity):
        # <enzyme> activates <substrate>
        upstream = str(statement.subj.name)
        downstream = str(statement.obj.name)
        if statement.subj_activity == 'act' and statement.obj_activity == 'act':
            return macros.directly_activates(upstream, downstream)
        else:
            raise NotImplementedError(str(statement))
    elif isinstance(statement, indra.statements.ActivityModification):
        # TODO: ActivityModification macro -- I can't get an INDRA example
        # to test by, but it will be very similar to the above.
        return macros.phosphorylated_is_active("ERK")

    raise NotImplementedError(str(statement))
