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
        enzyme = statement.enz.name.encode('utf-8')
        substrate = statement.sub.name.encode('utf-8')
        return macros.directly_phosphorylates(enzyme, substrate)
    elif isinstance(statement, indra.statements.Activation):
        # <enzyme> activates <substrate>
        upstream = statement.subj.name.encode('utf-8')
        downstream = statement.obj.name.encode('utf-8')
        if statement.subj_activity == 'activity' and statement.obj_activity == 'activity':
            return macros.directly_activates(upstream, downstream)
        else:
            raise NotImplementedError(str(statement))
    elif isinstance(statement, indra.statements.ActiveForm):
        if len(statement.mods) == 1 and \
            statement.mods[0].mod_type == 'phosphorylation' and \
            statement.is_active:
            name = statement.agent.name.encode('utf-8')
            return macros.phosphorylated_is_active(name)

    raise NotImplementedError(str(statement))
