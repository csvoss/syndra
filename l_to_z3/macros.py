import predicate

class Phosphorylates(predicate.Predicate):
    """
    L statement to ensure that an agent phosphorylates another.
    """
    def __init__(self, e, s, *args):
        """
        """
        super(Phosphorylates, self).__init__(*args)
        predicate.ensure_variable(e)
        predicate.ensure_variable(s)
        self.e = e
        self.s = s

    def get_predicate(self):
        predicates = [
            _phosphorylation_predicate_1(self.e, self.s),
            _phosphorylation_predicate_2(self.e, self.s),
            _phosphorylation_predicate_3(self.e, self.s),
        ]
        return predicate.PredicateOr(*predicates)


def _phosphorylation_predicate_only_binding(e, s):
    """
    Doesn't actually model reaction; only models the fact
    that the enzyme is allowed to bind to the substrate.
    E + S <-> ES.
    This should not be one of the default phosphorylation policies.
    """
    return predicate.DoLink(e, s)

def _phosphorylation_predicate_1(e, s):
    """
    Simple phosphorylation: E+U -> E+P
    Preconditions: s is labeled 'u'; e exists
    Postcondition: s is labeled 'p'; e still exists
    """
    predicates = [
        predicate.PreHas(e),
        predicate.PostHas(e),
        predicate.PreHas(s),
        predicate.PostHas(s),
        predicate.Labeled(s, 'u'),
        predicate.Labeled(s, 'p'), # TODO: Labeled as a postcondition?
    ]
    return predicate.PredicateAnd(*predicates)


def _phosphorylation_predicate_2(e, s):
    """
    Simple phosphorylation with binding: E+S <-> ES -> E+P
    """
    # TODO: Ask Jean or Adrien about how to make L stmts with multiple Kappa rules.
    return predicate.PredicateAnd(*predicates)


def _phosphorylation_predicate_3(e, s):
    """
    More complex phosphorylation model: E+S <-> ES -> EP <-> E+P.
    """
    return predicate.PredicateAnd(*predicates)

