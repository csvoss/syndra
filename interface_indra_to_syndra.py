"""
Run this file to demo INDRA -> Syndra.
"""

# These are just to quickly detect and tell the user about some issues which
# caused me errors during my test-runs; the issues are easy to fix.
try:
    import rdflib
except:
    raise StandardError("Run `source venv/bin/activate` before running this file.")
try:
    import indra
except:
    raise StandardError("indra must be a module accessible from this file")


def make_statements(text):
    """Given text, return a list of INDRA statements."""
    from indra.trips import trips_api
    tp = trips_api.process_text(text)
    return tp.statements

def make_model(text):
    """Given text, return an INDRA model."""
    from indra.pysb_assembler import PysbAssembler
    pa = PysbAssembler()
    pa.add_statements(make_statements(text))
    model = pa.make_model(policies='two_step')
    return model

def make_kappa(text):
    """Given text, use INDRA to produce Kappa code."""
    from pysb.export.kappa import KappaExporter
    return KappaExporter(make_model(text)).export(dialect='kasim')

def example_statements(i):
    """Unpickle and return statements from the ith preexisting INDRA example."""
    from indra.pysb_assembler import PysbAssembler
    import cPickle
    # i: the number of the example to load
    with open('examples/syndra_example_%s.pkl' % str(i), 'r') as f:
        return cPickle.load(f).statements

def syndra_from_statements(*statements):
    """Given a list of INDRA statements, produce an L formula, then
    return the corresponding model as determined by Z3."""
    from l_to_z3 import statements_to_predicates
    pred = statements_to_predicates.make_predicate_many(statements)
    return pred

if __name__ == '__main__':
    "Simple example from text."
    statements = make_statements("MEK phosphorylates ERK at serine 222. MEK activates ERK.")
    pred = syndra_from_statements(*statements)
    print pred
    print pred.check_sat()
    print ""
