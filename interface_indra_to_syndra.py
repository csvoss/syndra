try:
    import rdflib
except:
    print "Did you source venv/bin/activate?"
    raise

try:
    import indra
except:
    print "indra must be a module accessible from this file"
    raise

def make_statements(text):
    from indra.trips import trips_api
    tp = trips_api.process_text(text)
    return tp.statements

def make_model(text):
    from indra.pysb_assembler import PysbAssembler
    pa = PysbAssembler()
    pa.add_statements(make_statements(text))
    model = pa.make_model(policies='two_step')
    return model

def make_kappa(text):
    from pysb.export.kappa import KappaExporter
    return KappaExporter(make_model(text)).export(dialect='kasim')

def example_statements(i):
    from indra.pysb_assembler import PysbAssembler
    import cPickle
    # i: the number of the example to load
    with open('examples/syndra_example_%s.pkl' % str(i), 'r') as f:
        return cPickle.load(f).statements

def syndra_from_statements():
    pass # TODO: create a model / predicate using INDRA statements


if __name__ == '__main__':
    print "Simple example from text: MEK phosphorylates ERK."
    statements = make_statements("MEK phosphorylates ERK")
    from l_to_z3 import model, statements_to_predicate
    m = model.Model()
    p = statements_to_predicate.make_predicate(statements)
