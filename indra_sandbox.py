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


