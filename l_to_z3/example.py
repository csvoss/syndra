import model
import predicate
import z3


m = model.Model()

print "Asserting True."
p = predicate.Top(m)
status = p.check_sat()
print status
model = p.get_model()
print model
print ""

print "Asserting False."
p = predicate.Bottom(m)
status = p.check_sat()
print status
print ""

print "Asserting a is linked to b."
a = predicate.Variable.variable(1)
b = predicate.Variable.variable(2)
p = predicate.PreLink(a, b, m)
status = p.check_sat()
print status
model = p.get_model()
f = model[m.pregraph.links]
import pdb; pdb.set_trace()
print "pregraph_links:",  f
print ""
