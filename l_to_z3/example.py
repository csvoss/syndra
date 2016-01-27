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

# TODO: variables a and b should be allowed to refer to the same node...

print "Asserting a is linked to b."
a = predicate.Variable.variable(1)
b = predicate.Variable.variable(2)
#p1 = predicate.PreLink(a, b, m)
p = predicate.Equal(a, b, m)
#p = predicate.PredicateAnd(p1, p2, m)
status = p.check_sat()
print status
model = p.get_model()
f = model[m.pregraph.links]
print "For conciseness, just printing out the relevant bits:"
print "pregraph_links:",  f
print "Here's the entire model."
print model
print ""
# describes a set of graph, action pairs

# get_model() -> returns just one of the graph, action pairs



# make sure nodes cannot be bound to themselves
