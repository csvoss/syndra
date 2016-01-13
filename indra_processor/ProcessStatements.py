from indra.statements import *
from metakappa.DomainFacts import *

def typeStatement(statement):
    """
    Given an Indra statement, returns a tuple of the statement and its type.
    """
    if isinstance(statement, Phosphorylation):
        types = { 'sub': typeMappings[statement.sub.name]
                , 'enz': typeMappings[statement.enz.name]
                , 'mod': statement.mod } # TODO: Type this
        return types
    else:
        raise Exception('Unimplemented', statement)

def separateStatements(statements):
    pass

def sameCluster(s1, s2):
    def canCluster(x, y):
        return x == y or infamily(x, y)
    # TODO: Right now we only have Phosphorylation statements, but eventually
    # we are going to have to make this more general...
    return ((canCluster(s1['sub'], s2['sub']) and
                canCluster(s1['enz'], s2['enz']))
        or (canCluster(s2['sub'], s1['sub']) and
                canCluster(s2['enz'], s1['enz'])))
    # TODO: Eventually support the modification.

def addToCluster(statementType, statement, existingCluster):
    """
    Adds statement to a cluster. Right now, clusters are just lists.
    """
    existingCluster.append((statementType, statement))

def processStatements(statements):
    """
    This function takes a list of Indra statements and returns the statements
    separated into statements at different abstraction levels.
    """
    # Get typed statements.
    typedStatements = map(lambda s: (typeStatement(s), s), statements)

    # Combine statements that talk about the same thing.
    resultClusters = []
    for (t, s) in typedStatements:
        # Go through each of the statements and find a cluster for it.
        found = False
        for rcluster in resultClusters:
            # Look in each of the result clusters and see if there is a match.
            if filter(lambda (xt, x): sameCluster(xt, t), rcluster):
                addToCluster(t, s, rcluster)
                found = True

        if not found:
            newCluster = []
            addToCluster(t, s, newCluster)
            resultClusters.append(newCluster)

    return resultClusters
