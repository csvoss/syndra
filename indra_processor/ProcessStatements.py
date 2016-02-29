from indra.statements import *
from metakappa.DomainFacts import *

from Node import *

def typeStatement(statement):
    """
    Given an Indra statement, returns a tuple of the statement and its type.
    """
    # TODO: Do this in a more systematic way.
    if isinstance(statement, Phosphorylation):
        types = { 'sub': typeMappings[statement.sub.name]
                , 'enz': typeMappings[statement.enz.name]
                , 'mod': statement.mod
                , 'mod_pos': statement.mod_pos } # TODO: Type this
        return types
    else:
        raise Exception('Unimplemented', statement)

def mkClusters(typedStatements):
    def sameCluster(s1, s2):
        """
        Two statements can be in the same cluster if the enzymes and substrates
        have a sub-family relationship.

        TODO: Figure out if we want to subtype activity here.
        """
        def sharesParent(x, y):
            for p in x.parents:
                if p in y.parents:
                    return True
            return False
        def canCluster(x, y):
            return x == y or infamily(x, y) or sharesParent(x, y)
        # TODO: Right now we only have Phosphorylation statements, but
        # eventually we are going to have to make this more general...
        sameCluster = ((canCluster(s1['sub'], s2['sub']) and
                    canCluster(s1['enz'], s2['enz']))
            or (canCluster(s2['sub'], s1['sub']) and
                    canCluster(s2['enz'], s1['enz'])))
        # print s1
        # print s2
        # print sameCluster
        # TODO: Eventually support the modification.
        return sameCluster

    def addToCluster(statementType, statement, existingCluster):
        """
        Adds statement to a cluster. Right now, clusters are just lists.
        """
        existingCluster.append((statementType, statement))

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

def moreGeneral((aType, a), (bType, b)):
    """
    Returns whether a is more general than b. a is more general than b if
    b is a subtype of a in the sub and enz fields and some other stuff.
    
    The structure of the type information is:
    types = { 'sub': typeMappings[statement.sub.name]
            , 'enz': typeMappings[statement.enz.name]
            , 'mod': statement.mod
            , 'mod_pos': statement.mod_pos }
    """
    def moreGeneralMod(aMod, bMod):
        if aMod and bMod:
            return aMod == 'Phosphorylation' and \
                len(aMod) < len(bMod) 
    def moreGeneralPos(aPos, bPos):
        return aPos != None and bPos == None
    return infamily(bType['sub'], aType['sub']) and \
        infamily(bType['enz'], aType['enz']) and \
        moreGeneralMod(aType['mod'], bType['mod']) and \
        moreGeneralPos(aType['mod_pos'], bType['mod_pos'])

def mkTrees(clusters):
    """
    Takes clusters (which are currently lists of lists) and returns information
    at different levels of abstraction.
    """
    def mkTree(cluster, curTree):
        """
        Go through each element in the tree and find the right place in the
        tree to put it.
        """
        def addToTree(elt, curTree):
            eltNode = Node(elt)
            if curTree:
                # Check whether the element is more general than the root of
                # the tree. If so, then we make it the new root.
                # TODO: We're also going to need to handle the case where
                # two things are at the same level of generality.
                if moreGeneral(elt, curTree.v):
                    eltNode.addChild(curTree)
                    return eltNode
                # Otherwise figure out if it should be inserted between the root
                # and any of the children.
                else:
                    addedBetweenChildren = False
                    for c in curTree.children:
                        if moreGeneral(elt, c.v):
                            tmp = c.v
                            c.v = elt
                            c.addChild(Node(tmp))
                            break
                    # If not, it can simply be a child.
                    if not addedBetweenChildren:
                        curTree.addChild(eltNode)
                
            else:
                # If we don't have a current tree, make this the tree!
                return eltNode

        if cluster:
            nxt = cluster.pop()
            return mkTree(cluster, addToTree(nxt, curTree))
        else:
            return curTree

    trees = []
    for cluster in clusters:
        if cluster:
            trees.append(mkTree(cluster, None))
    return trees

def processStatements(statements):
    """
    This function takes a list of Indra statements and returns the statements
    separated into statements at different abstraction levels.
    """
    # Get typed statements.
    typedStatements = map(lambda s: (typeStatement(s), s), statements)

    # Combine statements that talk about the same thing.
    resultClusters = mkClusters(typedStatements)

    # Make tree out of the statement clusters.
    trees = mkTrees(resultClusters)

    return trees
