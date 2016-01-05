; Predicates from L to constrain a graph by
;
; Models are pairs of graphs and actions
;
; Graph: V, L, P, La.
;  - <V, L> undirected graph -- links
;  - <V, P> rooted forest -- parent/child relationships
;  - La: function from vertices to labels
;
; Action: atomic action or sum of actions.
; Atomic actions:
;  - id (noop)
;  - add(a)
;  - rem(a)
;  - a^b
;  - a/^b
;  - a.b
;  - a/.b
;
; L core:
; - Binding-edge from u to v
; - Parent-child from u to v
; - Node u exists
; - Node u has label i
; - Actions
;
; States:
; - u is phosphorylated
; - other states?
;
; - create an L predicate
; - be able to check if it's satisfiable
; - the model should be a <g, a> pair


; Graph datatype:
; V - list of vertices
; L - links between vertices
; P - parent/child relationships
(declare-datatypes () ((Vertex (vertex (label Int)))))
(declare-fun graph-has (Vertex) Bool)
(declare-fun graph-links (Vertex Vertex) Bool)
(declare-fun graph-parents (Vertex Vertex) Bool)

; Example usage.
(push)
(declare-const enzyme Vertex)
(declare-const substrate Vertex)
(declare-const site Vertex)
(assert (graph-links site substrate))
(assert (graph-parents enzyme site))
(check-sat)
(get-model)
(pop)


; Action datatype:
; ag+, ag-, ln+, ln-, pl+, pl-
; An action is a sum of atomic actions -- let's represent it that way instead.
; Note that the notation g.a in the paper refers to applying a to g.
(declare-datatypes () ((Identifier (identifier-labeled (label Int)))))
(declare-datatypes () ((Action
    id-action
    (add-action (added Identifier))
    (rem-action (removed Identifier))
    (link-action (link1 Identifier) (link2 Identifier))
    (unlink-action (unlink1 Identifier) (unlink2 Identifier))
    (parent-action (parent1 Identifier) (parent2 Identifier))
    (unparent-action (unparent1 Identifier) (unparent2 Identifier))
    )))
(declare-const actions (List Action))

; Example usage.
(push)
(declare-const u Identifier)
(declare-const v Identifier)
(assert (= actions (insert (link-action u v) nil)))
(check-sat)
(get-model)
(pop)

; Predicates over graphs and actions:
; see page 7
; Make functions for each predicate
; Assert implications: if the function is true, then some stuff about g,a holds
; Then, later on, we can call those functions as shortcuts
