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
; La - vertex labels (access using `get-label`)
(declare-datatypes () ((Identifier (node (get-label Int)))))
(declare-fun graph-has (Identifier) Bool)
(declare-fun graph-links (Identifier Identifier) Bool)
(declare-fun graph-parents (Identifier Identifier) Bool)

; Example usage.
(push)
(declare-const enzyme Identifier)
(declare-const substrate Identifier)
(declare-const site Identifier)
(assert (graph-links site substrate))
(assert (graph-parents enzyme site))
(check-sat)
(get-model)
(pop)


; Action datatype:
; ag+, ag-, ln+, ln-, pl+, pl-
; An action is a sum of atomic actions -- let's represent it that way instead.
; Note that the notation g.a in the paper refers to applying a to g.
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

; Utility function: list contains
; TODO; not currently working.
(define-fun contains ((xs (List Action)) (a Action)) Bool
  (ite (= xs nil) false
    (ite (= (head xs) a) true
                         (contains (tail xs) a))))
(assert (forall ((a Action))
  (not (contains nil a))))
(assert (forall ((xs (List Action)) (a Action))
    (iff (contains xs a)
         (or (= (head xs) a) (contains (tail xs) a)))))


; Example usage.
(push)
(declare-const u Identifier)
(declare-const v Identifier)
(assert (= actions (insert (link-action u v) nil)))
(check-sat)
(get-model)
(pop)


; Predicates over graphs and actions:
; see page 7 of L.pdf
; Make functions for each predicate.
; Assert implications: if the function is true, then some stuff about g,a holds.
; Then, later on, we can call those functions as shortcuts.

(declare-datatypes () ((Variable (variable (get-varname Int)))))
(declare-fun interpretation (Variable) Identifier)

; Top.
(push)
(assert true)
(check-sat)
(get-model)
(pop)

; Bottom.
(push)
(assert false)
(check-sat)     ;; should be unsat
(pop)

; Equality of variables x and y.
(push)
(declare-const x Variable)
(declare-const y Variable)
(assert (= (get-varname x) (get-varname y)))
(check-sat)
(get-model)
(pop)

; Variable has label from a specific subset of labels.
; (Not implementing; we can implement this with an OR of specific labels.)

; Variable has specific label.
(push)
(declare-const x Variable)
(declare-const label Int)
(assert (= (get-label (interpretation x)) label))
(check-sat)
(get-model)
(pop)

; Variable x has child y.
(push)
(declare-const x Variable)
(declare-const y Variable)
(assert (graph-parents (interpretation x) (interpretation y)))
(check-sat)
(get-model)
(pop)

; "Bar" of "Variable x has child y", which seems to indicate that x has
; child y only in the second graph produced by G combined with A.
; TODO.

; "Do" of "Variable x has child y".
(push)
(declare-const x Variable)
(declare-const y Variable)
(assert (contains actions (parent-action (interpretation x) (interpretation y))))
(check-sat)
(get-model)
(pop)
