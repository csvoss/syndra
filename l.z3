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
(echo "")
(echo "Example graph.")
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
(declare-fun actions-has (Action) Bool)

; Example usage.
(push)
(echo "")
(echo "Example action.")
(declare-const u Identifier)
(declare-const v Identifier)
(assert (actions-has (link-action u v)))
(check-sat)
(get-model)
(pop)


; Postcondition graph: the graph created by the graph-action pair.
; The following code was created by consulting Definition 3 on page 5.
(declare-fun graph-2-has (Identifier) Bool)
(assert (forall ((i Identifier))
  (iff (or (and (graph-has i) (not (actions-has (rem-action i)))) (actions-has (add-action i)))
       (graph-2-has i))))
(declare-fun graph-2-links (Identifier Identifier) Bool)
(assert (forall ((a Identifier) (b Identifier))
  (iff (or (actions-has (link-action a b))
           (and (and (graph-links a b) (not (actions-has (unlink-action a b))))
                (and (not (actions-has (rem-action a))) (not (actions-has (rem-action b))))))
       (graph-2-links a b))))
(declare-fun graph-2-parents (Identifier Identifier) Bool)
(assert (forall ((a Identifier) (b Identifier))
  (iff (or (actions-has (parent-action a b))
           (and (and (graph-parents a b) (not (actions-has (unparent-action a b))))
                (and (not (actions-has (rem-action a))) (not (actions-has (rem-action b))))))
       (graph-2-parents a b))))
(echo "")
(echo "Postcondition graph defined.")
(check-sat)

; Predicates over graphs and actions:
; see page 7 of L.pdf
; Make functions for each predicate.
; Assert implications: if the function is true, then some stuff about g,a holds.
; Then, later on, we can call those functions as shortcuts.

(declare-datatypes () ((Variable (variable (get-varname Int)))))
(declare-fun interpretation (Variable) Identifier)

; Top.
(push)
(echo "")
(echo "T")
(assert true)
(check-sat)
(get-model)
(pop)

; Bottom.
(push)
(echo "")
(echo "_|_")
(assert false)
(check-sat)     ;; should be unsat
(pop)

; Equality of variables x and y.
(push)
(echo "")
(echo "x=y")
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
(echo "")
(echo "Label(x)")
(declare-const x Variable)
(declare-const Label Int)
(assert (= (get-label (interpretation x)) Label))
(check-sat)
(get-model)
(pop)

; Variable x has child y.
(push)
(echo "")
(echo "x.y")
(declare-const x Variable)
(declare-const y Variable)
(assert (graph-parents (interpretation x) (interpretation y)))
(check-sat)
(get-model)
(pop)

; "Bar" of "Variable x has child y", which seems to indicate that x has
; child y only in the second graph produced by G combined with A.
; This is the postcondition!
(push)
(echo "")
(echo "bar x.y")
(declare-const x Variable)
(declare-const y Variable)
(assert (graph-2-parents (interpretation x) (interpretation y)))
(check-sat)
(get-model)
(pop)

; "Do" of "Variable x has child y".
(push)
(echo "")
(echo "do(x.y)")
(declare-const x Variable)
(declare-const y Variable)
(assert (actions-has (parent-action (interpretation x) (interpretation y))))
(check-sat)
(get-model)
(pop)

; Variable x links to variable y.
(push)
(echo "")
(echo "x^y")
(declare-const x Variable)
(declare-const y Variable)
(assert (graph-links (interpretation x) (interpretation y)))
(check-sat)
(get-model)
(pop)

; "Bar" of Variable x links to variable y; Again a postcondition.
(push)
(echo "")
(echo "bar x^y")
(declare-const x Variable)
(declare-const y Variable)
(assert (graph-2-links (interpretation x) (interpretation y)))
(check-sat)
(get-model)
(pop)

; "Do" of "Variable x links to variable y".
(push)
(echo "")
(echo "do(x^y)")
(declare-const x Variable)
(declare-const y Variable)
(assert (actions-has (link-action (interpretation x) (interpretation y))))
(check-sat)
(get-model)
(pop)

; "Do" of "Variable x unlinks to variable y".
(push)
(echo "")
(echo "do(x/^y)")
(declare-const x Variable)
(declare-const y Variable)
(assert (actions-has (unlink-action (interpretation x) (interpretation y))))
(check-sat)
(get-model)
(pop)

; "Has" of variable x.
(push)
(echo "")
(echo "has(x)")
(declare-const x Variable)
(assert (graph-has (interpretation x)))
(check-sat)
(get-model)
(pop)

; "Bar" of "Has" of x. Again, a postcondition.
(push)
(echo "")
(echo "bar has(x)")
(declare-const x Variable)
(assert (graph-2-has (interpretation x)))
(check-sat)
(get-model)
(pop)

; "Add" of variable x, and "Rem" of variable x. Given that these are
; preconditions, as written in the L paper, I'm not convinced that
; we gain anything by implementing them as opposed to using has(x) and !has(x).

; Examples:
; Kinase with two sites
; Prior knowledge about GTP-kinases, about kinases, ...
; Complexes
