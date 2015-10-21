; Tests for using Z3 to handle simple inferences
;
;   Run this file with "z3 -smt2 [file name].z3"
;   Running this file should output the following:
;     unsat
;     unsat
;     unsat
;     sat
;
;   Author: Jean Yang

; We only have sites right now.
(declare-datatypes () ((Site MEK)))

; If something is phosphorylated, then it should be active.
(declare-fun active (Site) Bool)
(declare-fun kinase-active (Site) Bool)
(assert (forall ((s Site)) (=> (kinase-active s) (active s))))

(push)
(declare-const s1 Site)
(assert (kinase-active s1))
; If something is phosphorylated (kinase-active), then it is active.
; Thus the following assertion should cause the model to be unsatisfiable. 
(assert (not (active s1)))
(check-sat)
(pop)

; Declare some relationships between different granularities of phosphorylation.
(declare-datatypes () ((KinaseFamily Serine)))
(declare-datatypes () ((KinaseMolecule S222)))
(declare-datatypes () ((KinaseLabel none (family (f KinaseFamily)) (kinase (k KinaseMolecule)))))
(declare-fun kinase-subsumes (KinaseLabel KinaseLabel) Bool)
(declare-fun in-kinase-family (KinaseLabel KinaseLabel) Bool)

; Declare subsumption relationships between different granularities of kinases.
(assert (forall ((k1 KinaseLabel) (k2 KinaseLabel))
  (=> (in-kinase-family k1 k2) (kinase-subsumes k2 k1))))
; Having some information about a kinase subsumes having no information.
(assert (forall ((k1 KinaseLabel)) (kinase-subsumes k1 none)))

; If we know something more specific phosphorylates a site, then we can infer
; the more general phosphorylation.
(declare-fun phosphorylated (Site KinaseLabel) Bool)
(assert (forall ((s Site) (k1 KinaseLabel) (k2 KinaseLabel))
  (=> (and (kinase-subsumes k2 k1) (phosphorylated s k2)) (phosphorylated s k1))))

(push)
(assert (in-kinase-family (family Serine) (kinase S222)))
(assert (phosphorylated MEK (kinase S222)))
(assert (kinase-subsumes (kinase S222) (family Serine)))

; The previous assertion should imply the next one can't be true.
(push)
(assert (not (phosphorylated MEK (family Serine))))
(check-sat)
(pop)

; The previous assertion should also imply the next one can't be true.
(push)
(assert (not (phosphorylated MEK none)))
(check-sat)
(pop)

; Sanity-checking: phosphorylating with S222 should imply general
; phosphorylation.
(push)
(assert (phosphorylated MEK none))
(check-sat)
(pop)

(pop)
