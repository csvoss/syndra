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
(declare-datatypes () ((Protein MEK)))

; If something is phosphorylated, then it should be active.
(declare-fun active (Protein) Bool)
(declare-fun site-active (Protein) Bool)
(assert (forall ((s Protein)) (=> (site-active s) (active s))))

(push)
(declare-const s1 Protein)
(assert (site-active s1))
; If something is site-active, then it is active.
; Thus the following assertion should cause the model to be unsatisfiable. 
(assert (not (active s1)))
(check-sat)
(pop)

; Declare some relationships between different granularities of phosphorylation.
(declare-datatypes () ((Residue Serine)))
(declare-datatypes () ((Site S222)))
(declare-datatypes () ((SiteLabel none (residue (f Residue)) (site (k Site)))))
(declare-fun site-refines (SiteLabel SiteLabel) Bool)
(declare-fun in-family (SiteLabel SiteLabel) Bool)

; Declare subsumption relationships between different granularities of sites.
(assert (forall ((k1 SiteLabel) (k2 SiteLabel))
  (=> (in-family k1 k2) (site-refines k2 k1))))
; Having some information about a site refines having no information.
(assert (forall ((k1 SiteLabel)) (site-refines k1 none)))

; If we know something more specific phosphorylates a site, then we can infer
; the more general phosphorylation.
(declare-fun phosphorylated (Protein SiteLabel) Bool)
(assert (forall ((s Protein) (k1 SiteLabel) (k2 SiteLabel))
  (=> (and (site-refines k2 k1) (phosphorylated s k2)) (phosphorylated s k1))))

(push)
(assert (in-family (residue Serine) (site S222)))
(assert (phosphorylated MEK (site S222)))
; (assert (site-refines (site S222) (residue Serine)))

; The previous assertion should imply the next one can't be true.
(push)
(assert (not (phosphorylated MEK (residue Serine))))
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

(push)
(assert (phosphorylated MEK none))
(check-sat)
(get-model)
; (assert (phosphorylated MEK (residue Serine)))
(pop)
