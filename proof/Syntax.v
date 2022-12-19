Require Export SeparationLogicProofSystem.Model.

Inductive slformula (Sigma: signature): Set :=
| sleq: term Sigma -> term Sigma -> slformula Sigma
| slhasval: term Sigma -> term Sigma -> slformula Sigma
| slprim (p: Pred Sigma): Vector.t (term Sigma) (adic p) -> slformula Sigma
| slnot: slformula Sigma -> slformula Sigma
| sland: slformula Sigma -> slformula Sigma -> slformula Sigma
| slforall: V -> slformula Sigma -> slformula Sigma
| sand: slformula Sigma -> slformula Sigma -> slformula Sigma 
| simp: slformula Sigma -> slformula Sigma -> slformula Sigma.

Arguments sleq {_} _ _.
Arguments slhasval {_} _ _.
Arguments slprim {_} _ _.
Arguments slnot {_} _.
Arguments sland {_} _ _.
Arguments slforall {_} _ _.
Arguments sand {_} _ _.
Arguments simp {_} _ _.

Definition slor {Sigma: signature} (phi psi: slformula Sigma): slformula Sigma :=
  slnot (sland (slnot phi) (slnot psi)).
Definition slimp {Sigma: signature} (phi psi: slformula Sigma): slformula Sigma :=
  slor (slnot phi) psi.
Definition slexists {Sigma: signature} (x: V) (phi: slformula Sigma): slformula Sigma :=
  slnot (slforall x (slnot phi)).

Inductive rooted (Sigma: signature): Set :=
| mkrooted: slformula Sigma -> binformula Sigma -> rooted Sigma.

Inductive biformula (Sigma: signature): Set :=
| fol: formula Sigma -> biformula Sigma
| sl: rooted Sigma -> biformula Sigma.

Inductive sequent (Sigma: signature): Set :=
| mksequent: list (biformula Sigma) -> list (biformula Sigma) -> sequent Sigma.
