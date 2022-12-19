Require Export SeparationLogicProofSystem.Syntax.

Fixpoint slsatisfy {Sigma: signature} {M: model Sigma}
  (R: binformula Sigma) (s: valuation M) (phi: slformula Sigma): Prop :=
match phi with
| sleq t1 t2 => interp s t1 = interp s t2
| slhasval t1 t2 => relation M R (interp s t1) (interp s t2)
| slprim p arg => pred p (Vector.map (interp s) arg)
| slnot phi => ~slsatisfy R s phi
| sland phi psi => slsatisfy R s phi /\ slsatisfy R s psi
| slforall x phi => forall (d: domain M), slsatisfy R (update s x d) phi
| sand phi psi => exists (R1 R2: binformula Sigma),
    DisjointUnion (relation M R) (relation M R1) (relation M R2) /\
    slsatisfy R1 s phi /\ slsatisfy R2 s psi
| simp phi psi => forall (R': binformula Sigma),
    Disjoint (relation M R) (relation M R') ->
    slsatisfy R' s phi -> slsatisfy (union R R') s psi
end.


