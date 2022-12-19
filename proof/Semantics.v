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
| sand phi psi => True
| simp phi psi => True
end.
