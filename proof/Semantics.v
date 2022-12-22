Require Export SeparationLogicProofSystem.Syntax.

Definition rsatisfy {Sigma: signature} {M: model Sigma}
  (t: replacement Sigma) (s: valuation M) (phi: rformula Sigma): Prop :=
satisfy s (rformula_replace t phi).

Definition rrelation {Sigma: signature} (M: model Sigma)
  (t: replacement Sigma) (phi: binrformula Sigma): M -> M -> Prop :=
fun d d' => rsatisfy t (update (update (nulval M) x d) y d') phi.

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

Definition rootedsatisfy {Sigma: signature} {M: model Sigma}
  (t: replacement Sigma) (s: valuation M) (phip: rooted Sigma): Prop :=
match phip with
| mkrooted phi p => slsatisfy (binrformula_binformula t p) s phi
end.

Definition sequentsatisfy {Sigma: signature} {M: model Sigma}
  (s: valuation M) (seq: sequent Sigma): Prop :=
let (left, right) := seq in forall t,
  List.fold_left and (List.map (rootedsatisfy t s) left) True /\
  List.fold_right or False (List.map (rootedsatisfy t s) right).

Definition sequenttrue {Sigma: signature} (M: model Sigma) (seq: sequent Sigma): Prop :=
forall (s: valuation M), sequentsatisfy s seq.

Definition sequentvalid {Sigma: signature} (seq: sequent Sigma): Prop :=
forall (M: model Sigma), sequenttrue M seq.
