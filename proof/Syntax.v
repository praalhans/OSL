Require Export SeparationLogicProofSystem.Model.

(* Second-order dyadic relation variables *)
Definition W := nat.

Inductive rformula (Sigma: signature): Set :=
| rvar: W -> term Sigma -> term Sigma -> rformula Sigma
| req: term Sigma -> term Sigma -> rformula Sigma
| rprim (P: Pred Sigma): Vector.t (term Sigma) (adic P) -> rformula Sigma
| rlnot: rformula Sigma -> rformula Sigma
| rland: rformula Sigma -> rformula Sigma -> rformula Sigma
| rlforall: V -> rformula Sigma -> rformula Sigma.

Arguments rvar {_} _ _ _.
Arguments req {_} _ _.
Arguments rprim {_} _ _.
Arguments rlnot {_} _.
Arguments rland {_} _ _.
Arguments rlforall {_} _ _.

Fixpoint freevarrfl {Sigma: signature} (phi: rformula Sigma): list V :=
match phi with
| rvar w t1 t2 => List.app (freevartl t1) (freevartl t2)
| req t1 t2 => List.app (freevartl t1) (freevartl t2)
| rprim _ arg => Vector.fold_right (@List.app V)
    (Vector.map (@freevartl Sigma) arg) List.nil
| rlnot phi => freevarrfl phi
| rland phi psi => List.app (freevarrfl phi) (freevarrfl psi)
| rlforall z phi => List.remove (Nat.eq_dec) z (freevarrfl phi)
end.

Definition freevarrf {Sigma: signature} (phi: rformula Sigma): V -> Prop :=
fun z => List.In z (freevarrfl phi).

Proposition freevarrf_rvar {Sigma: signature} (w: W) (t1 t2: term Sigma):
  freevarrf (rvar w t1 t2) = Union (freevart t1) (freevart t2).
apply functional_extensionality; intro z.
unfold freevarrf; simpl.
unfold Union.
apply propositional_extensionality.
apply List.in_app_iff.
Qed.

Proposition freevarrf_req {Sigma: signature} (t1 t2: term Sigma):
  freevarrf (req t1 t2) = Union (freevart t1) (freevart t2).
apply functional_extensionality; intro z.
unfold freevarrf; simpl.
unfold Union.
apply propositional_extensionality.
apply List.in_app_iff.
Qed.

Record binrformula (Sigma: signature) := mkbinrformula
{ binrformula_form: rformula Sigma
; binrformula_prop: forall z, freevarrf binrformula_form z ->
    z = x \/ z = y
}.
Coercion binrformula_form: binrformula >-> rformula.

Record rsentence (Sigma: signature) := mkrsentence
{ rsentence_form: rformula Sigma
; rsentence_prop: forall z, ~freevarrf rsentence_form z
}.
Coercion rsentence_form: rsentence >-> rformula.
Proposition rsentence_binrformula_prop {Sigma: signature} (phi: rsentence Sigma):
  forall z : V, freevarrf phi z -> z = x \/ z = y.
intros. pose proof (rsentence_prop _ phi).
exfalso. eapply H0. apply H.
Qed.
Definition rsentence_binrformula {Sigma: signature} (phi: rsentence Sigma): binrformula Sigma :=
mkbinrformula _ phi (rsentence_binrformula_prop phi).
Coercion rsentence_binrformula: rsentence >-> binrformula.

Definition replacement (Sigma: signature) := W -> binformula Sigma.

Fixpoint rformula_replace {Sigma: signature} (t: replacement Sigma) (phi: rformula Sigma): formula Sigma :=
match phi with
| rvar w t1 t2 => fsub t2 y (fsub t1 x (t w))
| req t1 t2 => eq t1 t2
| rprim p arg => prim p arg
| rlnot phi => lnot (rformula_replace t phi)
| rland phi psi => land (rformula_replace t phi) (rformula_replace t psi)
| rlforall z phi =>  lforall z (rformula_replace t phi)
end.

Proposition rformula_replace_prop {Sigma: signature} (t: replacement Sigma) (phi: binrformula Sigma):
  forall z : V, freevarf (rformula_replace t phi) z -> z = x \/ z = y.
intros.
destruct phi; simpl in *.
induction binrformula_form0; simpl in *.
- rewrite freevarf_fsub in H.
  unfold Union in H; destruct H.
  unfold Subtract in H; destruct (eq_dec z y); auto.
  rewrite freevarf_fsub in H.
  unfold Union in H; destruct H.
  unfold Subtract in H; destruct (eq_dec z x); auto.
  pose proof (binformula_prop _ (t w) _ H); auto.
  apply binrformula_prop0.
  rewrite freevarrf_rvar.
  unfold Union; auto.
  apply binrformula_prop0.
  rewrite freevarrf_rvar.
  unfold Union; auto.
- apply binrformula_prop0.
  rewrite freevarrf_req.
  rewrite freevarf_eq in H; auto.
- apply binrformula_prop0.
  unfold freevarrf.
  unfold freevarrfl.
  unfold freevarf in H.
  unfold freevarfl in H.
  auto.
- apply IHbinrformula_form0.
  intros. apply binrformula_prop0.
  unfold freevarrf; unfold freevarrf in H0.
  unfold freevarrfl; unfold freevarrfl in H0.
  auto.
  unfold freevarf; unfold freevarf in H.
  unfold freevarfl; unfold freevarfl in H.
  auto.
- unfold freevarf in H. simpl in H.
  rewrite List.in_app_iff in H; destruct H.
  apply IHbinrformula_form0_1.
  intros. apply binrformula_prop0.
  unfold freevarrf; unfold freevarrf in H0; simpl.
  rewrite List.in_app_iff; auto.
  unfold freevarf; auto.
  apply IHbinrformula_form0_2.
  intros. apply binrformula_prop0.
  unfold freevarrf; unfold freevarrf in H0; simpl.
  rewrite List.in_app_iff; auto.
  unfold freevarf; auto.
- apply IHbinrformula_form0.
  intros. apply binrformula_prop0.
  unfold freevarrf; unfold freevarrfl.
Admitted.

Definition binrformula_binformula {Sigma: signature} (t: replacement Sigma)
  (phi: binrformula Sigma): binformula Sigma :=
mkbinformula _ (rformula_replace t phi) (rformula_replace_prop t phi).

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
| mkrooted: slformula Sigma -> binrformula Sigma -> rooted Sigma.

Arguments mkrooted {_} _ _.

Definition slbin (Sigma: signature): slformula Sigma := slhasval (id x) (id y).

Definition root {Sigma: signature} (p: rsentence Sigma): rooted Sigma := mkrooted (slbin Sigma) p.

Inductive sequent (Sigma: signature): Set :=
| mksequent: list (rooted Sigma) -> list (rooted Sigma) -> sequent Sigma.
