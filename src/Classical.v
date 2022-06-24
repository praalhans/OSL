(* Copyright 2022 Centrum Wiskunde & Informatica *)

(* ON SEPERATION LOGIC *)
(* Author: Hans-Dieter A. Hiep *)

Require Export OnSeparationLogic.Language.

Module Classical (Export HS: HeapSig).

Module L := Language HS.
Include L.

Fixpoint satisfy (h: heap) (s: store) (p: assert): Prop :=
  match p with
  | test g => gval g s = true
  | hasval e e' => dom h (e s) /\ h (e s) = e' s
  | land p q => satisfy h s p /\ satisfy h s q
  | lor p q => ~(~satisfy h s p /\ ~satisfy h s q)
  | limp p q => satisfy h s p -> satisfy h s q
  | lforall x p => forall v, satisfy h (store_update s x v) p
  | lexists x p => ~forall v, ~satisfy h (store_update s x v) p
  | sand p q => ~forall h1 h2, ~(Partition h h1 h2 /\ satisfy h1 s p /\ satisfy h2 s q)
  | simp p q => forall h'' h', Partition h'' h h' -> satisfy h' s p -> satisfy h'' s q
  end.

Proposition satisfy_stable (h: heap) (s: store) (p: assert):
  ~~satisfy h s p -> satisfy h s p.
generalize dependent s. generalize dependent h.
induction p; intros h s; simpl.
- intro. destruct (g s). reflexivity.
  exfalso; apply H; intro; inversion H0.
- intro. destruct (dom_dec h (e s)).
  split. assumption.
  destruct (h (e s)).
  destruct (Z.eq_dec z (e0 s)).
  rewrite e1. reflexivity.
  exfalso. apply H. intro.
  destruct H1. apply n. inversion H2. reflexivity.
  exfalso. apply H. intro.
  destruct H1. inversion H2.
  exfalso. apply H. intro.
  destruct H1. apply H0. assumption.
- intro. split.
  apply IHp1. intro; apply H. intro; destruct H1. apply H0; assumption.
  apply IHp2. intro; apply H. intro; destruct H1. apply H0; assumption.
- intro. intro. apply H. intro. destruct H0.
  apply H1. split; assumption.
- intro. intro. apply IHp2. intro. apply H. intro.
  apply H1. apply H2. assumption.
- intro. intro. apply H. intro.
  apply H1. assumption.
- intro. intro.
  apply IHp. intro. apply H. intro.
  specialize H1 with v0. apply H0. assumption.
- intro. intro. apply H. intro. apply H1. apply H0.
- intros. apply IHp2. intro. apply H. intro.
  apply H2. eapply H3. apply H0. apply H1.
Qed.

(* emp <-> dom h = Empty_set Z *)

(* poitnsto <-> dom h = Singleton Z (eval e s) /\
      h (eval e s) = eval e' s *)

Proposition satisfy_land (h: heap) (s: store) (p q: assert):
  satisfy h s (land p q) <-> satisfy h s p /\ satisfy h s q.
simpl; split; intro; auto.
Qed.

Proposition satisfy_limp (h: heap) (s: store) (p q: assert):
  satisfy h s (limp p q) <-> (satisfy h s p -> satisfy h s q).
simpl; split; intro; auto.
Qed.

Proposition satisfy_lnot (h: heap) (s: store) (p: assert):
  satisfy h s (lnot p) <-> ~satisfy h s p.
simpl; split; intro; intro.
pose proof (H H0). inversion H1.
exfalso. apply H. assumption.
Qed.

Proposition satisfy_lor_intro1 (h: heap) (s: store) (p q: assert):
  satisfy h s p -> satisfy h s (lor p q).
simpl; intro. intro. destruct H0. apply H0; assumption.
Qed.

Proposition satisfy_lor_intro2 (h: heap) (s: store) (p q: assert):
  satisfy h s q -> satisfy h s (lor p q).
simpl; intro. intro. destruct H0. apply H1; assumption.
Qed.

Proposition satisfy_lor_elim (h: heap) (s: store) (p q r: assert):
  satisfy h s (lor p q) -> (satisfy h s p -> satisfy h s r) ->
  (satisfy h s q -> satisfy h s r) -> satisfy h s r.
simpl; intros.
apply satisfy_stable. intro.
apply H. split.
intro. apply H0 in H3. apply H2; assumption.
intro. apply H1 in H3. apply H2; assumption.
Qed.

Proposition satisfy_p_lor_not_p (h: heap) (s: store) (p: assert):
  satisfy h s (lor p (lnot p)).
simpl. intro. destruct H.
apply H0. intro. exfalso. apply H; assumption.
Qed.

Proposition satisfy_lforall (h: heap) (s: store) (x: V) (p: assert):
  satisfy h s (lforall x p) <-> forall v, satisfy h (store_update s x v) p.
simpl. tauto.
Qed.

Proposition satisfy_equals (h: heap) (s: store) (e0 e1: expr):
  satisfy h s (equals e0 e1) <-> e0 s = e1 s.
simpl. destruct (Z.eq_dec (eval e0 s) (eval e1 s)).
rewrite e. tauto. split. intro. inversion H.
intro. exfalso. apply n. assumption.
Qed.

Proposition satisfy_hasvaldash (h: heap) (s: store) (x: V):
  satisfy h s (hasvaldash x) <-> dom h (s x).
split; intro.
- unfold hasvaldash in H.
  remember (fresh (evar x)).
  simpl in H.
  destruct (dom_dec h (s x)). assumption.
  exfalso.
  apply H; clear H; intro; intro; destruct H.
  rewrite store_update_lookup_same in H1.
  rewrite store_update_lookup_diff in H1.
  apply H0. apply dom_spec. rewrite H1. intro. inversion H2.
  intro.
  rewrite H2 in Heqv.
  simpl in Heqv.
  pose proof (fresh_notIn (x :: nil)).
  rewrite <- Heqv in H3.
  apply H3. left. reflexivity.
- simpl. intro.
  remember (h (s x)). destruct o.
  specialize H0 with z.
  apply H0; clear H0.
  assert (store_update s (fresh (x :: nil)) z x = s x).
  rewrite store_update_lookup_diff. reflexivity.
  intro. pose proof (fresh_notIn (x :: nil)).
  apply H1. rewrite H0. left. reflexivity.
  rewrite H0.
  rewrite store_update_lookup_same.
  split; auto.
  eapply dom_spec. apply H. symmetry; assumption.
Qed.

Proposition acond (h: heap) (p: assert):
  forall (s t: store), eq_restr s t (avar p) ->
    (satisfy h s p <-> satisfy h t p).
generalize dependent h; induction p; intros; try tauto; simpl in *.
erewrite (gcond g); [|apply H]; apply iff_refl.
1,2,3,4: apply eq_restr_split in H; destruct H as (H0 & H1).
2,3,4: specialize IHp1 with h s t; specialize IHp2 with h s t; tauto.
pose proof (econd e s t) as G; rewrite G; try tauto;
pose proof (econd e0 s t) as I; rewrite I; tauto.
- apply not_iff_compat.
  apply forall_iff_compat; intro.
  split; intro.
  1: apply <- IHp.
  3: apply -> IHp.
  1,3: apply H0.
  1,2: intro; intro; unfold store_update.
  1,2: destruct (Nat.eq_dec v x0); try reflexivity.
  1,2: symmetry; apply H; apply In_remove; assumption.
- split; intros; specialize H0 with v0.
  1: apply <- IHp.
  3: apply -> IHp.
  1,3: apply H0.
  1,2: intro; intro; unfold store_update.
  1,2: destruct (Nat.eq_dec v x); try reflexivity.
  1,2: symmetry; apply H; apply In_remove; assumption.
- apply eq_restr_split in H; destruct H as (H & HH).
  apply not_iff_compat.
  apply forall2_iff_compat; intro.
  split; intros.
  1,2: destruct H0; destruct H1; split; [|split]; try assumption.
  specialize IHp1 with x s t.
  apply IHp1; assumption.
  specialize IHp2 with y s t.
  apply IHp2; assumption.
  specialize IHp1 with x t s.
  apply IHp1; try assumption.
  apply eq_restr_comm; assumption.
  specialize IHp2 with y t s.
  apply IHp2; try assumption.
  apply eq_restr_comm; assumption.
- apply eq_restr_split in H; destruct H as (H & HH).
  split; intros.
  1,2: specialize H0 with h'' h'.
  1,2: specialize (H0 H1).
  apply <- IHp1 in H2.
  specialize (H0 H2).
  apply -> IHp2 in H0.
  apply H0.
  1,2: assumption.
  apply -> IHp1 in H2.
  specialize (H0 H2).
  apply <- IHp2 in H0.
  apply H0.
  1,2: assumption.
Qed.

Definition validity (p: assert): Prop := forall h s, satisfy h s p.

Definition strong_partial_correct: hoare -> Prop := fun '(mkhoare p S q) =>
  forall h s, satisfy h s p ->
    ~bigstep S (h, s) None /\
    forall h' s', bigstep S (h, s) (Some (h', s')) -> satisfy h' s' q.

Example out_of_memory (x: V) (e: expr):
  strong_partial_correct (mkhoare (lforall x (hasvaldash x)) (new x e) false).
unfold strong_partial_correct.
intros.
split.
intro.
inversion H0.
intros.
inversion H0.
rewrite satisfy_lforall in H.
specialize (H n).
rewrite satisfy_hasvaldash in H.
rewrite store_update_lookup_same in H.
exfalso. apply H2. assumption.
Qed.

(* ============================================ *)
(* Weakest precondition axiomatization (WP-CSL) *)
(* ============================================ *)

Proposition satisfy_asub_fresh_general (h: heap) (s: store) (p ps: assert) (xs: list V) (e: expr):
  (forall x, In x (avar p) -> In x xs) -> asub p (fresh xs) e = Some ps ->
    satisfy h s ps <-> satisfy h s p.
intros.
generalize dependent ps; generalize dependent s; generalize dependent h; induction p; intros.
- inversion H0; clear H0.
  unfold satisfy. rewrite gval_gsub_fresh_general.
  apply iff_refl. assumption.
- inversion H0; clear H0.
  unfold satisfy.
  rewrite eval_esub_fresh_general.
  rewrite eval_esub_fresh_general.
  apply iff_refl.
  all: intros; apply H; simpl; apply in_or_app; auto.
- inversion H0; clear H0.
  apply option_app_elim in H2; destruct H2; destruct H0.
  apply option_app_elim in H1; destruct H1; destruct H1.
  inversion H2.
  simpl; apply iff_split_and;
  (apply IHp1 + apply IHp2); try assumption;
  intros; apply H; simpl; apply in_or_app; auto.
- inversion H0; clear H0.
  apply option_app_elim in H2; destruct H2; destruct H0.
  apply option_app_elim in H1; destruct H1; destruct H1.
  inversion H2.
  simpl; apply iff_split_not_and_not;
  (apply IHp1 + apply IHp2); try assumption;
  intros; apply H; simpl; apply in_or_app; auto.
- inversion H0; clear H0.
  apply option_app_elim in H2; destruct H2; destruct H0.
  apply option_app_elim in H1; destruct H1; destruct H1.
  inversion H2.
  simpl; apply iff_split_imp;
  (apply IHp1 + apply IHp2); try assumption;
  intros; apply H; simpl; apply in_or_app; auto.
- 
Admitted.

Proposition satisfy_asub_fresh (h: heap) (s: store) (p ps: assert) (e: expr):
  asub p (fresh (avar p)) e = Some ps -> satisfy h s ps <-> satisfy h s p.
apply satisfy_asub_fresh_general. auto.
Qed.

Lemma store_substitution_lemma (h: heap) (s: store) (p: assert) (x: V) (e: expr):
  forall ps, asub p x e = Some ps ->
    (satisfy h s ps <-> satisfy h (store_update s x (e s)) p).
generalize dependent s; generalize dependent h; generalize dependent x;
induction p; intros; simpl in H;
try (inversion H; unfold satisfy; apply iff_refl; fail).
- apply option_app_elim in H; destruct H; destruct H.
  apply option_app_elim in H0; destruct H0; destruct H0.
  inversion H1.
  simpl; apply iff_split_and.
  apply IHp1; assumption.
  apply IHp2; assumption.
- apply option_app_elim in H; destruct H; destruct H.
  apply option_app_elim in H0; destruct H0; destruct H0.
  inversion H1.
  simpl; apply iff_split_not_and_not.
  apply IHp1; assumption.
  apply IHp2; assumption.
- apply option_app_elim in H; destruct H; destruct H.
  apply option_app_elim in H0; destruct H0; destruct H0.
  inversion H1.
  simpl; apply iff_split_imp.
  apply IHp1; assumption.
  apply IHp2; assumption.
- destruct (in_dec Nat.eq_dec v (evar e)). inversion H.
  apply option_app_elim in H; destruct H; destruct H.
  inversion H0; clear H0 H2.
  simpl.
  apply iff_split_not_forall_not.
  destruct (Nat.eq_dec x v); intro.
  rewrite e0.
  rewrite store_update_collapse.
  apply (satisfy_asub_fresh h (store_update s v x1) _ _ _ H).
  rewrite store_update_swap; try assumption.
  rewrite eval_store_update_notInVar with (e := e) (x := v) (v := x1); try assumption.
  apply IHp; assumption.
- destruct (in_dec Nat.eq_dec v (evar e)). inversion H.
  apply option_app_elim in H; destruct H; destruct H.
  inversion H0; clear H0 H2.
  simpl.
  apply iff_split_forall.
  destruct (Nat.eq_dec x v); intro.
  rewrite e0.
  rewrite store_update_collapse.
  apply (satisfy_asub_fresh h (store_update s v x1) _ _ _ H).
  rewrite store_update_swap; try assumption.
  rewrite eval_store_update_notInVar with (e := e) (x := v) (v := x1); try assumption.
  apply IHp; assumption.
- apply option_app_elim in H; destruct H; destruct H.
  apply option_app_elim in H0; destruct H0; destruct H0.
  inversion H1.
  simpl.
  apply iff_split_and_not_forall_not.
  intro; apply IHp1; assumption.
  intro; apply IHp2; assumption.
- apply option_app_elim in H; destruct H; destruct H.
  apply option_app_elim in H0; destruct H0; destruct H0.
  inversion H1.
  simpl.
  apply iff_split_imp_forall.
  intro; apply IHp1; assumption.
  intro; apply IHp2; assumption.
Qed.

Corollary WPCSL_soundness_basic (p: assert) (x: V) (e: expr):
  forall ps, asub p x e = Some ps ->
    strong_partial_correct (mkhoare ps (basic x e) p).
Admitted.

Corollary WPCSL_soundness_lookup (p: assert) (x y: V) (e: expr):
  ~ In y (x :: aoccur p ++ evar e) ->
    forall ps, asub p x y = Some ps ->
      strong_partial_correct (mkhoare (lexists y (land (sand (hasval e y) true) ps)) (lookup x e) p).
Admitted.

Theorem WPCSL_soundness: forall pSq, WPCSL pSq -> strong_partial_correct pSq.
intros. induction H.
apply WPCSL_soundness_basic; assumption.
apply WPCSL_soundness_lookup; assumption.
Qed.

End Classical.
