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

Proposition satisfy_lor_elim (h h': heap) (s s': store) (p q r: assert):
  satisfy h s (lor p q) -> (satisfy h s p -> satisfy h' s' r) ->
  (satisfy h s q -> satisfy h' s' r) -> satisfy h' s' r.
simpl; intros.
apply satisfy_stable. intro.
apply H. split.
intro. apply H0 in H3. apply H2; assumption.
intro. apply H1 in H3. apply H2; assumption.
Qed.

Proposition satisfy_lor_elim_gen (h: heap) (s: store) (p q: assert) (P: Prop):
  (~~P -> P) -> satisfy h s (lor p q) -> (satisfy h s p -> P) -> (satisfy h s q -> P) -> P.
intros.
apply H. intro.
apply H0. fold satisfy. split.
intro. apply H3. apply H1. assumption.
intro. apply H3. apply H2. assumption.
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

Proposition satisfy_hasval (h: heap) (s: store) (e1 e2: expr):
  satisfy h s (hasval e1 e2) <-> h (e1 s) = e2 s.
split; intro.
simpl in H. destruct H.
apply H0.
simpl. split.
apply dom_spec. intro.
rewrite H in H0. inversion H0.
assumption.
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

Proposition satisfy_lnot_hasvaldash (h: heap) (s: store) (x: V):
  satisfy h s (lnot (hasvaldash x)) <-> ~dom h (s x).
rewrite satisfy_lnot.
apply not_iff_compat.
apply satisfy_hasvaldash.
Qed.

Proposition satisfy_sand_intro (h h1 h2: heap) (s: store) (p q: assert):
  Partition h h1 h2 -> satisfy h1 s p -> satisfy h2 s q -> satisfy h s (sand p q).
intros.
intro. specialize H2 with h1 h2.
apply H2; clear H2. split.
assumption. split; assumption.
Qed.

Proposition satisfy_sand_elim (h h': heap) (s s': store) (p q r: assert):
  satisfy h s (sand p q) ->
  (forall h1 h2, Partition h h1 h2 -> satisfy h1 s p -> satisfy h2 s q -> satisfy h' s' r) ->
  satisfy h' s' r.
intros.
apply satisfy_stable. intro.
apply H; clear H; fold satisfy.
intros. intro. destruct H. destruct H2.
apply H1. eapply H0. apply H. assumption. assumption.
Qed.

Proposition satisfy_simp (h: heap) (s: store) (p q: assert):
  satisfy h s (simp p q) <->
  (forall h' h'', Partition h'' h h' -> satisfy h' s p -> satisfy h'' s q).
split; intro.
intros.
eapply H. apply H0. apply H1.
simpl. intros. eapply H.
apply H0. apply H1.
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

Proposition store_substitution_lemma_p1 (p: assert) (e: expr):
  (forall (x: V) (h: heap) (s: store) (ps: assert),
      asub p x e = Some ps -> satisfy h s ps <-> satisfy h (store_update s x (e s)) p) ->
  forall (x: V) (h: heap) (s : store) (ps: assert),
    ~In x (avar p) -> asub p x e = Some ps ->
    satisfy h s ps <-> satisfy h s p.
intros.
pose proof (acond h p s (store_update s x (e s))).
rewrite H2. apply H. assumption.
intro; intro.
unfold store_update.
destruct (Nat.eq_dec x x0).
exfalso; apply H0. rewrite e0; assumption.
reflexivity.
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
  eapply store_substitution_lemma_p1; [apply IHp| |apply H].
  apply fresh_notIn.
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
  eapply store_substitution_lemma_p1; [apply IHp| |apply H].
  apply fresh_notIn.
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

Proposition heap_update_substitution_lemma_p1 (h: heap) (s: store) (x: V) (e e0 e1: expr):
  satisfy h s (lor (land (equals x e0) (equals e e1)) (land (lnot (equals x e0)) (hasval e0 e1))) <->
  (s x = e0 s -> e s = e1 s) /\ (s x <> e0 s -> h (e0 s) = e1 s).
split; intro.
- eapply satisfy_lor_elim_gen; [|apply H| |].
  split; intro.
  + destruct (Z.eq_dec (e s) (e1 s)).
    assumption.
    exfalso. apply H0.
    intro. destruct H2. apply n. apply H2. assumption.
  + cut (h (e0 s) = Some (e1 s)). intro. apply H2.
    destruct (h (e0 s)).
    f_equal.
    destruct (Z.eq_dec z (e1 s)).
    assumption.
    1,2: exfalso; apply H0.
    1,2: intro; destruct H2.
    apply n.
    1,2: pose proof (H3 H1); inversion H4.
    reflexivity.
  + intro.
    rewrite satisfy_land in H0. destruct H0.
    rewrite satisfy_equals in H0.
    rewrite satisfy_equals in H1.
    split; intro. assumption.
    exfalso. apply H2. assumption.
  + intro.
    rewrite satisfy_land in H0. destruct H0.
    rewrite satisfy_lnot in H0.
    rewrite satisfy_equals in H0.
    rewrite satisfy_hasval in H1.
    split; intro.
    exfalso. apply H0. assumption. assumption.
- destruct H.
  destruct (Z.eq_dec (s x) (e0 s)).
  + apply satisfy_lor_intro1.
    rewrite satisfy_land. split; rewrite satisfy_equals.
    assumption. apply H. assumption.
  + apply satisfy_lor_intro2.
    rewrite satisfy_land. split.
    rewrite satisfy_lnot. rewrite satisfy_equals. assumption.
    rewrite satisfy_hasval. apply H0. assumption.
Qed.

Proposition heap_update_substitution_lemma_p2 (h: heap) (s: store) (x: V) (e e0 e1: expr):
  (s x = e0 s -> e s = e1 s) /\ (s x <> e0 s -> h (e0 s) = e1 s) <->
  dom (heap_update h (s x) (e s)) (e0 s) /\ (heap_update h (s x) (e s)) (e0 s) = e1 s.
split; intro.
- split. apply dom_spec.
  destruct (Z.eq_dec (s x) (e0 s)).
  rewrite e2.
  rewrite heap_update_spec1. intro. inversion H0.
  rewrite heap_update_spec2. intro. destruct H. rewrite H1 in H0. inversion H0.
    assumption. assumption.
  destruct (Z.eq_dec (s x) (e0 s)).
  rewrite e2.
  rewrite heap_update_spec1. destruct H. rewrite H. reflexivity. assumption.
  rewrite heap_update_spec2. destruct H. apply H0. assumption. assumption.
- destruct H.
  split; intro.
  rewrite H1 in H0. rewrite heap_update_spec1 in H0. inversion H0. reflexivity.
  rewrite heap_update_spec2 in H0; assumption.
Qed.

Proposition heap_update_substitution_lemma_p3 (s: store) (x v: V) (e: expr) (x1: Z):
  ~ In v (x :: evar e) -> store_update s v x1 x = s x /\ e (store_update s v x1) = e s.
intro. split.
unfold store_update.
destruct (Nat.eq_dec v x).
exfalso. rewrite e0 in H. apply H. left. reflexivity. reflexivity.
apply econd. intro. intro. unfold store_update.
destruct (Nat.eq_dec v x0).
exfalso. apply H. right. rewrite e0. assumption.
reflexivity.
Qed.

Proposition heap_update_substitution_lemma_p4 (h h1 h2: heap) (k v: Z):
  Partition h h1 h2 -> ~ dom h2 k ->
  Partition (heap_update h k v) (heap_update h1 k v) h2.
intros.
pose proof (Partition_intro (heap_update h1 k v) h2).
destruct H1.
intro. intro. destruct H1.
destruct (Z.eq_dec k0 k).
rewrite e in H2. apply H0; assumption.
rewrite heap_update_dom2 in H1.
eapply Partition_spec4. apply H. split; [apply H1 | apply H2].
intro. rewrite H3 in n. apply n; reflexivity.
pose proof (heap_ext x (heap_update h k v)).
destruct H2. intro.
destruct (dom_dec h1 n).
pose proof (Partition_spec1 _ _ _ H1 n).
pose proof (Partition_spec1 _ _ _ H n H2).
destruct (Z.eq_dec n k).
rewrite H3. rewrite e.
rewrite heap_update_spec1. rewrite heap_update_spec1. reflexivity.
rewrite e. apply heap_update_dom1.
rewrite heap_update_spec2. rewrite H3.
rewrite heap_update_spec2. symmetry; assumption.
intro. apply n0. auto.
apply heap_update_dom2; auto. auto.
destruct (dom_dec h2 n).
assert (k <> n). intro. rewrite <- H4 in H3. apply H0. assumption.
rewrite heap_update_spec2; auto.
pose proof (Partition_spec2 _ _ _ H1 _ H3).
pose proof (Partition_spec2 _ _ _ H _ H3).
rewrite H5. auto.
destruct (Z.eq_dec n k).
pose proof (Partition_spec1 _ _ _ H1 k).
rewrite e. rewrite H4.
rewrite heap_update_spec1.
rewrite heap_update_spec1. reflexivity.
apply heap_update_dom1.
rewrite heap_update_spec2.
pose proof (Partition_spec3 _ _ _ H1 n).
pose proof (Partition_spec3 _ _ _ H n).
rewrite H5; try assumption.
rewrite H4; try assumption. reflexivity.
intro.
apply heap_update_dom2 in H6. apply H2; assumption.
auto. auto. assumption.
Qed.

Proposition heap_update_substitution_lemma_p5 (h h1 h2: heap) (k v: Z):
  Partition (heap_update h k v) h1 h2 ->
  (exists h1', Partition h h1' h2 /\ h1 = heap_update h1' k v /\ ~dom h2 k) \/
  (exists h2', Partition h h1 h2' /\ h2 = heap_update h2' k v /\ ~dom h1 k).
Admitted.

Proposition heap_update_substitution_lemma_p6 (h h' h'': heap) (k v: Z):
  Partition h'' (heap_update h k v) h' ->
  exists hh, h'' = heap_update hh k v /\ Partition hh h h'.
Admitted.

Proposition heap_update_substitution_lemma_p7 (h h' h'': heap) (k v: Z):
  Partition h'' h h' -> ~ dom h' k ->
  Partition (heap_update h'' k v) (heap_update h k v) h'.
Admitted.

Lemma heap_update_substitution_lemma (h: heap) (s: store) (p: assert) (x: V) (e: expr):
  forall ps, asub_heap_update p x e = Some ps ->
    (satisfy h s ps <-> satisfy (heap_update h (s x) (e s)) s p).
generalize dependent s; generalize dependent h;
induction p; intros.
- inversion H; unfold satisfy; apply iff_refl.
- inversion H.
  rewrite heap_update_substitution_lemma_p1.
  rewrite heap_update_substitution_lemma_p2.
  apply iff_refl.
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
- unfold asub_heap_update in H; fold asub_heap_update in H.
  destruct (in_dec Nat.eq_dec v (x :: evar e)).
  inversion H.
  apply option_app_elim in H; destruct H; destruct H.
  inversion H0; clear H0.
  simpl.
  apply iff_split_not_forall_not; intro.
  specialize IHp with h (store_update s v x1) x0.
  apply IHp in H. rewrite H.
  pose proof (heap_update_substitution_lemma_p3 s x v e x1 n).
  destruct H0. rewrite H0. rewrite H1.
  apply iff_refl.
- unfold asub_heap_update in H; fold asub_heap_update in H.
  destruct (in_dec Nat.eq_dec v (x :: evar e)).
  inversion H.
  apply option_app_elim in H; destruct H; destruct H.
  inversion H0; clear H0.
  simpl.
  apply iff_split_forall; intro.
  specialize IHp with h (store_update s v x1) x0.
  apply IHp in H. rewrite H.
  pose proof (heap_update_substitution_lemma_p3 s x v e x1 n).
  destruct H0. rewrite H0. rewrite H1.
  apply iff_refl.
- unfold asub_heap_update in H; fold asub_heap_update in H.
  apply option_app_elim in H; destruct H; destruct H.
  apply option_app_elim in H0; destruct H0; destruct H0.
  inversion H1; clear H1.
  split; intro.
  + eapply satisfy_lor_elim; [|intro|intro]. apply H1.
    intro. apply H2; fold satisfy. intros.
    intro. destruct H5. destruct H6. destruct H7.
    specialize H4 with (heap_update h1 (s x) (e s)) h2.
    apply H4; clear H4. split.
    apply satisfy_lnot_hasvaldash in H8.
    apply heap_update_substitution_lemma_p4; assumption.
    split.
    rewrite <- IHp1. apply H6. assumption. assumption.
    (* other direction is similar *)
    intro. apply H2; fold satisfy. intros.
    intro. destruct H5. destruct H6. destruct H6.
    specialize H4 with h1 (heap_update h2 (s x) (e s)).
    apply H4; clear H4. split.
    apply satisfy_lnot_hasvaldash in H8.
    apply Partition_comm.
    apply heap_update_substitution_lemma_p4.
    apply Partition_comm; assumption. assumption.
    split. assumption.
    rewrite <- IHp2. apply H7. assumption.
  + eapply satisfy_sand_elim. apply H1.
    intros.
    apply heap_update_substitution_lemma_p5 in H2.
    destruct H2; destruct H2. destruct H2. destruct H6.
    apply satisfy_lor_intro1.
    eapply satisfy_sand_intro. apply H2.
    rewrite H6 in H4.
    rewrite <- IHp1 in H4. apply H4. assumption.
    apply satisfy_land. split. assumption.
    apply satisfy_lnot_hasvaldash. assumption.
    (* other direction is similar *)
    destruct H2. destruct H6.
    apply satisfy_lor_intro2.
    eapply satisfy_sand_intro. apply H2.
    apply satisfy_land. split. assumption.
    apply satisfy_lnot_hasvaldash. assumption.
    rewrite H6 in H5.
    rewrite <- IHp2 in H5. apply H5. assumption.
- unfold asub_heap_update in H; fold asub_heap_update in H.
  destruct (sublist_part_dec Nat.eq_dec (x :: evar e) (abound p1)).
  inversion H.
  apply option_app_elim in H; destruct H; destruct H.
  inversion H0; clear H0; clear dependent ps.
  rewrite satisfy_simp.
  rewrite satisfy_simp.
  split; intro; intros.
  + pose proof (heap_update_substitution_lemma_p6 _ _ _ _ _ H1). destruct H3. destruct H3.
    rewrite H3. rewrite <- IHp2; [|apply H]. eapply H0. apply H4.
    apply satisfy_land. split. assumption.
    apply satisfy_lnot_hasvaldash.
    eapply Partition_dom_right. apply H1.
    rewrite H3. apply heap_update_dom1. apply heap_update_dom1.
  + rewrite IHp2; [|apply H].
    specialize H0 with h' (heap_update h'' (s x) (e s)).
    rewrite satisfy_land in H2. destruct H2.
    apply satisfy_lnot_hasvaldash in H3.
    apply H0.
    apply heap_update_substitution_lemma_p7; assumption.
    assumption.
Qed.

Lemma heap_clear_substitution_lemma (h: heap) (s: store) (p: assert) (x: V):
  forall ps, asub_heap_clear p x = Some ps ->
    (satisfy h s ps <-> satisfy (heap_clear h (s x)) s p).
generalize dependent s; generalize dependent h;
induction p; intros.
- inversion H; unfold satisfy; apply iff_refl.
- simpl in H; inversion H; clear H H1.
  simpl.
  split; intro; destruct H.
  + destruct (Z.eq_dec (s x) (e s)).
    exfalso. assert (false = true) by (apply H; reflexivity). inversion H1.
    destruct H0.
    split. apply heap_clear_dom2; assumption.
    rewrite heap_clear_spec2; assumption.
  + destruct (Z.eq_dec (s x) (e s)).
    exfalso. eapply heap_clear_dom1. rewrite e1 in H. apply H.
    split. auto. split.
    eapply heap_clear_dom2. apply n. assumption.
    rewrite heap_clear_spec2 in H0; assumption.
- 
Admitted.

Corollary WPCSL_soundness_basic (p: assert) (x: V) (e: expr):
  forall ps, asub p x e = Some ps ->
    strong_partial_correct (mkhoare ps (basic x e) p).
Admitted.

Corollary WPCSL_soundness_lookup (p: assert) (x y: V) (e: expr):
  ~ In y (x :: aoccur p ++ evar e) ->
    forall ps, asub p x y = Some ps ->
      strong_partial_correct (mkhoare (lexists y (land (sand (hasval e y) true) ps)) (lookup x e) p).
Admitted.

Corollary WPCSL_soundness_mutation (p: assert) (x: V) (e: expr):
  forall ps, asub_heap_update p x e = Some ps ->
    strong_partial_correct (mkhoare (land (hasvaldash x) ps) (mutation x e) p).
Admitted.

Corollary WPCSL_soundness_new (p: assert) (x: V) (e: expr):
  ~ In x (evar e) ->
  forall ps, asub_heap_update p x e = Some ps ->
    strong_partial_correct (mkhoare (lforall x (limp (lnot (hasvaldash x)) ps)) (new x e) p).
Admitted.

Corollary WPCSL_soundness_dispose (p: assert) (x: V):
  forall ps, asub_heap_clear p x = Some ps ->
    strong_partial_correct (mkhoare (land (hasvaldash x) ps) (dispose x) p).
Admitted.

Theorem WPCSL_soundness: forall pSq, WPCSL pSq -> strong_partial_correct pSq.
intros. induction H.
apply WPCSL_soundness_basic; assumption.
apply WPCSL_soundness_lookup; assumption.
apply WPCSL_soundness_mutation; assumption.
apply WPCSL_soundness_new; assumption.
apply WPCSL_soundness_dispose; assumption.
Qed.

End Classical.
