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

Proposition satisfy_lexists (h: heap) (s: store) (x: V) (p: assert):
  satisfy h s (lexists x p) <-> ~forall v, ~satisfy h (store_update s x v) p.
simpl. tauto.
Qed.

Proposition satisfy_lexists_intro (h: heap) (s: store) (x: V) (p: assert) (n: Z):
  satisfy h (store_update s x n) p -> satisfy h s (lexists x p).
intro. rewrite satisfy_lexists. intro.
eapply H0. apply H.
Qed.

Proposition satisfy_lexists_elim (h h': heap) (s s': store) (x: V) (p r: assert):
  satisfy h s (lexists x p) -> (forall n, satisfy h (store_update s x n) p -> satisfy h' s' r) ->
  satisfy h' s' r.
intros.
apply satisfy_stable. intro.
rewrite satisfy_lexists in H.
apply H. intros.
intro. apply H1. eapply H0. apply H2.
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

Proposition satisfy_hasvaldash (h: heap) (s: store) (e: expr):
  satisfy h s (hasvaldash e) <-> dom h (e s).
split; intro.
- unfold hasvaldash in H.
  remember (fresh (evar e)).
  simpl in H.
  destruct (dom_dec h (e s)). assumption.
  exfalso.
  apply H; clear H; intro; intro; destruct H.
  assert (e s = e (store_update s v v0)).
  apply econd. intro. intro.
  destruct (Nat.eq_dec x v). rewrite e0 in H2. rewrite Heqv in H2.
  exfalso. eapply fresh_notIn. apply H2.
  rewrite store_update_lookup_diff; auto.
  rewrite <- H2 in H. apply H0. assumption.
- simpl. intro.
  remember (h (e s)). destruct o.
  assert (e s = e (store_update s (fresh (evar e)) z)). {
    apply econd. intro. intro.
    rewrite store_update_lookup_diff; auto. intro.
    rewrite <- H2 in H1. eapply fresh_notIn. apply H1. }
  specialize H0 with z.
  apply H0; clear H0.
  rewrite <- H1.
  rewrite store_update_lookup_same.
  split.
  apply dom_spec. intro.
  rewrite H0 in Heqo. inversion Heqo.
  auto.
  apply dom_spec in H. apply H; auto.
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
rewrite satisfy_hasvaldash in H. simpl in H.
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
intros.
pose proof (heap_update_dom1 h k v); pose proof (Partition_dom_split _ _ _ _ H H0); destruct H1.
- left. remember (h k); destruct o.
  + exists (heap_update h1 k z).
    pose proof (Partition_dom_right _ _ _ k H H0 H1).
    split.
    pose proof (Partition_intro (heap_update h1 k z) h2). destruct H3.
    intros. intro. destruct H3.
    destruct (Z.eq_dec k0 k). rewrite e in H4.
    eapply Partition_spec4. apply H. split. apply H1. apply H4.
    apply heap_update_dom2 in H3; auto.
    eapply Partition_spec4. apply H. split. apply H3. apply H4.
    pose proof (heap_ext h x). rewrite H4. assumption.
    clear H4. intros.
    destruct (Z.eq_dec n k).
    rewrite e. rewrite <- Heqo.
    erewrite <- (heap_update_spec1 h1 k). symmetry.
    apply Partition_spec1 with (h2 := h2); auto. apply heap_update_dom1.
    rewrite <- heap_update_spec2 with (k := k) (v := v); auto.
    destruct (dom_dec h2 n).
    rewrite Partition_spec2 with (h1 := h1) (h2 := h2); auto.
    symmetry. eapply Partition_spec2. apply H3. assumption.
    destruct (dom_dec h1 n).
    rewrite Partition_spec1 with (h1 := h1) (h2 := h2); auto.
    rewrite <- heap_update_spec2 with (k := k) (v := z); auto. symmetry.
    eapply Partition_spec1. apply H3. apply heap_update_dom2; auto.
    rewrite Partition_spec3 with (h1 := h1) (h2 := h2); auto.
    symmetry. eapply Partition_spec3. apply H3.
    rewrite heap_update_dom2; auto. auto.
    split; auto.
    apply heap_ext; intro.
    destruct (Z.eq_dec n k).
    rewrite e. rewrite heap_update_spec1.
    erewrite <- Partition_spec1. 2: apply H.
    apply heap_update_spec1. auto.
    rewrite heap_update_spec2; auto.
    rewrite heap_update_spec2; auto.
  + exists (heap_clear h1 k).
    pose proof (Partition_dom_right _ _ _ k H H0 H1).
    assert (h1 k = v). { pose proof (Partition_spec1 _ _ _ H k H1).
    rewrite heap_update_spec1 in H3. inversion H3. reflexivity. }
    split.
    pose proof (Partition_intro (heap_clear h1 k) h2). destruct H4.
    intros. intro. destruct H4.
    destruct (Z.eq_dec k0 k). rewrite e in H4.
    eapply heap_clear_dom1. apply H4.
    rewrite heap_clear_dom2 in H4.
    eapply Partition_spec4. apply H. split. apply H4. apply H5.
    intro. apply n. auto.
    pose proof (heap_ext h x).
    rewrite H5. assumption. clear H5. intro.
    destruct (Z.eq_dec n k).
    rewrite e. rewrite <- Heqo.
    symmetry. eapply Partition_spec3. apply H4.
    apply heap_clear_dom1. assumption.
    rewrite <- heap_update_spec2 with (k := k) (v := v); auto.
    destruct (dom_dec h2 n).
    rewrite Partition_spec2 with (h1 := h1) (h2 := h2); try assumption.
    symmetry. eapply Partition_spec2. apply H4. assumption.
    destruct (dom_dec h1 n).
    rewrite Partition_spec1 with (h1 := h1) (h2 := h2); auto.
    symmetry. rewrite <- (heap_clear_spec2 h1 k); auto.
    erewrite Partition_spec1. reflexivity. apply H4.
    apply heap_clear_dom2; auto.
    rewrite Partition_spec3 with (h1 := h1) (h2 := h2); auto.
    rewrite Partition_spec3 with (h1 := heap_clear h1 k) (h2 := h2); auto.
    rewrite heap_clear_dom2; auto.
    split.
    apply heap_ext; intro. destruct (Z.eq_dec k n).
    rewrite <- e. rewrite heap_update_spec1. rewrite H3. reflexivity.
    rewrite heap_update_spec2; auto. rewrite heap_clear_spec2; auto.
    assumption.
- right.
  pose proof (Partition_comm _ _ _ H). clear H. rename H2 into H.
  remember (h k); destruct o.
  + exists (heap_update h2 k z).
    pose proof (Partition_dom_right _ _ _ k H H0 H1).
    split.
    pose proof (Partition_intro (heap_update h2 k z) h1). destruct H3.
    intros. intro. destruct H3.
    destruct (Z.eq_dec k0 k). rewrite e in H4.
    eapply Partition_spec4. apply H. split. apply H1. apply H4.
    apply heap_update_dom2 in H3; auto.
    eapply Partition_spec4. apply H. split. apply H3. apply H4.
    pose proof (heap_ext h x). rewrite H4. apply Partition_comm. assumption.
    clear H4. intros.
    destruct (Z.eq_dec n k).
    rewrite e. rewrite <- Heqo.
    erewrite <- (heap_update_spec1 h2 k). symmetry.
    apply Partition_spec1 with (h2 := h1); auto. apply heap_update_dom1.
    rewrite <- heap_update_spec2 with (k := k) (v := v); auto.
    destruct (dom_dec h1 n).
    rewrite Partition_spec2 with (h1 := h2) (h2 := h1); auto.
    symmetry. eapply Partition_spec2. apply H3. assumption.
    destruct (dom_dec h2 n).
    rewrite Partition_spec1 with (h1 := h2) (h2 := h1); auto.
    rewrite <- heap_update_spec2 with (k := k) (v := z); auto. symmetry.
    eapply Partition_spec1. apply H3. apply heap_update_dom2; auto.
    rewrite Partition_spec3 with (h1 := h2) (h2 := h1); auto.
    symmetry. eapply Partition_spec3. apply H3.
    rewrite heap_update_dom2; auto. auto.
    split; auto.
    apply heap_ext; intro.
    destruct (Z.eq_dec n k).
    rewrite e. rewrite heap_update_spec1.
    erewrite <- Partition_spec1. 2: apply H.
    apply heap_update_spec1. auto.
    rewrite heap_update_spec2; auto.
    rewrite heap_update_spec2; auto.
  + exists (heap_clear h2 k).
    pose proof (Partition_dom_right _ _ _ k H H0 H1).
    assert (h2 k = v). { pose proof (Partition_spec1 _ _ _ H k H1).
    rewrite heap_update_spec1 in H3. inversion H3. reflexivity. }
    split.
    apply Partition_comm.
    pose proof (Partition_intro (heap_clear h2 k) h1). destruct H4.
    intros. intro. destruct H4.
    destruct (Z.eq_dec k0 k). rewrite e in H4.
    eapply heap_clear_dom1. apply H4.
    rewrite heap_clear_dom2 in H4.
    eapply Partition_spec4. apply H. split. apply H4. apply H5.
    intro. apply n. auto.
    pose proof (heap_ext h x).
    rewrite H5. assumption. clear H5. intro.
    destruct (Z.eq_dec n k).
    rewrite e. rewrite <- Heqo.
    symmetry. eapply Partition_spec3. apply H4.
    apply heap_clear_dom1. assumption.
    rewrite <- heap_update_spec2 with (k := k) (v := v); auto.
    destruct (dom_dec h1 n).
    rewrite Partition_spec2 with (h1 := h2) (h2 := h1); try assumption.
    symmetry. eapply Partition_spec2. apply H4. assumption.
    destruct (dom_dec h2 n).
    rewrite Partition_spec1 with (h1 := h2) (h2 := h1); auto.
    symmetry. rewrite <- (heap_clear_spec2 h2 k); auto.
    erewrite Partition_spec1. reflexivity. apply H4.
    apply heap_clear_dom2; auto.
    rewrite Partition_spec3 with (h1 := h2) (h2 := h1); auto.
    rewrite Partition_spec3 with (h1 := heap_clear h2 k) (h2 := h1); auto.
    rewrite heap_clear_dom2; auto.
    split.
    apply heap_ext; intro. destruct (Z.eq_dec k n).
    rewrite <- e. rewrite heap_update_spec1. rewrite H3. reflexivity.
    rewrite heap_update_spec2; auto. rewrite heap_clear_spec2; auto.
    assumption.
Qed.

Proposition heap_update_substitution_lemma_p6 (h h' h'': heap) (k v: Z):
  Partition h'' (heap_update h k v) h' ->
  exists hh, h'' = heap_update hh k v /\ Partition hh h h'.
intros. remember (h k); destruct o.
- exists (heap_update h'' k z).
  split.
  + apply heap_ext; intro.
    destruct (Z.eq_dec n k).
    rewrite e.
    rewrite heap_update_spec1.
    rewrite (Partition_spec1 _ _ _ H).
    apply heap_update_spec1.
    apply heap_update_dom1.
    rewrite heap_update_spec2; auto.
    rewrite heap_update_spec2; auto.
  + pose proof (Partition_intro h h').
    destruct H0. intro. intro. destruct H0.
    eapply Partition_spec4. apply H. split; [| apply H1].
    destruct (Z.eq_dec k k0).
    rewrite e.
    apply heap_update_dom1.
    apply heap_update_dom2; auto.
    pose proof (heap_ext (heap_update h'' k z) x).
    rewrite H1. assumption. clear H1. intros.
    destruct (Z.eq_dec n k). rewrite e.
    rewrite heap_update_spec1. symmetry.
    rewrite Heqo. eapply Partition_spec1. apply H0.
    rewrite dom_spec. intro. rewrite <- Heqo in H1. inversion H1.
    rewrite heap_update_spec2; auto.
    destruct (dom_dec h' n).
    rewrite Partition_spec2 with (h1 := heap_update h k v) (h2 := h'); auto.
    symmetry. apply Partition_spec2 with (h1 := h) (h2 := h'); auto.
    destruct (dom_dec h n).
    rewrite Partition_spec1 with (h1 := heap_update h k v) (h2 := h'); auto.
    rewrite heap_update_spec2; auto.
    symmetry. apply Partition_spec1 with (h1 := h) (h2 := h'); auto.
    apply heap_update_dom2; auto.
    rewrite Partition_spec3 with (h1 := heap_update h k v) (h2 := h'); auto.
    symmetry. apply Partition_spec3 with (h1 := h) (h2 := h'); auto.
    rewrite heap_update_dom2; auto.
- exists (heap_clear h'' k).
  split.
  + apply heap_ext; intro.
    destruct (Z.eq_dec n k).
    rewrite e.
    rewrite heap_update_spec1.
    rewrite (Partition_spec1 _ _ _ H).
    apply heap_update_spec1.
    apply heap_update_dom1.
    rewrite heap_update_spec2; auto.
    rewrite heap_clear_spec2; auto.
  + pose proof (Partition_intro h h').
    destruct H0. intro. intro. destruct H0.
    eapply Partition_spec4. apply H. split; [| apply H1].
    destruct (Z.eq_dec k k0).
    rewrite e.
    apply heap_update_dom1.
    apply heap_update_dom2; auto.
    pose proof (heap_ext (heap_clear h'' k) x).
    rewrite H1. assumption. clear H1. intros.
    destruct (Z.eq_dec n k). rewrite e.
    rewrite heap_clear_spec1. symmetry.
    eapply Partition_spec3. apply H0.
    rewrite dom_spec; auto.
    eapply Partition_dom_right. apply H.
    rewrite dom_spec. intro.
    rewrite Partition_spec1 with (h1 := heap_update h k v) (h2 := h') in H1; auto.
    rewrite heap_update_spec1 in H1. inversion H1.
    apply heap_update_dom1. apply heap_update_dom1.
    rewrite heap_clear_spec2; auto.
    destruct (dom_dec h' n).
    rewrite Partition_spec2 with (h1 := heap_update h k v) (h2 := h'); auto.
    symmetry. apply Partition_spec2 with (h1 := h) (h2 := h'); auto.
    destruct (dom_dec h n).
    rewrite Partition_spec1 with (h1 := heap_update h k v) (h2 := h'); auto.
    rewrite heap_update_spec2; auto.
    symmetry. apply Partition_spec1 with (h1 := h) (h2 := h'); auto.
    apply heap_update_dom2; auto.
    rewrite Partition_spec3 with (h1 := heap_update h k v) (h2 := h'); auto.
    symmetry. apply Partition_spec3 with (h1 := h) (h2 := h'); auto.
    rewrite heap_update_dom2; auto.
Qed.

Proposition heap_update_substitution_lemma_p7 (h h' h'': heap) (k v: Z):
  Partition h'' h h' -> ~ dom h' k ->
  Partition (heap_update h'' k v) (heap_update h k v) h'.
intros.
pose proof (Partition_intro (heap_update h k v) h').
destruct H1. intros. intro. destruct H1.
destruct (Z.eq_dec k k0). rewrite <- e in H2. auto.
rewrite heap_update_dom2 in H1; auto.
eapply Partition_spec4. apply H. split. apply H1. apply H2.
pose proof (heap_ext x (heap_update h'' k v)). destruct H2; auto.
intros.
destruct (Z.eq_dec n k).
rewrite e.
rewrite heap_update_spec1; auto.
rewrite <- heap_update_spec1 with (h := h) (k := k).
apply Partition_spec1 with (h2 := h'); auto.
apply heap_update_dom1.
rewrite heap_update_spec2; auto.
destruct (dom_dec h' n).
rewrite Partition_spec2 with (h1 := heap_update h k v) (h2 := h'); auto.
symmetry. eapply Partition_spec2. apply H. auto.
destruct (dom_dec h n).
rewrite Partition_spec1 with (h1 := heap_update h k v) (h2 := h'); auto.
rewrite heap_update_spec2; auto. symmetry.
eapply Partition_spec1. apply H. auto.
apply heap_update_dom2; auto.
rewrite Partition_spec3 with (h1 := heap_update h k v) (h2 := h'); auto.
symmetry. eapply Partition_spec3. apply H. auto. auto.
rewrite heap_update_dom2; auto.
Qed.

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

Proposition heap_clear_substitution_lemma_p1 (h h1 h2: heap) (k: Z):
  Partition h h1 h2 ->
  Partition (heap_clear h k) (heap_clear h1 k) (heap_clear h2 k).
intros.
pose proof (Partition_intro (heap_clear h1 k) (heap_clear h2 k)).
destruct H0. intros. intro. destruct H0.
destruct (Z.eq_dec k0 k).
rewrite e in H0. eapply heap_clear_dom1. apply H0.
rewrite heap_clear_dom2 in H0, H1; auto.
eapply Partition_spec4. apply H. split. apply H0. apply H1.
pose proof (heap_ext (heap_clear h k) x). destruct H1; auto.
intros.
destruct (Z.eq_dec n k).
rewrite e. rewrite heap_clear_spec1. symmetry.
eapply Partition_spec3. apply H0.
apply heap_clear_dom1. apply heap_clear_dom1.
rewrite heap_clear_spec2; auto.
destruct (dom_dec h1 n).
rewrite Partition_spec1 with (h1 := h1) (h2 := h2); auto.
rewrite <- heap_clear_spec2 with (k := k); auto. symmetry.
eapply Partition_spec1. apply H0.
apply heap_clear_dom2; auto.
destruct (dom_dec h2 n).
rewrite Partition_spec2 with (h1 := h1) (h2 := h2); auto.
rewrite <- heap_clear_spec2 with (k := k); auto.
symmetry. eapply Partition_spec2. apply H0.
apply heap_clear_dom2; auto.
rewrite Partition_spec3 with (h1 := h1) (h2 := h2); auto.
symmetry. eapply Partition_spec3. apply H0.
rewrite heap_clear_dom2; auto.
rewrite heap_clear_dom2; auto.
Qed.

Proposition heap_clear_substitution_lemma_p2 (h h1 h2: heap) (k: Z):
  Partition (heap_clear h k) h1 h2 ->
  exists h11 h22, Partition h h11 h22 /\ h1 = heap_clear h11 k /\ h2 = heap_clear h22 k.
intros.
remember (h k); destruct o.
- exists (heap_update h1 k z). exists h2.
  split.
  pose proof (Partition_intro (heap_update h1 k z) h2).
  destruct H0. intros. intro. destruct H0.
  destruct (Z.eq_dec k k0).
  rewrite <- e in H1.
  pose proof (Partition_spec2 _ _ _ H _ H1).
  rewrite dom_spec in H1.
  rewrite heap_clear_spec1 in H2; auto.
  rewrite heap_update_dom2 in H0; auto.
  eapply Partition_spec4. apply H. split. apply H0. apply H1.
  pose proof (heap_ext x h). destruct H1; auto. intros.
  destruct (Z.eq_dec k n).
  rewrite <- e.
  rewrite Partition_spec1 with (h1 := heap_update h1 k z) (h2 := h2); auto.
  rewrite heap_update_spec1; auto.
  apply heap_update_dom1.
  destruct (dom_dec h1 n).
  rewrite Partition_spec1 with (h1 := heap_update h1 k z) (h2 := h2); auto.
  rewrite heap_update_spec2; auto.
  symmetry. rewrite <- heap_clear_spec2 with (k := k); auto.
  eapply Partition_spec1; auto. apply H.
  apply heap_update_dom2; auto.
  destruct (dom_dec h2 n).
  rewrite Partition_spec2 with (h1 := heap_update h1 k z) (h2 := h2); auto.
  symmetry. rewrite <- heap_clear_spec2 with (k := k); auto.
  eapply Partition_spec2; auto. apply H.
  rewrite Partition_spec3 with (h1 := heap_update h1 k z) (h2 := h2); auto.
  symmetry. rewrite <- heap_clear_spec2 with (k := k); auto.
  eapply Partition_spec3. apply H. auto. auto. rewrite heap_update_dom2; auto.
  split.
  apply heap_ext; intro.
  destruct (Z.eq_dec n k). rewrite e. rewrite heap_clear_spec1.
  remember (h1 k). destruct o; auto. exfalso.
  pose proof (Partition_spec1 _ _ _ H k). destruct H0.
  rewrite dom_spec. intro. rewrite <- Heqo0 in H0. inversion H0.
  rewrite heap_clear_spec1 in Heqo0. inversion Heqo0.
  rewrite heap_clear_spec2; auto.
  rewrite heap_update_spec2; auto.
  apply heap_ext; intro.
  destruct (Z.eq_dec n k). rewrite e. rewrite heap_clear_spec1.
  remember (h2 k). destruct o; auto. exfalso.
  pose proof (Partition_spec2 _ _ _ H k). destruct H0.
  rewrite dom_spec. intro. rewrite <- Heqo0 in H0. inversion H0.
  rewrite heap_clear_spec1 in Heqo0. inversion Heqo0.
  rewrite heap_clear_spec2; auto.
- exists h1. exists h2.
  split.
  pose proof (Partition_intro h1 h2). destruct H0.
  eapply Partition_spec4. apply H.
  pose proof (heap_ext x h). destruct H1; auto. intro.
  destruct (dom_dec h1 n).
  rewrite Partition_spec1 with (h1 := h1) (h2 := h2); auto.
  symmetry. rewrite <- heap_clear_spec2 with (k := k).
  eapply Partition_spec1; auto. apply H.
  intro. rewrite <- H2 in H1. pose proof (Partition_spec1 _ _ _ H k H1).
  rewrite heap_clear_spec1 in H3. rewrite dom_spec in H1; auto.
  destruct (dom_dec h2 n).
  rewrite Partition_spec2 with (h1 := h1) (h2 := h2); auto.
  symmetry. rewrite <- heap_clear_spec2 with (k := k).
  eapply Partition_spec2; auto. apply H.
  intro. rewrite <- H3 in H2. pose proof (Partition_spec2 _ _ _ H k H2).
  rewrite heap_clear_spec1 in H4. rewrite dom_spec in H2; auto.
  rewrite Partition_spec3 with (h1 := h1) (h2 := h2); auto.
  destruct (Z.eq_dec n k). rewrite e; auto.
  rewrite <- heap_clear_spec2 with (k := k); auto.
  symmetry. eapply Partition_spec3. apply H. auto. auto.
  split.
  apply heap_clear_not_dom_eq. intro.
  pose proof (Partition_dom_inv_left _ _ _ _ H H0).
  eapply heap_clear_dom1. apply H1.
  apply heap_clear_not_dom_eq. intro.
  pose proof (Partition_dom_inv_right _ _ _ _ H H0).
  eapply heap_clear_dom1. apply H1.
Qed.

Proposition heap_clear_substitution_lemma_p3 (h h': heap) (k0: Z):
  (forall k : Z, ~ (dom (heap_clear h k0) k /\ dom h' k)) ->
  forall k : Z, ~ (dom h k /\ dom (heap_clear h' k0) k).
intros. intro. destruct H0.
destruct (Z.eq_dec k k0).
rewrite e in H1.
eapply heap_clear_dom1. apply H1.
rewrite heap_clear_dom2 in H1; auto.
eapply H. split; [|apply H1].
rewrite heap_clear_dom2; auto.
Qed.

Proposition heap_clear_substitution_lemma_p4 (s: store) (y: V) (z: Z) (p: assert):
  ~In y (avar p) -> eq_restr (store_update s y z) s (avar p).
intro. intro. intro.
destruct (Nat.eq_dec x y).
exfalso. apply H. rewrite e in H0. auto.
rewrite store_update_lookup_diff; auto.
Qed.

Proposition heap_clear_substitution_lemma_p5 (x y: V) (s s': store) (z: Z) (h: heap):
  Some z = h (s x) -> s' = store_update s y z -> x <> y -> h = heap_update (heap_clear h (s x)) (s' x) (y s').
intros.
simpl. rewrite H0. clear dependent s'.
rewrite store_update_lookup_same.
rewrite store_update_lookup_diff; auto.
apply heap_ext; intro.
destruct (Z.eq_dec n (s x)).
rewrite e.
rewrite heap_update_spec1; auto.
rewrite heap_update_spec2; auto.
rewrite heap_clear_spec2; auto.
Qed.

Proposition heap_clear_substitution_lemma_p6 (x y: V) (s s': store) (z: Z) (h h' h'' hh: heap):
  Partition h'' (heap_clear h (s x)) h' ->
  Partition hh h (heap_clear h' (s x)) ->
  Some z = h' (s x) ->
  x <> y ->
  s' = store_update s y z ->
  h'' = heap_update hh (s' x) (y s').
intros. simpl. rewrite H3. clear dependent s'.
rewrite store_update_lookup_same.
rewrite store_update_lookup_diff; auto.
apply heap_ext; intro.
destruct (Z.eq_dec n (s x)).
rewrite e.
rewrite heap_update_spec1.
rewrite Partition_spec2 with (h1 := heap_clear h (s x)) (h2 := h'); auto.
rewrite dom_spec. intro. rewrite H3 in H1. inversion H1.
rewrite heap_update_spec2; auto.
destruct (dom_dec h n).
rewrite Partition_spec1 with (h1 := heap_clear h (s x)) (h2 := h'); auto.
rewrite heap_clear_spec2; auto.
symmetry. eapply Partition_spec1. apply H0. auto.
apply heap_clear_dom2; auto.
destruct (dom_dec h' n).
rewrite Partition_spec2 with (h1 := heap_clear h (s x)) (h2 := h'); auto.
symmetry. rewrite Partition_spec2 with (h1 := h) (h2 := heap_clear h' (s x)); auto.
rewrite heap_clear_spec2; auto.
apply heap_clear_dom2; auto.
rewrite Partition_spec3 with (h1 := heap_clear h (s x)) (h2 := h'); auto.
symmetry. rewrite Partition_spec3 with (h1 := h) (h2 := heap_clear h' (s x)); auto.
rewrite heap_clear_dom2; auto.
rewrite heap_clear_dom2; auto.
Qed.

Proposition heap_clear_substitution_lemma_p7 (h h' h'' hh: heap) (k: Z):
  Partition h'' (heap_clear h k) h' -> ~dom h' k ->
  Partition hh h h' -> h'' = heap_clear hh k.
intros. apply heap_ext; intro.
destruct (Z.eq_dec n k).
rewrite e. rewrite heap_clear_spec1.
eapply Partition_spec3. apply H.
apply heap_clear_dom1. assumption.
rewrite heap_clear_spec2; auto.
destruct (dom_dec h n).
rewrite Partition_spec1 with (h1 := heap_clear h k) (h2 := h'); auto.
rewrite heap_clear_spec2; auto.
symmetry. rewrite Partition_spec1 with (h1 := h) (h2 := h'); auto.
apply heap_clear_dom2; auto.
destruct (dom_dec h' n).
rewrite Partition_spec2 with (h1 := heap_clear h k) (h2 := h'); auto.
symmetry. rewrite Partition_spec2 with (h1 := h) (h2 := h'); auto.
rewrite Partition_spec3 with (h1 := heap_clear h k) (h2 := h'); auto.
symmetry. rewrite Partition_spec3 with (h1 := h) (h2 := h'); auto.
rewrite heap_clear_dom2; auto.
Qed.

Proposition heap_clear_substitution_lemma_p8 (h h' h'': heap) (k v: Z):
  Partition h'' h h' -> exists hh, Partition hh (heap_clear h k) (heap_update h' k v).
intros. apply Partition_intro. intros. intro.
destruct H0. destruct (Z.eq_dec k k0).
rewrite <- e in *.
apply heap_clear_dom1 in H0; auto.
apply heap_clear_dom2 in H0; auto.
apply heap_update_dom2 in H1; auto.
eapply Partition_spec4. apply H. split. apply H0. apply H1.
Qed.

Proposition heap_clear_substitution_lemma_p9 (h h' h'' hh: heap) (k v: Z):
  Partition h'' h h' -> Partition hh (heap_clear h k) (heap_update h' k v) ->
  hh = heap_update h'' k v.
intros. apply heap_ext; intro.
destruct (Z.eq_dec k n).
rewrite e. rewrite heap_update_spec1.
rewrite Partition_spec2 with (h1 := heap_clear h k) (h2 := heap_update h' k v); auto.
rewrite e. rewrite heap_update_spec1. auto.
rewrite e. apply heap_update_dom1.
rewrite heap_update_spec2; auto.
destruct (dom_dec h n).
rewrite Partition_spec1 with (h1 := heap_clear h k) (h2 := heap_update h' k v); auto.
rewrite heap_clear_spec2; auto.
symmetry. erewrite Partition_spec1. reflexivity. apply H. auto.
apply heap_clear_dom2; auto.
destruct (dom_dec h' n).
rewrite Partition_spec2 with (h1 := heap_clear h k) (h2 := heap_update h' k v); auto.
rewrite heap_update_spec2; auto.
symmetry. rewrite Partition_spec2 with (h1 := h) (h2 := h'); auto.
apply heap_update_dom2; auto.
rewrite Partition_spec3 with (h1 := heap_clear h k) (h2 := heap_update h' k v); auto.
symmetry. rewrite Partition_spec3 with (h1 := h) (h2 := h'); auto.
rewrite heap_clear_dom2; auto.
rewrite heap_update_dom2; auto.
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
- apply option_app_elim in H; destruct H; destruct H.
  fold asub_heap_clear in H; fold asub_heap_clear in H0.
  apply option_app_elim in H0; destruct H0; destruct H0.
  inversion H1. clear dependent ps.
  simpl; apply iff_split_and.
  apply IHp1; assumption.
  apply IHp2; assumption.
- apply option_app_elim in H; destruct H; destruct H.
  fold asub_heap_clear in H; fold asub_heap_clear in H0.
  apply option_app_elim in H0; destruct H0; destruct H0.
  inversion H1. clear dependent ps.
  simpl; apply iff_split_not_and_not.
  apply IHp1; assumption.
  apply IHp2; assumption.
- apply option_app_elim in H; destruct H; destruct H.
  fold asub_heap_clear in H; fold asub_heap_clear in H0.
  apply option_app_elim in H0; destruct H0; destruct H0.
  inversion H1. clear dependent ps.
  simpl; apply iff_split_imp.
  apply IHp1; assumption.
  apply IHp2; assumption.
- unfold asub_heap_clear in H; fold asub_heap_clear in H.
  destruct (Nat.eq_dec v x). inversion H.
  apply option_app_elim in H; destruct H; destruct H.
  inversion H0; clear dependent ps.
  simpl; apply iff_split_not_forall_not; intro.
  specialize IHp with h (store_update s v x1) x0.
  apply IHp in H. rewrite H.
  rewrite store_update_lookup_diff.
  apply iff_refl. assumption.
- unfold asub_heap_clear in H; fold asub_heap_clear in H.
  destruct (Nat.eq_dec v x). inversion H.
  apply option_app_elim in H; destruct H; destruct H.
  inversion H0; clear dependent ps.
  simpl; apply iff_split_forall; intro.
  specialize IHp with h (store_update s v x1) x0.
  apply IHp in H. rewrite H.
  rewrite store_update_lookup_diff.
  apply iff_refl. assumption.
- apply option_app_elim in H; destruct H; destruct H.
  fold asub_heap_clear in H; fold asub_heap_clear in H0.
  apply option_app_elim in H0; destruct H0; destruct H0.
  inversion H1. clear dependent ps.
  simpl. split; intro.
  + intro. apply H1. intros. intro.
    destruct H3; destruct H4.
    rewrite IHp1 in H4; try assumption.
    rewrite IHp2 in H5; try assumption.
    eapply H2. split.
    2: split; [apply H4 | apply H5].
    apply heap_clear_substitution_lemma_p1. assumption.
  + intro. apply H1; clear H1. intros. intro.
    destruct H1; destruct H3.
    pose proof (heap_clear_substitution_lemma_p2 _ _ _ _ H1).
    destruct H5; destruct H5; destruct H5; destruct H6.
    rewrite H6 in *; clear dependent h1.
    rewrite H7 in *; clear dependent h2.
    rewrite <- IHp1 in H3; [|apply H].
    rewrite <- IHp2 in H4; [|apply H0].
    eapply H2. split. apply H5. auto.
- apply option_app_elim in H; destruct H; destruct H.
  fold asub_heap_clear in H.
  apply option_app_elim in H0; destruct H0; destruct H0.
  apply option_app_elim in H1; destruct H1; destruct H1.
  inversion H2; clear dependent ps.
  remember (fresh (x :: aoccur p1 ++ aoccur p2)) as y.
  split; intro.
  + rewrite satisfy_land in H2; destruct H2.
    rewrite satisfy_simp; intros.
    remember (h' (s x)); destruct o.
    * remember (store_update s y z) as s'.
      rewrite acond with (t := s') in H5.
      pose proof (heap_update_substitution_lemma (heap_clear h' (s x)) s' p1 x y x1 H0).
      assert (h' = heap_update (heap_clear h' (s x)) (s' x) (y s')). {
        eapply heap_clear_substitution_lemma_p5. apply Heqo. apply Heqs'. intro. rewrite H7 in Heqy.
        pose proof (fresh_notIn (y :: aoccur p1 ++ aoccur p2)). rewrite <- Heqy in H8.
        apply H8. left. auto. }
      rewrite <- H7 in H6. apply H6 in H5.
      simpl in H3.
      pose proof (Partition_intro h (heap_clear h' (s x))); destruct H8.
      pose proof (Partition_spec4 h'' (heap_clear h (s x)) h' H4).
      apply heap_clear_substitution_lemma_p3. assumption.
      specialize H3 with z x3 (heap_clear h' (s x)).
      rewrite <- Heqs' in H3.
      pose proof (H3 H8 H5).
      pose proof (heap_update_substitution_lemma x3 s' p2 x y x2 H1).
      apply H10 in H9.
      rewrite acond with (t := s) in H9.
      assert (h'' = heap_update x3 (s' x) (y s')). {
        eapply heap_clear_substitution_lemma_p6. apply H4.
        apply H8. apply Heqo. intro. rewrite H11 in Heqy.
        pose proof (fresh_notIn (y :: aoccur p1 ++ aoccur p2)). rewrite <- Heqy in H12.
        apply H12. left. auto. apply Heqs'. }
      rewrite H11. assumption.
      rewrite Heqs'.
      apply heap_clear_substitution_lemma_p4.
      rewrite Heqy.
      apply fresh_notInGeneral. intros.
      right. apply in_or_app. right. unfold aoccur. apply in_or_app; auto.
      rewrite Heqs'.
      apply eq_restr_comm.
      apply heap_clear_substitution_lemma_p4.
      rewrite Heqy.
      apply fresh_notInGeneral. intros.
      right. apply in_or_app. left. unfold aoccur. apply in_or_app; auto.
    * rewrite satisfy_simp in H2.
      pose proof (Partition_intro h h'). destruct H6. {
        intro. destruct (Z.eq_dec k (s x)). intro. destruct H6.
        apply dom_spec in H7. apply H7. rewrite e. symmetry; assumption.
        pose proof (Partition_spec4 _ _ _ H4 k).
        intro. destruct H7. apply H6. split.
        apply heap_clear_dom2. intro. apply n. symmetry. assumption. assumption. assumption. }
      specialize H2 with h' x3.
      pose proof (H2 H6).
      assert (satisfy h' s (land p1 (lnot (hasvaldash x)))).
      rewrite satisfy_land. split. assumption.
      rewrite satisfy_lnot.
      rewrite satisfy_hasvaldash.
      rewrite dom_spec. intro. apply H8. symmetry. assumption.
      apply H7 in H8; clear H7.
      rewrite IHp2 in H8; try assumption.
      assert (h'' = heap_clear x3 (s x)). {
        eapply heap_clear_substitution_lemma_p7. apply H4.
        rewrite dom_spec; intro. apply H7. symmetry; assumption. assumption. }
      rewrite H7. assumption.
  + rewrite satisfy_land. split.
    * rewrite satisfy_simp. intros.
      rewrite satisfy_land in H4; destruct H4.
      rewrite satisfy_lnot in H5; rewrite satisfy_hasvaldash in H5.
      pose proof (Partition_intro (heap_clear h (s x)) h'). destruct H6. {
      intro. intro. destruct H6. destruct (Z.eq_dec (s x) k). apply H5. simpl.
      rewrite e. assumption. rewrite heap_clear_dom2 in H6.
      eapply Partition_spec4. apply H3. split. apply H6. apply H7. assumption. }
      rewrite satisfy_simp in H2.
      assert (satisfy x3 s p2). eapply H2. apply H6. assumption.
      apply <- IHp2; try assumption.
      pose proof (heap_clear_substitution_lemma_p7 _ _ _ _ _ H6 H5 H3).
      rewrite <- H8. assumption.
    * assert (y <> x) as G. {
        intro. rewrite H3 in Heqy. pose proof fresh_notIn (x :: aoccur p1 ++ aoccur p2).
        apply H4. rewrite <- Heqy. left. auto. }
      rewrite satisfy_lforall. intros.
      rewrite satisfy_simp. intros.
      pose proof (heap_update_substitution_lemma h' (store_update s y v) p1 x y x1 H0).
      apply H5 in H4. clear H5.
      rewrite acond with (t := s) in H4. simpl in H4. rewrite store_update_lookup_same in H4.
      rewrite store_update_lookup_diff in H4; try assumption. rewrite satisfy_simp in H2.
      pose proof (heap_clear_substitution_lemma_p8 h h' h'' (s x) v H3). destruct H5.
      pose proof (H2 _ _ H5 H4).
      rewrite acond with (t := store_update s y v) in H6.
      assert (x3 = heap_update h'' (s x) v). {
        eapply heap_clear_substitution_lemma_p9. apply H3. assumption. }
      rewrite H7 in H6.
      pose proof (heap_update_substitution_lemma h'' (store_update s y v) p2 x y x2 H1).
      simpl in H8. rewrite store_update_lookup_same in H8.
      rewrite store_update_lookup_diff in H8; try assumption.
      rewrite <- H8 in H6. assumption.
      apply eq_restr_comm.
      apply heap_clear_substitution_lemma_p4.
      rewrite Heqy. apply fresh_notInGeneral. intros. right.
      apply in_or_app. right. apply in_or_app. auto.
      apply heap_clear_substitution_lemma_p4.
      rewrite Heqy. apply fresh_notInGeneral. intros. right.
      apply in_or_app. left. apply in_or_app. auto.
Qed.

Proposition soundness_conseq (p pp q qq: assert) (x: program):
  validity (limp pp p) -> validity (limp q qq) -> strong_partial_correct (mkhoare p x q) ->
  strong_partial_correct (mkhoare pp x qq).
intros.
intro. intros.
unfold strong_partial_correct in H1.
specialize H1 with h s.
unfold validity in *.
specialize H with h s.
rewrite satisfy_limp in H.
split.
- destruct H1. apply H; assumption. assumption.
- intros.
  specialize H0 with h' s'.
  rewrite satisfy_limp in H0.
  destruct H1. apply H; assumption.
  apply H0. apply H4. assumption.
Qed.

(* ============================================ *)
(* Weakest precondition axiomatization (WP-CSL) *)
(* ============================================ *)

Corollary WPCSL_soundness_basic (p: assert) (x: V) (e: expr):
  forall ps, asub p x e = Some ps ->
    strong_partial_correct (mkhoare ps (basic x e) p).
intros. intro. intros. split.
intro. inversion H1. intros. inversion H1. rewrite <- H7.
rewrite <- store_substitution_lemma. apply H0. assumption.
Qed.

Corollary WPCSL_soundness_lookup (p: assert) (x y: V) (e: expr):
  ~ In y (x :: aoccur p ++ evar e) ->
    forall ps, asub p x y = Some ps ->
      strong_partial_correct (mkhoare (lexists y (land (hasval e y) ps)) (lookup x e) p).
intros. intro. intros.
split.
- intro. inversion H2.
  rewrite satisfy_lexists in H1.
  apply H1. intros. intro.
  rewrite satisfy_land in H8; destruct H8.
  rewrite satisfy_hasval in H8.
  simpl in H8. rewrite store_update_lookup_same in H8.
  rewrite econd with (t := s) in H8. rewrite H8 in H4. inversion H4.
  intro. intro. destruct (Nat.eq_dec x1 y).
  exfalso. rewrite e1 in H10. apply H. right. apply in_or_app. auto.
  rewrite store_update_lookup_diff; auto.
- intros. inversion H2. rewrite <- H8.
  rewrite satisfy_lexists in H1.
  apply satisfy_stable. intro.
  apply H1; clear H1. intros. intro. apply H10; clear H10.
  rewrite satisfy_land in H1; destruct H1.
  rewrite store_substitution_lemma in H10; [|apply H0].
  simpl in H10. rewrite store_update_lookup_same in H10.
  rewrite satisfy_hasval in H1. simpl in H1.
  rewrite store_update_lookup_same in H1.
  rewrite <- H8 in H4.
  assert (e s = e (store_update s y v0)). {
    apply econd. intro. intro. destruct (Nat.eq_dec x1 y). rewrite e1.
    exfalso. rewrite e1 in H11. apply H. right. apply in_or_app. auto.
    rewrite store_update_lookup_diff; auto. }
  rewrite <- H11 in H1.
  rewrite H1 in H4. inversion H4. rewrite H13 in H10.
  assert (x <> y). {
    intro. rewrite H12 in H. apply H. left. reflexivity. }
  rewrite store_update_swap in H10; auto.
  rewrite acond. apply H10.
  intro. intro.
  destruct (Nat.eq_dec x x1). rewrite e1.
  rewrite store_update_lookup_same.
  rewrite store_update_lookup_diff.
  rewrite store_update_lookup_same; auto.
  intro. apply H12. rewrite e1. rewrite H15. reflexivity.
  rewrite store_update_lookup_diff; auto.
  rewrite store_update_lookup_diff.
  rewrite store_update_lookup_diff; auto.
  intro. rewrite <- H15 in H14. apply H. right.
  apply in_or_app. left. apply in_or_app. auto.
Qed.

Corollary WPCSL_soundness_mutation (p: assert) (x: V) (e: expr):
  forall ps, asub_heap_update p x e = Some ps ->
    strong_partial_correct (mkhoare (land (hasvaldash x) ps) (mutation x e) p).
intros. intro. intros.
rewrite satisfy_land in H0; destruct H0.
rewrite satisfy_hasvaldash in H0.
split.
- intro.
  inversion H2. apply H4. assumption.
- intros. inversion H2.
  rewrite <- H9.
  rewrite <- heap_update_substitution_lemma.
  apply H1. assumption.
Qed.

Corollary WPCSL_soundness_new (p: assert) (x: V) (e: expr):
  ~ In x (evar e) ->
  forall ps, asub_heap_update p x e = Some ps ->
    strong_partial_correct (mkhoare (lforall x (limp (lnot (hasvaldash x)) ps)) (new x e) p).
intros. intro. intros.
rewrite satisfy_lforall in H1.
split.
- intro. inversion H2.
- intros. inversion H2.
  specialize H1 with n.
  rewrite satisfy_limp in H1.
  assert (e s = e (store_update s x n)). {
    apply econd. intro. intros. destruct (Nat.eq_dec x1 x).
    rewrite e1 in H10. exfalso. apply H. auto.
    rewrite store_update_lookup_diff; auto. }
  rewrite H10.
  assert (n = store_update s x n x). {
    rewrite store_update_lookup_same. reflexivity. }
  rewrite H11 at 1.
  rewrite <- heap_update_substitution_lemma.
  apply H1.
  rewrite satisfy_lnot.
  rewrite satisfy_hasvaldash. simpl. rewrite <- H11. assumption.
  assumption.
Qed.

Corollary WPCSL_soundness_dispose (p: assert) (x: V):
  forall ps, asub_heap_clear p x = Some ps ->
    strong_partial_correct (mkhoare (land (hasvaldash x) ps) (dispose x) p).
intros. intro. intros.
rewrite satisfy_land in H0; destruct H0.
rewrite satisfy_hasvaldash in H0.
split.
- intro. inversion H2. apply H5. assumption.
- intros. inversion H2.
  rewrite <- H8.
  rewrite <- heap_clear_substitution_lemma. apply H1.
  assumption.
Qed.

Theorem WPCSL_soundness (Gamma: assert -> Prop) (O: forall p, Gamma p -> validity p):
  forall pSq, WPCSL Gamma pSq -> strong_partial_correct pSq.
intros. induction H.
- apply WPCSL_soundness_basic; assumption.
- apply WPCSL_soundness_lookup; assumption.
- apply WPCSL_soundness_mutation; assumption.
- apply WPCSL_soundness_new; assumption.
- apply WPCSL_soundness_dispose; assumption.
- apply O in H. apply O in H1.
  eapply soundness_conseq.
  apply H. apply H1. assumption.
Qed.

Corollary WPCSL_weakest_basic (q p: assert) (x: V) (e: expr):
  strong_partial_correct (mkhoare p (basic x e) q) ->
  forall qs, asub q x e = Some qs ->
  validity (limp p qs).
intros. intro. intros.
rewrite satisfy_limp. intro.
unfold strong_partial_correct in H.
specialize H with h s.
apply H in H1; clear H. destruct H1.
specialize H1 with h (store_update s x (e s)).
pose proof (H1 (step_basic x e h s)); clear H1.
rewrite store_substitution_lemma. apply H2. assumption.
Qed.

Corollary WPCSL_weakest_lookup (q p: assert) (x: V) (e: expr):
  strong_partial_correct (mkhoare p (lookup x e) q) ->
  forall y, ~In y (x :: aoccur q ++ evar e) ->
  forall qs, asub q x y = Some qs ->
  validity (limp p (lexists y (land (hasval e y) qs))).
intros. intro. intros.
rewrite satisfy_limp; intro.
unfold strong_partial_correct in H; specialize H with h s.
apply H in H2; clear H; destruct H2.
remember (h (e s)). destruct o.
apply satisfy_lexists_intro with (n := z).
rewrite satisfy_land. split.
rewrite satisfy_hasval.
assert (e s = e (store_update s y z)). {
  apply econd. intro. intro. destruct (Nat.eq_dec x0 y).
  rewrite e0 in H3. exfalso. apply H0. right. apply in_or_app. auto.
  rewrite store_update_lookup_diff; auto. }
rewrite <- H3. simpl. rewrite store_update_lookup_same. auto.
specialize H2 with h (store_update s x z).
symmetry in Heqo.
pose proof (H2 (step_lookup x e h s z Heqo)); clear H2.
pose proof (store_substitution_lemma h (store_update s y z) q x y qs H1).
rewrite H2. simpl. rewrite store_update_lookup_same.
rewrite store_update_swap.
rewrite acond. apply H3.
intro. intro. destruct (Nat.eq_dec x0 y).
rewrite e0 in H4. exfalso. apply H0. right. apply in_or_app. left. apply in_or_app; auto.
rewrite store_update_lookup_diff; auto.
intro. rewrite H4 in H0. apply H0. left; auto.
exfalso. apply H. apply step_lookup_fail. auto.
Qed.

Corollary WPCSL_weakest_mutation (q p: assert) (x: V) (e: expr):
  strong_partial_correct (mkhoare p (mutation x e) q) ->
  forall qs, asub_heap_update q x e = Some qs ->
  validity (limp p (land (hasvaldash x) qs)).
intros. intro. intros.
rewrite satisfy_limp; intro.
unfold strong_partial_correct in H.
specialize H with h s.
apply H in H1; clear H. destruct H1.
assert (dom h (s x)).
destruct (dom_dec h (s x)); auto.
exfalso. apply H. apply step_mutation_fail; auto.
rewrite satisfy_land; split.
rewrite satisfy_hasvaldash; auto.
rewrite heap_update_substitution_lemma; [|apply H0].
apply H1. apply step_mutation; auto.
Qed.

Corollary WPCSL_weakest_allocation (q p: assert) (x: V) (e: expr):
  strong_partial_correct (mkhoare p (new x e) q) ->
  ~ In x (evar e) ->
  forall qs, asub_heap_update q x e = Some qs ->
  validity (limp p (lforall x (limp (lnot (hasvaldash x)) qs))).
intros. intro. intros.
rewrite satisfy_limp; intro.
rewrite satisfy_lforall; intro.
rewrite satisfy_limp; intro.
rewrite satisfy_lnot_hasvaldash in H3.
rewrite store_update_lookup_same in H3.
unfold strong_partial_correct in H.
specialize H with h s.
apply H in H2; clear H; destruct H2.
specialize H2 with (heap_update h v (e s)) (store_update s x v).
pose proof (H2 (step_new _ _ _ _ _ H3)); clear H2.
rewrite heap_update_substitution_lemma; [|apply H1].
rewrite store_update_lookup_same.
assert (e s = e (store_update s x v)).
apply econd. intro. intro. destruct (Nat.eq_dec x0 x).
exfalso. apply H0. rewrite e0 in H2. auto.
rewrite store_update_lookup_diff; auto.
rewrite <- H2. assumption.
Qed.

Corollary WPCSL_weakest_dispose (q p: assert) (x: V):
  strong_partial_correct (mkhoare p (dispose x) q) ->
  forall qs, asub_heap_clear q x = Some qs ->
  validity (limp p (land (hasvaldash x) qs)).
intros. intro. intros.
rewrite satisfy_limp; intro.
rewrite satisfy_land.
unfold strong_partial_correct in H.
specialize H with h s.
apply H in H1; clear H; destruct H1.
assert (dom h (s x)).
destruct (dom_dec h (s x)); auto.
exfalso. apply H. apply step_dispose_fail; auto.
split.
rewrite satisfy_hasvaldash; auto.
rewrite heap_clear_substitution_lemma; [|apply H0].
apply H1. apply step_dispose; auto.
Qed.

Theorem WPCSL_completeness (Gamma: assert -> Prop) (O: forall p, validity p -> Gamma p):
  forall pSq, restrict_post pSq -> strong_partial_correct pSq -> WPCSL Gamma pSq.
intros. destruct pSq as (p, S, q); destruct S; destruct a; unfold restrict_post in H.
- rewrite asub_defined with (x := v) in H.
  destruct H.
  apply wpc_conseq with (p := x) (q := q).
  apply O. eapply WPCSL_weakest_basic. apply H0. auto.
  apply wpc_basic; auto.
  apply O. intro. intro. rewrite satisfy_limp. tauto.
- remember (fresh (v :: aoccur q ++ evar e)) as y.
  pose proof (asub_defined q v y).
  assert (forall x : V, In x (evar y) -> ~ In x (abound q)).
  intros. simpl in H2. destruct H2. rewrite <- H2. rewrite Heqy.
  apply fresh_notInGeneral. intros. right. apply in_or_app. left. apply in_or_app. auto. inversion H2.
  apply H1 in H2; clear H1; destruct H2.
  apply wpc_conseq with (p := (lexists y (land (hasval e y) x))) (q := q).
  apply O. eapply WPCSL_weakest_lookup. apply H0.
  rewrite Heqy. apply fresh_notIn. auto.
  apply wpc_lookup; auto.
  rewrite Heqy. apply fresh_notIn.
  apply O. intro. intro. rewrite satisfy_limp. tauto.
- rewrite asub_heap_update_defined in H. destruct H.
  apply wpc_conseq with (p := land (hasvaldash v) x) (q := q).
  apply O. eapply WPCSL_weakest_mutation. apply H0. auto.
  apply wpc_mutation. auto.
  apply O. intro. intro. rewrite satisfy_limp. tauto.
- destruct H. rewrite asub_heap_update_defined in H1. destruct H1.
  apply wpc_conseq with (p := lforall v (limp (lnot (hasvaldash v)) x)) (q := q).
  apply O. eapply WPCSL_weakest_allocation. apply H0. auto. auto.
  apply wpc_new. auto. auto.
  apply O. intro. intro. rewrite satisfy_limp. tauto.
- rewrite asub_heap_clear_defined in H. destruct H.
  apply wpc_conseq with (p := land (hasvaldash v) x) (q := q).
  apply O. eapply WPCSL_weakest_dispose. apply H0. auto.
  apply wpc_dispose. auto.
  apply O. intro. intro. rewrite satisfy_limp. tauto.
Qed.

Corollary WPCSL_soundness_completeness:
  forall pSq, restrict_post pSq -> WPCSL validity pSq <-> strong_partial_correct pSq.
intros. split.
apply WPCSL_soundness; auto.
apply WPCSL_completeness; auto.
Qed.

(* =============================================== *)
(* Strongest postcondition axiomatization (SP-CSL) *)
(* =============================================== *)

Corollary SPCSL_soundness_basic (p: assert) (x y: V) (e: expr):
  ~ In y (x :: aoccur p ++ evar e) ->
  forall ps, asub p x y = Some ps ->
  strong_partial_correct (mkhoare p (basic x e) (lexists y (land ps (equals (esub e x y) x)))).
intros. intro. intros.
split. intro. inversion H2.
intros. inversion H2. rewrite <- H8.
apply satisfy_lexists_intro with (n := s x).
rewrite satisfy_land. split.
- assert (satisfy h (store_update (store_update s y (s x)) x (y (store_update s y (s x)))) p). {
    simpl.
    rewrite store_update_lookup_same.
    rewrite store_update_swap.
    rewrite store_update_id.
    rewrite acond. apply H1.
    intro. intro. destruct (Nat.eq_dec x1 y).
    exfalso. apply H. rewrite e1 in H3. right. apply in_or_app. left. apply in_or_app. auto.
    rewrite store_update_lookup_diff; auto.
    intro. apply H. rewrite H3. left; auto. }
  rewrite <- store_substitution_lemma in H3; [| apply H0].
  rewrite store_update_swap.
  rewrite acond. apply H3.
  intro. intro.
  destruct (Nat.eq_dec x x1).
  exfalso. eapply (asub_notInVar p x y).
    simpl. intro. destruct H11; auto. apply H. left. auto. apply H0.
    rewrite e1. assumption.
  rewrite store_update_lookup_diff; auto.
  intro. apply H. left; auto.
- rewrite satisfy_equals.
  simpl.
  assert (x <> y). intro. apply H. left; auto.
  rewrite store_update_lookup_same.
  rewrite store_update_lookup_diff; auto.
  rewrite store_update_lookup_same.
  rewrite store_update_swap; auto.
  rewrite store_update_collapse.
  rewrite store_update_id.
  apply econd. intro. intro.
  destruct (Nat.eq_dec x1 y).
  exfalso. apply H. right. apply in_or_app. right. rewrite e1 in H10. auto.
  rewrite store_update_lookup_diff; auto.
Qed.

Corollary SPCSL_soundness_lookup (p: assert) (x y: V) (e: expr):
  ~ In y (x :: aoccur p ++ evar e) ->
  forall ps, asub p x y = Some ps ->
  strong_partial_correct (mkhoare (land p (hasvaldash e)) (lookup x e) (lexists y (land ps (hasval (esub e x y) x)))).
intros. intro. intros.
rewrite satisfy_land in H1; destruct H1.
rewrite satisfy_hasvaldash in H2.
split. intro. inversion H3. apply dom_spec in H2. apply H2; auto.
intros. inversion H3. rewrite <- H9. clear dependent s'.
apply satisfy_lexists_intro with (n := s x).
assert (x <> y). intro. apply H. left; auto.
rewrite satisfy_land; split.
- rewrite store_update_swap; auto.
  pose proof (store_substitution_lemma h (store_update s y (s x)) p x y ps H0).
  simpl in H10.
  rewrite store_update_lookup_same in H10.
  rewrite store_update_swap in H10; auto.
  rewrite store_update_id in H10.
  rewrite acond with (t := (store_update s y (s x))).
  rewrite H10.
  rewrite acond with (t := s). auto.
  intro. intro. destruct (Nat.eq_dec x1 y).
  exfalso. apply H. right. apply in_or_app. left. apply in_or_app. rewrite e1 in H11; auto.
  rewrite store_update_lookup_diff; auto.
  intro. intro. destruct (Nat.eq_dec x1 x).
  exfalso. rewrite e1 in H11. eapply asub_notInVar; [|apply H0|apply H11].
  simpl. intro. destruct H12; auto.
  rewrite store_update_lookup_diff; auto.
- rewrite satisfy_hasval. simpl.
  rewrite store_update_lookup_same.
  rewrite store_update_lookup_diff; auto.
  rewrite store_update_lookup_same.
  rewrite store_update_swap.
  rewrite store_update_collapse.
  rewrite store_update_id.
  assert (e s = e (store_update s y (s x))).
  apply econd. intro. intro. destruct (Nat.eq_dec x1 y).
  exfalso. rewrite e1 in H10. apply H. right. apply in_or_app; auto.
  rewrite store_update_lookup_diff; auto.
  rewrite <- H10. rewrite H9. auto. auto.
Qed.

Corollary SPCSL_soundness_mutation (p: assert) (x y: V) (e: expr):
  ~ In y (x :: aoccur p ++ evar e) ->
  forall ps, asub_heap_update p x y = Some ps ->
  strong_partial_correct (mkhoare (land p (hasvaldash x)) (mutation x e) (land (lexists y ps) (hasval x e))).
intros. intro. intros.
rewrite satisfy_land in H1; destruct H1.
rewrite satisfy_hasvaldash in H2.
split. intro. inversion H3. apply H5; auto.
intros. inversion H3. rewrite <- H10 in *.
clear dependent s'. clear dependent h'.
clear dependent x0. clear dependent e0.
clear dependent h0. clear dependent s0.
clear H2.
rewrite satisfy_land. split.
- remember (h (s x)). destruct o.
  apply satisfy_lexists_intro with (n := z).
  pose proof (heap_update_substitution_lemma (heap_update h (s x) (e s)) (store_update s y z)
      p x y ps H0).
  rewrite H2; clear H2.
  rewrite store_update_lookup_diff. simpl.
  rewrite store_update_lookup_same.
  rewrite heap_update_collapse.
  rewrite heap_update_id; auto.
  rewrite acond. apply H1.
  intro. intro. destruct (Nat.eq_dec x0 y).
  exfalso. rewrite e0 in H2. apply H. right. apply in_or_app. left. apply in_or_app. auto.
  rewrite store_update_lookup_diff; auto.
  intro. apply H. left. auto.
  exfalso. apply dom_spec in H5. apply H5; auto.
- rewrite satisfy_hasval.
  rewrite heap_update_spec1. reflexivity.
Qed.

Corollary SPCSL_soundness_new (p: assert) (x y: V) (e: expr):
  ~ In x (evar e) ->
  ~ In y (x :: aoccur p ++ evar e) ->
  forall ps, asub p x y = Some ps ->
  forall pss, asub_heap_clear (lexists y ps) x = Some pss ->
  strong_partial_correct (mkhoare p (new x e) (land pss (hasval x e))).
intros. intro. intros.
split. intro. inversion H4.
intros. inversion H4.
clear dependent s'. clear dependent h'.
clear dependent x0. clear dependent e0.
clear dependent h0. clear dependent s0.
rewrite satisfy_land. apply and_comm. split.
rewrite satisfy_hasval. simpl.
rewrite store_update_lookup_same.
rewrite heap_update_spec1.
assert (e s = e (store_update s x n)).
apply econd. intro. intro. destruct (Nat.eq_dec x x0).
exfalso. rewrite e0 in H. apply H; auto.
rewrite store_update_lookup_diff; auto.
rewrite H4. reflexivity.
simpl in H2. destruct (Nat.eq_dec y x). inversion H2.
apply option_app_elim in H2; destruct H2; destruct H2.
inversion H4. clear dependent pss.
apply satisfy_lexists_intro with (n := s x).
rewrite heap_clear_substitution_lemma; [| apply H2].
assert (x <> y). intro. apply H0. left; auto.
rewrite store_update_lookup_diff; auto.
rewrite store_update_lookup_same.
rewrite heap_update_clear_collapse; auto.
rewrite store_update_swap; auto.
rewrite acond with (t := store_update s y (s x)).
rewrite store_substitution_lemma; [|apply H1].
simpl.
rewrite store_update_lookup_same.
rewrite store_update_swap; auto.
rewrite store_update_id.
rewrite acond. apply H3.
intro. intro. destruct (Nat.eq_dec x1 y).
rewrite e0 in H5. exfalso. apply H0. right.
apply in_or_app. left. apply in_or_app. auto.
rewrite store_update_lookup_diff; auto.
intro. intro. destruct (Nat.eq_dec x1 x).
rewrite e0 in H5.
exfalso. eapply asub_notInVar; [| apply H1|apply H5].
simpl. intro. destruct H7; auto.
rewrite store_update_lookup_diff; auto.
Qed.

Corollary SPCSL_soundness_dispose (p: assert) (x y: V):
  ~ In y (x :: aoccur p) ->
  forall ps, asub_heap_update p x y = Some ps ->
  strong_partial_correct (mkhoare (land p (hasvaldash x)) (dispose x) (land (lexists y ps) (lnot (hasvaldash x)))).
intros. intro. intros.
rewrite satisfy_land in H1; destruct H1.
rewrite satisfy_hasvaldash in H2; simpl in H2.
split. intro. inversion H3; auto.
intros. inversion H3. rewrite <- H9.
clear dependent s'. clear dependent h'.
clear dependent x0. clear dependent h0. clear dependent s0.
rewrite satisfy_land. rewrite and_comm. split.
rewrite satisfy_lnot_hasvaldash.
apply heap_clear_dom1.
remember (h (s x)); destruct o.
apply satisfy_lexists_intro with (n := z).
rewrite heap_update_substitution_lemma; [|apply H0].
assert (x <> y). intro. apply H. left; auto.
simpl.
rewrite store_update_lookup_same.
rewrite store_update_lookup_diff; auto.
rewrite heap_clear_update_collapse; auto.
rewrite acond. apply H1.
intro. intro. destruct (Nat.eq_dec y x0).
rewrite <- e in H4. exfalso. apply H. right. apply in_or_app. auto.
rewrite store_update_lookup_diff; auto.
rewrite dom_spec in H2. exfalso. auto.
Qed.

Theorem SPCSL_soundness (Gamma: assert -> Prop) (O: forall p, Gamma p -> validity p):
  forall pSq, SPCSL Gamma pSq -> strong_partial_correct pSq.
intros. induction H.
- apply SPCSL_soundness_basic; assumption.
- apply SPCSL_soundness_lookup; assumption.
- apply SPCSL_soundness_mutation; assumption.
- eapply SPCSL_soundness_new. apply H. apply H0. apply H1. assumption.
- apply SPCSL_soundness_dispose; assumption.
- apply O in H. apply O in H1.
  eapply soundness_conseq.
  apply H. apply H1. assumption.
Qed.

Corollary SPCSL_strongest_basic (p q: assert) (x y: V) (e: expr):
  strong_partial_correct (mkhoare p (basic x e) q) ->
  ~ In y (x :: aoccur p ++ evar e ++ aoccur q) ->
  forall ps, asub p x y = Some ps ->
  validity (limp (lexists y (land ps (equals (esub e x y) x))) q).
intros. intro. intros.
rewrite satisfy_limp. intro.
eapply satisfy_lexists_elim. apply H2. clear H2; intros.
rewrite satisfy_land in H2; destruct H2.
rewrite satisfy_equals in H3; simpl in H3.
rewrite store_update_lookup_same in H3.
assert (x <> y). intro. apply H0. left. auto.
rewrite store_update_lookup_diff in H3; auto.
pose proof (store_substitution_lemma h (store_update s y n) p x y ps H1).
apply H5 in H2; clear H5. simpl in H2.
rewrite store_update_lookup_same in H2.
unfold strong_partial_correct in H.
apply H in H2; clear H. destruct H2.
pose proof (step_basic x e h (store_update (store_update s y n) x n)).
apply H2 in H5. rewrite H3 in H5.
rewrite store_update_collapse in H5.
assert (s x = (store_update s y n) x).
rewrite store_update_lookup_diff; auto.
rewrite H6 in H5.
rewrite store_update_id in H5.
rewrite acond. apply H5.
intro. intro. destruct (Nat.eq_dec x0 y).
exfalso. rewrite e0 in H7. apply H0. right.
apply in_or_app. right. apply in_or_app. right. apply in_or_app; auto.
rewrite store_update_lookup_diff; auto.
Qed.

Corollary SPCSL_strongest_lookup (p q: assert) (x y: V) (e: expr):
  strong_partial_correct (mkhoare p (lookup x e) q) ->
  ~ In y (x :: aoccur p ++ evar e ++ aoccur q) ->
  forall ps, asub p x y = Some ps ->
  validity (limp (lexists y (land ps (hasval (esub e x y) x))) q).
intros. intro. intros.
rewrite satisfy_limp; intro.
eapply satisfy_lexists_elim. apply H2. clear H2; intros.
rewrite satisfy_land in H2; destruct H2.
rewrite satisfy_hasval in H3.
pose proof (store_substitution_lemma h (store_update s y n) p x y ps H1).
apply H4 in H2; clear H4. simpl in H2.
rewrite store_update_lookup_same in H2.
simpl in H3. rewrite store_update_lookup_same in H3.
assert (x <> y). intro. apply H0. left; auto.
rewrite store_update_lookup_diff in H3; auto.
unfold strong_partial_correct in H.
apply H in H2; clear H. destruct H2.
pose proof (step_lookup x e h _ _ H3).
apply H2 in H5; clear H2.
rewrite store_update_collapse in H5.
rewrite store_update_swap in H5; auto.
rewrite store_update_id in H5.
rewrite acond. apply H5.
intro. intro. destruct (Nat.eq_dec x0 y).
exfalso. apply H0. rewrite <- e0. right.
apply in_or_app. right. apply in_or_app. right. apply in_or_app; auto.
rewrite store_update_lookup_diff; auto.
Qed.

Corollary SPCSL_strongest_mutation (p q: assert) (x y: V) (e: expr):
  strong_partial_correct (mkhoare p (mutation x e) q) ->
  ~In y (x :: aoccur p ++ evar e ++ aoccur q) ->
  forall ps, asub_heap_update p x y = Some ps ->
  validity (limp (land (lexists y ps) (hasval x e)) q).
intros. intro. intros.
rewrite satisfy_limp; intro.
rewrite satisfy_land in H2; destruct H2.
rewrite satisfy_hasval in H3.
eapply satisfy_lexists_elim. apply H2. intros; clear H2.
rewrite heap_update_substitution_lemma in H4; [|apply H1].
assert (x <> y). intro. apply H0. left; auto.
rewrite store_update_lookup_diff in H4; auto. simpl in H4.
rewrite store_update_lookup_same in H4.
unfold strong_partial_correct in H.
apply H in H4; clear H; destruct H4.
pose proof (step_mutation x e (heap_update h (s x) n) (store_update s y n)).
assert (dom (heap_update h (s x) n) (store_update s y n x)).
rewrite store_update_lookup_diff; auto.
apply heap_update_dom1. apply H5 in H6; clear H5.
apply H4 in H6; clear H4.
rewrite store_update_lookup_diff in H6; auto.
assert (e s = e (store_update s y n)).
apply econd. intro. intro. destruct (Nat.eq_dec x0 y).
rewrite e0 in H4. exfalso. apply H0. right. apply in_or_app. right. apply in_or_app; auto.
rewrite store_update_lookup_diff; auto.
rewrite <- H4 in H6.
rewrite heap_update_collapse in H6.
rewrite heap_update_id in H6; auto.
rewrite acond.
apply H6.
intro. intro. destruct (Nat.eq_dec x0 y).
rewrite e0 in H5. exfalso. apply H0. right. apply in_or_app. right.
apply in_or_app. right. apply in_or_app; auto.
rewrite store_update_lookup_diff; auto.
Qed.

Corollary SPCSL_strongest_new (p q: assert) (x y: V) (e: expr):
  ~ In x (evar e) ->
  strong_partial_correct (mkhoare p (new x e) q) ->
  ~ In y (x :: aoccur p ++ evar e ++ aoccur q) ->
  forall ps, asub p x y = Some ps ->
  forall pss, asub_heap_clear (lexists y ps) x = Some pss ->
  validity (limp (land pss (hasval x e)) q).
intros. intro. intros.
rewrite satisfy_limp; intro.
rewrite satisfy_land in H4; destruct H4.
rewrite satisfy_hasval in H5.
rewrite heap_clear_substitution_lemma in H4; [|apply H3].
eapply satisfy_lexists_elim. apply H4. clear H4; intros.
rewrite store_substitution_lemma in H4; [|apply H2].
simpl in H4. rewrite store_update_lookup_same in H4.
unfold strong_partial_correct in H0. apply H0 in H4; clear H0.
destruct H4.
pose proof (heap_clear_update_collapse h (s x) (e s) H5).
pose proof (step_new x e (heap_clear h (s x)) (store_update (store_update s y n) x n) (s x)).
assert (~ dom (heap_clear h (s x)) (s x)).
  apply heap_clear_dom1. apply H7 in H8; clear H7.
apply H4 in H8; clear H4.
rewrite heap_clear_update_collapse in H8.
rewrite store_update_collapse in H8.
rewrite store_update_swap in H8.
rewrite store_update_id in H8.
rewrite acond. apply H8.
intro. intro. destruct (Nat.eq_dec x0 y).
rewrite e0 in H4. exfalso. apply H1. right. apply in_or_app.
right. apply in_or_app. right. apply in_or_app; auto.
rewrite store_update_lookup_diff; auto.
intro. apply H1. left; auto.
simpl in H5. rewrite H5.
rewrite econd with (t := (store_update (store_update s y n) x n)).
reflexivity. intro. intro.
destruct (Nat.eq_dec x0 x).
exfalso. rewrite e0 in H4. apply H; auto.
rewrite store_update_lookup_diff; auto.
destruct (Nat.eq_dec x0 y).
exfalso. rewrite e0 in H4. apply H1. right. apply in_or_app. right. apply in_or_app; auto.
rewrite store_update_lookup_diff; auto.
Qed.

Corollary SPCSL_strongest_dispose (p q: assert) (x y: V):
  strong_partial_correct (mkhoare p (dispose x) q) ->
  ~ In y (x :: aoccur p ++ aoccur q) ->
  forall ps, asub_heap_update p x y = Some ps ->
  validity (limp (land (lexists y ps) (lnot (hasvaldash x))) q).
intros. intro. intros.
rewrite satisfy_limp; intro.
rewrite satisfy_land in H2; destruct H2.
rewrite satisfy_lnot_hasvaldash in H3.
eapply satisfy_lexists_elim. apply H2. intros; clear H2.
rewrite heap_update_substitution_lemma in H4; [|apply H1].
simpl in H4. rewrite store_update_lookup_same in H4.
assert (x <> y). intro. apply H0. left; auto.
rewrite store_update_lookup_diff in H4; auto.
unfold strong_partial_correct in H.
apply H in H4; clear H; destruct H4.
pose proof (step_dispose x (heap_update h (s x) n) (store_update s y n)).
assert (dom (heap_update h (s x) n) (store_update s y n x)).
rewrite store_update_lookup_diff; auto.
apply heap_update_dom1. apply H5 in H6; clear H5.
apply H4 in H6; clear H4.
rewrite store_update_lookup_diff in H6; auto.
rewrite heap_update_clear_collapse in H6; auto.
rewrite acond. apply H6. intro. intro.
destruct (Nat.eq_dec x0 y).
exfalso. rewrite e in H4. apply H0. right. apply in_or_app. right. apply in_or_app; auto.
rewrite store_update_lookup_diff; auto.
Qed.

Theorem SPCSL_completeness (Gamma: assert -> Prop) (O: forall p, validity p -> Gamma p):
  forall pSq, restrict_pre pSq -> strong_partial_correct pSq -> SPCSL Gamma pSq.
intros. destruct pSq as (p, S, q); destruct S; destruct a; unfold restrict_pre in H.
- remember (fresh (v :: aoccur p ++ evar e ++ aoccur q)) as y.
  pose proof (asub_defined p v y).
  assert (forall x, In x (evar y) -> ~In x (abound p)). intros.
    simpl in H2. destruct H2; auto. rewrite <- H2. rewrite Heqy.
    apply fresh_notInGeneral. intros. right. apply in_or_app. left. apply in_or_app; auto.
  apply H1 in H2; clear H1; destruct H2.
  apply spc_conseq with (p := p) (q := (lexists y (land x (equals (esub e v y) v)))).
  apply O. intro. intro. rewrite satisfy_limp; tauto.
  apply spc_basic. rewrite Heqy. apply fresh_notInGeneral. intros.
    inversion H2. left; auto. apply in_app_or in H3; destruct H3.
    right. apply in_or_app; auto. right. apply in_or_app.
    right. apply in_or_app; auto. assumption.
  apply O. eapply SPCSL_strongest_basic. apply H0.
  rewrite Heqy. apply fresh_notIn. assumption.
- remember (fresh (v :: aoccur p ++ evar e ++ aoccur q)) as y.
  pose proof (asub_defined p v y).
  assert (forall x, In x (evar y) -> ~In x (abound p)). intros.
    simpl in H2. destruct H2; auto. rewrite <- H2. rewrite Heqy.
    apply fresh_notInGeneral. intros. right. apply in_or_app. left. apply in_or_app; auto.
  apply H1 in H2; clear H1; destruct H2.
  apply spc_conseq with (p := (land p (hasvaldash e))) (q := (lexists y (land x (hasval (esub e v y) v)))).
  apply O. intro. intros. rewrite satisfy_limp. intro. unfold strong_partial_correct in H0.
    rewrite satisfy_land. split; auto. rewrite satisfy_hasvaldash.
    apply H0 in H2. destruct H2. destruct (dom_dec h (e s)); auto. exfalso.
    apply H2. apply step_lookup_fail. rewrite dom_spec in H4. destruct (h (e s)); auto.
    exfalso. apply H4. intro. inversion H5.
  apply spc_lookup. rewrite Heqy. apply fresh_notInGeneral. intros.
    inversion H2. left; auto. right. apply in_app_or in H3; destruct H3.
    apply in_or_app; auto. apply in_or_app; right. apply in_or_app; auto.
    assumption.
  apply O. eapply SPCSL_strongest_lookup. apply H0.
  rewrite Heqy. apply fresh_notIn. assumption.
- remember (fresh (v :: aoccur p ++ evar e ++ aoccur q)) as y.
  pose proof (asub_heap_update_defined p v y).
  assert (forall y0 : V, In y0 (v :: evar y) -> ~ In y0 (abound p)). intros.
    simpl in H2. destruct H2. rewrite <- H2. auto. destruct H2. rewrite <- H2.
    rewrite Heqy. apply fresh_notInGeneral. intros. right. apply in_or_app. left.
    apply in_or_app; auto. inversion H2.
  apply H1 in H2; clear H1; destruct H2.
  apply spc_conseq with (p := (land p (hasvaldash v))) (q := land (lexists y x) (hasval v e)).
  apply O. intro. intro. rewrite satisfy_limp; intro.
    rewrite satisfy_land. split; auto. rewrite satisfy_hasvaldash.
    unfold strong_partial_correct in H0. apply H0 in H2. destruct H2.
    apply dom_spec. intro. apply H2. apply step_mutation_fail. intro.
    apply dom_spec in H5. simpl in H4. apply H5. auto.
  apply spc_mutation. rewrite Heqy. apply fresh_notInGeneral. intros.
    inversion H2. left; auto. right. apply in_app_or in H3; destruct H3.
    apply in_or_app; auto. apply in_or_app; right. apply in_or_app; auto. assumption.
  apply O. eapply SPCSL_strongest_mutation. apply H0. rewrite Heqy.
    apply fresh_notIn. assumption.
- remember (fresh (v :: aoccur p ++ evar e ++ aoccur q)) as y.
  pose proof (asub_defined p v y).
  assert (forall x, In x (evar y) -> ~In x (abound p)). intros.
    simpl in H2. destruct H2; auto. rewrite <- H2. rewrite Heqy.
    apply fresh_notInGeneral. intros. right. apply in_or_app. left. apply in_or_app; auto.
  apply H1 in H2; clear H1; destruct H2.
  pose proof (asub_heap_clear_defined (lexists y x) v).
  destruct H.
  assert (~In v (abound (lexists y x))). simpl. intro.
    destruct H4. rewrite <- H4 in Heqy.
    eapply fresh_notIn with (xs := y :: aoccur p ++ evar e ++ aoccur q).
    left. assumption. eapply (abound_asub _ _ _ H3 _ H1); assumption.
  apply H2 in H4; clear H2; destruct H4.
  apply spc_conseq with (p := p) (q := land x0 (hasval v e)).
  apply O. intro. intros. rewrite satisfy_limp; tauto.
  eapply spc_new; [ apply H | | apply H1 | ].
  rewrite Heqy. apply fresh_notInGeneral. intros. inversion H4.
    left; auto. right; apply in_or_app. apply in_app_or in H5; destruct H5; auto.
    right. apply in_or_app; auto. assumption.
  apply O. eapply SPCSL_strongest_new. apply H. apply H0.
    apply fresh_notIn. rewrite <- Heqy. apply H1.
    rewrite <- Heqy. assumption.
- remember (fresh (v :: aoccur p ++ aoccur q)) as y.
  pose proof (asub_heap_update_defined p v y).
  assert (forall y0 : V, In y0 (v :: evar y) -> ~ In y0 (abound p)). intros.
    simpl in H2. destruct H2. rewrite <- H2. auto. destruct H2. rewrite <- H2.
    rewrite Heqy. apply fresh_notInGeneral. intros. right. apply in_or_app. left.
    apply in_or_app; auto. inversion H2.
  apply H1 in H2; clear H1; destruct H2.
  apply spc_conseq with (p := (land p (hasvaldash v))) (q := land (lexists y x) (lnot (hasvaldash v))).
  apply O. intro. intro. rewrite satisfy_limp; intro.
    rewrite satisfy_land. split; auto. rewrite satisfy_hasvaldash.
    unfold strong_partial_correct in H0. apply H0 in H2. destruct H2.
    apply dom_spec. intro. apply H2. apply step_dispose_fail. intro.
    apply dom_spec in H5. simpl in H4. apply H5. auto.
  apply spc_dispose. rewrite Heqy. apply fresh_notInGeneral. intros.
    inversion H2. left; auto. right. apply in_app_or in H3; destruct H3.
    apply in_or_app; left. apply in_or_app; auto. apply in_or_app; left.
    apply in_or_app; auto. assumption.
  apply O. eapply SPCSL_strongest_dispose. apply H0. rewrite Heqy.
    apply fresh_notIn. assumption.
Qed.

Corollary SPCSL_soundness_completeness:
  forall pSq, restrict_pre pSq -> SPCSL validity pSq <-> strong_partial_correct pSq.
intros. split.
apply SPCSL_soundness. tauto.
apply SPCSL_completeness. tauto. tauto.
Qed.

Corollary result:
  forall pSq, restrict pSq -> SPCSL validity pSq <-> WPCSL validity pSq.
intros. destruct H. split.
intro. apply SPCSL_soundness_completeness in H1; auto.
apply WPCSL_soundness_completeness; auto.
intro. apply WPCSL_soundness_completeness in H1; auto.
apply SPCSL_soundness_completeness; auto.
Qed.

End Classical.

(* To show the used axioms in our development, we make everything concrete: *)
Module ClassicalIHeap := Classical IHeap.
Import ClassicalIHeap.
Print Assumptions result.
