(* Copyright 2022 <anonymized> *)

(* ON SEPARATION LOGIC *)
(* Author: <anonymized> *)

Require Export OnSeparationLogic.Language.

Module Intuitionistic (Export HS: HeapSig).

Module L := Language HS.
Include L.

Definition Extends (h h': heap): Prop :=
  exists h'', Partition h' h h''.

Proposition Extends_included (h h': heap):
  Extends h h' <-> forall n, dom h n -> h' n = h n.
unfold Extends; split; intro.
- intros.
  destruct H as (h'' & H).
  eapply Partition_spec1. apply H. assumption.
- apply Partition_intro2; assumption.
Qed.

Proposition Extends_refl (h: heap): Extends h h.
unfold Extends.
exists heap_empty.
assert (forall k : Z, ~ (dom h k /\ dom heap_empty k)).
  intro. intro. destruct H. apply dom_spec in H0.
  apply H0. apply heap_empty_spec.
pose proof (Partition_intro1 h heap_empty H); destruct H0.
assert (forall n : Z, h n = x n).
  intro. destruct (dom_dec h n).
  symmetry. apply Partition_spec1 with (h1 := h) (h2 := heap_empty); auto.
  rewrite (Partition_spec3 x) with (h1 := h) (h2 := heap_empty); auto.
  rewrite dom_spec in H1. destruct (h n); auto. exfalso. apply H1. intro. inversion H2.
  rewrite dom_spec. intro. apply H2. apply heap_empty_spec.
pose proof (heap_ext h x H1).
rewrite H2 at 1. assumption.
Qed.

Proposition Extends_trans (h h' h'': heap):
  Extends h h' -> Extends h' h'' -> Extends h h''.
unfold Extends; intros.
destruct H.
destruct H0.
assert (forall k, ~(dom x k /\ dom x0 k)). {
  intros; intro. destruct H1.
  eapply Partition_spec4. apply H0.
  split.
  eapply Partition_dom_inv_right. apply H. apply H1.
  assumption. }
pose proof (Partition_intro1 _ _ H1); destruct H2.
exists x1.
assert (forall k, ~(dom h k /\ dom x1 k)). {
  intros; intro. destruct H3.
  pose proof (Partition_dom_inv_left _ _ _ _ H H3).
  pose proof (Partition_dom_right1 _ _ _ _ H0 H5).
  pose proof (Partition_dom_split _ _ _ _ H2 H4). destruct H7.
  eapply Partition_dom_right1. apply H. apply H3. assumption.
  apply H6. assumption. }
pose proof (Partition_intro1 _ _ H3); destruct H4.
assert (forall n : Z, h'' n = x2 n). {
  intros. destruct (dom_dec h n).
  rewrite (Partition_spec1 x2) with (h1 := h) (h2 := x1); auto.
  pose proof (Partition_dom_inv_left _ _ _ _ H H5).
  rewrite (Partition_spec1) with (h1 := h') (h2 := x0); auto.
  rewrite (Partition_spec1) with (h1 := h) (h2 := x); auto.
  destruct (dom_dec x1 n).
  rewrite (Partition_spec2 x2) with (h1 := h) (h2 := x1); auto.
  pose proof (Partition_dom_split _ _ _ _ H2 H6). destruct H7.
  pose proof (Partition_dom_inv_right _ _ _ _ H H7).
  rewrite Partition_spec1 with (h1 := h') (h2 := x0); auto.
  rewrite Partition_spec2 with (h1 := h) (h2 := x); auto.
  rewrite (Partition_spec1 x1) with (h1 := x) (h2 := x0); auto.
  rewrite (Partition_spec2 x1) with (h1 := x) (h2 := x0); auto.
  rewrite Partition_spec2 with (h1 := h') (h2 := x0); auto.
  rewrite (Partition_spec3 x2) with (h1 := h) (h2 := x1); auto.
  apply Partition_spec3 with (h1 := h') (h2 := x0); auto.
  intro.
  pose proof (Partition_dom_split _ _ _ _ H H7). destruct H8.
  apply H5; auto. apply H6. eapply Partition_dom_inv_left. apply H2. assumption.
  intro.
  apply H6. eapply Partition_dom_inv_right. apply H2. assumption. }
pose proof (heap_ext h'' x2 H5).
rewrite H6. assumption.
Qed.

Proposition Extends_Partition_split (h h' h1 h2: heap):
  Extends h h' -> Partition h h1 h2 ->
  exists h1' h2', Partition h' h1' h2' /\ Extends h1 h1' /\ Extends h2 h2'.
intros.
unfold Extends in H; destruct H.
assert (forall k, ~(dom h1 k /\ dom x k)). {
  intros; intro; destruct H1.
  pose proof (Partition_dom_inv_left _ _ _ _ H0 H1).
  eapply Partition_spec4. apply H. split. apply H3. apply H2. }
pose proof (Partition_intro1 _ _ H1); destruct H2 as (h1' & H2).
exists h1'. exists h2. split.
assert (forall k, ~(dom h1' k /\ dom h2 k)). {
  intros; intro; destruct H3.
  apply Partition_dom_split with (h1 := h1) (h2 := x) in H3; auto; destruct H3.
  eapply Partition_spec4. apply H0. split. apply H3. apply H4.
  apply Partition_dom_inv_right with (h := h) (h1 := h1) in H4; auto.
  eapply Partition_spec4. apply H. split. apply H4. apply H3. }
pose proof (Partition_intro1 _ _ H3); destruct H4.
assert (forall n, h' n = x0 n). {
  intros. destruct (dom_dec h n).
  apply Partition_dom_split with (h1 := h1) (h2 := h2) in H5; auto. destruct H5.
  pose proof (Partition_dom_inv_left _ _ _ _ H2 H5).
  rewrite (Partition_spec1 x0) with (h1 := h1') (h2 := h2); auto.
  rewrite (Partition_spec1 h1') with (h1 := h1) (h2 := x); auto.
  pose proof (Partition_dom_inv_left _ _ _ _ H0 H5).
  rewrite (Partition_spec1 h') with (h1 := h) (h2 := x); auto.
  eapply Partition_spec1. apply H0. assumption.
  rewrite (Partition_spec2 x0) with (h1 := h1') (h2 := h2); auto.
  rewrite <- (Partition_spec2 h h1 h2); auto.
  apply Partition_dom_inv_right with (h := h) (h1 := h1) in H5; auto.
  eapply Partition_spec1. apply H. assumption.
  destruct (dom_dec x n).
  rewrite Partition_spec2 with (h1 := h) (h2 := x); auto.
  pose proof (Partition_dom_inv_right _ _ _ _ H2 H6).
  rewrite (Partition_spec1 x0) with (h1 := h1') (h2 := h2); auto.
  symmetry. eapply Partition_spec2. apply H2. auto.
  rewrite Partition_spec3 with (h1 := h) (h2 := x); auto.
  symmetry. eapply Partition_spec3. apply H4. intro.
  pose proof (Partition_dom_split _ _ _ _ H2 H7); destruct H8.
  apply H5. eapply Partition_dom_inv_left. apply H0. assumption.
  apply H6. assumption. intro. apply H5.
  eapply Partition_dom_inv_right. apply H0. assumption. }
pose proof (heap_ext _ _ H5).
rewrite H6. assumption.
split.
unfold Extends. exists x. assumption.
apply Extends_refl.
Qed.

Proposition Extends_Partition_extend (h h' h'' g: heap):
  Extends h h' -> Partition h'' h' g ->
  exists g', Partition h'' h g' /\ Extends g g'.
intros.
unfold Extends in H; destruct H.
assert (forall k, ~(dom x k /\ dom g k)). {
  intro; intro; destruct H1.
  eapply Partition_dom_right2. apply H0. apply H2.
  eapply Partition_dom_inv_right. apply H. assumption. }
pose proof (Partition_intro1 _ _ H1); destruct H2.
exists x0. split.
assert (forall k, ~(dom h k /\ dom x0 k)). {
  intro; intro; destruct H3.
  pose proof (Partition_dom_split _ _ _ _ H2 H4). destruct H5.
  eapply Partition_spec4. apply H. split. apply H3. apply H5.
  eapply Partition_spec4. apply H0. split; [|apply H5].
  eapply Partition_dom_inv_left. apply H. assumption. }
pose proof (Partition_intro1 _ _ H3); destruct H4.
assert (forall n, h'' n = x1 n). {
  intro. destruct (dom_dec h n).
  erewrite (Partition_spec1 x1); [|apply H4|apply H5].
  erewrite (Partition_spec1 h''); [|apply H0|].
  erewrite (Partition_spec1 h'). reflexivity. apply H. assumption.
  eapply Partition_dom_inv_left. apply H. assumption.
  destruct (dom_dec x0 n).
  erewrite (Partition_spec2 x1); [|apply H4|apply H6].
  eapply Partition_dom_split in H6; [|apply H2]. destruct H6.
  erewrite (Partition_spec1 h''); [|apply H0|].
  erewrite (Partition_spec2 h'); [|apply H|].
  symmetry. eapply Partition_spec1. apply H2. assumption. assumption.
  eapply Partition_dom_inv_right. apply H. assumption.
  erewrite (Partition_spec2 h''); [|apply H0|auto].
  erewrite (Partition_spec2 x0); [|apply H2|]; auto.
  erewrite (Partition_spec3 x1); [|apply H4|auto|auto].
  erewrite (Partition_spec3 h''). reflexivity. apply H0.
  intro. eapply Partition_dom_split in H7; [|apply H].
  destruct H7. apply H5; auto. apply H6.
  eapply Partition_dom_inv_left. apply H2. auto.
  intro. apply H6.
  eapply Partition_dom_inv_right. apply H2. auto. }
pose proof (heap_ext _ _ H5).
rewrite H6. assumption.
unfold Extends. exists x. apply Partition_comm. assumption.
Qed.

Proposition Extends_heap_update (h: heap) (k v: Z):
  ~dom h k ->
  Extends h (heap_update h k v).
intros.
unfold Extends.
exists (heap_update heap_empty k v).
assert (forall k', ~(dom h k' /\ dom (heap_update heap_empty k v) k')). {
  intro; intro; destruct H0.
  destruct (Z.eq_dec k k').
  rewrite <- e in H0. apply H; auto.
  rewrite heap_update_dom2 in H1; auto.
  rewrite dom_spec in H1.
  rewrite heap_empty_spec in H1.
  apply H1. reflexivity. }
pose proof (Partition_intro1 _ _ H0); destruct H1.
assert (forall n, x n = (heap_update h k v) n). {
  intro. destruct (dom_dec h n).
  rewrite heap_update_spec2.
  eapply Partition_spec1. apply H1. auto.
  intro. rewrite <- H3 in H2. apply H; auto.
  destruct (dom_dec (heap_update heap_empty k v) n).
  destruct (Z.eq_dec k n).
  rewrite e.
  rewrite heap_update_spec1.
  erewrite Partition_spec2; [|apply H1|].
  rewrite e.
  rewrite heap_update_spec1. reflexivity.
  rewrite e.
  apply heap_update_dom1.
  rewrite heap_update_spec2; auto.
  rewrite heap_update_dom2 in H3; auto.
  rewrite dom_spec in H3.
  rewrite heap_empty_spec in H3.
  exfalso; apply H3; auto.
  erewrite Partition_spec3; [|apply H1|auto|auto].
  destruct (Z.eq_dec k n).
  rewrite e in H3.
  exfalso. apply H3. apply heap_update_dom1.
  rewrite heap_update_spec2; auto.
  rewrite dom_spec in H2.
  destruct (h n); auto.
  exfalso. apply H2. intro. inversion H4. }
pose proof (heap_ext _ _ H2). rewrite <- H3.
assumption.
Qed.

Proposition Extends_lift_heap_update (h h': heap) (k v: Z):
  Extends h h' -> ~ dom h k -> dom h' k ->
  Extends (heap_update h k v) (heap_update h' k v).
unfold Extends; intros.
destruct H.
exists (heap_clear x k).
assert (forall k0, ~(dom (heap_update h k v) k0 /\ dom (heap_clear x k) k0)). {
  intros. intro. destruct H2. destruct (Z.eq_dec k k0).
  rewrite <- e in H2, H3.
  apply heap_clear_dom1 in H3; auto.
  apply heap_clear_dom2 in H3; auto.
  apply heap_update_dom2 in H2; auto.
  eapply Partition_spec4. apply H. split. apply H2. apply H3. }
pose proof (Partition_intro1 _ _ H2); clear H2; destruct H3.
assert (forall n, x0 n = (heap_update h' k v) n). {
  intros. destruct (Z.eq_dec k n). rewrite <- e.
  erewrite Partition_spec1; [|apply H2|].
  repeat rewrite heap_update_spec1; reflexivity.
  apply heap_update_dom1.
  rewrite heap_update_spec2; auto.
  destruct (dom_dec h' n).
  destruct (Partition_dom_split _ _ _ _ H H3).
  erewrite (Partition_spec1 x0); [|apply H2|].
  rewrite heap_update_spec2; auto.
  symmetry; eapply Partition_spec1. apply H.
  auto. apply heap_update_dom2; auto.
  erewrite (Partition_spec2 x0); [|apply H2|].
  rewrite heap_clear_spec2; auto.
  symmetry; eapply Partition_spec2. apply H.
  auto. apply heap_clear_dom2; auto.
  assert (~dom h n). intro. apply H3.
    eapply Partition_dom_inv_left. apply H. auto.
  assert (~dom x n). intro. apply H3.
    eapply Partition_dom_inv_right. apply H. auto.
  erewrite (Partition_spec3 h'); [|apply H|auto|auto].
  eapply Partition_spec3. apply H2. intro.
  rewrite heap_update_dom2 in H6; auto. intro.
  rewrite heap_clear_dom2 in H6; auto. }
pose proof (heap_ext _ _ H3); clear H3.
rewrite <- H4. assumption.
Qed.

Proposition Extends_heap_update_back (h h': heap) (k v: Z):
  dom h k -> Extends (heap_update h k v) h' ->
  exists h'', Extends h h'' /\ h' = heap_update h'' k v.
intros.
unfold Extends in H0; destruct H0.
rewrite dom_spec in H; remember (h k); destruct o.
2: exfalso; apply H; auto.
clear H. exists (heap_update h' k z); split.
- unfold Extends.
  exists x.
  assert (forall k : Z, ~ (dom h k /\ dom x k)). {
    intro; intro; destruct H.
    pose proof (Partition_spec4 _ _ _ H0 k0).
    apply H2. split; auto.
    destruct (Z.eq_dec k k0).
    rewrite e.
    apply heap_update_dom1.
    apply heap_update_dom2; auto. }
  pose proof (Partition_intro1 h x H); destruct H1.
  assert (forall n : Z, x0 n = heap_update h' k z n). {
    intros. destruct (Z.eq_dec n k).
    rewrite e. rewrite heap_update_spec1.
    erewrite Partition_spec1; [|apply H1|].
    auto. apply dom_spec. rewrite <- Heqo. intro. inversion H2.
    rewrite heap_update_spec2; auto.
    destruct (dom_dec h n).
    rewrite (Partition_spec1 x0) with (h1 := h) (h2 := x); auto.
    rewrite (Partition_spec1 h') with (h1 := heap_update h k v) (h2 := x); auto.
    rewrite heap_update_spec2; auto.
    apply heap_update_dom2; auto.
    destruct (dom_dec x n).
    rewrite (Partition_spec2 x0) with (h1 := h) (h2 := x); auto.
    rewrite (Partition_spec2 h') with (h1 := heap_update h k v) (h2 := x); auto.
    rewrite (Partition_spec3 x0) with (h1 := h) (h2 := x); auto.
    rewrite (Partition_spec3 h') with (h1 := heap_update h k v) (h2 := x); auto.
    intro. rewrite heap_update_dom2 in H4; auto. }
  pose proof (heap_ext x0 (heap_update h' k z) H2).
  rewrite <- H3. assumption.
- rewrite heap_update_collapse.
  apply heap_ext; intro.
  destruct (Z.eq_dec k n).
  rewrite <- e.
  rewrite heap_update_spec1.
  erewrite Partition_spec1; [|apply H0|].
  rewrite heap_update_spec1; reflexivity.
  apply heap_update_dom1.
  rewrite heap_update_spec2; auto.
Qed.

Proposition Extends_lift_heap_update2 (h h': heap) (k v: Z):
  Extends h h' -> dom h k ->
  Extends (heap_update h k v) (heap_update h' k v).
intros.
unfold Extends in *. destruct H.
exists x.
assert (forall z : Z, ~ (dom (heap_update h k v) z /\ dom x z)). {
  intro; intro; destruct H1.
  destruct (Z.eq_dec k z).
  eapply Partition_spec4. apply H. split. apply H0. rewrite e; auto.
  apply heap_update_dom2 in H1; auto.
  eapply Partition_spec4. apply H. split. apply H1. auto. }
pose proof (Partition_intro1 _ _ H1); destruct H2.
assert (forall n : Z, heap_update h' k v n = x0 n). {
  intros. destruct (Z.eq_dec k n).
  rewrite e. rewrite heap_update_spec1.
  erewrite Partition_spec1; [|apply H2|].
  rewrite e. rewrite heap_update_spec1; auto.
  rewrite e. apply heap_update_dom1.
  rewrite heap_update_spec2; auto.
  destruct (dom_dec h n).
  erewrite (Partition_spec1 h'); [|apply H|auto].
  erewrite (Partition_spec1 x0); [|apply H2|].
  rewrite heap_update_spec2; auto.
  apply heap_update_dom2; auto.
  destruct (dom_dec x n).
  erewrite (Partition_spec2 h'); [|apply H|auto].
  erewrite (Partition_spec2 x0); [|apply H2|]; auto.
  erewrite (Partition_spec3 h'); [|apply H|auto|auto].
  erewrite (Partition_spec3 x0); [auto|apply H2| |auto].
  intro. rewrite heap_update_dom2 in H5; auto. }
pose proof (heap_ext _ _ H3).
rewrite H4. assumption.
Qed.

Proposition Extends_dom (h h': heap) (k: Z):
  dom h k -> Extends h h' -> dom h' k.
intros.
unfold Extends in H0; destruct H0.
eapply Partition_dom_inv_left.
apply H0.
apply H.
Qed.

Proposition Extends_heap_clear (h h': heap) (k: Z):
  h' k = h k -> Extends (heap_clear h k) h' -> Extends h h'.
repeat rewrite Extends_included; intros.
destruct (Z.eq_dec n k).
rewrite e; apply H.
rewrite H0.
rewrite heap_clear_spec2; auto.
apply heap_clear_dom2; auto.
Qed.

Proposition Extends_heap_clear_update (h h': heap) (k v: Z):
  Extends (heap_clear h k) h' -> Extends (heap_clear h k) (heap_update h' k v).
repeat rewrite Extends_included; intros.
destruct (Z.eq_dec n k).
rewrite e in H0.
exfalso; eapply heap_clear_dom1; apply H0.
rewrite heap_update_spec2; auto.
Qed.

(* ====================================== *)
(* INTUITIONISTIC SEMANTICS OF ASSERTIONS *)
(* ====================================== *)

Fixpoint satisfy (h: heap) (s: store) (p: assert): Prop :=
  match p with
  | test g => gval g s = true
  | hasval e e' => dom h (e s) /\ h (e s) = e' s
  | land p q => satisfy h s p /\ satisfy h s q
  | lor p q => satisfy h s p \/ satisfy h s q
  | limp p q => forall h', Extends h h' -> satisfy h' s p -> satisfy h' s q
  | lforall x p => forall v, satisfy h (store_update s x v) p
  | lexists x p => exists v, satisfy h (store_update s x v) p
  | sand p q => exists h1 h2, Partition h h1 h2 /\ satisfy h1 s p /\ satisfy h2 s q
  | simp p q => forall h'' h', Partition h'' h h' -> satisfy h' s p -> satisfy h'' s q
  end.

Proposition satisfy_monotonic (h: heap) (s: store) (p: assert):
  satisfy h s p -> forall h', Extends h h' -> satisfy h' s p.
intros. generalize dependent s. generalize dependent h'. revert h. induction p; intros; simpl; simpl in H.
- apply H.
- destruct H.
  apply Extends_included with (n := e s) in H0; try assumption.
  split. apply dom_spec. rewrite H0. apply dom_spec in H. apply H.
  rewrite H0. assumption.
- destruct H.
  split. apply (IHp1 h); assumption.
  apply (IHp2 h); assumption.
- destruct H.
  left. apply (IHp1 h); assumption.
  right. apply (IHp2 h); assumption.
- intros h'' H1 H2. apply H.
  eapply Extends_trans. apply H0. apply H1. assumption.
- destruct H.
  exists x. apply (IHp h); assumption.
- intro z.
  specialize (H z). apply (IHp h); assumption.
- destruct H; destruct H; destruct H; destruct H1.
  pose proof (Extends_Partition_split _ _ _ _ H0 H); destruct H3; destruct H3.
  destruct H3; destruct H4.
  exists x1. exists x2. split. assumption. split.
  apply (IHp1 x). apply H4. assumption.
  apply (IHp2 x0). apply H5. assumption.
- intros.
  pose proof (Extends_Partition_extend _ _ _ _ H0 H1); destruct H3; destruct H3.
  apply IHp1 with (h' := x) in H2; auto.
  eapply H. apply H3. apply H2.
Qed.

Proposition satisfy_land (h: heap) (s: store) (p q: assert):
  satisfy h s (land p q) <-> satisfy h s p /\ satisfy h s q.
simpl; split; intro; auto.
Qed.

Proposition satisfy_lor (h: heap) (s: store) (p q: assert):
  satisfy h s (lor p q) <-> satisfy h s p \/ satisfy h s q.
simpl; split; intro; auto.
Qed.

Proposition satisfy_limp (h: heap) (s: store) (p q: assert):
  satisfy h s (limp p q) <-> (forall h', Extends h h' -> satisfy h' s p -> satisfy h' s q).
simpl; split; intro; auto.
Qed.

Proposition satisfy_limp_elim (h: heap) (s: store) (p q: assert):
  satisfy h s (limp p q) -> satisfy h s p -> satisfy h s q.
intros.
rewrite satisfy_limp in H.
specialize H with h.
pose proof (Extends_refl h).
apply H in H1; auto.
Qed.

Proposition satisfy_lnot (h: heap) (s: store) (p: assert):
  satisfy h s (lnot p) <-> (forall h', Extends h h' -> ~satisfy h' s p).
simpl; split; intros.
intro. specialize H with h'. apply H in H0; auto. inversion H0.
exfalso. eapply H. apply H0. auto.
Qed.

Proposition satisfy_lnot_elim (h: heap) (s: store) (p: assert):
  satisfy h s (lnot p) -> ~satisfy h s p.
intros. intro.
rewrite satisfy_lnot in H.
specialize H with h.
pose proof (Extends_refl h).
apply H in H1; auto.
Qed.

Proposition satisfy_lforall (h: heap) (s: store) (x: V) (p: assert):
  satisfy h s (lforall x p) <-> forall v, satisfy h (store_update s x v) p.
simpl; split; intros; auto.
Qed.

Proposition satisfy_lexists (h: heap) (s: store) (x: V) (p: assert):
  satisfy h s (lexists x p) <-> exists v, satisfy h (store_update s x v) p.
simpl; split; intros; auto.
Qed.

Proposition satisfy_equals (h: heap) (s: store) (e0 e1: expr):
  satisfy h s (equals e0 e1) <-> e0 s = e1 s.
simpl. destruct (Z.eq_dec (eval e0 s) (eval e1 s)).
rewrite e. tauto. split. intro. inversion H.
intro. exfalso. apply n. assumption.
Qed.

Proposition satisfy_lnot_equals (h: heap) (s: store) (e0 e1: expr):
  satisfy h s (lnot (equals e0 e1)) <-> e0 s <> e1 s.
split; intro.
rewrite satisfy_lnot in H.
specialize H with h.
pose proof (H (Extends_refl h)); clear H.
rewrite satisfy_equals in H0.
auto.
rewrite satisfy_lnot; intros; intro.
rewrite satisfy_equals in H1.
apply H; auto.
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
  simpl in H. destruct H. destruct H.
  rewrite store_update_lookup_same in H0.
  rewrite dom_spec; intro.
  assert (e s = e (store_update s v x)). {
  apply econd. intro; intro.
  unfold store_update.
  destruct (Nat.eq_dec v x0).
  rewrite <- e0 in H2.
  rewrite Heqv in H2.
  exfalso. eapply fresh_notIn. apply H2.
  reflexivity. }
  rewrite H2 in H1.
  rewrite H0 in H1.
  inversion H1.
- simpl.
  apply dom_spec in H.
  remember (h (e s)). destruct o.
  2: exfalso; apply H; auto.
  clear H. exists z.
  remember (fresh (evar e)).
  rewrite store_update_lookup_same.
  assert (e s = e (store_update s v z)). {
  apply econd. intro; intro.
  unfold store_update.
  destruct (Nat.eq_dec v x).
  rewrite <- e0 in H.
  rewrite Heqv in H.
  exfalso. eapply fresh_notIn. apply H.
  reflexivity. }
  rewrite <- H. split.
  apply dom_spec. intro. exfalso. rewrite <- Heqo in H0. inversion H0.
  rewrite <- Heqo. reflexivity.
Qed.

Proposition satisfy_sand (h: heap) (s: store) (p q: assert):
  satisfy h s (sand p q) <->
  (exists h1 h2, Partition h h1 h2 /\ satisfy h1 s p /\ satisfy h2 s q).
split; intro; auto.
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

Proposition satisfy_limp_hasvaldash_elim (h: heap) (s: store) (p: assert) (x: V):
  dom h (s x) -> satisfy h s (limp (hasvaldash x) p) <-> satisfy h s p.
intros. split; intro.
rewrite satisfy_limp in H0.
apply H0.
apply Extends_refl.
rewrite satisfy_hasvaldash; simpl; auto.
rewrite satisfy_limp; intros.
eapply satisfy_monotonic.
apply H0. assumption.
Qed.

(* =================================== *)
(* COINCIDENCE CONDITION ON ASSERTIONS *)
(* =================================== *)

Proposition acond (h: heap) (p: assert):
  forall (s t: store), eq_restr s t (avar p) ->
    (satisfy h s p <-> satisfy h t p).
generalize dependent h; induction p; intros; try tauto; simpl in *.
erewrite (gcond g); [|apply H]; apply iff_refl.
1,2,3,4: apply eq_restr_split in H; destruct H as (H0 & H1).
pose proof (econd e s t) as G; rewrite G; try tauto;
pose proof (econd e0 s t) as I; rewrite I; tauto.
- specialize IHp1 with h s t; specialize IHp2 with h s t; tauto.
- specialize IHp1 with h s t; specialize IHp2 with h s t; tauto.
- apply iff_split_imp_forall1; intros.
  specialize IHp1 with x s t; tauto.
  specialize IHp2 with x s t; tauto.
- apply iff_split_exists; intros.
  apply IHp. intro. intros.
  destruct (Nat.eq_dec v x0).
  rewrite e.
  repeat rewrite store_update_lookup_same. reflexivity.
  repeat rewrite store_update_lookup_diff; auto.
  apply H.
  apply In_remove; auto.
- apply iff_split_forall; intros.
  apply IHp. intro. intros.
  destruct (Nat.eq_dec v x0).
  rewrite e.
  repeat rewrite store_update_lookup_same. reflexivity.
  repeat rewrite store_update_lookup_diff; auto.
  apply H.
  apply In_remove; auto.
- apply iff_split_and_exists; intros.
  1: apply IHp1.
  2: apply IHp2.
  all: intro; intro; apply H; apply in_or_app; auto.
- apply iff_split_imp_forall; intros.
  1: apply IHp1.
  2: apply IHp2.
  all: intro; intro; apply H; apply in_or_app; auto.
Qed.

(* ======== *)
(* VALIDITY *)
(* ======== *)

Definition validity (p: assert): Prop := forall h s, satisfy h s p.

(* =========================================== *)
(* STRONG PARTIAL CORRECTNESS OF HOARE TRIPLES *)
(* =========================================== *)

Definition strong_partial_correct: hoare -> Prop := fun '(mkhoare p S q) =>
  forall h s, satisfy h s p ->
    ~bigstep S (h, s) None /\
    forall h' s', bigstep S (h, s) (Some (h', s')) -> satisfy h' s' q.

(* ======================== *)
(* STORE SUBSTITUTION LEMMA *)
(* ======================== *)

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
  simpl. apply iff_split_or.
  apply IHp1; assumption.
  apply IHp2; assumption.
- apply option_app_elim in H; destruct H; destruct H.
  apply option_app_elim in H0; destruct H0; destruct H0.
  inversion H1.
  simpl. apply iff_split_imp_forall1; intros.
  apply IHp1; assumption.
  apply IHp2; assumption.
- destruct (in_dec Nat.eq_dec v (evar e)). inversion H.
  apply option_app_elim in H; destruct H; destruct H.
  inversion H0; clear H0 H2.
  simpl.
  apply iff_split_exists; intro.
  destruct (Nat.eq_dec x v).
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
  apply iff_split_and_exists.
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

(* ========================================== *)
(* CONDITIONAL HEAP UPDATE SUBSTITUTION LEMMA *)
(* ========================================== *)

Proposition cheap_update_substitution_lemma_p1 (h: heap) (s: store) (x: V) (e e0 e1: expr):
  satisfy h s (lor (land (equals x e0) (equals e e1)) (land (lnot (equals x e0)) (hasval e0 e1))) <->
  (s x = e0 s -> e s = e1 s) /\ (s x <> e0 s -> h (e0 s) = e1 s).
split; intro.
- rewrite satisfy_lor in H; destruct H.
  + rewrite satisfy_land in H; destruct H.
    rewrite satisfy_equals in H.
    rewrite satisfy_equals in H0.
    split; intro.
    * destruct (Z.eq_dec (e s) (e1 s)).
      assumption.
      exfalso. apply n; auto.
    * simpl in H.
      exfalso. apply H1; auto.
  + rewrite satisfy_land in H; destruct H.
    rewrite satisfy_hasval in H0.
    rewrite satisfy_lnot in H.
    specialize H with h.
    pose proof (H (Extends_refl h)); clear H.
    rewrite satisfy_equals in H1.
    split; intro.
    * exfalso. apply H1; simpl; auto.
    * apply H0.
- destruct H.
  rewrite satisfy_lor.
  destruct (Z.eq_dec (s x) (e0 s)).
  + left.
    rewrite satisfy_land. split; rewrite satisfy_equals.
    assumption. apply H; auto.
  + right.
    rewrite satisfy_land. split.
    rewrite satisfy_lnot; intros. rewrite satisfy_equals. assumption.
    rewrite satisfy_hasval. apply H0. assumption.
Qed.

Proposition cheap_update_substitution_lemma_p2 (h: heap) (s: store) (x: V) (e e0 e1: expr):
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

Proposition cheap_update_substitution_lemma_p3 (s: store) (x v: V) (e: expr) (x1: Z):
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

Proposition cheap_update_substitution_lemma_p4 (h h1 h2: heap) (k v: Z):
  Partition h h1 h2 -> ~ dom h2 k ->
  Partition (heap_update h k v) (heap_update h1 k v) h2.
intros.
pose proof (Partition_intro1 (heap_update h1 k v) h2).
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

Proposition cheap_update_substitution_lemma_p5 (h h1 h2: heap) (k v: Z):
  Partition (heap_update h k v) h1 h2 ->
  (exists h1', Partition h h1' h2 /\ h1 = heap_update h1' k v /\ ~dom h2 k) \/
  (exists h2', Partition h h1 h2' /\ h2 = heap_update h2' k v /\ ~dom h1 k).
intros.
pose proof (heap_update_dom1 h k v); pose proof (Partition_dom_split _ _ _ _ H H0); destruct H1.
- left. remember (h k); destruct o.
  + exists (heap_update h1 k z).
    pose proof (Partition_dom_right1 _ _ _ k H H1).
    split.
    pose proof (Partition_intro1 (heap_update h1 k z) h2). destruct H3.
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
    pose proof (Partition_dom_right1 _ _ _ k H H1).
    assert (h1 k = v). { pose proof (Partition_spec1 _ _ _ H k H1).
    rewrite heap_update_spec1 in H3. inversion H3. reflexivity. }
    split.
    pose proof (Partition_intro1 (heap_clear h1 k) h2). destruct H4.
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
    pose proof (Partition_dom_right1 _ _ _ k H H1).
    split.
    pose proof (Partition_intro1 (heap_update h2 k z) h1). destruct H3.
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
    pose proof (Partition_dom_right1 _ _ _ k H H1).
    assert (h2 k = v). { pose proof (Partition_spec1 _ _ _ H k H1).
    rewrite heap_update_spec1 in H3. inversion H3. reflexivity. }
    split.
    apply Partition_comm.
    pose proof (Partition_intro1 (heap_clear h2 k) h1). destruct H4.
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

Proposition cheap_update_substitution_lemma_p6 (h h' h'': heap) (k v: Z):
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
  + pose proof (Partition_intro1 h h').
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
  + pose proof (Partition_intro1 h h').
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
    eapply Partition_dom_right1. apply H.
    assert (dom h'' k). {
    rewrite dom_spec. intro.
    rewrite Partition_spec1 with (h1 := heap_update h k v) (h2 := h') in H1; auto.
    rewrite heap_update_spec1 in H1. inversion H1.
    apply heap_update_dom1. }
    apply heap_update_dom1.
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

Proposition cheap_update_substitution_lemma_p7 (h h' h'': heap) (k v: Z):
  Partition h'' h h' -> ~ dom h' k ->
  Partition (heap_update h'' k v) (heap_update h k v) h'.
intros.
pose proof (Partition_intro1 (heap_update h k v) h').
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

Lemma cheap_update_substitution_lemma (h: heap) (s: store) (p: assert) (x: V) (e: expr):
  dom h (s x) ->
  forall ps, asub_cheap_update p x e = Some ps ->
    (satisfy h s ps <-> satisfy (heap_update h (s x) (e s)) s p).
generalize dependent s; generalize dependent h;
induction p; intros.
- inversion H0; unfold satisfy; apply iff_refl.
- inversion H0.
  rewrite cheap_update_substitution_lemma_p1.
  rewrite cheap_update_substitution_lemma_p2.
  apply iff_refl.
- apply option_app_elim in H0; destruct H0; destruct H0.
  apply option_app_elim in H1; destruct H1; destruct H1.
  inversion H2.
  simpl; apply iff_split_and.
  apply IHp1; assumption.
  apply IHp2; assumption.
- apply option_app_elim in H0; destruct H0; destruct H0.
  apply option_app_elim in H1; destruct H1; destruct H1.
  inversion H2.
  simpl; apply iff_split_or.
  apply IHp1; assumption.
  apply IHp2; assumption.
- apply option_app_elim in H0; destruct H0; destruct H0.
  fold asub_cheap_update in H0.
  apply option_app_elim in H1; destruct H1; destruct H1.
  fold asub_cheap_update in H1.
  inversion H2.
  simpl; split; intros.
  + pose proof (Extends_heap_update_back _ _ _ _ H H5).
    destruct H7; destruct H7.
    rewrite H8. rewrite H8 in H6.
    pose proof (Extends_dom _ _ _ H H7).
    rewrite <- IHp1 in H6; [|auto|apply H0].
    rewrite <- IHp2; [|auto|apply H1].
    apply H3; auto.
  + rewrite IHp1 in H6.
    apply H3 in H6.
    rewrite <- IHp2 in H6; [| |apply H1].
    assumption.
    eapply Extends_dom. apply H. auto.
    apply Extends_lift_heap_update2; auto.
    eapply Extends_dom. apply H. auto.
    assumption.
- unfold asub_cheap_update in H0; fold asub_cheap_update in H0.
  destruct (in_dec Nat.eq_dec v (x :: evar e)).
  inversion H0.
  apply option_app_elim in H0; destruct H0; destruct H0.
  inversion H1; clear H1.
  simpl.
  apply iff_split_exists; intro.
  specialize IHp with h (store_update s v x1) x0.
  apply IHp in H0. rewrite H0.
  pose proof (cheap_update_substitution_lemma_p3 s x v e x1 n).
  destruct H1. rewrite H1. rewrite H2.
  apply iff_refl.
  assert (v <> x). intro. apply n. rewrite H1. left; auto.
  rewrite store_update_lookup_diff; auto.
- unfold asub_cheap_update in H0; fold asub_cheap_update in H0.
  destruct (in_dec Nat.eq_dec v (x :: evar e)).
  inversion H0.
  apply option_app_elim in H0; destruct H0; destruct H0.
  inversion H1; clear H1.
  simpl.
  apply iff_split_forall; intro.
  specialize IHp with h (store_update s v x1) x0.
  apply IHp in H0. rewrite H0.
  pose proof (cheap_update_substitution_lemma_p3 s x v e x1 n).
  destruct H1. rewrite H1. rewrite H2.
  apply iff_refl.
  assert (v <> x). intro. apply n. rewrite H1. left; auto.
  rewrite store_update_lookup_diff; auto.
- unfold asub_cheap_update in H0; fold asub_cheap_update in H0.
  apply option_app_elim in H0; destruct H0; destruct H0.
  apply option_app_elim in H1; destruct H1; destruct H1.
  inversion H2; clear H2.
  clear dependent ps.
  split; intro.
  + rewrite satisfy_lor in H2. destruct H2.
    * rewrite satisfy_sand.
      rewrite satisfy_sand in H2; destruct H2 as (h1 & h2 & H2).
      destruct H2; destruct H3.
      rewrite satisfy_land in H3; destruct H3.
      rewrite satisfy_hasvaldash in H5.
      exists (heap_update h1 (s x) (e s)).
      exists h2.
      split.
      apply cheap_update_substitution_lemma_p4; auto.
      eapply Partition_dom_right1. apply H2. auto.
      split; auto.
      rewrite <- IHp1. apply H3. assumption. assumption.
    * rewrite satisfy_sand.
      rewrite satisfy_sand in H2; destruct H2 as (h1 & h2 & H2).
      destruct H2; destruct H3.
      rewrite satisfy_land in H4; destruct H4.
      rewrite satisfy_hasvaldash in H5.
      exists h1.
      exists (heap_update h2 (s x) (e s)).
      split.
      apply Partition_comm.
      apply cheap_update_substitution_lemma_p4.
      apply Partition_comm; auto.
      eapply Partition_dom_right2. apply H2. auto.
      split; auto.
      rewrite <- IHp2. apply H4. assumption. assumption.
  + rewrite satisfy_lor.
    rewrite satisfy_sand in H2; destruct H2 as (h1 & h2 & H2).
    destruct H2; destruct H3.
    apply cheap_update_substitution_lemma_p5 in H2; destruct H2.
    * destruct H2 as (h1' & H2 & H5 & H6).
      left. rewrite satisfy_sand.
      exists h1'. exists h2. split; auto.
      split; auto.
      assert (dom h1' (s x)). {
        destruct (Partition_dom_split _ _ _ _ H2 H); auto.
        exfalso; apply H6; auto. }
      rewrite satisfy_land; split.
      apply IHp1; auto.
      rewrite <- H5; auto.
      rewrite satisfy_hasvaldash; auto.
    * destruct H2 as (h2' & H2 & H5 & H6).
      right. rewrite satisfy_sand.
      exists h1. exists h2'. split; auto.
      split; auto.
      assert (dom h2' (s x)). {
        destruct (Partition_dom_split _ _ _ _ H2 H); auto.
        exfalso; apply H6; auto. }
      rewrite satisfy_land; split.
      apply IHp2; auto.
      rewrite <- H5; auto.
      rewrite satisfy_hasvaldash; auto.
- unfold asub_cheap_update in H0; fold asub_cheap_update in H0.
  destruct (sublist_part_dec Nat.eq_dec (x :: evar e) (abound p1)).
  inversion H0.
  apply option_app_elim in H0; destruct H0; destruct H0.
  inversion H1; clear H1; clear dependent ps.
  rewrite satisfy_simp.
  rewrite satisfy_simp.
  split; intro; intros.
  + pose proof (cheap_update_substitution_lemma_p6 _ _ _ _ _ H2).
    destruct H4; destruct H4.
    rewrite H4. rewrite <- IHp2; [| |apply H0].
    eapply H1. apply H5. assumption.
    eapply Partition_dom_inv_left.
    apply H5. assumption.
  + rewrite IHp2; [| |apply H0].
    specialize H1 with h' (heap_update h'' (s x) (e s)).
    apply H1; auto.
    apply cheap_update_substitution_lemma_p7; auto.
    eapply Partition_dom_right1. apply H2. assumption.
    eapply Partition_dom_inv_left. apply H2. assumption.
Qed.

(* ========================================= *)
(* CONDITIONAL HEAP CLEAR SUBSTITUTION LEMMA *)
(* ========================================= *)

Lemma cheap_clear_substitution_lemma (h: heap) (s: store) (p: assert) (x: V):
  dom h (s x) ->
  forall ps, asub_cheap_clear p x = Some ps ->
    (satisfy h s ps <-> satisfy (heap_clear h (s x)) s p).
generalize dependent s; generalize dependent h;
induction p; intros.
- inversion H0; unfold satisfy; apply iff_refl.
- simpl in H0; inversion H0; clear H0 H2.
  rewrite satisfy_land.
  repeat rewrite satisfy_hasval.
  rewrite satisfy_lnot_equals.
  simpl. split; intro.
  + destruct H0.
    rewrite heap_clear_spec2; auto.
  + destruct (Z.eq_dec (s x) (e s)).
    rewrite e1 in H0. rewrite heap_clear_spec1 in H0. inversion H0.
    split; auto.
    rewrite heap_clear_spec2 in H0; auto.
- unfold asub_cheap_clear in H0; fold asub_cheap_clear in H0.
  apply option_app_elim in H0; destruct H0; destruct H0.
  apply option_app_elim in H1; destruct H1; destruct H1.
  inversion H2. clear dependent ps.
  simpl; apply iff_split_and.
  apply IHp1; assumption.
  apply IHp2; assumption.
- unfold asub_cheap_clear in H0; fold asub_cheap_clear in H0.
  apply option_app_elim in H0; destruct H0; destruct H0.
  apply option_app_elim in H1; destruct H1; destruct H1.
  inversion H2. clear dependent ps.
  simpl; apply iff_split_or.
  apply IHp1; assumption.
  apply IHp2; assumption.
- unfold asub_cheap_clear in H0; fold asub_cheap_clear in H0.
  apply option_app_elim in H0; destruct H0; destruct H0.
  apply option_app_elim in H1; destruct H1; destruct H1.
  apply option_app_elim in H2; destruct H2; destruct H2.
  apply option_app_elim in H3; destruct H3; destruct H3.
  inversion H4. clear dependent ps.
  rewrite satisfy_land.
  remember (fresh (x :: aoccur p1 ++ aoccur p2)) as y.
  split; intro.
  + simpl; intros.
    destruct (dom_dec h' (s x)).
    * rewrite dom_spec in H. remember (h (s x)); destruct o; [clear H|exfalso;apply H;auto].
      rewrite dom_spec in H7. remember (h' (s x)); destruct o; [clear H7|exfalso;apply H7;auto].
      assert (satisfy (heap_update h' (s x) z) (store_update s y z0) p1). { admit. }
      destruct H4.
      rewrite satisfy_lforall in H7.
      specialize H7 with z0.
      rewrite satisfy_limp in H7.
      pose proof (Extends_heap_clear h (heap_update h' (s x) z) (s x)).
      apply Extends_heap_clear_update with (v := z) in H5.
      

      rewrite <- cheap_update_substitution_lemma in H; [| |apply H2].
      
      specialize 

      (* TODO *)
    * 

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
      pose proof (Partition_intro1 h (heap_clear h' (s x))); destruct H8.
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
      pose proof (Partition_intro1 h h'). destruct H6. {
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
      pose proof (Partition_intro1 (heap_clear h (s x)) h'). destruct H6. {
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
Admitted.

(* ========================== *)
(* SOUNDNESS CONSEQUENCE RULE *)
(* ========================== *)

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
specialize H with h.
pose proof (Extends_refl h).
apply H in H3; clear H; auto.
apply H1 in H3; clear H1. destruct H3.
split; auto.
intros.
specialize H0 with h' s'.
rewrite satisfy_limp in H0.
specialize H0 with h'.
pose proof (Extends_refl h').
apply H0 in H4; auto.
Qed.

(* ============================================ *)
(* SOUNDNESS AND COMPLETENESS OF                *)
(* WEAKEST PRECONDITION AXIOMATIZATION (WP-ISL) *)
(* ============================================ *)

Corollary WPISL_soundness_basic (p: assert) (x: V) (e: expr):
  forall ps, asub p x e = Some ps ->
    strong_partial_correct (mkhoare ps (basic x e) p).
intros. intro. intros. split.
intro. inversion H1. intros. inversion H1. rewrite <- H7.
rewrite <- store_substitution_lemma. apply H0. assumption.
Qed.

Corollary WPISL_soundness_lookup (p: assert) (x y: V) (e: expr):
  ~ In y (x :: aoccur p ++ evar e) ->
    forall ps, asub p x y = Some ps ->
      strong_partial_correct (mkhoare (lexists y (land (hasval e y) ps)) (lookup x e) p).
intros. intro. intros.
split.
- intro. inversion H2.
  rewrite satisfy_lexists in H1. destruct H1 as (z & H1).
  rewrite satisfy_land in H1; destruct H1.
  rewrite satisfy_hasval in H1.
  simpl in H1. rewrite store_update_lookup_same in H1.
  rewrite econd with (t := s) in H1. rewrite H1 in H4. inversion H4.
  intro. intro. destruct (Nat.eq_dec x1 y).
  exfalso. rewrite e1 in H9. apply H. right. apply in_or_app. auto.
  rewrite store_update_lookup_diff; auto.
- intros. inversion H2. rewrite <- H8.
  rewrite satisfy_lexists in H1.
  destruct H1 as (z & H1).
  rewrite satisfy_land in H1; destruct H1.
  rewrite store_substitution_lemma in H10; [|apply H0].
  simpl in H10. rewrite store_update_lookup_same in H10.
  rewrite satisfy_hasval in H1. simpl in H1.
  rewrite store_update_lookup_same in H1.
  rewrite <- H8 in H4.
  assert (e s = e (store_update s y z)). {
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

Corollary WPISL_soundness_mutation (p: assert) (x: V) (e: expr):
  forall ps, asub_cheap_update p x e = Some ps ->
    strong_partial_correct (mkhoare (land (hasvaldash x) ps) (mutation x e) p).
intros. intro. intros.
rewrite satisfy_land in H0; destruct H0.
rewrite satisfy_hasvaldash in H0.
split.
- intro.
  inversion H2. apply H4. assumption.
- intros. inversion H2.
  rewrite <- H9.
  rewrite <- cheap_update_substitution_lemma.
  apply H1. assumption. assumption.
Qed.

Corollary WPISL_soundness_new (p: assert) (x: V) (e: expr):
  ~ In x (evar e) ->
  forall ps, asub_cheap_update p x e = Some ps ->
    strong_partial_correct (mkhoare (lforall x (lor (hasvaldash x) (limp (hasvaldash x) ps))) (new x e) p).
intros. intro. intros.
rewrite satisfy_lforall in H1.
split. intro. inversion H2.
intros. inversion H2.
specialize H1 with n.
rewrite satisfy_lor in H1.
destruct H1.
rewrite satisfy_hasvaldash in H1.
simpl in H1. rewrite store_update_lookup_same in H1.
exfalso; apply H4; assumption.
assert (e s = e (store_update s x n)). {
  apply econd. intro. intros. destruct (Nat.eq_dec x1 x).
  rewrite e1 in H10. exfalso. apply H. auto.
  rewrite store_update_lookup_diff; auto. }
rewrite satisfy_limp in H1.
specialize H1 with h'.
pose proof (Extends_heap_update h n (e s) H4).
rewrite H8 in H11.
apply H1 in H11; clear H1.
rewrite cheap_update_substitution_lemma in H11; [| |apply H0].
rewrite store_update_lookup_same in H11.
rewrite <- H10 in H11.
rewrite <- H8 in H11.
rewrite heap_update_collapse in H11.
assumption.
rewrite store_update_lookup_same.
rewrite <- H8.
apply heap_update_dom1.
rewrite satisfy_hasvaldash; simpl.
rewrite store_update_lookup_same.
rewrite <- H8.
apply heap_update_dom1.
Qed.

Corollary WPISL_soundness_dispose (p: assert) (x: V):
  forall ps, asub_cheap_clear p x = Some ps ->
    strong_partial_correct (mkhoare (land (hasvaldash x) ps) (dispose x) p).
intros. intro. intros.
rewrite satisfy_land in H0; destruct H0.
rewrite satisfy_hasvaldash in H0.
split.
- intro. inversion H2. apply H5. assumption.
- intros. inversion H2.
  rewrite <- H8.
  rewrite <- cheap_clear_substitution_lemma. apply H1.
  rewrite H8. assumption.
  assumption.
Qed.

Theorem WPISL_soundness (Gamma: assert -> Prop) (O: forall p, Gamma p -> validity p):
  forall pSq, inhabited (WPISL Gamma pSq) -> strong_partial_correct pSq.
intros. destruct H. induction H.
- apply WPISL_soundness_basic; assumption.
- apply WPISL_soundness_lookup; assumption.
- apply WPISL_soundness_mutation; assumption.
- apply WPISL_soundness_new; assumption.
- apply WPISL_soundness_dispose; assumption.
- apply O in g. apply O in g0.
  eapply soundness_conseq.
  apply g. apply g0. assumption.
Qed.

Corollary WPISL_weakest_basic (q p: assert) (x: V) (e: expr):
  strong_partial_correct (mkhoare p (basic x e) q) ->
  forall qs, asub q x e = Some qs ->
  validity (limp p qs).
intros. intro. intros.
rewrite satisfy_limp. intros.
unfold strong_partial_correct in H.
specialize H with h' s.
apply H in H2; clear H. destruct H2.
specialize H2 with h' (store_update s x (e s)).
pose proof (H2 (step_basic x e h' s)); clear H2.
rewrite store_substitution_lemma. apply H3. assumption.
Qed.

Corollary WPISL_weakest_lookup (q p: assert) (x: V) (e: expr):
  strong_partial_correct (mkhoare p (lookup x e) q) ->
  forall y, ~In y (x :: aoccur q ++ evar e) ->
  forall qs, asub q x y = Some qs ->
  validity (limp p (lexists y (land (hasval e y) qs))).
intros. intro. intros.
rewrite satisfy_limp; intros.
unfold strong_partial_correct in H; specialize H with h' s.
apply H in H3; clear H; destruct H3.
remember (h' (e s)). destruct o.
rewrite satisfy_lexists. exists z.
rewrite satisfy_land. split.
rewrite satisfy_hasval.
assert (e s = e (store_update s y z)). {
  apply econd. intro. intro. destruct (Nat.eq_dec x0 y).
  rewrite e0 in H4. exfalso. apply H0. right. apply in_or_app. auto.
  rewrite store_update_lookup_diff; auto. }
rewrite <- H4. simpl. rewrite store_update_lookup_same. auto.
specialize H3 with h' (store_update s x z).
symmetry in Heqo.
pose proof (H3 (step_lookup x e h' s z Heqo)); clear H3.
rewrite (store_substitution_lemma h' (store_update s y z) q x y qs H1).
simpl. rewrite store_update_lookup_same.
rewrite store_update_swap.
rewrite acond. apply H4.
intro. intro. destruct (Nat.eq_dec x0 y).
rewrite e0 in H3. exfalso. apply H0. right. apply in_or_app. left. apply in_or_app; auto.
rewrite store_update_lookup_diff; auto.
intro. rewrite H3 in H0. apply H0. left; auto.
exfalso. apply H. apply step_lookup_fail. auto.
Qed.

Corollary WPISL_weakest_mutation (q p: assert) (x: V) (e: expr):
  strong_partial_correct (mkhoare p (mutation x e) q) ->
  forall qs, asub_cheap_update q x e = Some qs ->
  validity (limp p (land (hasvaldash x) qs)).
intros. intro. intros.
rewrite satisfy_limp; intros.
unfold strong_partial_correct in H.
specialize H with h' s.
apply H in H2; clear H; destruct H2.
assert (dom h' (s x)).
destruct (dom_dec h' (s x)); auto.
exfalso. apply H. apply step_mutation_fail; auto.
rewrite satisfy_land; split.
rewrite satisfy_hasvaldash; auto.
rewrite cheap_update_substitution_lemma; [|apply H3|apply H0].
apply H2. apply step_mutation; auto.
Qed.

Corollary WPISL_weakest_allocation (q p: assert) (x: V) (e: expr):
  strong_partial_correct (mkhoare p (new x e) q) ->
  ~ In x (evar e) ->
  forall qs, asub_cheap_update q x e = Some qs ->
  validity (limp p (lforall x (lor (hasvaldash x) (limp (hasvaldash x) qs)))).
intros. intro. intros.
rewrite satisfy_limp; intros.
rewrite satisfy_lforall; intro.
rewrite satisfy_lor.
destruct (dom_dec h' (store_update s x v x)); auto.
left. rewrite satisfy_hasvaldash; auto.
right.
rewrite satisfy_limp; intros.
rewrite satisfy_hasvaldash in H6; simpl in H6.
rewrite store_update_lookup_same in H4, H6.
unfold strong_partial_correct in H.
specialize H with h' s.
apply H in H3; clear H; destruct H3.
eapply cheap_update_substitution_lemma; [|apply H1|].
rewrite store_update_lookup_same; auto.
rewrite store_update_lookup_same.
specialize H3 with (heap_update h' v (e s)) (store_update s x v).
pose proof (step_new x e h' s v H4).
apply H3 in H7; clear H3.
assert (e s = e (store_update s x v)). {
  apply econd. intro. intros. destruct (Nat.eq_dec x0 x).
  rewrite e0 in H3. exfalso. apply H0. auto.
  rewrite store_update_lookup_diff; auto. }
rewrite <- H3.
eapply satisfy_monotonic in H7.
apply H7.
apply Extends_lift_heap_update; auto.
Qed.

Corollary WPISL_weakest_dispose (q p: assert) (x: V):
  strong_partial_correct (mkhoare p (dispose x) q) ->
  forall qs, asub_cheap_clear q x = Some qs ->
  validity (limp p (land (hasvaldash x) qs)).
intros. intro. intros.
rewrite satisfy_limp; intros.
rewrite satisfy_land.
unfold strong_partial_correct in H.
specialize H with h' s.
apply H in H2; clear H; destruct H2.
assert (dom h' (s x)).
destruct (dom_dec h' (s x)); auto.
exfalso. apply H. apply step_dispose_fail; auto.
split.
rewrite satisfy_hasvaldash; auto.
rewrite cheap_clear_substitution_lemma; [| |apply H0]; auto.
apply H2. apply step_dispose; auto.
Qed.

Theorem WPISL_completeness (Gamma: assert -> Prop) (O: forall p, validity p -> Gamma p):
  forall pSq, restrict_post pSq -> strong_partial_correct pSq -> inhabited (WPISL Gamma pSq).
intros. destruct pSq as (p, S, q); destruct S; destruct a; unfold restrict_post in H.
- rewrite asub_defined with (x := v) in H.
  destruct H. constructor.
  apply wpi_conseq with (p := x) (q := q).
  apply O. eapply WPISL_weakest_basic. apply H0. auto.
  apply wpi_basic; auto.
  apply O. intro. intro. rewrite satisfy_limp. tauto.
- remember (fresh (v :: aoccur q ++ evar e)) as y.
  pose proof (asub_defined q v y).
  assert (forall x : V, In x (evar y) -> ~ In x (abound q)).
  intros. simpl in H2. destruct H2. rewrite <- H2. rewrite Heqy.
  apply fresh_notInGeneral. intros. right. apply in_or_app. left. apply in_or_app. auto. inversion H2.
  apply H1 in H2; clear H1; destruct H2.
  constructor.
  apply wpi_conseq with (p := (lexists y (land (hasval e y) x))) (q := q).
  apply O. eapply WPISL_weakest_lookup. apply H0.
  rewrite Heqy. apply fresh_notIn. auto.
  apply wpi_lookup; auto.
  rewrite Heqy. apply fresh_notIn.
  apply O. intro. intro. rewrite satisfy_limp. tauto.
- rewrite asub_cheap_update_defined in H. destruct H.
  constructor.
  apply wpi_conseq with (p := land (hasvaldash v) x) (q := q).
  apply O. eapply WPISL_weakest_mutation. apply H0. auto.
  apply wpi_mutation. auto.
  apply O. intro. intro. rewrite satisfy_limp. tauto.
- destruct H. rewrite asub_cheap_update_defined in H1. destruct H1.
  constructor.
  apply wpi_conseq with (p := lforall v (lor (hasvaldash v) (limp (hasvaldash v) x))) (q := q).
  apply O. eapply WPISL_weakest_allocation. apply H0. auto. auto.
  apply wpi_new. auto. auto.
  apply O. intro. intro. rewrite satisfy_limp. tauto.
- rewrite asub_cheap_clear_defined in H. destruct H.
  constructor.
  apply wpi_conseq with (p := land (hasvaldash v) x) (q := q).
  apply O. eapply WPISL_weakest_dispose. apply H0. auto.
  apply wpi_dispose. auto.
  apply O. intro. intro. rewrite satisfy_limp. tauto.
Qed.

Corollary WPISL_soundness_completeness:
  forall pSq, restrict_post pSq -> inhabited (WPISL validity pSq) <-> strong_partial_correct pSq.
intros. split.
apply WPISL_soundness; auto.
apply WPISL_completeness; auto.
Qed.

(* =============================================== *)
(* SOUNDNESS AND COMPLETENESS OF                   *)
(* STRONGEST POSTCONDITION AXIOMATIZATION (SP-ISL) *)
(* =============================================== *)

Corollary SPISL_soundness_basic (p: assert) (x y: V) (e: expr):
  ~ In y (x :: aoccur p ++ evar e) ->
  forall ps, asub p x y = Some ps ->
  strong_partial_correct (mkhoare p (basic x e) (lexists y (land ps (equals (esub e x y) x)))).
Admitted.

Corollary SPISL_soundness_lookup (p: assert) (x y: V) (e: expr):
  ~ In y (x :: aoccur p ++ evar e) ->
  forall ps, asub p x y = Some ps ->
  strong_partial_correct (mkhoare (land p (hasvaldash e)) (lookup x e) (lexists y (land ps (hasval (esub e x y) x)))).
Admitted.

Corollary SPISL_soundness_mutation (p: assert) (x y: V) (e: expr):
  ~ In y (x :: aoccur p ++ evar e) ->
  forall ps, asub_cheap_update p x y = Some ps ->
  strong_partial_correct (mkhoare (land p (hasvaldash x)) (mutation x e) (land (lexists y ps) (hasval x e))).
Admitted.

Corollary SPISL_soundness_new (p: assert) (x y: V) (e: expr):
  ~ In x (evar e) ->
  ~ In y (x :: aoccur p ++ evar e) ->
  forall ps, asub p x y = Some ps ->
  forall pss, asub_cheap_clear (lexists y ps) x = Some pss ->
  strong_partial_correct (mkhoare p (new x e) (land pss (hasval x e))).
Admitted.

Corollary SPISL_soundness_dispose (p: assert) (x y: V):
  ~ In y (x :: aoccur p) ->
  forall ps, asub_cheap_update p x y = Some ps ->
  strong_partial_correct (mkhoare (land p (hasvaldash x)) (dispose x) (limp (hasvaldash x) (lexists y ps))).
Admitted.

Theorem SPISL_soundness (Gamma: assert -> Prop) (O: forall p, Gamma p -> validity p):
  forall pSq, inhabited (SPISL Gamma pSq) -> strong_partial_correct pSq.
intros. destruct H. induction H.
- apply SPISL_soundness_basic; assumption.
- apply SPISL_soundness_lookup; assumption.
- apply SPISL_soundness_mutation; assumption.
- eapply SPISL_soundness_new. apply n. apply n0. apply e0. assumption.
- apply SPISL_soundness_dispose; assumption.
- apply O in g. apply O in g0.
  eapply soundness_conseq.
  apply g. apply g0. assumption.
Qed.

Corollary SPISL_strongest_basic (p q: assert) (x y: V) (e: expr):
  strong_partial_correct (mkhoare p (basic x e) q) ->
  ~ In y (x :: aoccur p ++ evar e ++ aoccur q) ->
  forall ps, asub p x y = Some ps ->
  validity (limp (lexists y (land ps (equals (esub e x y) x))) q).
Admitted.

Corollary SPISL_strongest_lookup (p q: assert) (x y: V) (e: expr):
  strong_partial_correct (mkhoare p (lookup x e) q) ->
  ~ In y (x :: aoccur p ++ evar e ++ aoccur q) ->
  forall ps, asub p x y = Some ps ->
  validity (limp (lexists y (land ps (hasval (esub e x y) x))) q).
Admitted.

Corollary SPISL_strongest_mutation (p q: assert) (x y: V) (e: expr):
  strong_partial_correct (mkhoare p (mutation x e) q) ->
  ~In y (x :: aoccur p ++ evar e ++ aoccur q) ->
  forall ps, asub_cheap_update p x y = Some ps ->
  validity (limp (land (lexists y ps) (hasval x e)) q).
Admitted.

Corollary SPISL_strongest_new (p q: assert) (x y: V) (e: expr):
  ~ In x (evar e) ->
  strong_partial_correct (mkhoare p (new x e) q) ->
  ~ In y (x :: aoccur p ++ evar e ++ aoccur q) ->
  forall ps, asub p x y = Some ps ->
  forall pss, asub_cheap_clear (lexists y ps) x = Some pss ->
  validity (limp (land pss (hasval x e)) q).
Admitted.

Corollary SPISL_strongest_dispose (p q: assert) (x y: V):
  strong_partial_correct (mkhoare p (dispose x) q) ->
  ~ In y (x :: aoccur p ++ aoccur q) ->
  forall ps, asub_cheap_update p x y = Some ps ->
  validity (limp (limp (hasvaldash x) (lexists y ps)) q).
Admitted.

Theorem SPISL_completeness (Gamma: assert -> Prop) (O: forall p, validity p -> Gamma p):
  forall pSq, restrict_pre pSq -> strong_partial_correct pSq -> inhabited (SPISL Gamma pSq).
intros. destruct pSq as (p, S, q); destruct S; destruct a; unfold restrict_pre in H.
- remember (fresh (v :: aoccur p ++ evar e ++ aoccur q)) as y.
  pose proof (asub_defined p v y).
  assert (forall x, In x (evar y) -> ~In x (abound p)). intros.
    simpl in H2. destruct H2; auto. rewrite <- H2. rewrite Heqy.
    apply fresh_notInGeneral. intros. right. apply in_or_app. left. apply in_or_app; auto.
  apply H1 in H2; clear H1; destruct H2.
  constructor.
  apply spi_conseq with (p := p) (q := (lexists y (land x (equals (esub e v y) v)))).
  apply O. intro. intro. rewrite satisfy_limp; tauto.
  apply spi_basic. rewrite Heqy. apply fresh_notInGeneral. intros.
    inversion H2. left; auto. apply in_app_or in H3; destruct H3.
    right. apply in_or_app; auto. right. apply in_or_app.
    right. apply in_or_app; auto. assumption.
  apply O. eapply SPISL_strongest_basic. apply H0.
  rewrite Heqy. apply fresh_notIn. assumption.
- remember (fresh (v :: aoccur p ++ evar e ++ aoccur q)) as y.
  pose proof (asub_defined p v y).
  assert (forall x, In x (evar y) -> ~In x (abound p)). intros.
    simpl in H2. destruct H2; auto. rewrite <- H2. rewrite Heqy.
    apply fresh_notInGeneral. intros. right. apply in_or_app. left. apply in_or_app; auto.
  apply H1 in H2; clear H1; destruct H2.
  constructor.
  apply spi_conseq with (p := (land p (hasvaldash e))) (q := (lexists y (land x (hasval (esub e v y) v)))).
  apply O. intro. intros. rewrite satisfy_limp. intro. unfold strong_partial_correct in H0.
    rewrite satisfy_land. split; auto. rewrite satisfy_hasvaldash.
    apply H0 in H3. destruct H3. destruct (dom_dec h' (e s)); auto. exfalso.
    apply H3. apply step_lookup_fail. rewrite dom_spec in H5. destruct (h' (e s)); auto.
    exfalso. apply H5. intro. inversion H6.
  apply spi_lookup. rewrite Heqy. apply fresh_notInGeneral. intros.
    inversion H2. left; auto. right. apply in_app_or in H3; destruct H3.
    apply in_or_app; auto. apply in_or_app; right. apply in_or_app; auto.
    assumption.
  apply O. eapply SPISL_strongest_lookup. apply H0.
  rewrite Heqy. apply fresh_notIn. assumption.
- remember (fresh (v :: aoccur p ++ evar e ++ aoccur q)) as y.
  pose proof (asub_cheap_update_defined p v y).
  assert (forall y0 : V, In y0 (v :: evar y) -> ~ In y0 (abound p)). intros.
    simpl in H2. destruct H2. rewrite <- H2. auto. destruct H2. rewrite <- H2.
    rewrite Heqy. apply fresh_notInGeneral. intros. right. apply in_or_app. left.
    apply in_or_app; auto. inversion H2.
  apply H1 in H2; clear H1; destruct H2.
  constructor.
  apply spi_conseq with (p := (land p (hasvaldash v))) (q := land (lexists y x) (hasval v e)).
  apply O. intro. intro. rewrite satisfy_limp; intro.
    rewrite satisfy_land. split; auto. rewrite satisfy_hasvaldash.
    unfold strong_partial_correct in H0. apply H0 in H3. destruct H3.
    apply dom_spec. intro. apply H3. apply step_mutation_fail. intro.
    apply dom_spec in H6. simpl in H5. apply H6. auto.
  apply spi_mutation. rewrite Heqy. apply fresh_notInGeneral. intros.
    inversion H2. left; auto. right. apply in_app_or in H3; destruct H3.
    apply in_or_app; auto. apply in_or_app; right. apply in_or_app; auto. assumption.
  apply O. eapply SPISL_strongest_mutation. apply H0. rewrite Heqy.
    apply fresh_notIn. assumption.
- remember (fresh (v :: aoccur p ++ evar e ++ aoccur q)) as y.
  pose proof (asub_defined p v y).
  assert (forall x, In x (evar y) -> ~In x (abound p)). intros.
    simpl in H2. destruct H2; auto. rewrite <- H2. rewrite Heqy.
    apply fresh_notInGeneral. intros. right. apply in_or_app. left. apply in_or_app; auto.
  apply H1 in H2; clear H1; destruct H2.
  pose proof (asub_cheap_clear_defined (lexists y x) v).
  destruct H.
  assert (~In v (abound (lexists y x))). simpl. intro.
    destruct H4. rewrite <- H4 in Heqy.
    eapply fresh_notIn with (xs := y :: aoccur p ++ evar e ++ aoccur q).
    left. assumption. eapply (abound_asub _ _ _ H3 _ H1); assumption.
  apply H2 in H4; clear H2; destruct H4.
  constructor.
  apply spi_conseq with (p := p) (q := land x0 (hasval v e)).
  apply O. intro. intros. rewrite satisfy_limp; tauto.
  eapply spi_new; [ apply H | | apply H1 | ].
  rewrite Heqy. apply fresh_notInGeneral. intros. inversion H4.
    left; auto. right; apply in_or_app. apply in_app_or in H5; destruct H5; auto.
    right. apply in_or_app; auto. assumption.
  apply O. eapply SPISL_strongest_new. apply H. apply H0.
    apply fresh_notIn. rewrite <- Heqy. apply H1.
    rewrite <- Heqy. assumption.
- remember (fresh (v :: aoccur p ++ aoccur q)) as y.
  pose proof (asub_cheap_update_defined p v y).
  assert (forall y0 : V, In y0 (v :: evar y) -> ~ In y0 (abound p)). intros.
    simpl in H2. destruct H2. rewrite <- H2. auto. destruct H2. rewrite <- H2.
    rewrite Heqy. apply fresh_notInGeneral. intros. right. apply in_or_app. left.
    apply in_or_app; auto. inversion H2.
  apply H1 in H2; clear H1; destruct H2.
  constructor.
  apply spi_conseq with (p := (land p (hasvaldash v))) (q := limp (hasvaldash v) (lexists y x)).
  apply O. intro. intro. rewrite satisfy_limp; intro.
    rewrite satisfy_land. split; auto. rewrite satisfy_hasvaldash.
    unfold strong_partial_correct in H0. apply H0 in H3. destruct H3.
    apply dom_spec. intro. apply H3. apply step_dispose_fail. intro.
    apply dom_spec in H6. simpl in H5. apply H6. auto.
  apply spi_dispose. rewrite Heqy. apply fresh_notInGeneral. intros.
    inversion H2. left; auto. right. apply in_app_or in H3; destruct H3.
    apply in_or_app; left. apply in_or_app; auto. apply in_or_app; left.
    apply in_or_app; auto. assumption.
  apply O. eapply SPISL_strongest_dispose. apply H0. rewrite Heqy.
    apply fresh_notIn. assumption.
Qed.

Corollary SPISL_soundness_completeness:
  forall pSq, restrict_pre pSq -> inhabited (SPISL validity pSq) <-> strong_partial_correct pSq.
intros. split.
apply SPISL_soundness. tauto.
apply SPISL_completeness. tauto. tauto.
Qed.

Corollary result:
  forall pSq, restrict pSq -> inhabited (SPISL validity pSq) <-> inhabited (WPISL validity pSq).
intros. destruct H. split.
intro. apply SPISL_soundness_completeness in H1; auto.
apply WPISL_soundness_completeness; auto.
intro. apply WPISL_soundness_completeness in H1; auto.
apply SPISL_soundness_completeness; auto.
Qed.

End Intuitionistic.

(* To show all the used axioms in our development, we make everything concrete: *)

Module IntuitionisticIHeap := Intuitionistic IHeap.
Import IntuitionisticIHeap.
Print Assumptions WPISL_soundness_completeness.
