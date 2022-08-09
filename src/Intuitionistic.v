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

(* =================================== *)
(* COINCIDENCE CONDITION ON ASSERTIONS *)
(* =================================== *)

Proposition acond (h: heap) (p: assert):
  forall (s t: store), eq_restr s t (avar p) ->
    (satisfy h s p <-> satisfy h t p).
Admitted.

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

Lemma store_substitution_lemma (h: heap) (s: store) (p: assert) (x: V) (e: expr):
  forall ps, asub p x e = Some ps ->
    (satisfy h s ps <-> satisfy h (store_update s x (e s)) p).
Admitted.

(* ========================================== *)
(* CONDITIONAL HEAP UPDATE SUBSTITUTION LEMMA *)
(* ========================================== *)

Lemma cheap_update_substitution_lemma (h: heap) (s: store) (p: assert) (x: V) (e: expr):
  dom h (s x) ->
  forall ps, asub_cheap_update p x e = Some ps ->
    (satisfy h s ps <-> satisfy (heap_update h (s x) (e s)) s p).
Admitted.

(* ========================================= *)
(* CONDITIONAL HEAP CLEAR SUBSTITUTION LEMMA *)
(* ========================================= *)

Lemma cheap_clear_substitution_lemma (h: heap) (s: store) (p: assert) (x: V):
  dom h (s x) ->
  forall ps, asub_cheap_clear p x = Some ps ->
    (satisfy h s ps <-> satisfy (heap_clear h (s x)) s p).
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
Admitted.

Corollary WPISL_soundness_lookup (p: assert) (x y: V) (e: expr):
  ~ In y (x :: aoccur p ++ evar e) ->
    forall ps, asub p x y = Some ps ->
      strong_partial_correct (mkhoare (lexists y (land (hasval e y) ps)) (lookup x e) p).
Admitted.

Corollary WPISL_soundness_mutation (p: assert) (x: V) (e: expr):
  forall ps, asub_cheap_update p x e = Some ps ->
    strong_partial_correct (mkhoare (land (hasvaldash x) ps) (mutation x e) p).
Admitted.

Corollary WPISL_soundness_new (p: assert) (x: V) (e: expr):
  ~ In x (evar e) ->
  forall ps, asub_cheap_update p x e = Some ps ->
    strong_partial_correct (mkhoare (lforall x (lor (hasvaldash x) ps)) (new x e) p).
Admitted.

Corollary WPISL_soundness_dispose (p: assert) (x: V):
  forall ps, asub_cheap_clear p x = Some ps ->
    strong_partial_correct (mkhoare (land (hasvaldash x) ps) (dispose x) p).
Admitted.

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
Admitted.

Corollary WPISL_weakest_lookup (q p: assert) (x: V) (e: expr):
  strong_partial_correct (mkhoare p (lookup x e) q) ->
  forall y, ~In y (x :: aoccur q ++ evar e) ->
  forall qs, asub q x y = Some qs ->
  validity (limp p (lexists y (land (hasval e y) qs))).
Admitted.

Corollary WPISL_weakest_mutation (q p: assert) (x: V) (e: expr):
  strong_partial_correct (mkhoare p (mutation x e) q) ->
  forall qs, asub_cheap_update q x e = Some qs ->
  validity (limp p (land (hasvaldash x) qs)).
Admitted.

Corollary WPISL_weakest_allocation (q p: assert) (x: V) (e: expr):
  strong_partial_correct (mkhoare p (new x e) q) ->
  ~ In x (evar e) ->
  forall qs, asub_cheap_update q x e = Some qs ->
  validity (limp p (lforall x (lor (hasvaldash x) qs))).
Admitted.

Corollary WPISL_weakest_dispose (q p: assert) (x: V):
  strong_partial_correct (mkhoare p (dispose x) q) ->
  forall qs, asub_cheap_clear q x = Some qs ->
  validity (limp p (land (hasvaldash x) qs)).
Admitted.

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
  apply wpi_conseq with (p := lforall v (lor (hasvaldash v) x)) (q := q).
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

End Intuitionistic.


