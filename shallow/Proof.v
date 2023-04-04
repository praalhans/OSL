Require Export ShallowSeparationLogic.Language.

(* ========================== *)
(* AXIOMATIC CHARACTERIZATION *)
(* ========================== *)

(* Conjunction and program modality *)
Lemma cwlp_cland_distr (S1: program) (p q: cassert):
  valid (clequiv (cwlp S1 (cland p q)) (cland (cwlp S1 p) (cwlp S1 q))).
unfold valid; intros.
simpl. split; intros.
- destruct H.
  split; split; auto.
  all: intros; apply H0; auto.
- destruct H; destruct H; destruct H0.
  split. auto.
  intros. split.
  apply H1. auto.
  apply H2. auto.
Qed.

(* Complex programs *)
Lemma cwlp_diverge (p: cassert):
  valid (clequiv (cwlp diverge p) cltrue).
unfold valid; intros.
simpl. split; intros; auto.
split; intro; intros; inversion H0.
Qed.

Lemma cwlp_skip (p: cassert):
  valid (clequiv (cwlp skip p) p).
unfold valid; intros.
simpl. split; intros.
- destruct H. apply H0.
  apply step_skip.
- split; intro; intros; inversion H0.
  rewrite <- H4. rewrite <- H5.
  auto.
Qed.

Lemma cwlp_comp (S1 S2: program) (p: cassert):
  valid (clequiv (cwlp (comp S1 S2) p) (cwlp S1 (cwlp S2 p))).
unfold valid; intros.
simpl. split; intros.
- destruct H. split.
  + intro. apply H.
    apply step_comp_fail1. auto.
  + intros. split.
    intro. apply H.
    eapply step_comp_fail2. apply H1. auto.
    intros. apply H0.
    eapply step_comp. apply H1. apply H2.
- destruct H. split.
  + intro. inversion H1.
    apply H. auto.
    specialize H0 with h' s'.
    apply H0 in H5. destruct H5.
    apply H5. auto.
  + intros. inversion H1.
    edestruct H0. apply H5.
    apply H11. apply H9.
Qed.

Lemma cwlp_ite (g: guard) (S1 S2: program) (p: cassert):
  valid (clequiv (cwlp (ite g S1 S2) p) (cland (climp (ctest g) (cwlp S1 p)) (climp (clnot (ctest g)) (cwlp S2 p)))).
unfold valid; intros.
simpl. split; intros.
- destruct H. split; intros.
  + split. intro. apply H.
    apply step_ite_true; auto.
    intros. apply H0.
    apply step_ite_true; auto.
  + split. intro. apply H.
    apply step_ite_false; auto.
    destruct (g s); auto. symmetry; apply H1; auto.
    intros. apply H0.
    apply step_ite_false; auto.
    destruct (g s); auto. symmetry; apply H1; auto.
- destruct H.
  split.
  + intro. inversion H1.
    destruct H; auto.
    destruct H0; auto. intro.
    destruct (g s). inversion H8. inversion H0.
  + intros. inversion H1.
    apply H in H8. destruct H8. apply H10. auto.
    destruct H0. intro. destruct (g s). inversion H8. inversion H0.
    apply H10. auto.
Qed.

Lemma cwlp_while (g: guard) (S1: program) (p q: cassert):
  valid (clequiv (cwlp (while g S1) p) (cwlp (ite g (comp S1 (while g S1)) skip) p)).
unfold valid; intros.
simpl. split; intros.
- destruct H.
  split. intro.
  rewrite while_unfold in H.
  apply H; auto.
  intros. apply H0.
  rewrite while_unfold; auto.
- destruct H. split.
  intro.
  rewrite <- while_unfold in H.
  apply H; auto.
  intros. apply H0.
  rewrite <- while_unfold; auto.
Qed.

(* Simple assignment, E1-4 *)
Lemma cwlp_basic_ctest (x: V) (e: expr) (g: guard):
  valid (clequiv (cwlp (basic x e) (ctest g)) (ctest (gsub g x e))).
unfold valid; intros.
simpl. split; intros.
- destruct H.
  specialize H0 with h (store_update s x (e s)).
  apply H0.
  apply step_basic.
- split; intro; intros; inversion H0; auto.
Qed.

Lemma cwlp_basic_chasval (x: V) (e: expr) (e1 e2: expr):
  valid (clequiv (cwlp (basic x e) (chasval e1 e2)) (chasval (esub e1 x e) (esub e2 x e))).
unfold valid; intros.
simpl. split; intros.
- destruct H.
  specialize H0 with h (store_update s x (e s)).
  apply H0.
  apply step_basic.
- split. intro. inversion H0.
  intros. inversion H0.
  rewrite H6 in H. auto.
Qed.

Lemma cwlp_basic_climp (x: V) (e: expr) (p q: cassert):
  valid (clequiv (cwlp (basic x e) (climp p q)) (climp (cwlp (basic x e) p) (cwlp (basic x e) q))).
unfold valid; intros.
simpl. split; intros.
- destruct H; destruct H0. split; auto.
- split. intro. inversion H0.
  intros. destruct H.
  split. intro. inversion H.
  intros. inversion H.
  inversion H0. rewrite <- H7.
  rewrite H13. rewrite H14. auto.
  apply H2. auto.
Qed.

Lemma cwlp_basic_clforall (x: V) (e: expr) (y: V) (p: cassert):
  ~In y (pvar (basic x e)) ->
  valid (clequiv (cwlp (basic x e) (clforall y p)) (clforall y (cwlp (basic x e) p))).
intros. unfold valid; intros.
simpl. split; intros.
- split. intro. inversion H1.
  intros. destruct H0.
  pose proof (bigstep_cond (basic x e) _ _ H1 (pvar (basic x e))).
  destruct H3 with (h := h) (s := store_update s y v) (t := s); auto.
  intro. intro. unfold store_update.
    destruct (Nat.eq_dec y x0). exfalso. apply H. rewrite e0; auto. auto.
  destruct H4 with (h' := h') (s' := s'); auto. destruct H6.
  inversion H7.
  rewrite <- H13 in H7.
  rewrite <- H14 in H7.
  eapply H2 in H7.
  inversion H1.
  rewrite <- H19.
  rewrite store_update_swap.
  rewrite econd with (t := s).
  apply H7.
  intro; intros. unfold store_update.
    destruct (Nat.eq_dec y x3). exfalso. apply H. rewrite e2. simpl. auto. auto.
  intro. apply H. rewrite H8. simpl. auto.
- split. intro. inversion H1.
  intros. destruct H0 with (v := v).
  specialize H3 with h (store_update (store_update s y v) x (e (store_update s y v))).
  inversion H1.
  rewrite store_update_swap.
  rewrite econd with (t := (store_update s y v)).
  rewrite <- H9. apply H3.
  apply step_basic.
  intro. intro. unfold store_update.
    destruct (Nat.eq_dec y x1). exfalso. apply H. rewrite e1. simpl. auto. auto.
  intro. apply H. rewrite H4. simpl. auto.
Qed.

Lemma cwlp_basic_csand (x: V) (e: expr) (p q: cassert):
  valid (clequiv (cwlp (basic x e) (csand p q)) (csand (cwlp (basic x e) p) (cwlp (basic x e) q))).
unfold valid; intros.
simpl. split; intros.
- destruct H.
  intro. destruct H0 with (h' := h) (s' := store_update s x (e s)).
  apply step_basic.
  intros. intro. destruct H2.
  destruct H1 with (h1 := h1) (h2 := h2).
  split; auto.
  destruct H3.
  split; split.
  intro. inversion H5.
  intros. inversion H5.
  rewrite <- H11. auto.
  intro. inversion H5.
  intros. inversion H5.
  rewrite <- H11. auto.
- split. intro. inversion H0.
  intros. intro.
  apply H. intros. intro. destruct H2. destruct H3.
  destruct H3. destruct H4.
  destruct H1 with (h1 := h1) (h2 := h2).
  split. inversion H0. rewrite <- H12. auto.
  split. apply H5. inversion H0. apply step_basic.
  apply H6. inversion H0. apply step_basic.
Qed.

Lemma cwlp_basic_csimp (x: V) (e: expr) (p q: cassert):
  valid (clequiv (cwlp (basic x e) (csimp p q)) (csimp (cwlp (basic x e) p) (cwlp (basic x e) q))).
unfold valid; intros.
simpl. split; intros.
- destruct H.
  specialize H2 with h (store_update s x (e s)) h'' h'.
  pose proof (step_basic x e h s).
  apply H2 in H3; auto.
  split. intro. inversion H4.
  intros. inversion H4. rewrite <- H10. auto.
  destruct H1.
  specialize H4 with h' (store_update s x (e s)).
  pose proof (step_basic x e h' s).
  apply H4 in H5. auto.
- split. intro. inversion H0.
  intros. inversion H0.
  rewrite <- H8 in *. clear dependent h'.
  rewrite <- H9 in *. clear dependent s'.
  clear dependent x0. clear dependent e0.
  clear dependent h0. clear dependent s0.
  rename h'0 into h'.
  specialize H with h'' h'.
  apply H in H1; clear H.
  destruct H1. apply H1.
  apply step_basic.
  split. intro. inversion H.
  intros. inversion H. rewrite <- H8 in *.
  auto.
Qed.

(* E1-3 for heap update, E9-12 *)
Lemma csub_heap_update_ctest (x: V) (e: expr) (g: guard):
  valid (clequiv (csub_heap_update (ctest g) x e) (ctest g)).
unfold valid; intros.
simpl. split; auto.
Qed.

Proposition double_neg_option_Z (o1 o2: option Z):
  (~~o1 = o2) -> o1 = o2.
intro. destruct o1; destruct o2.
+ destruct (Z.eq_dec z z0).
  rewrite e. auto.
  exfalso. apply H. intro.
  apply n. inversion H0. auto.
+ exfalso. apply H. intro. inversion H0.
+ exfalso. apply H. intro. inversion H0.
+ auto.
Qed.

Lemma csub_heap_update_chasval (x: V) (e: expr) (e1 e2: expr):
  valid (clequiv (csub_heap_update (chasval e1 e2) x e)
    (clor (cland (ctest (equals x e1)) (ctest (equals e2 e))) (cland (clnot (ctest (equals x e1))) (chasval e1 e2)))).
unfold valid; intros.
simpl. split.
- intros. intro.
  destruct H0.
  unfold heap_update in H.
  destruct (Z.eq_dec (s x) (e1 s)).
  + apply H0. split; auto.
    destruct (Z.eq_dec (e2 s) (e s)); auto.
    inversion H. exfalso. apply n. auto.
  + apply H1. split; auto.
- intro.
  unfold heap_update.
  destruct (Z.eq_dec (s x) (e1 s)).
  + destruct (Z.eq_dec (e2 s) (e s)).
    rewrite e3; auto.
    exfalso. apply H. split.
    intro. destruct H0. inversion H1.
    intro. destruct H0.
    assert (false = true). apply H0; auto.
    inversion H2.
  + apply double_neg_option_Z. intro.
    apply H. split; intro.
    destruct H1. inversion H1.
    destruct H1. apply H0. apply H2.
Qed.

Lemma csub_heap_update_climp (x: V) (e: expr) (p q: cassert):
  valid (clequiv (csub_heap_update (climp p q) x e) (climp (csub_heap_update p x e) (csub_heap_update q x e))).
unfold valid; intros.
simpl.
assert ((p (heap_update h (s x) (e s), s) -> q (heap_update h (s x) (e s), s)) -> p (heap_update h (s x) (e s), s) -> q (heap_update h (s x) (e s), s)).
intros.
apply H. auto.
split; auto.
Qed.

Lemma csub_heap_update_clforall (x: V) (e: expr) (y: V) (p: cassert):
  ~In y (x :: evar e) ->
  valid (clequiv (csub_heap_update (clforall y p) x e) (clforall y (csub_heap_update p x e))).
unfold valid; intros.
simpl. split; intros.
- rewrite store_update_lookup_diff.
  rewrite econd with (t := s).
  apply H0.
  intro. intro. unfold store_update.
  destruct (Nat.eq_dec y x0).
    exfalso. apply H. rewrite e0. right. auto.
    auto.
  intro. apply H. rewrite H1. left. auto.
- specialize H0 with v.
  rewrite store_update_lookup_diff in H0.
  rewrite econd with (t := s) in H0.
  auto.
  intro. intro. unfold store_update.
  destruct (Nat.eq_dec y x0).
    exfalso. apply H. rewrite e0. right. auto.
    auto.
  intro. apply H. rewrite H1. left. auto.
Qed.

Lemma csub_heap_update_csand (x: V) (e: expr) (p q: cassert):
  valid (clequiv (csub_heap_update (csand p q) x e)
    (clor (csand (csub_heap_update p x e) (cland q (clnot (chasvaldash x))))
      (csand (cland p (clnot (chasvaldash x))) (csub_heap_update q x e)))).
unfold valid; intros.
simpl. split; intros.
- intro. destruct H0.
  apply H; clear H; intros; intro.
  destruct H. destruct H2.
  pose proof (Partition_heap_update_split _ _ _ _ _ H).
  destruct H4; destruct H4; destruct H4.
  + destruct H5.
    apply H0; clear H0. intro.
    specialize H0 with x0 h2. apply H0; clear H0.
    split. auto. split. rewrite <- H5. auto. split. auto.
    intro. exfalso. apply H0. intro. intro.
    rewrite store_update_lookup_diff in H7.
    rewrite store_update_lookup_same in H7.
    apply H6. intro. rewrite H7 in H8. inversion H8.
    intro. apply fresh_notIn with (xs := x :: nil). rewrite H8. left. auto.
  + destruct H5.
    apply H1; clear H1. intro.
    specialize H1 with h1 x0. apply H1; clear H1.
    split. auto. split. split. auto. intro.
    exfalso. apply H1; clear H1; intros. intro.
    rewrite store_update_lookup_diff in H1.
    rewrite store_update_lookup_same in H1.
    apply H6. intro. rewrite H1 in H7. inversion H7.
    intro. apply fresh_notIn with (xs := x :: nil). rewrite H7. left. auto.
    rewrite <- H5. auto.
- intro. apply H; clear H. split; intro.
  + apply H; intros; intro. destruct H1. destruct H2. destruct H3. clear H.
    assert (~dom h2 (s x)). { intro. assert (false = true). apply H4; clear H4. intro.
      unfold dom in H.
      remember (h2 (s x)). destruct o.
      specialize H4 with z.
      rewrite store_update_lookup_diff in H4.
      rewrite store_update_lookup_same in H4.
      apply H4. auto.
      intro. apply fresh_notIn with (xs := x :: nil). rewrite H5. left; auto.
      apply H; auto. inversion H5. }
    pose proof (heap_update_Partition _ _ _ (s x) (e s) H1 H).
    specialize H0 with (heap_update h1 (s x) (e s)) h2.
    apply H0; clear H0. split; auto.
  + apply H; intros; intro. clear H. destruct H1. destruct H1. destruct H1.
    apply Partition_comm in H.
    assert (~dom h1 (s x)). {
      intro. assert (false = true). apply H3; clear H3. intro.
      unfold dom in H4.
      remember (h1 (s x)). destruct o.
      specialize H3 with z.
      rewrite store_update_lookup_diff in H3.
      rewrite store_update_lookup_same in H3.
      apply H3. auto.
      intro. apply fresh_notIn with (xs := x :: nil). rewrite H5. left; auto.
      apply H4; auto. inversion H5.
    }
    pose proof (heap_update_Partition _ _ _ (s x) (e s) H H4).
    apply Partition_comm in H5.
    specialize H0 with h1 (heap_update h2 (s x) (e s)).
    apply H0; clear H0. split; auto.
Qed.

Lemma csub_heap_update_csimp (x: V) (e: expr) (p q: cassert):
  valid (clequiv (csub_heap_update (csimp p q) x e)
    (csimp (cland p (clnot (chasvaldash x))) (csub_heap_update q x e))).
unfold valid; intros.
simpl. split; intros.
- destruct H1.
  assert (~dom h' (s x)). {
    intro. assert (false = true). apply H2; clear H2. intro.
    unfold dom in H3.
    remember (h' (s x)). destruct o.
    specialize H2 with z.
    rewrite store_update_lookup_diff in H2.
    rewrite store_update_lookup_same in H2.
    apply H2. auto.
    intro. apply fresh_notIn with (xs := x :: nil). rewrite H4. left; auto.
    apply H3; auto. inversion H4.
  }
  pose proof (heap_update_Partition _ _ _ (s x) (e s) H0 H3).
  eapply H. apply H4. auto.
- pose proof (Partition_heap_update _ _ _ _ _ H0).
  destruct H2. destruct H2.
  specialize H with x0 h'.
  apply H in H3; clear H.
  rewrite H2. auto. split; auto.
  intro. exfalso. apply H; clear H. intros.
  rewrite store_update_lookup_diff.
  rewrite store_update_lookup_same.
  pose proof (Partition_dom_right1 _ _ _ (s x) H0).
  intro. destruct H. unfold heap_update. unfold dom.
    destruct (Z.eq_dec (s x) (s x)). intro. inversion H.
    exfalso. apply n. auto.
  unfold dom. rewrite H4. intro. inversion H.
  intro.
  apply fresh_notIn with (xs := x :: nil). rewrite H. left; auto.
Qed.

(* E1-3 for heap clear, E13-E16 *)
Lemma csub_heap_clear_ctest (x: V) (g: guard):
  valid (clequiv (csub_heap_clear (ctest g) x) (ctest g)).
unfold valid; intros.
simpl. auto.
Qed.

Lemma csub_heap_clear_chasval (x: V) (e1 e2: expr):
  valid (clequiv (csub_heap_clear (chasval e1 e2) x)
    (cland (clnot (ctest (equals x e1))) (chasval e1 e2))).
unfold valid; intros.
simpl. split; intros.
- unfold heap_clear in H.
  destruct (Z.eq_dec (s x) (e1 s)). inversion H.
  split; auto.
- unfold heap_clear.
  destruct (Z.eq_dec (s x) (e1 s)).
  destruct H. exfalso. assert (false = true). apply H; auto.
    inversion H1.
  destruct H. auto.
Qed.

Lemma csub_heap_clear_climp (x: V) (p q: cassert):
  valid (clequiv (csub_heap_clear (climp p q) x) (climp (csub_heap_clear p x) (csub_heap_clear q x))).
unfold valid; intros.
simpl.
assert ((p (heap_clear h (s x), s) -> q (heap_clear h (s x), s)) -> p (heap_clear h (s x), s) -> q (heap_clear h (s x), s)).
{ intros. auto. }
split; auto.
Qed.

Lemma csub_heap_clear_clforall (x: V) (y: V) (p: cassert):
  y <> x ->
  valid (clequiv (csub_heap_clear (clforall y p) x) (clforall y (csub_heap_clear p x))).
intros; unfold valid; intros.
simpl. split; intros.
- rewrite store_update_lookup_diff; auto.
- specialize H0 with v.
  rewrite store_update_lookup_diff in H0; auto.
Qed.

Lemma csub_heap_clear_csand (x: V) (p q: cassert):
  valid (clequiv (csub_heap_clear (csand p q) x)
    (csand (csub_heap_clear p x) (csub_heap_clear q x))).
unfold valid; intros.
simpl. split; intros.
- intro. apply H; clear H; intros; intro.
  destruct H. destruct H1.
  pose proof (Partition_heap_clear _ _ _ _ H).
  destruct H3. destruct H3. destruct H3. destruct H4.
  specialize H0 with x0 x1.
  apply H0. split; auto. split.
  rewrite <- H4. auto.
  rewrite <- H5. auto.
- intro. apply H; clear H. intros. intro.
  destruct H. destruct H1.
  pose proof (heap_clear_Partition _ _ _ (s x) H).
  specialize H0 with (heap_clear h1 (s x)) (heap_clear h2 (s x)).
  apply H0. split. auto. split; auto.
Qed.

Lemma csub_heap_clear_csimp (x: V) (p q: cassert):
  forall y, ~In y (x :: cvar p ++ cvar q) ->
  valid (clequiv (csub_heap_clear (csimp p q) x)
    (cland (csimp (cland p (clnot (chasvaldash x))) (csub_heap_clear q x))
      (clforall y (csimp (csub_heap_update p x y) (csub_heap_update q x y))))).
intros. unfold valid. intros.
simpl. split; intros.
- split; intros.
  + destruct H2.
    assert (~dom h' (s x)). {
      intro. assert (false = true). apply H3; clear H3. intro.
      unfold dom in H4.
      remember (h' (s x)). destruct o.
      specialize H3 with z.
      rewrite store_update_lookup_diff in H3.
      rewrite store_update_lookup_same in H3.
      apply H3. auto.
      intro. apply fresh_notIn with (xs := x :: nil). rewrite H5. left; auto.
      apply H4; auto. inversion H5.
    } clear H3.
    apply H0 with (h' := h'); auto.
    rewrite <- heap_clear_dom with (k := s x).
    apply heap_clear_Partition. auto. auto.
  + assert (y <> x). { admit. }
    rewrite store_update_lookup_diff in *; auto.
    rewrite store_update_lookup_same in *.
    rewrite ccond with (t := s).
    rewrite ccond with (t := s) in H2.
    pose proof (heap_clear_heap_update_Partition _ _ _ (s x) v H1).
    destruct H4.
    pose proof (H0 _ _ H4 H2).
    pose proof (Partition_heap_clear_heap_update _ _ _ _ _ _ H1 H4).
    rewrite <- H6. auto.
    admit.
    admit.
- destruct H0.
  remember (h' (s x)). destruct o.
  + (* Use second part, H3 *)
    symmetry in Heqo.
    remember (h (s x)). destruct o.
    * symmetry in Heqo0.
      pose proof (heap_clear_Partition_heap_update _ _ _ _ z0 H1 Heqo0).
      apply H3 with (v := z) in H4.
      rewrite store_update_lookup_diff in H4.
      rewrite store_update_lookup_same in H4.
      rewrite heap_update_cancel in H4.
      apply ccond with (t := store_update s y z); auto.
      admit.
      unfold Partition in H1. destruct H1. destruct H5. destruct H6.
      rewrite H7. auto. unfold dom. rewrite Heqo. intro. inversion H8.
      admit.
      rewrite store_update_lookup_diff.
      rewrite store_update_lookup_same.
      rewrite heap_update_heap_clear_cancel; auto.
      apply ccond with (t := s); auto.
      admit.
      admit.
    * symmetry in Heqo0.
      pose proof (heap_clear_Partition_heap_clear _ _ _ _ H1 Heqo0).
      apply H3 with (v := z) in H4.
      rewrite store_update_lookup_diff in H4.
      rewrite store_update_lookup_same in H4.
      rewrite heap_update_heap_clear_cancel in H4.
      apply ccond with (t := store_update s y z); auto.
      admit.
      unfold Partition in H1. destruct H1. destruct H5. destruct H6.
      rewrite H7. auto. unfold dom. rewrite Heqo. intro. inversion H8.
      admit.
      rewrite store_update_lookup_diff.
      rewrite store_update_lookup_same.
      rewrite heap_update_heap_clear_cancel; auto.
      apply ccond with (t := s); auto.
      admit.
      admit.
  + (* Use first part, H0 *)
    symmetry in Heqo.
    remember (h (s x)). destruct o.
    * symmetry in Heqo0.
      pose proof (heap_clear_Partition_heap_update _ _ _ _ z H1 Heqo0).
      apply H0 in H4.
      rewrite heap_clear_heap_update_cancel in H4.
      auto.
      admit.
      split.
      rewrite heap_clear_cancel.
      auto. auto.
      intro. exfalso. apply H5; clear H5. intros. intro.
      rewrite store_update_lookup_diff in H5.
      rewrite store_update_lookup_same in H5.
      rewrite heap_clear_cancel in H5; auto.
      rewrite Heqo in H5. inversion H5.
      admit.
    * symmetry in Heqo0.
      pose proof (heap_clear_Partition_heap_clear _ _ _ _ H1 Heqo0).
      apply H0 in H4.
      rewrite heap_clear_cancel in H4.
      rewrite heap_clear_cancel in H4. auto.
      admit.
      admit.
      split.
      rewrite heap_clear_cancel; auto.
      intro. exfalso. apply H5; clear H5. intros. intro.
      rewrite store_update_lookup_diff in H5.
      rewrite store_update_lookup_same in H5.
      rewrite heap_clear_cancel in H5; auto.
      rewrite Heqo in H5. inversion H5.
      admit.
Admitted.

(* E5 *)
Lemma cwlp_lookup_p1 (x: V) (e: expr) (h: heap) (s: store):
  ~ bigstep (lookup x e) (h, s) None -> exists z, h (e s) = Some z.
intros.
remember (h (e s)). destruct o.
exists z. auto.
exfalso. apply H.
apply step_lookup_fail. auto.
Qed.

Lemma cwlp_lookup (x: V) (e: expr) (p: cassert):
  forall y, ~In y (x :: cvar p ++ evar e) ->
    valid (clequiv (cwlp (lookup x e) p) (clexists y (cland (chasval e y) (cwlp (basic x y) p)))).
intros. unfold valid; intros.
simpl. split; intros.
- destruct H0.
  intro.
  pose proof (cwlp_lookup_p1 x e h s H0). destruct H3.
  specialize H2 with x0. apply H2; clear H2. split.
  rewrite store_update_lookup_same.
  rewrite econd with (t := s). auto.
  intro. intro. unfold store_update.
    destruct (Nat.eq_dec y x1). exfalso.
    apply H. rewrite e0. right. apply in_or_app. auto. auto.
  split. intro. inversion H2.
  intros. inversion H2. rewrite store_update_lookup_same.
  rewrite <- H9.
  rewrite store_update_swap.
  rewrite ccond with (t := store_update s x x0).
  apply H1.
  apply step_lookup. auto.
  intro. intro. unfold store_update at 1.
    destruct (Nat.eq_dec y x2). exfalso.
    apply H. rewrite e1. right. apply in_or_app. auto. auto.
  intro. apply H. rewrite H4. left. auto.
- split.
  intro. inversion H1. apply H0; clear H0. intros. intro. destruct H0.
  rewrite econd with (t := s) in H0. rewrite H3 in H0. inversion H0.
  intro. intros. unfold store_update.
    destruct (Nat.eq_dec y x1); auto. exfalso.
    apply H. rewrite e1. right. apply in_or_app; auto.
  intros. inversion H1. rewrite <- H7.
  apply cstable. intro. apply H0; clear H0. intros. intro.
    destruct H0. destruct H10.
  apply H9.
  rewrite ccond with (t := store_update (store_update s x v) y v0).
  assert (v = v0).
  { rewrite econd with (t := s) in H0.
    rewrite H7 in H0. rewrite H0 in H3. inversion H3.
    rewrite store_update_lookup_same. auto.
    intro. intro. unfold store_update.
      destruct (Nat.eq_dec y x1). exfalso. apply H.
      rewrite e1. right. apply in_or_app. auto. auto. }
  rewrite H12.
  rewrite store_update_swap.
  assert (v0 = y (store_update s y v0)).
  { simpl. rewrite store_update_lookup_same. auto. }
  rewrite H13 at 2.
  apply H11.
  apply step_basic.
  intro. apply H. rewrite H13. left; auto.
  intro. intros. unfold store_update at 2.
    destruct (Nat.eq_dec y x1). exfalso. apply H. rewrite e1.
    right. apply in_or_app; auto.
    auto.
Qed.

(* E6 *)
Lemma cwlp_mutation (x: V) (e: expr) (p: cassert):
  valid (clequiv (cwlp (mutation x e) p) (cland (chasvaldash x) (csub_heap_update p x e))).
Admitted.

(* E7 *)
Lemma cwlp_new (x: V) (e: expr) (p: cassert):
  valid (clequiv (cwlp (new x e) p) (clforall x (climp (clnot (chasvaldash x)) (csub_heap_update p x e)))).
Admitted.

(* E8 *)
Lemma cwlp_dispose (x: V) (p: cassert):
  valid (clequiv (cwlp (dispose x) p) (cland (chasvaldash x) (csub_heap_clear p x))).
Admitted.





















