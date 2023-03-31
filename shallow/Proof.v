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
Admitted.

Lemma csub_heap_update_chasval (x: V) (e: expr) (e1 e2: expr):
  valid (clequiv (csub_heap_update (chasval e1 e2) x e)
    (clor (cland (ctest (equals x e1)) (ctest (equals e2 e))) (cland (clnot (ctest (equals x e1))) (chasval e1 e2)))).
Admitted.

Lemma csub_heap_update_climp (x: V) (e: expr) (p q: cassert):
  valid (clequiv (csub_heap_update (climp p q) x e) (climp (csub_heap_update p x e) (csub_heap_update q x e))).
Admitted.

Lemma csub_heap_update_clforall (x: V) (e: expr) (y: V) (p: cassert):
  ~In y (x :: evar e) ->
  valid (clequiv (csub_heap_update (clforall y p) x e) (clforall y (csub_heap_update p x e))).
Admitted.

Lemma csub_heap_update_csand (x: V) (e: expr) (p q: cassert):
  valid (clequiv (csub_heap_update (csand p q) x e)
    (clor (csand (csub_heap_update p x e) (cland q (clnot (chasvaldash x))))
      (csand (cland p (clnot (chasvaldash x))) (csub_heap_update q x e)))).
Admitted.

Lemma csub_heap_update_csimp (x: V) (e: expr) (p q: cassert):
  valid (clequiv (csub_heap_update (csimp p q) x e)
    (csimp (cland p (clnot (chasvaldash x))) (csub_heap_update q x e))).
Admitted.

(* E1-3 for heap clear, E13-E16 *)
Lemma csub_heap_clear_ctest (x: V) (g: guard):
  valid (clequiv (csub_heap_clear (ctest g) x) (ctest g)).
Admitted.

Lemma csub_heap_clear_chasval (x: V) (e1 e2: expr):
  valid (clequiv (csub_heap_clear (chasval e1 e2) x)
    (cland (clnot (ctest (equals x e1))) (chasval e1 e2))).
Admitted.

Lemma csub_heap_clear_climp (x: V) (p q: cassert):
  valid (clequiv (csub_heap_clear (climp p q) x) (climp (csub_heap_clear p x) (csub_heap_clear q x))).
Admitted.

Lemma csub_heap_clear_clforall (x: V) (y: V) (p: cassert):
  y <> x ->
  valid (clequiv (csub_heap_clear (clforall y p) x) (clforall y (csub_heap_clear p x))).
Admitted.

Lemma csub_heap_clear_csand (x: V) (p q: cassert):
  valid (clequiv (csub_heap_clear (csand p q) x)
    (csand (csub_heap_clear p x) (csub_heap_clear q x))).
Admitted.

Lemma csub_heap_clear_csimp (x: V) (p q: cassert):
  forall y, ~In y (x :: cvar p ++ cvar q) ->
  valid (clequiv (csub_heap_clear (csimp p q) x)
    (cland (csimp (cland p (clnot (chasvaldash x))) (csub_heap_clear q x))
      (clforall y (csimp (csub_heap_update p x y) (csub_heap_update q x y))))).
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





















