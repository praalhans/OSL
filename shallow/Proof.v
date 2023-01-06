Require Export ShallowSeparationLogic.Language.

(* ============= *)
(* SPECIFICATION *)
(* ============= *)

Inductive spec: Type :=
| mkhoare: cassert -> program -> cassert -> spec.

Definition valid (p: cassert): Prop :=
  forall h s, p (h, s).

Definition correct (psq: spec): Prop :=
  match psq with
  | mkhoare p S1 q =>
    forall h s, p (h, s) ->
      ~bigstep S1 (h, s) None /\
      forall h' s', bigstep S1 (h, s) (Some (h', s')) -> q (h', s')
  end.

(* ======================================================================= *)
(* WEAKEST PRECONDITION AXIOMATIZATION (WP-CSL), SEE FIGURE 3 IN THE PAPER *)
(* ======================================================================= *)

Inductive WPCSL: spec -> Type :=
| wpc_basic (p: cassert) (x: V) (e: expr):
    WPCSL (mkhoare (csub p x e) (basic x e) p)
| wpc_lookup (p: cassert) (x y: V) (e: expr):
    ~In y (x :: cvar p ++ evar e) ->
    WPCSL (mkhoare (clexists y (cland (chasval e y) (csub p x y))) (lookup x e) p)
| wpc_mutation (p: cassert) (x: V) (e: expr):
    WPCSL (mkhoare (cland (chasvaldash x) (csub_heap_update p x e)) (mutation x e) p)
| wpc_new (p: cassert) (x: V) (e: expr):
    ~In x (evar e) ->
    WPCSL (mkhoare (clforall x (climp (clnot (chasvaldash x)) (csub_heap_update p x e))) (new x e) p)
| wpc_dispose (p: cassert) (x: V):
    WPCSL (mkhoare (cland (chasvaldash x) (csub_heap_clear p x)) (dispose x) p)
| wpc_skip (p: cassert):
    WPCSL (mkhoare p skip p)
| wpc_compose (p q r: cassert) (S1 S2: program):
    WPCSL (mkhoare p S1 r) ->
    WPCSL (mkhoare r S2 q) ->
    WPCSL (mkhoare p (comp S1 S2) q)
| wpc_ite (p q: cassert) (g: guard) (S1 S2: program):
    WPCSL (mkhoare (cland p (ctest g)) S1 q) ->
    WPCSL (mkhoare (cland p (clnot (ctest g))) S2 q) ->
    WPCSL (mkhoare p (ite g S1 S2) q)
| wpc_while (p: cassert) (g: guard) (S1: program):
    WPCSL (mkhoare (cland p (ctest g)) S1 p) ->
    WPCSL (mkhoare p (while g S1) (cland p (clnot (ctest g))))
| wpc_conseq (p pp q qq: cassert) (x: program):
    valid (climp pp p) -> WPCSL (mkhoare p x q) -> valid (climp q qq) ->
    WPCSL (mkhoare pp x qq).

(* Soundness of the proof system *)

Proposition WPCSL_basic_soundness (p: cassert) (x: V) (e: expr):
  correct (mkhoare (csub p x e) (basic x e) p).
Admitted.

Proposition WPCSL_lookup_soundness (p: cassert) (x y: V) (e: expr):
  ~ In y (x :: cvar p ++ evar e) ->
  correct (mkhoare (clexists y (cland (chasval e y) (csub p x y))) (lookup x e) p).
Admitted.

Proposition WPCSL_mutation_soundness (p: cassert) (x: V) (e: expr):
  correct (mkhoare (cland (chasvaldash x) (csub_heap_update p x e)) (mutation x e) p).
Admitted.

Proposition WPCSL_new_soundness (p: cassert) (x: V) (e: expr):
  ~ In x (evar e) ->
  correct (mkhoare (clforall x (climp (clnot (chasvaldash x)) (csub_heap_update p x e))) (new x e) p).
Admitted.

Proposition WPCSL_dispose_soundness (p: cassert) (x: V):
  correct (mkhoare (cland (chasvaldash x) (csub_heap_clear p x)) (dispose x) p).
Admitted.

Proposition WPCSL_skip_soundness (p: cassert):
  correct (mkhoare p skip p).
intro; intros. split.
+ intro. inversion H0.
+ intros. inversion H0.
  rewrite <- H4.
  rewrite <- H5.
  assumption.
Qed.

Proposition WPCSL_comp_soundness (p q r: cassert) (S1 S2: program):
  correct (mkhoare p S1 r) ->
  correct (mkhoare r S2 q) ->
  correct (mkhoare p (comp S1 S2) q).
intros; intro; intros. split.
+ unfold correct in *.
  specialize H with h s.
  apply H in H1; clear H.
  destruct H1.
  intro.
  inversion H2. apply H. assumption.
  apply H1 in H6.
  apply H0 in H6; clear H0.
  destruct H6.
  apply H0; assumption.
+ unfold correct in *.
  specialize H with h s.
  apply H in H1; clear H; destruct H1.
  intros.
  inversion H2.
  apply H1 in H6.
  apply H0 in H6.
  destruct H6.
  apply H11 in H10.
  assumption.
Qed.

Proposition WPCSL_ite_soundness (p q: cassert) (g: guard) (S1 S2: program):
  correct (mkhoare (cland p (ctest g)) S1 q) ->
  correct (mkhoare (cland p (clnot (ctest g))) S2 q) ->
  correct (mkhoare p (ite g S1 S2) q).
Admitted.

Proposition WPCSL_while_soundness (p: cassert) (g: guard) (S1: program):
  correct (mkhoare (cland p (ctest g)) S1 p) ->
  correct (mkhoare p (while g S1) (cland p (clnot (ctest g)))).
Admitted.

Proposition WPCSL_conseq_soundness (p pp q qq: cassert) (S1: program):
  valid (climp pp p) ->
  valid (climp q qq) ->
  correct (mkhoare p S1 q) ->
  correct (mkhoare pp S1 qq).
intros. unfold correct in *; intros.
split.
intro.
unfold valid in *.
simpl in H.
apply H in H2.
apply H1 in H2. destruct H2.
apply H2; auto.
intros.
apply H in H2.
apply H1 in H2; destruct H2.
apply H4 in H3.
apply H0 in H3.
assumption.
Qed.

Theorem WPCSL_soundness (psq: spec):
  WPCSL psq -> correct psq.
intro.
induction X.
- apply WPCSL_basic_soundness.
- apply WPCSL_lookup_soundness; auto.
- apply WPCSL_mutation_soundness.
- apply WPCSL_new_soundness; auto.
- apply WPCSL_dispose_soundness.
- apply WPCSL_skip_soundness.
- apply WPCSL_comp_soundness with (r := r); auto.
- apply WPCSL_ite_soundness; auto.
- apply WPCSL_while_soundness; auto.
- apply WPCSL_conseq_soundness with (p := p) (q := q); auto.
Qed.

(* Completeness of the proof system *)

(* TODO: also adapt to None outcome *)
Proposition bigstep_cond_Some (S1: program) (p: heap * store) (o: option (heap * store)):
  bigstep S1 p o ->
  forall xs, (forall x, In x (pvar S1) -> In x xs) ->
  forall h s, (h, s) = p ->
  forall h' s', Some (h', s') = o ->
  forall t, eq_restr s t xs ->
  exists t', eq_restr s' t' xs /\ bigstep S1 (h, t) (Some (h', t')).
intro.
induction H; intros xs G h0 s0 G1 h'0 s'0 G2 t G3;
inversion G1; inversion G2; clear G1 G2.
- rewrite H1 in G3.
  exists (store_update t x (e t)). split.
  + intro; intro.
    unfold store_update.
    destruct (Nat.eq_dec x x0).
    apply econd.
    eapply eq_restr_incl; [|apply G3].
    intros. apply G. simpl; auto.
    apply G3; auto.
  + apply step_basic.
- exists (store_update t x v). split.
  + intro; intro.
    rewrite <- H2.
    unfold store_update.
    destruct (Nat.eq_dec x x0); auto.
  + apply step_lookup.
    pose proof (econd e s t).
    rewrite <- H0; auto.
    rewrite <- H2.
    eapply eq_restr_incl; [|apply G3].
    intros. apply G. simpl; auto.
- exists t. split.
  + rewrite <- H2. auto.
  + assert (s x = t x).
    admit.
    assert (e s = e t).
    admit.
    rewrite H0.
    rewrite H5.
    apply step_mutation.
    rewrite <- H0. assumption.
- admit.
- admit.
- exists t. split.
  rewrite <- H1. auto.
  apply step_skip.
- destruct IHbigstep1 with (xs := xs) (h := h) (s := s) (h' := h') (s' := s') (t := t); auto.
  intros. apply G. simpl. apply in_or_app; auto. rewrite <- H3. auto.
  destruct H1.
  destruct IHbigstep2 with (xs := xs) (h := h') (s := s') (h' := h'') (s' := s'') (t := x); auto.
  intros. apply G. simpl. apply in_or_app; auto.
  destruct H7.
  exists x0. split; auto.
  eapply step_comp.
  apply H6.
  apply H8.
- destruct o. destruct p.
  destruct IHbigstep with (xs := xs) (h := h) (s := s) (h' := h1) (s' := s1) (t := t); auto.
  intros. apply G. simpl. apply in_or_app. right. apply in_or_app; auto.
  rewrite <- H3; auto.
  destruct H4.
  inversion H1.
  exists x. split; auto.
  apply step_ite_true; auto.
  rewrite H3 in G3.
  rewrite <- gcond with (s := s); auto.
  eapply eq_restr_incl; [|apply G3]. intros.
  apply G. simpl. apply in_or_app; auto.
  inversion H1.
- admit.
- destruct o; inversion H2. destruct p; inversion H6.
  destruct IHbigstep1 with (xs := xs) (h := h) (s := s) (h' := h') (s' := s') (t := t); auto.
  intros. apply G. simpl. apply in_or_app; auto. rewrite H4 in G3; auto.
  destruct H5.
  destruct IHbigstep2 with (xs := xs) (h := h') (s := s') (h' := h1) (s' := s1) (t := x); auto.
  destruct H10.
  exists x0.
  split; auto.
  eapply step_while_true.
  rewrite H4 in G3.
  rewrite <- gcond with (s := s); auto.
  intro; intro. apply G3. apply G. simpl. apply in_or_app; auto.
  apply H9.
  auto.
- admit.
Admitted.

(* Proposition cwlp_cond (S1: program) (q: cassert):
  forall (h : heap) (s t : store),
   eq_restr s t (pvar S1 ++ cvar q) ->
   ~(forall (h' : heap) (s' : store), ~(bigstep S1 (h, s) (Some (h', s')) /\ q (h', s'))) <->
   ~(forall (h' : heap) (s' : store), ~(bigstep S1 (h, t) (Some (h', s')) /\ q (h', s'))).
intros; split; intro; intro; apply H0; intros; intro; destruct H2.
- pose proof (bigstep_cond S1 (h, s) (Some (h', s')) H2 (pvar S1 ++ cvar q)).
  destruct H4 with (h0 := h) (s0 := s) (h'0 := h') (s'0 := s') (t := t); auto.
  apply eq_restr_split in H; destruct H. intros. apply in_or_app; auto.
  destruct H5.
  pose proof (H1 h' x).
  pose proof (ccond q h' s' x).
  rewrite H8 in H3.
  apply H7. split; auto.
  apply eq_restr_split in H5; destruct H5; auto.
- admit.
Admitted.
Proposition cwlp_stable (S1: program) (q: cassert):
  forall (h : heap) (s : store),
   ~ ~ ~ (forall (h' : heap) (s' : store), ~ (bigstep S1 (h, s) (Some (h', s')) /\ q (h', s'))) ->
   ~ forall (h' : heap) (s' : store), ~ (bigstep S1 (h, s) (Some (h', s')) /\ q (h', s')).
intros; intro; apply H; intro.
apply H1; intros. apply H0.
Qed.
Definition cwlp (S1: program) (q: cassert): cassert :=
  mkcassert (fun '(h, s) => ~forall h' s', ~(bigstep S1 (h, s) (Some (h', s')) /\ q (h', s')))
    (pvar S1 ++ cvar q) (cwlp_cond S1 q) (cwlp_stable S1 q). *)
Proposition cwlp_cond (S1: program) (q: cassert):
  forall (h : heap) (s t : store),
   eq_restr s t (pvar S1 ++ cvar q) ->
   (~ bigstep S1 (h, s) None /\ forall (h' : heap) (s' : store),
      bigstep S1 (h, s) (Some (h', s')) -> q (h', s')) <->
   (~ bigstep S1 (h, t) None /\ forall (h' : heap) (s' : store),
      bigstep S1 (h, t) (Some (h', s')) -> q (h', s')).
intros; split; intro; destruct H0.
- split.
  (* TODO: need to adapt above proposition to None outcome *)
  admit.
  intros.
  pose proof (bigstep_cond_Some S1 (h, t) (Some (h', s')) H2 (pvar S1 ++ cvar q)).
  destruct H3 with (h := h) (s := t) (h' := h') (s' := s') (t := s); auto.
  intros. apply in_or_app; auto.
  apply eq_restr_comm. apply H.
  destruct H4. apply H1 in H5.
  apply ccond with (s := x); auto.
  apply eq_restr_comm.
  apply eq_restr_split in H4; destruct H4.
  auto.
- admit.
Admitted.
Proposition cwlp_stable (S1: program) (q: cassert):
  forall (h : heap) (s : store),
   ~ ~ (~ bigstep S1 (h, s) None /\ forall (h' : heap) (s' : store),
      bigstep S1 (h, s) (Some (h', s')) -> q (h', s')) ->
   (~ bigstep S1 (h, s) None /\ forall (h' : heap) (s' : store),
      bigstep S1 (h, s) (Some (h', s')) -> q (h', s')).
intros. split.
intro. apply H. intro. destruct H1.
apply H1. assumption.
intros. apply cstable. intro.
apply H. intro. destruct H2.
apply H3 in H0.
apply H1. assumption.
Qed.
Definition cwlp (S1: program) (q: cassert): cassert :=
  mkcassert (fun '(h, s) => ~bigstep S1 (h, s) None /\
      forall h' s', bigstep S1 (h, s) (Some (h', s')) -> q (h', s'))
    (pvar S1 ++ cvar q) (cwlp_cond S1 q) (cwlp_stable S1 q).

Proposition cwlp_weakest (p q: cassert) (S1: program):
  valid (climp p (cwlp S1 q)) <-> correct (mkhoare p S1 q).
split; intros.
+ unfold valid in H.
  unfold correct.
  intros. split; apply H in H0; simpl in H0; destruct H0.
  apply H0.
  assumption.
+ unfold correct in H.
  unfold valid.
  intros; intro; simpl; intros.
  apply H in H0.
  destruct H0.
  split. assumption.
  assumption.
Qed.














