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















