Require Export FunctionalExtensionality.
Require Export PropExtensionality.
Require Export List.
Require Export Sorting.
Require Export PeanoNat.
Require Export ZArith.

Proposition In_remove (T: Type)
    (eq_dec: forall (x y: T), {x = y} + {x <> y})
    (x y: T) (xs: list T):
  In x xs -> y <> x -> In x (remove eq_dec y xs).
induction xs; intros; inversion H;
simpl; destruct (eq_dec y a).
exfalso. apply H0. rewrite <- H1. auto.
rewrite H1. left. reflexivity.
apply IHxs; assumption.
right. apply IHxs; assumption.
Qed.

Proposition In_remove_elim (T: Type)
    (eq_dec: forall (x y: T), {x = y} + {x <> y})
    (x y: T) (xs: list T):
  y <> x -> In x (remove eq_dec y xs) -> In x xs.
induction xs; intros; simpl in H0.
inversion H0.
specialize (IHxs H).
destruct (eq_dec y a).
specialize (IHxs H0). right. assumption.
inversion H0. rewrite H1. left. auto.
specialize (IHxs H1). right. assumption.
Qed.

(* ========= *)
(* VARIABLES *)
(* ========= *)

Definition V := nat.

Definition store := V -> Z.

Definition store_update (s: store) (x: V) (v: Z): store :=
  fun y => if Nat.eq_dec x y then v else s y.

Definition eq_restr (s t: store) (z: list V): Prop :=
  forall (x: V), In x z -> s x = t x.

Proposition eq_restr_split (s t: store) (xs ys: list V):
  eq_restr s t (xs ++ ys) -> eq_restr s t xs /\ eq_restr s t ys.
unfold eq_restr; intro; split; intros;
apply H; apply in_or_app; auto.
Qed.

Proposition eq_restr_comm (s t: store) (xs: list V):
  eq_restr s t xs -> eq_restr t s xs.
unfold eq_restr; intros; symmetry; apply H; assumption.
Qed.

(* ====================== *)
(* EXPRESSIONS AND GUARDS *)
(* ====================== *)

(* Expressions and guards are shallow, but finitely based *)
Record expr: Set := mkexpr {
  eval: store -> Z;
  evar: list V;
  econd: forall (s t: store), eq_restr s t evar -> eval s = eval t
}.
Coercion eval: expr >-> Funclass.

Proposition const_expr_cond (v: Z) (s t : store):
  eq_restr s t nil -> v = v.
intros. reflexivity.
Qed.
Definition const_expr (v: Z): expr :=
  mkexpr (fun s => v) nil (const_expr_cond v).
Coercion const_expr: Z >-> expr.
Proposition var_expr_cond (x: V) (s t : store):
  eq_restr s t (x :: nil) -> s x = t x.
intro. unfold eq_restr in H.
specialize H with x. apply H.
left. reflexivity.
Qed.
Definition var_expr (x: V): expr :=
  mkexpr (fun s => s x) (x :: nil) (var_expr_cond x).
Coercion var_expr: V >-> expr.

Proposition esub_cond (e: expr) (x: V) (e': expr) (s t : store):
  eq_restr s t (remove Nat.eq_dec x (evar e) ++ evar e') ->
  eval e (store_update s x (eval e' s)) =
    eval e (store_update t x (eval e' t)).
intro.
assert (eval e' s = eval e' t).
apply (econd e').
intro; intro; apply H.
apply in_or_app; right; assumption.
rewrite <- H0.
unfold store_update.
apply (econd e).
unfold eq_restr.
intro; intro.
destruct (Nat.eq_dec x x0).
reflexivity.
apply H; apply in_or_app; left.
apply In_remove; assumption.
Qed.
Definition esub (e: expr) (x: V) (e': expr): expr :=
  mkexpr (fun s => eval e (store_update s x (eval e' s)))
    (remove Nat.eq_dec x (evar e) ++ evar e') (esub_cond e x e').

Proposition esub_simpl (e: expr) (x: V) (e': expr):
  ~In x (evar e) -> forall s, eval (esub e x e') s = eval e s.
intros. simpl.
apply econd. intro. intro.
unfold store_update.
destruct (Nat.eq_dec x x0).
exfalso. apply H. rewrite e0. assumption.
reflexivity.
Qed.

Proposition esub_notInVar (e: expr) (x: V) (e': expr):
  ~In x (evar e') -> ~ In x (evar (esub e x e')).
intros; simpl; intro.
apply in_app_or in H0; destruct H0.
eapply remove_In; apply H0.
apply H; auto.
Qed.

Proposition expr_eq (e1 e2: expr):
  (eval e1 = eval e2) -> (evar e1 = evar e2) -> e1 = e2.
intros. destruct e1. destruct e2.
simpl in *. revert econd0. rewrite H. rewrite H0.
intro. pose proof (proof_irrelevance _ econd0 econd1).
rewrite H1. reflexivity.
Qed.

Record guard: Set := mkguard {
  gval: store -> bool;
  gvar: list V;
  gcond: forall (s t: store), eq_restr s t gvar -> gval s = gval t
}.
Coercion gval: guard >-> Funclass.

Proposition const_guard_cond (v: bool) (s t : store):
  eq_restr s t nil -> v = v.
intros. reflexivity.
Qed.
Definition const_guard (v: bool): guard :=
  mkguard (fun s => v) nil (const_guard_cond v).
Coercion const_guard: bool >-> guard.

Proposition equals_cond (e1 e2: expr) (s t : store):
  eq_restr s t (evar e1 ++ evar e2) ->
  (if Z.eq_dec (eval e1 s) (eval e2 s) then true else false) =
  (if Z.eq_dec (eval e1 t) (eval e2 t) then true else false).
intro H.
apply eq_restr_split in H; destruct H.
pose proof (econd e1 s t); rewrite H1.
pose proof (econd e2 s t); rewrite H2.
all: auto.
Qed.
Definition equals (e1 e2: expr): guard :=
  mkguard (fun s => if Z.eq_dec (eval e1 s) (eval e2 s) then
    true else false) (evar e1 ++ evar e2) (equals_cond e1 e2).

Proposition gsub_cond (g: guard) (x: V) (e: expr) (s t: store):
  eq_restr s t (remove Nat.eq_dec x (gvar g) ++ evar e) ->
  gval g (store_update s x (eval e s)) =
  gval g (store_update t x (eval e t)).
intro.
assert (eval e s = eval e t).
apply (econd e).
intro; intro; apply H.
apply in_or_app; right; assumption.
rewrite <- H0.
unfold store_update.
apply (gcond g).
unfold eq_restr.
intro; intro.
destruct (Nat.eq_dec x x0).
reflexivity.
apply H; apply in_or_app; left.
apply In_remove; assumption.
Qed.
Definition gsub (g: guard) (x: V) (e: expr): guard :=
  mkguard (fun s => gval g (store_update s x (eval e s)))
    (remove Nat.eq_dec x (gvar g) ++ evar e) (gsub_cond g x e).

Proposition gsub_notInVar (g: guard) (x:V) (e: expr):
  ~In x (evar e) -> ~In x (gvar (gsub g x e)).
intros; simpl; intro.
apply in_app_or in H0; destruct H0.
eapply remove_In; apply H0.
apply H. assumption.
Qed.

Proposition guard_eq (g1 g2: guard):
  (gval g1 = gval g2) -> (gvar g1 = gvar g2) -> g1 = g2.
intros. destruct g1. destruct g2.
simpl in *. revert gcond0. rewrite H. rewrite H0.
intro. pose proof (proof_irrelevance _ gcond0 gcond1).
rewrite H1. reflexivity.
Qed.

(* ==================== *)
(* CLASSICAL ASSERTIONS *)
(* ==================== *)

Definition heap := Z -> option Z.

Definition heap_update (h: heap) (k v: Z): heap :=
  fun n => if Z.eq_dec k n then Some v else h n.

Definition heap_clear (h: heap) (k: Z): heap :=
  fun n => if Z.eq_dec k n then None else h n.

Definition dom (h: heap) (k: Z): Prop := h k <> None.

Definition Partition (h h1 h2: heap): Prop :=
  (forall k, (dom h k -> dom h1 k \/ dom h2 k)) /\
  (forall k, ~(dom h1 k /\ dom h2 k)) /\
  (forall k, dom h1 k -> h k = h1 k) /\
  (forall k, dom h2 k -> h k = h2 k).

(* Assertions are shallow, but finitely based *)
Record cassert: Type := mkcassert {
  cval: heap * store -> Prop;
  cvar: list V;
  ccond: forall (h: heap) (s t: store), eq_restr s t cvar -> cval (h, s) <-> cval (h, t);
  cstable: forall (h: heap) (s: store), ~~cval (h, s) -> cval (h, s)
}.
Coercion cval: cassert >-> Funclass.

Proposition ctest_cond (g: guard):
  forall (h : heap) (s t : store),
   eq_restr s t (gvar g) -> g s = true <-> g t = true.
intros.
rewrite gcond with (t := t).
apply iff_refl.
assumption.
Qed.
Proposition ctest_stable (g: guard):
  forall (h : heap) (s : store),
   ~ ~ g s = true -> g s = true.
intros. destruct (g s); auto.
Qed.
Definition ctest (g: guard): cassert :=
  mkcassert (fun '(h, s) => gval g s = true) (gvar g) (ctest_cond g) (ctest_stable g).

Proposition chasval_cond (e1 e2: expr):
  forall (h : heap) (s t : store),
   eq_restr s t (evar e1 ++ evar e2) ->
   h (e1 s) = Some (e2 s) <->
   h (e1 t) = Some (e2 t).
intros.
apply eq_restr_split in H; destruct H.
split; intro.
- rewrite <- econd with (s := s); auto.
  rewrite <- (econd e2) with (s := s); auto.
- rewrite econd with (t := t); auto.
  rewrite (econd e2) with (t := t); auto.
Qed.
Proposition chasval_stable (e1 e2: expr):
  forall (h : heap) (s : store),
   ~ ~ (h (e1 s) = Some (e2 s)) ->
   h (e1 s) = Some (e2 s).
intros.
destruct (h (e1 s)).
remember (e2 s).
destruct (Z.eq_dec z z0).
rewrite e; auto.
exfalso; apply H. intro. inversion H0.
apply n; auto.
exfalso.
apply H. intro. inversion H0.
Qed.
Definition chasval (e1 e2: expr): cassert :=
  mkcassert (fun '(h, s) => h (e1 s) = Some (e2 s)) (evar e1 ++ evar e2)
    (chasval_cond e1 e2) (chasval_stable e1 e2).


