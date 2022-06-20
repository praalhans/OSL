(* Copyright 2022 Centrum Wiskunde & Informatica *)

(* ON SEPERATION LOGIC *)
(* Author: Hans-Dieter A. Hiep *)

Require Import FunctionalExtensionality.
Require Import PropExtensionality.
Require Import Ensembles.
Require Import List.
Require Import ZArith.

Require Import OnSeparationLogic.Heap.

Module Language (Export HS: HeapSig).

Module H := HeapFacts HS.
Export H.

Definition V := nat.
Definition dummy: V := 0.

Fixpoint maximum (xs: list V): V :=
  match xs with
  | nil => dummy
  | (x::xs) => max x (maximum xs)
  end.
Proposition maximum_prop (xs: list V):
  forall x, In x xs -> x <= maximum xs.
intros. induction xs. inversion H.
simpl. destruct H.
rewrite H.
apply Nat.le_max_l.
destruct (le_gt_dec a (maximum xs)).
rewrite max_r; try assumption.
apply IHxs; assumption.
unfold gt in g.
apply Nat.lt_le_incl in g.
rewrite max_l; try assumption.
eapply le_trans.
apply IHxs; assumption.
assumption.
Qed.

Proposition maximum_app (xs ys: list V):
  maximum (xs ++ ys) = max (maximum xs) (maximum ys).
induction xs; simpl. reflexivity.
rewrite IHxs.
apply Nat.max_assoc.
Qed.

Definition fresh (xs: list V): V := S (maximum xs).
Proposition fresh_prop (xs: list V):
  forall x, In x xs -> x < fresh xs.
unfold fresh.
intros. apply le_lt_n_Sm.
apply maximum_prop; assumption.
Qed.
Proposition fresh_notIn (xs: list V):
  ~In (fresh xs) xs.
intro.
pose proof (fresh_prop xs).
specialize H0 with (fresh xs).
specialize (H0 H).
eapply Nat.lt_irrefl. apply H0.
Qed.

Proposition fresh_app (xs ys: list V):
  fresh (xs ++ ys) = max (fresh xs) (fresh ys).
unfold fresh.
rewrite maximum_app.
simpl. reflexivity.
Qed.

Proposition fresh_notInApp (xs ys: list V):
  ~In (fresh (xs ++ ys)) xs.
rewrite fresh_app.
destruct (Nat.max_dec (fresh xs) (fresh ys)).
rewrite e. apply fresh_notIn.
rewrite e.
pose proof (Max.le_max_l (fresh xs) (fresh ys)).
rewrite e in H.
destruct (Nat.eq_dec (fresh xs) (fresh ys)).
rewrite <- e0. apply fresh_notIn.
apply Nat.le_lteq in H. destruct H. clear n.
intro.
apply fresh_prop in H0.
eapply Nat.lt_irrefl.
eapply Nat.lt_trans. apply H. apply H0.
exfalso. apply n. assumption.
Qed.

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

Proposition guard_eq (g1 g2: guard):
  (gval g1 = gval g2) -> (gvar g1 = gvar g2) -> g1 = g2.
intros. destruct g1. destruct g2.
simpl in *. revert gcond0. rewrite H. rewrite H0.
intro. pose proof (proof_irrelevance _ gcond0 gcond1).
rewrite H1. reflexivity.
Qed.

Inductive assert :=
| test: guard -> assert
| hasval: expr -> expr -> assert
| land: assert -> assert -> assert
| limp: assert -> assert -> assert
| lforall: V -> assert -> assert
| sand: assert -> assert -> assert
| simp: assert -> assert -> assert.
Coercion test: guard >-> assert.

Definition lnot (p: assert): assert := (limp p false).
Definition lor (p q: assert): assert := lnot (land (lnot p) (lnot q)).
Definition lexists (x: V) (p: assert): assert := lnot (lforall x (lnot p)).
Definition hasvaldash (e: expr): assert :=
  let y := fresh (evar e) in lexists y (hasval e y).
Definition emp: assert := (lforall dummy (lnot (hasvaldash dummy))).
Definition pointsto (e e': expr): assert :=
  let x := fresh (evar e) in land (hasval e e') (lforall x (limp (hasvaldash x) (equals x e))).
Definition pointstodash (e: expr): assert :=
  let y := fresh (evar e) in lexists y (pointsto e y).
Definition hasval_alt (e e': expr): assert :=
  sand (pointsto e e') true.
Definition hasvaldash_alt (e: expr): assert :=
  sand (pointstodash e) true.

End Language.

















