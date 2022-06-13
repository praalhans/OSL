(* Copyright 2022 Centrum Wiskunde & Informatica *)

(* ON SEPERATION LOGIC *)
(* Author: Hans-Dieter A. Hiep *)

From Coq Require Import ZArith.
From Coq Require Import Setoid.
From Coq Require Import Morphisms.
From Coq Require Import FunctionalExtensionality.
From Coq Require Import ProofIrrelevance.
From Coq Require Import Ensembles.
From Coq Require Import List.

Definition SomeZ (v: Z) := Some v.
Coercion SomeZ: Z >-> option.

Definition L := Z.

Record heap: Set := mkheap {
  hfun: L -> option Z;
  hvar: list L;
  hcond: forall x, In x hvar <-> hfun x <> None
}.
Coercion hfun: heap >-> Funclass.

Definition dom (h: heap): Ensemble L :=
  fun n => h n <> None.

Definition Partition (h h1 h2: heap): Prop :=
  ((Included Z (dom h) (Union Z (dom h1) (dom h2)) /\
    Disjoint Z (dom h1) (dom h2)) /\
   (forall n, dom h1 n -> h n = h1 n)) /\
  (forall n, dom h2 n -> h n = h2 n).

Definition hfun_update (h: heap) (n: L) (v: Z): L -> option Z :=
  fun m => if Z.eq_dec n m then v else h m.
Definition hvar_update (h: heap) (n: L) (v: Z): list L :=
  cons n (hvar h).
Proposition hcond_update (h: heap) (n: L) (v: Z):
    forall x, In x (hvar_update h n v) <-> (hfun_update h n v) x <> None.
split; unfold hvar_update; unfold hfun_update; intro.
- destruct H.
  rewrite H; destruct (Z.eq_dec x x).
  intro; inversion H0.
  exfalso; apply n0; reflexivity.
  unfold hfun_update.
  destruct (Z.eq_dec n x).
  intro; inversion H0.
  apply hcond; assumption.
- destruct (Z.eq_dec n x).
  rewrite e; constructor; reflexivity.
  right. apply hcond; assumption.
Qed.
Definition heap_update (h: heap) (n: L) (v: Z): heap :=
  mkheap (hfun_update h n v) (hvar_update h n v) (hcond_update h n v).

Definition V := nat.

Definition store := V -> Z.

Definition store_update (s: store) (x: V) (v: Z): store :=
  fun y => if Nat.eq_dec x y then v else s y.

Definition eq_restr (s t: store) (z: list V): Prop :=
  forall (x: V), In x z -> s x = t x.

(* Expressions are shallow, but finitely based *)
Record expr: Set := mkexpr {
  eval: store -> Z;
  evar: list V;
  econd: forall (s t: store), eq_restr s t evar -> eval s = eval t
}.
Coercion eval: expr >-> Funclass.

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

(* Classical *)

Fixpoint satisfy (h: heap) (s: store) (p: assert): Prop :=
  match p with
  | test g => g s = true
  | hasval e e' => dom h (e s) /\ h (e s) = e' s
  | land p q => satisfy h s p /\ satisfy h s q
  | limp p q => satisfy h s p -> satisfy h s q
  | lforall x p => forall v, satisfy h (store_update s x v) p
  | sand p q => exists h1 h2, Partition h h1 h2 /\
      satisfy h1 s p /\ satisfy h2 s q
  | simp p q => forall h'' h', Partition h'' h h' ->
      satisfy h' s p -> satisfy h'' s q
  end.

(* Stable assertions *)
Definition stable (p: assert) := forall h s, satisfy h s (lnot (lnot p)) -> satisfy h s p.

Proposition stable_simp (p q: assert): stable p -> stable q -> stable (simp p q).
intros.
unfold stable; intros.
simpl; intros.
apply H0.
simpl; intros.
simpl in H1; apply H1; intro.
apply H4.
eapply H5. apply H2. assumption.
Qed.

Fixpoint satisfy_i (h: heap) (s: store) (p: assert): Prop :=
  match p with
  | test g => g s = true
  | hasval e e' => dom h (e s) /\ h (e s) = e' s
  | land p q => satisfy_i h s p /\ satisfy_i h s q
  | limp p q => forall h'' h', Partition h'' h h' -> satisfy_i h' s p -> satisfy_i h' s q
  | lforall x p => forall v, satisfy_i h (store_update s x v) p
  | sand p q => exists h1 h2, Partition h h1 h2 /\
      satisfy_i h1 s p /\ satisfy_i h2 s q
  | simp p q => forall h'' h', Partition h'' h h' ->
      satisfy_i h' s p -> satisfy_i h'' s q
  end.

















