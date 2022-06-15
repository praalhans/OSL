(* Copyright 2022 Centrum Wiskunde & Informatica *)

(* ON SEPERATION LOGIC *)
(* Author: Hans-Dieter A. Hiep *)

From Coq Require Import FunctionalExtensionality.
From Coq Require Import PropExtensionality.
From Coq Require Import Structures.Orders.
From Coq Require Import Ensembles.
From Coq Require Import List.
From Coq Require Import Sorting.
From Coq Require Import ZArith.

Local Open Scope Z_scope.

Module Type HeapSig.

(* Memory heaps are treated as partial functions from Z to Z. *)
Parameter heap: Type.
Parameter hfun: heap -> Z -> option Z.

(* Empty heap *)
Parameter heap_empty: heap.
Axiom heap_empty_spec: forall n, hfun heap_empty n = None.

(* Heap update *)
Parameter heap_update: heap -> Z -> Z -> heap.
Axiom heap_update_spec1: forall h k v, hfun (heap_update h k v) k = Some v.
Axiom heap_update_spec2: forall h k v k',
  k <> k' -> hfun (heap_update h k v) k' = hfun h k'.

(* Domain of heap *)
Parameter heap_dom: heap -> Ensemble Z.
Axiom heap_dom_spec: forall h k, heap_dom h k <-> hfun h k <> None.

(* We have extensional equality for heaps. *)
Axiom heap_ext: forall (h g: heap),
  (forall n, hfun h n = hfun g n) -> h = g.

(* Two heaps may be merged into one (partial operation). *)
Parameter merge: heap -> heap -> option heap.

End HeapSig.

(* Possibly infinite heaps *)

(* Finitely-based heaps *)

Module FHeap <: HeapSig.

Definition assoclist := list (Z * Z).

Fixpoint minkey (l: Z) (xs: assoclist): Prop :=
  match xs with
  | nil => True
  | (k,v) :: xs => l < k /\ minkey l xs
  end.

Proposition minkey_trans (k k': Z) (xs: assoclist):
  k < k' -> minkey k' xs -> minkey k xs.
intros. induction xs.
simpl; auto.
destruct a; simpl.
inversion H0. split.
eapply Z.lt_trans. apply H. apply H1.
apply IHxs. assumption.
Qed.

Inductive heap_prop: assoclist -> Prop :=
| empty: heap_prop nil
| insert (k v: Z) (xs: assoclist):
    minkey k xs -> heap_prop xs -> heap_prop ((k, v) :: xs).

Proposition heap_prop_insert_val (k v v': Z) (xs: assoclist):
  heap_prop ((k, v') :: xs) -> heap_prop ((k, v) :: xs).
intro; inversion H; apply insert; assumption.
Qed.

Fixpoint lookup (xs: assoclist) (z: Z): option Z :=
  match xs with
  | nil => None
  | (k, v) :: xs => if Z.eq_dec z k then Some v else lookup xs z
  end.

Proposition lookup_minkey (xs: assoclist) (k: Z):
  minkey k xs -> lookup xs k = None.
intro; induction xs.
reflexivity.
destruct a as (k', v').
simpl in *. destruct H.
destruct (Z.eq_dec k k').
exfalso. eapply Z.lt_irrefl. rewrite e in H. apply H.
apply IHxs. assumption.
Qed.

Fixpoint update (xs: assoclist) (k v: Z): assoclist :=
  match xs with
  | nil => (k, v) :: nil
  | (k', v') :: xs => match k ?= k' with
    | Lt => (k, v) :: (k', v') :: xs
    | Eq => (k, v) :: xs
    | Gt => (k', v') :: (update xs k v)
    end
  end.

Proposition update_minkey (xs: assoclist) (k k' v: Z):
  k' < k -> minkey k' xs -> minkey k' (update xs k v).
intros. induction xs.
simpl; split; auto.
destruct a; simpl.
remember (k ?= z); destruct c; symmetry in Heqc;
simpl in H0; simpl.
+ apply Z.compare_eq_iff in Heqc. destruct H0.
  split. rewrite Heqc. assumption. assumption.
+ apply -> Z.compare_lt_iff in Heqc.
  split. assumption. assumption.
+ destruct H0.
  split. assumption. apply IHxs. assumption.
Qed.

Proposition update_cons (xs: assoclist) (k v: Z):
  minkey k xs -> update xs k v = (k, v) :: xs.
intro. destruct xs. reflexivity.
simpl. destruct p as (k', v').
simpl in H; destruct H.
remember (k ?= k'); destruct c; symmetry in Heqc.
- exfalso. apply Z.compare_eq_iff in Heqc.
  rewrite Heqc in H. eapply Z.lt_irrefl. apply H.
- reflexivity.
- apply Z.compare_gt_iff in Heqc.
  exfalso. eapply Z.lt_irrefl.
  eapply Z.lt_trans. apply H. assumption.
Qed.

Proposition update_lookup_same (xs: assoclist) (k v: Z):
  lookup (update xs k v) k = Some v.
induction xs; simpl.
destruct (Z.eq_dec k k); [|exfalso; apply n]; reflexivity.
destruct a as (k', v').
remember (k ?= k'); destruct c; simpl.
1,2: destruct (Z.eq_dec k k); [|exfalso; apply n]; reflexivity.
destruct (Z.eq_dec k k').
symmetry in Heqc. apply Z.compare_gt_iff in Heqc.
rewrite e in Heqc. exfalso. eapply Z.lt_irrefl. apply Heqc.
apply IHxs.
Qed.

Proposition update_lookup_diff (xs: assoclist) (k k' v: Z):
  k <> k' -> lookup (update xs k v) k' = lookup xs k'.
intro. induction xs; simpl.
destruct (Z.eq_dec k' k).
exfalso. apply H. symmetry. apply e. reflexivity.
destruct a.
remember (k ?= z); destruct c; symmetry in Heqc; simpl.
+ apply Z.compare_eq_iff in Heqc.
  rewrite Heqc. destruct (Z.eq_dec k' z).
  exfalso. apply H. rewrite Heqc. rewrite e. reflexivity.
  reflexivity.
+ destruct (Z.eq_dec k' k). exfalso. apply H. symmetry. assumption.
  reflexivity.
+ rewrite IHxs. reflexivity.
Qed.

Proposition update_heap_prop (xs: assoclist) (k v: Z):
  heap_prop xs -> heap_prop (update xs k v).
intro.
induction xs; simpl.
- apply insert. simpl; auto. assumption.
- destruct a as (k', v').
  remember (k ?= k'); destruct c; symmetry in Heqc.
  + apply Z.compare_eq_iff in Heqc.
    rewrite <- Heqc in H.
    eapply heap_prop_insert_val. apply H.
  + apply -> Z.compare_lt_iff in Heqc.
    apply insert. simpl. split. assumption.
    inversion H. eapply minkey_trans.
    apply Heqc. assumption. assumption.
  + apply Z.compare_gt_iff in Heqc.
    inversion H. apply insert.
    apply update_minkey; assumption.
    apply IHxs. assumption.
Qed.

Definition heap := {xs: assoclist | heap_prop xs}.
Definition hfun (h: heap) := lookup (proj1_sig h).

Definition heap_empty := exist heap_prop nil empty.
Proposition heap_empty_spec: forall n, hfun heap_empty n = None.
intro; unfold heap_empty; unfold hfun; reflexivity.
Qed.

Definition heap_update (h: heap) (k v: Z): heap :=
  let xs := proj1_sig h in
  exist heap_prop (update xs k v)
    (update_heap_prop xs k v (proj2_sig h)).
Proposition heap_update_spec1: forall h k v,
  hfun (heap_update h k v) k = Some v.
intros. unfold hfun; unfold heap_update; simpl.
apply update_lookup_same.
Qed.
Proposition heap_update_spec2: forall h k v k',
  k <> k' -> hfun (heap_update h k v) k' = hfun h k'.
intros. unfold hfun; unfold heap_update; simpl.
apply update_lookup_diff. assumption.
Qed.

Fixpoint assoclist_dom (xs: assoclist): list Z :=
  match xs with
  | nil => nil
  | (k, v) :: xs => k :: assoclist_dom xs
  end.

Proposition assoclist_dom_sorted (xs: assoclist):
  heap_prop xs -> Sorted Z.lt (assoclist_dom xs).
Abort.

(*Definition heap_dom (h: heap): Ensemble Z :=
  fun k => In *)

Lemma heap_ind: forall (P : heap -> Prop),
  P heap_empty ->
  (forall (h : heap) (k v: Z),
    P h -> hfun h k = None -> P (heap_update h k v)) ->
  forall h : heap, P h.
intros.
destruct h as (xs & G). induction xs.
- unfold heap_empty in H.
  assert (G = empty). apply proof_irrelevance.
  rewrite H1. apply H.
- destruct a as (k, v).
  inversion G.
  specialize IHxs with H5.
  remember (exist (fun xs : assoclist => heap_prop xs) xs H5) as h.
  specialize H0 with h k v.
  assert (hfun h k = None). apply lookup_minkey.
    rewrite Heqh; simpl. assumption.
  pose proof (H0 IHxs H6); clear H0.
  pose proof (update_cons xs k v H3).
  unfold heap_update in H7; rewrite Heqh in H7; simpl in H7.
  generalize dependent G; rewrite <- H0; intro.
  assert (G = update_heap_prop xs k v H5).
  apply proof_irrelevance.
  rewrite H8. apply H7.
Qed.

Lemma heap_ext: forall (h g: heap),
  (forall n, hfun h n = hfun g n) -> h = g.
intros.
induction g using heap_ind.
- induction h using heap_ind.
  + reflexivity.
  + pose proof (H k); clear H.
    rewrite heap_empty_spec in H1.
    rewrite heap_update_spec1 in H1.
    inversion H1.
- generalize dependent k. generalize dependent v.
  generalize dependent g. induction h using heap_ind; intros.
  + pose proof (H k); clear H.
    rewrite heap_empty_spec in H1.
    rewrite heap_update_spec1 in H1.
    inversion H1.
  + destruct (Z.eq_dec k k0).
    destruct (Z.eq_dec v v0).
    rewrite <- e in *; rewrite <- e0 in *; clear e; clear e0.
Abort.

End FHeap.
