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

(* Heap clear *)
Parameter heap_clear: heap -> Z -> heap.
Axiom heap_clear_spec1: forall h k, hfun (heap_clear h k) k = None.
Axiom heap_clear_spec2: forall h k k',
  k <> k' -> hfun (heap_clear h k) k' = hfun h k'.

(* Domain of heap *)
Parameter heap_dom: heap -> Ensemble Z.
Axiom heap_dom_spec: forall h k, heap_dom h k <-> hfun h k <> None.

(* We have extensional equality for heaps. *)
Axiom heap_ext: forall (h g: heap),
  (forall n, hfun h n = hfun g n) -> h = g.

(* Two heaps may be merged into one (partial operation). *)
(* Parameter merge: heap -> heap -> option heap. *)

End HeapSig.

Module HeapFacts (Import H: HeapSig).

End HeapFacts.

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

Fixpoint clear (xs: assoclist) (k: Z): assoclist :=
  match xs with
  | nil => nil
  | (k', v') :: xs => match k ?= k' with
    | Lt => (k', v') :: clear xs k (* <- may be just xs *)
    | Eq => clear xs k             (* <- if we assume heap_prop *)
    | Gt => (k', v') :: clear xs k
    end
  end.

Proposition clear_minkey (xs: assoclist) (k k': Z):
  minkey k' xs -> minkey k' (clear xs k).
intro. induction xs; simpl; auto.
destruct a as (k0, v0).
simpl in H; destruct H.
remember (k ?= k0); destruct c; symmetry in Heqc; simpl.
apply IHxs; assumption.
split; try assumption. apply IHxs; assumption.
split; try assumption. apply IHxs; assumption.
Qed.

Proposition clear_lookup_same (xs: assoclist) (k: Z):
  lookup (clear xs k) k = None.
induction xs; simpl. reflexivity.
destruct a as (k', v').
remember (k ?= k'); destruct c; symmetry in Heqc; simpl.
assumption.
1: apply -> Z.compare_lt_iff in Heqc.
2: apply Z.compare_gt_iff in Heqc.
all: destruct (Z.eq_dec k k').
1,3: exfalso; eapply Z.lt_irrefl.
1,2: rewrite e in Heqc; apply Heqc.
all: assumption.
Qed.
Proposition clear_lookup_diff (xs: assoclist) (k k': Z):
  k <> k' -> lookup (clear xs k) k' = lookup xs k'.
intros; induction xs; simpl; auto.
destruct a as (k0, v0).
remember (k ?= k0); destruct c; symmetry in Heqc; simpl.
{ apply Z.compare_eq_iff in Heqc.
  rewrite IHxs.
  destruct (Z.eq_dec k' k0).
  exfalso. apply H. rewrite e. apply Heqc.
  reflexivity. }
1: apply -> Z.compare_lt_iff in Heqc.
2: apply Z.compare_gt_iff in Heqc.
all: destruct (Z.eq_dec k' k0); try reflexivity.
all: assumption.
Qed.

Proposition clear_heap_prop (xs: assoclist) (k: Z):
  heap_prop xs -> heap_prop (clear xs k).
intro. induction xs; simpl.
- apply empty.
- destruct a as (k', v').
  remember (k ?= k'); destruct c; symmetry in Heqc.
  + inversion H. apply IHxs; assumption.
  + inversion H. apply insert.
    apply clear_minkey. assumption.
    apply IHxs. assumption.
  + apply Z.compare_gt_iff in Heqc.
    inversion H; clear H0 H1 H3 k0 v xs0.
    pose proof (IHxs H4); clear IHxs.
    apply insert; try assumption.
    apply clear_minkey. assumption.
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

Definition heap_clear (h: heap) (k: Z): heap :=
  let xs := proj1_sig h in
  exist heap_prop (clear xs k) (clear_heap_prop xs k (proj2_sig h)).
Proposition heap_clear_spec1: forall h k,
  hfun (heap_clear h k) k = None.
intros. unfold hfun; unfold heap_clear; simpl.
apply clear_lookup_same.
Qed.
Proposition heap_clear_spec2: forall h k k',
  k <> k' -> hfun (heap_clear h k) k' = hfun h k'.
intros. unfold hfun; unfold heap_clear; simpl.
apply clear_lookup_diff; assumption.
Qed.

Fixpoint assoclist_dom (xs: assoclist): list Z :=
  match xs with
  | nil => nil
  | (k, v) :: xs => k :: assoclist_dom xs
  end.

Proposition assoclist_dom_minkey (xs: assoclist) (k: Z):
  minkey k xs -> ~ In k (assoclist_dom xs).
intro. induction xs.
intro. inversion H0.
destruct a as (k', v'). simpl. intro.
simpl in H; destruct H. destruct H0.
rewrite H0 in H. 
eapply Z.lt_irrefl. apply H.
apply IHxs; assumption.
Qed.

Proposition assoclist_dom_NoDup (xs: assoclist):
  heap_prop xs -> NoDup (assoclist_dom xs).
intro. induction xs. left.
destruct a as (k, v).
simpl. inversion H. right.
apply assoclist_dom_minkey; assumption.
apply IHxs. assumption.
Qed.

Proposition assoclist_dom_sorted (xs: assoclist):
  heap_prop xs -> Sorted Z.lt (assoclist_dom xs).
intro. induction xs; simpl. left.
destruct a as (k, v). inversion H.
right. apply IHxs; assumption.
destruct xs. left.
simpl. destruct p as (k', v').
right. simpl in H2. destruct H2. assumption.
Qed.

Definition heap_dom (h: heap): Ensemble Z :=
  let xs := proj1_sig h in
  fun k => In k (assoclist_dom xs).

Proposition heap_dom_spec: forall h k, heap_dom h k <-> hfun h k <> None.
intros. destruct h as (xs & H); unfold heap_dom; unfold hfun; simpl.
induction xs. simpl.
split; intro; try inversion H0; apply H0; reflexivity.
inversion H.
simpl. destruct (Z.eq_dec k k0).
split; intro. intro. inversion H5.
left. symmetry. assumption.
split; intro. destruct H4.
exfalso. apply n. symmetry; assumption.
apply IHxs; assumption.
right. apply IHxs; assumption.
Qed.

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
intros h g.
destruct h as (xs & H).
destruct g as (ys & G).
unfold hfun. simpl. intro.
cut (xs = ys); [intro|].
generalize dependent H; rewrite H1; intros.
assert (G = H). apply proof_irrelevance. rewrite H2. reflexivity.
generalize dependent ys. induction xs; intros.
- destruct ys.
  reflexivity.
  destruct p as (k, v).
  specialize H0 with k; simpl in H0.
  destruct (Z.eq_dec k k).
  inversion H0. exfalso. apply n. reflexivity.
- destruct ys.
  destruct a as (k, v).
  specialize H0 with k. simpl in H0.
  destruct (Z.eq_dec k k).
  inversion H0. exfalso. apply n. reflexivity.
  destruct a as (k, v).
  destruct p as (k', v').
  destruct (Z.eq_dec k' k).
  destruct (Z.eq_dec v' v).
  { rewrite e in *; rewrite e0 in *; clear e e0 k' v'.
    f_equal.
    inversion H; clear H1 H2 H4 k0 v0 xs0.
    inversion G; clear H1 H2 H6 k0 v0 xs0.
    apply IHxs; try assumption.
    intro.
    specialize H0 with n; simpl in H0.
    destruct (Z.eq_dec n k).
    rewrite lookup_minkey.
    rewrite lookup_minkey.
    reflexivity.
    1,2: rewrite e; assumption.
    assumption. }
  { rewrite e in *; clear e k'.
    specialize H0 with k; simpl in H0.
    destruct (Z.eq_dec k k). inversion H0.
    exfalso. apply n. symmetry; assumption.
    exfalso. apply n0. reflexivity. }
  { exfalso. pose proof (H0 k).
    pose proof (H0 k').
    clear H0. simpl in H1, H2.
    destruct (Z.eq_dec k k).
    destruct (Z.eq_dec k k').
    apply n; symmetry; assumption.
    destruct (Z.eq_dec k' k).
    apply n; assumption.
    destruct (Z.eq_dec k' k').
    2: apply n2; reflexivity.
    2: apply n0; reflexivity.
    clear e n0 n1 e0.
    inversion H; clear H0 H3 H5 k0 v0 xs0.
    inversion G; clear H0 H3 H7 k0 v0 xs0.
    assert (k' < k \/ k < k').
    { destruct (Z.lt_ge_cases k' k).
      left; assumption.
      right. apply Zle_lt_or_eq in H0. destruct H0.
      assumption. exfalso. apply n; symmetry; assumption. }
    destruct H0.
    + pose proof (minkey_trans k' k xs H0 H4).
      pose proof (lookup_minkey xs k' H3).
      rewrite H7 in H2. inversion H2.
    + pose proof (minkey_trans k k' ys H0 H5).
      pose proof (lookup_minkey ys k H3).
      rewrite H7 in H1. inversion H1. }
Qed.

End FHeap.
