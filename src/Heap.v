(* Copyright 2022 <anonymized> *)

(* ON SEPARATION LOGIC *)
(* Author: <anonymized> *)

Require Export OnSeparationLogic.Util.

Local Open Scope Z_scope.

(* ======================= *)
(* Axiomatization of heaps *)
(* ======================= *)

(* SEE BEGINNING OF SECTION 2 OF THE PAPER. *)

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

(* We have extensional equality for heaps. *)
Axiom heap_ext: forall (h g: heap),
  (forall n, hfun h n = hfun g n) -> h = g.

(* Domain of heap *)
Parameter dom: heap -> Z -> Prop.
Axiom dom_spec: forall h k, dom h k <-> hfun h k <> None.

(* When a heap can be partitioned in two heaps. *)
Parameter Partition: heap -> heap -> heap -> Prop.
Axiom Partition_spec1: forall h h1 h2, Partition h h1 h2 -> forall k, dom h1 k -> hfun h k = hfun h1 k.
Axiom Partition_spec2: forall h h1 h2, Partition h h1 h2 -> forall k, dom h2 k -> hfun h k = hfun h2 k.
Axiom Partition_spec3: forall h h1 h2, Partition h h1 h2 -> forall k, ~dom h1 k -> ~dom h2 k -> hfun h k = None.
Axiom Partition_spec4: forall h h1 h2, Partition h h1 h2 -> forall k, ~(dom h1 k /\ dom h2 k).
Axiom Partition_intro1: forall h1 h2, (forall k, ~(dom h1 k /\ dom h2 k)) -> exists h, Partition h h1 h2.
(* Needed for intuitionistic semantics: *)
Axiom Partition_intro2: forall h h1, (forall k, dom h1 k -> hfun h k = hfun h1 k) -> exists h2, Partition h h1 h2.

End HeapSig.

Module HeapFacts (Import HS: HeapSig).

Coercion hfun: heap >-> Funclass.

Definition Some_Z (n: Z): option Z := Some n.
Coercion Some_Z: Z >-> option.

Proposition dom_dec (h: heap) (x: Z): dom h x \/ ~dom h x.
rewrite dom_spec.
destruct (h x).
left; intro; inversion H.
right; intro; apply H; reflexivity.
Qed.

Proposition heap_update_dom1 (h: heap) (k v: Z):
  dom (heap_update h k v) k.
apply dom_spec.
rewrite heap_update_spec1.
intro. inversion H.
Qed.

Proposition heap_update_dom2 (h: heap) (k k' v: Z):
  k <> k' -> dom (heap_update h k v) k' <-> dom h k'.
intro.
split; intro.
rewrite dom_spec in H0.
rewrite heap_update_spec2 in H0.
rewrite dom_spec. assumption.
assumption.
rewrite dom_spec.
rewrite heap_update_spec2.
rewrite dom_spec in H0. assumption.
assumption.
Qed.

Proposition heap_update_collapse (h: heap) (k v v': Z):
  heap_update (heap_update h k v) k v' = heap_update h k v'.
apply heap_ext; intro.
destruct (Z.eq_dec k n).
rewrite <- e.
rewrite heap_update_spec1.
rewrite heap_update_spec1.
reflexivity.
rewrite heap_update_spec2; auto.
rewrite heap_update_spec2; auto.
rewrite heap_update_spec2; auto.
Qed.

Proposition heap_update_id (h: heap) (k v: Z):
  h k = Some v -> heap_update h k v = h.
intros.
apply heap_ext; intro.
destruct (Z.eq_dec k n).
rewrite <- e.
rewrite heap_update_spec1; auto.
rewrite heap_update_spec2; auto.
Qed.

Proposition heap_update_clear_collapse (h: heap) (k v: Z):
  ~dom h k -> heap_clear (heap_update h k v) k = h.
intros.
apply heap_ext; intro.
destruct (Z.eq_dec k n).
rewrite <- e.
rewrite heap_clear_spec1.
rewrite dom_spec in H.
destruct (h k); auto. exfalso. apply H. intro. inversion H0.
rewrite heap_clear_spec2; auto.
rewrite heap_update_spec2; auto.
Qed.

Proposition heap_clear_update_collapse (h: heap) (k v: Z):
  h k = Some v -> heap_update (heap_clear h k) k v = h.
intros.
apply heap_ext; intro.
destruct (Z.eq_dec k n).
rewrite <- e.
rewrite heap_update_spec1; auto.
rewrite heap_update_spec2; auto.
rewrite heap_clear_spec2; auto.
Qed.

Proposition heap_clear_dom1 (h: heap) (k: Z):
  ~dom (heap_clear h k) k.
intro.
rewrite dom_spec in H.
rewrite heap_clear_spec1 in H.
apply H; reflexivity.
Qed.

Proposition heap_clear_dom2 (h: heap) (k k': Z):
  k <> k' -> dom (heap_clear h k) k' <-> dom h k'.
intro.
rewrite dom_spec.
rewrite dom_spec.
rewrite heap_clear_spec2.
apply iff_refl.
assumption.
Qed.

Proposition heap_clear_not_dom_eq (h: heap) (k: Z):
  ~dom h k -> h = heap_clear h k.
intros. apply heap_ext; intro.
destruct (Z.eq_dec n k).
rewrite e. rewrite heap_clear_spec1.
rewrite dom_spec in H. destruct (h k); auto.
exfalso. apply H. intro. inversion H0.
rewrite heap_clear_spec2; auto.
Qed.

Proposition Partition_lunique (h h' h1 h2: heap):
  Partition h h1 h2 /\ Partition h' h1 h2 -> h = h'.
intro; destruct H.
apply heap_ext; intro.
pose proof (dom_dec h1 n); destruct H1;
  [|pose proof (dom_dec h2 n); destruct H2].
(* Case analysis: *)
- rewrite (Partition_spec1 _ _ _ H); try assumption.
  rewrite (Partition_spec1 _ _ _ H0); try assumption.
  reflexivity.
- rewrite (Partition_spec2 _ _ _ H); try assumption.
  rewrite (Partition_spec2 _ _ _ H0); try assumption.
  reflexivity.
- rewrite (Partition_spec3 _ _ _ H); try assumption.
  rewrite (Partition_spec3 _ _ _ H0); try assumption.
  reflexivity.
Qed.

Proposition Partition_comm (h h1 h2: heap):
  Partition h h1 h2 -> Partition h h2 h1.
intro.
destruct (Partition_intro1 h2 h1).
intros; rewrite and_comm; eapply Partition_spec4; apply H.
cut (h = x). intro. rewrite H1. assumption.
apply heap_ext; intro.
pose proof (dom_dec h1 n); destruct H1;
  [|pose proof (dom_dec h2 n); destruct H2].
(* Case analysis: *)
- rewrite (Partition_spec1 _ _ _ H); try assumption.
  rewrite (Partition_spec2 _ _ _ H0); try assumption.
  reflexivity.
- rewrite (Partition_spec2 _ _ _ H); try assumption.
  rewrite (Partition_spec1 _ _ _ H0); try assumption.
  reflexivity.
- rewrite (Partition_spec3 _ _ _ H); try assumption.
  rewrite (Partition_spec3 _ _ _ H0); try assumption.
  reflexivity.
Qed.

Proposition Partition_dom_split (h h1 h2: heap) (x: Z):
  Partition h h1 h2 -> dom h x -> dom h1 x \/ dom h2 x.
intros.
destruct (dom_dec h1 x).
left; auto.
destruct (dom_dec h2 x).
right; auto.
apply dom_spec in H0.
exfalso. apply H0.
eapply Partition_spec3.
apply H. assumption. assumption.
Qed.

Proposition Partition_dom_inv_left (h h1 h2: heap) (x: Z):
  Partition h h1 h2 -> dom h1 x -> dom h x.
intros. destruct (dom_dec h x); auto.
exfalso.
pose proof (Partition_spec1 _ _ _ H x H0).
rewrite dom_spec in *. rewrite H2 in H1.
auto.
Qed.

Proposition Partition_dom_inv_right (h h1 h2: heap) (x: Z):
  Partition h h1 h2 -> dom h2 x -> dom h x.
intros. destruct (dom_dec h x); auto.
exfalso.
pose proof (Partition_spec2 _ _ _ H x H0).
rewrite dom_spec in *. rewrite H2 in H1.
auto.
Qed.

Proposition Partition_dom_right1 (h h1 h2: heap) (x: Z):
  Partition h h1 h2 -> dom h1 x -> ~dom h2 x.
intros.
destruct (dom_dec h2 x).
exfalso. eapply Partition_spec4. apply H. split. apply H0. apply H1.
assumption.
Qed.

Proposition Partition_dom_right2 (h h1 h2: heap) (x: Z):
  Partition h h1 h2 -> dom h2 x -> ~dom h1 x.
intros.
destruct (dom_dec h1 x).
exfalso. eapply Partition_spec4. apply H. split. apply H1. apply H0.
assumption.
Qed.

End HeapFacts.

(* ======================= *)
(* Possibly infinite heaps *)
(* ======================= *)

Module IHeap <: HeapSig.

Definition heap := Z -> option Z.
Definition hfun (h: heap) := h.

Definition heap_empty: heap := fun k => None.
Proposition heap_empty_spec: forall n, hfun heap_empty n = None.
unfold hfun; unfold heap_empty; intro; reflexivity.
Qed.

Definition heap_update (h: heap) (k v: Z): heap :=
  fun n => if Z.eq_dec k n then Some v else h n.
Proposition heap_update_spec1: forall h k v, hfun (heap_update h k v) k = Some v.
unfold hfun; unfold heap_update; intros.
destruct (Z.eq_dec k k). reflexivity. exfalso; apply n; reflexivity.
Qed.
Proposition heap_update_spec2: forall h k v k',
  k <> k' -> hfun (heap_update h k v) k' = hfun h k'.
unfold hfun; unfold heap_update; intros.
destruct (Z.eq_dec k k'). exfalso; apply H; assumption. reflexivity.
Qed.

Definition heap_clear (h: heap) (k: Z): heap :=
  fun n => if Z.eq_dec k n then None else h n.
Proposition heap_clear_spec1: forall h k, hfun (heap_clear h k) k = None.
unfold hfun; unfold heap_clear; intros.
destruct (Z.eq_dec k k). reflexivity. exfalso; apply n; reflexivity.
Qed.
Proposition heap_clear_spec2: forall h k k',
  k <> k' -> hfun (heap_clear h k) k' = hfun h k'.
unfold hfun; unfold heap_clear; intros.
destruct (Z.eq_dec k k'). exfalso; apply H; assumption. reflexivity.
Qed.

Proposition heap_ext: forall (h g: heap),
  (forall n, hfun h n = hfun g n) -> h = g.
unfold hfun; intros; apply functional_extensionality; apply H.
Qed.

Definition dom (h: heap) (k: Z): Prop := h k <> None.
Proposition dom_spec: forall h k, dom h k <-> hfun h k <> None.
unfold hfun; unfold dom; intros; apply iff_refl.
Qed.

(* When a heap can be partitioned in two heaps. *)
Definition Partition (h h1 h2: heap): Prop :=
  (forall k, (dom h k -> dom h1 k \/ dom h2 k)) /\
  (forall k, ~(dom h1 k /\ dom h2 k)) /\
  (forall k, dom h1 k -> h k = h1 k) /\
  (forall k, dom h2 k -> h k = h2 k).

Proposition Partition_spec1: forall h h1 h2, Partition h h1 h2 -> forall k, dom h1 k -> hfun h k = hfun h1 k.
unfold Partition; intros; destruct H as (H & (H1 & (H2 & H3))).
apply H2; assumption.
Qed.

Proposition Partition_spec2: forall h h1 h2, Partition h h1 h2 -> forall k, dom h2 k -> hfun h k = hfun h2 k.
unfold Partition; intros; destruct H as (H & (H1 & (H2 & H3))).
apply H3; assumption.
Qed.

Proposition Partition_spec3: forall h h1 h2, Partition h h1 h2 -> forall k, ~dom h1 k -> ~dom h2 k -> hfun h k = None.
unfold Partition; intros; destruct H as (H & (H2 & (H3 & H4))).
remember (h k); destruct o; try reflexivity.
exfalso.
assert (dom h k); unfold dom. intro. rewrite H5 in Heqo. inversion Heqo.
pose proof (H _ H5). destruct H6.
apply H0; assumption.
apply H1; assumption.
unfold hfun; symmetry; assumption.
Qed.

Proposition Partition_spec4: forall h h1 h2, Partition h h1 h2 -> forall k, ~(dom h1 k /\ dom h2 k).
unfold Partition; intros; destruct H as (H & (H1 & (H2 & H3))).
apply H1.
Qed.

Proposition Partition_intro1: forall h1 h2, (forall k, ~(dom h1 k /\ dom h2 k)) -> exists h, Partition h h1 h2.
intros.
exists (fun n => if option_dec (h1 n) then h1 n else h2 n).
unfold Partition; split; [|split; [|split]]; intros.
- unfold dom in *. destruct (option_dec (h1 k)). left; assumption. right; assumption.
- apply H.
- destruct (option_dec (h1 k)). reflexivity.
  exfalso. unfold dom in H0. apply H0; assumption.
- destruct (option_dec (h1 k)).
  destruct e. exfalso. eapply H. split; [|apply H0].
  unfold dom; intro. rewrite H1 in H2. inversion H2.
  reflexivity.
Qed.

Proposition Partition_intro2: forall h h1, (forall k, dom h1 k -> hfun h k = hfun h1 k) -> exists h2, Partition h h1 h2.
intros.
exists (fun n => if option_dec (h1 n) then None else h n).
unfold Partition; split; [|split; [|split]]; intros.
- unfold dom in *. destruct (option_dec (h1 k)).
    left. destruct e. intro. rewrite H1 in H2. inversion H2.
    right; auto.
- unfold dom in *. intro; destruct H0.
  destruct (option_dec (h1 k)). apply H1; auto. apply H0; auto.
- apply H; assumption.
- unfold dom in *. destruct (option_dec (h1 k)).
  exfalso; apply H0; auto. reflexivity.
Qed.

End IHeap.
