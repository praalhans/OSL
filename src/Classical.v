(* Copyright 2022 Centrum Wiskunde & Informatica *)

(* ON SEPERATION LOGIC *)
(* Author: Hans-Dieter A. Hiep *)

Require Import FunctionalExtensionality.
Require Import PropExtensionality.
Require Import List.
Require Import ZArith.

Require Import OnSeparationLogic.Heap.
Require Import OnSeparationLogic.Language.

Module Classical (Export HS: HeapSig).

Module L := Language HS.
Include L.

Fixpoint satisfy (h: heap) (s: store) (p: assert): Prop :=
  match p with
  | test g => gval g s = true
  | hasval e e' => dom h (e s) /\ h (e s) = e' s
  | land p q => satisfy h s p /\ satisfy h s q
  | lor p q => ~(~satisfy h s p /\ ~satisfy h s q)
  | limp p q => satisfy h s p -> satisfy h s q
  | lforall x p => forall v, satisfy h (store_update s x v) p
  | lexists x p => ~forall v, ~satisfy h (store_update s x v) p
  | sand p q => ~forall h1 h2, ~(Partition h h1 h2 /\ satisfy h1 s p /\ satisfy h2 s q)
  | simp p q => forall h'' h', Partition h'' h h' -> satisfy h' s p -> satisfy h'' s q
  end.

Proposition satisfy_stable (h: heap) (s: store) (p: assert):
  ~~satisfy h s p -> satisfy h s p.
generalize dependent s. generalize dependent h.
induction p; intros h s; simpl.
- intro. destruct (g s). reflexivity.
  exfalso; apply H; intro; inversion H0.
- intro. destruct (dom_dec h (e s)).
  split. assumption.
  destruct (h (e s)).
  destruct (Z.eq_dec z (e0 s)).
  rewrite e1. reflexivity.
  exfalso. apply H. intro.
  destruct H1. apply n. inversion H2. reflexivity.
  exfalso. apply H. intro.
  destruct H1. inversion H2.
  exfalso. apply H. intro.
  destruct H1. apply H0. assumption.
- intro. split.
  apply IHp1. intro; apply H. intro; destruct H1. apply H0; assumption.
  apply IHp2. intro; apply H. intro; destruct H1. apply H0; assumption.
- intro. intro. apply H. intro. destruct H0.
  apply H1. split; assumption.
- intro. intro. apply IHp2. intro. apply H. intro.
  apply H1. apply H2. assumption.
- intro. intro. apply H. intro.
  apply H1. assumption.
- intro. intro.
  apply IHp. intro. apply H. intro.
  specialize H1 with v0. apply H0. assumption.
- intro. intro. apply H. intro. apply H1. apply H0.
- intros. apply IHp2. intro. apply H. intro.
  apply H2. eapply H3. apply H0. apply H1.
Qed.

(* emp <-> dom h = Empty_set Z *)

(* poitnsto <-> dom h = Singleton Z (eval e s) /\
      h (eval e s) = eval e' s *)

Proposition satisfy_land (h: heap) (s: store) (p q: assert):
  satisfy h s (land p q) <-> satisfy h s p /\ satisfy h s q.
simpl; split; intro; auto.
Qed.

Proposition satisfy_limp (h: heap) (s: store) (p q: assert):
  satisfy h s (limp p q) <-> (satisfy h s p -> satisfy h s q).
simpl; split; intro; auto.
Qed.

Proposition satisfy_lnot (h: heap) (s: store) (p: assert):
  satisfy h s (lnot p) <-> ~satisfy h s p.
simpl; split; intro; intro.
pose proof (H H0). inversion H1.
exfalso. apply H. assumption.
Qed.

Proposition satisfy_lor_intro1 (h: heap) (s: store) (p q: assert):
  satisfy h s p -> satisfy h s (lor p q).
simpl; intro. intro. destruct H0. apply H0; assumption.
Qed.

Proposition satisfy_lor_intro2 (h: heap) (s: store) (p q: assert):
  satisfy h s q -> satisfy h s (lor p q).
simpl; intro. intro. destruct H0. apply H1; assumption.
Qed.

Proposition satisfy_lor_elim (h: heap) (s: store) (p q r: assert):
  satisfy h s (lor p q) -> (satisfy h s p -> satisfy h s r) ->
  (satisfy h s q -> satisfy h s r) -> satisfy h s r.
simpl; intros.
apply satisfy_stable. intro.
apply H. split.
intro. apply H0 in H3. apply H2; assumption.
intro. apply H1 in H3. apply H2; assumption.
Qed.

Proposition satisfy_p_lor_not_p (h: heap) (s: store) (p: assert):
  satisfy h s (lor p (lnot p)).
simpl. intro. destruct H.
apply H0. intro. exfalso. apply H; assumption.
Qed.

Proposition satisfy_lforall (h: heap) (s: store) (x: V) (p: assert):
  satisfy h s (lforall x p) <-> forall v, satisfy h (store_update s x v) p.
simpl. tauto.
Qed.

Proposition satisfy_equals (h: heap) (s: store) (e0 e1: expr):
  satisfy h s (equals e0 e1) <-> e0 s = e1 s.
simpl. destruct (Z.eq_dec (eval e0 s) (eval e1 s)).
rewrite e. tauto. split. intro. inversion H.
intro. exfalso. apply n. assumption.
Qed.

Proposition satisfy_hasvaldash (h: heap) (s: store) (x: V):
  satisfy h s (hasvaldash x) <-> dom h (s x).
split; intro.
- unfold hasvaldash in H.
  remember (fresh (evar x)).
  simpl in H.
  destruct (dom_dec h (s x)). assumption.
  exfalso.
  apply H; clear H; intro; intro; destruct H.
  rewrite store_update_lookup_same in H1.
  rewrite store_update_lookup_diff in H1.
  apply H0. apply dom_spec. rewrite H1. intro. inversion H2.
  intro.
  rewrite H2 in Heqv.
  simpl in Heqv.
  pose proof (fresh_notIn (x :: nil)).
  rewrite <- Heqv in H3.
  apply H3. left. reflexivity.
- simpl. intro.
  remember (h (s x)). destruct o.
  specialize H0 with z.
  apply H0; clear H0.
  assert (store_update s (fresh (x :: nil)) z x = s x).
  rewrite store_update_lookup_diff. reflexivity.
  intro. pose proof (fresh_notIn (x :: nil)).
  apply H1. rewrite H0. left. reflexivity.
  rewrite H0.
  rewrite store_update_lookup_same.
  split; auto.
  eapply dom_spec. apply H. symmetry; assumption.
Qed.

Definition validity (p: assert): Prop := forall h s, satisfy h s p.

Definition strong_partial_correct (p: assert) (S: program) (q: assert) :=
  forall h s, satisfy h s p ->
    ~bigstep S (h, s) None /\
    forall h' s', bigstep S (h, s) (Some (h', s')) -> satisfy h' s' q.

Example out_of_memory (x: V) (e: expr):
  strong_partial_correct (lforall x (hasvaldash x)) (new x e) false.
unfold strong_partial_correct.
intros.
split.
intro.
inversion H0.
intros.
inversion H0.
rewrite satisfy_lforall in H.
specialize (H n).
rewrite satisfy_hasvaldash in H.
rewrite store_update_lookup_same in H.
exfalso. apply H2. assumption.
Qed.

End Classical.
