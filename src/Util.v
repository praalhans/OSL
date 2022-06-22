(* Copyright 2022 Centrum Wiskunde & Informatica *)

(* ON SEPERATION LOGIC *)
(* Author: Hans-Dieter A. Hiep *)

Require Export FunctionalExtensionality.
Require Export PropExtensionality.
Require Export Structures.Orders.
Require Export List.
Require Export Sorting.
Require Export ZArith.

Definition option_dec {T: Type} (o: option T): {exists x, o = Some x} + {o = None} :=
  match o return ({exists x : T, o = Some x} + {o = None}) with
  | Some t => left (ex_intro (fun x : T => Some t = Some x) t eq_refl)
  | None => right eq_refl
  end.

Definition option_app {T1 T2: Type} (x: option T1) (f: T1 -> option T2): option T2 :=
  match x with
  | Some x => f x
  | None => None
  end.

Proposition option_app_elim {T1 T2: Type} (x: option T1) (f: T1 -> option T2) (z: T2):
  option_app x f = Some z -> exists y: T1, x = Some y /\ f y = Some z.
intros. destruct x.
simpl in H.
exists t. split; auto.
inversion H.
Qed.

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

Proposition not_In_split (T: Type) (xs ys: list T) (x: T):
  ~ In x (xs ++ ys) <-> ~ In x xs /\ ~ In x ys.
split.
intros; split; intro; apply H; apply in_or_app; auto.
intros; destruct H; intro; apply in_app_or in H1; destruct H1; auto.
Qed.

Proposition In_app_split (T: Type) (xs ys zs: list T):
  (forall x, In x xs -> ~ In x (ys ++ zs)) ->
  (forall x, In x xs -> ~ In x ys) /\ (forall x, In x xs -> ~ In x zs).
intros; split;
intros; specialize H with x; apply H in H0;
apply not_In_split in H0; destruct H0; auto.
Qed.

Proposition forall_iff_compat (T: Type) (P P': T -> Prop):
  (forall x : T, P x <-> P' x) ->
  (forall x : T, ~ P x) <-> (forall x : T, ~ P' x).
intros; split; intro;
intros; specialize H0 with x; intro;
apply H0; apply H; assumption.
Qed.

Proposition forall2_iff_compat (T: Type) (P P': T -> T -> Prop):
  (forall x y : T, P x y <-> P' x y) ->
  (forall x y : T, ~ P x y) <-> (forall x y : T, ~ P' x y).
intros; split; intro;
intros; specialize H0 with x y; intro;
apply H0; apply H; assumption.
Qed.

