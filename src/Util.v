(* Copyright 2022 <anonymized> *)

(* ON SEPARATION LOGIC *)
(* Author: <anonymized> *)

Require Export FunctionalExtensionality.
Require Export PropExtensionality.
Require Export Structures.Orders.
Require Export List.
Require Export Sorting.
Require Export ZArith.

Definition sublist_part_dec {T: Type} (dec: forall x y: T, {x = y} + {x <> y}) (xs: list T) (ys: list T):
  {exists x, In x xs /\ In x ys} + {forall x, In x xs -> ~In x ys}.
induction xs.
right. intros. inversion H.
destruct IHxs.
- left.
  destruct e as (x & H & H0).
  exists x; split.
  right; assumption.
  assumption.
- destruct (in_dec dec a ys).
  left.
  exists a; split.
  left; reflexivity.
  assumption.
  right.
  intros.
  inversion H.
  rewrite <- H0; assumption.
  apply n; assumption.
Defined.

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

Proposition iff_split_and (A B C D: Prop):
  (A <-> C) -> (B <-> D) -> ((A /\ B) <-> (C /\ D)).
intros; split; intros (H1&H2); split.
1,3: apply H; assumption.
all: apply H0; assumption.
Qed.
Proposition iff_split_or (A B C D: Prop):
  (A <-> C) -> (B <-> D) -> ((A \/ B) <-> (C \/ D)).
intros; split; intros H1; destruct H1.
1,3: apply H in H1; left; apply H1.
all: apply H0 in H1; right; apply H1.
Qed.
Proposition iff_split_not_and_not (A B C D: Prop):
  (A <-> C) -> (B <-> D) -> (~(~A /\ ~B) <-> ~(~C /\ ~D)).
intros; split; intros; intro; apply H1; split; intro; destruct H2; tauto.
Qed.
Proposition iff_split_imp (A B C D: Prop):
  (A <-> C) -> (B <-> D) -> ((A -> B) <-> (C -> D)).
intros. split; intros H1 H2.
all: apply H0; apply H1; apply H; assumption.
Qed.
Proposition iff_split_and_exists {T: Type}
    (A B C D: T -> Prop) (H: T -> T -> Prop):
  (forall x, (A x <-> C x)) -> (forall y, (B y <-> D y)) ->
    ((exists x y, H x y /\ A x /\ B y) <->
     (exists x y, H x y /\ C x /\ D y)).
intros; split; intros; destruct H2; destruct H2;
  exists x; exists x0; destruct H2; destruct H3;
  split; try assumption; split.
1,3: apply H0; assumption.
all: apply H1; assumption.
Qed.
Proposition iff_split_and_not_forall_not {T: Type}
    (A B C D: T -> Prop) (H: T -> T -> Prop):
  (forall x, (A x <-> C x)) -> (forall y, (B y <-> D y)) ->
    (~(forall x y, ~(H x y /\ A x /\ B y)) <->
     ~(forall x y, ~(H x y /\ C x /\ D y))).
intros; split; intro; intro; apply H2; intros; intro.
rewrite H0 in H4; rewrite H1 in H4; eapply H3; apply H4.
rewrite <- H0 in H4; rewrite <- H1 in H4; eapply H3; apply H4.
Qed.
Proposition iff_split_imp_forall {T: Type}
    (A B C D: T -> Prop) (H: T -> T -> Prop):
  (forall x, (A x <-> C x)) -> (forall x, (B x <-> D x)) ->
    ((forall x y, H x y -> A y -> B x) <->
     (forall x y, H x y -> C y -> D x)).
intros; split; intros;
apply H2 in H3.
1,3: apply H1; assumption.
all: apply H0; assumption.
Qed.
Proposition iff_split_exists {T: Type} (A B: T -> Prop):
  (forall x, (A x <-> B x)) -> ((exists x, A x) <-> (exists x, B x)).
intro; split; intro; destruct H0; exists x; apply H; assumption.
Qed.
Proposition iff_split_not_forall_not {T: Type} (A B: T -> Prop):
  (forall x, (A x <-> B x)) -> (~(forall x, ~A x) <-> ~(forall x, ~B x)).
intro; split; intro; intro; apply H0; intro; intro; apply H in H2; eapply H1; apply H2.
Qed.
Proposition iff_split_forall {T: Type} (A B: T -> Prop):
  (forall x, (A x <-> B x)) -> ((forall x, A x) <-> (forall x, B x)).
intro; split; intros; apply H; apply H0.
Qed.
Proposition iff_split_forall2 {T: Type} (A B: T -> T -> Prop):
  (forall x y, (A x y <-> B x y)) ->
  ((forall x y, A x y) <-> (forall x y, B x y)).
intro; split; intros; apply H; apply H0.
Qed.

