(* Copyright 2022 <anonymized> *)

(* ON SEPARATION LOGIC *)
(* Author: <anonymized> *)

Require Export OnSeparationLogic.Heap.

Module Language (Export HS: HeapSig).

Module H := HeapFacts HS.
Include H.

(* ========= *)
(* VARIABLES *)
(* ========= *)

Definition V := nat.
Definition dummy: V := 0.

(* ========================================= *)
(* FRESHNESS OF VARIABLES AND ITS PROPERTIES *)
(* ========================================= *)

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
Proposition maximum_In (xs: list V):
  xs <> nil -> In (maximum xs) xs.
intro. destruct xs.
exfalso; apply H; reflexivity.
induction xs.
simpl. left. unfold dummy.
rewrite Nat.max_0_r; reflexivity.
simpl.
assert (In (maximum (v :: xs)) (v :: xs)).
  apply IHxs. intro. inversion H0. clear IHxs.
inversion H0. simpl in H1.
destruct (Nat.max_dec a (maximum xs)).
rewrite e.
destruct (Nat.max_dec v a).
left. auto.
right. left. auto.
left. rewrite e. auto.
destruct (Nat.max_dec a (maximum xs)).
rewrite e.
destruct (Nat.max_dec v a).
left. auto.
right. left. auto.
rewrite e.
right. right. apply H1.
Qed.

Proposition maximum_app (xs ys: list V):
  maximum (xs ++ ys) = max (maximum xs) (maximum ys).
induction xs; simpl. reflexivity.
rewrite IHxs.
apply Nat.max_assoc.
Qed.

Proposition maximum_subset (xs zs: list V):
  (forall x : V, In x xs -> In x zs) -> maximum xs <= maximum zs.
intro. destruct xs.
simpl. unfold dummy.
apply Nat.le_0_l.
pose proof (maximum_prop zs).
pose proof (maximum_In (v :: xs)).
apply H0. apply H. apply H1. intro. inversion H2.
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

Proposition fresh_notInGeneral (xs zs: list V):
  (forall x, In x xs -> In x zs) -> ~In (fresh zs) xs.
intro.
apply maximum_subset in H.
unfold fresh.
intro.
apply maximum_prop in H0.
eapply le_trans in H; [|apply H0].
eapply Nat.nle_succ_diag_l. apply H.
Qed.

(* =========================================== *)
(* THE STORE, STORE UPDATE, AND ITS PROPERTIES *)
(* =========================================== *)

Definition store := V -> Z.

Definition store_update (s: store) (x: V) (v: Z): store :=
  fun y => if Nat.eq_dec x y then v else s y.

Proposition store_update_lookup_same (s: store) (x: V) (v: Z):
  store_update s x v x = v.
unfold store_update.
destruct (Nat.eq_dec x x).
reflexivity.
exfalso. apply n. reflexivity.
Qed.

Proposition store_update_lookup_diff (s: store) (x x': V) (v: Z):
  x <> x' -> store_update s x v x' = s x'.
intros. unfold store_update.
destruct (Nat.eq_dec x x').
exfalso. apply H; assumption.
reflexivity.
Qed.

Proposition store_update_id (s: store) (x: V):
  store_update s x (s x) = s.
apply functional_extensionality; intro.
unfold store_update.
destruct (Nat.eq_dec x x0).
rewrite e; reflexivity.
reflexivity.
Qed.

Proposition store_update_collapse (s: store) (x: V) (v w: Z):
  (store_update (store_update s x v) x w) =
  (store_update s x w).
apply functional_extensionality; intro z.
unfold store_update.
destruct (Nat.eq_dec x z); reflexivity.
Qed.

Proposition store_update_swap (s: store) (e: Z) (x y: V) (v: Z):
  x <> y ->
  (store_update (store_update s x e) y v) =
  (store_update (store_update s y v) x e).
intros G; apply functional_extensionality; intro z.
unfold store_update.
destruct (Nat.eq_dec y z); destruct (Nat.eq_dec x z); try reflexivity.
exfalso. apply G. rewrite e0; rewrite e1. reflexivity.
Qed.

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

Proposition eval_store_update_notInVar (s: store) (e: expr) (x: V) (v: Z):
  ~ In x (evar e) ->
  e s = e (store_update s x v).
intro. apply econd.
intro; intro. unfold store_update.
destruct (Nat.eq_dec x x0).
exfalso; apply H; rewrite e0; assumption.
reflexivity.
Qed.

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

(* ================================== *)
(* INDUCTIVE DEFINITION OF ASSERTIONS *)
(* ================================== *)

Inductive assert :=
| test: guard -> assert
| hasval: expr -> expr -> assert
| land: assert -> assert -> assert
| lor: assert -> assert -> assert
| limp: assert -> assert -> assert
| lexists: V -> assert -> assert
| lforall: V -> assert -> assert
| sand: assert -> assert -> assert
| simp: assert -> assert -> assert.
Coercion test: guard >-> assert.

Definition lnot (p: assert): assert := (limp p false).
Definition lequiv (p q: assert): assert := (land (limp p q) (limp q p)).
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

Fixpoint abound (p: assert): list V :=
  match p with
  | test g => nil
  | hasval e e' => nil
  | land p q => abound p ++ abound q
  | lor p q => abound p ++ abound q
  | limp p q => abound p ++ abound q
  | lexists x p => x :: abound p
  | lforall x p => x :: abound p
  | sand p q => abound p ++ abound q
  | simp p q => abound p ++ abound q
  end.

Fixpoint avar (p: assert): list V :=
  match p with
  | test g => gvar g
  | hasval e e' => evar e ++ evar e'
  | land p q => avar p ++ avar q
  | lor p q => avar p ++ avar q
  | limp p q => avar p ++ avar q
  | lexists x p => remove Nat.eq_dec x (avar p)
  | lforall x p => remove Nat.eq_dec x (avar p)
  | sand p q => avar p ++ avar q
  | simp p q => avar p ++ avar q
  end.

Definition aoccur (p: assert): list V := abound p ++ avar p.

Local Ltac aoccur_generic_bin := intros; unfold aoccur; split; intro H;
match goal with
| H: _ |- _ => apply in_app_or in H; simpl in H; destruct H; apply in_app_or in H; destruct H;
    try (apply in_or_app; left; apply in_or_app; auto; fail);
    try (apply in_or_app; right; apply in_or_app; auto; fail)
end.

Proposition aoccur_split_land (p1 p2: assert):
  forall x, In x (aoccur (land p1 p2)) <-> In x (aoccur p1 ++ aoccur p2).
aoccur_generic_bin.
Qed.

Proposition aoccur_split_lor (p1 p2: assert):
  forall x, In x (aoccur (lor p1 p2)) <-> In x (aoccur p1 ++ aoccur p2).
aoccur_generic_bin.
Qed.

Proposition aoccur_split_limp (p1 p2: assert):
  forall x, In x (aoccur (limp p1 p2)) <-> In x (aoccur p1 ++ aoccur p2).
aoccur_generic_bin.
Qed.

Local Ltac aoccur_generic_quan := intros; simpl; split; intro;
match goal with
| H: ?x = ?y \/ _ |- _ => destruct H; auto; apply in_app_or in H; destruct H;
    try (right; apply in_or_app; auto; fail);
    destruct (Nat.eq_dec x y); auto;
    right; apply in_or_app; right;
    try (apply In_remove; assumption; fail);
    match goal with
     | n: x <> y |- _ => eapply In_remove_elim; [apply n | apply H]
    end
end.

Proposition aoccur_split_lexists (x: V) (p: assert):
  forall y, In y (aoccur (lexists x p)) <-> In y (x :: aoccur p).
aoccur_generic_quan.
Qed.

Proposition aoccur_split_lforall (x: V) (p: assert):
  forall y, In y (aoccur (lforall x p)) <-> In y (x :: aoccur p).
aoccur_generic_quan.
Qed.

Proposition aoccur_split_sand (p1 p2: assert):
  forall x, In x (aoccur (sand p1 p2)) <-> In x (aoccur p1 ++ aoccur p2).
aoccur_generic_bin.
Qed.

Proposition aoccur_split_simp (p1 p2: assert):
  forall x, In x (aoccur (simp p1 p2)) <-> In x (aoccur p1 ++ aoccur p2).
aoccur_generic_bin.
Qed.

Definition Some_assert (p: assert): option assert := Some p.
Coercion Some_assert: assert >-> option.

(* ================================================== *)
(* STANDARD FIRST-ORDER CAPTURE-AVOIDING SUBSTITUTION *)
(* ================================================== *)

Fixpoint asub (p: assert) (x: V) (e: expr): option assert :=
  match p with
  | test g => test (gsub g x e)
  | hasval e1 e2 => hasval (esub e1 x e) (esub e2 x e)
  | land p q => option_app (asub p x e) (fun ps =>
      option_app (asub q x e) (fun qs => land ps qs))
  | lor p q => option_app (asub p x e) (fun ps =>
      option_app (asub q x e) (fun qs => lor ps qs))
  | limp p q => option_app (asub p x e) (fun ps =>
      option_app (asub q x e) (fun qs => limp ps qs))
  | lexists y p => if in_dec Nat.eq_dec y (evar e) then None else
      option_app (asub p (if Nat.eq_dec x y then fresh (avar p) else x) e) (fun ps => lexists y ps)
  | lforall y p => if in_dec Nat.eq_dec y (evar e) then None else
      option_app (asub p (if Nat.eq_dec x y then fresh (avar p) else x) e) (fun ps => lforall y ps)
  | sand p q => option_app (asub p x e) (fun ps =>
      option_app (asub q x e) (fun qs => sand ps qs))
  | simp p q => option_app (asub p x e) (fun ps =>
      option_app (asub q x e) (fun qs => simp ps qs))
  end.

Proposition asub_defined_step1 (C: assert -> assert -> assert) (p1 p2: assert) (x: V) (e: expr)
    (IHp1: forall x : V, (forall x : V, In x (evar e) -> ~ In x (abound p1)) <-> (exists q : assert, asub p1 x e = Some q))
    (IHp2: forall x : V, (forall x : V, In x (evar e) -> ~ In x (abound p2)) <-> (exists q : assert, asub p2 x e = Some q)):
  (forall x0 : V, In x0 (evar e) -> ~ In x0 (abound p1 ++ abound p2)) <->
  (exists q : assert, option_app (asub p1 x e) (fun ps : assert => option_app (asub p2 x e) (fun qs : assert => C ps qs)) = Some q).
split; intros; specialize IHp1 with x; specialize IHp2 with x.
- apply In_app_split in H; destruct H.
  apply IHp1 in H; destruct H.
  apply IHp2 in H0; destruct H0.
  exists (C x0 x1); rewrite H; rewrite H0; reflexivity.
- destruct H.
  apply option_app_elim in H; destruct H; destruct H.
  assert (exists q, asub p1 x e = Some q) by (exists x2; assumption).
  apply option_app_elim in H1; destruct H1; destruct H1.
  assert (exists q, asub p2 x e = Some q) by (exists x3; assumption).
  apply not_In_split; split.
  apply <- IHp1; assumption.
  apply <- IHp2; assumption.
Qed.

Proposition asub_defined_step2 (Q: V -> assert -> assert) (p: assert) (x v: V) (e: expr)
    (IHp: forall x : V, (forall x : V, In x (evar e) -> ~ In x (abound p)) <-> (exists q : assert, asub p x e = Some q)):
  (forall x0 : V, In x0 (evar e) -> ~ (v = x0 \/ In x0 (abound p))) <->
  (exists q : assert, (if in_dec Nat.eq_dec v (evar e) then None else
    option_app (asub p (if Nat.eq_dec x v then fresh (avar p) else x) e) (fun ps : assert => Q v ps)) = Some q).
split; intros.
- assert (forall x : V, In x (evar e) -> ~ In x (abound p)) by
    (intros; intro; eapply H; [apply H0 | auto]).
  destruct (in_dec Nat.eq_dec v (evar e)).
  specialize H with v.
  apply H in i; exfalso; apply i; auto.
  destruct (Nat.eq_dec x v).
  specialize IHp with (fresh (avar p)).
  apply IHp in H0; destruct H0.
  exists (Q v x0); rewrite H0; reflexivity.
  specialize IHp with x.
  apply IHp in H0; destruct H0.
  exists (Q v x0); rewrite H0; reflexivity.
- intro; destruct H; destruct H1.
  rewrite H1 in *; clear H1 v.
  destruct (in_dec Nat.eq_dec x0 (evar e)).
  inversion H.
  apply n; assumption.
  destruct (in_dec Nat.eq_dec v (evar e)).
  inversion H.
  apply option_app_elim in H; destruct H; destruct H.
  destruct (Nat.eq_dec x v).
  assert (exists q, asub p (fresh (avar p)) e = Some q) by (exists x2; assumption).
  eapply IHp in H3; [apply H3; apply H1 | assumption].
  assert (exists q, asub p x e = Some q) by (exists x2; assumption).
  eapply IHp in H3; [apply H3; apply H1 | assumption].
Qed.

Proposition asub_defined (p: assert) (x: V) (e: expr):
  (forall x, In x (evar e) -> ~In x (abound p)) <-> exists q, asub p x e = Some q.
generalize dependent x; induction p; intro x; simpl;
  try (apply asub_defined_step1; assumption; fail);
  try (apply asub_defined_step2; assumption; fail).
- split; intros; auto.
  exists (test (gsub g x e)); reflexivity.
- split; intros; auto.
  exists (hasval (esub e0 x e) (esub e1 x e)); reflexivity.
Qed.

Proposition asub_notInVar (p: assert) (x: V) (e: expr):
  ~In x (evar e) -> forall ps, asub p x e = Some ps -> ~In x (avar ps).
intro. induction p; intros;
try (simpl in H0;
  apply option_app_elim in H0; destruct H0; destruct H0;
  apply option_app_elim in H1; destruct H1; destruct H1;
  inversion H2; simpl;
  intro; apply in_app_or in H3; destruct H3;
  [eapply IHp1; [apply H0 | auto] | eapply IHp2; [apply H1 | auto]]; fail);
try (simpl in H0;
  destruct (in_dec Nat.eq_dec v (evar e)); inversion H0;
  apply option_app_elim in H0; destruct H0; destruct H0;
  inversion H1;
  simpl; intro;
  destruct (Nat.eq_dec x v);
  [eapply remove_In; rewrite e0 in H3; apply H3|
   apply In_remove_elim in H3; auto;
   eapply IHp; [apply H0 | auto]]).
- simpl in H0. inversion H0. unfold avar.
  apply gsub_notInVar. assumption.
- simpl in H0. inversion H0. unfold avar.
  intro. apply in_app_or in H1; destruct H1.
  eapply esub_notInVar. apply H. apply H1.
  eapply esub_notInVar. apply H. apply H1.
Qed.

Proposition abound_asub (p: assert) (x: V) (e: expr):
  ~In x (abound p) -> forall ps, asub p x e = Some ps -> ~ In x (abound ps).
generalize dependent x. induction p; intros; inversion H0; auto;
try (rename H2 into H1;
  apply option_app_elim in H1; destruct H1; destruct H1;
  apply option_app_elim in H2; destruct H2; destruct H2;
  inversion H3;
  simpl; intro; apply in_app_or in H4; destruct H4;
  [eapply IHp1; [intro; apply H; apply in_or_app; left; apply H6 | apply H1 | assumption ]|
   eapply IHp2; [intro; apply H; apply in_or_app; right; apply H6 | apply H2 | assumption ]]);
try (destruct (in_dec Nat.eq_dec v (evar e)); inversion H2; clear H2;
  rename H3 into H1;
  apply option_app_elim in H1; destruct H1; destruct H1;
  destruct (Nat.eq_dec x v);
  [exfalso; apply H; simpl; left; auto|];
  inversion H2; simpl; intro; destruct H3; auto;
  eapply IHp; [intro; apply H; simpl; right; apply H5|
  apply H1|assumption]).
Qed.

Fixpoint areplace (p: assert) (x y: V): assert :=
  match p with
  | test g => test (gsub g x y)
  | hasval e1 e2 => hasval (esub e1 x y) (esub e2 x y)
  | land p q => land (areplace p x y) (areplace q x y)
  | lor p q => lor (areplace p x y) (areplace q x y)
  | limp p q => limp (areplace p x y) (areplace q x y)
  | lexists z p => if Nat.eq_dec x z
      then lexists y (areplace p x y)
      else lexists z (areplace p x y)
  | lforall z p => if Nat.eq_dec x z
      then lforall y (areplace p x y)
      else lforall z (areplace p x y)
  | sand p q => sand (areplace p x y) (areplace q x y)
  | simp p q => simp (areplace p x y) (areplace q x y)
  end.

Proposition areplace_no_occur (p: assert) (x y: V):
  x <> y -> ~In y (aoccur p) -> ~In x (aoccur (areplace p x y)).
intros; induction p; simpl;
try (((rewrite aoccur_split_land in H0;
       rewrite aoccur_split_land) +
      (rewrite aoccur_split_lor in H0;
       rewrite aoccur_split_lor) +
      (rewrite aoccur_split_limp in H0;
       rewrite aoccur_split_limp) +
      (rewrite aoccur_split_sand in H0;
       rewrite aoccur_split_sand) +
      (rewrite aoccur_split_simp in H0;
       rewrite aoccur_split_simp));
  apply not_In_split;
  apply not_In_split in H0; tauto; fail).
- intro; apply in_app_or in H1; destruct H1.
  unfold abound in H1. inversion H1.
  pose proof (gsub_notInVar g x y).
  apply H2; auto. simpl; intro. destruct H3; auto.
- unfold aoccur in *; unfold abound in *; unfold avar in *.
  intro.
  apply in_app_or in H1; destruct H1.
  inversion H1.
  apply in_app_or in H1; destruct H1.
  pose proof (esub_notInVar e x y). apply H2; auto.
  simpl. intro. destruct H3; auto.
  pose proof (esub_notInVar e0 x y). apply H2; auto.
  simpl. intro. destruct H3; auto.
- destruct (Nat.eq_dec x v).
  + simpl; intro; destruct H1.
    apply H; auto.
    apply in_app_or in H1; destruct H1.
    * apply IHp. intro. rewrite aoccur_split_lexists in H0. apply H0.
      right. assumption.
      apply in_or_app; auto.
    * apply IHp. intro. rewrite aoccur_split_lexists in H0. apply H0.
      right. assumption.
      apply in_or_app; auto.
      apply In_remove_elim in H1.
      auto. apply Nat.neq_sym; assumption.
  + simpl. intro. destruct H1.
    apply n; symmetry; apply H1.
    apply in_app_or in H1; destruct H1.
    2: apply In_remove_elim in H1.
    3: apply Nat.neq_sym; assumption.
    all: apply IHp; [intro; rewrite aoccur_split_lexists in H0;
    apply H0; right; assumption | apply in_or_app; auto].
- destruct (Nat.eq_dec x v).
  + simpl; intro; destruct H1.
    apply H; auto.
    apply in_app_or in H1; destruct H1.
    * apply IHp. intro. rewrite aoccur_split_lforall in H0. apply H0.
      right. assumption.
      apply in_or_app; auto.
    * apply IHp. intro. rewrite aoccur_split_lforall in H0. apply H0.
      right. assumption.
      apply in_or_app; auto.
      apply In_remove_elim in H1.
      auto. apply Nat.neq_sym; assumption.
  + simpl. intro. destruct H1.
    apply n; symmetry; apply H1.
    apply in_app_or in H1; destruct H1.
    2: apply In_remove_elim in H1.
    3: apply Nat.neq_sym; assumption.
    all: apply IHp; [intro; rewrite aoccur_split_lforall in H0;
    apply H0; right; assumption | apply in_or_app; auto].
Qed.

(* ======================================================= *)
(* HEAP UPDATE SUBSTITUTION, SEE DEFINITION 2 IN THE PAPER *)
(* ======================================================= *)

Fixpoint asub_heap_update (p: assert) (x: V) (e: expr): option assert :=
  match p with
  | test g => test g
  | hasval e1 e2 => (lor (land (equals x e1) (equals e e2)) (land (lnot (equals x e1)) (hasval e1 e2)))
  | land p q => option_app (asub_heap_update p x e) (fun ps =>
      option_app (asub_heap_update q x e) (fun qs => land ps qs))
  | lor p q => option_app (asub_heap_update p x e) (fun ps =>
      option_app (asub_heap_update q x e) (fun qs => lor ps qs))
  | limp p q => option_app (asub_heap_update p x e) (fun ps =>
      option_app (asub_heap_update q x e) (fun qs => limp ps qs))
  | lexists y p => if in_dec Nat.eq_dec y (x :: evar e) then None else
      option_app (asub_heap_update p x e) (fun ps => lexists y ps)
  | lforall y p => if in_dec Nat.eq_dec y (x :: evar e) then None else
      option_app (asub_heap_update p x e) (fun ps => lforall y ps)
  | sand p q => option_app (asub_heap_update p x e) (fun ps =>
      option_app (asub_heap_update q x e) (fun qs => lor (sand ps (land q (lnot (hasvaldash x))))
        (sand (land p (lnot (hasvaldash x))) qs)))
  | simp p q => if sublist_part_dec Nat.eq_dec (x :: evar e) (abound p) then None else
      option_app (asub_heap_update q x e) (fun qs => simp (land p (lnot (hasvaldash x))) qs)
  end.

Proposition asub_heap_update_defined_step1 (C: assert -> assert -> assert) (p1 p2: assert) (x: V) (e: expr)
    (IHp1: (forall y : V, In y (x :: evar e) -> ~ In y (abound p1)) <-> (exists q : assert, asub_heap_update p1 x e = Some q))
    (IHp2: (forall y : V, In y (x :: evar e) -> ~ In y (abound p2)) <-> (exists q : assert, asub_heap_update p2 x e = Some q)):
  (forall y : V, In y (x :: evar e) -> ~ In y (abound p1 ++ abound p2)) <->
  (exists q : assert, option_app (asub_heap_update p1 x e) (fun ps : assert => option_app (asub_heap_update p2 x e) (fun qs : assert => C ps qs)) = Some q).
split; intros.
- apply In_app_split in H; destruct H.
  apply IHp1 in H; destruct H.
  apply IHp2 in H0; destruct H0.
  exists (C x0 x1); rewrite H; rewrite H0; reflexivity.
- destruct H.
  apply option_app_elim in H; destruct H; destruct H.
  assert (exists q, asub_heap_update p1 x e = Some q) by (exists x1; assumption).
  apply option_app_elim in H1; destruct H1; destruct H1.
  assert (exists q, asub_heap_update p2 x e = Some q) by (exists x2; assumption).
  apply not_In_split; split.
  apply <- IHp1; assumption.
  apply <- IHp2; assumption.
Qed.

Proposition asub_heap_update_defined (p: assert) (x: V) (e: expr):
  (forall y, In y (x :: evar e) -> ~In y (abound p)) <-> exists q, asub_heap_update p x e = Some q.
induction p;
try (apply asub_heap_update_defined_step1; assumption; fail).
- simpl; split; intros.
  eexists; reflexivity. tauto.
- simpl; split; intros.
  eexists; reflexivity. tauto.
- unfold asub_heap_update. fold asub_heap_update.
  destruct (in_dec Nat.eq_dec v (x :: evar e)).
  + split; intro. exfalso. eapply H. apply i.
    simpl. left; reflexivity.
    destruct H. inversion H.
  + split; intro.
    assert (forall y : V, In y (x :: evar e) -> ~ In y (abound p)).
    intros. intro. eapply H. apply H0. simpl. right; assumption.
    apply IHp in H0. destruct H0.
    exists (lexists v x0). rewrite H0. reflexivity.
    destruct H.
    apply option_app_elim in H; destruct H; destruct H.
    assert (exists q : assert, asub_heap_update p x e = Some q) by
      (exists x1; assumption).
    intros.
    eapply IHp in H1; [|apply H2].
    intro. simpl in H3. destruct H3.
    apply n. rewrite H3. assumption.
    apply H1. assumption.
- unfold asub_heap_update. fold asub_heap_update.
  destruct (in_dec Nat.eq_dec v (x :: evar e)).
  + split; intro. exfalso. eapply H. apply i.
    simpl. left; reflexivity.
    destruct H. inversion H.
  + split; intro.
    assert (forall y : V, In y (x :: evar e) -> ~ In y (abound p)).
    intros. intro. eapply H. apply H0. simpl. right; assumption.
    apply IHp in H0. destruct H0.
    exists (lforall v x0). rewrite H0. reflexivity.
    destruct H.
    apply option_app_elim in H; destruct H; destruct H.
    assert (exists q : assert, asub_heap_update p x e = Some q) by
      (exists x1; assumption).
    intros.
    eapply IHp in H1; [|apply H2].
    intro. simpl in H3. destruct H3.
    apply n. rewrite H3. assumption.
    apply H1. assumption.
- split; intros.
  + unfold abound in H; fold abound in H.
    apply In_app_split in H. destruct H.
    apply IHp2 in H0; destruct H0.
    exists (simp (land p1 (lnot (hasvaldash x))) x0).
    unfold asub_heap_update. fold asub_heap_update. rewrite H0.
    destruct (sublist_part_dec Nat.eq_dec (x :: evar e) (abound p1)).
    destruct e0 as (x1 & H1 & H2).
    exfalso; eapply H. apply H1. apply H2.
    reflexivity.
  + destruct H.
    unfold asub_heap_update in H; fold asub_heap_update in H.
    destruct (sublist_part_dec Nat.eq_dec (x :: evar e) (abound p1)).
    inversion H.
    apply option_app_elim in H; destruct H; destruct H.
    assert (exists q : assert, asub_heap_update p2 x e = Some q) by
      (exists x1; assumption).
    rewrite <- IHp2 in H2.
    simpl. intro. apply in_app_or in H3; destruct H3.
    eapply n. apply H0. apply H3.
    eapply H2. apply H0. apply H3.
Qed.

(* ====================================================== *)
(* HEAP CLEAR SUBSTITUTION, SEE DEFINITION 3 IN THE PAPER *)
(* ====================================================== *)

Fixpoint asub_heap_clear (p: assert) (x: V): option assert :=
  match p with
  | test g => test g
  | hasval e1 e2 => (land (lnot (equals x e1)) (hasval e1 e2))
  | land p q => option_app (asub_heap_clear p x) (fun ps =>
      option_app (asub_heap_clear q x) (fun qs => land ps qs))
  | lor p q => option_app (asub_heap_clear p x) (fun ps =>
      option_app (asub_heap_clear q x) (fun qs => lor ps qs))
  | limp p q => option_app (asub_heap_clear p x) (fun ps =>
      option_app (asub_heap_clear q x) (fun qs => limp ps qs))
  | lexists y p => if Nat.eq_dec y x then None else
      option_app (asub_heap_clear p x) (fun ps => lexists y ps)
  | lforall y p => if Nat.eq_dec y x then None else
      option_app (asub_heap_clear p x) (fun ps => lforall y ps)
  | sand p q => option_app (asub_heap_clear p x) (fun ps =>
      option_app (asub_heap_clear q x) (fun qs => sand ps qs))
  | simp p q => let y := fresh (x :: aoccur p ++ aoccur q) in
      option_app (asub_heap_clear q x) (fun qs =>
        option_app (asub_heap_update p x y) (fun pss =>
          option_app (asub_heap_update q x y) (fun qss =>
            (land (simp (land p (lnot (hasvaldash x))) qs) (lforall y (simp pss qss))))))
  end.

Proposition asub_heap_clear_defined_step1 (C: assert -> assert -> assert) (p1 p2: assert) (x: V)
    (IHp1: ~ In x (abound p1) <-> (exists q : assert, asub_heap_clear p1 x = Some q))
    (IHp2: ~ In x (abound p2) <-> (exists q : assert, asub_heap_clear p2 x = Some q)):
  ~ In x (abound p1 ++ abound p2) <-> (exists q : assert, option_app (asub_heap_clear p1 x)
    (fun ps : assert => option_app (asub_heap_clear p2 x) (fun qs : assert => C ps qs)) = Some q).
split; intros.
- assert (~In x (abound p1)) by
    (intro; apply H; apply in_or_app; auto).
  assert (~In x (abound p2)) by
    (intro; apply H; apply in_or_app; auto).
  rewrite IHp1 in H0; rewrite IHp2 in H1.
  destruct H0; destruct H1.
  exists (C x0 x1).
  rewrite H0; rewrite H1.
  reflexivity.
- destruct H.
  apply option_app_elim in H; destruct H; destruct H.
  apply option_app_elim in H0; destruct H0; destruct H0.
  intro. apply in_app_or in H2. destruct H2.
  apply <- IHp1; auto. exists x1; auto.
  apply <- IHp2; auto. exists x2; auto.
Qed.

Proposition asub_heap_clear_defined_step2 (Q: V -> assert -> assert) (p: assert) (x v: V)
    (IHp: ~ In x (abound p) <-> (exists q : assert, asub_heap_clear p x = Some q)):
  ~ (v = x \/ In x (abound p)) <->
  (exists q : assert, (if Nat.eq_dec v x then None else option_app (asub_heap_clear p x) (fun ps : assert => Q v ps)) = Some q).
split; intro.
- destruct (Nat.eq_dec v x).
  exfalso; apply H; auto.
  assert (~In x (abound p)) by
    (intro; apply H; auto).
  rewrite IHp in H0; destruct H0.
  exists (Q v x0); rewrite H0; reflexivity.
- destruct (Nat.eq_dec v x); destruct H.
  inversion H.
  apply option_app_elim in H; destruct H; destruct H.
  intro; destruct H1.
  apply n; auto.
  apply <- IHp.
  exists x1; auto.
  auto.
Qed.

Proposition asub_heap_clear_defined (p: assert) (x: V):
  ~In x (abound p) <-> exists q, asub_heap_clear p x = Some q.
induction p;
try (apply asub_heap_clear_defined_step1; assumption; fail);
try (apply asub_heap_clear_defined_step2; assumption; fail).
- simpl; split; intros.
  eexists; reflexivity. tauto.
- simpl; split; intros.
  eexists; reflexivity. tauto.
- simpl. split; intros.
  + assert (~In x (abound p2)) by
    (intro; apply H; apply in_or_app; auto).
    rewrite IHp2 in H0. destruct H0.
    remember (fresh (x :: aoccur p1 ++ aoccur p2)).
    pose proof (asub_heap_update_defined p1 x v).
    assert (forall y : V, In y (x :: evar v) -> ~ In y (abound p1)).
    { intros. inversion H2. rewrite <- H3.
      intro. apply H. apply in_or_app; auto.
      simpl in H3. destruct H3; auto.
      rewrite <- H3. rewrite Heqv.
      unfold aoccur.
      apply fresh_notInGeneral.
        intros. right. apply in_or_app. left.
        apply in_or_app. left. assumption. }
    apply H1 in H2. destruct H2.
    pose proof (asub_heap_update_defined p2 x v).
    assert (forall y : V, In y (x :: evar v) -> ~ In y (abound p2)).
    { intros. inversion H4. rewrite <- H5.
      intro. apply H. apply in_or_app; auto.
      simpl in H5. destruct H5; auto.
      rewrite <- H5. rewrite Heqv.
      unfold aoccur.
      apply fresh_notInGeneral.
        intros. right. apply in_or_app. right.
        apply in_or_app. left. assumption. }
    apply H3 in H4. destruct H4.
    exists (land (simp (land p1 (lnot (hasvaldash x))) x0) (lforall v (simp x1 x2))).
    rewrite H0. simpl. rewrite H2. simpl. rewrite H4. simpl. reflexivity.
  + destruct H.
    apply option_app_elim in H; destruct H; destruct H.
    apply option_app_elim in H0; destruct H0; destruct H0.
    assert (~ In x (abound p1)).
     pose proof (asub_heap_update_defined p1 x (fresh (x :: aoccur p1 ++ aoccur p2))).
      apply <- H2. exists x2; auto. left; auto.
    assert (~ In x (abound p2)).
      apply <- IHp2. exists x1; auto.
    intro. apply in_app_or in H4. destruct H4.
    apply H2; auto. apply H3; auto.
Qed.

(* ==================================== *)
(* CONDITIONAL HEAP UPDATE SUBSTITUTION *)
(* ==================================== *)

Fixpoint asub_cheap_update (p: assert) (x: V) (e: expr): option assert :=
  match p with
  | test g => test g
  | hasval e1 e2 => (lor (land (equals x e1) (equals e e2)) (land (lnot (equals x e1)) (hasval e1 e2)))
  | land p q => option_app (asub_cheap_update p x e) (fun ps =>
      option_app (asub_cheap_update q x e) (fun qs => land ps qs))
  | lor p q => option_app (asub_cheap_update p x e) (fun ps =>
      option_app (asub_cheap_update q x e) (fun qs => lor ps qs))
  | limp p q => option_app (asub_cheap_update p x e) (fun ps =>
      option_app (asub_cheap_update q x e) (fun qs => limp ps qs))
  | lexists y p => if in_dec Nat.eq_dec y (x :: evar e) then None else
      option_app (asub_cheap_update p x e) (fun ps => lexists y ps)
  | lforall y p => if in_dec Nat.eq_dec y (x :: evar e) then None else
      option_app (asub_cheap_update p x e) (fun ps => lforall y ps)
  | sand p q => option_app (asub_cheap_update p x e) (fun ps =>
      option_app (asub_cheap_update q x e) (fun qs =>
        lor (sand (land ps (hasvaldash x)) q) (sand p (land qs (hasvaldash x)))))
  | simp p q => if sublist_part_dec Nat.eq_dec (x :: evar e) (abound p) then None else
      option_app (asub_cheap_update q x e) (fun qs => simp p qs)
  end.

Proposition asub_cheap_update_defined_step1 (C: assert -> assert -> assert) (p1 p2: assert) (x: V) (e: expr)
    (IHp1: (forall y : V, In y (x :: evar e) -> ~ In y (abound p1)) <-> (exists q : assert, asub_cheap_update p1 x e = Some q))
    (IHp2: (forall y : V, In y (x :: evar e) -> ~ In y (abound p2)) <-> (exists q : assert, asub_cheap_update p2 x e = Some q)):
  (forall y : V, In y (x :: evar e) -> ~ In y (abound p1 ++ abound p2)) <->
  (exists q : assert, option_app (asub_cheap_update p1 x e) (fun ps : assert => option_app (asub_cheap_update p2 x e) (fun qs : assert => C ps qs)) = Some q).
split; intros.
- apply In_app_split in H; destruct H.
  apply IHp1 in H; destruct H.
  apply IHp2 in H0; destruct H0.
  exists (C x0 x1); rewrite H; rewrite H0; reflexivity.
- destruct H.
  apply option_app_elim in H; destruct H; destruct H.
  assert (exists q, asub_cheap_update p1 x e = Some q) by (exists x1; assumption).
  apply option_app_elim in H1; destruct H1; destruct H1.
  assert (exists q, asub_cheap_update p2 x e = Some q) by (exists x2; assumption).
  apply not_In_split; split.
  apply <- IHp1; assumption.
  apply <- IHp2; assumption.
Qed.

Proposition asub_cheap_update_defined (p: assert) (x: V) (e: expr):
  (forall y, In y (x :: evar e) -> ~In y (abound p)) <-> exists q, asub_cheap_update p x e = Some q.
induction p;
try (apply asub_cheap_update_defined_step1; assumption; fail).
- simpl; split; intros.
  eexists; reflexivity. tauto.
- simpl; split; intros.
  eexists; reflexivity. tauto.
- unfold asub_cheap_update. fold asub_cheap_update.
  destruct (in_dec Nat.eq_dec v (x :: evar e)).
  + split; intro. exfalso. eapply H. apply i.
    simpl. left; reflexivity.
    destruct H. inversion H.
  + split; intro.
    assert (forall y : V, In y (x :: evar e) -> ~ In y (abound p)).
    intros. intro. eapply H. apply H0. simpl. right; assumption.
    apply IHp in H0. destruct H0.
    exists (lexists v x0). rewrite H0. reflexivity.
    destruct H.
    apply option_app_elim in H; destruct H; destruct H.
    assert (exists q : assert, asub_cheap_update p x e = Some q) by
      (exists x1; assumption).
    intros.
    eapply IHp in H1; [|apply H2].
    intro. simpl in H3. destruct H3.
    apply n. rewrite H3. assumption.
    apply H1. assumption.
- unfold asub_cheap_update. fold asub_cheap_update.
  destruct (in_dec Nat.eq_dec v (x :: evar e)).
  + split; intro. exfalso. eapply H. apply i.
    simpl. left; reflexivity.
    destruct H. inversion H.
  + split; intro.
    assert (forall y : V, In y (x :: evar e) -> ~ In y (abound p)).
    intros. intro. eapply H. apply H0. simpl. right; assumption.
    apply IHp in H0. destruct H0.
    exists (lforall v x0). rewrite H0. reflexivity.
    destruct H.
    apply option_app_elim in H; destruct H; destruct H.
    assert (exists q : assert, asub_cheap_update p x e = Some q) by
      (exists x1; assumption).
    intros.
    eapply IHp in H1; [|apply H2].
    intro. simpl in H3. destruct H3.
    apply n. rewrite H3. assumption.
    apply H1. assumption.
- split; intros.
  + unfold abound in H; fold abound in H.
    apply In_app_split in H. destruct H.
    apply IHp2 in H0; destruct H0.
    exists (simp p1 x0).
    unfold asub_cheap_update. fold asub_cheap_update. rewrite H0.
    destruct (sublist_part_dec Nat.eq_dec (x :: evar e) (abound p1)).
    destruct e0 as (x1 & H1 & H2).
    exfalso; eapply H. apply H1. apply H2.
    reflexivity.
  + destruct H.
    unfold asub_cheap_update in H; fold asub_cheap_update in H.
    destruct (sublist_part_dec Nat.eq_dec (x :: evar e) (abound p1)).
    inversion H.
    apply option_app_elim in H; destruct H; destruct H.
    assert (exists q : assert, asub_cheap_update p2 x e = Some q) by
      (exists x1; assumption).
    rewrite <- IHp2 in H2.
    simpl. intro. apply in_app_or in H3; destruct H3.
    eapply n. apply H0. apply H3.
    eapply H2. apply H0. apply H3.
Qed.

(* ======================================= *)
(* INTUITIONISTIC HEAP UPDATE SUBSTITUTION *)
(* ======================================= *)

Definition asub_iheap_update (p: assert) (x: V) (e: expr): option assert :=
  match asub_cheap_update p x e with
  | None => None
  | Some ps => limp (hasvaldash x) ps
  end.

Proposition asub_iheap_update_defined (p: assert) (x: V) (e: expr):
  (forall y, In y (x :: evar e) -> ~In y (abound p)) <-> exists q, asub_iheap_update p x e = Some q.
split; intro.
- rewrite (asub_cheap_update_defined p x e) in H; destruct H.
  exists (limp (hasvaldash x) x0).
  unfold asub_iheap_update.
  rewrite H; reflexivity.
- destruct H.
  unfold asub_iheap_update in H.
  remember (asub_cheap_update p x e). destruct o.
  symmetry in Heqo.
  assert (exists q, asub_cheap_update p x e = Some q)
    by (exists a; auto).
  rewrite <- (asub_cheap_update_defined p x e) in H0; auto.
  inversion H.
Qed.

(* =================================== *)
(* CONDITIONAL HEAP CLEAR SUBSTITUTION *)
(* =================================== *)

Fixpoint asub_cheap_clear (p: assert) (x: V): option assert :=
  match p with
  | test g => test g
  | hasval e1 e2 => (land (lnot (equals x e1)) (hasval e1 e2))
  | land p q => option_app (asub_cheap_clear p x) (fun ps =>
      option_app (asub_cheap_clear q x) (fun qs => land ps qs))
  | lor p q => option_app (asub_cheap_clear p x) (fun ps =>
      option_app (asub_cheap_clear q x) (fun qs => lor ps qs))
  | limp p q => let y := fresh (x :: aoccur p ++ aoccur q) in
      option_app (asub_cheap_clear p x) (fun ps =>
        option_app (asub_cheap_clear q x) (fun qs =>
          option_app (asub_cheap_update p x y) (fun pss => 
            option_app (asub_cheap_update q x y) (fun qss =>
              (land (limp ps qs) (lforall y (limp pss qss)))))))
  | lexists y p => if Nat.eq_dec y x then None else
      option_app (asub_cheap_clear p x) (fun ps => lexists y ps)
  | lforall y p => if Nat.eq_dec y x then None else
      option_app (asub_cheap_clear p x) (fun ps => lforall y ps)
  | sand p q => if in_dec Nat.eq_dec x (abound p) then None else
      option_app (asub_cheap_clear q x) (fun qs =>
        sand p (land qs (hasvaldash x)))
  | simp p q => let y := fresh (x :: aoccur p ++ aoccur q) in
      option_app (asub_cheap_clear q x) (fun qs =>
        option_app (asub_iheap_update p x y) (fun pss =>
          option_app (asub_iheap_update q x y) (fun qss =>
            (land (simp p qs) (lforall y (simp pss qss))))))
  end.

Proposition asub_cheap_clear_defined_step1 (C: assert -> assert -> assert) (p1 p2: assert) (x: V)
    (IHp1: ~ In x (abound p1) <-> (exists q : assert, asub_cheap_clear p1 x = Some q))
    (IHp2: ~ In x (abound p2) <-> (exists q : assert, asub_cheap_clear p2 x = Some q)):
  ~ In x (abound p1 ++ abound p2) <-> (exists q : assert, option_app (asub_cheap_clear p1 x)
    (fun ps : assert => option_app (asub_cheap_clear p2 x) (fun qs : assert => C ps qs)) = Some q).
split; intros.
- assert (~In x (abound p1)) by
    (intro; apply H; apply in_or_app; auto).
  assert (~In x (abound p2)) by
    (intro; apply H; apply in_or_app; auto).
  rewrite IHp1 in H0; rewrite IHp2 in H1.
  destruct H0; destruct H1.
  exists (C x0 x1).
  rewrite H0; rewrite H1.
  reflexivity.
- destruct H.
  apply option_app_elim in H; destruct H; destruct H.
  apply option_app_elim in H0; destruct H0; destruct H0.
  intro. apply in_app_or in H2. destruct H2.
  apply <- IHp1; auto. exists x1; auto.
  apply <- IHp2; auto. exists x2; auto.
Qed.

Proposition asub_cheap_clear_defined_step2 (Q: V -> assert -> assert) (p: assert) (x v: V)
    (IHp: ~ In x (abound p) <-> (exists q : assert, asub_cheap_clear p x = Some q)):
  ~ (v = x \/ In x (abound p)) <->
  (exists q : assert, (if Nat.eq_dec v x then None else option_app (asub_cheap_clear p x) (fun ps : assert => Q v ps)) = Some q).
split; intro.
- destruct (Nat.eq_dec v x).
  exfalso; apply H; auto.
  assert (~In x (abound p)) by
    (intro; apply H; auto).
  rewrite IHp in H0; destruct H0.
  exists (Q v x0); rewrite H0; reflexivity.
- destruct (Nat.eq_dec v x); destruct H.
  inversion H.
  apply option_app_elim in H; destruct H; destruct H.
  intro; destruct H1.
  apply n; auto.
  apply <- IHp.
  exists x1; auto.
  auto.
Qed.

Proposition asub_cheap_clear_defined (p: assert) (x: V):
  ~In x (abound p) <-> exists q, asub_cheap_clear p x = Some q.
induction p;
try (apply asub_cheap_clear_defined_step1; assumption; fail);
try (apply asub_cheap_clear_defined_step2; assumption; fail).
- simpl; split; intros.
  eexists; reflexivity. tauto.
- simpl; split; intros.
  eexists; reflexivity. tauto.
- simpl. split; intros.
  + assert (~In x (abound p1)) by
    (intro; apply H; apply in_or_app; auto).
    rewrite IHp1 in H0; destruct H0.
    assert (~In x (abound p2)) by
    (intro; apply H; apply in_or_app; auto).
    rewrite IHp2 in H1; destruct H1.
    remember (fresh (x :: aoccur p1 ++ aoccur p2)).
    pose proof (asub_cheap_update_defined p1 x v).
    assert (forall y : V, In y (x :: evar v) -> ~ In y (abound p1)).
    { intros. inversion H3. rewrite <- H4.
      intro. apply H. apply in_or_app; auto.
      simpl in H4. destruct H4; auto.
      rewrite <- H4. rewrite Heqv.
      unfold aoccur.
      apply fresh_notInGeneral.
        intros. right. apply in_or_app. left.
        apply in_or_app. left. assumption. }
    apply H2 in H3; clear H2; destruct H3.
    pose proof (asub_cheap_update_defined p2 x v).
    assert (forall y : V, In y (x :: evar v) -> ~ In y (abound p2)).
    { intros. inversion H4. rewrite <- H5.
      intro. apply H. apply in_or_app; auto.
      simpl in H5. destruct H5; auto.
      rewrite <- H5. rewrite Heqv.
      unfold aoccur.
      apply fresh_notInGeneral.
        intros. right. apply in_or_app. right.
        apply in_or_app. left. assumption. }
    apply H3 in H4; clear H3; destruct H4.
    exists (land (limp x0 x1) (lforall v (limp x2 x3))).
    rewrite H0; simpl.
    rewrite H1; simpl.
    rewrite H2; simpl.
    rewrite H3; simpl.
    reflexivity.
  + destruct H.
    apply option_app_elim in H; destruct H; destruct H.
    apply option_app_elim in H0; destruct H0; destruct H0.
    assert (exists q, asub_cheap_clear p1 x = Some q) by
      (exists x1; auto).
    assert (exists q, asub_cheap_clear p2 x = Some q) by
      (exists x2; auto).
    apply IHp1 in H2.
    apply IHp2 in H3.
    intro. apply in_app_or in H4; destruct H4.
    tauto. tauto.
- simpl. split; intros.
  + assert (~In x (abound p2)) by
    (intro; apply H; apply in_or_app; auto).
    rewrite IHp2 in H0. destruct H0.
    exists (sand p1 (land x0 (hasvaldash x))).
    rewrite H0. simpl.
    destruct (in_dec Nat.eq_dec x (abound p1)).
    exfalso. apply H. apply in_or_app; auto.
    reflexivity.
  + destruct H.
    destruct (in_dec Nat.eq_dec x (abound p1)).
    inversion H.
    intro. apply in_app_or in H0. destruct H0.
    apply n; auto.
    apply option_app_elim in H; destruct H; destruct H.
    assert (exists q, asub_cheap_clear p2 x = Some q).
    exists x1; auto.
    apply IHp2 in H2.
    apply H2; auto.
- simpl. split; intros.
  + assert (~In x (abound p2)) by
    (intro; apply H; apply in_or_app; auto).
    rewrite IHp2 in H0. destruct H0.
    remember (fresh (x :: aoccur p1 ++ aoccur p2)).
    pose proof (asub_iheap_update_defined p1 x v).
    assert (forall y : V, In y (x :: evar v) -> ~ In y (abound p1)).
    { intros. inversion H2. rewrite <- H3.
      intro. apply H. apply in_or_app; auto.
      simpl in H3. destruct H3; auto.
      rewrite <- H3. rewrite Heqv.
      unfold aoccur.
      apply fresh_notInGeneral.
        intros. right. apply in_or_app. left.
        apply in_or_app. left. assumption. }
    apply H1 in H2; clear H1; destruct H2.
    pose proof (asub_iheap_update_defined p2 x v).
    assert (forall y : V, In y (x :: evar v) -> ~ In y (abound p2)).
    { intros. inversion H3. rewrite <- H4.
      intro. apply H. apply in_or_app; auto.
      simpl in H4. destruct H4; auto.
      rewrite <- H4. rewrite Heqv.
      unfold aoccur.
      apply fresh_notInGeneral.
        intros. right. apply in_or_app. right.
        apply in_or_app. left. assumption. }
    apply H2 in H3; clear H2; destruct H3.
    exists (land (simp p1 x0) (lforall v (simp x1 x2))).
    rewrite H0. simpl. rewrite H1. simpl. rewrite H2. simpl. reflexivity.
  + destruct H.
    apply option_app_elim in H; destruct H; destruct H.
    apply option_app_elim in H0; destruct H0; destruct H0.
    apply option_app_elim in H1; destruct H1; destruct H1.
    assert (~ In x (abound p1)).
      pose proof (asub_iheap_update_defined p1 x (fresh (x :: aoccur p1 ++ aoccur p2))).
      apply <- H3. exists x2; auto. left; auto.
    assert (~ In x (abound p2)).
      apply <- IHp2. exists x1; auto.
    intro. apply in_app_or in H5. destruct H5.
    apply H3; auto. apply H4; auto.
Qed.

(* ===================================== *)
(* BASIC INSTRUCTIONS AND WHILE PROGRAMS *)
(* ===================================== *)

Inductive assignment :=
| basic: V -> expr -> assignment
| lookup: V -> expr -> assignment
| mutation: V -> expr -> assignment
| new: V -> expr -> assignment
| dispose: V -> assignment.

Definition asvar (a: assignment): list V :=
  match a with
  | basic x e => x :: evar e
  | lookup x e => x :: evar e
  | mutation x e => x :: evar e
  | new x e => x :: evar e
  | dispose x => x :: nil
  end.

Inductive program :=
| assign: assignment -> program
| diverge: program
| skip: program
| comp: program -> program -> program
| ite: guard -> program -> program -> program
| while: guard -> program -> program.
Coercion assign: assignment >-> program.

Fixpoint pvar (p: program): list V :=
  match p with
  | assign a => asvar a
  | diverge => nil
  | skip => nil
  | comp S1 S2 => pvar S1 ++ pvar S2
  | ite g S1 S2 => gvar g ++ pvar S1 ++ pvar S2
  | while g S1 => gvar g ++ pvar S1
  end.

(* ================================================ *)
(* SEMANTICS OF PROGRAMS, SEE FIGURE 1 IN THE PAPER *)
(* ================================================ *)

Inductive bigstep: program -> heap * store -> option (heap * store) -> Prop :=
| step_basic (x: V) (e: expr) (h: heap) (s: store):
    bigstep (basic x e) (h, s) (Some (h, store_update s x (eval e s)))
| step_lookup (x: V) (e: expr) (h: heap) (s: store) (v: Z):
    h (eval e s) = Some v ->
    bigstep (lookup x e) (h, s) (Some (h, store_update s x v))
| step_lookup_fail (x: V) (e: expr) (h: heap) (s: store):
    h (eval e s) = None ->
    bigstep (lookup x e) (h, s) None
| step_mutation (x: V) (e: expr) (h: heap) (s: store):
    dom h (s x) ->
    bigstep (mutation x e) (h, s) (Some (heap_update h (s x) (eval e s), s))
| step_mutation_fail (x: V) (e: expr) (h: heap) (s: store):
    ~dom h (s x) ->
    bigstep (mutation x e) (h, s) None
| step_new (x: V) (e: expr) (h: heap) (s: store) (n: Z):
    ~(dom h n) ->
    bigstep (new x e) (h, s)
      (Some (heap_update h n (eval e s), store_update s x n))
| step_dispose (x: V) (h: heap) (s: store):
    dom h (s x) ->
    bigstep (dispose x) (h, s) (Some (heap_clear h (s x), s))
| step_dispose_fail (x: V) (h: heap) (s: store):
    ~dom h (s x) ->
    bigstep (dispose x) (h, s) None
| step_skip (h: heap) (s: store):
    bigstep skip (h, s) (Some (h, s))
| step_comp (S1 S2: program) (h h' h'': heap) (s s' s'': store):
    bigstep S1 (h, s) (Some (h', s')) ->
    bigstep S2 (h', s') (Some (h'', s'')) ->
    bigstep (comp S1 S2) (h, s) (Some (h'', s''))
| step_comp_fail1 (S1 S2: program) (h: heap) (s: store):
    bigstep S1 (h, s) None ->
    bigstep (comp S1 S2) (h, s) None
| step_comp_fail2 (S1 S2: program) (h h': heap) (s s': store):
    bigstep S1 (h, s) (Some (h', s')) ->
    bigstep S2 (h', s') None ->
    bigstep (comp S1 S2) (h, s) None
| step_ite_true (g: guard) (S1 S2: program) (h: heap) (s: store) o:
    g s = true ->
    bigstep S1 (h, s) o ->
    bigstep (ite g S1 S2) (h, s) o
| step_ite_false (g: guard) (S1 S2: program) (h: heap) (s: store) o:
    g s = false ->
    bigstep S2 (h, s) o ->
    bigstep (ite g S1 S2) (h, s) o
| step_while_true (g: guard) (S1: program) (h h': heap) (s s': store) o:
    g s = true ->
    bigstep S1 (h, s) (Some (h', s')) ->
    bigstep (while g S1) (h', s') o ->
    bigstep (while g S1) (h, s) o
| step_while_false (g: guard) (S1: program) (h: heap) (s: store):
    g s = false ->
    bigstep (while g S1) (h, s) (Some (h, s))
| step_while_fail (g: guard) (S1: program) (h: heap) (s: store):
    g s = true ->
    bigstep S1 (h, s) None ->
    bigstep (while g S1) (h, s) None.

Proposition diverge_empty (h: heap) (s: store):
  forall o, ~bigstep diverge (h, s) o.
intros; intro; inversion H.
Qed.

Fixpoint approx (n: nat) (g: guard) (S1: program): program :=
  match n with
  | O => diverge
  | S m => ite g (comp S1 (approx m g S1)) skip
  end.

Proposition while_approx (g: guard) (S1: program):
  forall h s o,
    bigstep (while g S1) (h, s) o <->
    exists n, bigstep (approx n g S1) (h, s) o.
intros; split; intro.
- remember (while g S1).
  induction H; try inversion Heqp.
  + apply IHbigstep2 in Heqp.
    destruct Heqp.
    exists (S x).
    simpl.
    apply step_ite_true.
    rewrite <- H3. apply H.
    destruct o; [destruct p|].
    eapply step_comp.
    rewrite <- H4. apply H0. apply H2.
    eapply step_comp_fail2.
    rewrite <- H4. apply H0. apply H2.
  + exists 1.
    simpl.
    apply step_ite_false.
    rewrite <- H1. apply H.
    apply step_skip.
  + exists 1.
    simpl.
    apply step_ite_true.
    rewrite <- H2. apply H.
    apply step_comp_fail1.
    rewrite <- H3. apply H0.
- destruct H.
  generalize dependent h.
  generalize dependent s.
  generalize dependent o.
  induction x; intros.
  + simpl in H.
    exfalso.
    pose proof (diverge_empty h s).
    specialize H0 with o.
    apply H0; auto.
  + simpl in H.
    inversion H.
    inversion H7.
    apply IHx in H14.
    eapply step_while_true.
    apply H6.
    apply H13.
    apply H14.
    apply step_while_fail.
    apply H6.
    apply H13.
    apply IHx in H14.
    eapply step_while_true.
    apply H6.
    apply H13.
    apply H14.
    inversion H7.
    eapply step_while_false.
    apply H6.
Qed.

Definition omega: program := while true skip.

Proposition omega_diverge_equiv:
  forall h s o,
    bigstep omega (h, s) o <->
    bigstep diverge (h, s) o.
intros. unfold omega.
rewrite while_approx.
split; intro.
destruct H.
generalize dependent s.
generalize dependent h.
induction x; intros; simpl in H.
auto.
inversion H.
inversion H7.
rewrite H11.
apply IHx.
inversion H13.
rewrite <- H11. assumption.
inversion H13.
rewrite H11.
apply IHx.
rewrite <- H11.
inversion H13. assumption.
inversion H6.
inversion H.
Qed.

(* ============= *)
(* HOARE TRIPLES *)
(* ============= *)

Inductive hoare :=
| mkhoare: assert -> program -> assert -> hoare.

Definition pre: hoare -> assert := fun '(mkhoare p _ _) => p.
Definition S: hoare -> program := fun '(mkhoare _ x _) => x.
Definition post: hoare -> assert := fun '(mkhoare _ _ q) => q.

Definition restrict_post: hoare -> Prop := fun '(mkhoare _ S1 q) =>
  match S1 with
  | assign S1 => match S1 with
    | basic x e => (forall y, In y (evar e) -> ~In y (abound q))
    | lookup x e => True
    | mutation x e => (forall y, In y (x :: evar e) -> ~In y (abound q))
    | new x e => ~In x (evar e) /\ (forall y, In y (x :: evar e) -> ~In y (abound q))
    | dispose x => ~In x (abound q)
    end
  | _ => False
  end.

Definition restrict_pre: hoare -> Prop := fun '(mkhoare p S1 _) =>
  match S1 with
  | assign S1 => match S1 with
    | basic x e => ~In x (abound p)
    | lookup x e => ~In x (abound p)
    | mutation x e => ~In x (abound p)
    | new x e => ~In x (evar e) /\ ~In x (abound p)
    | dispose x => ~In x (abound p)
    end
  | _ => False
  end.

Definition restrict (pSq: hoare): Prop := restrict_post pSq /\ restrict_pre pSq.

(* ======================================================================= *)
(* WEAKEST PRECONDITION AXIOMATIZATION (WP-CSL), SEE FIGURE 3 IN THE PAPER *)
(* ======================================================================= *)

Inductive WPCSL_FULL (Gamma: assert -> Prop): hoare -> Set :=
(* Rules for assignments *)
| wpcf_basic (p ps: assert) (x: V) (e: expr):
    asub p x e = Some ps ->
    WPCSL_FULL Gamma (mkhoare ps (basic x e) p)
| wpcf_lookup (p ps: assert) (x y: V) (e: expr):
    ~In y (x :: aoccur p ++ evar e) ->
    asub p x y = ps ->
    WPCSL_FULL Gamma (mkhoare (lexists y (land (hasval e y) ps)) (lookup x e) p)
| wpcf_mutation (p ps: assert) (x: V) (e: expr):
    asub_heap_update p x e = ps ->
    WPCSL_FULL Gamma (mkhoare (land (hasvaldash x) ps) (mutation x e) p)
| wpcf_new (p ps: assert) (x: V) (e: expr):
    ~In x (evar e) ->
    asub_heap_update p x e = ps ->
    WPCSL_FULL Gamma (mkhoare (lforall x (limp (lnot (hasvaldash x)) ps)) (new x e) p)
| wpcf_new_util (p q: assert) (x y: V) (e: expr):
    ~In y (x :: aoccur p ++ aoccur q ++ evar e) ->
    WPCSL_FULL Gamma (mkhoare p (comp (basic y e) (new x y)) q) ->
    WPCSL_FULL Gamma (mkhoare p (new x e) q)
| wpcf_dispose (p ps: assert) (x: V):
    asub_heap_clear p x = ps ->
    WPCSL_FULL Gamma (mkhoare (land (hasvaldash x) ps) (dispose x) p)
(* Standard compositional rules *)
| wpcf_skip (p: assert):
    WPCSL_FULL Gamma (mkhoare p skip p)
| wpcf_diverge (p: assert):
    WPCSL_FULL Gamma (mkhoare p diverge false)
| wpcf_compose (p q r: assert) (S1 S2: program):
    WPCSL_FULL Gamma (mkhoare p S1 r) ->
    WPCSL_FULL Gamma (mkhoare r S2 q) ->
    WPCSL_FULL Gamma (mkhoare p (comp S1 S2) q)
| wpcf_ite (p q: assert) (g: guard) (S1 S2: program):
    WPCSL_FULL Gamma (mkhoare (land p g) S1 q) ->
    WPCSL_FULL Gamma (mkhoare (land p (lnot g)) S2 q) ->
    WPCSL_FULL Gamma (mkhoare p (ite g S1 S2) q)
| wpcf_while (p: assert) (g: guard) (S1: program):
    WPCSL_FULL Gamma (mkhoare (land p g) S1 p) ->
    WPCSL_FULL Gamma (mkhoare p (while g S1) (land p (lnot g)))
| wpcf_conseq (p pp q qq: assert) (x: program):
    Gamma (limp pp p) -> WPCSL_FULL Gamma (mkhoare p x q) -> Gamma (limp q qq) ->
    WPCSL_FULL Gamma (mkhoare pp x qq).

Inductive WPCSL (Gamma: assert -> Prop): hoare -> Set :=
| wpc_basic (p ps: assert) (x: V) (e: expr):
    asub p x e = Some ps ->
    WPCSL Gamma (mkhoare ps (basic x e) p)
| wpc_lookup (p ps: assert) (x y: V) (e: expr):
    ~In y (x :: aoccur p ++ evar e) ->
    asub p x y = ps ->
    WPCSL Gamma (mkhoare (lexists y (land (hasval e y) ps)) (lookup x e) p)
| wpc_mutation (p ps: assert) (x: V) (e: expr):
    asub_heap_update p x e = ps ->
    WPCSL Gamma (mkhoare (land (hasvaldash x) ps) (mutation x e) p)
| wpc_new (p ps: assert) (x: V) (e: expr):
    ~In x (evar e) ->
    asub_heap_update p x e = ps ->
    WPCSL Gamma (mkhoare (lforall x (limp (lnot (hasvaldash x)) ps)) (new x e) p)
| wpc_dispose (p ps: assert) (x: V):
    asub_heap_clear p x = ps ->
    WPCSL Gamma (mkhoare (land (hasvaldash x) ps) (dispose x) p)
| wpc_conseq (p pp q qq: assert) (x: program):
    Gamma (limp pp p) -> WPCSL Gamma (mkhoare p x q) -> Gamma (limp q qq) ->
    WPCSL Gamma (mkhoare pp x qq).

(* ======================================================================= *)
(* GLOBAL WEAKEST PRECONDITION AXIOMATIZATION USING SEPARATING CONNECTIVES *)
(* ======================================================================= *)

Inductive WPCSL_SEP (Gamma: assert -> Prop): hoare -> Set :=
| wpcs_basic (p ps: assert) (x: V) (e: expr):
    asub p x e = Some ps ->
    WPCSL_SEP Gamma (mkhoare ps (basic x e) p)
| wpcs_lookup (p ps: assert) (x y: V) (e: expr):
    ~In y (x :: aoccur p ++ evar e) ->
    asub p x y = ps ->
    WPCSL_SEP Gamma (mkhoare (lexists y (land (hasval e y) ps)) (lookup x e) p)
| wpcs_mutation (p: assert) (x: V) (e: expr):
    WPCSL_SEP Gamma (mkhoare (sand (pointstodash x) (simp (pointsto x e) p)) (mutation x e) p)
| wpcs_new (p ps: assert) (x y: V) (e: expr):
    ~In y (x :: aoccur p ++ evar e) ->
    asub p x y = ps ->
    WPCSL_SEP Gamma (mkhoare (lforall y (simp (pointsto y e) ps)) (new x e) p)
| wpcs_dispose (p: assert) (x: V):
    WPCSL_SEP Gamma (mkhoare (sand (pointstodash x) p) (dispose x) p)
| wpcs_conseq (p pp q qq: assert) (x: program):
    Gamma (limp pp p) -> WPCSL_SEP Gamma (mkhoare p x q) -> Gamma (limp q qq) ->
    WPCSL_SEP Gamma (mkhoare pp x qq).

(* ========================================================================== *)
(* STRONGEST POSTCONDITION AXIOMATIZATION (SP-CSL), SEE FIGURE 6 IN THE PAPER *)
(* ========================================================================== *)

Inductive SPCSL (Gamma: assert -> Prop): hoare -> Set :=
| spc_basic (p ps: assert) (x y: V) (e: expr):
    ~In y (x :: aoccur p ++ evar e) ->
    asub p x y = Some ps ->
    SPCSL Gamma (mkhoare p (basic x e) (lexists y (land ps (equals (esub e x y) x))))
| spc_lookup (p ps: assert) (x y: V) (e: expr):
    ~In y (x :: aoccur p ++ evar e) ->
    asub p x y = Some ps ->
    SPCSL Gamma (mkhoare (land p (hasvaldash e)) (lookup x e) (lexists y (land ps (hasval (esub e x y) x))))
| spc_mutation (p ps: assert) (x y: V) (e: expr):
    ~In y (x :: aoccur p ++ evar e) ->
    asub_heap_update p x y = Some ps ->
    SPCSL Gamma (mkhoare (land p (hasvaldash x)) (mutation x e) (land (lexists y ps) (hasval x e)))
| spc_new (p ps pss: assert) (x y: V) (e: expr):
    ~In x (evar e) ->
    ~In y (x :: aoccur p ++ evar e) ->
    asub p x y = Some ps ->
    asub_heap_clear (lexists y ps) x = Some pss ->
    SPCSL Gamma (mkhoare p (new x e) (land pss (hasval x e)))
| spc_dispose (p ps: assert) (x y: V):
    ~In y (x :: aoccur p) ->
    asub_heap_update p x y = Some ps ->
    SPCSL Gamma (mkhoare (land p (hasvaldash x)) (dispose x) (land (lexists y ps) (lnot (hasvaldash x))))
| spc_conseq (p pp q qq: assert) (x: program):
    Gamma (limp pp p) -> SPCSL Gamma (mkhoare p x q) -> Gamma (limp q qq) ->
    SPCSL Gamma (mkhoare pp x qq).

(* ============================================ *)
(* WEAKEST PRECONDITION AXIOMATIZATION (WP-ISL) *)
(* ============================================ *)

Inductive WPISL (Gamma: assert -> Prop): hoare -> Set :=
| wpi_basic (p ps: assert) (x: V) (e: expr):
    asub p x e = Some ps ->
    WPISL Gamma (mkhoare ps (basic x e) p)
| wpi_lookup (p ps: assert) (x y: V) (e: expr):
    ~In y (x :: aoccur p ++ evar e) ->
    asub p x y = ps ->
    WPISL Gamma (mkhoare (lexists y (land (hasval e y) ps)) (lookup x e) p)
| wpi_mutation (p ps: assert) (x: V) (e: expr):
    asub_cheap_update p x e = ps ->
    WPISL Gamma (mkhoare (land (hasvaldash x) ps) (mutation x e) p)
| wpi_new (p ps: assert) (x: V) (e: expr):
    ~In x (evar e) ->
    asub_cheap_update p x e = ps ->
    WPISL Gamma (mkhoare (lforall x (lor (hasvaldash x) (limp (hasvaldash x) ps))) (new x e) p)
| wpi_dispose (p ps: assert) (x: V):
    asub_cheap_clear p x = ps ->
    WPISL Gamma (mkhoare (land (hasvaldash x) ps) (dispose x) p)
| wpi_conseq (p pp q qq: assert) (x: program):
    Gamma (limp pp p) -> WPISL Gamma (mkhoare p x q) -> Gamma (limp q qq) ->
    WPISL Gamma (mkhoare pp x qq).

(* =============================================== *)
(* STRONGEST POSTCONDITION AXIOMATIZATION (SP-ISL) *)
(* =============================================== *)

Inductive SPISL (Gamma: assert -> Prop): hoare -> Set :=
| spi_basic (p ps: assert) (x y: V) (e: expr):
    ~In y (x :: aoccur p ++ evar e) ->
    asub p x y = Some ps ->
    SPISL Gamma (mkhoare p (basic x e) (lexists y (land ps (equals (esub e x y) x))))
| spi_lookup (p ps: assert) (x y: V) (e: expr):
    ~In y (x :: aoccur p ++ evar e) ->
    asub p x y = Some ps ->
    SPISL Gamma (mkhoare (land p (hasvaldash e)) (lookup x e) (lexists y (land ps (hasval (esub e x y) x))))
| spi_mutation (p ps: assert) (x y: V) (e: expr):
    ~In y (x :: aoccur p ++ evar e) ->
    asub_cheap_update p x y = Some ps ->
    SPISL Gamma (mkhoare (land p (hasvaldash x)) (mutation x e) (land (lexists y ps) (hasval x e)))
| spi_new (p ps pss: assert) (x y: V) (e: expr):
    ~In x (evar e) ->
    ~In y (x :: aoccur p ++ evar e) ->
    asub p x y = Some ps ->
    asub_cheap_clear (lexists y ps) x = Some pss ->
    SPISL Gamma (mkhoare p (new x e) (land pss (hasval x e)))
| spi_dispose (p ps: assert) (x y: V):
    ~In y (x :: aoccur p) ->
    asub_cheap_update p x y = Some ps ->
    SPISL Gamma (mkhoare (land p (hasvaldash x)) (dispose x) (limp (hasvaldash x) (lexists y ps)))
| spi_conseq (p pp q qq: assert) (x: program):
    Gamma (limp pp p) -> SPISL Gamma (mkhoare p x q) -> Gamma (limp q qq) ->
    SPISL Gamma (mkhoare pp x qq).

End Language.

