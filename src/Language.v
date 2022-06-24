(* Copyright 2022 Centrum Wiskunde & Informatica *)

(* ON SEPERATION LOGIC *)
(* Author: Hans-Dieter A. Hiep *)

Require Export OnSeparationLogic.Heap.

Module Language (Export HS: HeapSig).

Module H := HeapFacts HS.
Include H.

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

Proposition esub_notInVar (e: expr) (x y: V):
  x <> y -> ~ In x (evar (esub e x y)).
intros; simpl; intro.
apply in_app_or in H0; destruct H0.
eapply remove_In; apply H0.
inversion H0.
apply H; symmetry; assumption.
inversion H1.
Qed.

Proposition eval_esub_fresh_general (s: store) (e e': expr) (xs: list V):
  (forall x, In x (evar e) -> In x xs) ->
  eval (esub e (fresh xs) e') s = eval e s.
intro; destruct e; simpl in *.
apply econd0. intro. intro.
unfold store_update.
destruct (Nat.eq_dec (fresh xs) x).
apply H in H0.
rewrite <- e in H0.
exfalso. eapply fresh_notIn; apply H0.
reflexivity.
Qed.

Proposition eval_esub_fresh (s: store) (e e': expr):
  eval (esub e (fresh (evar e)) e') s = eval e s.
apply eval_esub_fresh_general. auto.
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

Proposition gsub_notInVar (g: guard) (x y:V):
  x <> y -> ~In x (gvar (gsub g x y)).
intros; simpl; intro.
apply in_app_or in H0; destruct H0.
eapply remove_In; apply H0.
inversion H0. apply H; symmetry; assumption.
inversion H1.
Qed.

Proposition gval_gsub_fresh_general (s: store) (g: guard) (xs: list V) (e: expr):
  (forall x, In x (gvar g) -> In x xs) -> gval (gsub g (fresh xs) e) s = gval g s.
intro; destruct g; simpl in *.
apply gcond0. intro. intro.
unfold store_update.
destruct (Nat.eq_dec (fresh xs) x).
apply H in H0.
rewrite <- e0 in H0.
exfalso. eapply fresh_notIn; apply H0.
reflexivity.
Qed.

Proposition gval_gsub_fresh (s: store) (g: guard) (e: expr):
  gval (gsub g (fresh (gvar g)) e) s = gval g s.
apply gval_gsub_fresh_general. auto.
Qed.

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
  apply (gsub_notInVar _ _ _ H H1).
- unfold aoccur in *; unfold abound in *; unfold avar in *.
  intro.
  apply in_app_or in H1; destruct H1.
  inversion H1.
  apply in_app_or in H1; destruct H1.
  apply (esub_notInVar _ _ _ H H1).
  apply (esub_notInVar _ _ _ H H1).
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

Variant assignment :=
| basic: V -> expr -> assignment
| lookup: V -> expr -> assignment
| mutation: V -> expr -> assignment
| new: V -> expr -> assignment
| dispose: V -> assignment.

Inductive program :=
| assign: assignment -> program
| comp: program -> program -> program.
Coercion assign: assignment >-> program.

Inductive bigstep: program -> heap * store -> option (heap * store) -> Prop :=
| step_basic (x: V) (e: expr) (h: heap) (s: store):
    bigstep (basic x e) (h, s) (Some (h, store_update s x (eval e s)))
| step_lookup (x: V) (e: expr) (h: heap) (s: store) (v: Z):
    h (eval e s) = Some v ->
    bigstep (lookup x e) (h, s) (Some (h, store_update s x v))
| step_lookup_fail (x: V) (e: expr) (h: heap) (s: store) (v: Z):
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
    bigstep (comp S1 S2) (h, s) None.

Inductive hoare :=
| mkhoare: assert -> program -> assert -> hoare.

Definition pre: hoare -> assert := fun '(mkhoare p _ _) => p.
Definition S: hoare -> program := fun '(mkhoare _ x _) => x.
Definition post: hoare -> assert := fun '(mkhoare _ _ q) => q.

(* ============================================ *)
(* Weakest precondition axiomatization (WP-CSL) *)
(* ============================================ *)

Inductive WPCSL: hoare -> Set :=
| wpc_basic (p ps: assert) (x: V) (e: expr):
    asub p x e = Some ps ->
    WPCSL (mkhoare ps (basic x e) p)
| wpc_lookup (p ps: assert) (x y: V) (e: expr):
    ~In y (x :: aoccur p ++ evar e) ->
    asub p x y = ps ->
    WPCSL (mkhoare (lexists y (land (sand (hasval e y) true) ps)) (lookup x e) p).

End Language.

















