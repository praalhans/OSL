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
  | lexists y p => if Nat.eq_dec x y then lexists y p else
      if in_dec Nat.eq_dec y (evar e) then None
      else option_app (asub p x e) (fun ps => lexists y ps)
  | lforall y p => if Nat.eq_dec x y then lforall y p else
      if in_dec Nat.eq_dec y (evar e) then None
      else option_app (asub p x e) (fun ps => lforall y ps)
  | sand p q => option_app (asub p x e) (fun ps =>
      option_app (asub q x e) (fun qs => sand ps qs))
  | simp p q => option_app (asub p x e) (fun ps =>
      option_app (asub q x e) (fun qs => simp ps qs))
  end.

Proposition asub_defined (p: assert) (x: V) (e: expr):
  (forall x, In x (evar e) -> ~In x (abound p)) <-> exists q, asub p x e = Some q.
induction p; simpl.
- split; intros; auto.
  exists (test (gsub g x e)); reflexivity.
- split; intros; auto.
  exists (hasval (esub e0 x e) (esub e1 x e)); reflexivity.
- split; intros.
  + apply In_app_split in H; destruct H.
    apply IHp1 in H; destruct H.
    apply IHp2 in H0; destruct H0.
    exists (land x0 x1); rewrite H; rewrite H0; reflexivity.
  + destruct H.
    apply option_app_elim in H; destruct H; destruct H.
    assert (exists q, asub p1 x e = Some q) by (exists x2; assumption).
    apply option_app_elim in H1; destruct H1; destruct H1.
    assert (exists q, asub p2 x e = Some q) by (exists x3; assumption).
    apply not_In_split; split.
    apply <- IHp1; assumption.
    apply <- IHp2; assumption.
Abort.

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

End Language.

















