Require Export FunctionalExtensionality.
Require Export PropExtensionality.
Require Export List.
Require Export Sorting.
Require Export PeanoNat.
Require Export ZArith.

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

(* ========= *)
(* THE STORE *)
(* ========= *)

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

Proposition eq_restr_cons (s t: store) (x: V) (xs: list V):
  eq_restr s t (x :: xs) -> s x = t x /\ eq_restr s t xs.
intros; split.
apply H. left; auto.
intro; intro.
apply H. right; auto.
Qed.

Proposition eq_restr_comm (s t: store) (xs: list V):
  eq_restr s t xs -> eq_restr t s xs.
unfold eq_restr; intros; symmetry; apply H; assumption.
Qed.

Proposition eq_restr_incl (s t: store) (xs ys: list V):
  (forall x, In x ys -> In x xs) ->
  eq_restr s t xs -> eq_restr s t ys.
intros. intro; intro.
apply H in H1.
apply H0; auto.
Qed.

Proposition eq_restr_store_update (s t: store) (x: V) (v: Z) (xs: list V):
  eq_restr s t xs -> eq_restr (store_update s x v) (store_update t x v) xs.
intros. intro; intro.
unfold store_update. destruct (Nat.eq_dec x x0). reflexivity.
apply H. auto.
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

(* ===== *)
(* HEAPS *)
(* ===== *)

Definition heap := Z -> option Z.

Proposition heap_ext: forall (h g: heap), (forall n, h n = g n) -> h = g.
intros. apply functional_extensionality. apply H.
Qed.

Definition heap_update (h: heap) (k v: Z): heap :=
  fun n => if Z.eq_dec k n then Some v else h n.

Proposition heap_update_spec1: forall h k v, (heap_update h k v) k = Some v.
intros. unfold heap_update. destruct (Z.eq_dec k k). auto. exfalso. apply n. auto.
Qed.

Proposition heap_update_spec2: forall h k v k', k <> k' -> (heap_update h k v) k' = h k'.
intros. unfold heap_update. destruct (Z.eq_dec k k'). exfalso. apply H. auto. auto.
Qed.

Definition heap_clear (h: heap) (k: Z): heap :=
  fun n => if Z.eq_dec k n then None else h n.

Proposition heap_clear_spec1: forall h k, (heap_clear h k) k = None.
intros. unfold heap_clear. destruct (Z.eq_dec k k). auto. exfalso. apply n. auto.
Qed.

Proposition heap_clear_spec2: forall h k k', k <> k' -> (heap_clear h k) k' = h k'.
intros. unfold heap_clear. destruct (Z.eq_dec k k'). exfalso. apply H. auto. auto.
Qed.

Definition dom (h: heap) (k: Z): Prop := h k <> None.

Proposition dom_spec: forall h k, dom h k <-> h k <> None.
unfold dom. intros. split; intro; auto.
Qed.

Proposition heap_clear_dom (h: heap) (k: Z):
  ~dom h k -> heap_clear h k = h.
unfold dom; unfold heap_clear; intros.
apply functional_extensionality; intro.
destruct (Z.eq_dec k x). rewrite e in H.
destruct (h x). exfalso. apply H. intro. inversion H0. auto. auto.
Qed.

Proposition heap_update_cancel (h: heap) (k v z: Z):
  h k = Some z -> heap_update (heap_update h k v) k z = h.
intro.
apply functional_extensionality; intro.
unfold heap_update.
destruct (Z.eq_dec k x). rewrite <- e. rewrite H. reflexivity.
auto.
Qed.

Proposition heap_update_collapse (h: heap) (k v z: Z):
  heap_update (heap_update h k v) k z = heap_update h k z.
apply functional_extensionality; intro.
unfold heap_update.
destruct (Z.eq_dec k x); auto.
Qed.

Proposition heap_update_heap_clear_cancel (h: heap) (k z: Z):
  h k = Some z -> heap_update (heap_clear h k) k z = h.
intro.
apply functional_extensionality; intro.
unfold heap_update. unfold heap_clear.
destruct (Z.eq_dec k x). rewrite <- e. rewrite H. reflexivity.
auto.
Qed.

Proposition heap_clear_cancel (h: heap) (k: Z):
  h k = None -> heap_clear h k = h.
intro.
apply functional_extensionality; intro.
unfold heap_clear.
destruct (Z.eq_dec k x). rewrite <- e. auto.
auto.
Qed.

Proposition heap_clear_heap_update_cancel (h: heap) (k v: Z):
  h k = None -> heap_clear (heap_update h k v) k = h.
intro.
apply functional_extensionality; intro.
unfold heap_update. unfold heap_clear.
destruct (Z.eq_dec k x). rewrite <- e. auto.
auto.
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

Definition Partition (h h1 h2: heap): Prop :=
  (forall k, (dom h k -> dom h1 k \/ dom h2 k)) /\
  (forall k, ~(dom h1 k /\ dom h2 k)) /\
  (forall k, dom h1 k -> h k = h1 k) /\
  (forall k, dom h2 k -> h k = h2 k).

Proposition Partition_comm (h h1 h2: heap):
  Partition h h1 h2 -> Partition h h2 h1.
unfold Partition. intro.
destruct H as (H0 & H1 & H2).
split; try split; try tauto.
- intros. apply H0 in H. destruct H; auto.
- intros. intro. destruct H1 with (k := k). tauto.
Qed.

Proposition Partition_spec1: forall h h1 h2, Partition h h1 h2 -> forall k, dom h1 k -> h k = h1 k.
intros. unfold Partition in H. destruct H. destruct H1. destruct H2.
apply H2. auto.
Qed.

Proposition Partition_spec2: forall h h1 h2, Partition h h1 h2 -> forall k, dom h2 k -> h k = h2 k.
intros. unfold Partition in H. destruct H. destruct H1. destruct H2.
apply H3. auto.
Qed.

Proposition Partition_spec3: forall h h1 h2, Partition h h1 h2 -> forall k, ~dom h1 k -> ~dom h2 k -> h k = None.
intros. unfold Partition in H. destruct H. destruct H2. destruct H3.
remember (h k). destruct o; auto.
exfalso. specialize H with k.
assert (dom h k). unfold dom. intro. rewrite H5 in Heqo. inversion Heqo.
apply H in H5; clear H. destruct H5; auto.
Qed.

Proposition Partition_spec4: forall h h1 h2, Partition h h1 h2 -> forall k, ~(dom h1 k /\ dom h2 k).
intros. unfold Partition in H. destruct H. destruct H0. destruct H1.
apply H0.
Qed.

Proposition Partition_intro1: forall h1 h2, (forall k, ~(dom h1 k /\ dom h2 k)) -> exists h, Partition h h1 h2.
intros.
exists (fun x => match h1 x with None => h2 x | Some v => Some v end).
unfold Partition. split; try split; try split; intros; simpl.
- unfold dom in H0. remember (h1 k). destruct o.
  left. unfold dom. intro. rewrite H1 in Heqo. inversion Heqo.
  right. apply H0.
- apply H.
- remember (h1 k). destruct o. auto.
  exfalso. apply H0. auto.
- remember (h1 k). destruct o.
  exfalso. destruct H with (k := k). split; auto.
  unfold dom. intro. rewrite H1 in Heqo. inversion Heqo.
  auto.
Qed.

Definition option_dec {T: Type} (o: option T): {exists x, o = Some x} + {o = None} :=
  match o return ({exists x : T, o = Some x} + {o = None}) with
  | Some t => left (ex_intro (fun x : T => Some t = Some x) t eq_refl)
  | None => right eq_refl
  end.

(* Needed for intuitionistic semantics: *)
Proposition Partition_intro2: forall h h1, (forall k, dom h1 k -> h k = h1 k) -> exists h2, Partition h h1 h2.
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

Proposition Partition_dom_right1 (h h1 h2: heap) (x: Z):
  Partition h h1 h2 -> dom h1 x -> ~dom h2 x.
intros. unfold Partition in H. destruct H. destruct H1.
intro.
destruct H1 with (k := x). auto.
Qed.

Proposition Partition_dom_right2 (h h1 h2: heap) (x: Z):
  Partition h h1 h2 -> dom h2 x -> ~dom h1 x.
intros. unfold Partition in H. destruct H. destruct H1.
intro.
destruct H1 with (k := x). auto.
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

Proposition Partition_not_dom (h h1 h2: heap) (x: Z):
  Partition h h1 h2 -> ~dom h1 x -> ~dom h2 x -> ~dom h x.
intros. unfold Partition in H. destruct H. destruct H2.
intro. apply H in H4. destruct H4; tauto.
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

Proposition Partition_heap_update_split (h h1 h2: heap) (k v: Z):
  Partition (heap_update h k v) h1 h2 ->
  (exists h1', Partition h h1' h2 /\ h1 = heap_update h1' k v /\ ~dom h2 k) \/
  (exists h2', Partition h h1 h2' /\ h2 = heap_update h2' k v /\ ~dom h1 k).
intros.
pose proof (heap_update_dom1 h k v); pose proof (Partition_dom_split _ _ _ _ H H0); destruct H1.
- left. remember (h k); destruct o.
  + exists (heap_update h1 k z).
    pose proof (Partition_dom_right1 _ _ _ k H H1).
    split.
    pose proof (Partition_intro1 (heap_update h1 k z) h2). destruct H3.
    intros. intro. destruct H3.
    destruct (Z.eq_dec k0 k). rewrite e in H4.
    eapply Partition_spec4. apply H. split. apply H1. apply H4.
    apply heap_update_dom2 in H3; auto.
    eapply Partition_spec4. apply H. split. apply H3. apply H4.
    pose proof (heap_ext h x). rewrite H4. assumption.
    clear H4. intros.
    destruct (Z.eq_dec n k).
    rewrite e. rewrite <- Heqo.
    erewrite <- (heap_update_spec1 h1 k). symmetry.
    apply Partition_spec1 with (h2 := h2); auto. apply heap_update_dom1.
    rewrite <- heap_update_spec2 with (k := k) (v := v); auto.
    destruct (dom_dec h2 n).
    rewrite Partition_spec2 with (h1 := h1) (h2 := h2); auto.
    symmetry. eapply Partition_spec2. apply H3. assumption.
    destruct (dom_dec h1 n).
    rewrite Partition_spec1 with (h1 := h1) (h2 := h2); auto.
    rewrite <- heap_update_spec2 with (k := k) (v := z); auto. symmetry.
    eapply Partition_spec1. apply H3. apply heap_update_dom2; auto.
    rewrite Partition_spec3 with (h1 := h1) (h2 := h2); auto.
    symmetry. eapply Partition_spec3. apply H3.
    rewrite heap_update_dom2; auto. auto.
    split; auto.
    apply heap_ext; intro.
    destruct (Z.eq_dec n k).
    rewrite e. rewrite heap_update_spec1.
    erewrite <- Partition_spec1. 2: apply H.
    apply heap_update_spec1. auto.
    rewrite heap_update_spec2; auto.
    rewrite heap_update_spec2; auto.
  + exists (heap_clear h1 k).
    pose proof (Partition_dom_right1 _ _ _ k H H1).
    assert (h1 k = Some v). { pose proof (Partition_spec1 _ _ _ H k H1).
    rewrite heap_update_spec1 in H3. inversion H3. reflexivity. }
    split.
    pose proof (Partition_intro1 (heap_clear h1 k) h2). destruct H4.
    intros. intro. destruct H4.
    destruct (Z.eq_dec k0 k). rewrite e in H4.
    eapply heap_clear_dom1. apply H4.
    rewrite heap_clear_dom2 in H4.
    eapply Partition_spec4. apply H. split. apply H4. apply H5.
    intro. apply n. auto.
    pose proof (heap_ext h x).
    rewrite H5. assumption. clear H5. intro.
    destruct (Z.eq_dec n k).
    rewrite e. rewrite <- Heqo.
    symmetry. eapply Partition_spec3. apply H4.
    apply heap_clear_dom1. assumption.
    rewrite <- heap_update_spec2 with (k := k) (v := v); auto.
    destruct (dom_dec h2 n).
    rewrite Partition_spec2 with (h1 := h1) (h2 := h2); try assumption.
    symmetry. eapply Partition_spec2. apply H4. assumption.
    destruct (dom_dec h1 n).
    rewrite Partition_spec1 with (h1 := h1) (h2 := h2); auto.
    symmetry. rewrite <- (heap_clear_spec2 h1 k); auto.
    erewrite Partition_spec1. reflexivity. apply H4.
    apply heap_clear_dom2; auto.
    rewrite Partition_spec3 with (h1 := h1) (h2 := h2); auto.
    rewrite Partition_spec3 with (h1 := heap_clear h1 k) (h2 := h2); auto.
    rewrite heap_clear_dom2; auto.
    split.
    apply heap_ext; intro. destruct (Z.eq_dec k n).
    rewrite <- e. rewrite heap_update_spec1. rewrite H3. reflexivity.
    rewrite heap_update_spec2; auto. rewrite heap_clear_spec2; auto.
    assumption.
- right.
  pose proof (Partition_comm _ _ _ H). clear H. rename H2 into H.
  remember (h k); destruct o.
  + exists (heap_update h2 k z).
    pose proof (Partition_dom_right1 _ _ _ k H H1).
    split.
    pose proof (Partition_intro1 (heap_update h2 k z) h1). destruct H3.
    intros. intro. destruct H3.
    destruct (Z.eq_dec k0 k). rewrite e in H4.
    eapply Partition_spec4. apply H. split. apply H1. apply H4.
    apply heap_update_dom2 in H3; auto.
    eapply Partition_spec4. apply H. split. apply H3. apply H4.
    pose proof (heap_ext h x). rewrite H4. apply Partition_comm. assumption.
    clear H4. intros.
    destruct (Z.eq_dec n k).
    rewrite e. rewrite <- Heqo.
    erewrite <- (heap_update_spec1 h2 k). symmetry.
    apply Partition_spec1 with (h2 := h1); auto. apply heap_update_dom1.
    rewrite <- heap_update_spec2 with (k := k) (v := v); auto.
    destruct (dom_dec h1 n).
    rewrite Partition_spec2 with (h1 := h2) (h2 := h1); auto.
    symmetry. eapply Partition_spec2. apply H3. assumption.
    destruct (dom_dec h2 n).
    rewrite Partition_spec1 with (h1 := h2) (h2 := h1); auto.
    rewrite <- heap_update_spec2 with (k := k) (v := z); auto. symmetry.
    eapply Partition_spec1. apply H3. apply heap_update_dom2; auto.
    rewrite Partition_spec3 with (h1 := h2) (h2 := h1); auto.
    symmetry. eapply Partition_spec3. apply H3.
    rewrite heap_update_dom2; auto. auto.
    split; auto.
    apply heap_ext; intro.
    destruct (Z.eq_dec n k).
    rewrite e. rewrite heap_update_spec1.
    erewrite <- Partition_spec1. 2: apply H.
    apply heap_update_spec1. auto.
    rewrite heap_update_spec2; auto.
    rewrite heap_update_spec2; auto.
  + exists (heap_clear h2 k).
    pose proof (Partition_dom_right1 _ _ _ k H H1).
    assert (h2 k = Some v). { pose proof (Partition_spec1 _ _ _ H k H1).
    rewrite heap_update_spec1 in H3. inversion H3. reflexivity. }
    split.
    apply Partition_comm.
    pose proof (Partition_intro1 (heap_clear h2 k) h1). destruct H4.
    intros. intro. destruct H4.
    destruct (Z.eq_dec k0 k). rewrite e in H4.
    eapply heap_clear_dom1. apply H4.
    rewrite heap_clear_dom2 in H4.
    eapply Partition_spec4. apply H. split. apply H4. apply H5.
    intro. apply n. auto.
    pose proof (heap_ext h x).
    rewrite H5. assumption. clear H5. intro.
    destruct (Z.eq_dec n k).
    rewrite e. rewrite <- Heqo.
    symmetry. eapply Partition_spec3. apply H4.
    apply heap_clear_dom1. assumption.
    rewrite <- heap_update_spec2 with (k := k) (v := v); auto.
    destruct (dom_dec h1 n).
    rewrite Partition_spec2 with (h1 := h2) (h2 := h1); try assumption.
    symmetry. eapply Partition_spec2. apply H4. assumption.
    destruct (dom_dec h2 n).
    rewrite Partition_spec1 with (h1 := h2) (h2 := h1); auto.
    symmetry. rewrite <- (heap_clear_spec2 h2 k); auto.
    erewrite Partition_spec1. reflexivity. apply H4.
    apply heap_clear_dom2; auto.
    rewrite Partition_spec3 with (h1 := h2) (h2 := h1); auto.
    rewrite Partition_spec3 with (h1 := heap_clear h2 k) (h2 := h1); auto.
    rewrite heap_clear_dom2; auto.
    split.
    apply heap_ext; intro. destruct (Z.eq_dec k n).
    rewrite <- e. rewrite heap_update_spec1. rewrite H3. reflexivity.
    rewrite heap_update_spec2; auto. rewrite heap_clear_spec2; auto.
    assumption.
Qed.

Proposition Partition_heap_update (h h' h'': heap) (k v: Z):
  Partition h'' (heap_update h k v) h' ->
  exists hh, h'' = heap_update hh k v /\ Partition hh h h'.
intros. remember (h k); destruct o.
- exists (heap_update h'' k z).
  split.
  + apply heap_ext; intro.
    destruct (Z.eq_dec n k).
    rewrite e.
    rewrite heap_update_spec1.
    rewrite (Partition_spec1 _ _ _ H).
    apply heap_update_spec1.
    apply heap_update_dom1.
    rewrite heap_update_spec2; auto.
    rewrite heap_update_spec2; auto.
  + pose proof (Partition_intro1 h h').
    destruct H0. intro. intro. destruct H0.
    eapply Partition_spec4. apply H. split; [| apply H1].
    destruct (Z.eq_dec k k0).
    rewrite e.
    apply heap_update_dom1.
    apply heap_update_dom2; auto.
    pose proof (heap_ext (heap_update h'' k z) x).
    rewrite H1. assumption. clear H1. intros.
    destruct (Z.eq_dec n k). rewrite e.
    rewrite heap_update_spec1. symmetry.
    rewrite Heqo. eapply Partition_spec1. apply H0.
    rewrite dom_spec. intro. rewrite <- Heqo in H1. inversion H1.
    rewrite heap_update_spec2; auto.
    destruct (dom_dec h' n).
    rewrite Partition_spec2 with (h1 := heap_update h k v) (h2 := h'); auto.
    symmetry. apply Partition_spec2 with (h1 := h) (h2 := h'); auto.
    destruct (dom_dec h n).
    rewrite Partition_spec1 with (h1 := heap_update h k v) (h2 := h'); auto.
    rewrite heap_update_spec2; auto.
    symmetry. apply Partition_spec1 with (h1 := h) (h2 := h'); auto.
    apply heap_update_dom2; auto.
    rewrite Partition_spec3 with (h1 := heap_update h k v) (h2 := h'); auto.
    symmetry. apply Partition_spec3 with (h1 := h) (h2 := h'); auto.
    rewrite heap_update_dom2; auto.
- exists (heap_clear h'' k).
  split.
  + apply heap_ext; intro.
    destruct (Z.eq_dec n k).
    rewrite e.
    rewrite heap_update_spec1.
    rewrite (Partition_spec1 _ _ _ H).
    apply heap_update_spec1.
    apply heap_update_dom1.
    rewrite heap_update_spec2; auto.
    rewrite heap_clear_spec2; auto.
  + pose proof (Partition_intro1 h h').
    destruct H0. intro. intro. destruct H0.
    eapply Partition_spec4. apply H. split; [| apply H1].
    destruct (Z.eq_dec k k0).
    rewrite e.
    apply heap_update_dom1.
    apply heap_update_dom2; auto.
    pose proof (heap_ext (heap_clear h'' k) x).
    rewrite H1. assumption. clear H1. intros.
    destruct (Z.eq_dec n k). rewrite e.
    rewrite heap_clear_spec1. symmetry.
    eapply Partition_spec3. apply H0.
    rewrite dom_spec; auto.
    eapply Partition_dom_right1. apply H.
    assert (dom h'' k). {
    rewrite dom_spec. intro.
    rewrite Partition_spec1 with (h1 := heap_update h k v) (h2 := h') in H1; auto.
    rewrite heap_update_spec1 in H1. inversion H1.
    apply heap_update_dom1. }
    apply heap_update_dom1.
    rewrite heap_clear_spec2; auto.
    destruct (dom_dec h' n).
    rewrite Partition_spec2 with (h1 := heap_update h k v) (h2 := h'); auto.
    symmetry. apply Partition_spec2 with (h1 := h) (h2 := h'); auto.
    destruct (dom_dec h n).
    rewrite Partition_spec1 with (h1 := heap_update h k v) (h2 := h'); auto.
    rewrite heap_update_spec2; auto.
    symmetry. apply Partition_spec1 with (h1 := h) (h2 := h'); auto.
    apply heap_update_dom2; auto.
    rewrite Partition_spec3 with (h1 := heap_update h k v) (h2 := h'); auto.
    symmetry. apply Partition_spec3 with (h1 := h) (h2 := h'); auto.
    rewrite heap_update_dom2; auto.
Qed.

Proposition heap_update_Partition (h h1 h2: heap) (k v: Z):
  Partition h h1 h2 -> ~ dom h2 k ->
  Partition (heap_update h k v) (heap_update h1 k v) h2.
intros.
pose proof (Partition_intro1 (heap_update h1 k v) h2).
destruct H1. intros. intro. destruct H1.
destruct (Z.eq_dec k k0). rewrite <- e in H2. auto.
rewrite heap_update_dom2 in H1; auto.
eapply Partition_spec4. apply H. split. apply H1. apply H2.
pose proof (heap_ext x (heap_update h k v)). destruct H2; auto.
intros.
destruct (Z.eq_dec n k).
rewrite e.
rewrite heap_update_spec1; auto.
rewrite <- heap_update_spec1 with (h := h1) (k := k).
apply Partition_spec1 with (h2 := h2); auto.
apply heap_update_dom1.
rewrite heap_update_spec2; auto.
destruct (dom_dec h2 n).
rewrite Partition_spec2 with (h1 := heap_update h1 k v) (h2 := h2); auto.
symmetry. eapply Partition_spec2. apply H. auto.
destruct (dom_dec h1 n).
rewrite Partition_spec1 with (h1 := heap_update h1 k v) (h2 := h2); auto.
rewrite heap_update_spec2; auto. symmetry.
eapply Partition_spec1. apply H. auto.
apply heap_update_dom2; auto.
rewrite Partition_spec3 with (h1 := heap_update h1 k v) (h2 := h2); auto.
symmetry. eapply Partition_spec3. apply H. auto. auto.
rewrite heap_update_dom2; auto.
Qed.

Proposition Partition_heap_clear (h h1 h2: heap) (k: Z):
  Partition (heap_clear h k) h1 h2 ->
  exists h11 h22, Partition h h11 h22 /\ h1 = heap_clear h11 k /\ h2 = heap_clear h22 k.
intros.
remember (h k); destruct o.
- exists (heap_update h1 k z). exists h2.
  split.
  pose proof (Partition_intro1 (heap_update h1 k z) h2).
  destruct H0. intros. intro. destruct H0.
  destruct (Z.eq_dec k k0).
  rewrite <- e in H1.
  pose proof (Partition_spec2 _ _ _ H _ H1).
  rewrite dom_spec in H1.
  rewrite heap_clear_spec1 in H2; auto.
  rewrite heap_update_dom2 in H0; auto.
  eapply Partition_spec4. apply H. split. apply H0. apply H1.
  pose proof (heap_ext x h). destruct H1; auto. intros.
  destruct (Z.eq_dec k n).
  rewrite <- e.
  rewrite Partition_spec1 with (h1 := heap_update h1 k z) (h2 := h2); auto.
  rewrite heap_update_spec1; auto.
  apply heap_update_dom1.
  destruct (dom_dec h1 n).
  rewrite Partition_spec1 with (h1 := heap_update h1 k z) (h2 := h2); auto.
  rewrite heap_update_spec2; auto.
  symmetry. rewrite <- heap_clear_spec2 with (k := k); auto.
  eapply Partition_spec1; auto. apply H.
  apply heap_update_dom2; auto.
  destruct (dom_dec h2 n).
  rewrite Partition_spec2 with (h1 := heap_update h1 k z) (h2 := h2); auto.
  symmetry. rewrite <- heap_clear_spec2 with (k := k); auto.
  eapply Partition_spec2; auto. apply H.
  rewrite Partition_spec3 with (h1 := heap_update h1 k z) (h2 := h2); auto.
  symmetry. rewrite <- heap_clear_spec2 with (k := k); auto.
  eapply Partition_spec3. apply H. auto. auto. rewrite heap_update_dom2; auto.
  split.
  apply heap_ext; intro.
  destruct (Z.eq_dec n k). rewrite e. rewrite heap_clear_spec1.
  remember (h1 k). destruct o; auto. exfalso.
  pose proof (Partition_spec1 _ _ _ H k). destruct H0.
  rewrite dom_spec. intro. rewrite <- Heqo0 in H0. inversion H0.
  rewrite heap_clear_spec1 in Heqo0. inversion Heqo0.
  rewrite heap_clear_spec2; auto.
  rewrite heap_update_spec2; auto.
  apply heap_ext; intro.
  destruct (Z.eq_dec n k). rewrite e. rewrite heap_clear_spec1.
  remember (h2 k). destruct o; auto. exfalso.
  pose proof (Partition_spec2 _ _ _ H k). destruct H0.
  rewrite dom_spec. intro. rewrite <- Heqo0 in H0. inversion H0.
  rewrite heap_clear_spec1 in Heqo0. inversion Heqo0.
  rewrite heap_clear_spec2; auto.
- exists h1. exists h2.
  split.
  pose proof (Partition_intro1 h1 h2). destruct H0.
  eapply Partition_spec4. apply H.
  pose proof (heap_ext x h). destruct H1; auto. intro.
  destruct (dom_dec h1 n).
  rewrite Partition_spec1 with (h1 := h1) (h2 := h2); auto.
  symmetry. rewrite <- heap_clear_spec2 with (k := k).
  eapply Partition_spec1; auto. apply H.
  intro. rewrite <- H2 in H1. pose proof (Partition_spec1 _ _ _ H k H1).
  rewrite heap_clear_spec1 in H3. rewrite dom_spec in H1; auto.
  destruct (dom_dec h2 n).
  rewrite Partition_spec2 with (h1 := h1) (h2 := h2); auto.
  symmetry. rewrite <- heap_clear_spec2 with (k := k).
  eapply Partition_spec2; auto. apply H.
  intro. rewrite <- H3 in H2. pose proof (Partition_spec2 _ _ _ H k H2).
  rewrite heap_clear_spec1 in H4. rewrite dom_spec in H2; auto.
  rewrite Partition_spec3 with (h1 := h1) (h2 := h2); auto.
  destruct (Z.eq_dec n k). rewrite e; auto.
  rewrite <- heap_clear_spec2 with (k := k); auto.
  symmetry. eapply Partition_spec3. apply H. auto. auto.
  split.
  apply heap_clear_not_dom_eq. intro.
  pose proof (Partition_dom_inv_left _ _ _ _ H H0).
  eapply heap_clear_dom1. apply H1.
  apply heap_clear_not_dom_eq. intro.
  pose proof (Partition_dom_inv_right _ _ _ _ H H0).
  eapply heap_clear_dom1. apply H1.
Qed.

Proposition heap_clear_Partition (h h1 h2: heap) (k: Z):
  Partition h h1 h2 ->
  Partition (heap_clear h k) (heap_clear h1 k) (heap_clear h2 k).
intros.
pose proof (Partition_intro1 (heap_clear h1 k) (heap_clear h2 k)).
destruct H0. intros. intro. destruct H0.
destruct (Z.eq_dec k0 k).
rewrite e in H0. eapply heap_clear_dom1. apply H0.
rewrite heap_clear_dom2 in H0, H1; auto.
eapply Partition_spec4. apply H. split. apply H0. apply H1.
pose proof (heap_ext (heap_clear h k) x). destruct H1; auto.
intros.
destruct (Z.eq_dec n k).
rewrite e. rewrite heap_clear_spec1. symmetry.
eapply Partition_spec3. apply H0.
apply heap_clear_dom1. apply heap_clear_dom1.
rewrite heap_clear_spec2; auto.
destruct (dom_dec h1 n).
rewrite Partition_spec1 with (h1 := h1) (h2 := h2); auto.
rewrite <- heap_clear_spec2 with (k := k); auto. symmetry.
eapply Partition_spec1. apply H0.
apply heap_clear_dom2; auto.
destruct (dom_dec h2 n).
rewrite Partition_spec2 with (h1 := h1) (h2 := h2); auto.
rewrite <- heap_clear_spec2 with (k := k); auto.
symmetry. eapply Partition_spec2. apply H0.
apply heap_clear_dom2; auto.
rewrite Partition_spec3 with (h1 := h1) (h2 := h2); auto.
symmetry. eapply Partition_spec3. apply H0.
rewrite heap_clear_dom2; auto.
rewrite heap_clear_dom2; auto.
Qed.

Proposition heap_clear_heap_update_Partition (h h' h'': heap) (k v: Z):
  Partition h'' h h' -> exists hh, Partition hh (heap_clear h k) (heap_update h' k v).
intros. apply Partition_intro1. intros. intro.
destruct H0. destruct (Z.eq_dec k k0).
rewrite <- e in *.
apply heap_clear_dom1 in H0; auto.
apply heap_clear_dom2 in H0; auto.
apply heap_update_dom2 in H1; auto.
eapply Partition_spec4. apply H. split. apply H0. apply H1.
Qed.

Proposition Partition_heap_clear_heap_update (h h' h'' hh: heap) (k v: Z):
  Partition h'' h h' -> Partition hh (heap_clear h k) (heap_update h' k v) ->
  hh = heap_update h'' k v.
intros. apply heap_ext; intro.
destruct (Z.eq_dec k n).
rewrite e. rewrite heap_update_spec1.
rewrite Partition_spec2 with (h1 := heap_clear h k) (h2 := heap_update h' k v); auto.
rewrite e. rewrite heap_update_spec1. auto.
rewrite e. apply heap_update_dom1.
rewrite heap_update_spec2; auto.
destruct (dom_dec h n).
rewrite Partition_spec1 with (h1 := heap_clear h k) (h2 := heap_update h' k v); auto.
rewrite heap_clear_spec2; auto.
symmetry. erewrite Partition_spec1. reflexivity. apply H. auto.
apply heap_clear_dom2; auto.
destruct (dom_dec h' n).
rewrite Partition_spec2 with (h1 := heap_clear h k) (h2 := heap_update h' k v); auto.
rewrite heap_update_spec2; auto.
symmetry. rewrite Partition_spec2 with (h1 := h) (h2 := h'); auto.
apply heap_update_dom2; auto.
rewrite Partition_spec3 with (h1 := heap_clear h k) (h2 := heap_update h' k v); auto.
symmetry. rewrite Partition_spec3 with (h1 := h) (h2 := h'); auto.
rewrite heap_clear_dom2; auto.
rewrite heap_update_dom2; auto.
Qed.

Proposition heap_clear_Partition_heap_update (h h' h'': heap) (k v: Z):
  Partition h'' (heap_clear h k) h' -> h k = Some v -> Partition (heap_update h'' k v) h (heap_clear h' k).
intros.
unfold Partition in *.
split; try split; try split; intros.
+ unfold dom in H1. unfold heap_update in H1. unfold dom. unfold heap_clear.
  destruct H. unfold dom in H. unfold heap_clear in H.
  specialize H with k0.
  destruct (Z.eq_dec k k0).
  left. intro. rewrite <- e in H3. rewrite H0 in H3. inversion H3.
  apply H in H1; clear H. auto.
+ intro. destruct H1.
  unfold heap_clear in H2. unfold dom in H1, H2.
  destruct (Z.eq_dec k k0). apply H2; auto.
  destruct H. destruct H3.
  eapply H3. unfold dom. unfold heap_clear. split.
  2: apply H2.
  destruct (Z.eq_dec k k0). exfalso. apply n. auto. auto.
+ unfold heap_update.
  destruct (Z.eq_dec k k0). rewrite <- e. auto.
  destruct H. destruct H2. destruct H3.
  pose proof (H3 k0).
  rewrite H5.
  unfold heap_clear. destruct (Z.eq_dec k k0).
  exfalso. apply n. auto. auto.
  unfold dom. unfold heap_clear.
  destruct (Z.eq_dec k k0).
  exfalso. apply n. auto. intro.
  unfold dom in H1. rewrite H6 in H1.
  apply H1. auto.
+ unfold heap_update. unfold heap_clear.
  unfold dom in H1. unfold heap_clear in H1.
  destruct (Z.eq_dec k k0).
  exfalso. apply H1. auto.
  destruct H. destruct H2. destruct H3.
  apply H4. unfold dom. auto.
Qed.

Proposition heap_clear_Partition_heap_clear (h h' h'': heap) (k: Z):
  Partition h'' (heap_clear h k) h' -> h k = None -> Partition (heap_clear h'' k) h (heap_clear h' k).
intros.
unfold Partition in *.
split; try split; try split; intros.
+ unfold dom in H1. unfold heap_clear in H1.
  destruct (Z.eq_dec k k0). exfalso. apply H1; auto.
  destruct H. specialize H with k0.
  fold (dom h'' k0) in H1. apply H in H1. destruct H1.
  left. unfold dom in H1. unfold heap_clear in H1.
  unfold dom. destruct (Z.eq_dec k k0). exfalso. apply n; auto.
  auto. right. unfold dom. unfold heap_clear.
  destruct (Z.eq_dec k k0). exfalso. apply n. auto.
  unfold dom in H1. auto.
+ intro. destruct H1.
  unfold dom in H1.
  destruct (Z.eq_dec k k0). rewrite e in H0. apply H1. auto.
  destruct H. destruct H3. specialize H3 with k0. apply H3. split.
  unfold dom. unfold heap_clear. destruct (Z.eq_dec k k0).
  exfalso. apply n. auto. auto.
  unfold dom. unfold dom in H2. unfold heap_clear in H2.
  destruct (Z.eq_dec k k0). exfalso. apply n; auto. auto.
+ unfold heap_clear.
  destruct (Z.eq_dec k k0). exfalso. unfold dom in H1.
    apply H1. rewrite <- e. auto.
  destruct H. destruct H2. destruct H3.
  rewrite H3.
  unfold heap_clear.
  destruct (Z.eq_dec k k0). exfalso. apply n. auto. auto.
  unfold dom. unfold heap_clear.
  destruct (Z.eq_dec k k0). exfalso. apply n. auto.
  unfold dom in H1. auto.
+ unfold heap_clear. unfold dom in H1. unfold heap_clear in H1.
  destruct (Z.eq_dec k k0). auto.
  destruct H. destruct H2. destruct H3. apply H4.
  unfold dom. auto.
Qed.

(* ==================== *)
(* CLASSICAL ASSERTIONS *)
(* ==================== *)

(* Assertions are shallow, but finitely based *)
Record cassert: Type := mkcassert {
  cval: heap * store -> Prop;
  cvar: list V;
  ccond: forall (h: heap) (s t: store), eq_restr s t cvar -> cval (h, s) <-> cval (h, t);
  cstable: forall (h: heap) (s: store), ~~cval (h, s) -> cval (h, s)
}.
Coercion cval: cassert >-> Funclass.

Proposition ctest_cond (g: guard):
  forall (h : heap) (s t : store),
   eq_restr s t (gvar g) -> g s = true <-> g t = true.
intros.
rewrite gcond with (t := t).
apply iff_refl.
assumption.
Qed.
Proposition ctest_stable (g: guard):
  forall (h : heap) (s : store),
   ~ ~ g s = true -> g s = true.
intros. destruct (g s); auto.
Qed.
Definition ctest (g: guard): cassert :=
  mkcassert (fun '(h, s) => gval g s = true) (gvar g) (ctest_cond g) (ctest_stable g).

Proposition chasval_cond (e1 e2: expr):
  forall (h : heap) (s t : store),
   eq_restr s t (evar e1 ++ evar e2) ->
   h (e1 s) = Some (e2 s) <->
   h (e1 t) = Some (e2 t).
intros.
apply eq_restr_split in H; destruct H.
split; intro.
- rewrite <- econd with (s := s); auto.
  rewrite <- (econd e2) with (s := s); auto.
- rewrite econd with (t := t); auto.
  rewrite (econd e2) with (t := t); auto.
Qed.
Proposition chasval_stable (e1 e2: expr):
  forall (h : heap) (s : store),
   ~ ~ (h (e1 s) = Some (e2 s)) ->
   h (e1 s) = Some (e2 s).
intros.
destruct (h (e1 s)).
remember (e2 s).
destruct (Z.eq_dec z z0).
rewrite e; auto.
exfalso; apply H. intro. inversion H0.
apply n; auto.
exfalso.
apply H. intro. inversion H0.
Qed.
Definition chasval (e1 e2: expr): cassert :=
  mkcassert (fun '(h, s) => h (e1 s) = Some (e2 s)) (evar e1 ++ evar e2)
    (chasval_cond e1 e2) (chasval_stable e1 e2).

Proposition cland_cond (p q: cassert):
  forall (h : heap) (s t : store),
   eq_restr s t (cvar p ++ cvar q) ->
   p (h, s) /\ q (h, s) <->
   p (h, t) /\ q (h, t).
intros.
apply eq_restr_split in H; destruct H.
split; intro; destruct H1.
rewrite ccond with (t := t) in H1; auto.
rewrite ccond with (t := t) in H2; auto.
rewrite <- ccond with (s := s) in H1; auto.
rewrite <- ccond with (s := s) in H2; auto.
Qed.
Proposition cland_stable (p q: cassert):
  forall (h : heap) (s : store),
   ~ ~ (p (h, s) /\ q (h, s)) ->
   p (h, s) /\ q (h, s).
intros; split; apply cstable; intro;
apply H; intro; destruct H1; apply H0; auto.
Qed.
Definition cland (p q: cassert): cassert :=
  mkcassert (fun '(h, s) => p (h, s) /\ q (h, s)) (cvar p ++ cvar q)
    (cland_cond p q) (cland_stable p q).

Proposition clor_cond (p q: cassert):
  forall (h : heap) (s t : store),
   eq_restr s t (cvar p ++ cvar q) ->
   ~(~p (h, s) /\ ~q (h, s)) <->
   ~(~p (h, t) /\ ~q (h, t)).
intros.
apply eq_restr_split in H; destruct H.
split; intro; intro; destruct H2;
apply H1; split; intro.
rewrite ccond with (t := t) in H4; auto.
rewrite ccond with (t := t) in H4; auto.
rewrite <- ccond with (s := s) in H4; auto.
rewrite <- ccond with (s := s) in H4; auto.
Qed.
Proposition clor_stable (p q: cassert):
  forall (h : heap) (s : store),
   ~ ~ (~(~p (h, s) /\ ~q (h, s))) ->
   ~(~p (h, s) /\ ~q (h, s)).
intros; intro; destruct H0.
apply H; intro; apply H2; split; auto.
Qed.
Definition clor (p q: cassert): cassert :=
  mkcassert (fun '(h, s) => ~(~p (h, s) /\ ~q (h, s))) (cvar p ++ cvar q)
    (clor_cond p q) (clor_stable p q).

Proposition climp_cond (p q: cassert):
  forall (h : heap) (s t : store),
   eq_restr s t (cvar p ++ cvar q) ->
   (p (h, s) -> q (h, s)) <->
   (p (h, t) -> q (h, t)).
intros.
apply eq_restr_split in H; destruct H.
split; intros.
apply ccond with (s := s); auto.
apply H1.
apply ccond with (t := t); auto.
apply ccond with (t := t); auto.
apply H1.
apply ccond with (s := s); auto.
Qed.
Proposition climp_stable (p q: cassert):
  forall (h : heap) (s : store),
   ~ ~ (p (h, s) -> q (h, s)) ->
   (p (h, s) -> q (h, s)).
intros.
apply cstable; intro.
apply H; intro.
apply H1; apply H2; auto.
Qed.
Definition climp (p q: cassert): cassert :=
  mkcassert (fun '(h, s) => p (h, s) -> q (h, s)) (cvar p ++ cvar q)
    (climp_cond p q) (climp_stable p q).

Proposition clexists_cond (x: V) (p: cassert):
  forall (h : heap) (s t : store),
   eq_restr s t (remove Nat.eq_dec x (cvar p)) ->
   ~ (forall v : Z, ~ p (h, store_update s x v)) <->
   ~ (forall v : Z, ~ p (h, store_update t x v)).
intros; split; intro; intro; apply H0; intro; intro.
- apply H1 with (v := v).
  apply ccond with (s := store_update s x v); auto.
  intro; intro; unfold store_update.
  destruct (Nat.eq_dec x x0); auto.
  apply H.
  apply In_remove; auto.
- apply H1 with (v := v).
  apply ccond with (t := store_update t x v); auto.
  intro; intro; unfold store_update.
  destruct (Nat.eq_dec x x0); auto.
  apply H.
  apply In_remove; auto.
Qed.
Proposition clexists_stable (x: V) (p: cassert):
  forall (h : heap) (s : store),
   ~ ~ ~ (forall v : Z, ~ p (h, store_update s x v)) ->
   ~ (forall v : Z, ~ p (h, store_update s x v)).
intros; intro.
apply H; intro; apply H1; intros; intro.
apply H0 with (v := v).
auto.
Qed.
Definition clexists (x: V) (p: cassert): cassert :=
  mkcassert (fun '(h, s) => ~forall v, ~p (h, store_update s x v)) (remove Nat.eq_dec x (cvar p))
  (clexists_cond x p) (clexists_stable x p).

Proposition clforall_cond (x: V) (p: cassert):
  forall (h : heap) (s t : store),
   eq_restr s t (remove Nat.eq_dec x (cvar p)) ->
   (forall v : Z, p (h, store_update s x v)) <->
   (forall v : Z, p (h, store_update t x v)).
intros; split; intro; intro.
- apply ccond with (s := store_update s x v).
  intro; intro; unfold store_update.
  destruct (Nat.eq_dec x x0); auto.
  apply H.
  apply In_remove; auto.
  apply H0.
- apply ccond with (t := store_update t x v).
  intro; intro; unfold store_update.
  destruct (Nat.eq_dec x x0); auto.
  apply H.
  apply In_remove; auto.
  apply H0.
Qed.
Proposition clforall_stable (x: V) (p: cassert):
  forall (h : heap) (s : store),
   ~ ~ (forall v : Z, p (h, store_update s x v)) ->
   (forall v : Z, p (h, store_update s x v)).
intros. apply cstable; intro. apply H; intro.
apply H0.
apply H1.
Qed.
Definition clforall (x: V) (p: cassert): cassert :=
  mkcassert (fun '(h, s) => forall v, p (h, store_update s x v)) (remove Nat.eq_dec x (cvar p))
  (clforall_cond x p) (clforall_stable x p).

Proposition csand_cond (p q: cassert):
  forall (h : heap) (s t : store),
   eq_restr s t (cvar p ++ cvar q) ->
   ~ (forall h1 h2 : heap, ~ (Partition h h1 h2 /\ p (h1, s) /\ q (h2, s))) <->
   ~ (forall h1 h2 : heap, ~ (Partition h h1 h2 /\ p (h1, t) /\ q (h2, t))).
intros; split; intro; intro; apply H0; intros; intro.
- destruct H2.
  eapply H1. split. apply H2.
  destruct H3.
  apply eq_restr_split in H; destruct H.
  split.
  apply ccond with (s := s); auto.
  apply ccond with (s := s); auto.
- destruct H2.
  eapply H1. split. apply H2.
  destruct H3.
  apply eq_restr_split in H; destruct H.
  split.
  apply ccond with (t := t); auto.
  apply ccond with (t := t); auto.
Qed.
Proposition csand_stable (p q: cassert):
  forall (h : heap) (s : store),
   ~ ~ ~ (forall h1 h2 : heap, ~ (Partition h h1 h2 /\ p (h1, s) /\ q (h2, s))) ->
   ~ (forall h1 h2 : heap, ~ (Partition h h1 h2 /\ p (h1, s) /\ q (h2, s))).
intros; intro. apply H; intro. auto.
Qed.
Definition csand (p q: cassert): cassert :=
  mkcassert (fun '(h, s) => ~forall h1 h2, ~(Partition h h1 h2 /\ p (h1, s) /\ q (h2, s)))
    (cvar p ++ cvar q) (csand_cond p q) (csand_stable p q).

Proposition csimp_cond (p q: cassert):
  forall (h : heap) (s t : store),
   eq_restr s t (cvar p ++ cvar q) ->
   (forall h'' h' : heap, Partition h'' h h' -> p (h', s) -> q (h'', s)) <->
   forall h'' h' : heap, Partition h'' h h' -> p (h', t) -> q (h'', t).
intros.
apply eq_restr_split in H; destruct H.
split; intro; intros.
apply ccond with (s := s); auto.
apply H1 with (h' := h'); auto.
apply ccond with (t := t); auto.
apply ccond with (t := t); auto.
apply H1 with (h' := h'); auto.
apply ccond with (s := s); auto.
Qed.
Proposition csimp_stable (p q: cassert):
  forall (h : heap) (s : store),
   ~ ~ (forall h'' h' : heap, Partition h'' h h' -> p (h', s) -> q (h'', s)) ->
   forall h'' h' : heap, Partition h'' h h' -> p (h', s) -> q (h'', s).
intros. apply cstable; intro. apply H; intro. apply H2.
apply H3 with (h' := h'); auto.
Qed.
Definition csimp (p q: cassert): cassert :=
  mkcassert (fun '(h, s) => forall h'' h', Partition h'' h h' -> p (h', s) -> q (h'', s))
    (cvar p ++ cvar q) (csimp_cond p q) (csimp_stable p q).

(* Abbreviations *)

Definition cltrue: cassert := (ctest true).
Definition clfalse: cassert := (ctest false).
Definition clnot (p: cassert): cassert := (climp p clfalse).
Definition clequiv (p q: cassert): cassert := (cland (climp p q) (climp q p)).
Definition chasvaldash (e: expr): cassert :=
  let y := fresh (evar e) in clexists y (chasval e y).
Definition cemp: cassert := (clforall dummy (clnot (chasvaldash dummy))).
Definition cpointsto (e e': expr): cassert :=
  let x := fresh (evar e) in cland (chasval e e') (clforall x (climp (chasvaldash x) (ctest (equals x e)))).
Definition cpointstodash (e: expr): cassert :=
  let y := fresh (evar e) in clexists y (cpointsto e y).
Definition chasval_alt (e e': expr): cassert :=
  csand (cpointsto e e') (ctest true).
Definition chasvaldash_alt (e: expr): cassert :=
  csand (cpointstodash e) (ctest true).

(* Operations on assertions *)

Proposition csub_cond (p: cassert) (x: V) (e: expr):
  forall (h : heap) (s t : store),
   eq_restr s t (remove Nat.eq_dec x (cvar p) ++ evar e) ->
   p (h, store_update s x (e s)) <->
   p (h, store_update t x (e t)).
intros.
apply eq_restr_split in H; destruct H.
split; intro.
- pose proof (econd e s t H0).
  rewrite <- H2.
  apply ccond with (s := store_update s x (e s)); auto.
  intro; intro; unfold store_update.
  destruct (Nat.eq_dec x x0); auto.
  apply H.
  apply In_remove; auto.
- pose proof (econd e s t H0).
  rewrite H2.
  apply ccond with (t := store_update t x (e t)); auto.
  intro; intro; unfold store_update.
  destruct (Nat.eq_dec x x0); auto.
  apply H.
  apply In_remove; auto.
Qed.
Proposition csub_stable (p: cassert) (x: V) (e: expr):
  forall (h : heap) (s : store),
   ~ ~ p (h, store_update s x (e s)) ->
   p (h, store_update s x (e s)).
intros. apply cstable. auto.
Qed.
Definition csub (p: cassert) (x: V) (e: expr): cassert :=
  mkcassert (fun '(h, s) => p (h, store_update s x (eval e s)))
    (remove Nat.eq_dec x (cvar p) ++ evar e) (csub_cond p x e) (csub_stable p x e).

Proposition csub_heap_update_cond (p: cassert) (x: V) (e: expr):
  forall (h : heap) (s t : store),
   eq_restr s t (x :: cvar p ++ evar e) ->
   p (heap_update h (s x) (e s), s) <->
   p (heap_update h (t x) (e t), t).
intros.
apply eq_restr_cons in H; destruct H.
apply eq_restr_split in H0; destruct H0.
rewrite H.
pose proof (econd e s t H1).
rewrite H2.
apply ccond.
auto.
Qed.
Proposition csub_heap_update_stable (p: cassert) (x: V) (e: expr):
  forall (h : heap) (s : store),
   ~ ~ p (heap_update h (s x) (e s), s) ->
   p (heap_update h (s x) (e s), s).
intros. apply cstable. auto.
Qed.
Definition csub_heap_update (p: cassert) (x: V) (e: expr): cassert :=
  mkcassert (fun '(h, s) => p (heap_update h (s x) (e s), s))
    (x :: cvar p ++ evar e) (csub_heap_update_cond p x e) (csub_heap_update_stable p x e).

Proposition csub_heap_clear_cond (p: cassert) (x: V):
  forall (h : heap) (s t : store),
   eq_restr s t (x :: cvar p) ->
   p (heap_clear h (s x), s) <->
   p (heap_clear h (t x), t).
intros.
apply eq_restr_cons in H; destruct H.
rewrite H.
apply ccond.
auto.
Qed.
Proposition csub_heap_clear_stable (p: cassert) (x: V):
  forall (h : heap) (s : store),
   ~ ~ p (heap_clear h (s x), s) ->
   p (heap_clear h (s x), s).
intros. apply cstable. assumption.
Qed.
Definition csub_heap_clear (p: cassert) (x: V): cassert :=
  mkcassert (fun '(h, s) => p (heap_clear h (s x), s))
    (x :: cvar p) (csub_heap_clear_cond p x) (csub_heap_clear_stable p x).

(* Properties of assertions *)
Definition valid (p: cassert): Prop :=
  forall (h: heap) (s: store), p (h, s).

(* ===================================== *)
(* BASIC INSTRUCTIONS AND WHILE PROGRAMS *)
(* ===================================== *)

Inductive assignment :=
| basic: V -> expr -> assignment
| lookup: V -> expr -> assignment
| mutation: V -> expr -> assignment
| new: V -> expr -> assignment
| dispose: V -> assignment.

Definition avar (a: assignment): list V :=
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
  | assign a => avar a
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

Proposition while_unfold (g: guard) (S1: program):
  forall h s o,
    bigstep (while g S1) (h, s) o <->
    bigstep (ite g (comp S1 (while g S1)) skip) (h, s) o.
intros. split; intros.
- inversion H.
  apply step_ite_true; auto.
  destruct o. destruct p.
  eapply step_comp. apply H6. apply H7.
  eapply step_comp_fail2. apply H6. apply H7.
  apply step_ite_false; auto.
  apply step_skip.
  apply step_ite_true; auto.
  apply step_comp_fail1; auto.
- inversion H.
  inversion H7.
  eapply step_while_true; auto.
  apply H13. apply H14.
  eapply step_while_fail; auto.
  eapply step_while_true; auto.
  apply H13. apply H14.
  inversion H7.
  apply step_while_false; auto.
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

(* ================ *)
(* PROGRAM MODALITY *)
(* ================ *)

Proposition bigstep_cond (S1: program) (p: heap * store) (o: option (heap * store)):
  bigstep S1 p o ->
  forall xs, (forall x, In x (pvar S1) -> In x xs) ->
  forall h s, (h, s) = p ->
  forall t, eq_restr s t xs ->
  (forall h' s', Some (h', s') = o ->
    exists t', eq_restr s' t' xs /\ bigstep S1 (h, t) (Some (h', t'))) /\
  (None = o ->
    bigstep S1 (h, t) None).
intro.
induction H; intros xs G h0 s0 G1 t G3; inversion G1; clear G1;
(split; [intros h'0 s'0 G2; inversion G2; clear G2 | intro G2; inversion G2; clear G2 ]).
- rewrite H1 in G3.
  exists (store_update t x (e t)). split.
  + intro; intro.
    unfold store_update.
    destruct (Nat.eq_dec x x0).
    apply econd.
    eapply eq_restr_incl; [|apply G3].
    intros. apply G. simpl; auto.
    apply G3; auto.
  + apply step_basic.
- exists (store_update t x v). split.
  + intro; intro.
    rewrite <- H2.
    unfold store_update.
    destruct (Nat.eq_dec x x0); auto.
  + apply step_lookup.
    pose proof (econd e s t).
    rewrite <- H0; auto.
    rewrite <- H2.
    eapply eq_restr_incl; [|apply G3].
    intros. apply G. simpl; auto.
- apply step_lookup_fail.
  erewrite <- econd. apply H.
  rewrite <- H2.
  eapply eq_restr_incl; [|apply G3].
  intros. apply G. simpl. auto.
- exists t. split.
  + rewrite <- H2. auto.
  + assert (s x = t x).
    { rewrite H2 in G3.
      apply G3. apply G. simpl. auto. }
    assert (e s = e t).
    { apply econd.
      eapply eq_restr_incl; [ | rewrite H2 in G3; apply G3].
      intros. apply G. simpl. auto. }
    rewrite H0.
    rewrite H5.
    apply step_mutation.
    rewrite <- H0. assumption.
- apply step_mutation_fail.
  assert (s x = t x).
  rewrite H2 in G3. apply G3.
  apply G. simpl. auto.
  rewrite <- H0. auto.
- exists (store_update t x n).
  split. rewrite H2 in G3.
  apply eq_restr_store_update; assumption.
  assert (e s = e t).
  { apply econd.
    eapply eq_restr_incl; [ | rewrite H2 in G3; apply G3].
    intros. apply G. simpl. auto. }
  rewrite H0.
  apply step_new. assumption.
- exists t. split.
  rewrite H2 in G3. auto.
  assert (s x = t x).
  { rewrite H2 in G3.
    apply G3. apply G. simpl. auto. }
  rewrite H0.
  apply step_dispose.
  rewrite <- H0. assumption.
- apply step_dispose_fail.
  assert (s x = t x).
  rewrite H2 in G3. apply G3.
  apply G. simpl. auto.
  rewrite <- H0. auto.
- exists t. split.
  rewrite <- H1. auto.
  apply step_skip.
- destruct IHbigstep1 with (xs := xs) (h := h) (s := s) (t := t); auto.
  intros. apply G. simpl. apply in_or_app; auto. rewrite <- H3. auto.
  edestruct H1. reflexivity. destruct H7.
  destruct IHbigstep2 with (xs := xs) (h := h') (s := s') (t := x); auto.
  intros. apply G. simpl. apply in_or_app; auto.
  edestruct H9. reflexivity. destruct H11.
  exists x0. split; auto.
  eapply step_comp.
  apply H8.
  apply H12.
- apply step_comp_fail1.
  destruct IHbigstep with (xs := xs) (h := h) (s := s) (t := t); auto.
  intros. apply G. simpl. apply in_or_app; auto. rewrite <- H2. auto.
- destruct IHbigstep1 with (xs := xs) (h := h) (s := s) (t := t); auto.
  intros. apply G. simpl. apply in_or_app; auto. rewrite <- H3. auto.
  edestruct H1. reflexivity. destruct H5.
  eapply step_comp_fail2.
  apply H6.
  destruct IHbigstep2 with (xs := xs) (h := h') (s := s') (t := x); auto.
  intros. apply G. simpl. apply in_or_app; auto.
- destruct o. destruct p.
  destruct IHbigstep with (xs := xs) (h := h) (s := s) (t := t); auto.
  intros. apply G. simpl. apply in_or_app. right. apply in_or_app; auto.
  rewrite <- H3; auto.
  destruct H4 with (h' := h1) (s' := s1); auto. destruct H6.
  inversion H1.
  exists x. split; auto.
  apply step_ite_true; auto.
  rewrite H3 in G3.
  rewrite <- gcond with (s := s); auto.
  eapply eq_restr_incl; [|apply G3]. intros.
  apply G. simpl. apply in_or_app; auto.
  inversion H1.
- destruct o. inversion H1.
  destruct IHbigstep with (xs := xs) (h := h) (s := s) (t := t); auto.
  intros. apply G. simpl. apply in_or_app. right. apply in_or_app; auto.
  rewrite <- H3; auto.
  rewrite H3 in G3.
  apply step_ite_true.
  rewrite <- gcond with (s := s); auto.
  eapply eq_restr_incl; [|apply G3]. intros.
  apply G. simpl. apply in_or_app; auto.
  apply H5. auto.
- destruct o. destruct p.
  destruct IHbigstep with (xs := xs) (h := h) (s := s) (t := t); auto.
  intros. apply G. simpl. apply in_or_app. right. apply in_or_app; auto.
  rewrite <- H3; auto.
  destruct H4 with (h' := h1) (s' := s1); auto. destruct H6.
  inversion H1.
  exists x. split; auto.
  apply step_ite_false; auto.
  rewrite H3 in G3.
  rewrite <- gcond with (s := s); auto.
  eapply eq_restr_incl; [|apply G3]. intros.
  apply G. simpl. apply in_or_app; auto.
  inversion H1.
- destruct o. inversion H1.
  destruct IHbigstep with (xs := xs) (h := h) (s := s) (t := t); auto.
  intros. apply G. simpl. apply in_or_app. right. apply in_or_app; auto.
  rewrite <- H3; auto.
  rewrite H3 in G3.
  apply step_ite_false.
  rewrite <- gcond with (s := s); auto.
  eapply eq_restr_incl; [|apply G3]. intros.
  apply G. simpl. apply in_or_app; auto.
  apply H5. auto.
- destruct o; inversion H2. destruct p; inversion H6.
  destruct IHbigstep1 with (xs := xs) (h := h) (s := s) (t := t); auto.
  intros. apply G. simpl. apply in_or_app; auto. rewrite H4 in G3; auto.
  destruct H5 with (h' := h') (s' := s'); auto. destruct H10.
  destruct IHbigstep2 with (xs := xs) (h := h') (s := s') (t := x); auto.
  destruct H12 with (h' := h1) (s' := s1); auto. destruct H14.
  exists x0.
  split; auto.
  eapply step_while_true.
  rewrite H4 in G3.
  rewrite <- gcond with (s := s); auto.
  intro; intro. apply G3. apply G. simpl. apply in_or_app; auto.
  apply H11.
  auto.
- destruct o; inversion H2.
  destruct IHbigstep1 with (xs := xs) (h := h) (s := s) (t := t); auto.
  intros. apply G. simpl. apply in_or_app; auto. rewrite H4 in G3; auto.
  destruct H5 with (h' := h') (s' := s'); auto. destruct H7.
  destruct IHbigstep2 with (xs := xs) (h := h') (s := s') (t := x); auto.
  eapply step_while_true.
  erewrite <- gcond. apply H.
  rewrite H4 in G3.
  eapply eq_restr_incl; [|apply G3].
  intros. apply G. simpl.
  apply in_or_app. auto.
  apply H8.
  apply H10. auto.
- exists t. split. rewrite <- H2. assumption.
  apply step_while_false.
  erewrite <- gcond. apply H.
  rewrite H2 in G3.
  eapply eq_restr_incl; [|apply G3].
  intros. apply G. simpl.
  apply in_or_app. auto.
- destruct IHbigstep with (xs := xs) (h := h) (s := s) (t := t); auto.
  intros. apply G. simpl. apply in_or_app; auto. rewrite H3 in G3; auto.
  apply step_while_fail.
  erewrite <- gcond. apply H.
  rewrite H3 in G3.
  eapply eq_restr_incl; [|apply G3].
  intros. apply G. simpl.
  apply in_or_app. auto.
  apply H4. auto.
Qed.

Proposition cwlp_cond (S1: program) (q: cassert):
  forall (h : heap) (s t : store),
   eq_restr s t (pvar S1 ++ cvar q) ->
   (~ bigstep S1 (h, s) None /\ forall (h' : heap) (s' : store),
      bigstep S1 (h, s) (Some (h', s')) -> q (h', s')) <->
   (~ bigstep S1 (h, t) None /\ forall (h' : heap) (s' : store),
      bigstep S1 (h, t) (Some (h', s')) -> q (h', s')).
intros; split; intro; destruct H0.
- split.
  + intro.
    pose proof (bigstep_cond S1 (h, t) None H2 (pvar S1 ++ cvar q)).
    destruct H3 with (h := h) (s := t) (t := s); auto.
    intros. apply in_or_app; auto.
    apply eq_restr_comm. apply H.
  + intros.
    pose proof (bigstep_cond S1 (h, t) (Some (h', s')) H2 (pvar S1 ++ cvar q)).
    destruct H3 with (h := h) (s := t) (t := s); auto.
    intros. apply in_or_app; auto.
    apply eq_restr_comm. apply H.
    destruct H4 with (h' := h') (s' := s'); auto. destruct H6.
    rewrite ccond with (t := x).
    apply H1. assumption.
    eapply eq_restr_incl; [|apply H6].
    intros. apply in_or_app. auto.
- split.
  + intro.
    pose proof (bigstep_cond S1 (h, s) None H2 (pvar S1 ++ cvar q)).
    destruct H3 with (h := h) (s := s) (t := t); auto.
    intros. apply in_or_app; auto.
  + intros.
    pose proof (bigstep_cond S1 (h, s) (Some (h', s')) H2 (pvar S1 ++ cvar q)).
    destruct H3 with (h := h) (s := s) (t := t); auto.
    intros. apply in_or_app; auto.
    destruct H4 with (h' := h') (s' := s'); auto. destruct H6.
    rewrite ccond with (t := x).
    apply H1. assumption.
    eapply eq_restr_incl; [|apply H6].
    intros. apply in_or_app. auto.
Qed.
Proposition cwlp_stable (S1: program) (q: cassert):
  forall (h : heap) (s : store),
   ~ ~ (~ bigstep S1 (h, s) None /\ forall (h' : heap) (s' : store),
      bigstep S1 (h, s) (Some (h', s')) -> q (h', s')) ->
   (~ bigstep S1 (h, s) None /\ forall (h' : heap) (s' : store),
      bigstep S1 (h, s) (Some (h', s')) -> q (h', s')).
intros. split.
intro. apply H. intro. destruct H1.
apply H1. assumption.
intros. apply cstable. intro.
apply H. intro. destruct H2.
apply H3 in H0.
apply H1. assumption.
Qed.
Definition cwlp (S1: program) (q: cassert): cassert :=
  mkcassert (fun '(h, s) => ~bigstep S1 (h, s) None /\
      forall h' s', bigstep S1 (h, s) (Some (h', s')) -> q (h', s'))
    (pvar S1 ++ cvar q) (cwlp_cond S1 q) (cwlp_stable S1 q).


