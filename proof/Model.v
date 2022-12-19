Require Export FunctionalExtensionality.
Require Export PropExtensionality.
Require Export PeanoNat.
Require Export Classical.

Require Coq.Lists.List.
Require Coq.Vectors.Vector.

Record finite (T: Type) := mkfinite
{ listing: list T
; listing_full: forall (t: T), List.In t listing }.

Record denumerable (T: Type) := mkdenumerable
{ enumerate: nat -> T
; enumerate_inject: forall (n m: nat), enumerate n = enumerate m -> n = m
; enumerate_surject: forall (t: T), exists (n: nat), enumerate n = t }.

Inductive countable (T: Type) :=
| is_finite: finite T -> countable T
| is_infinite: denumerable T -> countable T.

Record signature: Type := mksignature
{ Func: Set
; arity: Func -> nat
; Pred: Set
; adic: Pred -> nat }.
Arguments arity {_} _.
Arguments adic {_} _.

Record csignature: Type := mkcsignature
{ sig :> signature
; Func_countable: countable (Func sig)
; Pred_countable: countable (Pred sig) }.

Record bcsignature: Type := mkbcsignature
{ sig2 :> csignature
; bin_enumerate: nat -> Pred sig2
; bin_inject: forall (n m: nat), bin_enumerate n = bin_enumerate m -> n = m
; bin_surject: forall (P: Pred sig2), exists (n: nat), bin_enumerate n = P }.

Definition V := nat.
Definition dummy1: V := 0.
Definition dummy2: V := 1.

Inductive term (Sigma: signature): Set :=
| id: V -> term Sigma
| app (f: Func Sigma): Vector.t (term Sigma) (arity f) -> term Sigma.
Arguments app {_} _ _.

Fixpoint freevartl {Sigma: signature} (t: term Sigma): list V :=
match t with
| id _ x => List.cons x List.nil
| app _ arg => Vector.fold_right (@List.app V)
    (Vector.map (@freevartl Sigma) arg) List.nil
end.

Definition freevart {Sigma: signature} (t: term Sigma): V -> Prop :=
fun x => List.In x (freevartl t).

Inductive formula (Sigma: signature): Set :=
| eq: term Sigma -> term Sigma -> formula Sigma
| prim (P: Pred Sigma): Vector.t (term Sigma) (adic P) -> formula Sigma
| lnot: formula Sigma -> formula Sigma
| land: formula Sigma -> formula Sigma -> formula Sigma
| lforall: V -> formula Sigma -> formula Sigma.
Arguments eq {_} _ _.
Arguments prim {_} _ _.
Arguments lnot {_} _.
Arguments land {_} _ _.
Arguments lforall {_} _ _.

Definition lor {Sigma: signature} (phi psi: formula Sigma): formula Sigma :=
  lnot (land (lnot phi) (lnot psi)).
Definition limp {Sigma: signature} (phi psi: formula Sigma): formula Sigma :=
  lor (lnot phi) psi.
Definition lbimp {Sigma: signature} (phi psi: formula Sigma): formula Sigma :=
  land (limp phi psi) (limp psi phi).
Definition lexists {Sigma: signature} (x: V) (phi: formula Sigma): formula Sigma :=
  lnot (lforall x (lnot phi)).

Fixpoint freevarfl {Sigma: signature} (phi: formula Sigma): list V :=
match phi with
| eq t1 t2 => List.app (freevartl t1) (freevartl t2)
| prim _ arg => Vector.fold_right (@List.app V)
    (Vector.map (@freevartl Sigma) arg) List.nil
| lnot phi => freevarfl phi
| land phi psi => List.app (freevarfl phi) (freevarfl psi)
| lforall x phi => List.remove (Nat.eq_dec) x (freevarfl phi)
end.

Definition freevarf {Sigma: signature} (phi: formula Sigma): V -> Prop :=
fun x => List.In x (freevarfl phi).

Record binformula (Sigma: signature) := mkbinformula
{ binformula_form: formula Sigma
; binformula_prop: forall x, freevarf binformula_form x ->
    x = dummy1 \/ x = dummy2
}.
Coercion binformula_form: binformula >-> formula.

Record model (Sigma: signature): Type := mkstructure
{ domain: Set
; element: domain
; func (f: Func Sigma): Vector.t domain (arity f) -> domain
; pred (P: Pred Sigma): Vector.t domain (adic P) -> Prop
}.
Coercion domain: model >-> Sortclass.
Arguments domain {_} _.
Arguments element {_} _.
Arguments func {_} {_} _ _.
Arguments pred {_} {_} _ _.

Definition valuation {Sigma: signature} (M: model Sigma) := V -> M.

Definition nulval {Sigma: signature} (M: model Sigma): valuation M :=
fun x => element M.

Definition update {Sigma: signature} {M: model Sigma}
  (s: valuation M) (x: V) (d: M): valuation M :=
fun y => if Nat.eq_dec x y then d else s y.

Fixpoint interp {Sigma: signature} {M: model Sigma}
  (s: valuation M) (t: term Sigma): M :=
match t with
| id _ x => s x
| app f arg => func f (Vector.map (interp s) arg)
end.

Fixpoint satisfy {Sigma: signature} {M: model Sigma}
  (s: valuation M) (phi: formula Sigma): Prop :=
match phi with
| eq t1 t2 => interp s t1 = interp s t2
| prim p arg => pred p (Vector.map (interp s) arg)
| lnot phi => ~satisfy s phi
| land phi psi => satisfy s phi /\ satisfy s psi
| lforall x phi => forall (d: domain M), satisfy (update s x d) phi
end.

Proposition satisfy_lnot {Sigma: signature} {M: model Sigma} (s: valuation M) (phi: formula Sigma):
  satisfy s (lnot phi) <-> ~satisfy s phi.
split; intro; simpl; auto.
Qed.

Proposition satisfy_land {Sigma: signature} {M: model Sigma} (s: valuation M) (phi psi: formula Sigma):
  satisfy s (land phi psi) <-> satisfy s phi /\ satisfy s psi.
split; intro; simpl; auto.
Qed.

Proposition satisfy_lor {Sigma: signature} {M: model Sigma} (s: valuation M) (phi psi: formula Sigma):
  satisfy s (lor phi psi) <-> satisfy s phi \/ satisfy s psi.
split; intro; unfold lor in *.
- rewrite satisfy_lnot in H.
  rewrite satisfy_land in H.
  rewrite satisfy_lnot in H.
  rewrite satisfy_lnot in H.
  apply not_and_or in H.
  destruct H.
  left. apply NNPP; auto.
  right. apply NNPP; auto.
- rewrite satisfy_lnot.
  rewrite satisfy_land.
  rewrite satisfy_lnot.
  rewrite satisfy_lnot.
  apply or_not_and.
  destruct H.
  left; intro; auto.
  right; intro; auto.
Qed.

Proposition satisfy_limp {Sigma: signature} {M: model Sigma} (s: valuation M) (phi psi: formula Sigma):
  satisfy s (limp phi psi) <-> (satisfy s phi -> satisfy s psi).
split; intro; unfold limp in *.
- intro.
  rewrite satisfy_lor in H.
  rewrite satisfy_lnot in H.
  destruct H.
  exfalso; auto. assumption.
- rewrite satisfy_lor.
  rewrite satisfy_lnot.
  apply imply_to_or in H.
  assumption.
Qed.

Proposition satisfy_lbimp {Sigma: signature} {M: model Sigma} (s: valuation M) (phi psi: formula Sigma):
  satisfy s (lbimp phi psi) <-> (satisfy s phi <-> satisfy s psi).
split; intro; unfold lbimp in *.
- rewrite satisfy_land in H.
  rewrite satisfy_limp in H.
  rewrite satisfy_limp in H.
  destruct H.
  split; auto.
- rewrite satisfy_land.
  destruct H.
  split; rewrite satisfy_limp; auto.
Qed.

Proposition satisfy_lforall {Sigma: signature} {M: model Sigma} (s: valuation M) (x: V) (phi: formula Sigma):
  satisfy s (lforall x phi) <-> forall d, satisfy (update s x d) phi.
split; intro; simpl; auto.
Qed.

Proposition satisfy_lexists {Sigma: signature} {M: model Sigma} (s: valuation M) (x: V) (phi: formula Sigma):
  satisfy s (lexists x phi) <-> exists d, satisfy (update s x d) phi.
split; intro; unfold lexists in *.
- rewrite satisfy_lnot in H.
  rewrite satisfy_lforall in H.
  apply not_all_ex_not in H; destruct H.
  rewrite satisfy_lnot in H.
  apply NNPP in H.
  exists x0; auto.
- destruct H.
  rewrite satisfy_lnot.
  rewrite satisfy_lforall.
  apply ex_not_not_all.
  exists x0.
  rewrite satisfy_lnot.
  intro. apply H0; auto.
Qed.

Definition relation {Sigma: signature} (M: model Sigma) (phi: binformula Sigma): M -> M -> Prop :=
fun d d' => satisfy (update (update (nulval M) dummy1 d) dummy2 d') phi.

Definition Union {D: Type} (R1 R2: D -> D -> Prop): D -> D -> Prop :=
fun x y => R1 x y \/ R2 x y.

Proposition union_prop {Sigma: signature} (phi psi: binformula Sigma):
  forall x : V, freevarf (lor phi psi) x -> x = dummy1 \/ x = dummy2.
intros.
unfold freevarf in H.
simpl in H.
apply List.in_app_or in H.
destruct H; eapply binformula_prop; unfold freevarf; apply H.
Qed.

Definition union {Sigma: signature} (phi: binformula Sigma) (psi: binformula Sigma): binformula Sigma :=
mkbinformula _ (lor phi psi) (union_prop phi psi).

Proposition Union_union {Sigma: signature} (M: model Sigma) (phi: binformula Sigma) (psi: binformula Sigma):
  Union (relation M phi) (relation M psi) = relation M (union phi psi).
unfold Union.
apply functional_extensionality; intro x.
apply functional_extensionality; intro y.
unfold relation.
simpl.
apply propositional_extensionality; split; intro.
destruct H.
intro. destruct H0.
apply H0; auto.
intro. destruct H0.
apply H1; auto.
apply not_and_or in H.
destruct H; apply NNPP in H; auto.
Qed.

Definition Intersect {D: Type} (R1 R2: D -> D -> Prop): D -> D -> Prop :=
fun x y => R1 x y /\ R2 x y.

Definition Empty {D: Type}: D -> D -> Prop :=
fun x y => False.

Definition Disjoint {D: Type} (R1 R2: D -> D -> Prop): Prop :=
Intersect R1 R2 = Empty.

Definition DisjointUnion {D: Type} (R R1 R2: D -> D -> Prop): Prop :=
R = Union R1 R2 /\ Disjoint R1 R2.

Lemma DisjointUnion_spec {D: Type} (R R1 R2: D -> D -> Prop):
  DisjointUnion R R1 R2 <-> forall x y, (R x y <-> R1 x y \/ R2 x y) /\ ~(R1 x y /\ R2 x y).
split; intro.
- unfold DisjointUnion in H; destruct H.
  unfold Union in H.
  unfold Disjoint in H0.
  unfold Empty in H0.
  unfold Intersect in H0.
  intros. split.
  + rewrite H. apply iff_refl.
  + remember (fun x y : D => R1 x y /\ R2 x y) as f.
    remember (fun _ _ : D => False) as g.
    assert (f x y = g x y).
    rewrite H0; reflexivity.
    rewrite Heqf in H1.
    rewrite Heqg in H1.
    rewrite H1.
    intro; auto.
- unfold DisjointUnion. split.
  + unfold Union.
    apply functional_extensionality; intro x.
    apply functional_extensionality; intro y.
    specialize H with x y; destruct H.
    apply propositional_extensionality; split; intro.
    rewrite H in H1; auto.
    rewrite H; auto.
  + unfold Disjoint.
    unfold Intersect.
    unfold Empty.
    apply functional_extensionality; intro x.
    apply functional_extensionality; intro y.
    specialize H with x y; destruct H.
    apply propositional_extensionality; split; intro.
    auto. exfalso; auto.
Qed.







