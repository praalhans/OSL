Require Export FunctionalExtensionality.
Require Export PropExtensionality.
Require Export PeanoNat.

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

Record binformula (Sigma: signature) :=
{ binformula_form: formula Sigma
; binformula_prop: forall x, freevarf binformula_form x ->
    x = dummy1 \/ x = dummy2
}.
Coercion binformula_form: binformula >-> formula.

Record model (Sigma: signature): Type := mkstructure
{ domain: Set
; element: domain
; domain_eq_dec: forall (x y: domain), x = y \/ x <> y
; func (f: Func Sigma): Vector.t domain (arity f) -> domain
; pred (P: Pred Sigma): Vector.t domain (adic P) -> Prop
; pred_stable (P: Pred Sigma) (xs: Vector.t domain (adic P)): pred P xs <-> ~~pred P xs
}.
Coercion domain: model >-> Sortclass.
Arguments domain {_} _.
Arguments element {_} _.
Arguments func {_} {_} _ _.
Arguments pred {_} {_} _ _.

Definition valuation {Sigma: signature} (M: model Sigma) := V -> M.

Definition defval {Sigma: signature} (M: model Sigma): valuation M :=
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

Proposition satisfy_lforall {Sigma: signature} {M: model Sigma} (s: valuation M) (x: V) (phi: formula Sigma):
  satisfy s (lforall x phi) <-> forall d, satisfy (update s x d) phi.
split; intro; simpl; auto.
Qed.

Lemma satisfy_stability {Sigma: signature} {M: model Sigma} (s: valuation M) (phi: formula Sigma):
  satisfy s phi <-> satisfy s (lnot (lnot phi)).
split; intro.
- induction phi; rewrite satisfy_lnot; rewrite satisfy_lnot.
  all: intro. all: apply H0. all: assumption.
- rewrite satisfy_lnot in H; rewrite satisfy_lnot in H.
  generalize dependent s. induction phi; intros.
  + simpl in *.
    pose proof (domain_eq_dec _ _ (interp s t) (interp s t0)).
    destruct H0.
    assumption. exfalso; apply H; assumption.
  + simpl in *.
    rewrite <- pred_stable in H. assumption.
  + rewrite satisfy_lnot.
    intro. apply H. rewrite satisfy_lnot.
    intro. apply H1. assumption.
  + simpl. split.
    apply IHphi1. intro. apply H. intro.
    simpl in H1. destruct H1. apply H0. assumption.
    apply IHphi2. intro. apply H. intro.
    simpl in H1. destruct H1. apply H0. assumption.
  + simpl. intro.
    apply IHphi. intro. apply H. intro.
    simpl in H1. apply H0. apply H1.
Qed.

Corollary satisfy_lem {Sigma: signature} {M: model Sigma} (s: valuation M) (phi: formula Sigma):
  satisfy s (lor phi (lnot phi)).
unfold lor.
rewrite satisfy_lnot; intro.
rewrite satisfy_land in H; destruct H.
rewrite satisfy_lnot in H, H0.
rewrite satisfy_lnot in H0.
apply H0; assumption.
Qed.

Definition relation {Sigma: signature} (M: model Sigma) (phi: binformula Sigma): M -> M -> Prop :=
fun d d' => satisfy (update (update (defval M) dummy1 d) dummy2 d') phi.

Proposition relation_stable {Sigma: signature} (phi: binformula Sigma):
  forall M x y, relation M phi x y <-> ~~relation M phi x y.
intros. unfold relation.
rewrite satisfy_stability at 1.
rewrite satisfy_lnot.
rewrite satisfy_lnot.
apply iff_refl.
Qed.
