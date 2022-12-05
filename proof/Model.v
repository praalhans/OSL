Require Export FunctionalExtensionality.
Require Export PropExtensionality.
Require Export Classical.
Require Export PeanoNat.

Require Coq.Lists.List.
Require Coq.Vectors.Vector.

Record finite (T: Set) := mkfinite
{ listing: list T
; listing_full: forall (t: T), List.In t listing }.

Record denumerable (T: Set) := mkdenumerable
{ enumerate: nat -> T
; enumerate_inject: forall (n m: nat), enumerate n = enumerate m -> n = m
; enumerate_surject: forall (t: T), exists (n: nat), enumerate n = t }.

Inductive countable (T: Set) :=
| is_finite: finite T -> countable T
| is_infinite: denumerable T -> countable T.

Record signature: Type := mksignature
{ Func: Set
; Fcountable: countable Func
; arity: Func -> nat
; Pred: Set
; Pcountable: countable Pred
; adic: Pred -> nat
; Bin: Set
; Benumerable: denumerable Bin }.
Arguments arity {_} _.
Arguments adic {_} _.

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
| bot: formula Sigma
| eq: term Sigma -> term Sigma -> formula Sigma
| prim2 (r: Bin Sigma): term Sigma -> term Sigma -> formula Sigma
| primn (p: Pred Sigma): Vector.t (term Sigma) (adic p) -> formula Sigma
| limp: formula Sigma -> formula Sigma -> formula Sigma
| lforall: V -> formula Sigma -> formula Sigma.
Arguments eq {_} _ _.
Arguments prim2 {_} _ _.
Arguments primn {_} _ _.
Arguments limp {_} _ _.
Arguments lforall {_} _ _.

Definition lnot {Sigma: signature} (phi: formula Sigma): formula Sigma :=
limp phi (bot Sigma).

Fixpoint freevarfl {Sigma: signature} (phi: formula Sigma): list V :=
match phi with
| bot _ => nil
| eq t1 t2 => List.app (freevartl t1) (freevartl t2)
| prim2 _ t1 t2 => List.app (freevartl t1) (freevartl t2)
| primn _ arg => Vector.fold_right (@List.app V)
    (Vector.map (@freevartl Sigma) arg) List.nil
| limp phi psi => List.app (freevarfl phi) (freevarfl psi)
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
; func (f: Func Sigma): Vector.t domain (arity f) -> domain
; bin (r: Bin Sigma): domain -> domain -> Prop
; pred (p: Pred Sigma): Vector.t domain (adic p) -> Prop
}.
Coercion domain: model >-> Sortclass.
Arguments domain {_} _.
Arguments element {_} _.
Arguments func {_} {_} _ _.
Arguments bin {_} {_} _ _.
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
| bot _ => False
| eq t1 t2 => interp s t1 = interp s t2
| prim2 r t1 t2 => bin r (interp s t1) (interp s t2)
| primn p arg => pred p (Vector.map (interp s) arg)
| limp phi psi => satisfy s phi -> satisfy s psi
| lforall x phi => forall (d: domain M), satisfy (update s x d) phi
end.

Record defrel {Sigma: signature} (M: model Sigma) (phi: binformula Sigma) :=
{ defrel_rel: M -> M -> Prop
; defrel_prop: forall d d', defrel_rel d d' <->
    satisfy (update (update (defval M) dummy1 d) dummy2 d') phi
}.
