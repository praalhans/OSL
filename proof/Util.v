Require Export FunctionalExtensionality.
Require Export PropExtensionality.
Require Export PeanoNat.
Require Export Classical.

Require Coq.Lists.List.
Require Coq.Vectors.Vector.

(* Type classifiers *)

Class finite (T: Type) := mkfinite
{ listing: list T
; listing_full: forall (t: T), List.In t listing }.

Class denumerable (T: Type) := mkdenumerable
{ enumerate: nat -> T
; enumerate_inject: forall (n m: nat), enumerate n = enumerate m -> n = m
; enumerate_surject: forall (t: T), exists (n: nat), enumerate n = t }.

Inductive countable (T: Type) :=
| is_finite: finite T -> countable T
| is_infinite: denumerable T -> countable T.

Class discrete (T: Type) := mkdiscrete
{ eq_dec (x y: T): {x = y} + {x <> y} }.

Instance nat_discrete: discrete nat := {| eq_dec := Nat.eq_dec |}.

(* Sets and relations *)

Definition Union {D: Type} (R1 R2: D -> Prop): D -> Prop :=
fun x => R1 x \/ R2 x.

Definition Intersect {D: Type} (R1 R2: D -> Prop): D -> Prop :=
fun x => R1 x /\ R2 x.

Definition Empty (D: Type): D -> Prop :=
fun x => False.

Definition Full (D: Type): D -> Prop :=
fun x => True.

Definition Subtract {D: Type} `{discrete D} (R: D -> Prop) (y: D): D -> Prop :=
fun x => if eq_dec x y then False else R x.

Definition Disjoint {D: Type} (R1 R2: D -> Prop): Prop :=
Intersect R1 R2 = Empty D.

Definition DisjointUnion {D: Type} (R R1 R2: D -> Prop): Prop :=
R = Union R1 R2 /\ Disjoint R1 R2.

Lemma DisjointUnion_spec {D: Type} (R R1 R2: D -> Prop):
  DisjointUnion R R1 R2 <-> forall x, (R x <-> R1 x \/ R2 x) /\ ~(R1 x /\ R2 x).
split; intro.
- unfold DisjointUnion in H; destruct H.
  unfold Union in H.
  unfold Disjoint in H0.
  unfold Empty in H0.
  unfold Intersect in H0.
  intros. split.
  + rewrite H. apply iff_refl.
  + remember (fun x : D => R1 x /\ R2 x) as f.
    remember (fun _ : D => False) as g.
    assert (f x = g x).
    rewrite H0; reflexivity.
    rewrite Heqf in H1.
    rewrite Heqg in H1.
    rewrite H1.
    intro; auto.
- unfold DisjointUnion. split.
  + unfold Union.
    apply functional_extensionality; intro x.
    specialize H with x; destruct H.
    apply propositional_extensionality; split; intro.
    rewrite H in H1; auto.
    rewrite H; auto.
  + unfold Disjoint.
    unfold Intersect.
    unfold Empty.
    apply functional_extensionality; intro x.
    specialize H with x; destruct H.
    apply propositional_extensionality; split; intro.
    auto. exfalso; auto.
Qed.
