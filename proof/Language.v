Require Import Classical.

(* We have the following objects:
   - the domain D,
   - the points to predicate on D in Prop,
   - the separating connectives in Prop,
   - the rooted assertion in Prop,
   - the proof rules for reasoning about rooted assertions. *)

Axiom D: Type.
Axiom hasval: D -> D -> Prop.
Definition pointsTo (x y: D) := hasval x y /\ forall z w, hasval z w -> z = x.
Definition emp := forall x y, ~hasval x y.

Axiom sep: Prop -> Prop -> Prop.
Axiom sepimp: Prop -> Prop -> Prop.
Notation "A ** B" := (sep A B) (at level 79, right associativity) : type_scope.
Notation "A -** B" := (sepimp A B) (at level 99, right associativity) : type_scope.

Axiom rooted: Prop -> (D -> D -> Prop) -> Prop.
Notation "A @ h" := (rooted A h) (at level 110) : type_scope.
Axiom root_equiv: forall (A: Prop), A <-> rooted A hasval.
Lemma rooted_intro: forall (A: Prop), (forall h, rooted A h) -> A.
intros.
rewrite root_equiv.
apply H.
Qed.
Ltac root := apply rooted_intro; intro.
Axiom root_above: forall (A: Prop), forall h h', (forall x y, h x y <-> h' x y) -> rooted A h -> rooted A h'.
Axiom root_assoc: forall (A: Prop) h h', rooted (rooted A h) h' <-> rooted A (fun x y => rooted (h x y) h').

Axiom root_True: forall (h: D -> D -> Prop), rooted True h.
Axiom root_False: forall (h: D -> D -> Prop), rooted False h -> False.
Ltac root_exfalso h := apply root_False with (h := h).
Axiom root_hasval: forall (h: D -> D -> Prop) x y, rooted (hasval x y) h <-> h x y.
Axiom root_eq: forall (h: D -> D -> Prop) (T: Type) (x y: T), rooted (x = y) h <-> x = y.

Axiom root_split': forall (A B: Prop), forall h, (rooted A h /\ rooted B h) -> rooted (A /\ B) h.
Ltac root_split := apply root_split'; split.
Axiom root_join': forall (A B: Prop), forall h, (rooted A h \/ rooted B h) -> rooted (A \/ B) h.
Ltac root_join := apply root_join'.
Axiom root_and_elim: forall (A B: Prop), forall h, rooted (A /\ B) h -> rooted A h /\ rooted B h.
Axiom root_or_elim: forall (A B: Prop), forall h, rooted (A \/ B) h -> rooted A h \/ rooted B h.

Axiom root_imp': forall (A B: Prop), forall h, (rooted A h -> rooted B h) -> rooted (A -> B) h.
Ltac root_imp H := apply root_imp'; intro H.
Axiom root_imp_elim': forall (A B: Prop), forall h, rooted (A -> B) h -> rooted A h -> rooted B h.
Ltac root_imp_elim H := apply (root_imp_elim' _ _ _ H).

Axiom root_forall': forall (T: Type), forall (A: T -> Prop),
  forall h, (forall (x: T), rooted (A x) h) -> rooted (forall (x: T), A x) h.
Ltac root_forall H := apply root_forall'; intro H.
Axiom root_forall_elim': forall (T: Type), forall (A: T -> Prop),
  forall h, rooted (forall (x: T), A x) h -> forall (x: T), rooted (A x) h.
Ltac root_forall_elim H R := apply root_forall_elim' with (x := R) in H.

Axiom root_exists': forall (T: Type), forall (A: T -> Prop),
  forall h, (exists (x: T), rooted (A x) h) -> rooted (exists (x: T), A x) h.
Ltac root_exists x := apply root_exists'; exists x.
Axiom root_exists_elim': forall (T: Type), forall (A: T -> Prop),
  forall h, rooted (exists (x: T), A x) h -> exists (x: T), rooted (A x) h.
Ltac root_exists_elim H := apply root_exists_elim' in H; destruct H.

Definition Par (h1 h2: D -> D -> Prop) :=
  (forall x y, h1 x y -> forall z, ~h2 x z) /\ (forall x y, h2 x y -> forall z, ~h1 x z).
Definition Split (h h1 h2: D -> D -> Prop) :=
  (forall x y, h x y <-> h1 x y \/ h2 x y) /\ Par h1 h2.

Lemma Split_comm (h h1 h2: D -> D -> Prop):
  Split h h1 h2 -> Split h h2 h1.
unfold Split; intro.
destruct H; split.
- intros; specialize H with x y; tauto.
- unfold Par in *; tauto.
Qed.

Lemma Par_comm (h1 h2: D -> D -> Prop):
  Par h1 h2 -> Par h2 h1.
unfold Par; intro.
destruct H; split; intros.
specialize H0 with x y z. tauto.
specialize H with x y z. tauto.
Qed.

Axiom sep_elim': forall (A B C: Prop) (h: D -> D -> Prop),
  rooted (A ** B) h -> (forall h1 h2, Split h h1 h2 -> rooted A h1 -> rooted B h2 -> C) -> C.
Ltac sep_elim H := match goal with
|- ?G => apply sep_elim' with (C := G) in H; [apply H | clear H; intros]
end.
Axiom sep_intro': forall (A B: Prop) (h: D -> D -> Prop),
  (exists h1 h2, Split h h1 h2 /\ rooted A h1 /\ rooted B h2) -> rooted (A ** B) h.
Ltac sep_intro h1 h2 := apply sep_intro'; exists h1; exists h2; split; [|split].

Axiom sepimp_elim': forall (A B C: Prop) (h h': D -> D -> Prop),
  rooted (A -** B) h -> Par h h' /\ rooted A h' /\ (rooted B (fun x y => h x y \/ h' x y) -> C) -> C.
Ltac sepimp_elim H h := match goal with
|- ?G => apply sepimp_elim' with (C := G) (h' := h) in H; [apply H|split;[|split;[|intro]]]
end.
Lemma sepimp_elim_in': forall (A B: Prop) (h h': D -> D -> Prop),
  rooted (A -** B) h -> rooted A h' -> Par h h' -> rooted B (fun x y => h x y \/ h' x y).
intros. sepimp_elim H h'; auto.
Qed.
Ltac sepimp_elim_in H G := apply (sepimp_elim_in' _ _ _ _ H) in G.
Axiom sepimp_intro': forall (A B: Prop) (h: D -> D -> Prop),
  (forall h', Par h h' -> rooted A h' -> rooted B (fun x y => h x y \/ h' x y)) -> rooted (A -** B) h.
Ltac sepimp_intro H := apply sepimp_intro'; let h := fresh "h" in intro h; let G := fresh in intro G; intro H.

Ltac root_destruct H := ((apply root_and_elim in H + apply root_or_elim in H + apply root_exists_elim' in H); destruct H) + sep_elim H.

Tactic Notation "root_intro" := let H := fresh in (root_imp H + root_forall H + sepimp_intro H).
Tactic Notation "root_intro" ident(H) := (root_imp H + root_forall H + sepimp_intro H).
Tactic Notation "root_apply" ident(H) := root_imp_elim H.
Tactic Notation "root_apply" ident(H) "in" ident(G) := (apply (root_imp_elim' _ _ _ H) in G + sepimp_elim_in H G).
Tactic Notation "root_specialize" ident(H) "with" uconstr(R) := root_forall_elim H R.

(* ============== *)
(* Example proofs *)
(* ============== *)

Definition Empty (h: D -> D -> Prop) := forall x y : D, ~ h x y.
Definition epsilon: D -> D -> Prop := fun x y => False.

Proposition Empty_epsilon: Empty epsilon.
unfold Empty; unfold epsilon; tauto.
Qed.

Lemma Split_Empty (h h1 h2: D -> D -> Prop):
  Split h h1 h2 /\ Empty h2 -> forall x y, h x y <-> h1 x y.
unfold Split; unfold Empty; intros;
destruct H; destruct H.
rewrite H.
split; intro. destruct H2; auto. apply H0 in H2; tauto. tauto.
Qed.

Lemma Split_epsilon (h: D -> D -> Prop):
  Split h h epsilon.
unfold Split; unfold epsilon.
split; [tauto|].
unfold Par; split; intros; tauto.
Qed.

Lemma root_emp (h: D -> D -> Prop): rooted emp h <-> Empty h.
unfold Empty; unfold emp; split; intro.
- intros.
  intro.
  root_specialize H with x.
  root_specialize H with y.
  root_exfalso h.
  root_apply H.
  apply root_hasval.
  auto.
- root_intro x.
  root_intro y.
  root_intro.
  exfalso.
  apply root_hasval in H0.
  apply H in H0. assumption.
Qed.

Lemma emp_epsilon: rooted emp epsilon.
unfold emp.
root_intro x.
root_intro y.
root_intro.
apply root_hasval in H.
unfold epsilon in H. inversion H.
Qed.

Lemma sep_comm (A B: Prop): A ** B -> B ** A.
root.
root_intro.
root_destruct H.
sep_intro h2 h1; auto.
apply Split_comm; auto.
Qed.

Lemma Split_assoc {h1 h2 h3 h4 h5: D -> D -> Prop}:
  Split h1 h2 h3 -> Split h2 h4 h5 -> exists h6, Split h6 h5 h3 /\ Split h1 h4 h6.
intros.
exists (fun x y => h5 x y \/ h3 x y).
unfold Split; split.
- split; try tauto.
  unfold Split in H; destruct H.
  unfold Split in H0; destruct H0.
  unfold Par; split; intros.
  unfold Par in H1; destruct H1.
  apply H1 with (y := y).
  apply <- H0; tauto.
  unfold Par in H1; destruct H1.
  apply H4 with (z := z) in H3.
  intro.
  apply or_intror with (A := h4 x z) in H5.
  apply <- H0 in H5.
  tauto.
- split.
  intros.
  unfold Split in H; destruct H.
  specialize H with x y.
  rewrite H.
  unfold Split in H0; destruct H0.
  specialize H0 with x y.
  rewrite H0.
  apply or_assoc.
  unfold Par; split; intros.
  + unfold Split in H0; destruct H0.
    intro.
    destruct H3.
    unfold Par in H2; destruct H2.
    apply H2 with (z := z) in H1. tauto.
    apply or_introl with (B := h5 x y) in H1.
    apply <- H0 in H1.
    unfold Split in H; destruct H.
    unfold Par in H4; destruct H4.
    apply H4 with (z := z) in H1. tauto.
  + destruct H1.
    unfold Split in H0; destruct H0.
    unfold Par in H2; destruct H2.
    apply H3 with (y := y). auto.
    unfold Split in H; destruct H.
    unfold Par in H2; destruct H2.
    apply H3 with (z := z) in H1.
    unfold Split in H0; destruct H0.
    rewrite H0 in H1. tauto.
Qed.

Lemma sep_assoc (A B C: Prop): (A ** B) ** C <-> A ** B ** C.
root.
root_split; root_intro.
- root_destruct H.
  root_destruct H0.
  pose proof (Split_assoc H H0); destruct H4; destruct H4.
  sep_intro h0 x; auto.
  sep_intro h3 h2; auto.
- root_destruct H.
  root_destruct H1.
  apply Split_comm in H.
  apply Split_comm in H1.
  pose proof (Split_assoc H H1); destruct H4; destruct H4.
  apply Split_comm in H4.
  apply Split_comm in H5.
  sep_intro x h3; auto.
  sep_intro h1 h0; auto.
Qed.

Lemma sep_Empty (A: Prop): A ** emp <-> A.
root.
root_split; root_intro.
- root_destruct H.
  rewrite root_emp in H1.
  apply root_above with (h := h1); auto.
  intros; apply iff_sym.
  eapply Split_Empty. split.
  apply H. apply H1.
- sep_intro h epsilon.
  apply Split_epsilon.
  auto.
  rewrite root_emp.
  apply Empty_epsilon.
Qed.

Lemma sep_or (A B C: Prop): (A \/ B) ** C <-> A ** C \/ B ** C.
root. root_split; root_intro.
- root_destruct H.
  root_join.
  root_destruct H0.
  left. sep_intro h1 h2; auto.
  right. sep_intro h1 h2; auto.
- root_destruct H; sep_elim H.
  sep_intro h1 h2; auto.
  root_join; tauto.
  sep_intro h1 h2; auto.
  root_join; auto.
Qed.

Lemma sep_and (A B C: Prop): (A /\ B) ** C -> A ** C /\ B ** C.
root. root_intro.
root_destruct H.
root_destruct H0.
root_split.
sep_intro h1 h2; auto.
sep_intro h1 h2; auto.
Qed.

Lemma sep_exists (T: Type) (A: T -> Prop) (B: Prop): (exists x, A x) ** B <-> exists x, A x ** B.
root. root_split; root_intro.
- root_destruct H.
  root_destruct H0.
  root_exists x.
  sep_intro h1 h2; auto.
- root_destruct H.
  root_destruct H.
  sep_intro h1 h2; auto.
  root_exists x; auto.
Qed.

Lemma sep_forall (T: Type) (A: T -> Prop) (B: Prop): (forall x, A x) ** B -> forall x, A x ** B.
root. root_intro.
root_intro x.
root_destruct H.
root_specialize H0 with x.
sep_intro h1 h2; auto.
Qed.

Lemma adjoint (A B: Prop): A ** (A -** B) -> B.
root.
root_intro.
root_destruct H.
sepimp_elim H1 h1.
apply Split_comm in H; unfold Split in H; tauto.
auto.
unfold Split in H; destruct H.
eapply root_above; [|apply H2]; intros; simpl.
rewrite H. tauto.
Qed.

Definition box (A: Prop) := True ** (emp /\ (True -** A)).

Lemma box_elim (A: Prop): box A -> A.
root.
root_intro.
unfold box in H.
root_destruct H.
root_destruct H1.
unfold Split in H; destruct H.
(* h2 = empty, so h = h1 *)
apply root_emp in H1; unfold Empty in H1.
root_apply H2 in H0.
apply root_above with (h := fun x y : D => h2 x y \/ h1 x y).
intros. apply iff_sym. rewrite or_comm. apply H.
apply H0.
apply Par_comm. auto.
Qed.

Lemma box_indep (A: Prop): box A -> forall h, rooted (box A) h.
intros.
unfold box in *.
apply root_equiv in H.
root_destruct H.
root_destruct H1.
sep_intro h epsilon.
apply Split_epsilon.
apply root_True.
root_split.
apply emp_epsilon.
apply root_emp in H1.
root_intro.
root_apply H2 in H3.
eapply root_above; [|apply H3].
intros; simpl.
unfold Empty in H1.
split; intro; destruct H5; auto.
exfalso. eapply H1. apply H5.
exfalso. apply H5.
unfold Par; split; intros.
unfold Empty in H1.
exfalso. eapply H1. apply H5.
apply H1.
Qed.

Lemma root_under: forall (A B: Prop), box (A -> B) -> forall h, rooted A h -> rooted B h.
intros A B.
intro.
intro.
pose proof (box_indep _ H h).
intro.
unfold box in H0.
root_destruct H0.
root_destruct H3.
unfold Split in H0; destruct H0.
root_apply H4 in H2.
apply root_above with (h' := h) in H2.
root_apply H2 in H1. auto.
intros. rewrite H0. tauto.
apply Par_comm. auto.
Qed.

Lemma box_rooted (A: Prop): (forall h, rooted A h) -> box A.
intro.
unfold box.
root.
sep_intro h epsilon.
apply Split_epsilon.
apply root_True.
root_split.
apply emp_epsilon.
root_intro.
apply root_above with (h := h0).
intros. unfold epsilon. tauto.
apply H.
Qed.

Lemma sep_mono (A A' B B': Prop): box (A -> A') -> box (B -> B') -> A ** B -> A' ** B'.
intro. intro.
root.
root_intro.
root_destruct H1.
sep_intro h1 h2; auto.
eapply root_under. apply H. auto.
eapply root_under. apply H0. auto.
Qed.

Definition Functional (h: D -> D -> Prop) := forall x y, h x y -> forall z, h x z -> y = z.
Definition Fun := forall x y, hasval x y -> forall z, hasval x z -> y = z.

Lemma root_Fun (h: D -> D -> Prop): rooted Fun h <-> Functional h.
unfold Functional. unfold Fun. split; intro.
- intros.
  root_specialize H with x.
  root_specialize H with y.
  rewrite <- root_hasval in H0.
  root_apply H in H0.
  root_specialize H0 with z.
  rewrite <- root_hasval in H1.
  root_apply H0 in H1.
  apply root_eq in H1. auto.
- root_intro x.
  root_intro y.
  root_intro.
  root_intro z.
  root_intro.
  apply root_eq.
  rewrite root_hasval in H0.
  rewrite root_hasval in H1.
  eapply H.
  apply H0. apply H1.
Qed.

Lemma hasval_pointsTo (x y: D):
  hasval x y <-> pointsTo x y ** True.
root.
root_split; root_intro.
- unfold pointsTo.
  rewrite root_hasval in H.
  sep_intro (fun z w => z = x /\ h z w) (fun z w => z <> x /\ h z w).
  + unfold Split; split; intros.
    split; intro.
    tauto.
    pose proof (classic (x0 = x)); destruct H1; tauto.
    unfold Par; split; intros; destruct H0; tauto.
  + root_split.
    apply root_hasval; tauto.
    root_intro z.
    root_intro w.
    root_intro.
    rewrite root_hasval in H0; destruct H0.
    apply root_eq. auto.
  + apply root_True.
- root_destruct H.
  unfold pointsTo in H0.
  root_destruct H0.
  rewrite root_hasval in H0.
  rewrite root_hasval.
  unfold Split in H; destruct H.
  apply or_introl with (B := h2 x y) in H0.
  apply <- H in H0. auto.
Qed.

Definition alloc (x: D) := exists y, hasval x y.
Definition free (x: D) := ~(alloc x).
Definition pointsToDash (x: D) := exists y, pointsTo x y.

Lemma root_free (h: D -> D -> Prop) (x: D): rooted (free x) h <-> forall y, ~h x y.
unfold free; unfold alloc. split; intro.
- intros. intro.
  apply root_False with (h := h).
  root_apply H.
  root_exists y.
  apply root_hasval. auto.
- root_intro.
  root_destruct H0.
  exfalso.
  apply H with (y := x0).
  rewrite root_hasval in H0. auto.
Qed.

Lemma pointsTo_singleton (x y: D): rooted (pointsTo x y) (fun z w => z = x /\ w = y).
unfold pointsTo.
root_split.
rewrite root_hasval. tauto.
root_intro z.
root_intro w.
root_intro.
rewrite root_hasval in H.
apply root_eq; tauto.
Qed.

Lemma sepimp_sep (x y: D) (A: Prop):
  free x -> (pointsTo x y -** pointsTo x y ** A) <-> A.
root.
root_intro.
rewrite root_free in H.
root_split; root_intro.
- pose proof (pointsTo_singleton x y).
  root_apply H0 in H1.
  root_destruct H1.
  unfold Split in H1; destruct H1.
  eapply root_above; [|apply H3].
  intros.
  split; intro.
  + pose proof (@or_intror (h1 x0 y0) _ H5).
    apply <- H1 in H6. destruct H6; auto. destruct H6.
    unfold Par in H4. destruct H4.
    exfalso.
    apply H8 with (z := y0) in H5; apply H5.
    unfold pointsTo in H2.
    root_destruct H2.
    rewrite root_hasval in H2.
    rewrite H6. rewrite H7. auto.
  + pose proof (classic (x = x0)). destruct H6.
    exfalso. rewrite <- H6 in H5. apply H in H5; auto.
    specialize H1 with x0 y0.
    eapply or_introl in H5. rewrite H1 in H5.
    destruct H5; auto. exfalso.
    unfold pointsTo in H2.
    root_destruct H2.
    root_specialize H7 with x0.
    root_specialize H7 with y0.
    rewrite <- root_hasval in H5.
    root_apply H7 in H5.
    apply root_eq in H5.
    apply H6. rewrite H5. auto.
  + unfold Par; split; intros.
    intro. destruct H3.
    rewrite H3 in H2. apply H in H2. auto.
    destruct H2. rewrite H2. apply H.
- root_intro.
  sep_intro h0 h.
  unfold Split; split; intros. tauto.
  unfold Par in *; tauto. tauto. tauto.
Qed.

(* Application *)
Section Application.

Variable x: D.
Variable y: D.
Variable z: D.
Variable w: D.

Definition F1: Prop := alloc x /\ ((x = y /\ z = w) \/ (x <> y /\ hasval y z)).
Definition F2: Prop := pointsToDash x ** (pointsTo x w -** hasval y z).

Proposition F12: Fun -> F1 -> F2.
unfold F1; unfold F2.
root.
root_intro.
apply root_Fun in H.
root_intro.
root_destruct H0.
root_destruct H1.
- root_destruct H1.
  apply root_eq in H1, H2.
  root_destruct H0.
  apply root_hasval in H0.
  (* Split h: remove x from domain. *)
  sep_intro (fun z z0 => z = x /\ z0 = x0) (fun z z0 => z <> x /\ h z z0).
  + unfold Split; split.
    intros. split; intro.
    pose proof (classic (x1 = x)); destruct H4.
    left. split; auto. eapply H. apply H3. rewrite H4. apply H0.
    right. split; auto.
    destruct H3.
    destruct H3. rewrite H3. rewrite H4. auto.
    destruct H3. auto.
    unfold Par; split; intros; intro.
    destruct H3. destruct H4. apply H4; auto.
    destruct H3. destruct H4. apply H3; auto.
  + unfold pointsToDash.
    root_exists x0.
    apply pointsTo_singleton.
  + root_intro.
    apply root_hasval.
    unfold pointsTo in H3.
    root_destruct H3.
    apply root_hasval in H3.
    right. rewrite <- H1. rewrite H2. auto.
- root_destruct H1.
  apply root_hasval in H2.
  unfold alloc in H0.
  root_destruct H0.
  apply root_hasval in H0.
  (* Split h: remove x from domain. *)
  sep_intro (fun z z0 => z = x /\ z0 = x0) (fun z z0 => z <> x /\ h z z0).
  + unfold Split; split.
    intros. split; intro.
    pose proof (classic (x1 = x)); destruct H4.
    left. split; auto. eapply H. apply H3. rewrite H4. apply H0.
    right. split; auto.
    destruct H3.
    destruct H3. rewrite H3. rewrite H4. auto.
    destruct H3. auto.
    unfold Par; split; intros; intro.
    destruct H3. destruct H4. apply H4; auto.
    destruct H3. destruct H4. apply H3; auto.
  + unfold pointsToDash.
    root_exists x0.
    apply pointsTo_singleton.
  + root_intro.
    apply root_hasval.
    unfold pointsTo in H3.
    root_destruct H3.
    apply root_hasval in H3.
    left. split.
    intro.
    eapply root_False.
    root_apply H1.
    apply root_eq. auto. auto.
Qed.

Proposition F12': F1 -> F2.
unfold F1; unfold F2.
root.
pose True as H.
root_intro.
root_destruct H0.
root_destruct H1.
- root_destruct H1.
  apply root_eq in H1, H2.
  root_destruct H0.
  apply root_hasval in H0.
  (* Split h: remove x from domain. *)
  sep_intro (fun z z0 => z = x /\ h z z0) (fun z z0 => z <> x /\ h z z0).
  + unfold Split; split.
    intros. split; intros.
    pose proof (classic (x1 = x)); destruct H4.
    left. auto.
    right. auto.
    destruct H3. destruct H3. auto.
    destruct H3. auto.
    unfold Par; split; intros; intro.
    destruct H3. destruct H4. apply H4; auto.
    destruct H3. destruct H4. apply H3; auto.
  + unfold pointsToDash.
    root_exists x0.
    unfold pointsTo.
    root_split.
    apply root_hasval. auto.
    root_intro z0.
    root_intro w0.
    root_intro.
    apply root_hasval in H3; destruct H3.
    apply root_eq. auto.
  + root_intro.
    apply root_hasval.
    unfold pointsTo in H3.
    root_destruct H3.
    apply root_hasval in H3.
    right. rewrite <- H1. rewrite H2. auto.
- root_destruct H1.
  apply root_hasval in H2.
  unfold alloc in H0.
  root_destruct H0.
  apply root_hasval in H0.
  (* Split h: remove x from domain. *)
  sep_intro (fun z z0 => z = x /\ h z z0) (fun z z0 => z <> x /\ h z z0).
  + unfold Split; split.
    intros. split; intro.
    pose proof (classic (x1 = x)); destruct H4.
    left. split; auto.
    right. split; auto.
    destruct H3. destruct H3. auto.
    destruct H3. auto.
    unfold Par; split; intros; intro.
    destruct H3. destruct H4. apply H4; auto.
    destruct H3. destruct H4. apply H3; auto.
  + unfold pointsToDash.
    root_exists x0.
    unfold pointsTo.
    root_split.
    apply root_hasval. auto.
    root_intro z0.
    root_intro w0.
    root_intro.
    apply root_hasval in H3; destruct H3.
    apply root_eq. auto.
  + root_intro.
    apply root_hasval.
    unfold pointsTo in H3.
    root_destruct H3.
    apply root_hasval in H3.
    left. split.
    intro.
    eapply root_False.
    root_apply H1.
    apply root_eq. auto. auto.
Qed.

Proposition F21: F2 -> F1.
unfold F1; unfold F2.
root.
pose True as H. (* Dummy *)
root_intro.
root_destruct H0.
unfold pointsToDash in H1.
root_destruct H1.
sepimp_elim H2 (fun z z0 => z = x /\ z0 = w \/ z <> x /\ h1 z z0).
- unfold Split in H0. destruct H0.
  unfold Par in *. destruct H3.
  split; intros; intro.
  + destruct H6; destruct H6.
    rewrite H6 in H5.
    apply H4 with (z := x0) in H5.
    unfold pointsTo in H1.
    root_destruct H1.
    apply root_hasval in H1. apply H5; auto.
    unfold pointsTo in H1.
    root_destruct H1.
    root_specialize H8 with x1.
    root_specialize H8 with z0.
    rewrite <- root_hasval in H7.
    root_apply H8 in H7.
    apply root_eq in H7.
    apply H6. apply H7.
  + destruct H5; destruct H5.
    rewrite H5 in H6.
    apply H4 with (z := x0) in H6.
    unfold pointsTo in H1.
    root_destruct H1.
    apply root_hasval in H1. auto.
    eapply H3 in H7. apply H7. apply H6.
- unfold pointsTo.
  root_split.
  apply root_hasval. left. auto.
  root_intro z0.
  root_intro w0.
  root_intro.
  apply root_hasval in H3.
  apply root_eq.
  destruct H3; destruct H3.
  auto.
  unfold pointsTo in H1.
  root_destruct H1.
  root_specialize H5 with z0.
  root_specialize H5 with w0.
  rewrite <- root_hasval in H4.
  root_apply H5 in H4.
  apply root_eq in H4. auto.
- (* We don't need H1 and H2 anymore. *)
  apply root_hasval in H3.
  root_split.
  + unfold pointsTo in H1.
    root_destruct H1.
    unfold alloc.
    root_exists x0.
    apply root_hasval.
    apply root_hasval in H1.
    unfold Split in H0. destruct H0.
    apply H0. left; auto.
  + destruct H3.
    root_join. right.
    root_split.
    * root_intro.
      apply root_eq in H4.
      rewrite <- H4 in H3.
      unfold pointsTo in H1.
      root_destruct H1.
      apply root_hasval in H1.
      exfalso. unfold Split in H0. destruct H0.
      unfold Par in H6. destruct H6.
      eapply H6 in H1.
      apply H1. apply H3.
    * apply root_hasval.
      unfold Split; destruct H0. apply H0. right; auto.
    * destruct H3.
      root_join. left. root_split; apply root_eq.
      destruct H3. auto. destruct H3. auto.
      root_join. right. root_split.
      root_intro. apply root_eq in H4.
      destruct H3. exfalso. apply H3; auto.
      destruct H3. apply root_hasval.
      unfold Split; destruct H0. apply H0. auto.
Qed.

End Application.

Section Elimination.

Lemma sep_after_root (A: Prop) (B C R: D -> D -> Prop):
  rooted A (fun x y => B x y ** C x y) ->
  (forall x y, R x y <-> B x y ** C x y) ->
  rooted A R.
intros.
eapply root_above; [| apply H].
simpl. intros. specialize H0 with x y. tauto.
Qed.









