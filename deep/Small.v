Require Export FunctionalExtensionality.
Require Export PropExtensionality.
Require Export Structures.Orders.
Require Export List.
Require Export Sorting.
Require Export ZArith.
Require Export Classical.

Require Import OnSeparationLogic.StrongInduction.

Module Type AbstractSemantics.

Parameter op: Type.
Parameter test: Type.
Parameter state: Type.
Parameter op_interp: op -> state -> option (state -> Prop).
Parameter test_interp: test -> state -> Prop.

End AbstractSemantics.

Module AbstractSemanticsFacts (Import AS: AbstractSemantics).

Inductive program :=
| oper: op -> program
| diverge: program
| skip: program
| comp: program -> program -> program
| ite: test -> program -> program -> program
| while: test -> program -> program.
Coercion oper: op >-> program.

Inductive continuation :=
| done: continuation
| next: program -> continuation.
Coercion next: program >-> continuation.

Inductive configuration :=
| continue: continuation -> state -> configuration
| failure: configuration.

Inductive smallstep: configuration -> configuration -> Prop :=
| sstep_oper (O: op) (s s': state) (X: state -> Prop):
    op_interp O s = Some X /\ X s' ->
    smallstep (continue O s) (continue done s')
| sstep_oper_fail (O: op) (s: state):
    op_interp O s = None ->
    smallstep (continue O s) failure
| sstep_skip (s: state):
    smallstep (continue skip s) (continue done s)
| sstep_comp1 (S1 S1' S2: program) (s s': state):
    smallstep (continue S1 s) (continue S1' s') ->
    smallstep (continue (comp S1 S2) s) (continue (comp S1' S2) s')
| sstep_comp2 (S1 S2: program) (s s': state):
    smallstep (continue S1 s) (continue done s') ->
    smallstep (continue (comp S1 S2) s) (continue S2 s')
| sstep_comp_fail (S1 S2: program) (s: state):
    smallstep (continue S1 s) failure ->
    smallstep (continue (comp S1 S2) s) failure
| sstep_ite_true (T: test) (S1 S2: program) (s: state):
    test_interp T s ->
    smallstep (continue (ite T S1 S2) s) (continue S1 s)
| sstep_ite_false (T: test) (S1 S2: program) (s: state):
    ~test_interp T s ->
    smallstep (continue (ite T S1 S2) s) (continue S2 s)
| sstep_while_true (T: test) (S: program) (s: state):
    test_interp T s ->
    smallstep (continue (while T S) s) (continue (comp S (while T S)) s)
| sstep_while_false (T: test) (S: program) (s: state):
    ~test_interp T s ->
    smallstep (continue (while T S) s) (continue done s).

Inductive context :=
| hole: context
| comp_left: context -> program -> context
| comp_right: program -> context -> context
| ite_left: test -> context -> program -> context
| ite_right: test -> program -> context -> context
| while_body: test -> context -> context.

Fixpoint plug (C: context) (S: program): program :=
match C with
| hole => S
| comp_left C S2 => comp (plug C S) S2
| comp_right S1 C => comp S1 (plug C S)
| ite_left T C S2 => ite T (plug C S) S2
| ite_right T S1 C => ite T S1 (plug C S)
| while_body T C => while T (plug C S)
end.

Fixpoint prime (S: program): program :=
match S with
| comp S1 S2 => prime S1
| _ => S
end.

Fixpoint prime_context (S: program): context :=
match S with
| comp S1 S2 => comp_left (prime_context S1) S2
| _ => hole
end.

Proposition prime_prime_context (S: program):
  plug (prime_context S) (prime S) = S.
induction S; auto.
simpl. rewrite IHS1. auto.
Qed.

Lemma smallstep_prime (S S': program) (s s': state):
  smallstep (continue (prime S) s) (continue S' s') ->
  smallstep (continue S s) (continue (plug (prime_context S) S') s').
intro.
rewrite <- prime_prime_context at 1.
induction S; intros; simpl; try apply H.
apply sstep_comp1. apply IHS1. apply H.
Qed.

Lemma smallstep_prime_fail (S: program) (s: state):
  smallstep (continue (prime S) s) failure ->
  smallstep (continue S s) failure.
intro.
rewrite <- prime_prime_context at 1.
induction S; intros; simpl; try apply H.
apply sstep_comp_fail. apply IHS1. apply H.
Qed.

Lemma halt_diverge (s: state):
  forall C, ~smallstep (continue diverge s) C.
intro. intro. inversion H.
Qed.

Lemma smallstep_comp_diverge (S1 S2: program) (s: state):
  (forall C, ~ smallstep (continue S1 s) C) ->
  forall C, ~ smallstep (continue (comp S1 S2) s) C.
intros.
intro. inversion H0; apply H in H5; trivial.
Qed.

Lemma smallstep_prime_diverge (S: program) (s: state):
  (forall C, ~smallstep (continue (prime S) s) C) ->
  forall C, ~smallstep (continue S s) C.
intro.
induction S; try apply H.
simpl in H. apply smallstep_comp_diverge.
apply IHS1. apply H.
Qed.

Fixpoint remainder (S: program): continuation :=
match S with
| comp S1 S2 => match (remainder S1) with
                | done => S2
                | next S1 => comp S1 S2
                end
| _ => done
end.

Lemma smallstep_remainder (S: program) (s s': state):
  smallstep (continue (prime S) s) (continue done s') ->
  smallstep (continue S s) (continue (remainder S) s').
intro.
rewrite <- prime_prime_context at 1.
induction S; try apply H.
simpl in H. simpl.
destruct (remainder S1).
apply sstep_comp2. apply IHS1. apply H.
apply sstep_comp1. apply IHS1. apply H.
Qed.

Definition plug_remainder (C1: continuation) (S2: program): continuation :=
match C1 with
| done => remainder S2
| next S1 => (plug (prime_context S2) S1)
end.

Lemma smallstep_plug_remainder (S: program) (CC: continuation) (s s': state):
  smallstep (continue (prime S) s) (continue CC s') ->
  smallstep (continue S s) (continue (plug_remainder CC S) s').
intro. destruct CC.
apply smallstep_remainder; auto.
apply smallstep_prime; auto.
Qed.

Lemma smallstep_always_prime_done (S: program) (s s': state):
  smallstep (continue S s) (continue done s') ->
  smallstep (continue (prime S) s) (continue done s').
intro. inversion H; simpl.
- eapply sstep_oper. apply H1.
- apply sstep_skip.
- apply sstep_while_false. apply H1.
Qed.

Lemma smallstep_always_prime_fail (S: program) (s: state):
  smallstep (continue S s) failure ->
  smallstep (continue (prime S) s) failure.
induction S; intro; inversion H; simpl.
- apply sstep_oper_fail. apply H1.
- apply IHS1. apply H1.
Qed.

Proposition smallstep_done_or_not (S S': program) (s s': state):
  smallstep (continue S s) (continue S' s') ->
  ~smallstep (continue S s) (continue done s').
intros. intro.
inversion H0.
- rewrite <- H1 in H. inversion H.
- rewrite <- H2 in H. inversion H.
- rewrite <- H1 in H. inversion H.
  apply H2. auto.
Qed.

Proposition smallstep_ite_left_or_right (T: test) (S1 S2 S' S'': program) (s s': state):
  smallstep (continue (ite T S1 S2) s) (continue S' s') ->
  smallstep (continue (ite T S1 S2) s) (continue S'' s') -> S' = S''.
intros.
inversion H.
inversion H0.
rewrite <- H6. rewrite <- H13. reflexivity.
exfalso. apply H9. auto.
inversion H0.
exfalso. apply H2. auto.
rewrite <- H6. rewrite <- H13. reflexivity.
Qed.

Lemma smallstep_always_remainder (S S': program) (s s': state):
  smallstep (continue S s) (continue S' s') ->
  forall (S'': program), smallstep (continue (prime S) s) (continue S'' s') ->
    S' = plug (prime_context S) S''.
generalize dependent s'.
generalize dependent s.
generalize dependent S'.
induction S; intros; inversion H.
- simpl in *.
  apply IHS1 with (S'' := S'') in H2.
  rewrite H2. reflexivity.
  apply H0.
- apply smallstep_always_prime_done in H2.
  simpl in H0.
  eapply smallstep_done_or_not in H2. inversion H2. apply H0.
- inversion H0. simpl. rewrite <- H6. rewrite <- H13. auto.
  exfalso. apply H9. auto.
- inversion H0. exfalso. apply H2. auto.
  simpl. rewrite <- H6. rewrite <- H13. auto.
- inversion H0. simpl. reflexivity.
Qed.

Inductive bigstep: configuration -> configuration -> Prop :=
| bstep_oper (O: op) (s s': state) (X: state -> Prop):
    op_interp O s = Some X /\ X s' ->
    bigstep (continue O s) (continue done s')
| bstep_oper_fail (O: op) (s: state):
    op_interp O s = None ->
    bigstep (continue O s) failure
| bstep_skip (s: state):
    bigstep (continue skip s) (continue done s)
| bstep_comp (S1 S2: program) (s s' s'': state):
    bigstep (continue S1 s) (continue done s') ->
    bigstep (continue S2 s') (continue done s'') ->
    bigstep (continue (comp S1 S2) s) (continue done s'')
| bstep_comp_fail1 (S1 S2: program) (s: state):
    bigstep (continue S1 s) failure ->
    bigstep (continue (comp S1 S2) s) failure
| bstep_comp_fail2 (S1 S2: program) (s s': state):
    bigstep (continue S1 s) (continue done s') ->
    bigstep (continue S2 s') failure ->
    bigstep (continue (comp S1 S2) s) failure
| bstep_ite_true (T: test) (S1 S2: program) (s: state) (C: configuration):
    test_interp T s ->
    bigstep (continue S1 s) C ->
    bigstep (continue (ite T S1 S2) s) C
| bstep_ite_false (T: test) (S1 S2: program) (s: state) (C: configuration):
    ~test_interp T s ->
    bigstep (continue S2 s) C ->
    bigstep (continue (ite T S1 S2) s) C
| bstep_while_true (T: test) (S: program) (s: state) (C: configuration):
    test_interp T s ->
    bigstep (continue (comp S (while T S)) s) C ->
    bigstep (continue (while T S) s) C
| bstep_while_false (T: test) (S: program) (s: state):
    ~test_interp T s ->
    bigstep (continue (while T S) s) (continue done s).

Inductive smallstep_seq: configuration -> configuration -> Prop :=
| seq_head (C1 C2: configuration):
    smallstep C1 C2 ->
    smallstep_seq C1 C2
| seq_cons (C1 C2 C3: configuration):
    smallstep_seq C1 C2 ->
    smallstep C2 C3 ->
    smallstep_seq C1 C3.

Lemma smallstep_seq_append (C1 C2 C3: configuration):
  smallstep_seq C1 C2 ->
  smallstep_seq C2 C3 ->
  smallstep_seq C1 C3.
intros.
induction H0.
eapply seq_cons. apply H. apply H0.
eapply seq_cons. apply IHsmallstep_seq. apply H. apply H1.
Qed.

Inductive smallstep_trans: configuration -> configuration -> Prop :=
| trans_direct (C1 C2: configuration):
    smallstep C1 C2 ->
    smallstep_trans C1 C2
| trans_indirect (C1 C2 C3: configuration):
    smallstep_trans C1 C2 ->
    smallstep_trans C2 C3 ->
    smallstep_trans C1 C3.

Lemma smallstep_seq_trans (C1 C2: configuration):
  smallstep_seq C1 C2 -> smallstep_trans C1 C2.
intro.
induction H.
apply trans_direct; auto.
eapply trans_indirect.
apply IHsmallstep_seq.
apply trans_direct. apply H0.
Qed.

Lemma smallstep_trans_seq (C1 C2: configuration):
  smallstep_trans C1 C2 -> smallstep_seq C1 C2.
intro.
induction H.
apply seq_head; auto.
eapply smallstep_seq_append.
apply IHsmallstep_trans1.
apply IHsmallstep_trans2.
Qed.

Inductive smallstep_nat: nat -> configuration -> configuration -> Prop :=
| nat_one (C1 C2: configuration):
    smallstep C1 C2 ->
    smallstep_nat 1 C1 C2
| nat_succ (n: nat) (C1 C2 C3: configuration):
    smallstep_nat n C1 C2 ->
    smallstep C2 C3 ->
    smallstep_nat (S n) C1 C3.

Proposition smallstep_nat_zero (C1 C2: configuration):
  ~smallstep_nat 0 C1 C2.
intro. remember 0. induction H; inversion Heqn.
Qed.

Lemma smallstep_nat_append (n m: nat) (C1 C2 C3: configuration):
  smallstep_nat n C1 C2 ->
  smallstep_nat m C2 C3 ->
  smallstep_nat (n + m) C1 C3.
intros.
rewrite Nat.add_comm.
induction H0.
- eapply nat_succ. apply H. apply H0.
- simpl. eapply nat_succ. apply IHsmallstep_nat.
  apply H. apply H1.
Qed.

Inductive smallstep_tan: nat -> configuration -> configuration -> Prop :=
| tan_one (C1 C2: configuration):
    smallstep C1 C2 ->
    smallstep_tan 1 C1 C2
| tan_succ (n: nat) (C1 C2 C3: configuration):
    smallstep C1 C2 ->
    smallstep_tan n C2 C3 ->
    smallstep_tan (S n) C1 C3.

Proposition smallstep_tan_zero (C1 C2: configuration):
  ~smallstep_tan 0 C1 C2.
intro. remember 0. induction H; inversion Heqn.
Qed.

Lemma smallstep_tan_append (n m: nat) (C1 C2 C3: configuration):
  smallstep_tan n C1 C2 ->
  smallstep_tan m C2 C3 ->
  smallstep_tan (n + m) C1 C3.
intros.
induction H.
- simpl. eapply tan_succ. apply H.
  apply H0.
- simpl. eapply tan_succ. apply H.
  apply IHsmallstep_tan. apply H0.
Qed.

Lemma smallstep_nat_tan (n: nat) (C1 C2: configuration):
  smallstep_nat n C1 C2 -> smallstep_tan n C1 C2.
intros.
destruct n.
apply smallstep_nat_zero in H. inversion H.
generalize dependent C2.
generalize dependent C1.
induction n; intros.
- inversion H.
  apply tan_one. auto.
  apply smallstep_nat_zero in H1. inversion H1.
- inversion H.
  apply IHn in H1.
  apply tan_one in H2.
  Search "+" S.
  rewrite <- Nat.add_1_r.
  eapply smallstep_tan_append.
  apply H1. apply H2.
Qed.

Inductive smallstep_plus: nat -> configuration -> configuration -> Prop :=
| plus_unit (C1 C2: configuration):
    smallstep C1 C2 ->
    smallstep_plus 1 C1 C2
| plus_plus (n m: nat) (C1 C2 C3: configuration):
    smallstep_plus n C1 C2 ->
    smallstep_plus m C2 C3 ->
    smallstep_plus (n + m) C1 C3.

Proposition smallstep_plus_zero (C1 C2: configuration):
  ~smallstep_plus 0 C1 C2.
intro. remember 0. induction H.
inversion Heqn.
apply Nat.eq_add_0 in Heqn. destruct Heqn. auto.
Qed.

Lemma smallstep_plus_nat (n: nat) (C1 C2: configuration):
  smallstep_plus n C1 C2 -> smallstep_nat n C1 C2.
intro.
induction H.
apply nat_one; auto.
eapply smallstep_nat_append.
apply IHsmallstep_plus1.
apply IHsmallstep_plus2.
Qed.

Lemma smallstep_nat_plus (n: nat) (C1 C2: configuration):
  smallstep_nat n C1 C2 -> smallstep_plus n C1 C2.
intro.
induction H.
apply plus_unit; auto.
rewrite <- Nat.add_1_r.
eapply plus_plus.
apply IHsmallstep_nat.
apply plus_unit; auto.
Qed.

Lemma smallstep_trans_plus (C1 C2: configuration):
  smallstep_trans C1 C2 -> exists n, smallstep_plus n C1 C2.
intro.
induction H.
- exists 1. apply plus_unit; auto.
- destruct IHsmallstep_trans1.
  destruct IHsmallstep_trans2.
  exists (x + x0).
  eapply plus_plus. apply H1. apply H2.
Qed.

Lemma smallstep_plus_trans (n: nat) (C1 C2: configuration):
  smallstep_plus n C1 C2 -> smallstep_trans C1 C2.
intro.
generalize dependent C2.
generalize dependent C1.
strong induction n; intros.
destruct n.
- apply smallstep_plus_zero in H0. inversion H0.
- inversion H0.
  apply trans_direct; auto.
  (* we know n0 > 0 and m > 0 *)
  apply trans_indirect with (C2 := C3).
  apply H with (n := n0); auto.
  rewrite <- H1.
  apply Nat.lt_add_pos_r.
  apply neq_0_lt.
  intro. rewrite <- H6 in H3.
  apply smallstep_plus_zero in H3; auto.
  apply H with (n := m); auto.
  rewrite <- H1.
  apply Nat.lt_add_pos_l.
  apply neq_0_lt.
  intro. rewrite <- H6 in H2.
  apply smallstep_plus_zero in H2; auto.
Qed.

Proposition smallstep_done (s: state) (C: configuration):
  ~smallstep (continue done s) C.
intro. inversion H.
Qed.

Proposition smallstep_tan_done (n: nat) (s: state) (C: configuration):
  ~smallstep_tan n (continue done s) C.
intro. induction n.
apply smallstep_tan_zero in H; auto.
inversion H; apply smallstep_done in H1; inversion H1.
Qed.

Proposition smallstep_failure (C: configuration):
  ~smallstep failure C.
intro. inversion H.
Qed.

Proposition smallstep_tan_failure (n: nat) (C: configuration):
  ~smallstep_tan n failure C.
intro. induction n.
apply smallstep_tan_zero in H; auto.
inversion H; apply smallstep_failure in H1; inversion H1.
Qed.

Lemma smallstep_comp1_trans (S1 S1' S2: program) (s s': state):
  smallstep_trans (continue S1 s) (continue S1' s') ->
  smallstep_trans (continue (comp S1 S2) s) (continue (comp S1' S2) s').
intros.
apply smallstep_trans_plus in H; destruct H.
apply smallstep_plus_nat in H.
destruct x.
apply smallstep_nat_zero in H. inversion H.
generalize dependent s'.
generalize dependent S1'.
induction x; intros.
- inversion H.
  apply trans_direct.
  apply sstep_comp1. auto.
  apply smallstep_nat_zero in H1. inversion H1.
- inversion H.
  destruct C2.
  destruct c.
  apply smallstep_done in H2. inversion H2.
  apply IHx in H1.
  eapply sstep_comp1 in H2.
  eapply trans_indirect.
  apply H1.
  apply trans_direct. apply H2.
  apply smallstep_failure in H2. inversion H2.
Qed.

Lemma smallstep_comp2_trans (S1 S2: program) (s s': state):
    smallstep_trans (continue S1 s) (continue done s') ->
    smallstep_trans (continue (comp S1 S2) s) (continue S2 s').
intros.
apply smallstep_trans_plus in H; destruct H.
apply smallstep_plus_nat in H.
apply smallstep_nat_tan in H.
destruct x.
apply smallstep_tan_zero in H. inversion H.
generalize dependent s'.
generalize dependent s.
generalize dependent S1.
induction x; intros.
- inversion H.
  apply trans_direct.
  apply sstep_comp2. auto.
  apply smallstep_tan_zero in H2. inversion H2.
- inversion H.
  destruct C2.
  destruct c.
  apply smallstep_tan_done in H2. inversion H2.
  apply IHx in H2.
  apply sstep_comp1 with (S2 := S2) in H1.
  apply trans_direct in H1.
  eapply trans_indirect. apply H1. apply H2.
  apply smallstep_tan_failure in H2. inversion H2.
Qed.

Lemma smallstep_trans_comp (S1 S2: program) (s s' s'': state):
  smallstep_trans (continue S1 s) (continue done s') ->
  smallstep_trans (continue S2 s') (continue done s'') ->
  smallstep_trans (continue (comp S1 S2) s) (continue done s'').
intros.
eapply smallstep_comp2_trans in H.
eapply trans_indirect. apply H. apply H0.
Qed.

Lemma smallstep_trans_failure (S1 S2: program) (s: state):
  smallstep_trans (continue S1 s) failure ->
  smallstep_trans (continue (comp S1 S2) s) failure.
intros.
apply smallstep_trans_plus in H.
destruct H.
apply smallstep_plus_nat in H.
apply smallstep_nat_tan in H.
generalize dependent s.
generalize dependent S1.
induction x; intros.
- apply smallstep_tan_zero in H. inversion H.
- inversion H.
  apply trans_direct.
  apply sstep_comp_fail. apply H1.
  destruct C2.
  destruct c.
  apply smallstep_tan_done in H2. inversion H2.
  apply IHx in H2.
  eapply sstep_comp1 in H1.
  apply trans_direct in H1.
  eapply trans_indirect. apply H1. apply H2.
  apply smallstep_tan_failure in H2. inversion H2.
Qed.

Lemma bigstep_smallstep_trans (C1 C2: configuration):
  bigstep C1 C2 -> smallstep_trans C1 C2.
intro.
induction H.
- apply trans_direct.
  eapply sstep_oper; apply H.
- apply trans_direct.
  apply sstep_oper_fail; auto.
- apply trans_direct.
  apply sstep_skip.
- eapply smallstep_trans_comp. apply IHbigstep1. apply IHbigstep2.
- apply smallstep_trans_failure. auto.
- eapply smallstep_comp2_trans in IHbigstep1.
  eapply trans_indirect. apply IHbigstep1. apply IHbigstep2.
- eapply trans_indirect.
  apply trans_direct.
  apply sstep_ite_true. auto. auto.
- eapply trans_indirect.
  apply trans_direct.
  apply sstep_ite_false. auto. auto.
- eapply trans_indirect.
  apply trans_direct.
  apply sstep_while_true. auto. auto.
- apply trans_direct.
  apply sstep_while_false. auto.
Qed.

Proposition bigstep_done (s: state) (C: configuration):
  ~bigstep (continue done s) C.
intro. inversion H.
Qed.

Proposition bigstep_failure (C: configuration):
  ~bigstep failure C.
intro. inversion H.
Qed.

Proposition bigstep_continue_final (C: configuration) (S: program) (s: state):
  ~bigstep C (continue S s).
intro. destruct C. destruct c.
apply bigstep_done in H. auto.
induction p; inversion H.
apply IHp1 in H6. auto.
apply IHp2 in H6. auto.
inversion H5.
apply bigstep_failure in H. auto.
Qed.

Proposition smallstep_bigstep_fail (S: program) (s: state):
  smallstep (continue S s) failure ->
  bigstep (continue S s) failure.
intros. induction S; inversion H.
apply bstep_oper_fail. auto.
apply bstep_comp_fail1.
apply IHS1.
apply H1.
Qed.

Lemma smallstep_bigstep (C1 C2 C3: configuration):
  smallstep C1 C2 -> bigstep C2 C3 -> bigstep C1 C3.
intros.
destruct C1. destruct c.
apply smallstep_done in H. inversion H.
destruct C2. destruct c.
apply bigstep_done in H0. inversion H0.
rename p into S1. rename p0 into S2.
rename s0 into s'.
generalize dependent S2.
generalize dependent s.
generalize dependent s'.
generalize dependent C3.
induction S1; intros; inversion H.
- destruct C3. destruct c.
  + rewrite <- H5 in H0. inversion H0.
    eapply bstep_comp; [|apply H12].
    eapply IHS1_1. apply H2. apply H9.
  + apply bigstep_continue_final in H0. inversion H0.
  + rewrite <- H5 in H0.
    inversion H0.
    eapply bstep_comp_fail1.
    eapply IHS1_1. apply H2. apply H8.
    eapply bstep_comp_fail2; [|apply H11].
    eapply IHS1_1. apply H2. apply H9.
- destruct C3. destruct c.
  + eapply bstep_comp; [|apply H0].
    inversion H2.
    eapply bstep_oper. apply H8.
    apply bstep_skip.
    apply bstep_while_false. auto.
  + apply bigstep_continue_final in H0. inversion H0.
  + eapply bstep_comp_fail2; [|apply H0].
    inversion H2.
    eapply bstep_oper. apply H8.
    apply bstep_skip.
    apply bstep_while_false. auto.
- apply bstep_ite_true. auto. auto.
- apply bstep_ite_false. auto. auto.
- apply bstep_while_true. auto.
  rewrite H5. auto.
- apply bigstep_failure in H0. inversion H0.
- apply smallstep_failure in H. inversion H.
Qed.

Lemma smallstep_trans_bigstep_fail (C1: configuration):
  smallstep_trans C1 failure -> bigstep C1 failure.
intro.
apply smallstep_trans_plus in H; destruct H.
apply smallstep_plus_nat in H.
apply smallstep_nat_tan in H.
generalize dependent C1.
induction x; intros.
- apply smallstep_tan_zero in H. inversion H.
- inversion H.
  + destruct C1.
    destruct c.
    apply smallstep_done in H1. inversion H1.
    apply smallstep_bigstep_fail. auto.
    apply smallstep_failure in H1. inversion H1.
  + apply IHx in H2.
    eapply smallstep_bigstep. apply H1. apply H2.
Qed.

Lemma smallstep_trans_bigstep (C1: configuration) (s: state):
  smallstep_trans C1 (continue done s) -> bigstep C1 (continue done s).
intro.
apply smallstep_trans_plus in H; destruct H.
apply smallstep_plus_nat in H.
apply smallstep_nat_tan in H.
generalize dependent C1.
induction x; intros.
- apply smallstep_tan_zero in H. inversion H.
- inversion H.
  + destruct C1.
    destruct c.
    apply smallstep_done in H1. inversion H1.
    inversion H1.
    eapply bstep_oper. apply H5.
    apply bstep_skip.
    apply bstep_while_false. auto.
    apply smallstep_failure in H1. inversion H1.
  + apply IHx in H2.
    eapply smallstep_bigstep. apply H1. apply H2.
Qed.
