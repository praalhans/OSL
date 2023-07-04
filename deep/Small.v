Require Export FunctionalExtensionality.
Require Export PropExtensionality.
Require Export Structures.Orders.
Require Export List.
Require Export Sorting.
Require Export ZArith.
Require Export Classical.

Require Import OnSeparationLogic.StrongInduction.

Section ProgramSignature.

Variable op: Type.
Variable test: Type.

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

Fixpoint remainder (S: program): continuation :=
match S with
| comp S1 S2 => match (remainder S1) with
                | done => S2
                | next S1 => comp S1 S2
                end
| _ => done
end.

Definition plug_remainder (C1: continuation) (S2: program): continuation :=
match C1 with
| done => remainder S2
| next S1 => (plug (prime_context S2) S1)
end.

Record machine_model (mstate: Type) :=
{ mop_interp: op -> mstate -> option (mstate -> Prop)
; mtest_interp: test -> mstate -> Prop }.

Section AbstractSemantics.

Context {state: Type}.
Variable M: machine_model state.
Definition op_interp (o: op) (s: state) := mop_interp state M o s.
Definition test_interp (t: test) (s: state) := mtest_interp state M t s.

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

Definition resultset := option state -> Prop.
Definition stateset := state -> Prop.

Definition stateset_to_resultset (X: stateset): resultset :=
fun os => exists s, os = Some s /\ X s.
Coercion stateset_to_resultset: stateset >-> resultset.

Definition bigstep_initial_resultset (I: configuration): resultset :=
fun os => match os with
| None => bigstep I failure
| Some s => bigstep I (continue done s)
end.

Definition bigstep_program_resultset (S: program) (os: option state): resultset :=
match os with
| None => fun os' => os' = None
| Some s => bigstep_initial_resultset (continue S s)
end.

Definition bigstep_denotation (S: program) (Y: resultset): resultset :=
fun os => forall y, Y y -> (bigstep_program_resultset S y) os.

Definition compose {A: Type} (f g: A -> A): A -> A := fun x => f (g x).

Definition cap_fail (Y: resultset): resultset :=
fun os => Y os /\ os = None.
Definition cap_state (Y: resultset) (X: state -> Prop): resultset :=
fun os => Y os /\ forall s, os = Some s -> X s.
Definition complement (X: state -> Prop): state -> Prop :=
fun s => ~X s.

Fixpoint approx_denotation (n: nat): program -> resultset -> resultset :=
fix approx_denotation_prog (S: program) :=
  match S with
  | oper o => fun Y os =>
      cap_fail Y os \/
      (exists s, Y (Some s) /\ op_interp o s = None /\ os = None) \/
      (exists s X s', Y (Some s) /\ op_interp o s = Some X /\ os = Some s' /\ X s')
  | skip => id
  | diverge => cap_fail
  | comp S1 S2 => compose (approx_denotation_prog S2) (approx_denotation_prog S1)
  | ite T S1 S2 => fun Y os =>
      cap_fail Y os \/
      (approx_denotation_prog S1 (cap_state Y (test_interp T)) os) \/
      (approx_denotation_prog S2 (cap_state Y (complement (test_interp T))) os)
  | while T S1 =>
      match n with
      | O => cap_fail
      | S n => approx_denotation n (ite T (comp S1 (while T S1)) skip)
      end
  end.
Proposition approx_denotation_comp (n: nat) (S1 S2: program):
  approx_denotation n (comp S1 S2) = compose (approx_denotation n S2) (approx_denotation n S1).
destruct n; reflexivity.
Qed.
Proposition approx_denotation_ite (n: nat) (T: test) (S1 S2: program) (Y: resultset):
  approx_denotation n (ite T S1 S2) Y =
  fun os => (cap_fail Y os) \/
    (approx_denotation n S1 (cap_state Y (test_interp T)) os) \/
    (approx_denotation n S2 (cap_state Y (complement (test_interp T))) os).
destruct n.
apply functional_extensionality; intros.
apply propositional_extensionality.
simpl.
apply or_iff_compat_l.
apply ZifyClasses.or_morph.
apply iff_refl.
apply iff_refl.
apply functional_extensionality; intros.
apply propositional_extensionality.
simpl.
apply or_iff_compat_l.
apply ZifyClasses.or_morph.
apply iff_refl.
apply iff_refl.
Qed.
Proposition approx_denotation_while (n: nat) (T: test) (S1: program):
  approx_denotation (S n) (while T S1) = approx_denotation n (ite T (comp S1 (while T S1)) skip).
reflexivity.
Qed.

Lemma approx_monotonic (n: nat) (S1: program) (X Y: resultset):
  (forall os, X os -> Y os) ->
  forall os, approx_denotation n S1 X os -> approx_denotation n S1 Y os.
intros. generalize dependent Y. generalize dependent X. generalize dependent os. generalize dependent S1. induction n; intros.
- generalize dependent Y. generalize dependent X. generalize dependent os. induction S1; intros.
  + simpl in *. destruct H0.
    left. unfold cap_fail in *. destruct H0. constructor; auto.
    right. destruct H0.
    left. destruct H0. exists x. destruct H0. destruct H1. constructor; auto.
    right. destruct H0. destruct H0. destruct H0. destruct H0. destruct H1. destruct H2.
    exists x. exists x0. exists x1. constructor; auto.
  + simpl in *. unfold cap_fail in *. destruct H0. constructor; auto.
  + simpl in *. unfold id in *. auto.
  + rewrite approx_denotation_comp in H0.
    rewrite approx_denotation_comp.
    unfold compose in *.
    eapply IHS1_2. apply H0. intros.
    eapply IHS1_1. apply H1. apply H.
  + rewrite approx_denotation_ite in H0.
    rewrite approx_denotation_ite.
    destruct H0. left. unfold cap_fail in *. destruct H0. constructor; auto.
    destruct H0. right. left.
    eapply IHS1_1. apply H0. intros.
    unfold cap_state in *. destruct H1. constructor; auto.
    right. right. eapply IHS1_2. apply H0.
    intros. unfold cap_state in *. destruct H1. constructor; auto.
  + unfold approx_denotation in H0. unfold cap_fail in H0.
    unfold approx_denotation. unfold cap_fail. destruct H0. constructor; auto.
- generalize dependent Y. generalize dependent X. generalize dependent os. induction S1; intros.
  + simpl in *. destruct H0.
    left. unfold cap_fail in *. destruct H0. constructor; auto.
    right. destruct H0.
    left. destruct H0. exists x. destruct H0. destruct H1. constructor; auto.
    right. destruct H0. destruct H0. destruct H0. destruct H0. destruct H1. destruct H2.
    exists x. exists x0. exists x1. constructor; auto.
  + simpl in *. unfold cap_fail in *. destruct H0. constructor; auto.
  + simpl in *. unfold id in *. auto.
  + rewrite approx_denotation_comp in H0.
    rewrite approx_denotation_comp.
    unfold compose in *.
    eapply IHS1_2. apply H0. intros.
    eapply IHS1_1. apply H1. apply H.
  + rewrite approx_denotation_ite in H0.
    rewrite approx_denotation_ite.
    destruct H0. left. unfold cap_fail in *. destruct H0. constructor; auto.
    destruct H0. right. left.
    eapply IHS1_1. apply H0. intros.
    unfold cap_state in *. destruct H1. constructor; auto.
    right. right. eapply IHS1_2. apply H0.
    intros. unfold cap_state in *. destruct H1. constructor; auto.
  + rewrite approx_denotation_while in H0.
    rewrite approx_denotation_while.
    eapply IHn. apply H0. apply H.
Qed.

Lemma approximation (n: nat) (S1: program) (Y: resultset):
  forall os, approx_denotation n S1 Y os -> approx_denotation (S n) S1 Y os.
intros. generalize dependent S1. generalize dependent os. generalize dependent Y. induction n; intros.
- generalize dependent os. generalize dependent Y. induction S1; intros; auto.
  + rewrite approx_denotation_comp in H.
    rewrite approx_denotation_comp.
    unfold compose in *.
    apply IHS1_2.
    eapply approx_monotonic; [|apply H].
    apply IHS1_1.
  + rewrite approx_denotation_ite in H.
    rewrite approx_denotation_ite.
    destruct H. left; auto.
    destruct H; right.
    left. apply IHS1_1. auto.
    right. apply IHS1_2. auto.
  + simpl in H. unfold approx_denotation; left. auto.
- generalize dependent os. generalize dependent Y. induction S1; intros; auto.
  + rewrite approx_denotation_comp in H.
    rewrite approx_denotation_comp.
    unfold compose in *.
    apply IHS1_2.
    eapply approx_monotonic; [|apply H].
    apply IHS1_1.
  + rewrite approx_denotation_ite in H.
    rewrite approx_denotation_ite.
    destruct H. left; auto.
    destruct H; right.
    left. apply IHS1_1. auto.
    right. apply IHS1_2. auto.
  + rewrite approx_denotation_while in H.
    rewrite approx_denotation_while.
    apply IHn. auto.
Qed.

Corollary approximation_le (n m: nat) (S1: program) (Y: resultset):
  n <= m -> forall os, approx_denotation n S1 Y os -> approx_denotation m S1 Y os.
intro. induction m.
- inversion H. auto.
- inversion H. auto.
  intros.
  apply approximation.
  apply IHm; auto.
Qed.

Proposition approx_comp (n m: nat) (S1 S2: program) (X: resultset) (os: option state):
  approx_denotation n S2 (approx_denotation m S1 X) os ->
  approx_denotation (max n m) (comp S1 S2) X os.
intros.
generalize dependent os.
generalize dependent X.
generalize dependent S2.
generalize dependent S1.
generalize dependent m.
induction n; intros.
- simpl. rewrite approx_denotation_comp.
  unfold compose.
  apply approximation_le with (n := 0).
  apply Nat.le_0_l. auto.
- rewrite approx_denotation_comp.
  unfold compose.
  destruct m.
  + rewrite Nat.max_0_r.
    eapply approx_monotonic; [|apply H].
    intros. apply approximation_le with (n := 0).
    apply Nat.le_0_l. auto.
  + rewrite <- Nat.succ_max_distr.
    generalize dependent os.
    generalize dependent X.
    generalize dependent S1.
    generalize dependent n.
    generalize dependent m.
    induction S2; intros.
    * unfold approx_denotation at 1.
      unfold approx_denotation in H at 1.
      destruct H. left. unfold cap_fail in *.
      destruct H. constructor.
      eapply approximation_le; [|apply H].
      apply Peano.le_n_S.
      apply Nat.le_max_r. auto.
      right. destruct H. left.
      destruct H. exists x. destruct H.
      constructor.
      eapply approximation_le; [|apply H].
      apply Peano.le_n_S.
      apply Nat.le_max_r. auto.
      right. destruct H. destruct H. destruct H. destruct H.
      exists x. exists x0. exists x1. constructor.
      eapply approximation_le; [|apply H].
      apply Peano.le_n_S.
      apply Nat.le_max_r. auto.
    * unfold approx_denotation at 1.
      unfold approx_denotation in H at 1.
      unfold cap_fail in *. destruct H. constructor; auto.
      eapply approximation_le; [|apply H].
      apply Peano.le_n_S.
      apply Nat.le_max_r.
    * unfold approx_denotation at 1.
      unfold approx_denotation in H at 1.
      unfold id in *.
      eapply approximation_le; [|apply H].
      apply Peano.le_n_S.
      apply Nat.le_max_r.
    * rewrite approx_denotation_comp.
      rewrite approx_denotation_comp in H.
      unfold compose in *.
      apply approx_monotonic with (Y := (approx_denotation (S (max n m)) S2_1 (approx_denotation (S m) S1 X))) in H.
      **  apply IHS2_2 in H; auto.
          rewrite Nat.max_assoc in H.
          rewrite Nat.max_id in H.
          eapply approx_monotonic; [|apply H].
          intros.
          eapply approx_monotonic; [|apply H0].
          intros.
          eapply approximation_le; [|apply H1].
          apply Peano.le_n_S.
          apply Nat.le_max_r.
      **  intros.
          eapply approximation_le; [|apply H0].
          apply Peano.le_n_S.
          apply Nat.le_max_l.
    * rewrite approx_denotation_ite.
      rewrite approx_denotation_ite in H. destruct H.
      left. unfold cap_fail in *.
      destruct H. constructor; auto.
      eapply approximation_le; [|apply H].
      apply Peano.le_n_S.
      apply Nat.le_max_r.
      destruct H. right. left.
      apply approx_monotonic with (Y := (cap_state (approx_denotation (S (max n m)) S1 X) (test_interp t))) in H.
      eapply approximation_le; [|apply H].
      apply Peano.le_n_S.
      apply Nat.le_max_l.
      intros. unfold cap_state in H0. unfold cap_state. destruct H0.
      constructor.
      eapply approximation_le; [|apply H0].
      apply Peano.le_n_S.
      apply Nat.le_max_r. auto.
      right. right.
      apply approx_monotonic with (Y := (cap_state (approx_denotation (S (max n m)) S1 X) (complement (test_interp t)))) in H.
      eapply approximation_le; [|apply H].
      apply Peano.le_n_S.
      apply Nat.le_max_l.
      intros. unfold cap_state in H0. unfold cap_state. destruct H0.
      constructor.
      eapply approximation_le; [|apply H0].
      apply Peano.le_n_S.
      apply Nat.le_max_r. auto.
    * rewrite approx_denotation_while in H.
      rewrite approx_denotation_while.
      rewrite approx_denotation_ite.
      rewrite approx_denotation_ite in H. destruct H.
      left. unfold cap_fail in *.
      destruct H. constructor; auto.
      eapply approximation_le; [|apply H].
      apply Peano.le_n_S.
      apply Nat.le_max_r.
      right. destruct H; [left|right].
      apply approx_monotonic with (Y := (cap_state (approx_denotation (S (Nat.max n m)) S1 X) (test_interp t))) in H.
      eapply approximation_le; [|apply H].
      apply Nat.le_max_l.
      intros. unfold cap_state in H0. unfold cap_state. destruct H0.
      constructor. eapply approximation_le; [|apply H0].
      apply Peano.le_n_S.
      apply Nat.le_max_r. auto.
      apply approx_monotonic with (Y := (cap_state (approx_denotation (S (Nat.max n m)) S1 X) (complement (test_interp t)))) in H.
      eapply approximation_le; [|apply H].
      apply Nat.le_max_l.
      intros. unfold cap_state in H0. unfold cap_state. destruct H0.
      constructor. eapply approximation_le; [|apply H0].
      apply Peano.le_n_S.
      apply Nat.le_max_r. auto.
Qed.

Definition denotation (S1: program): resultset -> resultset :=
fun Y os => exists n, approx_denotation n S1 Y os.

Lemma denotation_monotonic (S1: program) (X Y: resultset):
  (forall os, X os -> Y os) ->
  forall os, denotation S1 X os -> denotation S1 Y os.
intros. unfold denotation in H0. unfold denotation.
destruct H0. exists x.
eapply approx_monotonic; [|apply H0].
auto.
Qed.

Proposition denotation_oper (o: op):
  denotation (oper o) = (fun Y os =>
      cap_fail Y os \/
      (exists s, Y (Some s) /\ op_interp o s = None /\ os = None) \/
      (exists s X s', Y (Some s) /\ op_interp o s = Some X /\ os = Some s' /\ X s')).
unfold denotation. unfold approx_denotation.
apply functional_extensionality; intro.
apply functional_extensionality; intro.
apply propositional_extensionality.
split; intro. destruct H. destruct x1; auto.
exists 0. auto.
Qed.

Proposition denotation_skip:
  denotation skip = id.
unfold denotation. unfold approx_denotation.
apply functional_extensionality; intro.
apply functional_extensionality; intro.
apply propositional_extensionality.
split; intro. destruct H. destruct x1; auto.
exists 0. auto.
Qed.

Proposition denotation_diverge:
  denotation diverge = cap_fail.
unfold denotation. unfold approx_denotation.
apply functional_extensionality; intro.
apply functional_extensionality; intro.
apply propositional_extensionality.
split; intro. destruct H. destruct x1; auto.
exists 0. auto.
Qed.

Proposition approx_assoc (n: nat) (S1 S2 S3: program) (X: resultset):
  approx_denotation n (comp (comp S1 S2) S3) X =
  approx_denotation n (comp S1 (comp S2 S3)) X.
rewrite approx_denotation_comp.
rewrite approx_denotation_comp.
rewrite approx_denotation_comp.
rewrite approx_denotation_comp.
unfold compose.
reflexivity.
Qed.

Proposition denotation_assoc (S1 S2 S3: program) (X: resultset):
  denotation (comp (comp S1 S2) S3) X =
  denotation (comp S1 (comp S2 S3)) X.
unfold denotation.
apply functional_extensionality; intro os.
apply propositional_extensionality; split; intro; destruct H; exists x.
rewrite <- approx_assoc. auto.
rewrite approx_assoc. auto.
Qed.

Definition assert (T: test): program := ite T skip diverge.
Definition assert_not (T: test): program := ite T diverge skip.

Proposition approx_fail (n: nat) (S1: program) (X: resultset):
  X None -> approx_denotation n S1 X None.
intros.
generalize dependent X.
generalize dependent S1.
induction n; intro.
- induction S1; intros.
  + unfold approx_denotation. left. unfold cap_fail. auto.
  + unfold approx_denotation. unfold cap_fail. auto.
  + unfold approx_denotation. unfold id. auto.
  + rewrite approx_denotation_comp. unfold compose.
    apply IHS1_2. apply IHS1_1. auto.
  + rewrite approx_denotation_ite. left. unfold cap_fail. auto.
  + unfold approx_denotation. unfold cap_fail. auto.
- induction S1; intros.
  + unfold approx_denotation. left. unfold cap_fail. auto.
  + unfold approx_denotation. unfold cap_fail. auto.
  + unfold approx_denotation. unfold id. auto.
  + rewrite approx_denotation_comp. unfold compose.
    apply IHS1_2. apply IHS1_1. auto.
  + rewrite approx_denotation_ite. left. unfold cap_fail. auto.
  + rewrite approx_denotation_while.
    apply IHn. auto.
Qed.

Proposition denotation_assert (T: test) (S: program) (X: resultset) (os: option state):
  (cap_state (denotation S X) (test_interp T)) os -> (denotation (comp S (assert T)) X) os.
unfold denotation in *; unfold cap_state in *; intros.
destruct H. destruct H. exists x.
rewrite approx_denotation_comp. unfold compose.
unfold assert. rewrite approx_denotation_ite.
right. left. unfold approx_denotation at 1; destruct x; unfold id;
unfold cap_state; auto.
Qed.

Proposition denotation_assert_not (T: test) (S: program) (X: resultset) (os: option state):
  (cap_state (denotation S X) (complement (test_interp T))) os -> (denotation (comp S (assert_not T)) X) os.
unfold denotation in *; unfold cap_state in *; intros.
destruct H. destruct H. exists x.
rewrite approx_denotation_comp. unfold compose.
unfold assert_not. rewrite approx_denotation_ite.
right. right. unfold approx_denotation at 1; destruct x; unfold id;
unfold cap_state; auto.
Qed.

Proposition approx_ite_comp (n: nat) (T: test) (S1 S2 S3: program) (X: resultset) (os: option state):
  approx_denotation n (ite T S1 S2) (denotation S3 X) os ->
    approx_denotation n S1 (denotation (comp S3 (assert T)) X) os \/
    approx_denotation n S2 (denotation (comp S3 (assert_not T)) X) os.
intro.
rewrite approx_denotation_ite in H.
destruct H.
unfold cap_fail in H. destruct H. rewrite H0 in *. clear dependent H0.
left. apply approx_fail. unfold denotation in H. destruct H.
unfold denotation. exists x. rewrite approx_denotation_comp. unfold compose.
apply approx_fail. auto.
destruct H; [left|right].
eapply approx_monotonic; [intros|apply H].
apply denotation_assert in H0. auto.
eapply approx_monotonic; [intros|apply H].
apply denotation_assert_not in H0. auto.
Qed.

Proposition approx_comp_ite_left (n: nat) (T: test) (S1 S2 S3: program) (X: resultset) (os: option state):
  approx_denotation n (comp (comp S1 (assert T)) S2) X os ->
  approx_denotation n (comp S1 (ite T S2 S3)) X os.
intros.
rewrite approx_denotation_comp in H.
rewrite approx_denotation_comp.
unfold compose in *.
rewrite approx_denotation_ite.
right. left.
eapply approx_monotonic; [intros|apply H].
rewrite approx_denotation_comp in H0.
unfold compose in H0.
unfold assert in H0.
rewrite approx_denotation_ite in H0.
destruct H0. unfold cap_fail in H0. destruct H0. rewrite H1.
unfold cap_state. constructor. rewrite H1 in H0; auto. intros. inversion H2.
destruct H0.
unfold approx_denotation in H0 at 1; destruct n; unfold id in H0; auto.
unfold approx_denotation in H0 at 1; destruct n; unfold cap_fail in H0. destruct H0.
unfold cap_state in H0. destruct H0.
unfold cap_state. constructor; auto. intros. rewrite H1 in H3. inversion H3.
unfold cap_state in H0. destruct H0. destruct H0.
unfold cap_state. constructor; auto. intros. rewrite H1 in H3. inversion H3.
Qed.

Proposition approx_comp_ite_right (n: nat) (T: test) (S1 S2 S3: program) (X: resultset) (os: option state):
  approx_denotation n (comp (comp S1 (assert_not T)) S3) X os ->
  approx_denotation n (comp S1 (ite T S2 S3)) X os.
intros.
rewrite approx_denotation_comp in H.
rewrite approx_denotation_comp.
unfold compose in *.
rewrite approx_denotation_ite.
right. right.
eapply approx_monotonic; [intros|apply H].
rewrite approx_denotation_comp in H0.
unfold compose in H0.
unfold assert_not in H0.
rewrite approx_denotation_ite in H0.
destruct H0. unfold cap_fail in H0. destruct H0. rewrite H1.
unfold cap_state. constructor. rewrite H1 in H0; auto. intros. inversion H2.
destruct H0.
unfold approx_denotation in H0 at 1; destruct n; unfold cap_fail in H0. destruct H0.
unfold cap_state in H0. destruct H0.
unfold cap_state. constructor; auto. intros. rewrite H1 in H3. inversion H3.
unfold cap_state in H0. destruct H0. destruct H0.
unfold cap_state. constructor; auto. intros. rewrite H1 in H3. inversion H3.
unfold approx_denotation in H0 at 1; destruct n; unfold id in H0; auto.
Qed.

(* Proposition approx_fail (n: nat) (S1: program) (X: resultset): *)

Lemma denotation_comp (S1 S2: program):
  denotation (comp S1 S2) = compose (denotation S2) (denotation S1).
unfold compose.
apply functional_extensionality; intro.
apply functional_extensionality; intro.
apply propositional_extensionality.
unfold denotation.
split; intro.
- destruct H.
  exists x1.
  rewrite approx_denotation_comp in H.
  unfold compose in H.
  eapply approx_monotonic; [|apply H].
  intros.
  exists x1. auto.
- destruct H.
  generalize dependent x0.
  generalize dependent x.
  generalize dependent S1.
  generalize dependent S2.
  induction x1; intro.
  + induction S2; intros.
    * unfold approx_denotation in H at 1. destruct H.
      unfold cap_fail in H. destruct H. destruct H.
      exists x1. rewrite approx_denotation_comp. unfold compose.
      unfold approx_denotation at 1. destruct x1; left.
      unfold cap_fail. auto. unfold cap_fail. auto.
      destruct H. destruct H. destruct H. destruct H.
      exists x2. rewrite approx_denotation_comp. unfold compose.
      unfold approx_denotation at 1.
      destruct x2; right; left; exists x1; constructor; auto.
      destruct H. destruct H. destruct H. destruct H. destruct H.
      exists x4. rewrite approx_denotation_comp. unfold compose.
      unfold approx_denotation at 1.
      destruct x4; right; right; exists x1; exists x2; exists x3; constructor; auto.
    * unfold approx_denotation in H at 1.
      unfold cap_fail in H. destruct H. destruct H.
      exists x1. rewrite approx_denotation_comp; unfold compose.
      unfold approx_denotation at 1. destruct x1; unfold cap_fail; auto.
    * unfold approx_denotation in H at 1.
      unfold id in H. destruct H.
      exists x1. rewrite approx_denotation_comp; unfold compose.
      unfold approx_denotation at 1. destruct x1; unfold id; auto.
    * rewrite approx_denotation_comp in H. unfold compose in H.
      apply approx_monotonic with (Y := fun os => (exists n : nat, approx_denotation n (comp S1 S2_1) x os)) in H.
      enough (exists n : nat, approx_denotation n (comp (comp S1 S2_1) S2_2) x x0).
      destruct H0. exists x1. rewrite <- approx_assoc. auto.
      apply IHS2_2. auto.
      intros. apply IHS2_1. auto.
    * fold (denotation S1 x) in H. apply approx_ite_comp in H.
      destruct H.
      apply IHS2_1 in H. destruct H. exists x1.
      apply approx_comp_ite_left. auto.
      apply IHS2_2 in H. destruct H. exists x1.
      apply approx_comp_ite_right. auto.
    * unfold approx_denotation in H at 1. unfold cap_fail in H. destruct H. destruct H.
      exists x1. rewrite approx_denotation_comp. unfold compose. rewrite H0. apply approx_fail.
      rewrite H0 in H. auto.
  + induction S2; intros.
    * unfold approx_denotation in H at 1. destruct H.
      unfold cap_fail in H. destruct H. destruct H.
      exists x2. rewrite approx_denotation_comp. unfold compose.
      unfold approx_denotation at 1. destruct x2; left.
      unfold cap_fail. auto. unfold cap_fail. auto.
      destruct H. destruct H. destruct H. destruct H.
      exists x3. rewrite approx_denotation_comp. unfold compose.
      unfold approx_denotation at 1.
      destruct x3; right; left; exists x2; constructor; auto.
      destruct H. destruct H. destruct H. destruct H. destruct H.
      exists x5. rewrite approx_denotation_comp. unfold compose.
      unfold approx_denotation at 1.
      destruct x5; right; right; exists x2; exists x3; exists x4; constructor; auto.
    * unfold approx_denotation in H at 1.
      unfold cap_fail in H. destruct H. destruct H.
      exists x2. rewrite approx_denotation_comp; unfold compose.
      unfold approx_denotation at 1. destruct x2; unfold cap_fail; auto.
    * unfold approx_denotation in H at 1.
      unfold id in H. destruct H.
      exists x2. rewrite approx_denotation_comp; unfold compose.
      unfold approx_denotation at 1. destruct x2; unfold id; auto.
    * rewrite approx_denotation_comp in H. unfold compose in H.
      apply approx_monotonic with (Y := fun os => (exists n : nat, approx_denotation n (comp S1 S2_1) x os)) in H.
      enough (exists n : nat, approx_denotation n (comp (comp S1 S2_1) S2_2) x x0).
      destruct H0. exists x2. rewrite <- approx_assoc. auto.
      apply IHS2_2. auto.
      intros. apply IHS2_1. auto.
    * fold (denotation S1 x) in H. apply approx_ite_comp in H.
      destruct H.
      apply IHS2_1 in H. destruct H. exists x2.
      apply approx_comp_ite_left. auto.
      apply IHS2_2 in H. destruct H. exists x2.
      apply approx_comp_ite_right. auto.
    * rewrite approx_denotation_while in H.
      apply IHx1 in H. destruct H. exists (S x2).
      rewrite approx_denotation_comp in H.
      rewrite approx_denotation_comp.
      unfold compose in *.
      rewrite approx_denotation_while.
      eapply approx_monotonic; [|apply H].
      intros. apply approximation. auto.
Qed.

Proposition approx_skip (n: nat) (S1: program):
  approx_denotation n S1 = approx_denotation n (comp skip S1).
apply functional_extensionality; intro.
rewrite approx_denotation_comp. unfold compose.
unfold approx_denotation at 3. destruct n; unfold id; auto.
Qed.

Lemma denotation_ite (T: test) (S1 S2: program):
  denotation (ite T S1 S2) = (fun X os => denotation (comp (assert T) S1) X os \/ denotation (comp (assert_not T) S2) X os).
apply functional_extensionality; intro X.
apply functional_extensionality; intro os.
apply propositional_extensionality. split; intro.
- unfold denotation in H. destruct H.
  rewrite approx_denotation_ite in H. destruct H.
  unfold cap_fail in H. destruct H.
  left. unfold denotation. exists x.
  rewrite approx_denotation_comp. unfold compose.
  rewrite H0. apply approx_fail. apply approx_fail. rewrite <- H0. auto.
  destruct H; [left|right].
  + unfold denotation. exists x.
    rewrite approx_denotation_comp. unfold compose.
    eapply approx_monotonic; [intros|apply H].
    unfold assert. rewrite approx_denotation_ite.
    unfold cap_state in H0. destruct H0.
    right. left.
    unfold approx_denotation; destruct x; unfold id; unfold cap_state; auto.
  + unfold denotation. exists x.
    rewrite approx_denotation_comp. unfold compose.
    eapply approx_monotonic; [intros|apply H].
    unfold assert_not. rewrite approx_denotation_ite.
    unfold cap_state in H0. destruct H0.
    right. right.
    unfold approx_denotation; destruct x; unfold id; unfold cap_state; auto.
- destruct H; unfold denotation in H; destruct H.
  unfold denotation; exists x.
  rewrite approx_skip in H.
  rewrite <- approx_assoc in H.
  rewrite approx_skip.
  apply approx_comp_ite_left. auto.
  unfold denotation; exists x.
  rewrite approx_skip in H.
  rewrite <- approx_assoc in H.
  rewrite approx_skip.
  apply approx_comp_ite_right. auto.
Qed.

Fixpoint loop_unroll (k: nat) (T: test) (S1: program): program :=
match k with
| O => diverge
| S k => ite T (comp S1 (loop_unroll k T S1)) skip
end.

Proposition iff_exists {T: Type} (P Q: T -> Prop):
  (forall x, P x <-> Q x) ->
  (exists x, P x) <-> (exists x, Q x).
intros. split; intro; destruct H0; exists x; apply H; auto.
Qed.

Proposition compose_id_left {T: Type} (f: T -> T):
  compose id f = f.
apply functional_extensionality; intro x.
unfold compose. unfold id. reflexivity.
Qed.

Lemma denotation_while (T: test) (S1: program):
  denotation (while T S1) = (fun X os => exists k, denotation (loop_unroll k T S1) X os).
apply functional_extensionality; intro X.
apply functional_extensionality; intro os.
apply propositional_extensionality.
split; intro.
- unfold denotation in H. destruct H.
  generalize dependent X. generalize dependent os.
  induction x; intros; simpl.
  unfold approx_denotation in H.
  exists 0. simpl. rewrite denotation_diverge. auto.
  rewrite approx_denotation_while in H.
  rewrite approx_denotation_ite in H. destruct H.
  exists 0. simpl. rewrite denotation_diverge. auto.
  destruct H.
  + rewrite approx_denotation_comp in H. unfold compose in H.
    apply IHx in H. destruct H. exists (S x0). simpl.
    rewrite denotation_ite. left.
    unfold denotation in H. destruct H.
    unfold denotation.
    apply approx_comp in H.
    exists (max x1 x).
    unfold assert.
    rewrite approx_denotation_comp. unfold compose.
    eapply approx_monotonic; [intros|apply H].
    rewrite approx_denotation_ite. right. left.
    unfold approx_denotation; destruct (max x1 x); unfold id; auto.
  + unfold approx_denotation in H; destruct x; unfold id in H; exists 1; simpl;
    unfold denotation; exists 0; rewrite approx_denotation_ite;
    right; right; unfold approx_denotation; unfold id; auto.
- destruct H.
  unfold denotation in H. destruct H.
  unfold denotation.
  generalize dependent X. generalize dependent os.
  induction x; intros.
  simpl in H. exists 0. simpl. unfold approx_denotation in H. destruct x0; auto.
  simpl in H. rewrite approx_denotation_ite in H. destruct H.
  exists 0. simpl. auto. destruct H.
  + rewrite approx_denotation_comp in H. unfold compose in H.
    apply IHx in H. destruct H.
    apply approx_comp in H.
    exists (S (max x1 x0)).
    rewrite approx_denotation_while.
    rewrite approx_denotation_ite. right. left. auto.
  + exists (S x0).
    rewrite approx_denotation_while.
    rewrite approx_denotation_ite. right. right. auto.
Qed.

Proposition denotation_while_compat (T: test) (S1 S2: program):
  denotation S1 = denotation S2 ->
  denotation (while T S1) = denotation (while T S2).
intro.
rewrite denotation_while.
rewrite denotation_while.
enough (forall k, denotation (loop_unroll k T S1) = denotation (loop_unroll k T S2)).
{ apply functional_extensionality; intro X.
apply functional_extensionality; intro os.
apply propositional_extensionality.
apply iff_exists. intro. rewrite H0. apply iff_refl. }
intros. induction k; simpl. reflexivity.
repeat rewrite denotation_ite.
repeat rewrite denotation_comp.
rewrite IHk. rewrite H. reflexivity.
Qed.

Lemma compositionality (S1 S2: program) (SC: context):
  denotation S1 = denotation S2 ->
  denotation (plug SC S1) = denotation (plug SC S2).
intro. induction SC; simpl.
- auto.
- rewrite denotation_comp.
  rewrite denotation_comp.
  rewrite IHSC. reflexivity.
- rewrite denotation_comp.
  rewrite denotation_comp.
  rewrite IHSC. reflexivity.
- rewrite denotation_ite.
  rewrite denotation_ite.
  rewrite denotation_comp.
  rewrite denotation_comp.
  rewrite denotation_comp.
  rewrite IHSC. reflexivity.
- rewrite denotation_ite.
  rewrite denotation_ite.
  rewrite denotation_comp.
  rewrite denotation_comp.
  rewrite denotation_comp.
  rewrite IHSC. reflexivity.
- apply denotation_while_compat. auto.
Qed.

Lemma full_abstraction (S1: program):
  bigstep_denotation S1 = denotation S1.
Admitted.

Lemma denotation_or (S: program) (X1 X2: resultset) (os: option state):
  denotation S (fun os : option state => X1 os \/ X2 os) os ->
  denotation S X1 os \/ denotation S X2 os.
intros. generalize dependent X1. generalize dependent X2. generalize dependent os. induction S; intros.
- rewrite denotation_oper in H.
  rewrite denotation_oper.
  admit.
- admit.
- admit.
- rewrite denotation_comp in H. unfold compose in H.
  rewrite denotation_comp. unfold compose.
  apply denotation_monotonic with (Y := fun os => denotation S1 X1 os \/ denotation S1 X2 os) in H.
  apply IHS2 in H. auto.
  intros. apply IHS1 in H0. auto.
- rewrite denotation_ite in H.
  destruct H.
  rewrite denotation_comp in H. unfold compose in H.
Admitted.

Lemma denotation_stateset_or (S: program) (X1 X2: stateset) (os: option state):
  denotation S (fun os : option state => exists s : state, os = Some s /\ (X1 s \/ X2 s)) os ->
  denotation S X1 os \/ denotation S X2 os.
intros.
apply denotation_monotonic with (Y := fun os : option state => (stateset_to_resultset X1) os \/ (stateset_to_resultset X2) os) in H.
apply denotation_or. auto.
intros. unfold stateset_to_resultset.
destruct H0. destruct H0. destruct H1.
left. exists x. tauto.
right. exists x. tauto.
Qed.

End AbstractSemantics.

Section AbstractHoare.

Variable state: Type.

Definition spec: Type := (state -> Prop) * program * (state -> Prop).

Inductive HS (Ax: spec -> Prop): spec -> Prop :=
| HS_axiom (pSq: spec): Ax pSq -> HS Ax pSq
| HS_skip (X: state -> Prop): HS Ax (X, skip, X)
| HS_diverge (X: state -> Prop): HS Ax (X, diverge, fun _ => False)
| HS_comp (X Y Z: state -> Prop) (S1 S2: program):
    HS Ax (X, S1, Y) -> HS Ax (Y, S2, Z) -> HS Ax (X, comp S1 S2, Z)
| HS_ite (X Y: state -> Prop) (T: test) (S1 S2: program):
    HS Ax (X, comp (assert T) S1, Y) -> HS Ax (X, comp (assert_not T) S2, Y) ->
    HS Ax (X, ite T S1 S2, Y)
| HS_while (X Y: state -> Prop) (T: test) (S: program):
    HS Ax (X, comp (assert T) S, X) -> HS Ax (X, assert_not T, Y) ->
    HS Ax (X, while T S, Y)
| HS_conseq (X X' Y Y': state -> Prop) (S: program):
    (forall x, X' x -> X x) -> (forall x, Y x -> Y' x) ->
    HS Ax (X, S, Y) -> HS Ax (X', S, Y').

Definition satisfied (M: machine_model state) (pSq: spec): Prop :=
match pSq with
| (X, S1, Y) => forall os, denotation M S1 (stateset_to_resultset X) os -> exists s, os = Some s /\ Y s
end.

Lemma HS_satisfied (M: machine_model state) (Ax: spec -> Prop) (pSq: spec):
  (forall pSq, Ax pSq -> satisfied M pSq) -> HS Ax pSq -> satisfied M pSq.
intros G H. induction H; simpl; intros.
- apply G. auto.
- rewrite denotation_skip in H. unfold id in H.
  unfold stateset_to_resultset in H. auto.
- rewrite denotation_diverge in H. unfold cap_fail in H.
  destruct H. unfold stateset_to_resultset in H. destruct H. destruct H.
  rewrite H in H0. inversion H0.
- unfold satisfied in IHHS1, IHHS2.
  rewrite denotation_comp in H1. unfold compose in H1.
  eapply denotation_monotonic in H1.
  apply IHHS2. apply H1.
  intros. apply IHHS1. auto.
- unfold satisfied in IHHS1, IHHS2.
  rewrite denotation_ite in H1. destruct H1.
  apply IHHS1 in H1. auto.
  apply IHHS2 in H1. auto.
- rename S into S1.
  rewrite denotation_while in H1. destruct H1. induction x.
  + simpl in H1. rewrite denotation_diverge in H1. unfold cap_fail in H1.
    destruct H1. unfold stateset_to_resultset in H1. destruct H1. destruct H1.
    rewrite H1 in H2. inversion H2.
  + simpl in H1. rewrite denotation_ite in H1. destruct H1.
    * rewrite <- denotation_assoc in H1.
      rewrite denotation_comp in H1. unfold compose in H1.
      unfold satisfied in IHHS1.
      eapply denotation_monotonic in H1. apply IHx. apply H1.
      intros. apply IHHS1 in H2. unfold stateset_to_resultset. auto.
    * unfold satisfied in IHHS2.
      rewrite denotation_comp in H1. unfold compose in H1.
      rewrite denotation_skip in H1. unfold id in H1.
      apply IHHS2 in H1. auto.
- unfold satisfied in IHHS.
  eapply denotation_monotonic in H2.
  apply IHHS in H2. destruct H2. destruct H2. exists x. constructor; auto.
  intros. unfold stateset_to_resultset in H3. unfold stateset_to_resultset.
  destruct H3. destruct H3. exists x. auto.
(*- unfold satisfied in IHX1, IHX2.
  pose proof H as G.
  eapply denotation_monotonic in H. apply IHX1 in H.
  eapply denotation_monotonic in G. apply IHX2 in G.
  destruct H. destruct G. assert (x = x0).
  enough (Some x = Some x0). inversion H1. reflexivity.
  destruct H. destruct H0. rewrite <- H. rewrite <- H0. reflexivity.
  exists x. constructor. destruct H; auto.
  destruct H; destruct H0; constructor; auto; rewrite H1; auto.
  intros. unfold stateset_to_resultset in H0. destruct H0.
  unfold stateset_to_resultset. exists x. tauto.
  intros. unfold stateset_to_resultset in H0. destruct H0.
  unfold stateset_to_resultset. exists x. tauto.
- unfold satisfied in IHX1, IHX2.
  unfold stateset_to_resultset in H.
  apply denotation_stateset_or in H. destruct H.
  eapply denotation_monotonic in H. apply IHX1 in H.
  destruct H. exists x. tauto. tauto.
  eapply denotation_monotonic in H. apply IHX2 in H.
  destruct H. exists x. tauto. tauto. *)
Qed.

Definition singleton (s: state): resultset :=
fun os => os = Some s.

Definition weakest_pre (M: machine_model state) (S1: program) (Y: state -> Prop): state -> Prop :=
fun p => exists q, Y q /\ denotation M S1 (singleton p) (Some q).

Inductive HS_weakest (M: machine_model state): spec -> Prop :=
| weakest_HS (pSq: spec): HS (HS_weakest M) pSq -> HS_weakest M pSq
| weakest_oper (o: op) (Y: state -> Prop): HS_weakest M (weakest_pre M (oper o) Y, oper o, Y).










