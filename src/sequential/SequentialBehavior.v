Require Import Bool.
Require Import RelationClasses.
Require Import Program.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Language.
From PromisingLib Require Import Loc.

Require Import Event.
Require Import List.

Require Import SeqLib.
Require Import Sequential.
Require Import OracleFacts.

Require Import SeqAux.
Require Import SimAux.
Require Import SeqAux.

Set Implicit Arguments.


Module SeqTrace.
  Variant result: Type :=
  | term (v: ValueMap.t) (f: Flags.t)
  | partial (f: Flags.t)
  | ub
  .

  Definition t: Type := list (ProgramEvent.t * SeqEvent.input * Oracle.output) * result.

  Inductive le: Flags.t -> t -> t -> Prop :=
  | le_term
      d v_src v_tgt f_src f_tgt
      (VAL: ValueMap.le v_tgt v_src)
      (FLAG: Flags.le (Flags.join d f_tgt) f_src)
    :
      le d ([], term v_tgt f_tgt) ([], term v_src f_src)
  | le_partial
      d tr_src f_src f_tgt w
      (TRACE: SeqThread.writing_trace tr_src w)
      (FLAG: Flags.le (Flags.join d f_tgt) (Flags.join w f_src))
    :
      le d ([], partial f_tgt) (tr_src, partial f_src)
  | le_ub
      d tr_src tr_tgt w
      (TRACE: SeqThread.writing_trace tr_src w)
    :
      le d tr_tgt (tr_src, ub)
  | le_cons
      d0 d1 e_src e_tgt i_src i_tgt o tr_src tr_tgt r_src r_tgt
      (LE: le d1 (tr_tgt, r_tgt) (tr_src, r_src))
      (MATCH: SeqEvent.input_match d0 d1 i_src i_tgt)
      (EVENT: ProgramEvent.le e_tgt e_src)
    :
      le d0 ((e_tgt, i_tgt, o)::tr_tgt, r_tgt) ((e_src, i_src, o)::tr_src, r_src)
  .

  Lemma le_deferred_mon d0 d1 tr0 tr1
        (DEFERRED: Flags.le d0 d1)
        (LE: le d1 tr0 tr1)
    :
      le d0 tr0 tr1.
  Proof.
    induction LE.
    { econs 1; eauto. etrans; eauto.
      eapply Flags.join_mon_l. eauto. }
    { econs 2; eauto.
      etrans; eauto. eapply Flags.join_mon_l; eauto.
    }
    { econs 3; eauto. }
    { econs 4.
      { eauto. }
      { eapply SeqEvent.input_match_mon; eauto. refl. }
      { eauto. }
    }
  Qed.

  (* Program Instance le_PreOrder: PreOrder (le Flags.bot). *)
  (* Next Obligation. *)
  (* Proof. *)
  (*   ii. destruct x. induction l. *)
  (*   { destruct r. *)
  (*     { econs 1; refl. } *)
  (*     { econs 2; eauto. *)
  (*       { econs 1. } *)
  (*       { refl. } *)
  (*     } *)
  (*     { econs 3; eauto. econs 1. } *)
  (*   } *)
  (*   { destruct a as [[e i] o]. econs 4; eauto. *)
  (*     { eapply SeqEvent.input_match_bot; eauto. } *)
  (*     { refl. } *)
  (*   } *)
  (* Qed. *)
  (* Next Obligation. *)
  (* Proof. *)
  (*   ii. destruct z. ginduction l. *)
  (*   { i. inv H0. *)
  (*     { inv H. econs 1. *)
  (*       { etrans; eauto. } *)
  (*       { etrans; eauto. } *)
  (*     } *)
  (*     { inv TRACE. inv H. inv TRACE. econs 2. *)
  (*       { econs. } *)
  (*       { etrans; eauto. } *)
  (*     } *)
  (*     { econs 3. econs. } *)
  (*   } *)
  (*   { i. inv H0. *)
  (*     { inv H. econs 2; eauto. *)
  (*       inv TRACE0. etrans; eauto. *)
  (*     } *)
  (*     { econs; eauto. } *)
  (*     { inv H. *)
  (*       { inv LE. *)
  (*         { econs 2. *)

  Definition incl (b0: t -> Prop) (b1: t -> Prop): Prop :=
    forall tr0, b0 tr0 -> exists tr1, b1 tr1 /\ le Flags.bot tr0 tr1.

  (* Program Instance incl_PreOrder: PreOrder incl. *)
  (* Next Obligation. *)
  (* Proof. *)
  (*   ii. exists tr0. split; auto. refl. *)
  (* Qed. *)
  (* Next Obligation. *)
  (* Proof. *)
  (*   ii. apply H in H1. des. apply H0 in H1. des. *)
  (*   esplits; eauto. etrans; eauto. *)
  (* Qed. *)
End SeqTrace.


Module SeqBehavior.
Section LANG.
  Variable lang: language.
  Variable state_step:
    Perms.t -> MachineEvent.t -> SeqState.t lang -> SeqState.t lang -> Prop.

  Inductive behavior: forall (th0: SeqThread.t lang) (tr: SeqTrace.t), Prop :=
  | behavior_term
      st v f p o
      (TERMINAL: lang.(Language.is_terminal) st)
    :
      behavior (SeqThread.mk (SeqState.mk _ st (SeqMemory.mk v f)) p o) ([], SeqTrace.term v f)
  | behavior_partial
      st v f p o
    :
      behavior (SeqThread.mk (SeqState.mk _ st (SeqMemory.mk v f)) p o) ([], SeqTrace.partial f)
  | behavior_ub
      st m p o
      (FAILURE: SeqThread.failure state_step (SeqThread.mk (SeqState.mk _ st m) p o))
    :
      behavior (SeqThread.mk (SeqState.mk _ st m) p o) ([], SeqTrace.ub)
  | behavior_na_step
      th0 th1 tr
      (STEP: SeqThread.na_step state_step MachineEvent.silent th0 th1)
      (BEHAVIOR: behavior th1 tr)
    :
      behavior th0 tr
  | behavior_at_step
      e i o th0 th1 es st
      (STEP: SeqThread.at_step e i o th0 th1)
      (BEHAVIOR: behavior th1 (es, st))
    :
      behavior th0 ((e, i, o)::es, st)
  .
End LANG.

Definition refine
           (lang_tgt lang_src: language)
           (st_tgt: lang_tgt.(Language.state)) (st_src: lang_src.(Language.state))
  : Prop :=
  forall p m o (WF: Oracle.wf o),
    SeqTrace.incl
      (behavior (@SeqState.na_step _) (SeqThread.mk (SeqState.mk _ st_tgt m) p o))
      (behavior (@SeqState.na_step _) (SeqThread.mk (SeqState.mk _ st_src m) p o)).
End SeqBehavior.


Section DETERMINISM.
  Variable lang: language.

  Definition similar (e0 e1: ProgramEvent.t): Prop :=
    match e0, e1 with
    | ProgramEvent.read loc0 val0 ord0, ProgramEvent.read loc1 val1 ord1 =>
      loc0 = loc1 /\ ord0 = ord1
    | ProgramEvent.write loc0 val0 ord0, ProgramEvent.write loc1 val1 ord1 =>
      loc0 = loc1 /\ ord0 = ord1 /\ val0 = val1
    | ProgramEvent.update loc0 valr0 valw0 ordr0 ordw0, ProgramEvent.update loc1 valr1 valw1 ordr1 ordw1 =>
      loc0 = loc1 /\ ordr0 = ordr1 /\ ordw0 = ordw1 /\ (valr0 = valr1 -> valw0 = valw1)
    | ProgramEvent.read loc0 val0 ord0, ProgramEvent.update loc1 valr1 valw1 ordr1 ordw1 =>
      loc0 = loc1 /\ ord0 = ordr1 /\ val0 <> valr1
    | ProgramEvent.update loc0 valr0 valw0 ordr0 ordw0, ProgramEvent.read loc1 val1 ord1 =>
      loc0 = loc1 /\ ordr0 = ord1 /\ valr0 <> val1
    | ProgramEvent.fence ordr0 ordw0, ProgramEvent.fence ordr1 ordw1 =>
      ordr0 = ordr1 /\ ordw0 = ordw1
    | _, _ => e0 = e1
    end.

  Lemma similar_le_eq
        e1 e2 e
        (SIMILAR: similar e1 e2)
        (LE1: ProgramEvent.le e e1)
        (LE2: ProgramEvent.le e e2):
    e1 = e2.
  Proof.
    destruct e1, e2, e; ss.
    - inv LE1. inv LE2. ss.
    - des. subst. ss.
    - des. subst. exploit SIMILAR2; eauto. i. subst. ss.
    - inv LE1. inv LE2. ss.
  Qed.

  Variant _deterministic (deterministic: lang.(Language.state) -> Prop) (st0: lang.(Language.state)): Prop :=
  | deterministic_intro
      (PRESERVE:
         forall e st1 (STEP: lang.(Language.step) e st0 st1),
           deterministic st1)
      (STEP_TERMINAL:
         forall e st1 (STEP: lang.(Language.step) e st0 st1)
                (TERMINAL: lang.(Language.is_terminal) st0), False)
      (STEP_STEP:
         forall e1 st1 (STEP1: lang.(Language.step) e1 st0 st1)
                e2 st2 (STEP2: lang.(Language.step) e2 st0 st2),
           similar e1 e2 /\ (e1 = e2 -> st1 = st2))
      (NO_NA_UPDATE:
         forall loc valr valw ordr ordw st1
           (STEP: lang.(Language.step) (ProgramEvent.update loc valr valw ordr ordw) st0 st1),
           Ordering.le Ordering.plain ordr /\ Ordering.le Ordering.plain ordw)
  .

  Lemma deterministic_mon: monotone1 _deterministic.
  Proof.
    ii. inv IN. econs; eauto.
  Qed.
  Hint Resolve deterministic_mon: paco.

  Definition deterministic := paco1 _deterministic bot1.
End DETERMINISM.
#[export] Hint Resolve deterministic_mon: paco.

Lemma deterministic_step
      lang e1 e2 st st1 st2
      (DETERM: deterministic lang st)
      (STEP1: lang.(Language.step) e1 st st1)
      (STEP2: lang.(Language.step) e2 st st2):
  similar e1 e2 /\ (e1 = e2 -> st1 = st2).
Proof.
  punfold DETERM. inv DETERM. eauto.
Qed.

Lemma deterministic_terminal
      lang e st1 st2
      (DETERM: deterministic lang st1)
      (STEP: lang.(Language.step) e st1 st2)
      (TERMINAL: lang.(Language.is_terminal) st1):
  False.
Proof.
  punfold DETERM. inv DETERM. eauto.
Qed.

Lemma step_deterministic
      lang e st0 st1
      (DETERM: deterministic lang st0)
      (STEP: lang.(Language.step) e st0 st1):
  deterministic lang st1.
Proof.
  punfold DETERM. inv DETERM.
  exploit PRESERVE; eauto. i. inv x; done.
Qed.


Section RECEPTIVE.
  Variable lang: language.

  Variant _receptive (receptive: lang.(Language.state) -> Prop) (st0: lang.(Language.state)): Prop :=
  | receptive_intro
      (PRESERVE:
         forall e st1 (STEP: lang.(Language.step) e st0 st1),
           receptive st1)
      (READ:
         forall loc val ord st1
           (STEP: lang.(Language.step) (ProgramEvent.read loc val ord) st0 st1),
         forall val',
           (exists st1', lang.(Language.step) (ProgramEvent.read loc val' ord) st0 st1') \/
           (exists valw ordw st1',
               lang.(Language.step) (ProgramEvent.update loc val' valw ord ordw) st0 st1'))
      (UPDATE:
         forall loc valr valw ordr ordw st1
           (STEP: lang.(Language.step) (ProgramEvent.update loc valr valw ordr ordw) st0 st1),
         forall val',
           (exists st1', lang.(Language.step) (ProgramEvent.read loc val' ordr) st0 st1') \/
           (exists valw' st1',
               lang.(Language.step) (ProgramEvent.update loc val' valw' ordr ordw) st0 st1'))
      (NO_NA_UPDATE:
         forall loc valr valw ordr ordw st1
           (STEP: lang.(Language.step) (ProgramEvent.update loc valr valw ordr ordw) st0 st1),
           Ordering.le Ordering.plain ordr /\ Ordering.le Ordering.plain ordw)
  .

  Lemma receptive_mon: monotone1 _receptive.
  Proof.
    ii. inv IN. econs; eauto.
  Qed.
  Hint Resolve receptive_mon: paco.

  Definition receptive := paco1 _receptive bot1.
End RECEPTIVE.
#[export] Hint Resolve receptive_mon: paco.

Definition wsimilar (e0 e1: ProgramEvent.t): Prop :=
  match e0, e1 with
  | ProgramEvent.read loc0 val0 ord0, ProgramEvent.read loc1 val1 ord1 =>
    loc0 = loc1 /\ ord0 = ord1
  | ProgramEvent.write loc0 val0 ord0, ProgramEvent.write loc1 val1 ord1 =>
    loc0 = loc1 /\ ord0 = ord1 /\ val0 = val1
  | ProgramEvent.update loc0 valr0 valw0 ordr0 ordw0, ProgramEvent.update loc1 valr1 valw1 ordr1 ordw1 =>
    loc0 = loc1 /\ ordr0 = ordr1 /\ ordw0 = ordw1
  | ProgramEvent.read loc0 val0 ord0, ProgramEvent.update loc1 valr1 valw1 ordr1 ordw1 =>
    loc0 = loc1 /\ ord0 = ordr1
  | ProgramEvent.update loc0 valr0 valw0 ordr0 ordw0, ProgramEvent.read loc1 val1 ord1 =>
    loc0 = loc1 /\ ordr0 = ord1
  | ProgramEvent.fence ordr0 ordw0, ProgramEvent.fence ordr1 ordw1 =>
    ordr0 = ordr1 /\ ordw0 = ordw1
  | _, _ => e0 = e1
  end.

Lemma similar_wsimilar
      e1 e2
      (SIMILAR: similar e1 e2):
  wsimilar e1 e2.
Proof.
  destruct e1, e2; ss; des; subst; ss.
Qed.

Lemma receptive_oracle_progress
      lang e st1 st2
      orc1
      (RECEPTIVE: receptive _ st1)
      (ORACLE: Oracle.wf orc1)
      (STEP: lang.(Language.step) e st1 st2)
      (ATOMIC: is_atomic_event e):
  exists e' st2',
    (<<EVENT: wsimilar e e'>>) /\
    (<<STEP: lang.(Language.step) e' st1 st2'>>) /\
    (<<ATOMIC: is_atomic_event e'>>) /\
    (<<PROGRESS: Oracle.progress e' orc1>>).
Proof.
  punfold RECEPTIVE. inv RECEPTIVE.
  punfold ORACLE. inv ORACLE.
  destruct e; ss.
  - specialize (LOAD loc ord). des.
    exploit READ; eauto. i. des.
    + esplits; eauto. ss.
    + exploit NO_NA_UPDATE; eauto. i. des.
      esplits; eauto; ss.
      destruct ord, ordw; ss.
  - specialize (STORE loc ord val).
    esplits; try exact STORE; eauto. ss.
  - specialize (LOAD loc ordr). des.
    exploit UPDATE; eauto. i. des.
    + esplits; eauto. ss. destruct ordr; ss.
    + exploit NO_NA_UPDATE; eauto. i. des.
      esplits; eauto; ss.
  - specialize (FENCE ordr ordw).
    esplits; try exact FENCE; eauto. ss.
  - esplits; try apply SYSCALL; eauto.
Qed.

Lemma step_receptive
      lang e st1 st2
      (RECEPTIVE: receptive lang st1)
      (STEP: lang.(Language.step) e st1 st2):
  receptive _ st2.
Proof.
  punfold RECEPTIVE. inv RECEPTIVE.
  exploit PRESERVE; eauto. i. inv x; ss.
Qed.
