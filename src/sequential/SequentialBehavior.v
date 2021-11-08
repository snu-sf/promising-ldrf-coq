Require Import Bool.
Require Import RelationClasses.

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

Require Import Simple.

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
      (TRACE: SeqThread.writing_trace d tr_src w)
      (FLAG: Flags.le (Flags.join d f_tgt) (Flags.join w f_src))
    :
      le d ([], partial f_tgt) (tr_src, partial f_src)
  | le_ub
      d tr_src tr_tgt w
      (TRACE: SeqThread.writing_trace d tr_src w)
    :
      le d tr_tgt (tr_src, ub)
  | le_cons
      d0 d1 e i_src i_tgt o tr_src tr_tgt r_src r_tgt
      (LE: le d1 (tr_tgt, r_tgt) (tr_src, r_src))
      (MATCH: SeqEvent.input_match d0 d1 i_src i_tgt)
    :
      le d0 ((e, i_tgt, o)::tr_tgt, r_tgt) ((e, i_src, o)::tr_src, r_src)
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
    { econs 2.
      { eapply SeqThread.writing_trace_mon; eauto. }
      { etrans; eauto. eapply Flags.join_mon_l; eauto. }
    }
    { econs 3; eauto. eapply SeqThread.writing_trace_mon; eauto. }
    { econs 4.
      { eauto. }
      { eapply SeqEvent.input_match_mon; eauto. refl. }
    }
  Qed.

  Program Instance le_PreOrder: PreOrder (le Flags.bot).
  Next Obligation.
  Proof.
    ii. destruct x. induction l.
    { destruct r.
      { econs 1; refl. }
      { econs 2; eauto.
        { econs 1. }
        { refl. }
      }
      { econs 3; eauto. econs 1. }
    }
    { destruct a as [[e i] o]. econs 4; eauto.
      eapply SeqEvent.input_match_bot; eauto. }
  Qed.
  Next Obligation.
  Proof.
    ii. destruct z. ginduction l.
    { i. inv H0.
      { inv H. econs 1.
        { etrans; eauto. }
        { etrans; eauto. }
      }
      { inv TRACE. inv H. inv TRACE. econs 2.
        { econs. }
        { etrans; eauto. }
      }
      { econs 3. econs. }
    }
    { i.
  Admitted.

  Definition incl (b0: t -> Prop) (b1: t -> Prop): Prop :=
    forall tr0, b0 tr0 -> exists tr1, b1 tr1 /\ le Flags.bot tr0 tr1.

  Program Instance incl_PreOrder: PreOrder incl.
  Next Obligation.
  Proof.
    ii. exists tr0. split; auto. refl.
  Qed.
  Next Obligation.
  Proof.
    ii. apply H in H1. des. apply H0 in H1. des.
    esplits; eauto. etrans; eauto.
  Qed.
End SeqTrace.


Module SeqBehavior.
Section LANG.
  Variable lang: language.
  Variable state_step:
    Perms.t -> MachineEvent.t -> SeqState.t lang -> SeqState.t lang -> Prop.

  Inductive behavior: forall (th0: SeqThread.t lang) (tr: SeqTrace.t), Prop :=
  | behavior_term
      st v0 v1 f0 f1 p o
      (TERMINAL: lang.(Language.is_terminal) st)
      (VALUE: ValueMap.le v0 v1)
      (FLAG: Flags.le f0 f1)
    :
      behavior (SeqThread.mk (SeqState.mk _ st (SeqMemory.mk v1 f1)) p o) ([], SeqTrace.term v0 f0)
  | behavior_partial
      st v f0 f1 p o
      (FLAG: Flags.le f0 f1)
    :
      behavior (SeqThread.mk (SeqState.mk _ st (SeqMemory.mk v f1)) p o) ([], SeqTrace.partial f0)
  | behavior_ub
      st m p o tr r
      (FAILURE: SeqThread.failure state_step (SeqThread.mk (SeqState.mk _ st m) p o))
    :
      behavior (SeqThread.mk (SeqState.mk _ st m) p o) (tr, r)
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
  forall o p m (WF: Oracle.wf o),
    SeqTrace.incl
      (behavior (@SeqState.na_step _) (SeqThread.mk (SeqState.mk _ st_tgt m) p o))
      (behavior (@SeqState.na_step _) (SeqThread.mk (SeqState.mk _ st_src m) p o)) .
End SeqBehavior.


Section DETERMINISM.
  Variable lang: language.

  Definition similar (e0 e1: ProgramEvent.t): Prop :=
    e0 = e1 \/
    match e0, e1 with
    | ProgramEvent.read loc0 val0 ord0, ProgramEvent.write loc1 val1 ord1 =>
      loc0 = loc1 /\ ord0 = ord1
    | ProgramEvent.update loc0 valr0 valw0 ordr0 ordw0, ProgramEvent.update loc1 valr1 valw1 ordr1 ordw1 =>
      loc0 = loc1 /\ ordr0 = ordr1 /\ ordw0 = ordw1 /\ (valr0 = valr1 -> valw0 = valw1)
    | ProgramEvent.read loc0 val0 ord0, ProgramEvent.update loc1 valr1 valw1 ordr1 ordw1 =>
      loc0 = loc1 /\ val0 <> valr1
    | ProgramEvent.update loc0 valr0 valw0 ordr0 ordw0, ProgramEvent.read loc1 val1 ord1 =>
      loc0 = loc1 /\ valr0 <> val1
    | _, _ => False
    end.

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
  .

  Lemma deterministic_mon: monotone1 _deterministic.
  Proof.
    ii. inv IN. econs; eauto.
  Qed.
  Hint Resolve deterministic_mon: paco.

  Definition deterministic := paco1 _deterministic bot1.
End DETERMINISM.
#[export] Hint Resolve deterministic_mon: paco.


Section ADEQUACY.
  Variable lang_src lang_tgt: language.
  Variable state_step:
    Perms.t -> MachineEvent.t -> SeqState.t lang_src -> SeqState.t lang_src -> Prop.

  Hypothesis state_step_subset: state_step <4= (@SeqState.na_step _).

  Hypothesis state_step_determ:
    forall p st e0 e1 st0 st1
           (STEP0: state_step p e0 st st0)
           (STEP1: state_step p e1 st st1),
      e0 = e1 /\ st0 = st1.

  Theorem refinement_imply_simulation
          (st_src: lang_src.(Language.state)) (st_tgt: lang_tgt.(Language.state))
          (REFINE: SeqBehavior.refine _ _ st_tgt st_src)
          (DETERM: deterministic _ st_src)
          (TOP: forall o p m (WF: Oracle.wf o),
              SeqBehavior.behavior (@SeqState.na_step _) (SeqThread.mk (SeqState.mk _ st_src m) p o)
              <1=
              SeqBehavior.behavior state_step (SeqThread.mk (SeqState.mk _ st_src m) p o))
    :
      sim_seq_all _ _ (fun _ _ => True) st_src st_tgt.
  Proof.
  Admitted.
End ADEQUACY.
