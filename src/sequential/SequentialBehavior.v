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
    { econs 2.
      { eapply SeqThread.writing_trace_mon; eauto. }
      { etrans; eauto. eapply Flags.join_mon_l; eauto. }
    }
    { econs 3; eauto. eapply SeqThread.writing_trace_mon; eauto. }
    { econs 4.
      { eauto. }
      { eapply SeqEvent.input_match_mon; eauto. refl. }
      { eauto. }
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
      { eapply SeqEvent.input_match_bot; eauto. }
      { refl. }
    }
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
      st v f p o
      (TERMINAL: lang.(Language.is_terminal) st)
    :
      behavior (SeqThread.mk (SeqState.mk _ st (SeqMemory.mk v f)) p o) ([], SeqTrace.term v f)
  | behavior_partial
      st v f p o
    :
      behavior (SeqThread.mk (SeqState.mk _ st (SeqMemory.mk v f)) p o) ([], SeqTrace.partial f)
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
      loc0 = loc1 /\ val0 <> valr1
    | ProgramEvent.update loc0 valr0 valw0 ordr0 ordw0, ProgramEvent.read loc1 val1 ord1 =>
      loc0 = loc1 /\ valr0 <> val1
    | ProgramEvent.fence ordr0 ordw0, ProgramEvent.fence ordr1 ordw1 =>
      ordr0 = ordr1 /\ ordw0 = ordw1
    | ProgramEvent.syscall e0, ProgramEvent.syscall e1 =>
      e0 = e1
    | _, _ => True
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

  Lemma refine_mon
        (st_tgt: lang_tgt.(Language.state)) (st_src: lang_src.(Language.state))
        (REFINE: SeqBehavior.refine _ _ st_tgt st_src)
        (TOP: forall p m o (WF: Oracle.wf o),
            SeqBehavior.behavior (@SeqState.na_step _) (SeqThread.mk (SeqState.mk _ st_src m) p o)
            <1=
            SeqBehavior.behavior state_step (SeqThread.mk (SeqState.mk _ st_src m) p o)):
    forall p m o (WF: Oracle.wf o),
      SeqTrace.incl
        (SeqBehavior.behavior (@SeqState.na_step _) (SeqThread.mk (SeqState.mk _ st_tgt m) p o))
        (SeqBehavior.behavior state_step (SeqThread.mk (SeqState.mk _ st_src m) p o)).
  Proof.
    ii. specialize (TOP p m o WF).
    exploit REFINE; eauto. i. des. eauto.
  Qed.

  Inductive state_steps (lang: language)
                        (step: forall (p: Perms.t) (e: MachineEvent.t) (st1 st2: SeqState.t lang), Prop):
    forall (tr: list (ProgramEvent.t * SeqEvent.input * Oracle.output))
      (st1 st2: SeqState.t lang) (p1 p2: Perms.t), Prop :=
  | state_steps_refl
      st p:
      state_steps step [] st st p p
  | state_steps_na_step
      tr st1 st2 st3 p1 p2
      (STEPS: state_steps step tr st1 st2 p1 p2)
      (STEP: step p2 MachineEvent.silent st2 st3):
      state_steps step tr st1 st3 p1 p2
  | state_steps_at_step
      tr st1 st2 p1 p2
      e i o st3 mem3 p3
      (STEPS: state_steps step tr st1 st2 p1 p2)
      (LSTEP: lang.(Language.step) e st2.(SeqState.state) st3)
      (ESTEP: SeqEvent.step i o p2 st2.(SeqState.memory) p3 mem3):
      state_steps step (tr ++ [(e, i, o)]) st1 (SeqState.mk _ st3 mem3) p1 p3
  .

  Inductive match_traces: forall (d: Flags.t) (tr_src tr_tgt: list (ProgramEvent.t * SeqEvent.input * Oracle.output)), Prop :=
  | match_traces_nil:
      match_traces Flags.bot [] []
  | match_traces_cons
      d1 tr_src tr_tgt d2
      e_src i_src o_src
      e_tgt i_tgt o_tgt
      (MATCH: match_traces d1 tr_src tr_tgt)
      (EVENT: ProgramEvent.le e_src e_tgt)
      (INPUT: SeqEvent.input_match d1 d2 i_src i_tgt)
      (OUTPUT: o_src = o_tgt):
      match_traces d2 (tr_src ++ [(e_src, i_src, o_src)]) (tr_tgt ++ [(e_tgt, i_tgt, o_tgt)])
  .

  Definition oracle_simple_output (i: Oracle.input): Oracle.output :=
    let 'Oracle.mk_input acc acq rel := i in
    Oracle.mk_output
      (if is_some acc then Some (Perm.low, Const.undef) else None)
      (if is_some acq then Some (fun _ => Perm.low, fun _ => Const.undef) else None)
      (if is_some rel then Some (fun _ => Perm.low) else None).

  Definition oracle_similar_input (i1 i2: Oracle.input): bool :=
    andb (eqb (is_some i1.(Oracle.in_access)) (is_some i2.(Oracle.in_access)))
         (andb (eqb (is_some i1.(Oracle.in_acquire)) (is_some i2.(Oracle.in_acquire)))
               (eqb (is_some i1.(Oracle.in_release)) (is_some i2.(Oracle.in_release)))).

  Definition oracle_output_of_event
             (i: Oracle.input) (o: Oracle.output) (i_src: Oracle.input): Oracle.output :=
    if oracle_similar_input i i_src
    then o
    else oracle_simple_output i_src.

  Variant oracle_step_of_event (i: Oracle.input) (o: Oracle.output) (orc: Oracle.t):
    forall (pe: ProgramEvent.t) (i: Oracle.input) (o: Oracle.output) (orc0 orc1: option orc.(Oracle._t)), Prop :=
  | oracle_step_of_event_None
      pe i_src:
      oracle_step_of_event i o orc pe i_src (oracle_output_of_event i o i_src)
                           None (Some orc.(Oracle._o))
  | oracle_step_of_event_Some
      pe i_src o_src orc0 orc1
      (STEP: orc.(Oracle._step) pe i_src o_src orc0 orc1):
      oracle_step_of_event i o orc pe i_src o_src (Some orc0) (Some orc1)
  .

  Definition oracle_of_event (i: Oracle.input) (o: Oracle.output) (orc: Oracle.t): Oracle.t :=
    Oracle.mk (oracle_step_of_event i o orc) None.

  Fixpoint oracle_of_trace
           (tr: list (ProgramEvent.t * SeqEvent.input * Oracle.output)) (orc: Oracle.t): Oracle.t :=
    match tr with
    | [] => orc
    | (_, i, o) :: tr =>
      oracle_of_event (SeqEvent.get_oracle_input i) o (oracle_of_trace tr orc)
    end.

  Lemma refinement_implies_simulation_aux
        (st_src: lang_src.(Language.state)) (st_tgt: lang_tgt.(Language.state))
        (REFINE: forall p m o (WF: Oracle.wf o),
            SeqTrace.incl
              (SeqBehavior.behavior (@SeqState.na_step _) (SeqThread.mk (SeqState.mk _ st_tgt m) p o))
              (SeqBehavior.behavior state_step (SeqThread.mk (SeqState.mk _ st_src m) p o)))
        (DETERM: deterministic _ st_src)
        p m p1 d
        tr_src st1_src
        tr_tgt st1_tgt
        (STEPS_SRC: state_steps state_step tr_src (SeqState.mk _ st_src m) st1_src p p1)
        (STEPS_TGT: state_steps (@SeqState.na_step lang_tgt) tr_tgt (SeqState.mk _ st_tgt m) st1_tgt p p1)
        (TRACES: match_traces d tr_src tr_tgt):
      sim_seq (fun _ _ => True) p1 d st1_src st1_tgt.
  Proof.
    specialize (REFINE p m).
    revert p1 d tr_src st1_src tr_tgt st1_tgt STEPS_SRC STEPS_TGT TRACES.
    pcofix CIH. i. pfold.
    destruct (classic (sim_seq_failure_case p1 d st1_src)).
    { econs 2; eauto. }

    econs.
    { (* terminal *)
      admit.
    }

    { (* na step *)
      ii. destruct e.
      { esplits; eauto; try by econs 2.
        right. eapply CIH; eauto.
        econs 2; eauto.
      }
      { inv STEP_TGT. inv LOCAL; ss. destruct (p1 loc); ss. }
      admit.
    }

    { (* at step *)
      admit.
    }

    { (* partial *)
      admit.
    }
  Admitted.

  Theorem refinement_implies_simulation
          (st_src: lang_src.(Language.state)) (st_tgt: lang_tgt.(Language.state))
          (REFINE: SeqBehavior.refine _ _ st_tgt st_src)
          (DETERM: deterministic _ st_src)
          (TOP: forall p m o (WF: Oracle.wf o),
              SeqBehavior.behavior (@SeqState.na_step _) (SeqThread.mk (SeqState.mk _ st_src m) p o)
              <1=
              SeqBehavior.behavior state_step (SeqThread.mk (SeqState.mk _ st_src m) p o))
    :
      sim_seq_all _ _ (fun _ _ => True) st_src st_tgt.
  Proof.
    ii. eapply refinement_implies_simulation_aux; eauto; try by econs 1.
    ii. exploit REFINE; eauto. i. des. eauto.
  Qed.
End ADEQUACY.
