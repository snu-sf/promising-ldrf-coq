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

Require Import SequentialDef.

Set Implicit Arguments.

Program Instance option_rel_PreOrder A R `{@PreOrder A R}: PreOrder (option_rel R).
Next Obligation.
Proof.
  ii. destruct x; ss. refl.
Qed.
Next Obligation.
Proof.
  ii. destruct x, y, z; ss. etrans; eauto.
Qed.


Module SeqTrace.
  Variant output: Type :=
  | term (m: SeqMemory.t)
  | partial (f: Flags.t)
  | ub
  .

  Definition t: Type := list (ProgramEvent.t * SeqEvent.input * SeqEvent.output) * output.

  Variant le: t -> t -> Prop :=
  | le_term
      es m_src m_tgt
      (MEMORY: SeqMemory.le m_tgt m_src)
    :
      le (es, term m_tgt) (es, term m_src)
  | le_pterm
      es_src es_tgt f_src f_tgt
      (EVENTS: exists es, es_tgt = es_src ++ es)
      (FLAGS: Flags.le f_tgt f_src)
    :
      le (es_tgt, partial f_tgt) (es_src, partial f_src)
  | le_ub
      es tr_tgt
    :
      le tr_tgt (es, ub)
  .

  Program Instance le_PreOrder: PreOrder le.
  Next Obligation.
  Proof.
    ii. destruct x as [? []].
    { econs. refl. }
    { econs 2; [|refl]. exists [].
      rewrite app_nil_r. auto. }
    { econs 3. }
  Qed.
  Next Obligation.
  Proof.
    ii. inv H; inv H0.
    { econs 1; eauto. etrans; eauto. }
    { econs 3. }
    { des; subst. econs 2.
      { eexists. rewrite app_assoc. eauto. }
      { etrans; eauto. }
    }
    { econs 3. }
    { econs 3. }
  Qed.

  Definition incl (b0: t -> Prop) (b1: t -> Prop): Prop :=
    forall tr0, b0 tr0 -> exists tr1, b1 tr1 /\ le tr0 tr1.

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

  Inductive behavior: forall (th0: SeqThread.t lang) (tr: SeqTrace.t), Prop :=
  | behavior_term
      st m p o
      (TERMINAL: lang.(Language.is_terminal) st)
    :
      behavior (SeqThread.mk (SeqState.mk _ st m) p o) ([], SeqTrace.term m)
  | behavior_partial
      st m p o
    :
      behavior (SeqThread.mk (SeqState.mk _ st m) p o) ([], SeqTrace.partial (SeqMemory.flags m))
  | behavior_ub
      st m p o
      (FAILURE: SeqThread.failure (SeqThread.mk (SeqState.mk _ st m) p o))
    :
      behavior (SeqThread.mk (SeqState.mk _ st m) p o) ([], SeqTrace.ub)
  | behavior_na_step
      th0 th1 tr
      (STEP: SeqThread.na_step MachineEvent.silent th0 th1)
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
      (behavior (SeqThread.mk (SeqState.mk _ st_tgt m) p o))
      (behavior (SeqThread.mk (SeqState.mk _ st_src m) p o)) .
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

  Theorem refinement_imply_simulation
          (st_src: lang_src.(Language.state)) (st_tgt: lang_tgt.(Language.state))
          (DETERM: deterministic _ st_src)
          (REFINE: SeqBehavior.refine _ _ st_tgt st_src)
    :
      sim_seq_all _ _ (fun _ _ => True) st_src st_tgt.
  Proof.
  Admitted.
End ADEQUACY.
