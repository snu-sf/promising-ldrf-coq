From sflib Require Import sflib.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Language.
From PromisingLib Require Import Loc.

Require Import Event.
Require Import Time.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.
Require Import Pred.
Require Import Trace.
Require Import Behavior.

Require Import MemoryProps.
Require Import Single.

Set Implicit Arguments.

Lemma semi_failure_machine_failure (c0: Configuration.t)
      tid lang st0 lc0 st1 lc1 st2 lc2 sc1 mem1 sc2 mem2 pf
      (WF: Configuration.wf c0)
      (TID: IdentMap.find tid (Configuration.threads c0) = Some (existT _ lang st0, lc0))
      (STEPS: rtc (@Thread.tau_step lang) (Thread.mk _ st0 lc0 (Configuration.sc c0) (Configuration.memory c0)) (Thread.mk _ st1 lc1 sc1 mem1))
      (STEP: Thread.step pf ThreadEvent.failure (Thread.mk _ st1 lc1 sc1 mem1) (Thread.mk _ st2 lc2 sc2 mem2))
  :
    exists c1 c2,
      (<<STEPS: rtc SConfiguration.tau_machine_step c0 c1>>) /\
      (<<STEP: SConfiguration.step ThreadEvent.failure tid c1 c2>>).
Proof.
  hexploit SConfiguration.multi_step_machine_step.
  { econs 1.
    { eapply TID. }
    { eapply STEPS. }
    { eapply STEP. }
  }
  { eauto. }
  i. des. inv STEP0. inv STEP1. destruct e; ss. eauto.
Qed.
