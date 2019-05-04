Require Import RelationClasses.

Require Import sflib.
From Paco Require Import paco.

Require Import Axioms.
Require Import Basic.
Require Import DataStructure.
Require Import DenseOrder.
Require Import Event.
Require Import Time.
Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import MemoryFacts.
Require Import TView.
Require Import Local.
Require Import Thread.

Set Implicit Arguments.


Lemma concrete_promise_step
      lc1 mem1 loc from to msg lc2 mem2 kind
      mem1'
      (CLOSED1: Memory.closed mem1)
      (WF1: Local.wf lc1 mem1)
      (STEP: Local.promise_step lc1 mem1 loc from to msg lc2 mem2 kind)
      (WF1': Local.wf lc1 mem1')
      (CONCRETE1: Memory.concrete mem1 mem1'):
  exists mem2',
    <<STEP': Local.promise_step lc1 mem1' loc from to msg lc2 mem2' kind>> /\
    <<CONCRETE2: Memory.concrete mem2 mem2'>>.
Proof.
  inv WF1. inv WF1'. inv STEP.
  exploit Memory.concrete_promise_exists; try exact PROMISE; eauto. i. des.
  esplits; eauto. econs; eauto.
  eapply Memory.concrete_closed_message; eauto.
Qed.

Lemma concrete_read_step
      lc1 mem1 loc ts val released ord lc2
      mem1'
      (STEP: Local.read_step lc1 mem1 loc ts val released ord lc2)
      (CONCRETE1: Memory.concrete mem1 mem1'):
  <<STEP': Local.read_step lc1 mem1' loc ts val released ord lc2>>.
Proof.
  inv CONCRETE1. inv STEP.
  exploit SOUND; eauto. i. des; ss.
  esplits; eauto.
Qed.

Lemma concrete_write_step
      lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind
      mem1'
      (CLOSED1: Memory.closed mem1)
      (WF1: Local.wf lc1 mem1)
      (WF1': Local.wf lc1 mem1')
      (CONCRETE1: Memory.concrete mem1 mem1')
      (STEP: Local.write_step lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind):
  exists mem2',
    <<STEP': Local.write_step lc1 sc1 mem1' loc from to val releasedm released ord lc2 sc2 mem2' kind>> /\
    <<CONCRETE2: Memory.concrete mem2 mem2'>>.
Proof.
  inv WF1. inv WF1'. inv STEP. inv WRITE.
  exploit Memory.concrete_promise_exists; try exact PROMISE; eauto. i. des.
  esplits; eauto.
Qed.

Lemma concrete_program_step
      e lc1 sc1 mem1 lc2 sc2 mem2
      mem1'
      (CLOSED1: Memory.closed mem1)
      (WF1: Local.wf lc1 mem1)
      (WF1': Local.wf lc1 mem1')
      (CONCRETE1: Memory.concrete mem1 mem1')
      (STEP: Local.program_step e lc1 sc1 mem1 lc2 sc2 mem2):
  exists mem2',
    <<STEP': Local.program_step e lc1 sc1 mem1' lc2 sc2 mem2'>> /\
    <<CONCRETE2: Memory.concrete mem2 mem2'>>.
Proof.
  inv STEP.
  - esplits; eauto.
  - exploit concrete_read_step; eauto.
  - exploit concrete_write_step; eauto. i. des.
    esplits; eauto.
  - exploit Memory.concrete_closed; eauto. i.
    exploit concrete_read_step; eauto. i. des.
    exploit Local.read_step_future; try exact LOCAL1; eauto. i. des.
    exploit Local.read_step_future; try exact x0; eauto. i. des.
    exploit concrete_write_step; try exact LOCAL2; eauto. i. des.
    esplits; eauto.
  - esplits; eauto.
  - esplits; eauto.
Qed.

Lemma concrete_thread_promise_step
      lang pf e e1 e2
      mem1'
      (CLOSED1: Memory.closed e1.(Thread.memory))
      (WF1: Local.wf e1.(Thread.local) e1.(Thread.memory))
      (WF1': Local.wf e1.(Thread.local) mem1')
      (CONCRETE1: Memory.concrete e1.(Thread.memory) mem1')
      (STEP: Thread.promise_step pf e e1 e2):
  exists mem2',
    <<STEP': Thread.promise_step pf e
                                 (Thread.mk lang e1.(Thread.state) e1.(Thread.local) e1.(Thread.sc) mem1')
                                 (Thread.mk lang e2.(Thread.state) e2.(Thread.local) e2.(Thread.sc) mem2')>> /\
    <<CONCRETE2: Memory.concrete e2.(Thread.memory) mem2'>>.
Proof.
  destruct e1. destruct e2. ss. inv STEP.
  exploit concrete_promise_step; eauto. i. des.
  esplits; eauto. econs; eauto.
Qed.

Lemma concrete_thread_program_step
      lang e e1 e2
      mem1'
      (CLOSED1: Memory.closed e1.(Thread.memory))
      (WF1: Local.wf e1.(Thread.local) e1.(Thread.memory))
      (WF1': Local.wf e1.(Thread.local) mem1')
      (CONCRETE1: Memory.concrete e1.(Thread.memory) mem1')
      (STEP: Thread.program_step e e1 e2):
  exists mem2',
    <<STEP': Thread.program_step e
                                 (Thread.mk lang e1.(Thread.state) e1.(Thread.local) e1.(Thread.sc) mem1')
                                 (Thread.mk lang e2.(Thread.state) e2.(Thread.local) e2.(Thread.sc) mem2')>> /\
    <<CONCRETE2: Memory.concrete e2.(Thread.memory) mem2'>>.
Proof.
  destruct e1. destruct e2. ss. inv STEP.
  exploit concrete_program_step; eauto. i. des.
  esplits; eauto. econs; eauto.
Qed.

Lemma concrete_thread_step
      lang pf e e1 e2
      mem1'
      (CLOSED1: Memory.closed e1.(Thread.memory))
      (WF1: Local.wf e1.(Thread.local) e1.(Thread.memory))
      (WF1': Local.wf e1.(Thread.local) mem1')
      (CONCRETE1: Memory.concrete e1.(Thread.memory) mem1')
      (STEP: Thread.step pf e e1 e2):
  exists mem2',
    <<STEP': Thread.step pf e
                         (Thread.mk lang e1.(Thread.state) e1.(Thread.local) e1.(Thread.sc) mem1')
                         (Thread.mk lang e2.(Thread.state) e2.(Thread.local) e2.(Thread.sc) mem2')>> /\
    <<CONCRETE2: Memory.concrete e2.(Thread.memory) mem2'>>.
Proof.
  inv STEP.
  - exploit concrete_thread_promise_step; eauto. i. des.
    esplits; eauto. econs 1. eauto.
  - exploit concrete_thread_program_step; eauto. i. des.
    esplits; eauto. econs 2. eauto.
Qed.

Lemma concrete_thread_opt_step
      lang e e1 e2
      mem1'
      (CLOSED1: Memory.closed e1.(Thread.memory))
      (WF1: Local.wf e1.(Thread.local) e1.(Thread.memory))
      (WF1': Local.wf e1.(Thread.local) mem1')
      (CONCRETE1: Memory.concrete e1.(Thread.memory) mem1')
      (STEP: Thread.opt_step e e1 e2):
  exists mem2',
    <<STEP': Thread.opt_step e
                             (Thread.mk lang e1.(Thread.state) e1.(Thread.local) e1.(Thread.sc) mem1')
                             (Thread.mk lang e2.(Thread.state) e2.(Thread.local) e2.(Thread.sc) mem2')>> /\
    <<CONCRETE2: Memory.concrete e2.(Thread.memory) mem2'>>.
Proof.
  inv STEP.
  - esplits; eauto. econs 1; eauto.
  - exploit concrete_thread_step; eauto. i. des.
    esplits; eauto. econs 2; eauto.
Qed.

Lemma concrete_thread_rtc_all_step
      lang e1 e2
      mem1'
      (CLOSED1: Memory.closed e1.(Thread.memory))
      (WF1: Local.wf e1.(Thread.local) e1.(Thread.memory))
      (WF1': Local.wf e1.(Thread.local) mem1')
      (SC1: Memory.closed_timemap e1.(Thread.sc) e1.(Thread.memory))
      (CONCRETE1: Memory.concrete e1.(Thread.memory) mem1')
      (STEP: rtc (@Thread.all_step _) e1 e2):
  exists mem2',
    <<STEP': rtc (@Thread.all_step _)
                 (Thread.mk lang e1.(Thread.state) e1.(Thread.local) e1.(Thread.sc) mem1')
                 (Thread.mk lang e2.(Thread.state) e2.(Thread.local) e2.(Thread.sc) mem2')>> /\
    <<CONCRETE2: Memory.concrete e2.(Thread.memory) mem2'>>.
Proof.
  revert mem1' CLOSED1 WF1 WF1' SC1 CONCRETE1. induction STEP; i.
  - esplits; eauto.
  - inv H. inv USTEP.
    exploit concrete_thread_step; eauto. i. des.
    exploit Thread.step_future; try exact STEP0; eauto. i. des.
    exploit Thread.step_future; try exact STEP'; eauto; s.
    { eapply Memory.concrete_closed_timemap; eauto. }
    { eapply Memory.concrete_closed; eauto. }
    i. des.
    exploit IHSTEP; try exact CONCRETE2; eauto. i. des.
    esplits; eauto. econs; eauto. econs. econs. eauto.
Qed.

Lemma concrete_thread_rtc_tau_step
      lang e1 e2
      mem1'
      (CLOSED1: Memory.closed e1.(Thread.memory))
      (WF1: Local.wf e1.(Thread.local) e1.(Thread.memory))
      (WF1': Local.wf e1.(Thread.local) mem1')
      (SC1: Memory.closed_timemap e1.(Thread.sc) e1.(Thread.memory))
      (CONCRETE1: Memory.concrete e1.(Thread.memory) mem1')
      (STEP: rtc (@Thread.tau_step _) e1 e2):
  exists mem2',
    <<STEP': rtc (@Thread.tau_step _)
                 (Thread.mk lang e1.(Thread.state) e1.(Thread.local) e1.(Thread.sc) mem1')
                 (Thread.mk lang e2.(Thread.state) e2.(Thread.local) e2.(Thread.sc) mem2')>> /\
    <<CONCRETE2: Memory.concrete e2.(Thread.memory) mem2'>>.
Proof.
  revert mem1' CLOSED1 WF1 WF1' SC1 CONCRETE1. induction STEP; i.
  - esplits; eauto.
  - inv H. inv TSTEP.
    exploit concrete_thread_step; eauto. i. des.
    exploit Thread.step_future; try exact STEP0; eauto. i. des.
    exploit Thread.step_future; try exact STEP'; eauto; s.
    { eapply Memory.concrete_closed_timemap; eauto. }
    { eapply Memory.concrete_closed; eauto. }
    i. des.
    exploit IHSTEP; try exact CONCRETE2; eauto. i. des.
    esplits; eauto. econs; eauto. econs; eauto. econs. eauto.
Qed.
