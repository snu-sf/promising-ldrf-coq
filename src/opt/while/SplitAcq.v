From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Basic.
From PromisingLib Require Import Loc.
From PromisingLib Require Import Language.

Require Import Event.
Require Import Time.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.

Require Import FulfillStep.

Require Import SimMemory.
Require Import SimPromises.
Require Import SimLocal.
Require Import SimThread.
Require Import Compatibility.
Require Import SplitAcqCommon.

Require Import Syntax.
Require Import Semantics.

Set Implicit Arguments.


Inductive split_acquire: forall (i1 i2:Instr.t), Prop :=
| split_acquire_load
    r l:
    split_acquire (Instr.load r l Ordering.acqrel) (Instr.load r l Ordering.relaxed)
| split_acquire_update
    r l rmw ow
    (OW: Ordering.le ow Ordering.strong_relaxed):
    split_acquire (Instr.update r l rmw Ordering.acqrel ow) (Instr.update r l rmw Ordering.relaxed ow)
.

Inductive sim_acquired: forall (st_src:(Language.state lang)) (lc_src:Local.t) (sc1_src:TimeMap.t) (mem1_src:Memory.t)
                          (st_tgt:(Language.state lang)) (lc_tgt:Local.t) (sc1_tgt:TimeMap.t) (mem1_tgt:Memory.t), Prop :=
| sim_acquired_intro
    rs
    lc1_src sc1_src mem1_src
    lc1_tgt sc1_tgt mem1_tgt
    (LOCAL: sim_local SimPromises.bot lc1_src (local_acquired lc1_tgt))
    (SC: TimeMap.le sc1_src sc1_tgt)
    (MEMORY: sim_memory mem1_src mem1_tgt)
    (WF_SRC: Local.wf lc1_src mem1_src)
    (WF_TGT: Local.wf lc1_tgt mem1_tgt)
    (SC_SRC: Memory.closed_timemap sc1_src mem1_src)
    (SC_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
    (MEM_SRC: Memory.closed mem1_src)
    (MEM_TGT: Memory.closed mem1_tgt):
    sim_acquired
      (State.mk rs []) lc1_src sc1_src mem1_src
      (State.mk rs [Stmt.instr (Instr.fence Ordering.acqrel Ordering.plain)]) lc1_tgt sc1_tgt mem1_tgt
.

Lemma sim_local_sim_acquired
      rs
      lc_src sc_src mem_src
      lc_tgt sc_tgt mem_tgt
      (SIM: sim_local SimPromises.bot lc_src lc_tgt)
      (SC1: TimeMap.le sc_src sc_tgt)
      (MEM1: sim_memory mem_src mem_tgt)
      (WF_SRC: Local.wf lc_src mem_src)
      (WF_TGT: Local.wf lc_tgt mem_tgt)
      (SC_SRC: Memory.closed_timemap sc_src mem_src)
      (SC_TGT: Memory.closed_timemap sc_tgt mem_tgt)
      (MEM_SRC: Memory.closed mem_src)
      (MEM_TGT: Memory.closed mem_tgt):
  sim_acquired (State.mk rs []) lc_src sc_src mem_src
               (State.mk rs [Stmt.instr (Instr.fence Ordering.acqrel Ordering.plain)]) lc_tgt sc_tgt mem_tgt.
Proof.
  econs; eauto.
  inv SIM. econs; ss. etrans; eauto.
  apply TViewFacts.read_fence_tview_incr. apply WF_TGT.
Qed.

Lemma sim_acquired_mon
      st_src lc_src sc1_src mem1_src
      st_tgt lc_tgt sc1_tgt mem1_tgt
      sc2_src mem2_src
      sc2_tgt mem2_tgt
      (SIM1: sim_acquired st_src lc_src sc1_src mem1_src
                          st_tgt lc_tgt sc1_tgt mem1_tgt)
      (SC_FUTURE_SRC: TimeMap.le sc1_src sc2_src)
      (SC_FUTURE_TGT: TimeMap.le sc1_tgt sc2_tgt)
      (MEM_FUTURE_SRC: Memory.future_weak mem1_src mem2_src)
      (MEM_FUTURE_TGT: Memory.future_weak mem1_tgt mem2_tgt)
      (SC1: TimeMap.le sc2_src sc2_tgt)
      (MEM1: sim_memory mem2_src mem2_tgt)
      (WF_SRC: Local.wf lc_src mem2_src)
      (WF_TGT: Local.wf lc_tgt mem2_tgt)
      (SC_SRC: Memory.closed_timemap sc2_src mem2_src)
      (SC_TGT: Memory.closed_timemap sc2_tgt mem2_tgt)
      (MEM_SRC: Memory.closed mem2_src)
      (MEM_TGT: Memory.closed mem2_tgt):
  sim_acquired st_src lc_src sc2_src mem2_src
               st_tgt lc_tgt sc2_tgt mem2_tgt.
Proof.
  inv SIM1. econs; eauto.
Qed.

Lemma sim_acquired_step
      st1_src lc1_src sc1_src mem1_src
      st1_tgt lc1_tgt sc1_tgt mem1_tgt
      (SIM: sim_acquired st1_src lc1_src sc1_src mem1_src
                         st1_tgt lc1_tgt sc1_tgt mem1_tgt):
  _sim_thread_step lang lang ((sim_thread (sim_terminal eq)) \8/ sim_acquired)
                   st1_src lc1_src sc1_src mem1_src
                   st1_tgt lc1_tgt sc1_tgt mem1_tgt.
Proof.
  inv SIM. ii.
  inv STEP_TGT; [inv STEP|inv STEP; inv LOCAL0];
    try (inv STATE; inv INSTR; inv SPLIT); ss.
  - (* promise *)
    right.
    exploit Local.promise_step_future; eauto. i. des.
    exploit sim_local_promise_acquired; try exact LOCAL; eauto. i. des.
    exploit Local.promise_step_future; eauto. i. des.
    esplits; try apply SC; eauto; ss.
    + econs 2. econs. econs; eauto.
    + eauto.
    + right. econs; eauto.
  - (* fence *)
    right.
    exploit Local.fence_step_future; eauto. i. des.
    inv STATE. inv INSTR. inv LOCAL1. ss.
    esplits; (try by econs 1); eauto; ss.
    left. eapply paco11_mon; [apply sim_stmts_nil|]; ss. econs; ss.
    + rewrite TViewFacts.write_fence_tview_strong_relaxed; ss. apply LOCAL.
    + apply LOCAL.
Qed.

Lemma sim_acquired_sim_thread:
  sim_acquired <8= (sim_thread (sim_terminal eq)).
Proof.
  pcofix CIH. i. pfold. ii. ss. splits; ss; ii.
  - inv TERMINAL_TGT. inv PR; ss.
  - right. esplits; eauto.
    inv PR. eapply sim_local_memory_bot; eauto.
  - exploit sim_acquired_mon; eauto. i.
    exploit sim_acquired_step; eauto. i. des; eauto.
    + right. esplits; eauto.
      left. eapply paco11_mon; eauto. ss.
    + right. esplits; eauto.
Qed.

Lemma split_acquire_sim_stmts
      i_src i_tgt
      (SPLIT: split_acquire i_src i_tgt):
  sim_stmts eq
            [Stmt.instr i_src]
            [Stmt.instr i_tgt; Stmt.instr (Instr.fence Ordering.acqrel Ordering.plain)]
            eq.
Proof.
  pcofix CIH. ii. subst. pfold. ii. splits; ii.
  { inv TERMINAL_TGT. }
  { right. esplits; eauto.
    inv LOCAL. apply SimPromises.sem_bot_inv in PROMISES; auto. rewrite PROMISES. auto.
  }
  inv STEP_TGT; [inv STEP|inv STEP; inv LOCAL0];
    try (inv STATE; inv INSTR; inv SPLIT); ss.
  - (* promise *)
    right.
    exploit sim_local_promise; eauto. i. des.
    esplits; try apply SC; eauto; ss.
    econs 2. econs 1; eauto. econs; eauto. eauto.
  - (* load *)
    right.
    exploit Local.read_step_future; eauto. i. des.
    exploit sim_local_read_acquired; eauto. i. des.
    exploit Local.read_step_future; eauto. i. des.
    esplits; try apply SC; eauto; ss.
    + econs 2. econs 2. econs; cycle 1.
      * econs 2. eauto.
      * econs. econs.
    + auto.
    + left. eapply paco11_mon; [apply sim_acquired_sim_thread|]; ss.
  - (* update-load *)
    right.
    exploit Local.read_step_future; eauto. i. des.
    exploit sim_local_read_acquired; eauto. i. des.
    exploit Local.read_step_future; eauto. i. des.
    esplits; try apply SC; eauto; ss.
    + econs 2. econs 2. econs; cycle 1.
      * econs 2. eauto.
      * econs. econs. eauto.
    + auto.
    + left. eapply paco11_mon; [apply sim_acquired_sim_thread|]; ss.
  - (* update *)
    right.
    exploit Local.read_step_future; eauto. i. des.
    exploit sim_local_read_acquired; eauto. i. des.
    exploit Local.read_step_future; eauto. i. des.
    exploit Local.write_step_future; eauto. i. des.
    hexploit sim_local_write_acquired; try exact LOCAL2; try exact SC; eauto; try refl.
    { inv LOCAL1. inv MEM_TGT. exploit CLOSED; eauto. i. des.
      inv MSG_TS. ss. }
    { inv STEP_SRC. inv LOCAL1. ss. repeat (condtac; aggrtac).
      - rewrite <- ? View.join_l. apply LOCAL.
      - apply WF_TGT.
      - unfold TimeMap.join. rewrite <- Time.join_l. rewrite <- Time.join_l. rewrite <- Time.join_r.
        unfold View.singleton_ur_if. condtac; ss. unfold TimeMap.singleton, LocFun.add.
        condtac; ss. refl.
    }
    i. des.
    exploit Local.write_step_future; eauto. i. des.
    esplits; try apply SC; eauto; ss.
    + econs 2. econs 2. econs; cycle 1.
      * econs 4; eauto.
      * econs. econs. eauto.
    + auto.
    + left. eapply paco11_mon; [apply sim_acquired_sim_thread|]; ss.
  - (* racy read *)
    right.
    exploit sim_local_racy_read_acquired; try exact LOCAL1; eauto. i. des.
    esplits; try apply SC; eauto; ss.
    + econs 2. econs 2. econs; cycle 1.
      * econs 9; eauto.
      * econs. econs.
    + ss.
    + left. eapply paco11_mon; [apply sim_acquired_sim_thread|]; ss.
      apply sim_local_sim_acquired; eauto.
  - (* racy read *)
    right.
    exploit sim_local_racy_read_acquired; try exact LOCAL1; eauto. i. des.
    esplits; try apply SC; eauto; ss.
    + econs 2. econs 2. econs; [|econs 9]; eauto. econs. econs. eauto.
    + ss.
    + left. eapply paco11_mon; [apply sim_acquired_sim_thread|]; ss.
      apply sim_local_sim_acquired; eauto.
  - (* racy update *)
    left.
    exploit sim_local_racy_update_acquired; try exact LOCAL1; eauto. i. des.
    unfold Thread.steps_failure.
    esplits; try refl.
    + econs 2. econs; [|econs 11]; eauto. econs. econs. eauto.
    + ss.
Qed.
