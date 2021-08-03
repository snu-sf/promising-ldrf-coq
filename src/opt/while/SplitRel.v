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
Require Import SplitRelCommon.

Require Import Syntax.
Require Import Semantics.

Set Implicit Arguments.


Inductive split_release: forall (i1 i2:Instr.t), Prop :=
| split_release_store
    l v:
    split_release (Instr.store l v Ordering.acqrel) (Instr.store l v Ordering.strong_relaxed)
| split_release_update
    r l rmw or
    (OR: Ordering.le or Ordering.strong_relaxed):
    split_release (Instr.update r l rmw or Ordering.acqrel) (Instr.update r l rmw or Ordering.strong_relaxed)
.

Inductive sim_released: forall (st_src:(Language.state lang)) (lc_src:Local.t) (sc1_src:TimeMap.t) (mem1_src:Memory.t)
                          (st_tgt:(Language.state lang)) (lc_tgt:Local.t) (sc1_tgt:TimeMap.t) (mem1_tgt:Memory.t), Prop :=
| sim_released_intro
    i_src i_tgt rs
    lc1_src sc1_src mem1_src
    lc1_tgt sc1_tgt mem1_tgt
    (SPLIT: split_release i_src i_tgt)
    (LOCAL: sim_local SimPromises.bot lc1_src lc1_tgt)
    (RELEASED: forall l, View.le (TView.cur (Local.tview lc1_tgt)) ((TView.rel (Local.tview lc1_tgt)) l))
    (SC: TimeMap.le sc1_src sc1_tgt)
    (MEMORY: sim_memory mem1_src mem1_tgt)
    (WF_SRC: Local.wf lc1_src mem1_src)
    (WF_TGT: Local.wf lc1_tgt mem1_tgt)
    (SC_SRC: Memory.closed_timemap sc1_src mem1_src)
    (SC_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
    (MEM_SRC: Memory.closed mem1_src)
    (MEM_TGT: Memory.closed mem1_tgt):
    sim_released
      (State.mk rs [Stmt.instr i_src]) lc1_src sc1_src mem1_src
      (State.mk rs [Stmt.instr i_tgt]) lc1_tgt sc1_tgt mem1_tgt
.

Lemma sim_released_mon
      st_src lc_src sc1_src mem1_src
      st_tgt lc_tgt sc1_tgt mem1_tgt
      sc2_src mem2_src
      sc2_tgt mem2_tgt
      (SIM1: sim_released st_src lc_src sc1_src mem1_src
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
  sim_released st_src lc_src sc2_src mem2_src
               st_tgt lc_tgt sc2_tgt mem2_tgt.
Proof.
  inv SIM1. econs; eauto.
Qed.

Lemma sim_released_step
      st1_src lc1_src sc1_src mem1_src
      st1_tgt lc1_tgt sc1_tgt mem1_tgt
      (SIM: sim_released st1_src lc1_src sc1_src mem1_src
                         st1_tgt lc1_tgt sc1_tgt mem1_tgt):
  _sim_thread_step lang lang ((sim_thread (sim_terminal eq)) \8/ sim_released)
                   st1_src lc1_src sc1_src mem1_src
                   st1_tgt lc1_tgt sc1_tgt mem1_tgt.
Proof.
  inv SIM. ii.
  inv STEP_TGT; [inv STEP|inv STEP; inv LOCAL0];
    try (inv STATE; inv INSTR; inv SPLIT); ss.
  - (* promise *)
    right.
    exploit Local.promise_step_future; eauto. i. des.
    exploit sim_local_promise; eauto. i. des.
    exploit Local.promise_step_future; eauto. i. des.
    esplits; try apply SC; eauto; ss.
    + econs 2. econs. econs; eauto.
    + eauto.
    + right. econs; eauto.
      inv LOCAL0. ss.
  - (* update-load *)
    right.
    exploit sim_local_read; (try by etrans; eauto); eauto; try refl. i. des.
    esplits; eauto; ss.
    + econs 2. econs 2. econs; [|econs 2]; eauto. econs. econs. eauto.
    + eauto.
    + left. eapply paco11_mon; [apply sim_stmts_nil|]; ss.
  - (* write *)
    right.
    hexploit sim_local_write_released; (try by etrans; eauto); eauto; try refl; try by econs.
    { by rewrite <- View.join_l. }
    i. des.
    esplits; eauto; ss.
    + econs 2. econs 2. econs; [|econs 3]; eauto. econs. econs.
    + ss.
    + left. eapply paco11_mon; [apply sim_stmts_nil|]; ss.
  - (* update *)
    right.
    exploit Local.read_step_future; eauto. i. des.
    exploit sim_local_read; (try by etrans; eauto); eauto; try refl; try by econs. i. des.
    exploit Local.read_step_future; eauto. i. des.
    hexploit sim_local_write_released; (try by etrans; eauto); eauto; try refl; try by econs.
    { assert (TS: Time.lt tsr tsw).
      { inv LOCAL2. eapply MemoryFacts.MemoryFacts.write_time_lt. eauto. }
      inv LOCAL1. ss. repeat (condtac; aggrtac); try by apply WF_TGT.
      destruct ordr; ss.
    }
    i. des.
    esplits; eauto; ss.
    + econs 2. econs 2. econs; [|econs 4]; eauto. econs. econs. eauto.
    + ss.
    + left. eapply paco11_mon; [apply sim_stmts_nil|]; ss.
  - (* na write *)
    inv LOCAL1. inv ORD.
  - (* racy read *)
    right.
    exploit sim_local_racy_read; try exact LOCAL1; eauto; try refl. i. des.
    esplits; try apply SC; eauto; ss.
    + econs 2. econs 2. econs; [|econs 9]; eauto. econs. econs. eauto.
    + ss.
    + left. eapply paco11_mon; [apply sim_stmts_nil|]; ss.
  - (* racy write *)
    left.
    exploit sim_local_racy_write_released; try exact LOCAL1; eauto. i. des.
    unfold Thread.steps_failure.
    esplits; try refl.
    + econs 2. econs; [|econs 10]; eauto. econs. econs.
    + ss.
  - (* racy update *)
    left.
    exploit sim_local_racy_update_released; try exact LOCAL1; eauto. i. des.
    unfold Thread.steps_failure.
    esplits; try refl.
    + econs 2. econs; [|econs 11]; eauto. econs. econs. eauto.
    + ss.
Qed.

Lemma sim_released_sim_thread:
  sim_released <8= (sim_thread (sim_terminal eq)).
Proof.
  pcofix CIH. i. pfold. ii. ss. splits; ss; ii.
  - inv TERMINAL_TGT. inv PR; ss.
  - right. esplits; eauto.
    inv PR. eapply sim_local_memory_bot; eauto.
  - exploit sim_released_mon; eauto. i.
    exploit sim_released_step; eauto. i. des; eauto.
    + right. esplits; eauto.
      left. eapply paco11_mon; eauto. ss.
    + right. esplits; eauto.
Qed.

Lemma split_release_sim_stmts
      i_src i_tgt
      (SPLIT: split_release i_src i_tgt):
  sim_stmts eq
            [Stmt.instr i_src]
            [Stmt.instr (Instr.fence Ordering.plain Ordering.acqrel); Stmt.instr i_tgt]
            eq.
Proof.
  pcofix CIH. ii. subst. pfold. ii. splits; ii.
  { inv TERMINAL_TGT. }
  { right. esplits; eauto.
    inv LOCAL. apply SimPromises.sem_bot_inv in PROMISES; auto. rewrite PROMISES. auto.
  }
  right.
  inv STEP_TGT; [inv STEP|inv STEP; inv LOCAL0];
    try (inv STATE; inv INSTR); ss.
  - (* promise *)
    exploit sim_local_promise; eauto. i. des.
    esplits; try apply SC; eauto; ss.
    econs 2. econs 1; eauto. econs; eauto. eauto.
  - (* fence *)
    exploit Local.fence_step_future; eauto. i. des.
    esplits.
    + ss.
    + eauto.
    + econs 1.
    + ss.
    + inv LOCAL1. ss.
    + ss.
    + left. eapply paco11_mon; [apply sim_released_sim_thread|]; ss.
      inv LOCAL1. econs; eauto.
      * inv LOCAL. econs; ss. etrans; eauto.
      * s. i. repeat condtac; ss. refl.
Qed.
