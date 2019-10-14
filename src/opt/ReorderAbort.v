Require Import Bool.
Require Import List.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Basic.
Require Import Event.
From PromisingLib Require Import Language.
Require Import Time.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.

Require Import SimMemory.
Require Import SimPromises.
Require Import SimLocal.
Require Import Compatibility.
Require Import SimThread.

Require Import ReorderStep.

Require Import Syntax.
Require Import Semantics.

Set Implicit Arguments.


Inductive reorder_abort: forall (i2:Instr.t), Prop :=
| reorder_abort_load
    r2 l2 o2
    (ORD2: Ordering.le o2 Ordering.relaxed):
    reorder_abort (Instr.load r2 l2 o2)
| reorder_abort_store
    l2 v2 o2
    (ORD: Ordering.le o2 Ordering.acqrel):
    reorder_abort (Instr.store l2 v2 o2)
| reorder_abort_update
    r2 l2 rmw2 or2 ow2
    (ORDR2: Ordering.le or2 Ordering.relaxed)
    (ORDW2: Ordering.le ow2 Ordering.acqrel):
    reorder_abort (Instr.update r2 l2 rmw2 or2 ow2)
| reorder_abort_fence
    or2 ow2
    (ORDR2: Ordering.le or2 Ordering.relaxed)
    (ORDW2: Ordering.le ow2 Ordering.acqrel):
    reorder_abort (Instr.fence or2 ow2)
.

Inductive sim_abort: forall (st_src:lang.(Language.state)) (lc_src:Local.t) (sc1_src:TimeMap.t) (mem1_src:Memory.t)
                       (st_tgt:lang.(Language.state)) (lc_tgt:Local.t) (sc1_tgt:TimeMap.t) (mem1_tgt:Memory.t), Prop :=
| sim_abort_intro
    rs i2
    lc1_src sc1_src mem1_src
    lc1_tgt sc1_tgt mem1_tgt
    (REORDER: reorder_abort i2)
    (FAILURE: Local.failure_step lc1_src)
    (LOCAL: sim_local SimPromises.bot lc1_src lc1_tgt)
    (SC: TimeMap.le sc1_src sc1_tgt)
    (MEMORY: sim_memory mem1_src mem1_tgt)
    (WF_SRC: Local.wf lc1_src mem1_src)
    (WF_TGT: Local.wf lc1_tgt mem1_tgt)
    (SC_SRC: Memory.closed_timemap sc1_src mem1_src)
    (SC_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
    (MEM_SRC: Memory.closed mem1_src)
    (MEM_TGT: Memory.closed mem1_tgt):
    sim_abort
      (State.mk rs [Stmt.instr i2; Stmt.instr Instr.abort]) lc1_src sc1_src mem1_src
      (State.mk rs [Stmt.instr i2]) lc1_tgt sc1_tgt mem1_tgt
.

Lemma sim_abort_mon
      st_src lc_src sc1_src mem1_src
      st_tgt lc_tgt sc1_tgt mem1_tgt
      sc2_src mem2_src
      sc2_tgt mem2_tgt
      (SIM1: sim_abort st_src lc_src sc1_src mem1_src
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
  sim_abort st_src lc_src sc2_src mem2_src
            st_tgt lc_tgt sc2_tgt mem2_tgt.
Proof.
  inv SIM1. econs; eauto.
Qed.

Lemma sim_abort_cap
      st_src lc_src sc1_src mem1_src
      st_tgt lc_tgt sc1_tgt mem1_tgt
      mem2_src
      (MEM1: sim_memory mem1_src mem1_tgt)
      (SIM1: sim_abort st_src lc_src sc1_src mem1_src
                       st_tgt lc_tgt sc1_tgt mem1_tgt)
      (CAP_SRC: Memory.cap lc_src.(Local.promises) mem1_src mem2_src):
  exists lc'_src mem2_tgt,
    <<MEM2: sim_memory mem2_src mem2_tgt>> /\
    <<CAP_TGT: Memory.cap lc_tgt.(Local.promises) mem1_tgt mem2_tgt>> /\
    <<SIM2: sim_abort st_src lc'_src sc1_src mem2_src
                      st_tgt lc_tgt sc1_tgt mem2_tgt>>.
Proof.
  inv SIM1.
  exploit Memory.cap_future_weak; try exact CAP_SRC; eauto. i.
  exploit SimPromises.cap; try apply MEM1; eauto.
  { inv LOCAL. apply SimPromises.sem_bot_inv in PROMISES; auto. rewrite <- PROMISES.
    apply SimPromises.sem_bot.
  }
  i. des.
  exploit cap_property; try exact CAP_SRC; eauto. i. des.
  exploit cap_property; try exact CAP_TGT; eauto. i. des.
  esplits; eauto.
  econs; eauto.
Qed.

Lemma sim_abort_steps_failure
      st1_src lc1_src sc1_src mem1_src
      st1_tgt lc1_tgt sc1_tgt mem1_tgt
      (SIM: sim_abort st1_src lc1_src sc1_src mem1_src
                      st1_tgt lc1_tgt sc1_tgt mem1_tgt):
  Thread.steps_failure (Thread.mk lang st1_src lc1_src sc1_src mem1_src).
Proof.
Admitted.
