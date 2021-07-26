Require Import RelationClasses.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import Loc.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Language.

Require Import Event.
Require Import Time.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import MemoryFacts.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.
Require Import Behavior.

Require Import Cover.
Require Import MemorySplit.
Require Import MemoryMerge.
Require Import FulfillStep.
Require Import PromiseConsistent.

Require Import Program.


Set Implicit Arguments.

Definition world: Type. Admitted.
Definition world_le: world -> world -> Prop. Admitted.
Instance world_le_PreOrder: PreOrder world_le. Admitted.

Definition sim_memory: forall (w: world) (mem_src mem_tgt:Memory.t), Prop. Admitted.
Definition sim_timemap: forall (w: world) (sc_src sc_tgt: TimeMap.t), Prop. Admitted.
Definition sim_local: forall (w: world) (lc_src lc_tgt:Local.t), Prop. Admitted.

Definition sim_local_world_mon: forall (w0 w1: world) (WORLD: world_le w0 w1),
    sim_local w0 <2= sim_local w1.
Admitted.

Definition sim_timemap_world_mon: forall (w0 w1: world) (WORLD: world_le w0 w1),
    sim_timemap w0 <2= sim_timemap w1.
Admitted.

Lemma sim_local_memory_bot:
  forall w lc_src lc_tgt
         (SIM: sim_local w lc_src lc_tgt)
         (BOT: (Local.promises lc_tgt) = Memory.bot),
    (Local.promises lc_src) = Memory.bot.
Admitted.

Lemma sim_memory_cap: forall
    w1
    mem1_src mem2_src
    mem1_tgt mem2_tgt
    sc1_src sc1_tgt
    (MEM1: sim_memory w1 mem1_src mem1_tgt)
    (CAP_SRC: Memory.cap mem1_src mem2_src)
    (CAP_TGT: Memory.cap mem1_tgt mem2_tgt)
    (MEM1_SRC: Memory.closed mem1_src)
    (MEM1_TGT: Memory.closed mem1_tgt)
    (CLOSED_SRC: Memory.closed_timemap sc1_src mem1_src)
    (CLOSED_TGT: Memory.closed_timemap sc1_tgt mem1_tgt),
    exists w2,
      (<<MEM2: sim_memory w2 mem2_src mem2_tgt>>) /\
      (<<TIMEMAP: sim_timemap w2 sc1_src sc1_tgt>>) /\
      (<<WORLD: world_le w1 w2>>)
.
Admitted.

Lemma sim_local_promise
      w0
      lc1_src mem1_src
      lc1_tgt mem1_tgt
      lc2_tgt mem2_tgt
      loc from to msg_tgt kind_tgt
      (STEP_TGT: Local.promise_step lc1_tgt mem1_tgt loc from to msg_tgt lc2_tgt mem2_tgt kind_tgt)
      (LOCAL1: sim_local w0 lc1_src lc1_tgt)
      (MEM1: sim_memory w0 mem1_src mem1_tgt)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
      (MEM1_SRC: Memory.closed mem1_src)
      (MEM1_TGT: Memory.closed mem1_tgt):
  exists lc2_src mem2_src msg_src kind_src w1,
    (<<STEP_SRC: Local.promise_step lc1_src mem1_src loc from to msg_src lc2_src mem2_src kind_src>>) /\
    (<<LOCAL2: sim_local w1 lc2_src lc2_tgt>>) /\
    (<<MEM2: sim_memory w1 mem2_src mem2_tgt>>) /\
    (<<WORLD: world_le w0 w1>>).
Admitted.
