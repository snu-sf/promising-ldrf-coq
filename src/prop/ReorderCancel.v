Require Import Lia.
Require Import RelationClasses.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Language.

From PromisingLib Require Import Event.
Require Import Time.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.

Require Import PromiseConsistent.
Require Import ReorderPromise.
Require Import ReorderPromises.
Require Import MemoryReorder.
Require Import MemoryFacts.
Require Import Pred.
Require Import MemoryProps.

Set Implicit Arguments.


Lemma reorder_read_cancel
      lc0 mem0
      lc1 mem1
      lc2
      loc1 from1 to1 msg1
      loc2 to2 val2 released2 ord2
      (STEP1: Local.read_step lc0 mem0 loc2 to2 val2 released2 ord2 lc1)
      (STEP2: Local.promise_step lc1 mem0 loc1 from1 to1 msg1 lc2 mem1 Memory.op_kind_cancel)
  :
    exists lc1',
      (<<STEP1: Local.promise_step lc0 mem0 loc1 from1 to1 msg1 lc1' mem1 Memory.op_kind_cancel>>) /\
      (<<STEP2: Local.read_step lc1' mem1 loc2 to2 val2 released2 ord2 lc2>>).
Proof.
  inv STEP1. inv STEP2.
  hexploit MemoryFacts.promise_get1_diff; eauto.
  { ii. clarify. ss. inv PROMISE.
    eapply Memory.remove_get0 in MEM. des. clarify. }
  i. des. esplits; eauto.
Qed.

Lemma remove_non_synch_loc loc0 prom0 loc1 from to msg prom1
      (NONSYNCH: Memory.nonsynch_loc loc0 prom0)
      (REMOVE: Memory.remove prom0 loc1 from to msg prom1)
  :
    Memory.nonsynch_loc loc0 prom1.
Proof.
  ii. erewrite Memory.remove_o in GET; eauto.
  des_ifs. exploit NONSYNCH; eauto.
Qed.

Lemma remove_non_synch prom0 loc from to msg prom1
      (NONSYNCH: Memory.nonsynch prom0)
      (REMOVE: Memory.remove prom0 loc from to msg prom1)
  :
    Memory.nonsynch prom1.
Proof.
  ii. erewrite Memory.remove_o in GET; eauto.
  des_ifs. exploit NONSYNCH; eauto.
Qed.

Lemma reorder_write_cancel
      lc0 sc0 mem0
      lc1 mem1
      lc2 sc2 mem2
      loc1 from1 to1 msg1
      loc2 from2 to2 val2 releasedm2 released2 ord2 kind2
      (STEP1: Local.write_step lc0 sc0 mem0 loc2 from2 to2 val2 releasedm2 released2 ord2 lc1 sc2 mem1 kind2)
      (STEP2: Local.promise_step lc1 mem1 loc1 from1 to1 msg1 lc2 mem2 Memory.op_kind_cancel)
  :
    exists lc1' mem1',
      (<<STEP1: Local.promise_step lc0 mem0 loc1 from1 to1 msg1 lc1' mem1' Memory.op_kind_cancel>>) /\
      (<<STEP2: Local.write_step lc1' sc0 mem1' loc2 from2 to2 val2 releasedm2 released2 ord2 lc2 sc2 mem2 kind2>>).
Proof.
  inv STEP1. inv STEP2. ss.
  exploit MemoryReorder.write_cancel; [exact WRITE| exact PROMISE|]. i. des.
  esplits.
  - econs; eauto.
    inv CANCEL1. eapply Memory.cancel_closed_message; eauto.
  - econs; eauto.
    i. hexploit RELEASE; eauto. i. inv CANCEL1.
    eapply remove_non_synch_loc; eauto.
Qed.

Lemma reorder_write_na_cancel
      lc0 sc0 mem0
      lc1 mem1
      lc2 sc2 mem2
      loc1 from1 to1 msg1
      loc2 from2 to2 val2 ord2 msgs2 kinds2 kind2
      (STEP1: Local.write_na_step lc0 sc0 mem0 loc2 from2 to2 val2 ord2 lc1 sc2 mem1 msgs2 kinds2 kind2)
      (STEP2: Local.promise_step lc1 mem1 loc1 from1 to1 msg1 lc2 mem2 Memory.op_kind_cancel)
  :
    exists lc1' mem1',
      (<<STEP1: Local.promise_step lc0 mem0 loc1 from1 to1 msg1 lc1' mem1' Memory.op_kind_cancel>>) /\
      (<<STEP2: Local.write_na_step lc1' sc0 mem1' loc2 from2 to2 val2 ord2 lc2 sc2 mem2 msgs2 kinds2 kind2>>).
Proof.
  inv STEP1. inv STEP2. ss.
  exploit MemoryReorder.write_na_cancel; [exact WRITE|exact PROMISE|]. i. des.
  esplits.
  - econs; eauto.
    inv CANCEL1. eapply Memory.cancel_closed_message; eauto.
  - econs; eauto.
Qed.

Lemma reorder_fence_cancel
      lc0 mem0
      lc1 mem1
      lc2
      loc1 from1 to1 msg1
      ord1 ord2 sc0 sc1
      (STEP1: Local.fence_step lc0 sc0 ord1 ord2 lc1 sc1)
      (STEP2: Local.promise_step lc1 mem0 loc1 from1 to1 msg1 lc2 mem1 Memory.op_kind_cancel)
  :
    exists lc1',
      (<<STEP1: Local.promise_step lc0 mem0 loc1 from1 to1 msg1 lc1' mem1 Memory.op_kind_cancel>>) /\
      (<<STEP2: Local.fence_step lc1' sc0 ord1 ord2 lc2 sc1>>).
Proof.
  inv STEP1. inv STEP2. ss. esplits.
  - econs; eauto.
  - econs; eauto.
    + inv PROMISE. i. eapply remove_non_synch; eauto.
    + i. ss. subst. erewrite PROMISES in *; auto.
      inv PROMISE. eapply Memory.remove_get0 in PROMISES0. des.
      erewrite Memory.bot_get in *. ss.
Qed.

Lemma reorder_promise_consistent_cancel
      lc1 mem1 loc from to msg lc2 mem2
      (CONS: Local.promise_consistent lc1)
      (STEP: Local.promise_step lc1 mem1 loc from to msg lc2 mem2 Memory.op_kind_cancel):
  (<<CONS: Local.promise_consistent lc2>>).
Proof.
  inv STEP. inv PROMISE. ii. ss.
  revert PROMISE. erewrite Memory.remove_o; eauto. condtac; ss. eauto.
Qed.

Lemma reorder_failure_cancel
      lc1 mem1
      lc2 mem2
      loc1 from1 to1 msg1
      (STEP1: Local.failure_step lc1)
      (STEP2: Local.promise_step lc1 mem1 loc1 from1 to1 msg1 lc2 mem2 Memory.op_kind_cancel):
  (<<STEP2: Local.failure_step lc2>>).
Proof.
  inv STEP1. econs.
  eapply reorder_promise_consistent_cancel; eauto.
Qed.

Lemma reorder_is_racy_cancel
      lc1 mem1
      lc2 mem2
      loc2 to2 ord2
      loc1 from1 to1 msg1
      (RACY: Local.is_racy lc1 mem1 loc2 to2 ord2)
      (STEP: Local.promise_step lc1 mem1 loc1 from1 to1 msg1 lc2 mem2 Memory.op_kind_cancel):
  (<<RACY: Local.is_racy lc2 mem2 loc2 to2 ord2>>).
Proof.
  inv RACY. inv STEP. inv PROMISE.
  exploit Memory.remove_get1; try exact GET; eauto. i. des.
  { subst.
    exploit Memory.remove_get0; try exact PROMISES. i. des. congr.
  }
  econs; eauto. s.
  erewrite Memory.remove_o; eauto. condtac; ss.
Qed.

Lemma reorder_racy_read_cancel
      lc1 mem1
      lc2 mem2
      loc2 to2 val2 ord2
      loc1 from1 to1 msg1
      (STEP1: Local.racy_read_step lc1 mem1 loc2 to2 val2 ord2)
      (STEP2: Local.promise_step lc1 mem1 loc1 from1 to1 msg1 lc2 mem2 Memory.op_kind_cancel):
  (<<STEP2: Local.racy_read_step lc2 mem2 loc2 to2 val2 ord2>>).
Proof.
  inv STEP1. econs.
  eapply reorder_is_racy_cancel; eauto.
Qed.

Lemma reorder_racy_write_cancel
      lc1 mem1
      lc2 mem2
      loc2 to2 ord2
      loc1 from1 to1 msg1
      (STEP1: Local.racy_write_step lc1 mem1 loc2 to2 ord2)
      (STEP2: Local.promise_step lc1 mem1 loc1 from1 to1 msg1 lc2 mem2 Memory.op_kind_cancel):
  (<<STEP2: Local.racy_write_step lc2 mem2 loc2 to2 ord2>>).
Proof.
  inv STEP1. econs.
  - eapply reorder_is_racy_cancel; eauto.
  - eapply reorder_promise_consistent_cancel; eauto.
Qed.

Lemma reorder_racy_update_cancel
      lc1 mem1
      lc2 mem2
      loc2 to2 ordr2 ordw2
      loc1 from1 to1 msg1
      (STEP1: Local.racy_update_step lc1 mem1 loc2 to2 ordr2 ordw2)
      (STEP2: Local.promise_step lc1 mem1 loc1 from1 to1 msg1 lc2 mem2 Memory.op_kind_cancel):
  (<<STEP2: Local.racy_update_step lc2 mem2 loc2 to2 ordr2 ordw2>>).
Proof.
  inv STEP1.
  - econs 1; eauto.
    eapply reorder_promise_consistent_cancel; eauto.
  - econs 2; eauto.
    eapply reorder_promise_consistent_cancel; eauto.
  - econs 3; eauto.
    + eapply reorder_is_racy_cancel; eauto.
    + eapply reorder_promise_consistent_cancel; eauto.
Qed.

Lemma reorder_step_cancel
      lang
      pf1 pf2 e1 e2 th0 th1 th2
      (STEP1: @Thread.step lang pf1 e1 th0 th1)
      (STEP2: Thread.step pf2 e2 th1 th2)
      (CANCEL: ThreadEvent.is_cancel e2):
  (exists th1',
    (<<STEP1: Thread.step pf2 e2 th0 th1'>>) /\
    (<<STEP2: Thread.step pf1 e1 th1' th2>>)) \/
  (th2 = th0 /\ <<RESERVE: ThreadEvent.is_reserve e1>>)
.
Proof.
  unfold ThreadEvent.is_cancel in *. des_ifs.
  inv STEP2; inv STEP; [|inv LOCAL]. ss.
  inv STEP1; ss.
  - inv STEP. ss. exploit reorder_promise_promise_cancel; eauto.
    i. des; clarify; eauto.
    left. esplits.
    + econs 1. econs; eauto.
    + econs 1. econs; eauto.
  - left. inv STEP. ss. inv LOCAL0; ss.
    + esplits.
      * econs 1. econs; eauto.
      * econs 2. econs; eauto; ss.
    + exploit reorder_read_cancel; eauto. i. des. esplits.
      * econs 1. econs; eauto.
      * econs 2. econs; eauto; ss.
    + exploit reorder_write_cancel; eauto. i. des. esplits.
      * econs 1. econs; eauto.
      * econs 2. econs; eauto; ss.
    + exploit reorder_write_cancel; eauto. i. des.
      exploit reorder_read_cancel; eauto. i. des.
      esplits.
      * econs 1. econs; eauto.
      * econs 2. econs; eauto; ss.
    + exploit reorder_fence_cancel; eauto. i. des. esplits.
      * econs 1. econs; eauto.
      * econs 2. econs; eauto; ss.
    + exploit reorder_fence_cancel; eauto. i. des. esplits.
      * econs 1. econs; eauto.
      * econs 2. econs; eauto; ss.
    + exploit reorder_failure_cancel; eauto. i. des. esplits.
      * econs 1. econs; eauto.
      * econs 2. econs; eauto.
    + exploit reorder_write_na_cancel; eauto. i. des. esplits.
      * econs 1. econs; eauto.
      * econs 2. econs; eauto.
    + exploit reorder_racy_read_cancel; eauto. i. des. esplits.
      * econs 1. econs; eauto.
      * econs 2. econs; eauto.
    + exploit reorder_racy_write_cancel; eauto. i. des. esplits.
      * econs 1. econs; eauto.
      * econs 2. econs; eauto.
    + exploit reorder_racy_update_cancel; eauto. i. des. esplits.
      * econs 1. econs; eauto.
      * econs 2. econs; eauto.
Qed.

Lemma reorder_step_cancels
      lang
      pf e1 th0 th1 th2
      (STEP1: Thread.step pf e1 th0 th1)
      (STEPS2: rtc (@Thread.cancel_step lang) th1 th2)
  :
    (exists th1',
        (<<STEPS1: rtc (@Thread.cancel_step lang) th0 th1'>>) /\
        (<<STEP2: Thread.step pf e1 th1' th2>>)) \/
    ((<<STEPS1: rtc (@Thread.cancel_step lang) th0 th2>>) /\ (<<RESERVE: ThreadEvent.is_reserve e1>>))
.
Proof.
  ginduction STEPS2; i.
  - esplits; eauto.
  - inv H. exploit reorder_step_cancel.
    { eapply STEP1. }
    { eapply STEP. }
    { ss. }
    i. des.
    { exploit IHSTEPS2; eauto. i. des.
      - left. esplits.
        + econs 2.
          * splits; auto. econs; eauto.
          * eauto.
        + eauto.
      - right. splits; auto. econs 2; eauto. econs; eauto.
    }
    { subst. right. esplits; eauto. }
Qed.

Lemma reorder_opt_step_cancels
      lang
      e1 th0 th1 th2
      (STEP1: Thread.opt_step e1 th0 th1)
      (STEPS2: rtc (@Thread.cancel_step lang) th1 th2)
  :
    (exists th1',
        (<<STEPS1: rtc (@Thread.cancel_step lang) th0 th1'>>) /\
        (<<STEP2: Thread.opt_step e1 th1' th2>>)) \/
    ((<<STEPS1: rtc (@Thread.cancel_step lang) th0 th2>>) /\ (<<RESERVE: ThreadEvent.is_reserve e1>>)).
Proof.
  inv STEP1.
  { left. esplits; eauto. econs 1. }
  { exploit reorder_step_cancels; eauto. i. des.
    { left. esplits; eauto. econs 2; eauto. }
    { right. esplits; eauto. }
  }
Qed.

Lemma reorder_opt_step_cancels2
      lang
      e1 th0 th1 th2
      (STEP1: Thread.opt_step e1 th0 th1)
      (STEPS2: rtc (@Thread.cancel_step lang) th1 th2)
  :
    exists th1' e1',
      (<<STEPS1: rtc (@Thread.cancel_step lang) th0 th1'>>) /\
      (<<STEP2: Thread.opt_step e1' th1' th2>>) /\
      __guard__(e1' = e1 \/ e1' = ThreadEvent.silent /\ <<RESERVE: ThreadEvent.is_reserve e1>>).
Proof.
  unguard. inv STEP1.
  { esplits.
    { eauto. }
    { econs 1. }
    { auto. }
  }
  { exploit reorder_step_cancels; eauto. i. des.
    { esplits; eauto. econs 2; eauto. }
    { esplits; eauto. econs 1; eauto. }
  }
Qed.

Lemma steps_cancels_not_cancels
      P lang th0 th2
      (STEPS: rtc (tau (@pred_step P lang)) th0 th2)
  :
    exists th1,
      (<<STEPS1: rtc (@Thread.cancel_step _) th0 th1>>) /\
      (<<STEPS2: rtc (tau (@pred_step (P /1\ fun e => ~ ThreadEvent.is_cancel e) _)) th1 th2>>)
.
Proof.
  ginduction STEPS; i.
  - esplits; eauto.
  - inv H. inv TSTEP. inv STEP.
    hexploit IHSTEPS; eauto. i. des.
    destruct (classic (ThreadEvent.is_cancel e)).
    + unfold ThreadEvent.is_cancel in H. des_ifs. esplits.
      * econs 2.
        { econs; eauto. }
        { eapply STEPS1. }
      * eapply STEPS2.
    + exploit reorder_step_cancels.
      { eapply STEP0. }
      { eapply STEPS1. }
      i. des; eauto. esplits.
      * eauto.
      * econs 2.
        { econs; eauto. econs; eauto. econs; eauto. }
        { eauto. }
Qed.
