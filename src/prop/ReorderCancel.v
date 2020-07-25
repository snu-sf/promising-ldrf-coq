Require Import Omega.
Require Import RelationClasses.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
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
  (* (LOCAL0: Local.wf lc0 mem0) *)
  (* (MEM0: Memory.closed mem0) *)
  (* (LOCTS: (loc1, to1) <> (loc2, to2)): *)
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

Lemma reorder_promise_read
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
    exists kind2' lc1' mem1',
      (exists from1', <<STEP2: Local.promise_step lc0 mem0 loc1 from1' to1 msg1 lc1' mem1' Memory.op_kind_cancel>>) /\
      (<<STEP2: Local.write_step lc1' sc0 mem1' loc2 from2 to2 val2 releasedm2 released2 ord2 lc2 sc2 mem2 kind2'>>).
Proof.
  inv STEP2. inv PROMISE.
  inv STEP1. ss. inv WRITE.
  exploit MemoryReorder.remove_remove.
  { eapply REMOVE. }
  { eapply PROMISES. } i. des.
  assert (LOCTS: (loc2, to2) <> (loc1, to1)).
  { ii. clarify. apply Memory.remove_get0 in MEM. inv PROMISE.
    - apply Memory.add_get0 in MEM0. des. clarify.
    - apply Memory.split_get0 in MEM0. des. clarify.
    - apply Memory.lower_get0 in MEM0. des. clarify.
    - clarify. }
  inv PROMISE.
  - exploit MemoryReorder.add_remove.
    { eapply LOCTS. }
    { eapply PROMISES0. }
    { eauto. } i. des.
    exploit MemoryReorder.add_remove.
    { eapply LOCTS. }
    { eapply MEM0. }
    { eauto. } i. des.
    esplits.
    + econs; eauto.
    + econs; ss.
      * econs.
        { econs 1; eauto.
          i. erewrite Memory.remove_o in GET; eauto.
          des_ifs. eapply ATTACH; eauto. }
        { eauto. }
      * intros ORD. eapply RELEASE in ORD.
        eapply remove_non_synch_loc; eauto.
  - destruct (classic ((loc2, ts3) = (loc1, to1))) as [|LOCTS2]; clarify.
    { exploit MemoryReorder.split_remove_same.
      { eapply PROMISES0. }
      { eauto. } i. des. clarify.
    }
    { exploit MemoryReorder.split_remove.
      { eapply LOCTS. }
      { eapply LOCTS2. }
      { eapply PROMISES0. }
      { eauto. } i. des.
      exploit MemoryReorder.split_remove.
      { eapply LOCTS. }
      { eapply LOCTS2. }
      { eapply MEM0. }
      { eauto. } i. des.
      esplits.
      + econs; eauto.
      + econs; ss.
        * econs.
          { econs 2; eauto. }
          { eauto. }
        * intros ORD. eapply RELEASE in ORD.
          eapply remove_non_synch_loc; eauto. }
  - exploit MemoryReorder.lower_remove.
    { eapply LOCTS. }
    { eapply PROMISES0. }
    { eauto. } i. des.
    exploit MemoryReorder.lower_remove.
    { eapply LOCTS. }
    { eapply MEM0. }
    { eauto. } i. des.
    esplits.
    + econs; eauto.
    + econs; ss.
      * econs.
        { econs 3; eauto. }
        { eauto. }
      * intros ORD. eapply RELEASE in ORD.
        eapply remove_non_synch_loc; eauto.
  - clarify.
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

Lemma reorder_pf_step_cancel
      lang
      e1 e2 th0 th1 th2
      (STEP1: @pred_step (promise_free /1\ (fun e => ~ is_cancel e)) lang
                         e1 th0 th1)
      (STEP2: pred_step is_cancel e2 th1 th2)
      (LOCAL: Local.wf th0.(Thread.local) th0.(Thread.memory))
      (MEMORY: Memory.closed th0.(Thread.memory)):
  exists e2' e1' th1',
    (<<STEP1: pred_step is_cancel e2' th0 th1'>>) /\
    (<<STEP2: pred_step (promise_free /1\ (fun e => ~ is_cancel e)) e1' th1' th2>>) /\
    (<<EVT: ThreadEvent.get_machine_event e1' = ThreadEvent.get_machine_event e1>>)
.
Proof.
  inv STEP1. inv STEP2. des. unfold is_cancel in SAT0. des_ifs.
  inv STEP0. inv STEP1; inv STEP0; [|inv LOCAL0]. ss.
  inv STEP. inv STEP0; ss.
  - inv STEP. ss. exploit reorder_promise_promise_cancel; eauto.
    { des_ifs. }
    i. des; clarify. esplits.
    + econs.
      * econs. econs 1. econs; eauto.
      * ss.
    + econs.
      * econs. econs 1. econs; eauto.
      * ss.
    + ss.
  - inv STEP. ss. inv LOCAL1; ss.
    + esplits.
      * econs.
        { econs. econs 1. econs; eauto. }
        { ss. }
      * econs.
        { econs. econs 2. econs; eauto; ss. }
        { ss. }
      * ss.
    + exploit reorder_read_cancel; eauto. i. des. esplits.
      * econs.
        { econs. econs 1. econs; eauto. }
        { ss. }
      * econs.
        { econs. econs 2. econs; eauto; ss. }
        { ss. }
      * ss.
    + exploit reorder_write_cancel; eauto. i. des. esplits.
      * econs.
        { econs. econs 1. econs; eauto. }
        { ss. }
      * econs.
        { econs. econs 2. econs; eauto; ss. }
        { ss. }
      * ss.
    + exploit reorder_write_cancel; eauto. i. des.
      exploit reorder_read_cancel; eauto. i. des.
      esplits.
      * econs.
        { econs. econs 1. econs; eauto. }
        { ss. }
      * econs.
        { econs. econs 2. econs; eauto; ss. }
        { ss. }
      * ss.
    + exploit reorder_fence_cancel; eauto. i. des. esplits.
      * econs.
        { econs. econs 1. econs; eauto. }
        { ss. }
      * econs.
        { econs. econs 2. econs; eauto; ss. }
        { ss. }
      * ss.
    + exploit reorder_fence_cancel; eauto. i. des. esplits.
      * econs.
        { econs. econs 1. econs; eauto. }
        { ss. }
      * econs.
        { econs. econs 2. econs; eauto; ss. eauto. }
        { ss. }
      * ss.
    + esplits.
      * econs; eauto.
        { econs. econs 1. econs; eauto. }
        { ss. }
      * econs.
        { econs. econs 2. econs.
          - instantiate (1:=ThreadEvent.failure). auto.
          - econs. econs. inv LOCAL2. inv LOCAL0. inv PROMISE.
            ii. ss. erewrite Memory.remove_o in PROMISE; eauto. des_ifs.
            eapply CONSISTENT; eauto. }
        { ss. }
      * ss.
Qed.

Lemma reorder_pf_step_cancels
      lang
      e1 th0 th1 th2
      (STEP1: @pred_step (promise_free /1\ (fun e => ~ is_cancel e)) lang
                         e1 th0 th1)
      (STEPS2: rtc (tau (@pred_step is_cancel _)) th1 th2)
      (LOCAL: Local.wf th0.(Thread.local) th0.(Thread.memory))
      (MEMORY: Memory.closed th0.(Thread.memory))
      (SC: Memory.closed_timemap (Thread.sc th0) (Thread.memory th0))
  :
    exists e1' th1',
      (<<STEPS1: rtc (tau (@pred_step is_cancel _)) th0 th1'>>) /\
      (<<STEP2: pred_step (promise_free /1\ (fun e => ~ is_cancel e)) e1' th1' th2>>) /\
      (<<EVT: ThreadEvent.get_machine_event e1' = ThreadEvent.get_machine_event e1>>)
.
Proof.
  ginduction STEPS2; i.
  - esplits; eauto.
  - inv H. exploit reorder_pf_step_cancel.
    { eapply STEP1. }
    { eapply TSTEP. }
    { eauto. }
    { eauto. }
    i. des.
    dup STEP0. inv STEP3. inv STEP. exploit Thread.step_future.
    { eapply STEP3. }
    { eauto. }
    { eauto. }
    { eauto. } i. des.
    exploit IHSTEPS2; eauto. i. des.
    esplits.
    + econs 2.
      * econs; eauto.
        unfold is_cancel in SAT. des_ifs.
      * eauto.
    + eauto.
    + etrans; eauto.
Qed.

Lemma pf_steps_cancels_not_cancels
      lang th0 th2
      (STEPS: rtc (tau (@pred_step promise_free lang)) th0 th2)
      (LOCAL: Local.wf th0.(Thread.local) th0.(Thread.memory))
      (MEMORY: Memory.closed th0.(Thread.memory))
      (SC: Memory.closed_timemap (Thread.sc th0) (Thread.memory th0))
  :
    exists th1,
      (<<STEPS1: rtc (tau (@pred_step is_cancel _)) th0 th1>>) /\
      (<<STEPS2: rtc (tau (@pred_step (promise_free /1\ (fun e => ~ is_cancel e)) _)) th1 th2>>)
.
Proof.
  ginduction STEPS; i.
  - esplits; eauto.
  - inv H. dup TSTEP. inv TSTEP0. inv STEP.
    exploit Thread.step_future; eauto. i. des.
    exploit IHSTEPS; eauto. i. des.
    destruct (classic (is_cancel e)).
    + esplits.
      * econs 2.
        { econs.
          - econs; eauto.
            econs. eapply STEP0.
          - unfold is_cancel in H. des_ifs. }
        { eapply STEPS1. }
      * eapply STEPS2.
    + exploit reorder_pf_step_cancels.
      { econs.
        - econs. eapply STEP0.
        - splits; auto. }
      { eapply STEPS1. }
      { eauto. }
      { eauto. }
      { eauto. }
      i. des. esplits.
      * eauto.
      * econs 2.
        { econs; eauto. etrans; eauto. }
        { eauto. }
Qed.


Lemma reorder_pf_step_cancel_no_sc
      lang
      e1 e2 th0 th1 th2
      (STEP1: @pred_step (no_sc /1\ (fun e => ~ is_cancel e)) lang
                         e1 th0 th1)
      (STEP2: pred_step is_cancel e2 th1 th2)
      (LOCAL: Local.wf th0.(Thread.local) th0.(Thread.memory))
      (MEMORY: Memory.closed th0.(Thread.memory)):
  exists e2' e1' th1',
    (<<STEP1: opt_pred_step is_cancel e2' th0 th1'>>) /\
    (<<STEP2: opt_pred_step (no_sc /1\ (fun e => ~ is_cancel e)) e1' th1' th2>>) /\
    (<<EVT: ThreadEvent.get_machine_event e1' = ThreadEvent.get_machine_event e1>>)
.
Proof.
  inv STEP1. inv STEP2. des. unfold is_cancel in SAT0. des_ifs.
  inv STEP0. inv STEP1; inv STEP0; [|inv LOCAL0]. ss.
  inv STEP. inv STEP0; ss.
  - inv STEP. ss. exploit reorder_promise_promise_cancel; eauto.
    { des_ifs. }
    i. des; clarify.
    { esplits.
      + econs 1.
      + econs 1.
      + ss.
    }
    { esplits.
      + econs 2. econs.
        * econs. econs 1. econs; eauto.
        * ss.
      + econs 2. econs.
        * econs. econs 1. econs; eauto.
        * ss.
      + ss.
    }
  - inv STEP. ss. inv LOCAL1; ss.
    + esplits.
      * econs 2. econs.
        { econs. econs 1. econs; eauto. }
        { ss. }
      * econs 2. econs.
        { econs. econs 2. econs; eauto; ss. }
        { ss. }
      * ss.
    + exploit reorder_read_cancel; eauto. i. des. esplits.
      * econs 2. econs.
        { econs. econs 1. econs; eauto. }
        { ss. }
      * econs 2. econs.
        { econs. econs 2. econs; eauto; ss. }
        { ss. }
      * ss.
    + exploit reorder_write_cancel; eauto. i. des. esplits.
      * econs 2. econs.
        { econs. econs 1. econs; eauto. }
        { ss. }
      * econs 2. econs.
        { econs. econs 2. econs; eauto; ss. }
        { ss. }
      * ss.
    + exploit reorder_write_cancel; eauto. i. des.
      exploit reorder_read_cancel; eauto. i. des.
      esplits.
      * econs 2. econs.
        { econs. econs 1. econs; eauto. }
        { ss. }
      * econs 2. econs.
        { econs. econs 2. econs; eauto; ss. }
        { ss. }
      * ss.
    + exploit reorder_fence_cancel; eauto. i. des. esplits.
      * econs 2. econs.
        { econs. econs 1. econs; eauto. }
        { ss. }
      * econs 2. econs.
        { econs. econs 2. econs; eauto; ss. }
        { ss. }
      * ss.
    + esplits.
      * econs 2. econs; eauto.
        { econs. econs 1. econs; eauto. }
        { ss. }
      * econs 2. econs.
        { econs. econs 2. econs.
          - instantiate (1:=ThreadEvent.failure). auto.
          - econs. econs. inv LOCAL2. inv LOCAL0. inv PROMISE.
            ii. ss. erewrite Memory.remove_o in PROMISE; eauto. des_ifs.
            eapply CONSISTENT; eauto. }
        { ss. }
      * ss.
Qed.

Lemma reorder_pf_step_cancels_no_sc
      lang
      e1 th0 th1 th2
      (STEP1: @opt_pred_step (no_sc /1\ (fun e => ~ is_cancel e)) lang
                         e1 th0 th1)
      (STEPS2: rtc (tau (@pred_step is_cancel _)) th1 th2)
      (LOCAL: Local.wf th0.(Thread.local) th0.(Thread.memory))
      (MEMORY: Memory.closed th0.(Thread.memory))
      (SC: Memory.closed_timemap (Thread.sc th0) (Thread.memory th0))
  :
    exists e1' th1',
      (<<STEPS1: rtc (tau (@pred_step is_cancel _)) th0 th1'>>) /\
      (<<STEP2: opt_pred_step (no_sc /1\ (fun e => ~ is_cancel e)) e1' th1' th2>>) /\
      (<<EVT: ThreadEvent.get_machine_event e1' = ThreadEvent.get_machine_event e1>>)
.
Proof.
  ginduction STEPS2; i.
  - esplits; eauto.
  - inv STEP1.
    { eexists _, z. esplits; eauto. econs. }
    inv H. exploit reorder_pf_step_cancel_no_sc.
    { eapply STEP. }
    { eapply TSTEP. }
    { eauto. }
    { eauto. }
    i. des. inv STEP1.
    { exploit IHSTEPS2; eauto. i. des.
      esplits.
      + eauto.
      + eauto.
      + etrans; eauto.
    }
    { dup STEP0. inv STEP1. inv STEP3. exploit Thread.step_future.
      { eapply STEP1. }
      { eauto. }
      { eauto. }
      { eauto. } i. des.
      exploit IHSTEPS2; eauto. i. des.
      esplits.
      + econs 2.
        * econs; eauto.
          unfold is_cancel in SAT. des_ifs.
        * eauto.
      + eauto.
      + etrans; eauto.
    }
Qed.

Lemma pf_steps_cancels_not_cancels_no_sc
      lang th0 th2
      (STEPS: rtc (tau (@pred_step no_sc lang)) th0 th2)
      (LOCAL: Local.wf th0.(Thread.local) th0.(Thread.memory))
      (MEMORY: Memory.closed th0.(Thread.memory))
      (SC: Memory.closed_timemap (Thread.sc th0) (Thread.memory th0))
  :
    exists th1,
      (<<STEPS1: rtc (tau (@pred_step is_cancel _)) th0 th1>>) /\
      (<<STEPS2: rtc (tau (@pred_step (no_sc /1\ (fun e => ~ is_cancel e)) _)) th1 th2>>)
.
Proof.
  ginduction STEPS; i.
  - esplits; eauto.
  - inv H. dup TSTEP. inv TSTEP0. inv STEP.
    exploit Thread.step_future; eauto. i. des.
    exploit IHSTEPS; eauto. i. des.
    destruct (classic (is_cancel e)).
    + esplits.
      * econs 2.
        { econs.
          - econs; eauto.
            econs. eapply STEP0.
          - unfold is_cancel in H. des_ifs. }
        { eapply STEPS1. }
      * eapply STEPS2.
    + exploit reorder_pf_step_cancels_no_sc.
      { econs 2. econs.
        - econs. eapply STEP0.
        - splits; auto. }
      { eapply STEPS1. }
      { eauto. }
      { eauto. }
      { eauto. }
      i. des. esplits.
      * eauto.
      * inv STEP2; eauto. econs 2.
        { econs; eauto. etrans; eauto. }
        { eauto. }
Qed.
