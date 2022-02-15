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


Lemma reorder_abort_reserve
      lang
      pf th0 th1 th2
      (STEP0: @Thread.step lang pf ThreadEvent.failure th0 th1)
      (STEP1: Thread.reserve_step th1 th2)
  :
    exists th1',
      (<<STEP0: Thread.reserve_step th0 th1'>>) /\
      (<<STEP1: Thread.step pf ThreadEvent.failure th1' th2>>).
Proof.
  inv STEP1. inv STEP; inv STEP1; inv LOCAL.
  inv STEP0; inv STEP. inv LOCAL. inv LOCAL0. esplits.
  { econs; eauto. econs; eauto. econs; eauto. }
  { econs 2; eauto. econs; eauto. econs; eauto. econs.
    ii. inv PROMISE. erewrite Memory.add_o in PROMISE0; eauto. des_ifs.
    eapply CONSISTENT; eauto. }
Qed.

Lemma reorder_abort_reserves
      lang
      pf th0 th1 th2
      (STEP: Thread.step pf ThreadEvent.failure th0 th1)
      (STEPS: rtc (@Thread.reserve_step lang) th1 th2)
  :
    exists th1',
      (<<STEPS: rtc (@Thread.reserve_step lang) th0 th1'>>) /\
      (<<STEP: Thread.step pf ThreadEvent.failure th1' th2>>).
Proof.
  ginduction STEPS; eauto. i.
  exploit reorder_abort_reserve; eauto. i. des.
  exploit IHSTEPS; eauto. i. des. esplits.
  { econs 2; eauto. }
  { eauto. }
Qed.

Lemma reorder_reserve_promise
      lc0 mem0
      lc1 mem1
      lc2 mem2
      loc1 from1 to1
      loc2 from2 to2 msg2 kind2
      (STEP1: Local.promise_step lc0 mem0 loc1 from1 to1 Message.reserve lc1 mem1 Memory.op_kind_add)
      (STEP2: Local.promise_step lc1 mem1 loc2 from2 to2 msg2 lc2 mem2 kind2):
  (loc1 = loc2 /\ from1 = from2 /\ to1 = to2 /\ msg2 = Message.reserve /\ kind2 = Memory.op_kind_cancel /\
   lc0 = lc2 /\ mem0 = mem2) \/
  (exists lc1' mem1',
      <<STEP1: Local.promise_step lc0 mem0 loc2 from2 to2 msg2 lc1' mem1' kind2>> /\
      <<STEP2: Local.promise_step lc1' mem1' loc1 from1 to1 Message.reserve lc2 mem2 Memory.op_kind_add>>).
Proof.
  inv STEP1. inv STEP2. ss.
  exploit MemoryReorder.reserve_promise; eauto. i. des; subst.
  { left. splits; auto. destruct lc0; auto. }
  right. esplits.
  { econs; eauto. inv STEP2.
    eapply memory_concrete_le_closed_msg; try apply CLOSED0.
    ii. erewrite (@Memory.add_o mem2 mem1') in GET; eauto. des_ifs. }
  { econs; eauto. }
Qed.

Lemma add_non_synch_loc loc0 prom0 loc1 from to msg prom1
      (NONSYNCH: Memory.nonsynch_loc loc0 prom1)
      (ADD: Memory.add prom0 loc1 from to msg prom1)
  :
    Memory.nonsynch_loc loc0 prom0.
Proof.
  ii. eapply Memory.add_get1 in GET; eauto.
  des_ifs. exploit NONSYNCH; eauto.
Qed.

Lemma add_non_synch prom0 loc from to msg prom1
      (NONSYNCH: Memory.nonsynch prom1)
      (ADD: Memory.add prom0 loc from to msg prom1)
  :
    Memory.nonsynch prom0.
Proof.
  ii. eapply Memory.add_get1 in GET; eauto.
  des_ifs. exploit NONSYNCH; eauto.
Qed.

Lemma reorder_reserve_read
      lc0 mem0
      lc1 mem1
      lc2
      loc1 from1 to1
      loc2 to2 val2 released2 ord2
      (STEP1: Local.promise_step lc0 mem0 loc1 from1 to1 Message.reserve lc1 mem1 Memory.op_kind_add)
      (STEP2: Local.read_step lc1 mem1 loc2 to2 val2 released2 ord2 lc2)
  :
    exists lc1',
      (<<STEP1: Local.read_step lc0 mem0 loc2 to2 val2 released2 ord2 lc1'>>) /\
      (<<STEP2: Local.promise_step lc1' mem0 loc1 from1 to1 Message.reserve lc2 mem1 Memory.op_kind_add>>).
Proof.
  inv STEP1. inv STEP2. esplits; eauto.
  { econs; eauto. inv PROMISE.
    erewrite Memory.add_o in GET; eauto. des_ifs. eauto. }
  { econs; eauto. }
Qed.

Lemma reorder_reserve_write
      lc0 sc0 mem0
      lc1 mem1
      lc2 sc2 mem2
      loc1 from1 to1
      loc2 from2 to2 val2 releasedm2 released2 ord2 kind2
      (STEP1: Local.promise_step lc0 mem0 loc1 from1 to1 Message.reserve lc1 mem1 Memory.op_kind_add)
      (STEP2: Local.write_step lc1 sc0 mem1 loc2 from2 to2 val2 releasedm2 released2 ord2 lc2 sc2 mem2 kind2)
  :
    exists lc1' mem1',
      (<<STEP1: Local.write_step lc0 sc0 mem0 loc2 from2 to2 val2 releasedm2 released2 ord2 lc1' sc2 mem1' kind2>>) /\
      (<<STEP2: Local.promise_step lc1' mem1' loc1 from1 to1 Message.reserve lc2 mem2 Memory.op_kind_add>>).
Proof.
  inv STEP1. inv STEP2. ss.
  exploit MemoryReorder.reserve_write; eauto; ss. i. des.
  esplits.
  { econs; eauto. i. inv PROMISE. eapply add_non_synch_loc; eauto. }
  { econs; eauto. }
Qed.

Lemma reorder_reserve_write_na
      lc0 sc0 mem0
      lc1 mem1
      lc2 sc2 mem2
      loc1 from1 to1
      loc2 from2 to2 val2 ord2 msgs2 kinds2 kind2
      (STEP1: Local.promise_step lc0 mem0 loc1 from1 to1 Message.reserve lc1 mem1 Memory.op_kind_add)
      (STEP2: Local.write_na_step lc1 sc0 mem1 loc2 from2 to2 val2 ord2 lc2 sc2 mem2 msgs2 kinds2 kind2)
  :
    exists lc1' mem1',
      (<<STEP1: Local.write_na_step lc0 sc0 mem0 loc2 from2 to2 val2 ord2 lc1' sc2 mem1' msgs2 kinds2 kind2>>) /\
      (<<STEP2: Local.promise_step lc1' mem1' loc1 from1 to1 Message.reserve lc2 mem2 Memory.op_kind_add>>).
Proof.
  inv STEP1. inv STEP2. ss.
  exploit MemoryReorder.reserve_write_na; eauto; ss. i. des.
  esplits; eauto.
Qed.

Lemma reorder_reserve_fence
      lc0 mem0
      lc1 mem1
      lc2
      loc1 from1 to1
      ord1 ord2 sc0 sc1
      (STEP1: Local.promise_step lc0 mem0 loc1 from1 to1 Message.reserve lc1 mem1 Memory.op_kind_add)
      (STEP2: Local.fence_step lc1 sc0 ord1 ord2 lc2 sc1)
  :
    exists lc1',
      (<<STEP1: Local.fence_step lc0 sc0 ord1 ord2 lc1' sc1>>) /\
      (<<STEP2: Local.promise_step lc1' mem0 loc1 from1 to1 Message.reserve lc2 mem1 Memory.op_kind_add>>).
Proof.
  inv STEP1. inv STEP2. ss. esplits.
  - econs; eauto.
    + inv PROMISE. i. eapply add_non_synch; eauto.
    + i. ss. subst. erewrite PROMISES in *; auto.
      inv PROMISE. eapply Memory.add_get0 in PROMISES0. des.
      erewrite Memory.bot_get in *. ss.
  - econs; eauto.
Qed.

Lemma reorder_reserve_promise_consistent
      lc0 mem0 loc1 from1 to1 lc1 mem1
      (STEP1: Local.promise_step lc0 mem0 loc1 from1 to1 Message.reserve lc1 mem1 Memory.op_kind_add)
      (CONS: Local.promise_consistent lc1):
  Local.promise_consistent lc0.
Proof.
  inv STEP1. inv PROMISE.
  ii. eapply Memory.add_get1 in PROMISE; eauto.
Qed.

Lemma reorder_reserve_failure
      lc0 mem0 loc1 from1 to1 lc1 mem1
      (STEP1: Local.promise_step lc0 mem0 loc1 from1 to1 Message.reserve lc1 mem1 Memory.op_kind_add)
      (STEP2: Local.failure_step lc1):
  Local.failure_step lc0.
Proof.
  inv STEP2. econs.
  eapply reorder_reserve_promise_consistent; eauto.
Qed.

Lemma reorder_reserve_is_racy
      lc0 mem0 loc1 from1 to1 lc1 mem1
      loc2 to2 ord2
      (STEP1: Local.promise_step lc0 mem0 loc1 from1 to1 Message.reserve lc1 mem1 Memory.op_kind_add)
      (STEP2: Local.is_racy lc1 mem1 loc2 to2 ord2):
  Local.is_racy lc0 mem0 loc2 to2 ord2.
Proof.
  inv STEP1. inv PROMISE. inv STEP2. ss.
  revert GET. erewrite Memory.add_o; eauto.
  revert GETP. erewrite Memory.add_o; eauto.
  condtac; ss; try congr. i.
  econs; eauto.
Qed.

Lemma reorder_reserve_racy_read
      lc0 mem0 loc1 from1 to1 lc1 mem1
      loc2 to2 val2 ord2
      (STEP1: Local.promise_step lc0 mem0 loc1 from1 to1 Message.reserve lc1 mem1 Memory.op_kind_add)
      (STEP2: Local.racy_read_step lc1 mem1 loc2 to2 val2 ord2):
  Local.racy_read_step lc0 mem0 loc2 to2 val2 ord2.
Proof.
  inv STEP2. econs.
  eapply reorder_reserve_is_racy; eauto.
Qed.

Lemma reorder_reserve_racy_write
      lc0 mem0 loc1 from1 to1 lc1 mem1
      loc2 to2 ord2
      (STEP1: Local.promise_step lc0 mem0 loc1 from1 to1 Message.reserve lc1 mem1 Memory.op_kind_add)
      (STEP2: Local.racy_write_step lc1 mem1 loc2 to2 ord2):
  Local.racy_write_step lc0 mem0 loc2 to2 ord2.
Proof.
  inv STEP2. econs.
  - eapply reorder_reserve_is_racy; eauto.
  - eapply reorder_reserve_promise_consistent; eauto.
Qed.

Lemma reorder_reserve_racy_update
      lc0 mem0 loc1 from1 to1 lc1 mem1
      loc2 to2 ordr2 ordw2
      (STEP1: Local.promise_step lc0 mem0 loc1 from1 to1 Message.reserve lc1 mem1 Memory.op_kind_add)
      (STEP2: Local.racy_update_step lc1 mem1 loc2 to2 ordr2 ordw2):
  Local.racy_update_step lc0 mem0 loc2 to2 ordr2 ordw2.
Proof.
  inv STEP2.
  - econs 1; eauto.
    eapply reorder_reserve_promise_consistent; eauto.
  - econs 2; eauto.
    eapply reorder_reserve_promise_consistent; eauto.
  - econs 3; eauto.
    + eapply reorder_reserve_is_racy; eauto.
    + eapply reorder_reserve_promise_consistent; eauto.
Qed.

Lemma reorder_reserve_step
      lang
      pf1 pf2 e1 e2 th0 th1 th2
      (STEP1: @Thread.step lang pf1 e1 th0 th1)
      (STEP2: Thread.step pf2 e2 th1 th2)
      (RESERVE: ThreadEvent.is_reserve e1)
  :
  (exists th1',
    (<<STEP1: Thread.step pf2 e2 th0 th1'>>) /\
    (<<STEP2: Thread.step pf1 e1 th1' th2>>)) \/
  (th2 = th0 /\ <<CANCEL: ThreadEvent.is_cancel e2>>)
.
Proof.
  unfold ThreadEvent.is_reserve in *. des_ifs.
  inv STEP1; inv STEP; [|inv LOCAL]. ss.
  inv STEP2; ss.
  - inv STEP. ss. exploit reorder_reserve_promise; eauto.
    i. des; clarify; eauto.
    left. esplits.
    + econs 1. econs; eauto.
    + econs 1. econs; eauto.
  - left. inv STEP. ss. inv LOCAL0; ss.
    + esplits.
      * econs 2. econs; eauto.
      * econs 1. econs; eauto; ss.
    + exploit reorder_reserve_read; eauto. i. des. esplits.
      * econs 2. econs; eauto.
      * econs 1. econs; eauto; ss.
    + exploit reorder_reserve_write; eauto. i. des. esplits.
      * econs 2. econs; eauto.
      * econs 1. econs; eauto; ss.
    + exploit reorder_reserve_read; eauto. i. des.
      exploit reorder_reserve_write; eauto. i. des.
      esplits.
      * econs 2. econs; eauto.
      * econs 1. econs; eauto; ss.
    + exploit reorder_reserve_fence; eauto. i. des. esplits.
      * econs 2. econs; eauto.
      * econs 1. econs; eauto; ss.
    + exploit reorder_reserve_fence; eauto. i. des. esplits.
      * econs 2. econs; eauto.
      * econs 1. econs; eauto; ss.
    + exploit reorder_reserve_failure; eauto. i. esplits.
      * econs 2. econs; eauto.
      * econs 1. econs; eauto; ss.
    + exploit reorder_reserve_write_na; eauto. i. des. esplits.
      * econs 2. econs; eauto.
      * econs 1. econs; eauto; ss.
    + exploit reorder_reserve_racy_read; eauto. i. esplits.
      * econs 2. econs; eauto.
      * econs 1. econs; eauto; ss.
    + exploit reorder_reserve_racy_write; eauto. i. esplits.
      * econs 2. econs; eauto.
      * econs 1. econs; eauto; ss.
    + exploit reorder_reserve_racy_update; eauto. i. esplits.
      * econs 2. econs; eauto.
      * econs 1. econs; eauto; ss.
Qed.

Lemma reorder_reserves_step
      lang
      pf e2 th0 th1 th2
      (STEPS1: rtc (@Thread.reserve_step lang) th0 th1)
      (STEP2: Thread.step pf e2 th1 th2)
  :
    (exists th1',
        (<<STEP1: Thread.step pf e2 th0 th1'>>) /\
        (<<STEPS2: rtc (@Thread.reserve_step lang) th1' th2>>)) \/
    ((<<STEPS1: rtc (@Thread.reserve_step lang) th0 th2>>) /\ (<<CANCEL: ThreadEvent.is_cancel e2>>))
.
Proof.
  eapply Operators_Properties.clos_rt_rt1n_iff in STEPS1.
  eapply Operators_Properties.clos_rt_rtn1_iff in STEPS1.
  ginduction STEPS1; i.
  - esplits; eauto.
  - inv H. exploit reorder_reserve_step.
    { eapply STEP. }
    { eapply STEP2. }
    { ss. }
    i. des.
    { exploit IHSTEPS1; try apply STEP1. i. des.
      - left. esplits.
        + eauto.
        + etrans.
          { eauto. }
          { econs 2; [|refl]. econs; eauto. }
      - right. esplits; eauto. etrans.
        + eauto.
        + econs 2; [|refl]. econs; eauto.
    }
    { subst. right.
      eapply Operators_Properties.clos_rt_rtn1_iff in STEPS1.
      eapply Operators_Properties.clos_rt_rt1n_iff in STEPS1. auto. }
Qed.

Lemma reorder_reserves_opt_step
      lang
      e2 th0 th1 th2
      (STEPS1: rtc (@Thread.reserve_step lang) th0 th1)
      (STEP2: Thread.opt_step e2 th1 th2)
  :
    (exists th1',
        (<<STEP1: Thread.opt_step e2 th0 th1'>>) /\
        (<<STEPS2: rtc (@Thread.reserve_step lang) th1' th2>>)) \/
    ((<<STEPS1: rtc (@Thread.reserve_step lang) th0 th2>>) /\ (<<CANCEL: ThreadEvent.is_cancel e2>>)).
Proof.
  inv STEP2.
  { left. esplits; eauto. econs 1. }
  { exploit reorder_reserves_step; eauto. i. des.
    { left. esplits; eauto. econs 2; eauto. }
    { right. esplits; eauto. }
  }
Qed.

Lemma reorder_reserves_opt_step2
      lang
      e2 th0 th1 th2
      (STEPS1: rtc (@Thread.reserve_step lang) th0 th1)
      (STEP2: Thread.opt_step e2 th1 th2)
  :
    exists th1' e2',
      (<<STEP1: Thread.opt_step e2' th0 th1'>>) /\
      (<<STEPS2: rtc (@Thread.reserve_step lang) th1' th2>>) /\
      __guard__(e2' = e2 \/ e2' = ThreadEvent.silent /\ <<CANCEL: ThreadEvent.is_cancel e2>>).
Proof.
  unguard. inv STEP2.
  { esplits.
    { econs 1. }
    { eauto. }
    { auto. }
  }
  { exploit reorder_reserves_step; eauto. i. des.
    { esplits; eauto. econs 2; eauto. }
    { esplits; eauto. econs 1; eauto. }
  }
Qed.

Lemma steps_not_reserves_reserves
      P lang th0 th2
      (STEPS: rtc (tau (@pred_step P lang)) th0 th2)
  :
    exists th1,
      (<<STEPS1: rtc (tau (@pred_step (P /1\ fun e => ~ ThreadEvent.is_reserve e) _)) th0 th1>>) /\
      (<<STEPS2: rtc (@Thread.reserve_step _) th1 th2>>)
.
Proof.
  eapply Operators_Properties.clos_rt_rt1n_iff in STEPS.
  eapply Operators_Properties.clos_rt_rtn1_iff in STEPS.
  ginduction STEPS; i.
  - esplits; eauto.
  - inv H. inv TSTEP. inv STEP.
    hexploit IHSTEPS; eauto. i. des.
    destruct (classic (ThreadEvent.is_reserve e)).
    + unfold ThreadEvent.is_cancel in H. des_ifs. esplits.
      * eapply STEPS1.
      * etrans; eauto. econs 2; [|refl].
        unfold ThreadEvent.is_reserve in *. des_ifs. econs; eauto.
    + exploit reorder_reserves_step.
      { eapply STEPS2. }
      { eapply STEP0. }
      i. des; eauto. esplits.
      * etrans.
        { eauto. }
        { econs 2; [|refl]. econs; eauto.
          econs; eauto. econs; eauto. }
      * eauto.
Qed.
