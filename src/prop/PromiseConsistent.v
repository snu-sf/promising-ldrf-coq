Require Import Omega.
Require Import RelationClasses.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Loc.

Require Import Event.
Require Import Time.
From PromisingLib Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.

Require Import SimMemory.
Require Import SimPromises.
Require Import SimLocal.
Require Import FulfillStep.
Require Import MemoryReorder.
Require Import Configuration.

Set Implicit Arguments.


Lemma promise_step_promise_consistent
      lc1 mem1 loc from to msg lc2 mem2 kind
      (STEP: Local.promise_step lc1 mem1 loc from to msg lc2 mem2 kind)
      (CONS: Local.promise_consistent lc2):
  Local.promise_consistent lc1.
Proof.
  inv STEP. ii.
  exploit Memory.promise_get1_promise; eauto. i. des.
  exploit CONS; eauto.
Qed.

Lemma read_step_promise_consistent
      lc1 mem1 loc to val released ord lc2
      (STEP: Local.read_step lc1 mem1 loc to val released ord lc2)
      (CONS: Local.promise_consistent lc2):
  Local.promise_consistent lc1.
Proof.
  inv STEP. ii. exploit CONS; eauto. i.
  eapply TimeFacts.le_lt_lt; eauto. ss.
  etrans; [|apply Time.join_l]. etrans; [|apply Time.join_l]. refl.
Qed.

Lemma fulfill_unset_promises
      loc from ts msg
      promises1 promises2
      l t f m
      (FULFILL: Memory.remove promises1 loc from ts msg promises2)
      (TH1: Memory.get l t promises1 = Some (f, m))
      (TH2: Memory.get l t promises2 = None):
  l = loc /\ t = ts /\ f = from /\ Message.le msg m.
Proof.
  revert TH2. erewrite Memory.remove_o; eauto. condtac; ss; [|congr].
  des. subst. exploit Memory.remove_get0; eauto. i. des.
  rewrite GET in TH1. inv TH1.
  esplits; eauto. refl.
Qed.

Lemma write_step_promise_consistent
      lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind
      (STEP: Local.write_step lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind)
      (CONS: Local.promise_consistent lc2):
  Local.promise_consistent lc1.
Proof.
  inv STEP. ii.
  destruct (Memory.get loc0 ts promises2) as [[]|] eqn:X.
  - apply CONS in X. eapply TimeFacts.le_lt_lt; eauto.
    s. etrans; [|apply Time.join_l]. refl.
  - inv WRITE.
    exploit Memory.promise_get1_promise; eauto. i. des.
    exploit fulfill_unset_promises; eauto. i. des. subst.
    apply WRITABLE.
Qed.

Lemma fulfill_step_promise_consistent
      lc1 sc1 loc from to val releasedm released ord lc2 sc2
      (STEP: fulfill_step lc1 sc1 loc from to val releasedm released ord lc2 sc2)
      (CONS: Local.promise_consistent lc2):
  Local.promise_consistent lc1.
Proof.
  inv STEP. ii.
  destruct (Memory.get loc0 ts promises2) as [[]|] eqn:X.
  - apply CONS in X. eapply TimeFacts.le_lt_lt; eauto.
    s. etrans; [|apply Time.join_l]. refl.
  - exploit fulfill_unset_promises; eauto. i. des. subst.
    apply WRITABLE.
Qed.

Lemma fence_step_promise_consistent
      lc1 sc1 mem1 ordr ordw lc2 sc2
      (STEP: Local.fence_step lc1 sc1 ordr ordw lc2 sc2)
      (WF: Local.wf lc1 mem1)
      (SC: Memory.closed_timemap sc1 mem1)
      (MEM: Memory.closed mem1)
      (CONS: Local.promise_consistent lc2):
  Local.promise_consistent lc1.
Proof.
  exploit Local.fence_step_future; eauto. i. des.
  inversion STEP. subst. ii. exploit CONS; eauto. i.
  eapply TimeFacts.le_lt_lt; eauto. apply TVIEW_FUTURE.
Qed.

Lemma ordering_relaxed_dec
      ord:
  Ordering.le ord Ordering.relaxed \/ Ordering.le Ordering.strong_relaxed ord.
Proof. destruct ord; auto. Qed.

Lemma step_promise_consistent
      lang pf e th1 th2
      (STEP: @Thread.step lang pf e th1 th2)
      (CONS: Local.promise_consistent th2.(Thread.local))
      (WF1: Local.wf th1.(Thread.local) th1.(Thread.memory))
      (SC1: Memory.closed_timemap th1.(Thread.sc) th1.(Thread.memory))
      (MEM1: Memory.closed th1.(Thread.memory)):
  Local.promise_consistent th1.(Thread.local).
Proof.
  inv STEP; [inv STEP0|inv STEP0; inv LOCAL]; ss.
  - eapply promise_step_promise_consistent; eauto.
  - eapply read_step_promise_consistent; eauto.
  - eapply write_step_promise_consistent; eauto.
  - eapply read_step_promise_consistent; eauto.
    eapply write_step_promise_consistent; eauto.
  - eapply fence_step_promise_consistent; eauto.
  - eapply fence_step_promise_consistent; eauto.
Qed.

Lemma rtc_all_step_promise_consistent
      lang th1 th2
      (STEP: rtc (@Thread.all_step lang) th1 th2)
      (CONS: Local.promise_consistent th2.(Thread.local))
      (WF1: Local.wf th1.(Thread.local) th1.(Thread.memory))
      (SC1: Memory.closed_timemap th1.(Thread.sc) th1.(Thread.memory))
      (MEM1: Memory.closed th1.(Thread.memory)):
  Local.promise_consistent th1.(Thread.local).
Proof.
  revert_until STEP. induction STEP; auto. i.
  inv H. inv USTEP. exploit Thread.step_future; eauto. i. des.
  eapply step_promise_consistent; eauto.
Qed.

Lemma rtc_tau_step_promise_consistent
      lang th1 th2
      (STEP: rtc (@Thread.tau_step lang) th1 th2)
      (CONS: Local.promise_consistent th2.(Thread.local))
      (WF1: Local.wf th1.(Thread.local) th1.(Thread.memory))
      (SC1: Memory.closed_timemap th1.(Thread.sc) th1.(Thread.memory))
      (MEM1: Memory.closed th1.(Thread.memory)):
  Local.promise_consistent th1.(Thread.local).
Proof.
  eapply rtc_all_step_promise_consistent; cycle 1; eauto.
  eapply rtc_implies; [|eauto].
  apply tau_union.
Qed.

Lemma consistent_promise_consistent
      lang th
      (CONS: @Thread.consistent lang th)
      (WF: Local.wf th.(Thread.local) th.(Thread.memory))
      (SC: Memory.closed_timemap th.(Thread.sc) th.(Thread.memory))
      (MEM: Memory.closed th.(Thread.memory)):
  Local.promise_consistent th.(Thread.local).
Proof.
  destruct th. ss.
  exploit Memory.cap_exists; eauto. i. des.
  exploit Memory.future_closed; eauto. i.
  exploit Local.cap_wf; eauto. i.
  exploit Memory.max_full_timemap_exists; try apply x0. i. des.
  hexploit Memory.max_full_timemap_closed; eauto. i.
  exploit CONS; eauto. s. i. des.
  - inv ABORT. des. inv ABORT; inv STEP. inv LOCAL. inv LOCAL0.
    hexploit rtc_tau_step_promise_consistent; try exact STEPS; eauto.
  - hexploit rtc_tau_step_promise_consistent; try exact STEPS; eauto.
    ii. rewrite PROMISES, Memory.bot_get in *. congr.
Qed.

Lemma promise_consistent_promise_read
      lc1 mem1 loc to val ord released lc2
      f t m
      (STEP: Local.read_step lc1 mem1 loc to val released ord lc2)
      (PROMISE: Memory.get loc t lc1.(Local.promises) = Some (f, m))
      (CONS: Local.promise_consistent lc2):
  Time.lt to t.
Proof.
  inv STEP. exploit CONS; eauto. s. i.
  apply TimeFacts.join_lt_des in x. des.
  apply TimeFacts.join_lt_des in AC. des.
  revert BC0. unfold View.singleton_ur_if. condtac; ss.
  - unfold TimeMap.singleton, FLocFun.add. condtac; ss.
  - unfold TimeMap.singleton, FLocFun.add. condtac; ss.
Qed.

Lemma promise_consistent_promise_write
      lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind
      f t m
      (STEP: Local.write_step lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind)
      (PROMISE: Memory.get loc t lc1.(Local.promises) = Some (f, m))
      (CONS: Local.promise_consistent lc2):
  Time.le to t.
Proof.
  destruct (Memory.get loc t (Local.promises lc2)) as [[]|] eqn:X.
  - inv STEP. inv WRITE.
    exploit CONS; eauto. i. ss.
    apply TimeFacts.join_lt_des in x. des.
    left. revert BC. unfold TimeMap.singleton, FLocFun.add. condtac; ss.
  - inv STEP. inv WRITE.
    exploit Memory.promise_get1_promise; eauto. i. des.
    exploit fulfill_unset_promises; eauto. i. des. subst. refl.
Qed.
