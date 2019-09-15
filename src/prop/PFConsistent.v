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

Require Import PromiseConsistent.
Require Import ReorderPromises.

Set Implicit Arguments.


Definition pf_consistent lang (e:Thread.t lang): Prop :=
  forall mem1 sc1
         (WF: Local.wf e.(Thread.local) e.(Thread.memory))
         (MEM: Memory.closed e.(Thread.memory))
         (CAP: Memory.cap e.(Thread.local).(Local.promises) e.(Thread.memory) mem1)
         (SC_MAX: Memory.max_full_timemap mem1 sc1),
    (<<FAILURE: Thread.steps_failure (Thread.mk _ e.(Thread.state) e.(Thread.local) sc1 mem1)>>) \/
    exists e2,
      (<<STEPS: rtc (tau (Thread.step true)) (Thread.mk _ e.(Thread.state) e.(Thread.local) sc1 mem1) e2>>) /\
      (<<PROMISES: e2.(Thread.local).(Local.promises) = Memory.bot>>).

Lemma consistent_pf_consistent:
  Thread.consistent <2= pf_consistent.
Proof.
  s. ii. exploit PR; eauto. i. des.
  - inv FAILURE. des. left. red. econs.
    hexploit tau_steps_pf_tau_steps; eauto; ss.
    { inv FAILURE; inv STEP. inv LOCAL. inv LOCAL0.
      hexploit rtc_tau_step_promise_consistent; eauto; ss.
      { eapply Local.cap_wf; eauto. }
      { eapply Memory.max_full_timemap_closed; eauto. }
      { eapply Memory.cap_closed; eauto. }
    }
    { eapply Local.cap_wf; eauto. }
    { eapply Memory.max_full_timemap_closed; eauto. }
    { eapply Memory.cap_closed; eauto. }
  - exploit tau_steps_pf_tau_steps; eauto; ss.
    { ii. rewrite PROMISES, Memory.bot_get in *.  congr. }
    { eapply Local.cap_wf; eauto. }
    { eapply Memory.max_full_timemap_closed; eauto. }
    { eapply Memory.cap_closed; eauto. }
    i. des.
    exploit rtc_union_step_nonpf_bot; [|eauto|].
    { eapply rtc_implies; [|eauto]. apply tau_union. }
    i. subst. esplits; eauto.
Qed.
