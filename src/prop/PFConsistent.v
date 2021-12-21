From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
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

Require Import PromiseConsistent.
Require Import ReorderPromises.

Set Implicit Arguments.


Definition pf_consistent lang (e:Thread.t lang): Prop :=
  forall mem1 (CAP: Memory.cap (Thread.memory e) mem1),
  exists e2,
    (<<STEPS: rtc (tau (Thread.step true)) (Thread.mk _ (Thread.state e) (Thread.local e) (Thread.sc e) mem1) e2>>) /\
    ((exists e e3,
         (<<STEP_FAILURE: Thread.step true e e2 e3 >>) /\
         (<<EVENT_FAILURE: ThreadEvent.get_machine_event e = MachineEvent.failure>>)) \/
     (<<PROMISES: (Local.promises (Thread.local e2)) = Memory.bot>>)).

Lemma promise_step_is_racy
      lc1 mem1 loc from to msg lc2 mem2 kind
      loc' ord
      (STEP: Local.promise_step lc1 mem1 loc from to msg lc2 mem2 kind)
      (RACE: Local.is_racy lc2 mem2 loc' ord):
  Local.is_racy lc1 mem1 loc' ord.
Proof.
  destruct lc1 as [tview1 promises1]. inv STEP. ss.
  inv RACE. ss. inv PROMISE; ss.
  { revert GET. erewrite Memory.add_o; eauto.
    revert GETP. erewrite Memory.add_o; eauto.
    condtac; ss; eauto.
  }
  { revert GET. erewrite Memory.split_o; eauto.
    revert GETP. erewrite Memory.split_o; eauto.
    repeat (condtac; ss); eauto.
  }
  { revert GET. erewrite Memory.lower_o; eauto.
    revert GETP. erewrite Memory.lower_o; eauto.
    condtac; ss; eauto.
  }
  { revert GET. erewrite Memory.remove_o; eauto.
    revert GETP. erewrite Memory.remove_o; eauto.
    condtac; ss; eauto.
  }
Qed.

Lemma rtc_union_step_nonpf_failure
      lang e1 e e2 e2'
      (STEP: rtc (union (@Thread.step lang false)) e1 e2)
      (FAILURE: Thread.step true e e2 e2')
      (EVENT: ThreadEvent.get_machine_event e = MachineEvent.failure)
  :
    exists e1',
      Thread.step true e e1 e1'.
Proof.
  ginduction STEP; eauto.
  i. exploit IHSTEP; eauto. i. des.
  exists (Thread.mk _ (Thread.state e1') (Thread.local x) (Thread.sc x) (Thread.memory x)).
  econs 2; eauto.
    inv H. inv USTEP. inv STEP0. ss.
  inv x0; inv STEP0; ss. inv LOCAL0; ss.
  - inv LOCAL1; ss.
    econs; eauto. econs; eauto. econs; eauto; ss.
    eapply promise_step_promise_consistent; eauto.
  - inv LOCAL1; ss.
    econs; eauto. econs; eauto. econs; eauto; ss.
    + eapply promise_step_is_racy; eauto.
    + eapply promise_step_promise_consistent; eauto.
  - econs; eauto. econs; eauto.
    inv LOCAL1; ss; eauto using promise_step_is_racy, promise_step_promise_consistent.
Qed.

Lemma consistent_pf_consistent lang (e:Thread.t lang)
      (WF: Local.wf (Thread.local e) (Thread.memory e))
      (SC: Memory.closed_timemap (Thread.sc e) (Thread.memory e))
      (MEM: Memory.closed (Thread.memory e))
      (CONSISTENT: Thread.consistent e)
  :
    pf_consistent e.
Proof.
  ii. exploit CONSISTENT; eauto. i. des.
  - inv FAILURE. des.
    hexploit tau_steps_pf_tau_steps; eauto; ss.
    { inv STEP_FAILURE; inv STEP; ss.
      inv LOCAL; ss; inv LOCAL0; ss.
    }
    { eapply Local.cap_wf; eauto. }
    { eapply Memory.cap_closed_timemap; eauto. }
    { eapply Memory.cap_closed; eauto. }
    i. des.
    exploit rtc_union_step_nonpf_failure.
    { eapply rtc_implies; [|eauto]. apply tau_union. }
    { eauto. }
    { eauto. }
    i. des.
    esplits; eauto.
  - exploit tau_steps_pf_tau_steps; eauto; ss.
    { ii. rewrite PROMISES, Memory.bot_get in *.  congr. }
    { eapply Local.cap_wf; eauto. }
    { eapply Memory.cap_closed_timemap; eauto. }
    { eapply Memory.cap_closed; eauto. }
    i. des.
    exploit rtc_union_step_nonpf_bot; [|eauto|].
    { eapply rtc_implies; [|eauto]. apply tau_union. }
    i. subst. esplits; eauto.
Qed.
