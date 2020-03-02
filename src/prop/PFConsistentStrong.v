Require Import Omega.
Require Import Bool.
Require Import RelationClasses.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Language.
From PromisingLib Require Import Loc.

Require Import Event.
Require Import Time.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Pred.

Require Import MemoryMerge.
Require Import PromiseConsistent.
Require Import PFConsistent.
Require Import ReorderCancel.
Require Import MemoryProps.

Set Implicit Arguments.


Definition pf_consistent_strong lang (e0:Thread.t lang): Prop :=
  forall mem1 sc1
         (CAP: Memory.cap e0.(Thread.memory) mem1),
  exists e1,
    (<<STEPS0: rtc (tau (@pred_step is_cancel lang)) (Thread.mk _ e0.(Thread.state) e0.(Thread.local) sc1 mem1) e1>>) /\
    (<<NORESERVE: no_reserves e1.(Thread.local).(Local.promises)>>) /\
    exists e2,
      (<<STEPS1: rtc (tau (@pred_step ((promise_free /1\ (fun e => ~ is_cancel e)) /1\ no_sc) lang)) e1 e2>>) /\
      (__guard__((exists st',
                     (<<LOCAL: Local.failure_step e2.(Thread.local)>>) /\
                     (<<FAILURE: Language.step lang ProgramEvent.failure (@Thread.state lang e2) st'>>)) \/
                 (<<PROMISES: e2.(Thread.local).(Local.promises) = Memory.bot>>))).

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

Lemma pf_consistent_pf_consistent_strong lang (th: Thread.t lang)
      (WF: Local.wf th.(Thread.local) th.(Thread.memory))
      (MEM: Memory.closed th.(Thread.memory))
      (CONSISTENT: pf_consistent th)
  :
    pf_consistent_strong th.
Proof.
  assert (INHABITED: Memory.inhabited th.(Thread.memory)).
  { inv MEM. auto. }
  ii. exploit Memory.max_concrete_timemap_exists; eauto. intros MAX. des.
  ii. exploit Memory.max_concrete_timemap_exists.
  { eapply le_inhabited; eauto. eapply Memory.cap_le; eauto. refl. }
  i. des. exploit CONSISTENT; eauto. i.

  assert (exists e2,
             (<<STEPS: rtc (tau (Thread.step true))
                           (Thread.mk _ (Thread.state th) (Thread.local th)
                                      tm0 mem1) e2 >>) /\
             (<<NORESERVES: no_reserves e2.(Thread.local).(Local.promises)>>) /\
             (__guard__ ((exists e3, (<< FAILURE: Thread.step true ThreadEvent.failure e2 e3 >>)) \/
                         (<<PROMISES: Local.promises (Thread.local e2) = Memory.bot >>)))).
  { des.
    - exploit Thread.rtc_tau_step_future.
      + eapply rtc_implies; [|apply STEPS].
        i. inv H. econs; eauto. econs; eauto.
      + ss. eapply Local.cap_wf; eauto.
      + ss. eapply Memory.max_concrete_timemap_closed; eauto.
      + ss. eapply Memory.cap_closed; eauto.
      + i. des.
        destruct e2. destruct local. inv WF2. ss.
        exploit reserves_cancelable; eauto. i. des.
        esplits.
        * etrans.
          { eapply STEPS. }
          { eapply rtc_implies; [|apply STEPS0].
            i. inv H. inv TSTEP. inv STEP.
            unfold is_cancel in SAT. des_ifs.
            inv STEP0; inv STEP.
            - econs; eauto. econs; eauto. econs; eauto.
            - inv LOCAL. }
        * ss.
        * left. inv FAILURE; inv STEP. inv LOCAL. inv LOCAL0.
          exists (Thread.mk _ st2 (Local.mk tview proms1) sc2 mem0).
          ss. econs 2. econs; eauto. econs; eauto. econs; eauto.
          eapply nacancels_promises_decrease in STEPS0; auto. ss.
          ii. eapply CONSISTENT0; eauto.
    - unguard. esplits; eauto. rewrite PROMISES. ii.
      rewrite Memory.bot_get in GET. clarify. }

  clear x. des.
  eapply pf_step_promise_free_step_rtc in STEPS.
  eapply pf_steps_cancels_not_cancels in STEPS; cycle 1.
  { ss. eapply Local.cap_wf; eauto. }
  { ss. eapply Memory.cap_closed; eauto. }
  { ss. eapply Memory.max_concrete_timemap_closed; eauto. } des.

  exploit Thread.rtc_tau_step_future.
  { eapply thread_steps_pred_steps. eapply STEPS1. }
  { ss. eapply Local.cap_wf; eauto. }
  { ss. eapply Memory.max_concrete_timemap_closed; eauto. }
  { ss. eapply Memory.cap_closed; eauto. }
  i. des. ss.

  destruct th1. exploit no_sc_any_sc_rtc; try apply STEPS1; ss.
  { i. unfold is_cancel in PR. des_ifs. }
  i. des. instantiate (1:=sc1) in STEP. clear STEPS1.

  eexists. splits.
  { eapply STEP. }
  { ss. ii. clarify.
    eapply steps_not_cancel_reserves_same in STEPS2; eauto.
    unguard. des.
    - eapply NORESERVES; eauto.
    - rewrite PROMISES in *. erewrite Memory.bot_get in STEPS2. clarify. }

  eapply hold_or_not with (Q := no_sc) in STEPS2. des.

  - destruct e2. ss.
    exploit no_sc_any_sc_rtc; try eapply HOLD; eauto.
    { ss. i. des. auto. } i. des.
    esplits.
    + eapply pred_step_rtc_mon; try eapply STEP0. i. ss.
    + ss. unguard. des.
      * left. ss. inv FAILURE; inv STEP1. inv LOCAL. eauto.
      * right. esplits; eauto.

  - exploit Thread.rtc_tau_step_future.
    { eapply thread_steps_pred_steps. eapply STEPS0. }
    { ss. }
    { ss. }
    { ss. } i. des.
    inv STEP0.
    exploit Thread.step_future; eauto. i. des.

    assert (PROMS: Local.promise_consistent e3.(Thread.local)).
    { eapply rtc_tau_step_promise_consistent.
      - eapply thread_steps_pred_steps. eapply STEPS1.
      - unguard. des.
        + inv FAILURE; inv STEP0. inv LOCAL. inv LOCAL0. ss.
        + ii. rewrite PROMISES in PROMISE.
          rewrite Memory.bot_get in PROMISE. clarify.
      - eauto.
      - eauto.
      - eauto. }

    assert (NOPROMISE: e2'.(Thread.local).(Local.promises) = Memory.bot).
    { apply Memory.ext. i. rewrite Memory.bot_get.
      destruct (Memory.get loc ts (Local.promises (Thread.local e2')))
        as [[from [val released|]]|] eqn:GET; auto; cycle 1.
      - exfalso.
        eapply step_not_cancel_reserves_same in GET; cycle 1.
        + econs.
          * econs; eauto.
          * instantiate (1:=promise_free /1\ (fun e => ~ is_cancel e)). ss.
        + ss.
        + des. eapply steps_not_cancel_reserves_same in GET; eauto.
          des. eapply NORESERVES; eauto.
      - exfalso.
        exploit pf_step_rtc_promises_decrease.
        { eapply STEPS0. }
        { i. ss. des. auto. }
        { econs; eauto. } ss. i.
        exploit pf_step_rtc_promises_decrease.
        { eapply STEP. }
        { i. unfold is_cancel in *. des_ifs. }
        { ss. eauto. }
        ss. i. inv x2.
        ss. unfold no_sc in BREAKQ. des_ifs; try by (exfalso; eauto).
        + des; clarify. apply NNPP in BREAKQ.
          inv STEP1; inv STEP0. ss. inv LOCAL. inv LOCAL0. ss.
          eapply PROMS in GET. ss. des_ifs. ss.
          hexploit max_concrete_timemap_get; eauto.
          * inv WF. eapply Memory.cap_le; eauto.
          * i. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt; eauto.
        + inv STEP1; inv STEP0. ss. inv LOCAL. inv LOCAL0. ss.
          eapply PROMS in GET. ss. des_ifs. ss.
          hexploit max_concrete_timemap_get; eauto.
          * inv WF. eapply Memory.cap_le; eauto.
          * i. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt; eauto.
    }

    destruct e2'. destruct local. ss.
    eapply no_sc_any_sc_rtc in STEPS0; ss; cycle 1.
    { i. des; ss. } des.
    esplits.
    * eapply pred_step_rtc_mon; eauto. i. ss.
    * unguard. ss. eauto.
Qed.
