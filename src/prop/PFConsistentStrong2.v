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
Require Import PFConsistentStrong.
Require Import ReorderCancel.
Require Import MemoryProps.
Require Import Mapping.
Require Import CapFlex.
Require Import GoodFuture.

Set Implicit Arguments.

Inductive promise_writing_event
          (loc: Loc.t) (from to: Time.t) (val: Const.t) (released: option View.t)
  : forall (e: ThreadEvent.t), Prop :=
| writing_event_write
    from' released' ord
    (FROM: Time.le from from')
    (RELEASED: View.opt_le released' released)
    (ORD: Ordering.le ord Ordering.relaxed)
  :
    promise_writing_event
      loc from to val released
      (ThreadEvent.write loc from' to val released' ord)
| writing_event_update
    from' released' ord valr releasedr ordr
    (FROM: Time.le from from')
    (RELEASED: View.opt_le released' released)
    (ORD: Ordering.le ord Ordering.relaxed)
  :
    promise_writing_event
      loc from to val released
      (ThreadEvent.update loc from' to valr val releasedr released' ordr ord)
.
Hint Constructors promise_writing_event.

Lemma promise_writing_event_mon loc from to val released from' released' e
      (FROM: Time.le from from')
      (RELEASED: View.opt_le released' released)
      (WRITING: promise_writing_event loc from' to val released' e)
  :
    promise_writing_event loc from to val released e.
Proof.
  inv WRITING; econs; try by (etrans; eauto).
Qed.

Lemma promise_promise_decrease prom0 mem0 prom1 mem1
      l f t m k
      (PROMISE: Memory.promise prom0 mem0 l f t m prom1 mem1 k)
      loc from to val released
      (GET: Memory.get loc to prom0 = Some (from, Message.concrete val released))
  :
    exists from' released',
      (<<FROM: Time.le from from'>>) /\
      (<<RELEASED: View.opt_le released' released>>) /\
      (<<GET: Memory.get loc to prom1 = Some (from', Message.concrete val released')>>).
Proof.
  inv PROMISE.
  { eapply Memory.add_get1 in GET; eauto.
    exists from, released. splits; auto; try by refl. }
  { eapply Memory.split_get1 in GET; eauto. des.
    exists f', released. splits; auto; try by refl. }
  { eapply Memory.lower_get1 in GET; eauto. des. inv MSG_LE.
    exists from, released1. splits; auto; try by refl. }
  { dup GET. eapply Memory.remove_get1 in GET; eauto. des.
    { subst. eapply Memory.remove_get0 in PROMISES. des. clarify. }
    { exists from, released. splits; auto; try by refl. }
  }
Qed.

Lemma step_promise_decrease_promise_writing_event lang (th0 th1: Thread.t lang) pf e
      (STEP: Thread.step pf e th0 th1)
      loc from to val released
      (GET: Memory.get loc to th0.(Thread.local).(Local.promises) = Some (from, Message.concrete val released))
  :
    (exists from' released',
        (<<FROM: Time.le from from'>>) /\
        (<<RELEASED: View.opt_le released' released>>) /\
        (<<GET: Memory.get loc to th1.(Thread.local).(Local.promises) = Some (from', Message.concrete val released')>>)) \/
    (promise_writing_event loc from to val released e).
Proof.
  inv STEP.
  { left. inv STEP0; ss. inv LOCAL.
    eapply promise_promise_decrease in GET; eauto. }
  { inv STEP0; ss.
    inv LOCAL; try by (inv LOCAL0; left; exists from, released; splits; auto; refl).
    { left; exists from, released; splits; auto; refl. }
    { inv LOCAL0. ss. inv WRITE.
      eapply promise_promise_decrease in PROMISE; eauto. des.
      dup GET0. eapply Memory.remove_get1 in GET0; eauto. des.
      { subst. eapply Memory.remove_get0 in REMOVE. des. clarify.
        right. econs; eauto. apply NNPP. ii.
        exploit RELEASE.
        { destruct ord; ss. }
        { eapply GET. }
        { ss. i. subst. inv RELEASED.
          unfold TView.write_released in *. des_ifs. destruct ord; ss. }
      }
      { left. esplits; eauto. }
    }
    { inv LOCAL1. inv LOCAL2. ss. inv WRITE.
      eapply promise_promise_decrease in PROMISE; eauto. des.
      dup GET1. eapply Memory.remove_get1 in GET1; eauto. des.
      { subst. eapply Memory.remove_get0 in REMOVE. des. clarify.
        right. econs; eauto. apply NNPP. ii.
        exploit RELEASE.
        { destruct ordw; ss. }
        { eapply GET. }
        { ss. i. subst. inv RELEASED.
          unfold TView.write_released in *. des_ifs; destruct ordw; ss. }
      }
      { left. esplits; eauto. }
    }
  }
Qed.

Lemma steps_promise_decrease_promise_writing_event lang (th0 th1: Thread.t lang) tr
      (STEPS: traced_step tr th0 th1)
      loc from to val released
      (GET: Memory.get loc to th0.(Thread.local).(Local.promises) = Some (from, Message.concrete val released))
  :
    (exists from' released',
        (<<FROM: Time.le from from'>>) /\
        (<<RELEASED: View.opt_le released' released>>) /\
        (<<GET: Memory.get loc to th1.(Thread.local).(Local.promises) = Some (from', Message.concrete val released')>>)) \/
    (exists e m,
        (<<WRITING: promise_writing_event loc from to val released e>>) /\
        (<<IN: List.In (e, m) tr>>)
    ).
Proof.
  ginduction STEPS.
  { i. left. exists from, released. splits; auto; try refl. }
  { subst. i. inv HD.
    exploit step_promise_decrease_promise_writing_event; eauto. i. des.
    { exploit IHSTEPS; eauto. i. des.
      { left. exists from'0, released'0. splits; auto.
        { etrans; eauto. }
        { etrans; eauto. }
      }
      { right. ss. esplits; eauto.
        eapply promise_writing_event_mon; eauto. }
    }
    { right. ss. esplits; eauto. }
  }
Qed.

Definition pf_consistent_aux lang (e0:Thread.t lang): Prop :=
  forall mem1
         (CAP: Memory.cap e0.(Thread.memory) mem1),
  exists tr e1 times,
    (<<STEPS: traced_step tr (Thread.mk _ e0.(Thread.state) e0.(Thread.local) TimeMap.bot mem1) e1>>) /\
    (<<EVENTS: List.Forall (fun em => <<SAT: (promise_free /1\ no_sc /1\ (wf_time_evt (fun loc to => List.In to (times loc)))) (fst em)>> /\ <<TAU: ThreadEvent.get_machine_event (fst em) = MachineEvent.silent>>) tr >>) /\
    (__guard__((exists st',
                   (<<LOCAL: Local.failure_step e1.(Thread.local)>>) /\
                   (<<FAILURE: Language.step lang ProgramEvent.failure (@Thread.state lang e1) st'>>)) \/
               ((<<PROMISES: e1.(Thread.local).(Local.promises) = Memory.bot>>) /\
                (<<WRITES: forall loc from to val released
                                  (GET: Memory.get loc to e0.(Thread.local).(Local.promises) = Some (from, Message.concrete val released)),
                    exists e m,
                      (<<WRITING: promise_writing_event loc from to val released e>>) /\
                      (<<IN: List.In (e, m) tr>>)>>)))).

Lemma pf_consistent_strong_pf_consistent_aux lang (th: Thread.t lang)
      (WF: Local.wf th.(Thread.local) th.(Thread.memory))
      (MEM: Memory.closed th.(Thread.memory))
      (CONSISTENT: pf_consistent_strong th)
  :
    pf_consistent_aux th.
Proof.
  ii. exploit CONSISTENT; eauto. i. des.
  eapply pred_step_rtc_mon with (Q:=(promise_free /1\ no_sc)) in STEPS0; cycle 1.
  { i. destruct x1; ss. destruct kind; ss. }
  eapply pred_step_rtc_mon with (Q:=(promise_free /1\ no_sc)) in STEPS1; cycle 1.
  { i. des; auto. }
  hexploit (proj1 (@pred_steps_traced_step (promise_free /1\ no_sc) _ (Thread.mk _ th.(Thread.state) th.(Thread.local) TimeMap.bot mem1) e2)).
  { etrans; eauto. } i. des.
  exploit traced_times_list_exists; eauto. i. des.
  eexists tr, e2, times. esplits; eauto.
  { eapply list_Forall_sum.
    { eapply EVENTS. }
    { eapply WFTIME. }
    i. ss. des. splits; auto. }
  unguard. des; eauto. right. splits; auto.
  i. exploit steps_promise_decrease_promise_writing_event.
  { eapply STEPS. }
  { ss. eapply GET. }
  i. des; eauto. erewrite PROMISES in *.
  erewrite Memory.bot_get in *. clarify.
Qed.

Definition pf_consistent_flex lang (e0:Thread.t lang): Prop :=
  exists tr times,
  forall mem1 tm
         (TM: forall loc, Time.lt (Memory.max_ts loc e0.(Thread.memory)) (tm loc))
         (CAP: cap_flex e0.(Thread.memory) mem1 tm),
  exists ftr e1 f,
    (<<STEPS: traced_step ftr (Thread.mk _ e0.(Thread.state) e0.(Thread.local) TimeMap.bot mem1) e1>>) /\
    (<<EVENTS: List.Forall (fun em => <<SAT: (promise_free /1\ no_sc /1\ (wf_time_evt (fun loc to => List.In to (times loc)))) (fst em)>> /\ <<TAU: ThreadEvent.get_machine_event (fst em) = MachineEvent.silent>>) ftr >>) /\
    (<<MAP: cap_flex_map
              (Memory.max_timemap e0.(Thread.memory))
              (fun loc => Time.incr (Memory.max_ts loc e0.(Thread.memory)))
              tm times f>>) /\
    (<<TRACE: List.Forall2 (fun em fem => <<EVENT: tevent_map f (fst fem) (fst em)>> /\ <<MEM: memory_map f (snd em) (snd fem)>>) tr ftr>>) /\
    (__guard__((exists st',
                   (<<LOCAL: Local.failure_step e1.(Thread.local)>>) /\
                   (<<FAILURE: Language.step lang ProgramEvent.failure (@Thread.state lang e1) st'>>)) \/
               ((<<PROMISES: e1.(Thread.local).(Local.promises) = Memory.bot>>) /\
                (<<WRITES: forall loc from to val released
                                  (GET: Memory.get loc to e0.(Thread.local).(Local.promises) = Some (from, Message.concrete val released)),
                    exists e m,
                      (<<WRITING: promise_writing_event loc from to val released e>>) /\
                      (<<IN: List.In (e, m) ftr>>)>>)))).

Lemma pf_consistent_aux_pf_consistent_flex lang (th: Thread.t lang)
      (WF: Local.wf th.(Thread.local) th.(Thread.memory))
      (MEM: Memory.closed th.(Thread.memory))
      (CONSISTENT: pf_consistent_aux th)
  :
    pf_consistent_flex th.
Proof.
  exploit Memory.cap_exists; eauto. i. des.
  exploit CONSISTENT; eauto. i. des.
  eapply cap_cap_flex in CAP.
  exists tr, times. ii.
  exploit (@cap_flex_map_exists
             (Memory.max_timemap th.(Thread.memory))
             (fun loc => Time.incr (Memory.max_ts loc th.(Thread.memory)))
             tm).
  { i. eapply Time.incr_spec. }
  { auto. }
  i. des. destruct e1. ss.
  hexploit traced_steps_map.
  { eapply mapping_map_lt_map_le. eapply MAP. }
  { eapply MAP. }
  { eapply mapping_map_lt_map_eq. eapply MAP. }
  { eapply wf_time_mapped_mappable.
    { eapply List.Forall_impl; eauto. i. ss. des; eauto. }
    { eapply cap_flex_map_complete; eauto. }
  }
  { eapply STEPS. }
  { ss. }
  { ss. }
  { ss. }
  { admit. }
  {



Definition flex_consistent lang (e0:Thread.t lang): Prop :=
  forall mem1 sc1 tm
         (CAP: cap_flex e0.(Thread.memory) mem1 tm)
         (TM: forall loc, Time.lt (Memory.max_ts loc e0.(Thread.memory)) (tm loc)),
  exists e1,
    (<<STEPS0: rtc (tau (@pred_step is_cancel lang)) (Thread.mk _ e0.(Thread.state) e0.(Thread.local) sc1 mem1) e1>>) /\
    (<<NORESERVE: no_reserves e1.(Thread.local).(Local.promises)>>) /\
    (<<SC0: e1.(Thread.sc) = sc1>>) /\
    exists e2,
      (<<STEPS1: rtc (tau (@pred_step ((promise_free /1\ (fun e => ~ is_cancel e)) /1\ no_sc) lang)) e1 e2>>) /\
      (<<SC1: e2.(Thread.sc) = sc1>>) /\
      (__guard__((exists st',
                     (<<LOCAL: Local.failure_step e2.(Thread.local)>>) /\
                     (<<FAILURE: Language.step lang ProgramEvent.failure (@Thread.state lang e2) st'>>)) \/
                 (<<PROMISES: e2.(Thread.local).(Local.promises) = Memory.bot>>))).

write_not_in

Definition super_consistent lang (e0:Thread.t lang): Prop :=
  forall mem1 sc1 mem_future
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


Definition super_consistent lang (e0:Thread.t lang): Prop :=
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
