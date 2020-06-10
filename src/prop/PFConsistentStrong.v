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


Require Import Mapping.
Require Import CapFlex.
Require Import GoodFuture.
Require Import Cover.


Definition pf_consistent_strong_aux lang (e0:Thread.t lang): Prop :=
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

Lemma pf_consistent_strong_pf_consistent_strong_aux lang (th: Thread.t lang)
      (WF: Local.wf th.(Thread.local) th.(Thread.memory))
      (MEM: Memory.closed th.(Thread.memory))
      (CONSISTENT: pf_consistent_strong th)
  :
    pf_consistent_strong_aux th.
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
    (<<EVENTS: List.Forall (fun em => <<SAT: (promise_free /1\ no_sc /1\ write_not_in (fun loc ts => (<<TS: Time.le ts (tm loc)>>) /\ (<<PROM: ~ covered loc ts e0.(Thread.local).(Local.promises)>>))) (fst em)>> /\ <<TAU: ThreadEvent.get_machine_event (fst em) = MachineEvent.silent>>) ftr >>) /\
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

Lemma pf_consistent_strong_aux_pf_consistent_flex lang (th: Thread.t lang)
      (WF: Local.wf th.(Thread.local) th.(Thread.memory))
      (MEM: Memory.closed th.(Thread.memory))
      (CONSISTENT: pf_consistent_strong_aux th)
  :
    pf_consistent_flex th.
Proof.
  exploit Memory.cap_exists; eauto. i. des.
  exploit CONSISTENT; eauto. i. des.
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
  { eapply Local.cap_wf; eauto. }
  { instantiate (1:=mem1). instantiate (1:=th.(Thread.local)).
    eapply cap_flex_wf; eauto. }
  { eapply cap_flex_closed; eauto. }
  { eapply Memory.cap_closed; eauto. }
  { eapply Memory.closed_timemap_bot.
    eapply cap_flex_closed in CAP0; auto. eapply CAP0. }
  { eapply Memory.closed_timemap_bot.
    eapply Memory.cap_closed in CAP; auto. eapply CAP. }
  { eapply map_ident_in_memory_local.
    { ii. eapply MAP. eapply TS. }
    { eapply MAP. }
    { eauto. }
    { eauto. }
  }
  { eapply concrete_messages_le_cap_flex_memory_map.
    { refl. }
    { instantiate (1:=(fun loc => Time.incr (Memory.max_ts loc th.(Thread.memory)))).
      i. eapply Time.incr_spec. }
    { eapply TM. }
    { eapply cap_cap_flex; eauto. }
    { eauto. }
    { eauto. }
    { eauto. }
    { eauto. }
  }
  { eapply mapping_map_lt_collapsable_unwritable. eapply MAP. }
  { eapply timemap_bot_map. eapply MAP. }
  { refl. } i. des.
  exploit write_not_in_traced; eauto.
  { ss. transitivity (th.(Thread.memory)).
    { eapply WF. }
    { eapply CAP0. }
  } intros NOTIN. ss.
  exists ftr, (Thread.mk _ state flc1 fsc1 fmem1), f. splits; auto.
  { eapply List.Forall_forall. i.
    cut ((promise_free /1\ no_sc) (fst x) /\ ThreadEvent.get_machine_event (fst x) = MachineEvent.silent).
    { i. des. splits; auto. eapply List.Forall_forall in H; eauto. ss.
      eapply write_not_in_mon_bot; eauto. intros loc ts. intros. des.
      assert (ITV: Interval.mem (Time.bot, tm loc) ts).
      { econs; ss. }
      erewrite cap_flex_covered in ITV; eauto.
      inv ITV. econs; eauto. econs; eauto.
      destruct (Memory.get loc to (Local.promises (Thread.local th)))
        as [[from' msg']|] eqn:GETPROM; eauto.
      exfalso. dup GETPROM.
      eapply WF in GETPROM. eapply CAP0 in GETPROM. clarify.
      eapply SAT0. econs; eauto.
    }
    eapply list_Forall2_in in H; eauto. des.
    eapply List.Forall_forall in IN; eauto. ss. des.
    destruct x, a. ss. inv EVENT; ss. inv KIND; ss.
    splits; auto. inv MSG0; ss. inv MSG; ss. inv MAP1; ss.
  }
  { ss. unguard. des; eauto.
    { left. esplits; eauto. eapply failure_step_map; eauto.
      { eapply mapping_map_lt_map_le. eapply MAP. }
      { eapply mapping_map_lt_map_eq. eapply MAP. }
    }
    { right. splits.
      { inv LOCAL. erewrite PROMISES in *. eapply bot_promises_map; eauto. }
      { i. exploit WRITES; eauto. i. des.
        eapply list_Forall2_in2 in IN; eauto. des.
        destruct b. ss. eexists t, _. splits; eauto.
        eapply promise_writing_event_map; eauto.
        { inv WF. eapply PROMISES0 in GET. eauto. }
        { eapply MAP. }
        { ii. eapply MAP. auto. }
      }
    }
  }
Qed.

Definition pf_consistent_flex_aux lang (e0:Thread.t lang): Prop :=
  exists (tr: list (ThreadEvent.t * Memory.t)) times,
  forall mem1 tm
         (FUTURE: Memory.future_weak e0.(Thread.memory) mem1)
         (CLOSED: Memory.closed mem1)
         (LOCAL: Local.wf e0.(Thread.local) mem1)
         (TM0: forall loc, Time.lt (Memory.max_ts loc e0.(Thread.memory)) (tm loc))
         (TM1: forall loc, Time.lt (Memory.max_ts loc mem1) (tm loc)),
  exists ftr e1 f,
    (<<STEPS: traced_step ftr (Thread.mk _ e0.(Thread.state) e0.(Thread.local) TimeMap.bot mem1) e1>>) /\
    (<<EVENTS: List.Forall (fun em => <<SAT: (promise_free /1\ no_sc /1\ write_not_in (fun loc ts => (<<TS: Time.le ts (tm loc)>>) /\ (<<PROM: ~ covered loc ts e0.(Thread.local).(Local.promises)>>))) (fst em)>> /\ <<TAU: ThreadEvent.get_machine_event (fst em) = MachineEvent.silent>>) ftr >>) /\
    (<<MAP: cap_flex_map
              (Memory.max_timemap e0.(Thread.memory))
              (fun loc => Time.incr (Memory.max_ts loc e0.(Thread.memory)))
              tm times f>>) /\
    (<<TRACE: List.Forall2 (fun em fem => tevent_map f (fst fem) (fst em)) tr ftr>>) /\
    (__guard__((exists st',
                   (<<LOCAL: Local.failure_step e1.(Thread.local)>>) /\
                   (<<FAILURE: Language.step lang ProgramEvent.failure (@Thread.state lang e1) st'>>)) \/
               ((<<PROMISES: e1.(Thread.local).(Local.promises) = Memory.bot>>) /\
                (<<WRITES: forall loc from to val released
                                  (GET: Memory.get loc to e0.(Thread.local).(Local.promises) = Some (from, Message.concrete val released)),
                    exists e m,
                      (<<WRITING: promise_writing_event loc from to val released e>>) /\
                      (<<IN: List.In (e, m) ftr>>)>>)))).

Lemma pf_consistent_flex_pf_consistent_flex_aux lang (th: Thread.t lang)
      (WF: Local.wf th.(Thread.local) th.(Thread.memory))
      (MEM: Memory.closed th.(Thread.memory))
      (CONSISTENT: pf_consistent_flex th)
  :
    pf_consistent_flex_aux th.
Proof.
  unfold pf_consistent_flex in *. des. exists tr, times.
  ii. exploit (@cap_flex_exists th.(Thread.memory) tm); eauto. i. des.
  exploit CONSISTENT; eauto. i. des. destruct e1. ss.
  hexploit traced_steps_map.
  { eapply ident_map_le; eauto. }
  { eapply ident_map_bot; eauto. }
  { eapply ident_map_eq; eauto. }
  { eapply List.Forall_forall. i. eapply ident_map_mappable_evt. }
  { eapply STEPS. }
  { ss. }
  { ss. }
  { ss. }
  { eapply cap_flex_wf; eauto. }
  { eapply LOCAL. }
  { eauto. }
  { eapply cap_flex_closed; eauto. }
  { eapply Memory.closed_timemap_bot. inv CLOSED. auto. }
  { eapply Memory.closed_timemap_bot.
    eapply cap_flex_closed in CAP; eauto. eapply CAP. }
  { eapply ident_map_local. }
  { eapply cap_flex_future_memory_map; try apply CAP; eauto.
    ii. left. eauto. }
  { eapply mapping_map_lt_collapsable_unwritable. eapply ident_map_lt. }
  { eapply timemap_bot_map. eapply ident_map_bot. }
  { refl. }
  i. des. exists ftr0, (Thread.mk _ state flc1 fsc1 fmem1), f.
  splits; auto.
  { eapply List.Forall_forall. i.
    cut ((promise_free /1\ no_sc) (fst x) /\ ThreadEvent.get_machine_event (fst x) = MachineEvent.silent).
    { i. des. splits; auto.
      eapply list_Forall2_in in H; eauto. des.
      eapply List.Forall_forall in IN; eauto. ss. des.
      eapply ident_map_write_not_in; eauto. }
    eapply list_Forall2_in in H; eauto. des.
    eapply List.Forall_forall in IN; eauto. ss. des.
    destruct x, a. ss. inv EVENT; ss. inv KIND; ss.
    splits; auto. inv MSG0; ss. inv MSG; ss. inv MAP1; ss. }
    { eapply list_Forall2_compose; eauto.
    i. ss. des. eapply ident_map_compose_tevent; eauto. }
  { ss. unguard. des; eauto.
    { left. esplits; eauto. eapply failure_step_map; eauto.
      { eapply ident_map_le. }
      { eapply ident_map_eq. }
    }
    { right. splits.
      { inv LOCAL0. erewrite PROMISES in *. eapply bot_promises_map; eauto. }
      { i. exploit WRITES; eauto. i. des.
        eapply list_Forall2_in2 in IN; eauto. des.
        destruct b. ss. eexists t, _. splits; eauto.
        eapply promise_writing_event_map; eauto.
        { inv LOCAL. eapply PROMISES0 in GET. eauto. }
        { eapply ident_map_lt. }
        { ii. ss. }
      }
    }
  }
Qed.

Definition pf_consistent_super_strong lang (e0:Thread.t lang): Prop :=
  exists (tr: list (ThreadEvent.t * Memory.t)) times,
  forall mem1 tm sc
         (FUTURE: Memory.future_weak e0.(Thread.memory) mem1)
         (CLOSED: Memory.closed mem1)
         (LOCAL: Local.wf e0.(Thread.local) mem1)
         (TM0: forall loc, Time.lt (Memory.max_ts loc e0.(Thread.memory)) (tm loc))
         (TM1: forall loc, Time.lt (Memory.max_ts loc mem1) (tm loc)),
  exists ftr e1 f,
    (<<STEPS: traced_step ftr (Thread.mk _ e0.(Thread.state) e0.(Thread.local) sc mem1) e1>>) /\
    (<<EVENTS: List.Forall (fun em => <<SAT: (promise_free /1\ no_sc) (fst em)>> /\ <<TAU: ThreadEvent.get_machine_event (fst em) = MachineEvent.silent>>) ftr >>) /\
    (<<MAP: cap_flex_map
              (Memory.max_timemap e0.(Thread.memory))
              (fun loc => Time.incr (Memory.max_ts loc e0.(Thread.memory)))
              tm times f>>) /\
    (<<TRACE: List.Forall2 (fun em fem => tevent_map f (fst fem) (fst em)) tr ftr>>) /\
    (<<GOOD: good_future tm mem1 e1.(Thread.memory)>>) /\
    (<<SC: e1.(Thread.sc) = sc>>) /\
    (__guard__((exists st',
                   (<<LOCAL: Local.failure_step e1.(Thread.local)>>) /\
                   (<<FAILURE: Language.step lang ProgramEvent.failure (@Thread.state lang e1) st'>>)) \/
               ((<<PROMISES: e1.(Thread.local).(Local.promises) = Memory.bot>>) /\
                (<<WRITES: forall loc from to val released
                                  (GET: Memory.get loc to e0.(Thread.local).(Local.promises) = Some (from, Message.concrete val released)),
                    exists e m,
                      (<<WRITING: promise_writing_event loc from to val released e>>) /\
                      (<<IN: List.In (e, m) ftr>>)>>)))).

Lemma pf_consistent_flex_aux_pf_consistent_super_strong lang (th: Thread.t lang)
      (WF: Local.wf th.(Thread.local) th.(Thread.memory))
      (MEM: Memory.closed th.(Thread.memory))
      (CONSISTENT: pf_consistent_flex_aux th)
  :
    pf_consistent_super_strong th.
Proof.
  unfold pf_consistent_flex_aux in *. des. exists tr, times.
  ii. exploit CONSISTENT; eauto. i. des. destruct e1.
  exploit write_not_in_good_future_traced; try apply STEPS; ss; auto.
  { eapply Memory.closed_timemap_bot. inv CLOSED. auto. }
  { eapply List.Forall_impl; eauto. i. ss. des. eapply write_not_in_mon; eauto.
    i. ss. des. split; auto. ii. eapply PROM.
    inv H. econs; eauto. eapply LOCAL in GET; eauto. }
  eapply no_sc_any_sc_traced in STEPS; ss; cycle 1.
  { i. eapply List.Forall_forall in IN; eauto. ss. des; auto. } des.
  esplits; eauto.
  { eapply List.Forall_impl; [|apply EVENTS]. i. ss. des; auto. }
  { eapply no_sc_same_sc_traced in STEPS0; eauto.
    eapply List.Forall_impl; eauto. i. ss. des; auto. }
Qed.

Lemma consistent_pf_consistent_super_strong lang (th: Thread.t lang)
      (LOCAL: Local.wf th.(Thread.local) th.(Thread.memory))
      (MEM: Memory.closed th.(Thread.memory))
      (CONSISTENT: Thread.consistent th)
  :
    pf_consistent_super_strong th.
Proof.
  eapply pf_consistent_flex_aux_pf_consistent_super_strong; eauto.
  eapply pf_consistent_flex_pf_consistent_flex_aux; eauto.
  eapply pf_consistent_strong_aux_pf_consistent_flex; eauto.
  eapply pf_consistent_strong_pf_consistent_strong_aux; eauto.
  eapply pf_consistent_pf_consistent_strong; eauto.
  eapply consistent_pf_consistent; eauto.
Qed.