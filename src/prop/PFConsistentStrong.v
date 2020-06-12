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
Require Import OrderedTimes.

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

Definition certification_times (times : Loc.t -> list Time.t)
           (f: Loc.t -> nat -> (Time.t -> Time.t -> Prop))
           (max: TimeMap.t)
           (loc: Loc.t) (fts: Time.t): Prop :=
  ((<<IN: List.In fts (times loc)>>) /\ (<<TS: Time.le fts (max loc)>>)) \/
  (exists ts n,
      (<<IN: List.In ts (times loc)>>) /\ (<<TS: Time.lt (max loc) ts>>)
      /\ (<<MAX: Time.lt (max loc) (incr_time_seq n)>>)
      /\ (<<MAP: f loc n ts fts>>)).

Lemma certification_times_well_ordered times f max
      (MAP: forall loc n
                   (TS: Time.lt (max loc) (incr_time_seq n)),
          cap_flex_map_loc
            (max loc)
            (Time.incr (max loc))
            (incr_time_seq n) (times loc) (f loc n))
  :
    forall loc, well_ordered (certification_times times f max loc).
Proof.
  i. hexploit (@increasing_join_well_ordered
                 incr_time_seq
                 (fun n fts =>
                    (exists ts,
                        (<<IN: List.In ts (times loc)>>) /\ (<<TS: Time.lt (max loc) ts>>)
                        /\ (<<MAX: Time.lt (max loc) (incr_time_seq n)>>)
                        /\ (<<MAP: f loc n ts fts>>)))).
  { i. eapply incr_time_seq_lt; eauto. }
  { eapply incr_time_seq_diverge. }
  { i. des. exploit MAP; eauto. intros FLEXMAP.
    eapply (FLEXMAP.(cap_flex_map_loc_bound)); try apply MAP0. auto. }
  { i. assert (INJ: forall (TS: Time.lt (max loc) (incr_time_seq n))
                           ts fts0 fts1
                           (MAP0: f loc n ts fts0)
                           (MAP1: f loc n ts fts1),
                  fts0 = fts1).
    { i. specialize (MAP _ _ TS). eapply mapping_map_lt_loc_map_eq; eauto. eapply MAP. }
    remember (times loc). clear MAP times Heql. induction l.
    { eapply sub_well_ordered with (times0 := bot1).
      { eapply empty_well_ordered. }
      { i. des. ss. }
    }
    { destruct (classic (exists fts,
                            (<<TS: Time.lt (max loc) a>>)
                            /\ (<<MAX: Time.lt (max loc) (incr_time_seq n)>>)
                            /\ (<<MAP: f loc n a fts>>))).
      { des. eapply sub_well_ordered.
        { eapply join_well_ordered.
          { eapply IHl. }
          { eapply (singleton_well_ordered fts). }
        }
        i. des. ss. des.
        { subst. right. eapply INJ; eauto. }
        { left. eauto. }
      }
      { eapply sub_well_ordered.
        { eapply IHl. }
        i. des. ss. des; eauto. subst.
        exfalso. eapply H. esplits; eauto. }
    }
  }
  intros WO. eapply sub_well_ordered.
  { eapply join_well_ordered.
    { eapply WO. }
    { eapply (finite_well_ordered (times loc)). }
  }
  { i. unfold certification_times in *. des; eauto. left.
    esplits; eauto. }
Qed.

Lemma wf_time_evt_map times f te fte
      (WF: wf_time_evt times te)
      (MAP: tevent_map f fte te)
  :
    wf_time_evt (fun loc fts => exists ts, (<<IN: times loc ts>>) /\ (<<MAP: f loc ts fts>>)) fte.
Proof.
  inv MAP; ss.
  { des. splits; eauto. }
  { des. splits; eauto. }
  { des. splits; eauto. }
Qed.

Definition pf_consistent_flex lang (e0:Thread.t lang)
           (tr : list (ThreadEvent.t * Memory.t)) (times : Loc.t -> list Time.t)
           (f: Loc.t -> nat -> (Time.t -> Time.t -> Prop))
  : Prop :=
  (<<MAP: forall loc n
                 (TS: Time.lt (Memory.max_ts loc e0.(Thread.memory)) (incr_time_seq n)),
      cap_flex_map_loc
        (Memory.max_ts loc e0.(Thread.memory))
        (Time.incr (Memory.max_ts loc e0.(Thread.memory)))
        (incr_time_seq n) (times loc) (f loc n)>>) /\
  (<<CONSISTENT: forall mem1 (tm: Loc.t -> nat)
                        (TM: forall loc, Time.lt (Memory.max_ts loc e0.(Thread.memory)) (incr_time_seq (tm loc)))
                        (CAP: cap_flex e0.(Thread.memory) mem1 (fun loc => incr_time_seq (tm loc))),
      exists ftr e1,
        (<<STEPS: traced_step ftr (Thread.mk _ e0.(Thread.state) e0.(Thread.local) TimeMap.bot mem1) e1>>) /\
        (<<EVENTS: List.Forall (fun em => <<SAT: (promise_free
                                                    /1\ no_sc
                                                    /1\ write_not_in (fun loc ts => (<<TS: Time.le ts (incr_time_seq (tm loc))>>) /\ (<<PROM: ~ covered loc ts e0.(Thread.local).(Local.promises)>>))
                                                    /1\ wf_time_evt (fun loc => certification_times times f (Memory.max_timemap e0.(Thread.memory)) loc)
                                                    /1\ no_read_msgs (fun loc ts => ~ (covered loc ts e0.(Thread.local).(Local.promises) \/ concrete_promised e0.(Thread.memory) loc ts \/ Time.lt (incr_time_seq (tm loc)) ts))) (fst em)>> /\ <<TAU: ThreadEvent.get_machine_event (fst em) = MachineEvent.silent>>) ftr >>) /\
        (<<TRACE: List.Forall2 (fun em fem => <<EVENT: tevent_map (fun loc => f loc (tm loc)) (fst fem) (fst em)>> /\ <<MEM: memory_map (fun loc => f loc (tm loc)) (snd em) (snd fem)>>) tr ftr>>) /\
        (__guard__((exists st',
                       (<<LOCAL: Local.failure_step e1.(Thread.local)>>) /\
                       (<<FAILURE: Language.step lang ProgramEvent.failure (@Thread.state lang e1) st'>>)) \/
                   ((<<PROMISES: e1.(Thread.local).(Local.promises) = Memory.bot>>) /\
                    (<<WRITES: forall loc from to val released
                                      (GET: Memory.get loc to e0.(Thread.local).(Local.promises) = Some (from, Message.concrete val released)),
                        exists e m,
                          (<<WRITING: promise_writing_event loc from to val released e>>) /\
                          (<<IN: List.In (e, m) ftr>>)>>))))>>).

Lemma pf_consistent_strong_aux_pf_consistent_flex lang (th: Thread.t lang)
      (WF: Local.wf th.(Thread.local) th.(Thread.memory))
      (MEM: Memory.closed th.(Thread.memory))
      (CONSISTENT: pf_consistent_strong_aux th)
  :
    exists tr times f, <<CONSISTENT: pf_consistent_flex th tr times f>>.
Proof.
  exploit Memory.cap_exists; eauto. i. des.
  exploit CONSISTENT; eauto. i. des. exists tr, times.
  hexploit (@choice
              (Loc.t * nat)
              (Time.t -> Time.t -> Prop)
              (fun locn f =>
                 let (loc, n) := locn in
                 forall
                   (TS: Time.lt (Memory.max_ts loc th.(Thread.memory)) (incr_time_seq n)),
                   cap_flex_map_loc
                     (Memory.max_ts loc th.(Thread.memory))
                     (Time.incr (Memory.max_ts loc th.(Thread.memory)))
                     (incr_time_seq n) (times loc) f)).
  { intros [loc n].
    destruct (classic (Time.lt (Memory.max_ts loc th.(Thread.memory)) (incr_time_seq n))).
    { des. hexploit cap_flex_map_loc_exists.
      { eapply Time.incr_spec. }
      { eapply H. }
      i. des. eauto. }
    { exists bot2. i. exfalso. eapply H. auto. }
  }
  intros [f SPEC]. des. exists (fun loc ts => f (loc, ts)). econs.
  { ii. specialize (SPEC (loc, n)). ss. eauto. }
  ii. assert (MAP: cap_flex_map
                     (Memory.max_timemap (Thread.memory th))
                     (fun loc => Time.incr (Memory.max_ts loc (Thread.memory th)))
                     (fun loc => incr_time_seq (tm loc))
                     times (fun loc => f (loc, tm loc))).
  { eapply cap_flex_map_locwise. i.
    eapply (SPEC (loc, tm loc)). eauto. }
  destruct e1. ss.
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
  exploit no_read_unreadable_traced; eauto. intros NOREAD. ss.
  exists ftr, (Thread.mk _ state flc1 fsc1 fmem1). splits; auto.
  { eapply List.Forall_forall. i.
    cut ((promise_free /1\ no_sc) (fst x) /\ ThreadEvent.get_machine_event (fst x) = MachineEvent.silent).
    { i. des. splits; auto.
      { eapply List.Forall_forall in NOTIN; eauto. ss.
        eapply write_not_in_mon_bot; eauto. intros loc ts. intros. des.
        assert (ITV: Interval.mem (Time.bot, incr_time_seq (tm loc)) ts).
        { econs; ss. }
        erewrite (@cap_flex_covered _ _ (fun loc => incr_time_seq (tm loc))) in ITV; eauto.
        inv ITV. econs; eauto. econs; eauto.
        destruct (Memory.get loc to (Local.promises (Thread.local th)))
          as [[from' msg']|] eqn:GETPROM; eauto.
        exfalso. dup GETPROM.
        eapply WF in GETPROM. eapply CAP0 in GETPROM. clarify.
        eapply SAT0. econs; eauto. }
      { eapply list_Forall2_in in H; eauto. des.
        eapply List.Forall_forall in IN; eauto. ss. des.
        eapply wf_time_evt_map in SAT0; eauto. eapply wf_time_evt_mon; try apply SAT0.
        i. ss. des. destruct (Time.le_lt_dec ts (Memory.max_timemap (Thread.memory th) x0)).
        { left. assert (ts = x2).
          { eapply mapping_map_lt_map_eq.
            { eapply MAP. }
            { ss. eapply MAP. eauto. }
            { eauto. }
          }
          subst. eauto. }
        { right. esplits; eauto. }
      }
      { eapply List.Forall_forall in NOREAD; eauto.
        eapply no_read_msgs_mon; eauto. i.
        apply not_or_and in PR. des. apply not_or_and in PR0. des.
        exploit cap_flex_covered; eauto. intros COV. hexploit (proj1 COV).
        { instantiate (1:=x2). instantiate (1:=x0). econs; ss.
          { destruct (Time.bot_spec x2); auto. inv H3. exfalso. eapply PR0.
            econs. eapply MEM. }
          { destruct (Time.le_lt_dec x2 (incr_time_seq (tm x0))); ss. }
        }
        intros COVERED. inv COVERED. econs; eauto.
        { econs; eauto. econs; eauto.
          destruct (Memory.get x0 to (Local.promises (Thread.local th)))
            as [[from0 msgs]|] eqn: GETPROM; auto.
          dup GETPROM. eapply WF in GETPROM.
          eapply CAP0 in GETPROM. clarify.
          exfalso. eapply PR. econs; eauto. }
        { i. eapply cap_flex_inv in GET0; eauto. des; clarify.
          eapply PR0. econs; eauto. }
      }
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

Definition pf_consistent_flex_aux lang (e0:Thread.t lang)
           (tr : list (ThreadEvent.t * Memory.t)) (times : Loc.t -> list Time.t)
           (f: Loc.t -> nat -> (Time.t -> Time.t -> Prop))
  : Prop :=
  (<<MAP: forall loc n
                 (TS: Time.lt (Memory.max_ts loc e0.(Thread.memory)) (incr_time_seq n)),
      cap_flex_map_loc
        (Memory.max_ts loc e0.(Thread.memory))
        (Time.incr (Memory.max_ts loc e0.(Thread.memory)))
        (incr_time_seq n) (times loc) (f loc n)>>) /\
  (<<CONSISTENT: forall mem1
                        (tm: Loc.t -> nat)
                        (FUTURE: Memory.future_weak e0.(Thread.memory) mem1)
                        (CLOSED: Memory.closed mem1)
                        (LOCAL: Local.wf e0.(Thread.local) mem1)
                        (TM0: forall loc, Time.lt (Memory.max_ts loc e0.(Thread.memory)) (incr_time_seq (tm loc)))
                        (TM1: forall loc, Time.lt (Memory.max_ts loc mem1) (incr_time_seq (tm loc))),
      exists ftr e1,
        (<<STEPS: traced_step ftr (Thread.mk _ e0.(Thread.state) e0.(Thread.local) TimeMap.bot mem1) e1>>) /\
        (<<EVENTS: List.Forall (fun em => <<SAT: (promise_free
                                                    /1\ no_sc
                                                    /1\ write_not_in (fun loc ts => (<<TS: Time.le ts (incr_time_seq (tm loc))>>) /\ (<<PROM: ~ covered loc ts e0.(Thread.local).(Local.promises)>>))
                                                    /1\ no_read_msgs (fun loc ts => ~ (covered loc ts e0.(Thread.local).(Local.promises) \/ concrete_promised e0.(Thread.memory) loc ts \/ Time.lt (incr_time_seq (tm loc)) ts))
                                                    /1\ wf_time_evt (fun loc => certification_times times f (Memory.max_timemap e0.(Thread.memory)) loc)) (fst em)>> /\ <<TAU: ThreadEvent.get_machine_event (fst em) = MachineEvent.silent>>) ftr >>) /\
        (<<TRACE: List.Forall2 (fun em fem => tevent_map (fun loc => f loc (tm loc)) (fst fem) (fst em)) tr ftr>>) /\
        (__guard__((exists st',
                       (<<LOCAL: Local.failure_step e1.(Thread.local)>>) /\
                       (<<FAILURE: Language.step lang ProgramEvent.failure (@Thread.state lang e1) st'>>)) \/
                   ((<<PROMISES: e1.(Thread.local).(Local.promises) = Memory.bot>>) /\
                    (<<WRITES: forall loc from to val released
                                      (GET: Memory.get loc to e0.(Thread.local).(Local.promises) = Some (from, Message.concrete val released)),
                        exists e m,
                          (<<WRITING: promise_writing_event loc from to val released e>>) /\
                          (<<IN: List.In (e, m) ftr>>)>>))))>>).

Lemma pf_consistent_flex_pf_consistent_flex_aux lang (th: Thread.t lang) tr times f
      (WF: Local.wf th.(Thread.local) th.(Thread.memory))
      (MEM: Memory.closed th.(Thread.memory))
      (CONSISTENT: pf_consistent_flex th tr times f)
  :
    pf_consistent_flex_aux th tr times f.
Proof.
  unfold pf_consistent_flex in *. des. econs; eauto.
  ii. exploit (@cap_flex_exists th.(Thread.memory) (fun loc => incr_time_seq (tm loc))); eauto. i. des.
  exploit CONSISTENT0; eauto. i. des. destruct e1. ss.
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
  i. des. exists ftr0, (Thread.mk _ state flc1 fsc1 fmem1).
  splits; auto.
  { eapply List.Forall_forall. i.
    cut ((promise_free /1\ no_sc) (fst x) /\ ThreadEvent.get_machine_event (fst x) = MachineEvent.silent).
    { i. des. eapply list_Forall2_in in H; eauto. des.
      eapply List.Forall_forall in IN; eauto. ss. des.
      splits; auto.
      { eapply ident_map_write_not_in; eauto. }
      { eapply ident_map_no_read_msgs; eauto. }
      { eapply wf_time_evt_map in SAT1; eauto.
        eapply wf_time_evt_mon; try apply SAT1. ss.
        i. des. inv MAP0. eauto. }
    }
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

Definition pf_consistent_super_strong lang (e0:Thread.t lang)
           (tr : list (ThreadEvent.t * Memory.t))
           (times: Loc.t -> list Time.t)
           (certimes: Loc.t -> (Time.t -> Prop))
  : Prop :=
  forall mem1 tm sc
         (FUTURE: Memory.future_weak e0.(Thread.memory) mem1)
         (CLOSED: Memory.closed mem1)
         (LOCAL: Local.wf e0.(Thread.local) mem1),
  exists ftm ftr e1 f,
    (<<TM: TimeMap.le tm ftm>>) /\
    (<<STEPS: traced_step ftr (Thread.mk _ e0.(Thread.state) e0.(Thread.local) sc mem1) e1>>) /\
    (<<EVENTS: List.Forall (fun em => <<SAT: (promise_free
                                                /1\ no_sc
                                                /1\ wf_time_evt certimes
                                                /1\ no_read_msgs (fun loc ts => ~ (covered loc ts e0.(Thread.local).(Local.promises) \/ concrete_promised e0.(Thread.memory) loc ts \/ Time.lt (ftm loc) ts))) (fst em)>> /\ <<TAU: ThreadEvent.get_machine_event (fst em) = MachineEvent.silent>>) ftr >>) /\
    (<<MAP: cap_flex_map
              (Memory.max_timemap e0.(Thread.memory))
              (fun loc => Time.incr (Memory.max_ts loc e0.(Thread.memory)))
              ftm times f>>) /\
    (<<TRACE: List.Forall2 (fun em fem => tevent_map f (fst fem) (fst em)) tr ftr>>) /\
    (<<GOOD: good_future ftm mem1 e1.(Thread.memory)>>) /\
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

Lemma pf_consistent_flex_aux_pf_consistent_super_strong lang (th: Thread.t lang) tr times f
      (WF: Local.wf th.(Thread.local) th.(Thread.memory))
      (MEM: Memory.closed th.(Thread.memory))
      (CONSISTENT: pf_consistent_flex_aux th tr times f)
  :
    exists certimes,
      (<<WO: forall loc, well_ordered (certimes loc)>>) /\
      (<<CONSISTENT: pf_consistent_super_strong th tr times certimes>>).
Proof.
  unfold pf_consistent_flex_aux in *. des.
  exists (certification_times times f (Memory.max_timemap th.(Thread.memory))). splits.
  { eapply certification_times_well_ordered. eauto. }
  ii. assert (TM: exists (ftm: Loc.t -> nat),
                 forall loc,
                   (<<TM0: Time.lt (Memory.max_ts loc th.(Thread.memory)) (incr_time_seq (ftm loc))>>) /\
                   (<<TM1: Time.lt (Memory.max_ts loc mem1) (incr_time_seq (ftm loc))>>) /\
                   (<<TM2: Time.le (tm loc) (incr_time_seq (ftm loc))>>)).
  { eapply (choice
              (fun loc n =>
                 (<<TM0: Time.lt (Memory.max_ts loc th.(Thread.memory)) (incr_time_seq n)>>) /\
                 (<<TM1: Time.lt (Memory.max_ts loc mem1) (incr_time_seq n)>>) /\
                 (<<TM2: Time.le (tm loc) (incr_time_seq n)>>))).
    intros loc. hexploit (incr_time_seq_diverge
                            (Time.join (Time.join
                                          (Memory.max_ts loc th.(Thread.memory))
                                          (Memory.max_ts loc mem1))
                                       (tm loc))).
    i. des. exists n. splits.
    { eapply TimeFacts.le_lt_lt; eauto. etrans.
      { eapply Time.join_l. }
      eapply Time.join_l. }
    { eapply TimeFacts.le_lt_lt; eauto. etrans.
      { eapply Time.join_r. }
      eapply Time.join_l. }
    { left. eapply TimeFacts.le_lt_lt; eauto.
      eapply Time.join_r. }
  }
  des. hexploit (CONSISTENT0 mem1 ftm); eauto.
  { eapply TM; eauto. }
  { eapply TM; eauto. }
  i. des. destruct e1.
  exploit write_not_in_good_future_traced; try apply STEPS; ss; auto.
  { eapply TM. }
  { eapply Memory.closed_timemap_bot. inv CLOSED. auto. }
  { eapply List.Forall_impl; eauto. i. ss. des. eapply write_not_in_mon; eauto.
    i. ss. des. split; auto. ii. eapply PROM.
    inv H. econs; eauto. eapply LOCAL in GET; eauto. } intros GOOD.
  eapply no_sc_any_sc_traced in STEPS; ss; cycle 1.
  { i. eapply List.Forall_forall in IN; eauto. ss. des; auto. } des.
  eexists (fun loc => incr_time_seq (ftm loc)), ftr, _, (fun loc => f loc (ftm loc)).
  esplits; eauto.
  { ii. eapply TM. }
  { eapply List.Forall_impl; [|apply EVENTS]. i. ss. des; auto. }
  { eapply cap_flex_map_locwise. i. eapply MAP. eapply TM. }
  { eapply no_sc_same_sc_traced in STEPS0; eauto.
    eapply List.Forall_impl; eauto. i. ss. des; auto. }
Qed.

Lemma consistent_pf_consistent_super_strong lang (th: Thread.t lang)
      (LOCAL: Local.wf th.(Thread.local) th.(Thread.memory))
      (MEM: Memory.closed th.(Thread.memory))
      (CONSISTENT: Thread.consistent th)
  :
    exists tr times certimes,
      (<<WO: forall loc, well_ordered (certimes loc)>>) /\
      <<CONSISTENT: pf_consistent_super_strong th tr times certimes>>.
Proof.
  eapply consistent_pf_consistent in CONSISTENT; eauto.
  eapply pf_consistent_pf_consistent_strong in CONSISTENT; eauto.
  eapply pf_consistent_strong_pf_consistent_strong_aux in CONSISTENT; eauto.
  eapply pf_consistent_strong_aux_pf_consistent_flex in CONSISTENT; eauto. des.
  eapply pf_consistent_flex_pf_consistent_flex_aux in CONSISTENT0; eauto.
  eapply pf_consistent_flex_aux_pf_consistent_super_strong in CONSISTENT0; eauto.
Qed.
