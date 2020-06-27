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
Require Import Trace.

Require Import MemoryMerge.
Require Import PromiseConsistent.
Require Import PFConsistent.
Require Import ReorderCancel.
Require Import MemoryProps.
Require Import OrderedTimes.

Require Import Mapping.
Require Import CapFlex.
Require Import GoodFuture.
Require Import Cover.

Set Implicit Arguments.


Section CONCRETEMAX.

  Inductive concrete_promise_max_ts mem prom loc ts: Prop :=
  | concrete_or_promise_max_ts_intro
      (EXISTS:
         (<<CONCRETE: exists from val released,
             (<<GET: Memory.get loc ts mem = Some (from, Message.concrete val released)>>)>>) \/
         (<<PROMISE: exists from msg, (<<GET: Memory.get loc ts prom = Some (from, msg)>>)>>))
      (CONCRETE: forall to from val released
                        (GET: Memory.get loc to mem = Some (from, Message.concrete val released)),
          Time.le to ts)
      (PROMISE: forall to from msg
                       (GET: Memory.get loc to prom = Some (from, msg)),
          Time.le to ts)
  .

  Lemma concrete_promise_max_ts_inj mem prom loc ts0 ts1
        (MAX0: concrete_promise_max_ts mem prom loc ts0)
        (MAX1: concrete_promise_max_ts mem prom loc ts1)
    :
      ts0 = ts1.
  Proof.
    eapply TimeFacts.antisym.
    { inv MAX0. des.
      { eapply MAX1 in GET. auto. }
      { eapply MAX1 in GET. auto. }
    }
    { inv MAX1. des.
      { eapply MAX0 in GET. auto. }
      { eapply MAX0 in GET. auto. }
    }
  Qed.

  Lemma concrete_promise_max_ts_exists mem prom loc
        (INHABITED: Memory.inhabited mem)
    :
      exists ts, (<<MAX: concrete_promise_max_ts mem prom loc ts>>).
  Proof.
    exploit Memory.max_concrete_ts_exists; eauto. intros [max MAX].
    exploit Memory.max_concrete_ts_spec.
    { eapply MAX. }
    { eapply INHABITED. } i. des.
    destruct (classic (exists to from msg, (<<INHABITED: Memory.get loc to prom = Some (from, msg)>>))).
    { des. eapply Cell.max_ts_spec in INHABITED0. des.
      exists (Time.join max (Cell.max_ts (prom loc))). econs.
      { unfold Time.join. des_ifs; eauto. left. eauto. }
      { i. etrans; [|eapply Time.join_l].
        eapply Memory.max_concrete_ts_spec in GET1; eauto. des. auto. }
      { i. etrans; [|eapply Time.join_r].
        eapply Cell.max_ts_spec in GET1; eauto. des. auto. }
    }
    { exists max. econs.
      { left. eauto. }
      { i. eapply Memory.max_concrete_ts_spec in GET0; eauto. des. auto. }
      { i. exfalso. eauto. }
    }
  Qed.

  Lemma concrete_promise_max_ts_max_ts mem prom loc ts
        (MAX: concrete_promise_max_ts mem prom loc ts)
        (MLE: Memory.le prom mem)
    :
      Time.le ts (Memory.max_ts loc mem).
  Proof.
    inv MAX. des.
    { eapply Memory.max_ts_spec; eauto. }
    { eapply Memory.max_ts_spec; eauto. }
  Qed.

  Lemma concrete_promise_max_ts_max_concrete_ts mem prom loc ts max
        (MAX: concrete_promise_max_ts mem prom loc ts)
        (CONCRETE: Memory.max_concrete_ts mem loc max)
    :
      Time.le max ts.
  Proof.
    inv CONCRETE. des. eapply MAX in GET; eauto.
  Qed.

  Definition concrete_promise_max_timemap mem prom tm: Prop :=
    forall loc, concrete_promise_max_ts mem prom loc (tm loc).

  Lemma concrete_promise_max_timemap_inj mem prom tm0 tm1
        (MAX0: concrete_promise_max_timemap mem prom tm0)
        (MAX1: concrete_promise_max_timemap mem prom tm1)
    :
      tm0 = tm1.
  Proof.
    extensionality loc.
    eapply concrete_promise_max_ts_inj; eauto.
  Qed.

  Lemma concrete_promise_max_timemap_exists mem prom
        (INHABITED: Memory.inhabited mem)
    :
      exists tm, (<<MAX: concrete_promise_max_timemap mem prom tm>>).
  Proof.
    eapply choice. i. eapply concrete_promise_max_ts_exists; eauto.
  Qed.

  Lemma map_ident_concrete_promises mem prom tm (f: Loc.t -> Time.t -> Time.t -> Prop)
        (MAX: concrete_promise_max_timemap mem prom tm)
        (IDENT: forall loc ts (TS: Time.le ts (tm loc)), f loc ts ts)
        (MAPLT: mapping_map_lt f)
        (CLOSED: Memory.closed mem)
        (MLE: Memory.le prom mem)
    :
      promises_map f prom prom.
  Proof.
    assert (CONCRETE: map_ident_concrete f mem).
    { ii. inv CONCRETE. eapply MAX in GET. auto. }
    econs.
    { i. exists to, from, msg. splits; auto.
      { eapply mapping_map_lt_non_collapsable; eauto. }
      { eapply IDENT. eapply MAX in GET; eauto. }
      { eapply map_ident_concrete_closed_message; eauto.
        eapply MLE in GET. eapply CLOSED; eauto. }
    }
    { i. exists fto, ffrom, fmsg. splits; auto.
      { eapply IDENT. eapply MAX in GET; eauto. }
      { eapply IDENT. transitivity fto.
        { eapply memory_get_ts_le; eauto. }
        { eapply MAX in GET; eauto. }
      }
    }
  Qed.

  Lemma memory_ident_map_concrete_max f mem fmem
        (MEM: memory_map f mem fmem)
        (IDENT: forall loc to fto (MAP: f loc to fto), to = fto)
        loc max fmax
        (CLOSED: Memory.closed mem)
        (MAX: Memory.max_concrete_ts mem loc max)
        (FMAX: Memory.max_concrete_ts fmem loc fmax)
    :
      Time.le max fmax.
  Proof.
    eapply Memory.max_concrete_ts_spec in MAX; eauto.
    { des. eapply MEM in GET. des; ss. inv MSG. inv MSGLE.
      eapply Memory.max_concrete_ts_spec in GET; eauto. des.
      eapply IDENT in TO. subst. auto. }
    { eapply CLOSED. }
  Qed.

  Lemma memory_ident_map_concrete_promise_max_timemap
        f mem_src mem_tgt prom_src prom_tgt tm_src tm_tgt
        (MAXSRC: concrete_promise_max_timemap mem_src prom_src tm_src)
        (MAXTGT: concrete_promise_max_timemap mem_tgt prom_tgt tm_tgt)
        (LOCAL: promises_map f prom_tgt prom_src)
        (MEM: memory_map f mem_tgt mem_src)
        (IDENT: forall loc to fto (MAP: f loc to fto), to = fto)
    :
      TimeMap.le tm_tgt tm_src.
  Proof.
    ii. specialize (MAXTGT loc). inv MAXTGT. des.
    { eapply MEM in GET. des; ss.
      eapply IDENT in TO. subst. inv MSG. inv MSGLE.
      eapply MAXSRC in GET. auto. }
    { eapply LOCAL in GET. des; ss.
      eapply IDENT in TO. subst.
      eapply MAXSRC in GET. auto. }
  Qed.

End CONCRETEMAX.


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
          eapply cancels_promises_decrease in STEPS0; auto. ss.
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


Definition pf_consistent_strong_aux lang (e0:Thread.t lang): Prop :=
  forall mem1
         (CAP: Memory.cap e0.(Thread.memory) mem1),
  exists tr e1 times,
    (<<STEPS: Trace.steps tr (Thread.mk _ e0.(Thread.state) e0.(Thread.local) TimeMap.bot mem1) e1>>) /\
    (<<EVENTS: List.Forall (fun em => <<SAT: (promise_free /1\ no_sc /1\ (wf_time_evt (fun loc to => List.In to (times loc)))) (snd em)>> /\ <<TAU: ThreadEvent.get_machine_event (snd em) = MachineEvent.silent>>) tr >>) /\
    (__guard__((exists st',
                   (<<LOCAL: Local.failure_step e1.(Thread.local)>>) /\
                   (<<FAILURE: Language.step lang ProgramEvent.failure (@Thread.state lang e1) st'>>)) \/
               ((<<PROMISES: e1.(Thread.local).(Local.promises) = Memory.bot>>) /\
                (<<WRITES: forall loc from to val released
                                  (GET: Memory.get loc to e0.(Thread.local).(Local.promises) = Some (from, Message.concrete val released)),
                    exists th e,
                      (<<WRITING: promise_writing_event loc from to val released e>>) /\
                      (<<IN: List.In (th, e) tr>>)>>)))).

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
  hexploit (proj1 (@pred_steps_trace_steps (promise_free /1\ no_sc) _ (Thread.mk _ th.(Thread.state) th.(Thread.local) TimeMap.bot mem1) e2)).
  { etrans; eauto. } i. des.
  exploit trace_times_list_exists; eauto. i. des.
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
           (maxmap: TimeMap.t)
           (loc: Loc.t) (fts: Time.t): Prop :=
  ((<<IN: List.In fts (times loc)>>) /\ (<<TS: Time.le fts (max loc)>>)) \/
  (exists ts n,
      (<<IN: List.In ts (times loc)>>) /\ (<<TS: Time.lt (max loc) ts>>)
      /\ (<<MAX: Time.lt (maxmap loc) (incr_time_seq n)>>)
      /\ (<<MAP: f loc n ts fts>>)).

Lemma certification_times_well_ordered times f max maxmap tm
      (MAP: forall loc n
                   (TS: Time.lt (maxmap loc) (incr_time_seq n)),
          cap_flex_map_loc
            (max loc)
            (tm loc)
            (incr_time_seq n) (times loc) (f loc n))
      (TM: forall loc, Time.lt (maxmap loc) (tm loc))
      (MAXMAP: TimeMap.le max maxmap)
  :
    forall loc, well_ordered (certification_times times f max maxmap loc).
Proof.
  i. hexploit (@increasing_join_well_ordered
                 incr_time_seq
                 (fun n fts =>
                    (exists ts,
                        (<<IN: List.In ts (times loc)>>)
                        /\ (<<TS: Time.lt (max loc) ts>>)
                        /\ (<<MAX: Time.lt (maxmap loc) (incr_time_seq n)>>)
                        /\ (<<MAP: f loc n ts fts>>)))).
  { i. eapply incr_time_seq_lt; eauto. }
  { eapply incr_time_seq_diverge. }
  { i. des. exploit MAP; eauto. intros FLEXMAP.
    eapply (FLEXMAP.(cap_flex_map_loc_bound)); try apply MAP0. auto. }
  { i. destruct (classic (Time.lt (maxmap loc) (incr_time_seq n))).
    { specialize (MAP _ _ H). eapply mapped_well_ordered.
      { eapply MAP. }
      { eapply (finite_well_ordered (times loc)). }
      i. des. esplits; eauto.
    }
    { eapply sub_well_ordered.
      { eapply empty_well_ordered. }
      i. des; ss.
    }
  }
  intros WO.
  eapply sub_well_ordered.
  { eapply join_well_ordered.
    { eapply WO. }
    { eapply (finite_well_ordered (times loc)). }
  }
  { i. unfold certification_times in *. des; eauto. left. esplits; eauto. }
Qed.


Definition pf_consistent_flex lang (e0:Thread.t lang)
           (tr : Trace.t) (times : Loc.t -> list Time.t)
           (f: Loc.t -> nat -> (Time.t -> Time.t -> Prop))
  : Prop :=
  forall max
         (MAX: concrete_promise_max_timemap
                 (e0.(Thread.memory))
                 (e0.(Thread.local).(Local.promises))
                 max),
    (<<MAP: forall loc n
                   (TS: Time.lt (Memory.max_ts loc e0.(Thread.memory)) (incr_time_seq n)),
        cap_flex_map_loc
          (max loc)
          (Time.incr (Memory.max_ts loc e0.(Thread.memory)))
          (incr_time_seq n) (times loc) (f loc n)>>) /\
    (<<CONSISTENT: forall mem1 (tm: Loc.t -> nat)
                          (TM: forall loc, Time.lt (Memory.max_ts loc e0.(Thread.memory)) (incr_time_seq (tm loc)))
                          (CAP: cap_flex e0.(Thread.memory) mem1 (fun loc => incr_time_seq (tm loc))),
        exists ftr e1,
          (<<STEPS: Trace.steps ftr (Thread.mk _ e0.(Thread.state) e0.(Thread.local) TimeMap.bot mem1) e1>>) /\
          (<<EVENTS: List.Forall (fun em => <<SAT: (promise_free
                                                      /1\ no_sc
                                                      /1\ write_not_in (fun loc ts => (<<TS: Time.le ts (incr_time_seq (tm loc))>>) /\ (<<PROM: ~ covered loc ts e0.(Thread.local).(Local.promises)>>))
                                                      /1\ wf_time_evt (fun loc => certification_times times f max (Memory.max_timemap e0.(Thread.memory)) loc)
                                                      /1\ no_read_msgs (fun loc ts => ~ (covered loc ts e0.(Thread.local).(Local.promises) \/ concrete_promised e0.(Thread.memory) loc ts \/ Time.lt (incr_time_seq (tm loc)) ts))) (snd em)>> /\ <<TAU: ThreadEvent.get_machine_event (snd em) = MachineEvent.silent>>) ftr >>) /\
          (<<TRACE: List.Forall2 (fun em fem => tevent_map (fun loc => f loc (tm loc)) (snd fem) (snd em)) tr ftr>>) /\
          (__guard__((exists st',
                         (<<LOCAL: Local.failure_step e1.(Thread.local)>>) /\
                         (<<FAILURE: Language.step lang ProgramEvent.failure (@Thread.state lang e1) st'>>)) \/
                     ((<<PROMISES: e1.(Thread.local).(Local.promises) = Memory.bot>>) /\
                      (<<WRITES: forall loc from to val released
                                        (GET: Memory.get loc to e0.(Thread.local).(Local.promises) = Some (from, Message.concrete val released)),
                          exists th e,
                            (<<WRITING: promise_writing_event loc from to val released e>>) /\
                            (<<IN: List.In (th, e) ftr>>)>>))))>>).


Lemma pf_consistent_strong_aux_pf_consistent_flex lang (th: Thread.t lang)
      (WF: Local.wf th.(Thread.local) th.(Thread.memory))
      (MEM: Memory.closed th.(Thread.memory))
      (CONSISTENT: pf_consistent_strong_aux th)
  :
    exists tr times f, <<CONSISTENT: pf_consistent_flex th tr times f>>.
Proof.
  exploit Memory.cap_exists; eauto. i. des.
  exploit CONSISTENT; eauto. i. des. exists tr, times.
  hexploit (@concrete_promise_max_timemap_exists
              (th.(Thread.memory))
              (th.(Thread.local).(Local.promises))).
  { eapply MEM. } intros [max MAX]. des.
  hexploit (@choice
              (Loc.t * nat)
              (Time.t -> Time.t -> Prop)
              (fun locn f =>
                 let (loc, n) := locn in
                 forall
                   (TS: Time.lt (Memory.max_ts loc th.(Thread.memory)) (incr_time_seq n)),
                   cap_flex_map_loc
                     (max loc)
                     (Time.incr (Memory.max_ts loc th.(Thread.memory)))
                     (incr_time_seq n) (times loc) f)).
  { intros [loc n].
    destruct (classic (Time.lt (Memory.max_ts loc th.(Thread.memory)) (incr_time_seq n))).
    { des. hexploit (@cap_flex_map_loc_exists
                       (max loc)
                       (Time.incr (Memory.max_ts loc (Thread.memory th)))
                       (incr_time_seq n)).
      { eapply TimeFacts.le_lt_lt.
        { eapply concrete_promise_max_ts_max_ts; eauto. eapply WF. }
        { eapply Time.incr_spec. }
      }
      { eapply TimeFacts.le_lt_lt.
        { eapply concrete_promise_max_ts_max_ts; eauto. eapply WF. }
        { auto. }
      }
      i. des. eauto. }
    { exists bot2. i. exfalso. eapply H. auto. }
  }
  intros [f SPEC]. des. exists (fun loc ts => f (loc, ts)). ii.
  assert (max0 = max).
  { eapply concrete_promise_max_timemap_inj; eauto. } subst. econs.
  { ii. specialize (SPEC (loc, n)). ss. eauto. }
  ii. assert (MAP: cap_flex_map
                     max
                     (fun loc => Time.incr (Memory.max_ts loc (Thread.memory th)))
                     (fun loc => incr_time_seq (tm loc))
                     times (fun loc => f (loc, tm loc))).
  { eapply cap_flex_map_locwise. i.
    eapply (SPEC (loc, tm loc)). eauto. }

  assert (IDENT: map_ident_concrete (fun loc => f (loc, tm loc)) th.(Thread.memory)).
  { ii. inv CONCRETE. eapply MAX in GET. eapply MAP; eauto. }
  destruct e1. ss.
  hexploit trace_steps_map.
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
  { econs.
    { refl. }
    { eapply map_ident_concrete_closed_tview; eauto. eapply WF. }
    { eapply map_ident_concrete_promises; eauto.
      { i. eapply MAP; eauto. }
      { eapply MAP. }
      { eapply WF. }
    }
  }
  { exploit (@Memory.max_concrete_timemap_exists th.(Thread.memory)).
    { eapply MEM. } i. des.
    eapply concrete_messages_le_cap_flex_memory_map.
    { refl. }
    { eauto. }
    { ii. eapply concrete_promise_max_ts_max_concrete_ts; eauto. }
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
    cut ((promise_free /1\ no_sc) (snd x) /\ ThreadEvent.get_machine_event (snd x) = MachineEvent.silent).
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
        eapply wf_time_evt_map in EVENT; eauto. eapply wf_time_evt_mon; try apply EVENT.
        i. ss. des. destruct (Time.le_lt_dec ts (max x0)).
        { left. assert (ts = x2).
          { eapply mapping_map_lt_map_eq.
            { eapply MAP. }
            { ss. eapply MAP. eauto. }
            { eauto. }
          }
          subst. splits; auto.
        }
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
  { eapply list_Forall2_impl; eauto. i. ss. des. auto. }
  { ss. unguard. des; eauto.
    { left. esplits; eauto. eapply failure_step_map; eauto.
      { eapply mapping_map_lt_map_le. eapply MAP. }
      { eapply mapping_map_lt_map_eq. eapply MAP. }
    }
    { right. splits.
      { inv LOCAL. erewrite PROMISES in *. eapply bot_promises_map; eauto. }
      { i. exploit WRITES; eauto. i. des.
        eapply list_Forall2_in2 in IN; eauto. des.
        destruct b. ss. eexists t, _. splits; try apply IN0.
        eapply promise_writing_event_map; eauto.
        { inv WF. eapply PROMISES0 in GET. eauto. }
        { eapply MAP. }
        { ii. ss. eapply MAP. eapply MAX in GET0. etrans; eauto. }
      }
    }
  }
Qed.

Definition pf_consistent_flex_aux lang (e0:Thread.t lang)
           (tr : Trace.t) (times : Loc.t -> list Time.t)
           (f: Loc.t -> nat -> (Time.t -> Time.t -> Prop))
  : Prop :=
  forall max
         (MAX: concrete_promise_max_timemap
                 (e0.(Thread.memory))
                 (e0.(Thread.local).(Local.promises))
                 max),
    (<<MAP: forall loc n
                   (TS: Time.lt (Memory.max_ts loc e0.(Thread.memory)) (incr_time_seq n)),
        cap_flex_map_loc
          (max loc)
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
          (<<STEPS: Trace.steps ftr (Thread.mk _ e0.(Thread.state) e0.(Thread.local) TimeMap.bot mem1) e1>>) /\
          (<<EVENTS: List.Forall (fun em => <<SAT: (promise_free
                                                      /1\ no_sc
                                                      /1\ write_not_in (fun loc ts => (<<TS: Time.le ts (incr_time_seq (tm loc))>>) /\ (<<PROM: ~ covered loc ts e0.(Thread.local).(Local.promises)>>))
                                                      /1\ no_read_msgs (fun loc ts => ~ (covered loc ts e0.(Thread.local).(Local.promises) \/ concrete_promised e0.(Thread.memory) loc ts \/ Time.lt (incr_time_seq (tm loc)) ts))
                                                      /1\ wf_time_evt (fun loc => certification_times times f max (Memory.max_timemap e0.(Thread.memory)) loc)) (snd em)>> /\ <<TAU: ThreadEvent.get_machine_event (snd em) = MachineEvent.silent>>) ftr >>) /\
          (<<TRACE: List.Forall2 (fun em fem => tevent_map (fun loc => f loc (tm loc)) (snd fem) (snd em)) tr ftr>>) /\
          (__guard__((exists st',
                         (<<LOCAL: Local.failure_step e1.(Thread.local)>>) /\
                         (<<FAILURE: Language.step lang ProgramEvent.failure (@Thread.state lang e1) st'>>)) \/
                     ((<<PROMISES: e1.(Thread.local).(Local.promises) = Memory.bot>>) /\
                      (<<WRITES: forall loc from to val released
                                        (GET: Memory.get loc to e0.(Thread.local).(Local.promises) = Some (from, Message.concrete val released)),
                          exists th e,
                            (<<WRITING: promise_writing_event loc from to val released e>>) /\
                            (<<IN: List.In (th, e) ftr>>)>>))))>>).

Lemma pf_consistent_flex_pf_consistent_flex_aux lang (th: Thread.t lang) tr times f
      (WF: Local.wf th.(Thread.local) th.(Thread.memory))
      (MEM: Memory.closed th.(Thread.memory))
      (CONSISTENT: pf_consistent_flex th tr times f)
  :
    pf_consistent_flex_aux th tr times f.
Proof.
  ii. specialize (CONSISTENT _ MAX). des. econs; eauto.
  ii. exploit (@cap_flex_exists th.(Thread.memory) (fun loc => incr_time_seq (tm loc))); eauto. i. des.
  exploit CONSISTENT0; eauto. i. des. destruct e1. ss.
  hexploit trace_steps_map.
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
    cut ((promise_free /1\ no_sc) (snd x) /\ ThreadEvent.get_machine_event (snd x) = MachineEvent.silent).
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
        destruct b. ss. eexists t, _. splits; try apply IN0.
        eapply promise_writing_event_map; eauto.
        { inv LOCAL. eapply PROMISES0 in GET. eauto. }
        { eapply ident_map_lt. }
        { ii. ss. }
      }
    }
  }
Qed.

Definition pf_consistent_super_strong lang (e0:Thread.t lang)
           (tr : Trace.t)
           (times: Loc.t -> (Time.t -> Prop))
  : Prop :=
  forall mem1 tm sc max
         (FUTURE: Memory.future_weak e0.(Thread.memory) mem1)
         (CLOSED: Memory.closed mem1)
         (LOCAL: Local.wf e0.(Thread.local) mem1)
         (MAX: concrete_promise_max_timemap
                 (e0.(Thread.memory))
                 (e0.(Thread.local).(Local.promises))
                 max),
  exists ftr e1 f,
    (<<STEPS: Trace.steps ftr (Thread.mk _ e0.(Thread.state) e0.(Thread.local) sc mem1) e1>>) /\
    (<<EVENTS: List.Forall (fun em => <<SAT: (promise_free
                                                /1\ no_sc
                                                /1\ no_read_msgs (fun loc ts => ~ (covered loc ts e0.(Thread.local).(Local.promises) \/ concrete_promised e0.(Thread.memory) loc ts \/ Time.lt (tm loc) ts))
                                                /1\ write_not_in (fun loc ts => (<<TS: Time.le ts (tm loc)>>) /\ (<<PROM: ~ covered loc ts e0.(Thread.local).(Local.promises)>>))
                                                /1\ wf_time_evt times) (snd em)>> /\ <<TAU: ThreadEvent.get_machine_event (snd em) = MachineEvent.silent>>) ftr >>) /\
    (<<MAPLT: mapping_map_lt f>>) /\
    (<<MAPIDENT: forall loc ts fts
                     (TS: Time.le fts (max loc))
                     (MAP: f loc ts fts),
        ts = fts>>) /\
    (<<BOUND: forall loc ts fts (TS: Time.lt (max loc) fts) (MAP: f loc ts fts),
        Time.le (tm loc) fts>>) /\
    (<<TRACE: List.Forall2 (fun em fem => tevent_map f (snd fem) (snd em)) tr ftr>>) /\
    (<<GOOD: good_future tm mem1 e1.(Thread.memory)>>) /\
    (<<SC: e1.(Thread.sc) = sc>>) /\
    (__guard__((exists st',
                   (<<LOCAL: Local.failure_step e1.(Thread.local)>>) /\
                   (<<FAILURE: Language.step lang ProgramEvent.failure (@Thread.state lang e1) st'>>)) \/
               ((<<PROMISES: e1.(Thread.local).(Local.promises) = Memory.bot>>) /\
                (<<WRITES: forall loc from to val released
                                  (GET: Memory.get loc to e0.(Thread.local).(Local.promises) = Some (from, Message.concrete val released)),
                    exists th e,
                      (<<WRITING: promise_writing_event loc from to val released e>>) /\
                      (<<IN: List.In (th, e) ftr>>)>>)))).

Lemma pf_consistent_flex_aux_pf_consistent_super_strong lang (th: Thread.t lang) tr times f
      (WF: Local.wf th.(Thread.local) th.(Thread.memory))
      (MEM: Memory.closed th.(Thread.memory))
      (CONSISTENT: pf_consistent_flex_aux th tr times f)
  :
    exists certimes,
      (<<WO: forall loc, well_ordered (certimes loc)>>) /\
      (<<CONSISTENT: pf_consistent_super_strong th tr certimes>>).
Proof.
  hexploit (@concrete_promise_max_timemap_exists
              (th.(Thread.memory))
              (th.(Thread.local).(Local.promises))).
  { eapply MEM. } intros [max MAX]. specialize (CONSISTENT _ MAX). des.
  exists (certification_times times f max (Memory.max_timemap th.(Thread.memory))). splits.
  { eapply certification_times_well_ordered; eauto.
    { i. eapply MAP. auto. }
    { i. ss. eapply Time.incr_spec. }
    { ii. eapply concrete_promise_max_ts_max_ts; eauto. eapply WF. }
  }
  ii. assert (max0 = max).
  { eapply concrete_promise_max_timemap_inj; eauto. } subst.
  assert (TM: exists (ftm: Loc.t -> nat),
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
  { eapply List.Forall_impl; eauto. i. ss. des. auto. } i. des.
  assert (CAP: cap_flex_map
                 max
                 (fun loc : Loc.t => Time.incr (Memory.max_ts loc (Thread.memory th))) (fun loc => incr_time_seq (ftm loc)) times (fun loc => f loc (ftm loc))).
  { eapply cap_flex_map_locwise. i. eapply MAP. eapply TM. }
  eexists tr_src, _, (fun loc => f loc (ftm loc)).
  esplits; eauto.
  { eapply List.Forall_forall. i.
    eapply list_Forall2_in2 in H; eauto. des. rewrite SAT.
    eapply List.Forall_forall in EVENTS; eauto. ss. des. splits; auto.
    { eapply no_read_msgs_mon; eauto. i. ss. ii. eapply PR. des; auto.
      right. right. eapply TimeFacts.le_lt_lt; eauto. eapply TM. }
    { eapply write_not_in_mon; eauto. i. ss. des. split; auto.
      red. etrans; eauto. eapply TM. }
  }
  { eapply CAP. }
  { i. destruct (Time.le_lt_dec ts (max loc)).
    { eapply CAP in l. eapply mapping_map_lt_map_eq.
      { eapply CAP. }
      { ss. eauto. }
      { ss. }
    }
    { eapply CAP.(cap_flex_map_bound) in l; eauto.
      exfalso. eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt.
      { eapply l. } eapply TimeFacts.le_lt_lt.
      { eapply TS. } eapply TimeFacts.le_lt_lt.
      { eapply concrete_promise_max_ts_max_ts; eauto. eapply WF. }
      { eapply TM. }
    }
  }
  { i. destruct (Time.le_lt_dec ts (max loc)).
    { dup l. eapply CAP in l. exploit mapping_map_lt_map_eq.
      { eapply CAP. }
      { eapply MAP0. }
      { eapply l. }
      i. subst. timetac. }
    { eapply CAP.(cap_flex_map_bound) in l; eauto. etrans; eauto. eapply TM. }
  }
  { eapply list_Forall2_rev in EVENTS0.
    eapply list_Forall2_compose; eauto. i. ss. rewrite SAT1. auto. }
  { eapply good_future_mon; eauto. ii. apply TM. }
  { eapply no_sc_same_sc_traced in STEPS0; eauto.
    eapply List.Forall_forall. i.
    eapply list_Forall2_in2 in H; eauto. des. rewrite SAT.
    eapply List.Forall_forall in EVENTS; eauto. ss. des. splits; auto. }
  { ss. unguard. des; eauto. right. splits; auto. i.
    eapply WRITES in GET. des.
    eapply list_Forall2_in in EVENTS0; eauto. des. destruct a. ss. subst.
    esplits; eauto. }
Qed.

Lemma consistent_pf_consistent_super_strong lang (th: Thread.t lang)
      (LOCAL: Local.wf th.(Thread.local) th.(Thread.memory))
      (MEM: Memory.closed th.(Thread.memory))
      (CONSISTENT: Thread.consistent th)
  :
    exists tr certimes,
      (<<WO: forall loc, well_ordered (certimes loc)>>) /\
      <<CONSISTENT: pf_consistent_super_strong th tr certimes>>.
Proof.
  eapply consistent_pf_consistent in CONSISTENT; eauto.
  eapply pf_consistent_pf_consistent_strong in CONSISTENT; eauto.
  eapply pf_consistent_strong_pf_consistent_strong_aux in CONSISTENT; eauto.
  eapply pf_consistent_strong_aux_pf_consistent_flex in CONSISTENT; eauto. des.
  eapply pf_consistent_flex_pf_consistent_flex_aux in CONSISTENT0; eauto.
  eapply pf_consistent_flex_aux_pf_consistent_super_strong in CONSISTENT0; eauto.
Qed.

Lemma pf_consistent_super_strong_consistent lang (th: Thread.t lang)
      (LOCAL: Local.wf th.(Thread.local) th.(Thread.memory))
      (MEM: Memory.closed th.(Thread.memory))
      tr certimes
      (CONSISTENT: pf_consistent_super_strong th tr certimes)
  :
    Thread.consistent th.
Proof.
  hexploit (@concrete_promise_max_timemap_exists
              (th.(Thread.memory))
              (th.(Thread.local).(Local.promises))).
  { eapply MEM. } intros [max MAX]. des.
  ii. exploit (CONSISTENT mem1 sc1 sc1).
  { eapply Memory.cap_future_weak; eauto. }
  { eapply Memory.cap_closed; eauto. }
  { eapply Local.cap_wf; eauto. }
  { eauto. }
  i. des.
  eapply pred_steps_trace_steps2 in STEPS; cycle 1.
  { instantiate (1:=fun _ => True). eapply List.Forall_impl; eauto.
    i. ss. des. splits; auto. }
  eapply thread_steps_pred_steps in STEPS.
  unguard. des.
  { destruct e1. ss. left. econs. esplits; eauto. }
  { right. esplits; eauto. }
Qed.

Definition pf_consistent_super_strong_mon lang e0 tr certimes0 certimes1
           (CONSISTENT: @pf_consistent_super_strong
                          lang e0 tr certimes0)
           (LE: certimes0 <2= certimes1)
  :
    pf_consistent_super_strong e0 tr certimes1.
Proof.
  ii. exploit CONSISTENT; eauto. i. des. esplits; eauto.
  eapply List.Forall_impl; eauto. i. ss. des. splits; auto.
  eapply wf_time_evt_mon; eauto.
Qed.

Lemma good_future_future_future mem0 mem_good0 mem_good1 tm
      (f0: Loc.t -> Time.t -> Time.t -> Prop)
      (IDENT: forall loc to fto (MAP: f0 loc to fto), to = fto)
      (MAPBOT: mapping_map_bot f0)
      (GOOD: memory_map f0 mem0 mem_good0)
      (FUTURE: Memory.future_weak mem_good0 mem_good1)
      (CLOSED: Memory.closed mem0)
      (TM0: forall loc, Time.lt (Memory.max_ts loc mem_good1) (tm loc))
      (TM1: forall loc, Time.lt (Memory.max_ts loc mem0) (tm loc))
  :
    exists mem1,
      (<<CAP: cap_flex mem0 mem1 tm>>) /\
      (<<MAP: memory_map ident_map mem1 mem_good1>>).
Proof.
  exploit (@cap_flex_exists mem0 tm); eauto. intros [mem1 CAP].
  exists mem1. splits; auto. econs.
  { i. eapply cap_flex_inv in GET; eauto. des; auto.
    apply GOOD in GET. des; auto. destruct fmsg as [val freleased|]; cycle 1.
    { inv MSGLE. inv MSG. auto. }
    eapply Memory.future_weak_get1 in GET; eauto. des.
    dup MSG. dup MSGLE. dup MSG_LE.
    inv MSG; inv MSGLE; inv MSG_LE; auto.
    right. esplits; cycle 3.
    { eauto. }
    { eapply IDENT; eauto. }
    { eapply message_map_incr; eauto. }
    { econs; eauto. }
  }
  { i. left. exists (tm loc), Time.bot, (tm loc), Time.bot. splits; ss.
    { eapply Time.bot_spec. }
    { eapply Memory.max_ts_spec in GET. des. left.
      eapply TimeFacts.le_lt_lt; eauto. }
    { i. erewrite cap_flex_covered in ITV; eauto. }
  }
Qed.

Lemma good_future_consistent times lang st lc_src lc_tgt sc_src sc_tgt mem_src mem_tgt tr
      (f: Loc.t -> Time.t -> Time.t -> Prop)
      (CONSISTENT: pf_consistent_super_strong
                     (Thread.mk lang st lc_tgt sc_tgt mem_tgt)
                     tr times)
      (IDENT: forall loc to fto (MAP: f loc to fto), to = fto)
      (MAPBOT: mapping_map_bot f)
      (LOCALSRC: Local.wf lc_src mem_src)
      (LOCALTGT: Local.wf lc_tgt mem_tgt)
      (MEMSRC: Memory.closed mem_src)
      (MEMTGT: Memory.closed mem_tgt)
      (LOCAL: local_map f lc_tgt lc_src)
      (MEM: memory_map f mem_tgt mem_src)
  :
    pf_consistent_super_strong (Thread.mk lang st lc_src sc_src mem_src) tr times.
Proof.
  ii. ss.
  set (tm0 := TimeMap.join tm
                           (fun loc => Time.incr
                                         (Time.join
                                            (max loc)
                                            (Time.join
                                               (Memory.max_ts loc mem1)
                                               (Memory.max_ts loc mem_tgt))))).
  assert (TM0: forall loc, Time.lt (Memory.max_ts loc mem1) (tm0 loc)).
  { i. unfold tm0. eapply TimeFacts.le_lt_lt.
    { eapply Time.join_l. } eapply TimeFacts.le_lt_lt.
    { eapply Time.join_r. } eapply TimeFacts.lt_le_lt.
    { eapply Time.incr_spec. }
    { eapply Time.join_r. }
  }
  assert (TM1: forall loc, Time.lt (Memory.max_ts loc mem_tgt) (tm0 loc)).
  { i. unfold tm0. eapply TimeFacts.le_lt_lt.
    { eapply Time.join_r. } eapply TimeFacts.le_lt_lt.
    { eapply Time.join_r. } eapply TimeFacts.lt_le_lt.
    { eapply Time.incr_spec. }
    { eapply Time.join_r. }
  }
  assert (TM2: TimeMap.le tm tm0).
  { eapply TimeMap.join_l. }
  assert (TM3: forall loc, Time.lt (max loc) (tm0 loc)).
  { i. unfold tm0. eapply TimeFacts.le_lt_lt.
    { eapply Time.join_l. } eapply TimeFacts.lt_le_lt.
    { eapply Time.incr_spec. }
    { eapply Time.join_r. }
  }
  exploit good_future_future_future; eauto. i. des.
  exploit (@concrete_promise_max_timemap_exists mem_tgt lc_tgt.(Local.promises)).
  { eapply MEMTGT. } intros [max_tgt MAXTGT].
  assert (MAXMAP: TimeMap.le max_tgt max).
  { eapply memory_ident_map_concrete_promise_max_timemap; eauto.
    eapply LOCAL. }

  exploit (CONSISTENT mem0 tm0 TimeMap.bot); eauto.
  { ss. eapply cap_flex_future_weak; eauto. }
  { eapply cap_flex_closed; eauto. }
  { ss. eapply cap_flex_wf; eauto. }
  ss. i. des. destruct e1. ss.
  hexploit trace_steps_map.
  { eapply ident_map_le; eauto. }
  { eapply ident_map_bot; eauto. }
  { eapply ident_map_eq; eauto. }
  { eapply List.Forall_forall. i. eapply ident_map_mappable_evt. }
  { eauto. }
  { ss. }
  { ss. }
  { ss. }
  { eapply cap_flex_wf; eauto. }
  { eapply LOCAL0. }
  { eauto. }
  { eapply cap_flex_closed; eauto. }
  { eapply Memory.closed_timemap_bot. eapply CLOSED. }
  { eapply Memory.closed_timemap_bot.
    eapply cap_flex_closed in CAP; eauto. eapply CAP. }
  { eapply local_map_incr; eauto. eapply ident_map_lt; eauto. }
  { eauto. }
  { eapply mapping_map_lt_collapsable_unwritable; eauto. eapply ident_map_lt. }
  { eapply ident_map_timemap. }
  { refl. }
  i. des.
  exploit no_sc_any_sc_traced; try apply STEPS0; eauto.
  { eapply List.Forall_forall. i.
    eapply list_Forall2_in in H; eauto. des. destruct a, x. ss.
    eapply List.Forall_forall in IN; eauto. ss. des. inv EVENT; ss. }
  i. des. exists tr_src.
  assert (NOTIN: List.Forall
                   (fun em =>
                      ((((promise_free (snd em) /\ no_sc (snd em)) /\
                         no_read_msgs
                           (fun loc ts =>
                              ~
                                (covered loc ts (Local.promises lc_src) \/
                                 concrete_promised mem_src loc ts \/ Time.lt (tm loc) ts))
                           (snd em)) /\
                        write_not_in
                          (fun loc ts =>
                             Time.le ts (tm0 loc) /\ ~ covered loc ts (Local.promises lc_src))
                          (snd em)) /\ wf_time_evt times (snd em)) /\
                      ThreadEvent.get_machine_event (snd em) = MachineEvent.silent) tr_src).
  { eapply List.Forall_forall. i.
    eapply list_Forall2_in2 in H; eauto. des. clear EVENTS0.
    eapply list_Forall2_in in IN; eauto. des.
    eapply List.Forall_forall in IN0; eauto. ss. des.
    destruct a, b, x. ss. subst. inv EVENT; splits; ss.
    { inv KIND; ss. inv MSG0; ss. inv MSG; ss. inv MAP1; ss. }
    { inv KIND; ss. inv FROM. inv TO. ii. eapply SAT2; eauto. des. split; auto.
      inv LOCAL. erewrite <- promises_ident_map_covered in H0; eauto. }
    { inv FROM. inv TO. des. splits; auto. }
    { inv TO. apply NNPP in SAT3. ii. apply H. des; auto.
      { inv LOCAL. erewrite promises_ident_map_covered in SAT3; eauto. }
      { eapply memory_ident_map_concrete in SAT3; eauto. }
      { right. right. eapply TimeFacts.le_lt_lt; eauto. }
    }
    { inv FROM. inv TO. ii. eapply SAT2; eauto. des. split; auto.
      inv LOCAL. erewrite <- promises_ident_map_covered in H0; eauto. }
    { inv FROM. inv TO. des. splits; auto. }
    { inv TO. inv FROM. apply NNPP in SAT3. ii. apply H. des; auto.
      { inv LOCAL. erewrite promises_ident_map_covered in SAT3; eauto. }
      { eapply memory_ident_map_concrete in SAT3; eauto. }
      { right. right. eapply TimeFacts.le_lt_lt; eauto. }
    }
    { inv FROM. inv TO. ii. eapply SAT2; eauto. des. split; auto.
      inv LOCAL. erewrite <- promises_ident_map_covered in H0; eauto. }
    { inv FROM. inv TO. auto. }
  }
  esplits; eauto; ss.
  { eapply List.Forall_impl; eauto. i. ss. des. splits; auto.
    eapply write_not_in_mon; eauto. i. ss. des. split; auto. etrans; eauto. }
  { i. destruct (Time.le_lt_dec fts (max_tgt loc)); eauto.
    dup l. exploit BOUND; eauto.
    i. exfalso. eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt.
    { eapply x. } eapply TimeFacts.le_lt_lt.
    { eapply TS. } eauto.
  }
  { i. exploit BOUND.
    { eapply TimeFacts.le_lt_lt.
      { eapply MAXMAP. }
      { eapply TS. }
    }
    { eauto. }
    { i. etrans; eauto. }
  }
  { eapply list_Forall2_rev in EVENTS0.
    eapply list_Forall2_compose.
    { eapply TRACE. }
    { eapply list_Forall2_compose.
      { eauto. }
      { eauto. }
      i. simpl in *. des. rewrite <- SAT1 in *.
      instantiate (1:=fun em fem : Local.t * ThreadEvent.t => tevent_map ident_map (snd fem) (snd em)).
      auto. }
    { i. ss. eapply ident_map_compose_tevent; eauto. }
  }
  { eapply write_not_in_good_future_traced in STEPS0; ss.
    { eapply good_future_mon; eauto. }
    { eapply Memory.closed_timemap_bot; eauto. apply CLOSED. }
    { eapply List.Forall_forall. i.
      eapply list_Forall2_in in H; eauto. des. rewrite <- SAT.
      eapply List.Forall_forall in NOTIN; eauto. ss. des.
      eapply write_not_in_mon; eauto. i. ss. des. split; auto.
      ii. eapply PROM. eapply memory_le_covered; eauto. eapply LOCAL0. }
  }
  { eapply no_sc_same_sc_traced in STEPS1; eauto.
    eapply List.Forall_impl; eauto. i. ss. des. auto. }
  { unguard. des.
    { left. esplits; eauto. eapply failure_step_map; eauto.
      { eapply ident_map_le. }
      { eapply ident_map_eq. }
    }
    { inv LOCAL1. right. esplits; eauto.
      { erewrite PROMISES in *.
        eapply bot_promises_map in PROMISES0; eauto. }
      { i. dup GET. eapply LOCAL in GET. des. dup GET.
        eapply LOCAL in GET; eauto. des.
        eapply IDENT in TO. eapply IDENT in TO0. eapply IDENT in FROM. subst. clarify.
        inv MSG. exploit WRITES; eauto. i. des.
        eapply list_Forall2_in2 in IN; eauto. des.
        eapply list_Forall2_in in IN0; eauto. des.
        destruct a, b. ss. subst. esplits; eauto.
        dup GET0. eapply LOCAL0 in GET0.
        eapply promise_writing_event_map; try apply GET0; try apply EVENT; eauto.
        { eapply ident_map_lt. }
        { ii. refl. }
        { eapply promise_writing_event_mon in WRITING; eauto.
          { refl. }
          { eapply opt_view_ident_map in MAP0; auto. subst. refl. }
        }
      }
    }
  }
Qed.
