Require Import Lia.
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
Require Import Cover.
Require Import PFConsistent.
Require Import ReorderCancel.
Require Import MemoryProps.
Require Import OrderedTimes.

Require Import Mapping.
Require Import CapFlex.
Require Import GoodFuture.
Require Import PreReserve.

Set Implicit Arguments.


Section CONCRETEMAX.

  Lemma map_ident_concrete_promises mem prom tm (f: Loc.t -> Time.t -> Time.t -> Prop)
        (MAX: concrete_promise_max_timemap mem prom tm)
        (IDENT: forall loc ts (TS: Time.le ts (tm loc)), f loc ts ts)
        (MAPLT: mapping_map_lt_iff f)
        (CLOSED: Memory.closed mem)
        (MLE: Memory.le prom mem)
    :
      promises_map f prom prom.
  Proof.
    assert (CONCRETE: map_ident_concrete f mem).
    { ii. inv CONCRETE. eapply MAX in GET; auto. }
    econs.
    { i. exists to, from, msg. splits; auto.
      { eapply mapping_map_lt_iff_non_collapsable; eauto. }
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
      eapply IDENT in TO. subst.
      inv MSG; inv MSGLE; ss;
        eapply MAXSRC in GET; auto; ss. }
    { eapply LOCAL in GET. des; ss.
      eapply IDENT in TO. subst.
      eapply MAXSRC in GET. auto. }
  Qed.

End CONCRETEMAX.




Definition pf_consistent_strong lang (e0:Thread.t lang): Prop :=
  forall mem1 sc1 (CAP: Memory.cap (Thread.memory e0) mem1),
  exists e1,
    (<<STEPS0: rtc (tau (@pred_step ThreadEvent.is_cancel lang))
                   (Thread.mk _ (Thread.state e0) (Thread.local e0) sc1 mem1) e1>>) /\
    (<<NORESERVE: no_reserves (Local.promises (Thread.local e1))>>) /\
    exists e2,
      (<<STEPS1: rtc (tau (@pred_step ((promise_free /1\ (fun e => ~ ThreadEvent.is_cancel e)) /1\ no_sc) lang)) e1 e2>>) /\
      (<<PROMISES: (Local.promises (Thread.local e2)) = Memory.bot>>).

Lemma pf_consistent_pf_consistent_strong lang (th: Thread.t lang)
      (WF: Local.wf (Thread.local th) (Thread.memory th))
      (SC: Memory.closed_timemap (Thread.sc th) (Thread.memory th))
      (MEM: Memory.closed (Thread.memory th))
      (CONSISTENT: pf_consistent th)
  :
    pf_consistent_strong th.
Proof.
  assert (INHABITED: Memory.inhabited (Thread.memory th)).
  { inv MEM. auto. }
  ii. exploit CONSISTENT; eauto. i.

  des.
  eapply pf_step_promise_free_step_rtc in STEPS.
  eapply steps_cancels_not_cancels in STEPS. des.

  exploit Thread.rtc_cancel_step_future.
  { eapply STEPS1. }
  { ss. eapply Local.cap_wf; eauto. }
  { ss. eapply Memory.cap_closed_timemap; eauto. }
  { ss. eapply Memory.cap_closed; eauto. }
  s. i. des.

  eapply rtc_implies with (R2 := tau (@pred_step ThreadEvent.is_cancel lang)) in STEPS1; cycle 1.
  { clear. i. inv H. econs.
    { econs; eauto.
      { econs; eauto. }
      { ss. }
    }
    { ss. }
  }
  destruct th1. exploit no_sc_any_sc_rtc; try apply STEPS1; ss.
  { i. unfold ThreadEvent.is_cancel in PR. des_ifs. }
  i. des. instantiate (1:=sc1) in STEP.
  clear STEPS1. rename STEP into STEPS1.

  eexists. splits.
  { eapply STEPS1. }
  { ss. ii. clarify.
    eapply steps_not_cancel_reserves_same in STEPS2; eauto.
    des. rewrite PROMISES in *. erewrite Memory.bot_get in STEPS2. clarify.
  }

  eapply hold_or_not with (Q := no_sc) in STEPS2. des.
  - destruct e2. ss.
    exploit no_sc_any_sc_rtc; try eapply HOLD; eauto.
    { ss. i. des. auto. } i. des.
    esplits.
    + eapply pred_step_rtc_mon; try eapply STEP. i. ss.
    + eauto.

  - exploit Thread.rtc_tau_step_future.
    { eapply thread_steps_pred_steps. eapply STEPS0. }
    { ss. }
    { ss. }
    { ss. } i. des.
    inv STEP.
    exploit Thread.step_future; eauto. i. des.

    assert (PROMS: Local.promise_consistent (Thread.local e3)).
    { eapply rtc_tau_step_promise_consistent.
      - eapply thread_steps_pred_steps. eapply STEPS2.
      - ii. rewrite PROMISES in PROMISE.
        rewrite Memory.bot_get in PROMISE. clarify.
      - eauto.
      - eauto.
      - eauto.
    }

    assert (NOPROMISE: (Local.promises (Thread.local e2')) = Memory.bot).
    { apply Memory.ext. i. rewrite Memory.bot_get.
      destruct (Memory.get loc ts (Local.promises (Thread.local e2'))) as [[from msg]|] eqn:GET; ss.
      exfalso.
      destruct (classic (msg = Message.reserve)).
      - subst.
        eapply step_not_cancel_reserves_same in GET; cycle 1.
        + econs.
          * econs; eauto.
          * instantiate (1:=promise_free /1\ (fun e => ~ ThreadEvent.is_cancel e)). ss.
        + ss.
        + des. eapply steps_not_cancel_reserves_same in GET; eauto.
          des. rewrite PROMISES in GET. rewrite Memory.bot_get in GET. ss.
      - exploit pf_step_rtc_promises_decrease.
        { eapply STEPS0. }
        { i. ss. des. auto. }
        { econs; eauto. } ss. i.
        exploit pf_step_rtc_promises_decrease.
        { eapply STEPS1. }
        { i. unfold ThreadEvent.is_cancel in *. des_ifs. }
        { ss. eauto. }
        ss. i. inv x1.
        ss. unfold no_sc in BREAKQ. des_ifs; try by (exfalso; eauto).
        + des; clarify. apply NNPP in BREAKQ.
          inv STEP0; inv STEP. ss. inv LOCAL. inv LOCAL0. ss.
          destruct ordw; ss. exploit PROMISES0; eauto. i.
          rewrite x, Memory.bot_get in *. ss.
        + inv STEP0; inv STEP. ss. inv LOCAL. inv LOCAL0. ss.
          exploit PROMISES0; eauto. i.
          rewrite x, Memory.bot_get in *. ss.
    }

    destruct e2'. destruct local. ss.
    eapply no_sc_any_sc_rtc in STEPS0; ss; cycle 1.
    { i. des; ss. } des.
    esplits.
    * eapply pred_step_rtc_mon; eauto. i. ss.
    * eauto.
Qed.

Definition cancel_normal_trace (tr: Trace.t): Prop :=
  exists tr_cancel tr_normal,
    (<<EQ: tr = tr_cancel ++ tr_normal>>) /\
    (<<CANCEL: List.Forall (fun em => <<SAT: ThreadEvent.is_cancel (snd em)>>) tr_cancel>>) /\
    (<<NORMAL: List.Forall (fun em => <<SAT: (fun e => ~ ThreadEvent.is_cancel e) (snd em)>>) tr_normal>>).

Definition pf_consistent_strong_aux lang (e0:Thread.t lang): Prop :=
  forall mem1 (CAP: Memory.cap (Thread.memory e0) mem1),
  exists tr e1 times,
    (<<STEPS: Trace.steps tr (Thread.mk _ (Thread.state e0) (Thread.local e0) TimeMap.bot mem1) e1>>) /\
    (<<EVENTS: List.Forall (fun em => <<SAT: (promise_free /1\ no_sc /1\ (wf_time_evt (fun loc to => List.In to (times loc)))) (snd em)>> /\ <<TAU: ThreadEvent.get_machine_event (snd em) = MachineEvent.silent>>) tr >>) /\
    (<<CANCEL: cancel_normal_trace tr>>) /\
    (<<PROMISES: (Local.promises (Thread.local e1)) = Memory.bot>>).

Lemma pf_consistent_strong_pf_consistent_strong_aux lang (th: Thread.t lang)
      (WF: Local.wf (Thread.local th) (Thread.memory th))
      (MEM: Memory.closed (Thread.memory th))
      (CONSISTENT: pf_consistent_strong th)
  :
    pf_consistent_strong_aux th.
Proof.
  ii. exploit CONSISTENT; eauto. i. des.
  eapply pred_steps_trace_steps in STEPS0. des.
  eapply pred_steps_trace_steps in STEPS1. des.
  hexploit (trace_times_list_exists (tr ++ tr0)); eauto. i. des.
  eexists (tr ++ tr0), e2, times. esplits; eauto.
  { eapply Trace.steps_trans; eauto. }
  { eapply list_Forall_sum.
    { eapply WFTIME. }
    { instantiate (1:=(fun em => <<SAT: (promise_free /1\ no_sc) (snd em)>> /\ <<TAU: ThreadEvent.get_machine_event (snd em) = MachineEvent.silent>>)).
      eapply Forall_app.
      { eapply List.Forall_impl; eauto. i. ss. destruct a. ss. des.
        destruct t0; ss. des_ifs. }
      { eapply List.Forall_impl; eauto. i. ss. des. splits; auto. }
    }
    { i. ss. des. splits; auto. }
  }
  { unfold cancel_normal_trace. esplits; eauto.
    { eapply List.Forall_impl; eauto. i. ss. des; auto. }
    { eapply List.Forall_impl; eauto. i. ss. des; auto. }
  }
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
    eapply ((cap_flex_map_loc_bound FLEXMAP)); try apply MAP0. auto. }
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
                 ((Thread.memory e0))
                 ((Local.promises (Thread.local e0)))
                 max),
    (<<MAP: forall loc n
                   (TS: Time.lt (Memory.max_ts loc (Thread.memory e0)) (incr_time_seq n)),
        cap_flex_map_loc
          (max loc)
          (Time.incr (Memory.max_ts loc (Thread.memory e0)))
          (incr_time_seq n) (times loc) (f loc n)>>) /\
    (<<CONSISTENT: forall mem1 (tm: Loc.t -> nat)
                          (TM: forall loc, Time.lt (Memory.max_ts loc (Thread.memory e0)) (incr_time_seq (tm loc)))
                          (CAP: cap_flex (Thread.memory e0) mem1 (fun loc => incr_time_seq (tm loc))),
        exists ftr e1,
          (<<STEPS: Trace.steps ftr (Thread.mk _ (Thread.state e0) (Thread.local e0) TimeMap.bot mem1) e1>>) /\
          (<<EVENTS: List.Forall (fun em => <<SAT: (promise_free
                                                      /1\ no_sc
                                                      /1\ wf_time_evt (fun loc => certification_times times f max (Memory.max_timemap (Thread.memory e0)) loc)) (snd em)>> /\ <<TAU: ThreadEvent.get_machine_event (snd em) = MachineEvent.silent>>) ftr >>) /\
          (<<TRACE: List.Forall2 (fun em fem => tevent_map (fun loc => f loc (tm loc)) (snd fem) (snd em)) tr ftr>>) /\
          (<<PROMISES: (Local.promises (Thread.local e1)) = Memory.bot>>)>>).


Lemma pf_consistent_strong_aux_pf_consistent_flex lang (th: Thread.t lang)
      (WF: Local.wf (Thread.local th) (Thread.memory th))
      (MEM: Memory.closed (Thread.memory th))
      (CONSISTENT: pf_consistent_strong_aux th)
  :
    exists tr times f, <<CONSISTENT: pf_consistent_flex th tr times f>> /\ <<CANCELNORMAL: cancel_normal_trace tr>>.
Proof.
  exploit Memory.cap_exists; eauto. i. des.
  exploit CONSISTENT; eauto. i. des. exists tr, times.
  hexploit (@concrete_promise_max_timemap_exists
              ((Thread.memory th))
              ((Local.promises (Thread.local th)))).
  { eapply MEM. } intros [max MAX]. des.
  hexploit (@choice
              (Loc.t * nat)
              (Time.t -> Time.t -> Prop)
              (fun locn f =>
                 let (loc, n) := locn in
                 forall
                   (TS: Time.lt (Memory.max_ts loc (Thread.memory th)) (incr_time_seq n)),
                   cap_flex_map_loc
                     (max loc)
                     (Time.incr (Memory.max_ts loc (Thread.memory th)))
                     (incr_time_seq n) (times loc) f)).
  { intros [loc n].
    destruct (classic (Time.lt (Memory.max_ts loc (Thread.memory th)) (incr_time_seq n))).
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
  intros [f SPEC]. des. exists (fun loc ts => f (loc, ts)). splits; auto. ii.
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

  assert (IDENT: map_ident_concrete (fun loc => f (loc, tm loc)) (Thread.memory th)).
  { ii. inv CONCRETE. eapply MAX in GET. eapply MAP; eauto. ss. }
  destruct e1. ss.
  hexploit trace_steps_map.
  { eapply mapping_map_lt_iff_map_le. eapply MAP. }
  { eapply MAP. }
  { eapply mapping_map_lt_iff_map_eq. eapply MAP. }
  { eapply mapping_map_lt_iff_map_lt. eapply MAP. }
  { eapply wf_time_mapped_mappable.
    { eapply List.Forall_impl; eauto. i. ss. des; eauto. }
    { eapply cap_flex_map_complete; eauto. }
  }
  { eapply STEPS. }
  { ss. }
  { ss. }
  { ss. }
  { eapply Local.cap_wf; eauto. }
  { instantiate (1:=mem1). instantiate (1:=(Thread.local th)).
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
  { exploit (@Memory.max_non_reserve_timemap_exists (Thread.memory th)).
    { eapply MEM. } i. des.
    eapply concrete_messages_le_cap_flex_memory_map.
    { refl. }
    { eauto. }
    { ii. eapply concrete_promise_max_ts_max_concrete_ts; eauto. }
    { instantiate (1:=(fun loc => Time.incr (Memory.max_ts loc (Thread.memory th)))).
      i. eapply Time.incr_spec. }
    { eapply TM. }
    { eapply cap_cap_flex; eauto. }
    { eauto. }
    { eauto. }
    { eauto. }
    { eauto. }
  }
  { eapply mapping_map_lt_iff_collapsable_unwritable. eapply MAP. }
  { eapply timemap_bot_map. eapply MAP. }
  { refl. } i. des.
  exists ftr, (Thread.mk _ state flc1 fsc1 fmem1). splits; auto.
  { eapply List.Forall_forall. i.
    cut ((promise_free /1\ no_sc) (snd x) /\ ThreadEvent.get_machine_event (snd x) = MachineEvent.silent).
    { i. des. splits; auto.
      { eapply list_Forall2_in in H; eauto. des.
        eapply List.Forall_forall in IN; eauto. ss. des.
        eapply wf_time_evt_map in EVENT; eauto. eapply wf_time_evt_mon; try apply EVENT.
        i. ss. des. destruct (Time.le_lt_dec ts (max x0)).
        { left. assert (ts = x1).
          { eapply mapping_map_lt_iff_map_eq.
            { eapply MAP. }
            { ss. eapply MAP. eauto. }
            { eauto. }
          }
          subst. splits; auto.
        }
        { right. esplits; eauto. }
      }
    }
    eapply list_Forall2_in in H; eauto. des.
    eapply List.Forall_forall in IN; eauto. ss. des.
    destruct x, a. ss. inv EVENT; ss. inv KIND; ss.
    splits; auto. inv MSG; ss. inv MAP0; ss.
  }
  { eapply list_Forall2_impl; eauto. i. ss. des. auto. }
  { inv LOCAL. erewrite PROMISES in *. eapply bot_promises_map; eauto. }
Qed.

Definition pf_consistent_super_strong_easy lang (e0:Thread.t lang)
           (tr : Trace.t)
           (times: Loc.t -> (Time.t -> Prop))
  : Prop :=
  forall cap (tm: Loc.t -> nat) max
         (CAPTM: forall loc, Time.lt (Memory.max_ts loc (Thread.memory e0)) (incr_time_seq (tm loc)))
         (CAP: cap_flex (Thread.memory e0) cap (fun loc => incr_time_seq (tm loc)))
         (MAX: concrete_promise_max_timemap
                 ((Thread.memory e0))
                 ((Local.promises (Thread.local e0)))
                 max),
  exists ftr e1 f,
    (<<STEPS: Trace.steps ftr (Thread.mk _ (Thread.state e0) (Thread.local e0) TimeMap.bot cap) e1>>) /\
    (<<EVENTS: List.Forall (fun em => <<SAT: (promise_free
                                                /1\ no_sc
                                                /1\ wf_time_evt times) (snd em)>> /\ <<TAU: ThreadEvent.get_machine_event (snd em) = MachineEvent.silent>>) ftr >>) /\
    (<<CANCELNORMAL: cancel_normal_trace ftr>>) /\
    (<<MAPLT: mapping_map_lt_iff f>>) /\
    (<<MAPIDENT: forall loc ts fts
                        (TS: Time.le fts (max loc))
                        (MAP: f loc ts fts),
        ts = fts>>) /\
    (<<BOUND: forall loc ts fts (TS: Time.lt (max loc) fts) (MAP: f loc ts fts),
        Time.lt (max loc) ts /\ Time.le (incr_time_seq (tm loc)) fts>>) /\
    (<<TRACE: List.Forall2 (fun em fem => tevent_map_weak f (snd fem) (snd em)) tr ftr>>) /\
    (<<PROMISES: (Local.promises (Thread.local e1)) = Memory.bot>>).

Lemma pf_consistent_super_strong_easy_same_sc lang (e0: Thread.t lang) tr times sc
      (CONSISTENT: pf_consistent_super_strong_easy e0 tr times)
  :
    pf_consistent_super_strong_easy (Thread.mk _ (Thread.state e0) (Thread.local e0) sc (Thread.memory e0)) tr times.
Proof.
  ii. exploit CONSISTENT; eauto.
Qed.

Definition pf_consistent_super_strong_easy_mon lang e0 tr certimes0 certimes1
           (CONSISTENT: @pf_consistent_super_strong_easy
                          lang e0 tr certimes0)
           (LE: certimes0 <2= certimes1)
  :
    pf_consistent_super_strong_easy e0 tr certimes1.
Proof.
  ii. exploit CONSISTENT; eauto. i. des. esplits; eauto.
  eapply List.Forall_impl; eauto. i. ss. des. splits; eauto.
  eapply wf_time_evt_mon; eauto.
Qed.

Lemma memory_times_wf_exists (mem: Memory.t)
  :
    exists times_mem,
      (<<MWF: memory_times_wf times_mem mem>>) /\
      (<<MEMWO: forall loc, well_ordered (times_mem loc)>>).
Proof.
  hexploit (choice
              (fun loc times =>
                 (<<WF: forall to from msg
                               (GET: Memory.get loc to mem = Some (from, msg)),
                     times from /\ times to>>) /\ (<<WO: well_ordered times>>))).
  { intros loc. hexploit (Cell.finite (mem loc)). i. des.
    set (f := (fun to => match (Memory.get loc to mem) with
                         | Some (from, _) => from
                         | _ => Time.bot
                         end)).
    set (froms:=List.map f dom).
    hexploit (finite_well_ordered (dom++froms)). intros WO. esplits; try apply WO.
    i. ss. dup GET. eapply H in GET. split.
    { eapply List.in_map with (f:=f) in GET. unfold f in GET. erewrite GET0 in *.
      eapply List.in_or_app; eauto. }
    { eapply List.in_or_app; eauto. }
  }
  i. des. exists f. splits.
  { ii. specialize (H loc). des. apply WF in GET. auto. }
  { apply H; eauto. }
Qed.

Lemma pf_consistent_flex_super_strong_easy
      lang (th: Thread.t lang) tr times f
      (WF: Local.wf (Thread.local th) (Thread.memory th))
      (MEM: Memory.closed (Thread.memory th))
      (CONSISTENT: pf_consistent_flex th tr times f)
      (CANCELNORMAL: cancel_normal_trace tr)
  :
    exists certimes,
      (<<WO: forall loc, well_ordered (certimes loc)>>) /\
      (<<MWF: memory_times_wf certimes (Thread.memory th)>>) /\
      (<<DIVERGE: forall loc n, certimes loc (incr_time_seq n)>>) /\
      (<<CONSISTENT: pf_consistent_super_strong_easy th tr certimes>>).
Proof.
  hexploit (@concrete_promise_max_timemap_exists
              ((Thread.memory th))
              ((Local.promises (Thread.local th)))).
  { eapply MEM. } intros [max MAX]. specialize (CONSISTENT _ MAX). des.
  hexploit (memory_times_wf_exists (Thread.memory th)). i. des.
  exists ((certification_times times f max (Memory.max_timemap (Thread.memory th))) \2/ times_mem \2/ (fun loc => incr_times)). splits.
  { i. eapply join_well_ordered.
    { eapply join_well_ordered; eauto.
      eapply certification_times_well_ordered; eauto.
      { i. eapply MAP. auto. }
      { i. ss. eapply Time.incr_spec. }
      { ii. eapply concrete_promise_max_ts_max_ts; eauto. eapply WF. }
    }
    eapply incr_times_well_ordered.
  }
  { ii. eapply MWF in GET. des; auto. }
  { i. right. unfold incr_times. eauto. }
  ii. assert (max0 = max).
  { eapply concrete_promise_max_timemap_inj; eauto. } subst.
  hexploit CONSISTENT0; eauto. i. des.
  assert (MAPALL: cap_flex_map
                    max
                    (fun loc => Time.incr (Memory.max_ts loc (Thread.memory th)))
                    (fun loc => incr_time_seq (tm loc))
                    times (fun loc => f loc (tm loc))).
  { eapply cap_flex_map_locwise; eauto. }
  eexists _, _, (fun loc => f loc (tm loc)). splits; eauto.
  { eapply List.Forall_impl; eauto. i. ss. des. splits; auto.
    eapply wf_time_evt_mon; try apply SAT0; eauto. }
  { unfold cancel_normal_trace in *. des. subst.
    eapply List.Forall2_app_inv_l in TRACE. des. esplits; eauto.
    { eapply List.Forall_forall. i. eapply list_Forall2_in in H; eauto. des.
      destruct a, x. ss. eapply List.Forall_forall in IN; eauto. ss. inv SAT; ss.
      inv KIND; ss; des_ifs; inv MSG. }
    { eapply List.Forall_forall. i. eapply list_Forall2_in in H; eauto. des.
      destruct a, x. ss. eapply List.Forall_forall in IN; eauto. ss. inv SAT; ss.
      inv KIND; ss; des_ifs; inv MSG. }
  }
  { eapply MAPALL. }
  { i. eapply MAPALL in TS; eauto.
    eapply mapping_map_lt_iff_inj.
    { eapply MAPALL; eauto. }
    { ss. eauto. }
    { eauto. }
  }
  { i. destruct (Time.le_lt_dec ts (max loc)).
    { dup l. eapply MAPALL in l; eauto.
      exploit mapping_map_lt_iff_map_eq.
      { eapply MAPALL. }
      { eapply MAP0. }
      { eapply l. }
      i. subst. timetac.
    }
    { split; auto. eapply (cap_flex_map_bound MAPALL) in l; eauto. }
  }
  { eapply list_Forall2_impl; eauto. i. eapply tevent_map_tevent_map_weak; eauto. }
Qed.


Definition pf_consistent_special lang (e0:Thread.t lang)
           (tr : Trace.t)
           (times: Loc.t -> (Time.t -> Prop))
  : Prop :=
  forall cap (tm: Loc.t -> nat) max
         (CAPTM: forall loc, Time.lt (Memory.max_ts loc (Thread.memory e0)) (incr_time_seq (tm loc)))
         (CAP: cap_flex (Thread.memory e0) cap (fun loc => incr_time_seq (tm loc)))
         (MAX: concrete_promise_max_timemap
                 ((Thread.memory e0))
                 ((Local.promises (Thread.local e0)))
                 max),
  exists ftr e1,
    (<<STEPS: Trace.steps ftr (Thread.mk _ (Thread.state e0) (Thread.local e0) TimeMap.bot cap) e1>>) /\
    (<<EVENTS: List.Forall (fun em => <<SAT: (promise_free
                                                /1\ no_sc
                                                /1\ wf_time_evt times) (snd em)>> /\ <<TAU: ThreadEvent.get_machine_event (snd em) = MachineEvent.silent>>) ftr >>) /\
    (<<CANCELNORMAL: cancel_normal_trace ftr>>) /\
    (<<TRACE: List.Forall2 (fun em fem => tevent_map_weak (fun loc ts fts => ts = fts /\ Time.le ts (max loc)) (snd fem) (snd em)) tr ftr>>) /\
    (<<PROMISES: (Local.promises (Thread.local e1)) = Memory.bot>>).

Lemma pf_consistent_speciali_strong_easy
      lang (th: Thread.t lang) tr times
      (CONSISTENT: pf_consistent_special th tr times)
  :
    pf_consistent_super_strong_easy th tr times.
Proof.
  ii. exploit CONSISTENT; eauto. i. des. esplits; eauto.
  { ii. des. subst. auto. }
  { ii. ss. des. auto. }
  { ii. ss. des. subst. exfalso. timetac. }
Qed.

Lemma pf_consistent_speciali_events_map
      lang (th: Thread.t lang) tr0 tr1 times
      (CONSISTENT: pf_consistent_special th tr0 times)
      (EVENTS: List.Forall2 (fun em fem => tevent_map_weak ident_map (snd fem) (snd em)) tr0 tr1)
  :
    pf_consistent_special th tr1 times.
Proof.
  ii. exploit CONSISTENT; eauto. i. des. esplits; eauto.
  eapply list_Forall2_compose.
  { eapply list_Forall2_rev; eauto. }
  { eauto. }
  { i. ss. eapply tevent_map_weak_rev with (f1:=ident_map) in SAT0; ss.
    eapply tevent_map_weak_compose; eauto. i. ss. inv MAP0. des; auto. }
Qed.


Definition pf_consistent_super_strong_split lang (e0:Thread.t lang)
           (tr : Trace.t)
           (times: Loc.t -> (Time.t -> Prop))
  : Prop :=
  forall cap (tm: Loc.t -> nat) max
         (CAPTM: forall loc, Time.lt (Memory.max_ts loc (Thread.memory e0)) (incr_time_seq (tm loc)))
         (CAP: cap_flex (Thread.memory e0) cap (fun loc => incr_time_seq (tm loc)))
         (MAX: concrete_promise_max_timemap
                 ((Thread.memory e0))
                 ((Local.promises (Thread.local e0)))
                 max),
  exists ftr e1 f,
    (<<STEPS: Trace.steps ftr (Thread.mk _ (Thread.state e0) (Thread.local e0) TimeMap.bot cap) e1>>) /\
    (<<EVENTS: List.Forall (fun em => <<SAT: (promise_free
                                                /1\ no_sc
                                                /1\ wf_time_evt times) (snd em)>> /\ <<TAU: ThreadEvent.get_machine_event (snd em) = MachineEvent.silent>>) ftr >>) /\
    (<<CANCELNORMAL: cancel_normal_trace ftr>>) /\

    (<<SPLIT:
       forall ftr0 ftr1 e_mid
              (FTRACE: ftr = ftr0 ++ ftr1)
              (NORMAL: List.Forall (fun em => ~ ThreadEvent.is_cancel (snd em)) ftr1)
              (STEPS0: Trace.steps ftr0 (Thread.mk _ (Thread.state e0) (Thread.local e0) TimeMap.bot cap) e_mid)
              (STEPS1: Trace.steps ftr1 e_mid e1)
       ,
       exists ftr_reserve ftr_cancel e2,
         (<<STEPS: Trace.steps ftr_reserve e_mid e2>>) /\
         (<<RESERVE: List.Forall (fun em => <<SAT: (ThreadEvent.is_reserve /1\ wf_time_evt times) (snd em)>>) ftr_reserve>>) /\
         (<<CANCEL: List.Forall (fun em => <<SAT: (ThreadEvent.is_cancel /1\ wf_time_evt times) (snd em)>>) ftr_cancel>>) /\
         (<<CONSISTENT: pf_consistent_special e2 (ftr_cancel ++ ftr1) times>>) /\
         (<<CANCELNORMAL: cancel_normal_trace (ftr_cancel ++ ftr1)>>)>>) /\

    (<<MAPLT: mapping_map_lt_iff f>>) /\
    (<<MAPIDENT: forall loc ts fts
                        (TS: Time.le fts (max loc))
                        (MAP: f loc ts fts),
        ts = fts>>) /\
    (<<BOUND: forall loc ts fts (TS: Time.lt (max loc) fts) (MAP: f loc ts fts),
        Time.lt (max loc) ts /\ Time.le (incr_time_seq (tm loc)) fts>>) /\
    (<<TRACE: List.Forall2 (fun em fem => tevent_map_weak f (snd fem) (snd em)) tr ftr>>) /\
    (<<PROMISES: (Local.promises (Thread.local e1)) = Memory.bot>>).

Lemma cap_flex_memory_times_wf times mem cap tm
      (MEMWF: memory_times_wf times mem)
      (CAP: cap_flex mem cap tm)
      (TM: forall loc, Time.lt (Memory.max_ts loc mem) (tm loc))
      (IN: forall loc, times loc (tm loc))
      (CLOSED: Memory.closed mem)
  :
    memory_times_wf times cap.
Proof.
  ii. eapply cap_flex_inv in GET; eauto. des.
  { eapply MEMWF; eauto. }
  { inv GET0. eapply MEMWF in GET3. eapply MEMWF in GET4. des. auto. }
  { subst. split; auto. exploit Memory.max_ts_spec.
    { eapply CLOSED. }
    i. des. eapply MEMWF in GET0. des. eauto.
  }
Qed.

Lemma list_Forall_refl_Forall2 A (P: A -> A -> Prop) (l: list A)
      (FORALL: List.Forall (fun a => P a a) l)
  :
    List.Forall2 P l l.
Proof.
  ginduction l; eauto. i. inv FORALL. econs; eauto.
Qed.


Lemma ident_map_compose_tevent_weak f te0 te1 te2
      (MAP0: tevent_map_weak f te1 te0)
      (MAP1: tevent_map_weak ident_map te2 te1)
  :
    tevent_map_weak f te2 te0.
Proof.
  inv MAP0; inv MAP1; econs;
    (try by inv FROM0; auto);
    (try by inv TO0; auto).
  { inv TO0. etrans; eauto. }
  { revert_until MSGS.
    induction MSGS; i; inv MSGS0; ss. des.
    econs; eauto.
    inv H2. inv H0. splits; auto.
    destruct x, y, y0. ss.
    inv H5; inv H1; econs.
  }
Qed.

Lemma ident_map_compose_tevent_weak2 f te0 te1 te2
      (MAP0: tevent_map_weak ident_map te1 te0)
      (MAP1: tevent_map_weak f te2 te1)
  :
    tevent_map_weak f te2 te0.
Proof.
  inv MAP0; inv MAP1; econs;
    (try by inv FROM; auto);
    (try by inv TO; auto).
  { inv TO. eauto. etrans; eauto. }
  { revert_until MSGS.
    induction MSGS; i; inv MSGS0; ss. des.
    econs; eauto.
    inv H. inv H3. splits; try congr.
    destruct x, y, y0. ss.
    inv H5; inv H1; econs.
  }
Qed.

Lemma ident_map_pf_consistent_super_strong_easy
      lang (th0 th1: Thread.t lang) tr times
      (CONSISTENT: pf_consistent_special th0 tr times)
      (WF0: Local.wf (Thread.local th0) (Thread.memory th0))
      (MEM0: Memory.closed (Thread.memory th0))
      (WF1: Local.wf (Thread.local th1) (Thread.memory th1))
      (MEM1: Memory.closed (Thread.memory th1))
      (MAP: thread_map ident_map th0 th1)
  :
    pf_consistent_special th1 tr times.
Proof.
  ii.
  assert (exists (tm_src: Loc.t -> nat),
             (<<CAPTMSRC: forall loc,
                 Time.lt (Memory.max_ts loc (Thread.memory th0)) (incr_time_seq (tm_src loc))>>)  /\
             (<<TMLE: forall loc, Time.le (incr_time_seq (tm loc)) (incr_time_seq (tm_src loc))>>)).
  { exploit (choice (fun loc n =>
                       (<<CAPTMSRC:
                          Time.lt (Memory.max_ts loc (Thread.memory th0)) (incr_time_seq n)>>)  /\
                       (<<TMLE: Time.le (incr_time_seq (tm loc)) (incr_time_seq n)>>))).
    { i. hexploit (@incr_time_seq_diverge
                     (Time.join
                        (Memory.max_ts x (Thread.memory th0))
                        (incr_time_seq (tm x)))). i. des.
      exists n. splits; auto.
      { eapply TimeFacts.le_lt_lt; eauto. eapply Time.join_l. }
      { left. eapply TimeFacts.le_lt_lt; eauto. eapply Time.join_r. }
    }
    i. des. exists f. splits.
    { i. specialize (x0 loc). des; auto. }
    { i. specialize (x0 loc). des; auto. }
  }
  des.
  exploit (@concrete_promise_max_timemap_exists (Thread.memory th0) (Local.promises (Thread.local th0))).
  { eapply MEM0. }
  i. des.
  assert (MAXLE: TimeMap.le tm0 max).
  { inv MAP. ss. inv LOCAL. eapply memory_ident_map_concrete_promise_max_timemap; eauto. }
  exploit (@cap_flex_exists (Thread.memory th0) (fun loc => incr_time_seq (tm_src loc))); eauto.
  i. des.
  exploit CONSISTENT; eauto. i. des. inv MAP. ss.
  destruct e1. ss. hexploit trace_steps_map.
  { eapply ident_map_le; eauto. }
  { eapply ident_map_bot; eauto. }
  { eapply ident_map_eq; eauto. }
  { eapply ident_map_lt; eauto. }
  { eapply List.Forall_forall. i. eapply ident_map_mappable_evt. }
  { eapply STEPS. }
  { ss. }
  { ss. }
  { ss. }
  { eapply cap_flex_wf; eauto. }
  { eapply cap_flex_wf; try apply CAP; eauto. }
  { eapply cap_flex_closed; eauto. }
  { eapply cap_flex_closed; eauto. }
  { eapply Memory.closed_timemap_bot; eauto.
    eapply cap_flex_closed; eauto. }
  { eapply Memory.closed_timemap_bot; eauto.
    eapply cap_flex_closed; eauto. }
  all: eauto.
  { econs.
    { i. eapply cap_flex_inv in GET; try apply CAP0; eauto. des; auto.
      eapply MEM in GET. des; auto. right. esplits; eauto.
      eapply CAP in GET; eauto. }
    { i. left.
      exists (incr_time_seq (tm_src loc)), Time.bot, (incr_time_seq (tm_src loc)), Time.bot.
      splits; auto; ss.
      { eapply Time.bot_spec. }
      { eapply Memory.max_ts_spec in GET. des.
        erewrite (@cap_flex_max_ts fmem cap) in MAX1; eauto. ss.
        etrans; eauto. }
      i. eapply cap_flex_covered; eauto.
    }
  }
  { eapply mapping_map_lt_iff_collapsable_unwritable. eapply ident_map_lt_iff. }
  { eapply ident_map_timemap. }
  { refl. }
  i. des. esplits.
  { eauto. }
  { eapply List.Forall_forall. i. eapply list_Forall2_in in H; eauto. des.
    eapply List.Forall_forall in IN; eauto. ss. des.
    destruct a, x. ss. unfold ident_map in *.
    inv EVENT; ss; des; subst; auto.
    - splits; auto.
      inv KIND; ss. inv MSG; ss. inv MAP; ss.
    - splits; auto.
      clear - MSGS0 MSGS. revert_until MSGS0.
      induction MSGS0; i; inv MSGS; ss. des.
      econs; eauto. split; congr.
  }
  { clear - CANCELNORMAL TRACE0. unfold cancel_normal_trace in *. des.
    subst. eapply List.Forall2_app_inv_l in TRACE0. des. subst. esplits; eauto.
    { eapply List.Forall_forall. i. eapply list_Forall2_in in H; eauto. des.
      eapply List.Forall_forall in IN; eauto. ss.
      destruct a, x. ss. inv EVENT; ss. inv KIND; ss; des_ifs; inv MSG. }
    { eapply List.Forall_forall. i. eapply list_Forall2_in in H; eauto. des.
      eapply List.Forall_forall in IN; eauto. ss.
      destruct a, x. ss. inv EVENT; ss. inv KIND; ss; des_ifs; inv MSG. }
  }
  { eapply list_Forall2_compose.
    { eapply TRACE. }
    { eapply TRACE0. }
    i. ss. des. eapply tevent_map_tevent_map_weak in EVENT.
    eapply tevent_map_weak_compose; eauto.
    i. ss. des; subst. inv MAP1. split; auto. etrans; eauto.
  }
  { i. ss. inv LOCAL0.
    rewrite PROMISES in *. eapply bot_promises_map in PROMISES0; auto.
  }
Qed.


Lemma pf_consistent_flex_super_strong_easy_split
      lang (th: Thread.t lang) tr times
      (WF: Local.wf (Thread.local th) (Thread.memory th))
      (MEM: Memory.closed (Thread.memory th))
      (CONSISTENT: pf_consistent_super_strong_easy th tr times)
      (CANCELNORMAL: cancel_normal_trace tr)
      (MWF: memory_times_wf times (Thread.memory th))
      (DIVERGE: forall loc n, times loc (incr_time_seq n))
  :
    pf_consistent_super_strong_split th tr times.
Proof.
  ii. exploit CONSISTENT; eauto. i. des. esplits; eauto.
  i. subst. exploit Trace.steps_future; try apply STEPS0; eauto; ss.
  { eapply cap_flex_wf; eauto. }
  { eapply Memory.closed_timemap_bot; eauto.
    eapply cap_flex_closed; eauto. }
  { eapply cap_flex_closed; eauto. } i. des.
  eapply Forall_app_inv in EVENTS. des.
  destruct e_mid, e1. ss.
  assert (sc = TimeMap.bot).
  { eapply no_sc_same_sc_traced in STEPS0; eauto.
    eapply List.Forall_impl; eauto. i. ss. des; auto. } subst.
  hexploit can_reserve_all_needed.
  { instantiate (1:=times). i. hexploit (incr_time_seq_diverge ts).
    i. des. esplits; eauto. }
  { instantiate (1:=memory).
    eapply memory_times_wf_traced in STEPS0; eauto.
    { ss. eapply cap_flex_memory_times_wf; eauto. ss. }
    { eapply List.Forall_impl; eauto. i. ss. des; auto. }
  }
  { eapply STEPS1. }
  { eapply list_Forall_sum.
    { eapply FORALL2. }
    { eapply NORMAL. }
    i. ss. des; auto.
  }
  { eauto. }
  { eauto. }
  { eauto. }
  i. des. exists tr_reserve, tr_cancel. esplits; eauto.
  { ii. exploit (CAP0 cap0).
    { eapply CAP1. } i. des.
    eexists (tr_cancel ++ ftr1), _. esplits.
    { eapply Trace.steps_trans.
      { eapply CANCELSTEPS. }
      { eapply STEPS2. }
    }
    { eapply Forall_app; eauto.
      eapply List.Forall_impl; eauto. i. ss. des.
      destruct a. ss. destruct t0; ss. des_ifs.
    }
    { unfold cancel_normal_trace. esplits; eauto.
      eapply List.Forall_impl; eauto. i. ss. des; auto.
    }
    { eauto. }
    { ss. }
  }
  { unfold cancel_normal_trace. esplits; eauto.
    eapply List.Forall_impl; eauto. i. ss. des; auto. }
Qed.


Definition pf_consistent_super_strong_aux lang (e0:Thread.t lang)
           (tr : Trace.t)
           (times: Loc.t -> (Time.t -> Prop))
  : Prop :=
  forall cap (tm: Loc.t -> nat) max
         (CAPTM: forall loc, Time.lt (Memory.max_ts loc (Thread.memory e0)) (incr_time_seq (tm loc)))
         (CAP: cap_flex (Thread.memory e0) cap (fun loc => incr_time_seq (tm loc)))
         (MAX: concrete_promise_max_timemap
                 ((Thread.memory e0))
                 ((Local.promises (Thread.local e0)))
                 max),
  exists ftr e1 f,
    (<<STEPS: Trace.steps ftr (Thread.mk _ (Thread.state e0) (Thread.local e0) TimeMap.bot cap) e1>>) /\
    (<<EVENTS: List.Forall (fun em => <<SAT: (promise_free
                                                /1\ no_sc
                                                /1\ no_read_msgs (fun loc ts => ~ (covered loc ts (Local.promises (Thread.local e0)) \/ concrete_promised (Thread.memory e0) loc ts \/ Time.lt (incr_time_seq (tm loc)) ts))
                                                /1\ write_not_in (fun loc ts => (<<TS: Time.le ts (incr_time_seq (tm loc))>>) /\ (<<PROM: ~ covered loc ts (Local.promises (Thread.local e0))>>))
                                                /1\ wf_time_evt times) (snd em)>> /\ <<TAU: ThreadEvent.get_machine_event (snd em) = MachineEvent.silent>>) ftr >>) /\

    (<<CANCELNORMAL: cancel_normal_trace ftr>>) /\
    (<<SPLIT:
       forall ftr0 ftr1 e_mid
              (FTRACE: ftr = ftr0 ++ ftr1)
              (STEPS0: Trace.steps ftr0 (Thread.mk _ (Thread.state e0) (Thread.local e0) TimeMap.bot cap) e_mid)
              (STEPS1: Trace.steps ftr1 e_mid e1)
              (NORMAL: List.Forall (fun em => ~ ThreadEvent.is_cancel (snd em)) ftr1),
       exists ftr_reserve ftr_cancel e2,
         (<<STEPS: Trace.steps ftr_reserve e_mid e2>>) /\
         (<<RESERVE: List.Forall (fun em => <<SAT: (ThreadEvent.is_reserve
                                                     /1\ wf_time_evt times
                                                     /1\ write_not_in (fun loc ts => (<<TS: Time.le ts (incr_time_seq (tm loc))>>) /\ (<<PROM: ~ covered loc ts (Local.promises (Thread.local e0))>>))) (snd em)>>) ftr_reserve>>) /\
         (<<CANCEL: List.Forall (fun em => <<SAT: (ThreadEvent.is_cancel /1\ wf_time_evt times) (snd em)>>) ftr_cancel>>) /\
         (<<CONSISTENT: pf_consistent_special e2 (ftr_cancel ++ ftr1) times>>) /\
         (<<CANCELNORMAL: cancel_normal_trace (ftr_cancel ++ ftr1)>>)>>) /\

    (<<MAPLT: mapping_map_lt_iff f>>) /\
    (<<MAPIDENT: forall loc ts fts
                        (TS: Time.le fts (max loc))
                        (MAP: f loc ts fts),
        ts = fts>>) /\
    (<<BOUND: forall loc ts fts (TS: Time.lt (max loc) fts) (MAP: f loc ts fts),
        Time.lt (max loc) ts /\ Time.le (incr_time_seq (tm loc)) fts>>) /\
    (<<TRACE: List.Forall2 (fun em fem => tevent_map_weak f (snd fem) (snd em)) tr ftr>>) /\
    (<<PROMISES: (Local.promises (Thread.local e1)) = Memory.bot>>).

Lemma pf_consistent_super_strong_easy_aux
      lang (th: Thread.t lang) tr times
      (WF: Local.wf (Thread.local th) (Thread.memory th))
      (MEM: Memory.closed (Thread.memory th))
      (CONSISTENT: pf_consistent_super_strong_split th tr times)
  :
    pf_consistent_super_strong_aux th tr times.
Proof.
  ii. exploit CONSISTENT; eauto. i. des.
  assert (MLE: Memory.le (Local.promises (Thread.local th)) cap).
  { etrans.
    { eapply WF. }
    { eapply CAP. }
  }
  esplits; eauto.
  { exploit write_not_in_traced; eauto.
    intros WRITENOTIN.
    exploit no_read_unreadable_traced; eauto.
    intros NOREAD. ss.
    esplits; eauto.
    eapply list_Forall_sum.
    { eapply list_Forall_sum.
      { eapply WRITENOTIN. }
      { eapply NOREAD. }
      instantiate (1:=fun lce => (no_read_msgs (fun loc ts => ~ (covered loc ts (Local.promises (Thread.local th)) \/ concrete_promised (Thread.memory th) loc ts \/ Time.lt (incr_time_seq (tm loc)) ts))
                                               /1\ write_not_in (fun loc ts => (<<TS: Time.le ts (incr_time_seq (tm loc))>>) /\ (<<PROM: ~ covered loc ts (Local.promises (Thread.local th))>>))) (snd lce)).
      i. ss. splits.
      { eapply no_read_msgs_mon; eauto. i.
        eapply not_or_and in PR. des.
        eapply not_or_and in PR0. des. econs.
        { eapply unwritable_eq; eauto. econs; eauto.
          eapply cap_flex_covered; eauto. ss. econs; eauto.
          { ss. destruct (Time.bot_spec x1); auto. inv H.
            exfalso. eapply PR0. econs; [eapply MEM|ss]. }
          { ss. destruct (Time.le_lt_dec x1 (incr_time_seq (tm x0))); ss. }
        }
        { i. eapply PR0.
          eapply cap_flex_inv in GET; eauto. des; ss. econs; eauto. }
      }
      { eapply write_not_in_mon_bot; eauto. i. des.
        eapply unwritable_eq; eauto. econs; eauto.
        eapply cap_flex_covered; eauto. ss. }
    }
    { eapply EVENTS. }
    { i. ss. des. splits; auto. }
  }
  { i. exploit SPLIT; eauto. i. des. esplits; eauto.
    exploit write_not_in_traced.
    { eapply Trace.steps_trans.
      { eapply STEPS0. }
      { eapply STEPS2. }
    }
    { eauto. }
    i. ss.
    eapply list_Forall_sum.
    { eapply RESERVE. }
    { eapply Forall_app_inv in x0. des. eapply FORALL2. }
    i. ss. des. splits; auto.
    { eapply write_not_in_mon_bot; eauto. i. des.
      eapply unwritable_eq; eauto. econs; eauto.
      eapply cap_flex_covered; eauto. ss. }
  }
Qed.


Definition pf_consistent_super_strong_aux2 lang (e0:Thread.t lang)
           (tr : Trace.t)
           (times: Loc.t -> (Time.t -> Prop))
  : Prop :=
  forall mem1 tm max
         (FUTURE: Memory.future_weak (Thread.memory e0) mem1)
         (CLOSED: Memory.closed mem1)
         (LOCAL: Local.wf (Thread.local e0) mem1)
         (MAX: concrete_promise_max_timemap
                 ((Thread.memory e0))
                 ((Local.promises (Thread.local e0)))
                 max),
  exists ftr e1 f,
    (<<STEPS: Trace.steps ftr (Thread.mk _ (Thread.state e0) (Thread.local e0) TimeMap.bot mem1) e1>>) /\
    (<<EVENTS: List.Forall (fun em => <<SAT: (promise_free
                                                /1\ no_sc
                                                /1\ no_read_msgs (fun loc ts => ~ (covered loc ts (Local.promises (Thread.local e0)) \/ concrete_promised (Thread.memory e0) loc ts \/ Time.lt (tm loc) ts))
                                                /1\ write_not_in (fun loc ts => (<<TS: Time.le ts (tm loc)>>) /\ (<<PROM: ~ covered loc ts (Local.promises (Thread.local e0))>>))
                                                /1\ wf_time_evt times) (snd em)>> /\ <<TAU: ThreadEvent.get_machine_event (snd em) = MachineEvent.silent>>) ftr >>) /\

    (<<CANCELNORMAL: cancel_normal_trace ftr>>) /\
    (<<SPLIT:
       forall ftr0 ftr1
              (FTRACE: ftr = ftr0 ++ ftr1)
              (NORMAL: List.Forall (fun em => ~ ThreadEvent.is_cancel (snd em)) ftr1),
       exists ftr_reserve ftr_cancel e2,
         (<<STEPS: Trace.steps (ftr0 ++ ftr_reserve) (Thread.mk _ (Thread.state e0) (Thread.local e0) TimeMap.bot mem1) e2>>) /\
         (<<RESERVE: List.Forall (fun em => <<SAT: (ThreadEvent.is_reserve
                                                      /1\ wf_time_evt times
                                                      /1\ write_not_in (fun loc ts => (<<TS: Time.le ts (tm loc)>>) /\ (<<PROM: ~ covered loc ts (Local.promises (Thread.local e0))>>))) (snd em)>>) ftr_reserve>>) /\
         (<<CANCEL: List.Forall (fun em => <<SAT: (ThreadEvent.is_cancel /1\ wf_time_evt times) (snd em)>>) ftr_cancel>>) /\
         (<<CONSISTENT: pf_consistent_special e2 (ftr_cancel ++ ftr1) times>>) /\
         (<<CANCELNORMAL: cancel_normal_trace (ftr_cancel ++ ftr1)>>)>>) /\

    (<<MAPLT: mapping_map_lt_iff f>>) /\
    (<<MAPIDENT: forall loc ts fts
                     (TS: Time.le fts (max loc))
                     (MAP: f loc ts fts),
        ts = fts>>) /\
    (<<BOUND: forall loc ts fts (TS: Time.lt (max loc) fts) (MAP: f loc ts fts),
        Time.lt (max loc) ts /\ Time.le (tm loc) fts>>) /\
    (<<TRACE: List.Forall2 (fun em fem => tevent_map_weak f (snd fem) (snd em)) tr ftr>>) /\
    (<<PROMISES: (Local.promises (Thread.local e1)) = Memory.bot>>).

Lemma thread_trace_trace_match_map lang (ttr: ThreadTrace.t lang) (tr: Trace.t)
      (MATCH: List.Forall2
                (fun the lce =>
                   (Thread.local (fst the)) = (fst lce) /\
                   (snd the) = (snd lce)) ttr tr)
  :
    tr = List.map (fun the => ((Thread.local (fst the)), snd the)) ttr.
Proof.
  ginduction ttr; eauto; i; ss.
  { inv MATCH. ss. }
  { inv MATCH. f_equal; eauto. destruct a, y. ss. des. clarify. }
Qed.

Lemma pf_consistent_super_strong_aux_aux2
      lang (th: Thread.t lang) tr times
      (WF: Local.wf (Thread.local th) (Thread.memory th))
      (MEM: Memory.closed (Thread.memory th))
      (CONSISTENT: pf_consistent_super_strong_aux th tr times)
  :
    pf_consistent_super_strong_aux2 th tr times.
Proof.
  ii.
  assert (TM: exists (ftm: Loc.t -> nat),
             forall loc,
               (<<TM0: Time.lt (Memory.max_ts loc (Thread.memory th)) (incr_time_seq (ftm loc))>>) /\
               (<<TM1: Time.lt (Memory.max_ts loc mem1) (incr_time_seq (ftm loc))>>) /\
               (<<TM2: Time.le (tm loc) (incr_time_seq (ftm loc))>>)).
  { eapply (choice
              (fun loc n =>
                 (<<TM0: Time.lt (Memory.max_ts loc (Thread.memory th)) (incr_time_seq n)>>) /\
                 (<<TM1: Time.lt (Memory.max_ts loc mem1) (incr_time_seq n)>>) /\
                 (<<TM2: Time.le (tm loc) (incr_time_seq n)>>))).
    intros loc. hexploit (incr_time_seq_diverge
                            (Time.join (Time.join
                                          (Memory.max_ts loc (Thread.memory th))
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
  des.
  hexploit (@cap_flex_exists (Thread.memory th) (fun loc => incr_time_seq (ftm loc))); eauto.
  { i. eapply TM. }
  intros [cap CAP]. des.
  exploit CONSISTENT; eauto.
  { i. eapply TM. }
  i. des.
  exploit ThreadTrace.trace_steps_thread_trace_steps; eauto. i. des.
  hexploit (@cap_flex_future_memory_map (Thread.memory th)); eauto.
  { i. eapply TM. }
  { i. left. eapply TM. }
  intros MEMORY. destruct e1. ss.
  hexploit thread_trace_steps_map.
  { eapply ident_map_le; eauto. }
  { eapply ident_map_bot; eauto. }
  { eapply ident_map_eq; eauto. }
  { eapply ident_map_lt; eauto. }
  { eapply List.Forall_forall. i. eapply ident_map_mappable_evt. }
  { eapply STEPS0. }
  { ss. }
  { ss. }
  { ss. }
  { eapply cap_flex_wf; eauto. }
  { eapply LOCAL. }
  { eauto. }
  { eapply cap_flex_closed; eauto. i. eapply TM. }
  { eapply Memory.closed_timemap_bot; eauto. eapply CLOSED. }
  { eapply Memory.closed_timemap_bot; eauto.
    eapply cap_flex_closed; eauto. i. eapply TM. }
  { econs; eauto.
    { eapply ident_map_local. }
    { eapply mapping_map_lt_iff_collapsable_unwritable. eapply ident_map_lt_iff. }
    { eapply ident_map_timemap. }
    { refl. }
  }
  i. des.
  exploit ThreadTrace.thread_trace_steps_trace_steps; eauto. i. des.
  assert (LCTRACE: List.Forall2
                     (fun em fem : Local.t * ThreadEvent.t => tevent_map ident_map (snd fem) (snd em)) ftr tr0).
  { eapply list_Forall2_compose.
    { eapply list_Forall2_rev. eauto. }
    { eapply list_Forall2_compose.
      { eauto. }
      { eauto. }
      simpl. i.
      instantiate (1:=fun em fem => tevent_map ident_map (snd fem) (snd em)).
      ss. des. rewrite SAT2 in *. auto.
    }
    i. ss. des. rewrite SAT2 in *. auto.
  }
  assert (FEVENTS: List.Forall
                     (fun em : Local.t * ThreadEvent.t =>
                        ((((promise_free (snd em) /\ no_sc (snd em)) /\
                           no_read_msgs
                             (fun (loc : Loc.t) (ts : Time.t) =>
                                ~
                                  (covered loc ts (Local.promises (Thread.local th)) \/
                                   concrete_promised (Thread.memory th) loc ts \/ Time.lt (tm loc) ts))
                             (snd em)) /\
                          write_not_in
                            (fun (loc : Loc.t) (ts : Time.t) =>
                               Time.le ts (tm loc) /\ ~ covered loc ts (Local.promises (Thread.local th)))
                            (snd em)) /\ wf_time_evt times (snd em)) /\
                        ThreadEvent.get_machine_event (snd em) = MachineEvent.silent) tr0).
  { esplits; eauto.
    eapply List.Forall_forall. i.
    eapply list_Forall2_in in H; eauto. des.
    eapply List.Forall_forall in IN; eauto. ss. des.
    destruct a, x. ss. splits; auto.
    { inv SAT; ss. inv FROM. inv TO. inv KIND; ss.
      inv MSG; ss. inv MAP0; ss. }
    { inv SAT; ss. }
    { inv SAT; ss.
      { inv TO. ii. eapply SAT3. ii. eapply H. des; auto.
        right. right. eapply TimeFacts.le_lt_lt; eauto. apply TM. }
      { inv FROM. ii. eapply SAT3. ii. eapply H. des; auto.
        right. right. eapply TimeFacts.le_lt_lt; eauto. apply TM. }
      { inv TO. ii. eapply SAT3. ii. eapply H. des; auto.
        right. right. eapply TimeFacts.le_lt_lt; eauto. apply TM. }
    }
    { inv SAT; ss.
      { inv TO. inv FROM. inv KIND; ss. ii. eapply SAT2; eauto.
        des. split; auto. red. etrans; eauto. eapply TM. }
      { inv TO. inv FROM. ii. eapply SAT2; eauto.
        des. split; auto. red. etrans; eauto. eapply TM. }
      { splits.
        { i. inv TO. inv FROM. ii. eapply SAT2; eauto.
          des. split; auto. red. etrans; eauto. eapply TM. }
        { eapply List.Forall_forall. ii.
          eapply list_Forall2_in in H; eauto. des.
          eapply List.Forall_forall in IN0; eauto. ss.
          destruct a, x. ss. destruct p, t3. ss. inv SAT. inv SAT5.
          eapply IN0; eauto.
          split; auto. red. etrans; eauto. eapply TM. }
      }
      { inv TO. inv FROM. ii. eapply SAT2; eauto.
        des. split; auto. red. etrans; eauto. eapply TM. }
    }
    { inv SAT; ss.
      { inv FROM. inv TO. auto. }
      { inv FROM. inv TO. auto. }
      { inv FROM. inv TO. des. splits; auto.
        eapply List.Forall_forall. ii.
        eapply list_Forall2_in in H; eauto. des.
        destruct a, x. ss. destruct p, p0. ss. inv SAT. inv SAT1.
        eapply List.Forall_forall in MSGS0; eauto. auto.
      }
      { inv FROM. inv TO. auto. }
    }
    { inv SAT; ss. }
  }
  esplits; eauto.
  { unfold cancel_normal_trace in *. des. subst.
    eapply List.Forall2_app_inv_l in LCTRACE. des. subst. esplits; eauto.
    { eapply List.Forall_forall. i. eapply list_Forall2_in in H; eauto. des.
      destruct a, x. ss. eapply List.Forall_forall in IN; eauto. ss. inv SAT; ss.
      inv KIND; ss; des_ifs; inv MSG. }
    { eapply List.Forall_forall. i. eapply list_Forall2_in in H; eauto. des.
      destruct a, x. ss. eapply List.Forall_forall in IN; eauto. ss. inv SAT; ss.
      inv KIND; ss; des_ifs; inv MSG. }
  }
  { i. subst.
    assert (exists l1 l2 e_mid fe_mid,
               (<<EQ: ftr = l1 ++ l2>>) /\
               (<<STEPSCAP1: Trace.steps
                               l1
                               (Thread.mk _ (Thread.state th) (Thread.local th) TimeMap.bot cap) e_mid>>) /\
               (<<STEPSCAP2: Trace.steps
                               l2
                               e_mid
                               (Thread.mk _ state local sc memory)>>) /\
               (<<STEPSMEM: Trace.steps
                              ftr1
                              (Thread.mk _ (Thread.state th) (Thread.local th) TimeMap.bot mem1) fe_mid>>) /\
               (<<MAP: thread_map ident_map e_mid fe_mid>>) /\
               (<<LCTRACE0: List.Forall2
                             (fun em fem => tevent_map ident_map (snd fem) (snd em))
                             l1 ftr1>>) /\
               (<<LCTRACE1: List.Forall2
                              (fun em fem => tevent_map ident_map (snd fem) (snd em))
                              l2 ftr2>>)).
    { clear SPLIT CANCELNORMAL EVENTS CAP MAPLT MAPIDENT BOUND FEVENTS.
      eapply List.Forall2_app_inv_r in MATCH0. des. subst.
      eapply List.Forall2_app_inv_r in TRACE0. des. subst.
      eapply ThreadTrace.steps_separate in STEPS0. des.
      eapply ThreadTrace.steps_separate in STEPS1. des.
      eapply ThreadTrace.thread_trace_steps_trace_steps in STEPS3.
      dup STEPS4. eapply ThreadTrace.thread_trace_steps_trace_steps in STEPS4.
      eapply ThreadTrace.thread_trace_steps_trace_steps in STEPS0. des.
      assert (ftr1 = tr0).
      { eapply thread_trace_trace_match_map in MATCH2.
        eapply thread_trace_trace_match_map in MATCH0. subst. auto. }
      subst.
      assert (ftr = tr2 ++ tr1).
      { eapply thread_trace_trace_match_map in MATCH.
        eapply thread_trace_trace_match_map in MATCH4.
        eapply thread_trace_trace_match_map in MATCH3. subst.
        eapply List.map_app. }
      subst. esplits; eauto.
      { destruct l3.
        { inv TRACE1. inv MATCH1. inv NORMAL. inv MATCH3.
          inv STEPS5; ss. inv STEPS0; ss. }
        { inv TRACE1. inv MATCH1. inv MATCH3.
          inv STEPS5; ss. inv STEPS1; ss. clarify. ss. des. auto. }
      }
      { eapply list_Forall2_compose.
        { eapply list_Forall2_rev. eapply MATCH4. }
        { eapply list_Forall2_compose.
          { eapply TRACE0. }
          { eauto. }
          { simpl. i. instantiate (1:=fun em fem =>tevent_map ident_map (snd fem) (snd em)).
            ss. des. rewrite SAT2 in *. auto. }
        }
        { i. ss. des. rewrite SAT2 in *. auto. }
      }
      { eapply list_Forall2_compose.
        { eapply list_Forall2_rev. eapply MATCH3. }
        { eapply list_Forall2_compose.
          { eapply TRACE1. }
          { eauto. }
          { simpl. i. instantiate (1:=fun em fem =>tevent_map ident_map (snd fem) (snd em)).
            ss. des. rewrite SAT2 in *. auto. }
        }
        { i. ss. des. rewrite SAT2 in *. auto. }
      }
    }
    clear LCTRACE. des. exploit SPLIT; eauto.
    { clear - LCTRACE1 NORMAL.
      eapply List.Forall_forall. i. eapply list_Forall2_in2 in H; eauto.
      des. eapply List.Forall_forall in IN; eauto. ss.
      destruct b, x. ss. inv SAT; ss.
      inv KIND; ss; des_ifs; inv MSG. }
    i. des.
    inv MAP0. destruct e2. ss.

    exploit Trace.steps_future; try apply STEPSCAP1; eauto.
    { eapply cap_flex_wf; eauto. }
    { eapply Memory.closed_timemap_bot; eauto.
      eapply cap_flex_closed; eauto. i. eapply TM. }
    { eapply cap_flex_closed; eauto. i. eapply TM. } i. des. ss.
    exploit Trace.steps_future; try apply STEPSMEM; eauto.
    { eapply Memory.closed_timemap_bot; eauto. eapply CLOSED. } i. des. ss.

    hexploit trace_steps_map; try apply STEPS3.
    { eapply ident_map_le; eauto. }
    { eapply ident_map_bot; eauto. }
    { eapply ident_map_eq; eauto. }
    { eapply ident_map_lt; eauto. }
    { eapply List.Forall_forall. i. eapply ident_map_mappable_evt. }
    { ss. }
    { ss. }
    { ss. }
    { eauto. }
    { eapply WF0. }
    all: eauto. i. des.
    eexists ftr, ftr_cancel, _. splits.
    { eapply Trace.steps_trans.
      { eapply STEPSMEM. }
      { eapply STEPS4. }
    }
    { clear - TM RESERVE TRACE1. eapply List.Forall_forall. i.
      eapply list_Forall2_in in H; eauto. des.
      eapply List.Forall_forall in IN; eauto. ss. des.
      destruct a, x. ss. unfold ident_map in *.
      inv EVENT; ss; des; subst; eauto. inv MSG; inv KIND; ss. splits; auto.
      ii. eapply IN0; eauto. des. splits; auto. etrans; eauto. eapply TM. }
    { eauto. }
    { eapply pf_consistent_speciali_events_map with (tr1 := ftr_cancel ++ ftr2) in CONSISTENT0; cycle 1.
      { eapply list_Forall2_app.
        { eapply list_Forall_refl_Forall2; eauto. eapply List.Forall_forall.
          ii. destruct x. ss. destruct t0; econs; ss.
          eapply list_Forall2_impl.
          { instantiate (1:=eq). refl. }
          { i. subst. destruct b as [[from0 to0] msg0].
            ss. splits; ss. destruct msg0; econs.
          }
        }
        { eapply list_Forall2_impl; eauto. i. eapply tevent_map_tevent_map_weak; eauto. }
      }
      { eapply Trace.steps_future in STEPS3; eauto. des.
        eapply Trace.steps_future in STEPS4; eauto. des.
        eapply ident_map_pf_consistent_super_strong_easy; eauto.
        econs; eauto.
        eapply mapping_map_lt_iff_collapsable_unwritable; eauto. eapply ident_map_lt_iff; eauto.
      }
    }
    { exists ftr_cancel, ftr2. splits; auto.
      eapply List.Forall_impl; eauto. i. ss. des. auto. }
  }
  { ii. exploit BOUND; eauto. i. des. split; auto.
    etrans; eauto. eapply TM. }
  { eapply list_Forall2_compose; eauto. i. ss. des.
    eapply ident_map_compose_tevent_weak; eauto.
    eapply tevent_map_tevent_map_weak; eauto.
  }
  { ss. inv MAP. inv LOCAL0. rewrite PROMISES in *.
    eapply bot_promises_map; eauto.
  }
Qed.

Lemma pf_consistent_super_strong_easy_promise_consistent lang (e0: Thread.t lang) tr times
      (CONSISTENT: pf_consistent_super_strong_easy e0 tr times)
      (CLOSED: Memory.closed (Thread.memory e0))
      (LOCAL: Local.wf (Thread.local e0) (Thread.memory e0))
  :
    Local.promise_consistent (Thread.local e0).
Proof.
  hexploit (@concrete_promise_max_timemap_exists
              (Thread.memory e0)
              (Local.promises (Thread.local e0))); eauto.
  { eapply CLOSED. } i. des.
  assert (exists (f: Loc.t -> nat),
             forall loc,
               Time.lt (Memory.max_ts loc (Thread.memory e0)) (incr_time_seq (f loc))).
  { eapply (choice
              (fun loc n =>
                 Time.lt (Memory.max_ts loc (Thread.memory e0)) (incr_time_seq n))).
    i. eapply incr_time_seq_diverge; eauto. }
  des.
  exploit (@cap_flex_exists
             (Thread.memory e0)
             (fun loc => incr_time_seq (f loc))); eauto. i. des.
  exploit CONSISTENT; eauto. i. des.
  eapply Trace.steps_promise_consistent in STEPS; eauto; ss.
  { ii. erewrite PROMISES in *. erewrite Memory.bot_get in *. ss. }
  { eapply cap_flex_wf; eauto. }
  { eapply Memory.closed_timemap_bot; eauto.
    eapply cap_flex_closed; eauto. }
  { eapply cap_flex_closed; eauto. }
Qed.

Definition pf_consistent_super_strong lang (e0:Thread.t lang)
           (tr : Trace.t)
           (times: Loc.t -> (Time.t -> Prop))
  : Prop :=
  forall mem1 tm sc max
         (FUTURE: Memory.future_weak (Thread.memory e0) mem1)
         (CLOSED: Memory.closed mem1)
         (LOCAL: Local.wf (Thread.local e0) mem1)
         (MAX: concrete_promise_max_timemap
                 ((Thread.memory e0))
                 ((Local.promises (Thread.local e0)))
                 max),
  exists ftr e1 f,
    (<<STEPS: Trace.steps ftr (Thread.mk _ (Thread.state e0) (Thread.local e0) sc mem1) e1>>) /\
    (<<EVENTS: List.Forall (fun em => <<SAT: (promise_free
                                                /1\ no_sc
                                                /1\ no_read_msgs (fun loc ts => ~ (covered loc ts (Local.promises (Thread.local e0)) \/ concrete_promised (Thread.memory e0) loc ts \/ Time.lt (tm loc) ts))
                                                /1\ write_not_in (fun loc ts => (<<TS: Time.le ts (tm loc)>>) /\ (<<PROM: ~ covered loc ts (Local.promises (Thread.local e0))>>))
                                                /1\ wf_time_evt times) (snd em)>> /\ <<TAU: ThreadEvent.get_machine_event (snd em) = MachineEvent.silent>>) ftr >>) /\

    (<<CANCELNORMAL: cancel_normal_trace ftr>>) /\
    (<<SPLIT:
       forall ftr0 ftr1
              (FTRACE: ftr = ftr0 ++ ftr1)
              (NORMAL: List.Forall (fun em => ~ ThreadEvent.is_cancel (snd em)) ftr1),
       exists ftr_reserve ftr_cancel e2,
         (<<STEPS: Trace.steps (ftr0 ++ ftr_reserve) (Thread.mk _ (Thread.state e0) (Thread.local e0) sc mem1) e2>>) /\
         (<<RESERVE: List.Forall (fun em => <<SAT: (ThreadEvent.is_reserve
                                                      /1\ wf_time_evt times
                                                      /1\ write_not_in (fun loc ts => (<<TS: Time.le ts (tm loc)>>) /\ (<<PROM: ~ covered loc ts (Local.promises (Thread.local e0))>>))) (snd em)>>) ftr_reserve>>) /\
         (<<CANCEL: List.Forall (fun em => <<SAT: (ThreadEvent.is_cancel /1\ wf_time_evt times) (snd em)>>) ftr_cancel>>) /\
         (<<CONSISTENT: pf_consistent_super_strong_easy e2 (ftr_cancel ++ ftr1) times>>) /\
         (<<PROMCONSISTENT: Local.promise_consistent (Thread.local e2)>>) /\
         (<<CANCELNORMAL: cancel_normal_trace (ftr_cancel ++ ftr1)>>) /\
         (<<GOOD: good_future tm mem1 (Thread.memory e2)>>) /\
         (<<SC: (Thread.sc e2) = sc>>)>>) /\

    (<<MAPLT: mapping_map_lt_iff f>>) /\
    (<<MAPIDENT: forall loc ts fts
                        (TS: Time.le fts (max loc))
                        (MAP: f loc ts fts),
        ts = fts>>) /\
    (<<BOUND: forall loc ts fts (TS: Time.lt (max loc) fts) (MAP: f loc ts fts),
        Time.lt (max loc) ts /\ Time.le (tm loc) fts>>) /\
    (<<TRACE: List.Forall2 (fun em fem => tevent_map_weak f (snd fem) (snd em)) tr ftr>>) /\
    (<<GOOD: good_future tm mem1 (Thread.memory e1)>>) /\
    (<<SC: (Thread.sc e1) = sc>>) /\
    (<<PROMCONSISTENT: Local.promise_consistent (Thread.local e1)>>) /\
    ((<<PROMISES: (Local.promises (Thread.local e1)) = Memory.bot>>) /\
     (<<WRITES: forall loc from to msg
                       (GET: Memory.get loc to (Local.promises (Thread.local e0)) = Some (from, msg))
                       (NRESERVE: msg <> Message.reserve),
         exists th e,
           (<<WRITING: promise_writing_event loc from to msg e>>) /\
           (<<IN: List.In (th, e) ftr>>)>>)).

Lemma pf_consistent_super_strong_aux2_super_strong
      lang (th: Thread.t lang) tr times
      (WF: Local.wf (Thread.local th) (Thread.memory th))
      (MEM: Memory.closed (Thread.memory th))
      (CONSISTENT: pf_consistent_super_strong_aux2 th tr times)
  :
    pf_consistent_super_strong th tr times.
Proof.
  ii. set (tm0:=TimeMap.join tm (fun loc => Time.incr (Memory.max_ts loc mem1))).
  assert (TM0: forall loc, Time.lt (Memory.max_ts loc mem1) (tm0 loc)).
  { i. eapply TimeFacts.lt_le_lt.
    { eapply Time.incr_spec. }
    { eapply Time.join_r. }
  }
  assert (TM1: TimeMap.le tm tm0).
  { eapply TimeMap.join_l. }
  exploit (CONSISTENT mem1 tm0 max); eauto. i. des. destruct e1. ss.
  dup STEPS. eapply no_sc_any_sc_traced in STEPS; eauto; cycle 1.
  { eapply List.Forall_impl; eauto. i. ss. des. auto. } des.
  esplits; eauto.
  { eapply List.Forall_impl; eauto. i. ss. des. splits; auto.
    { eapply no_read_msgs_mon; eauto. ii. eapply PR. des; auto.
      right. right. eapply TimeFacts.le_lt_lt; eauto. }
    { eapply write_not_in_mon; eauto. ii. des. split; auto.
      red. etrans; eauto. }
  }
  { i. subst.
    exploit SPLIT; eauto. i. des. destruct e2. ss.
    assert (NOSC: List.Forall (fun em => no_sc (snd em)) (ftr0 ++ ftr_reserve)).
    { eapply Forall_app.
      { eapply Forall_app_inv in EVENTS. des.
        eapply List.Forall_impl; eauto. i. ss. des. auto. }
      { eapply List.Forall_impl; eauto. i. ss. des.
        destruct a. ss. destruct t0; ss. }
    }
    dup STEPS.
    eapply no_sc_any_sc_traced in STEPS; eauto; cycle 1. des.
    esplits; eauto.
    { eapply List.Forall_impl; eauto. i. ss. des. splits; auto.
      eapply write_not_in_mon; eauto. i. ss. des. splits; auto. etrans; eauto. }
    { eapply pf_consistent_speciali_strong_easy in CONSISTENT0; eauto. }
    { eapply Trace.steps_future in STEPS2; eauto.
      { ss. des. eapply pf_consistent_speciali_strong_easy in CONSISTENT0; eauto.
        eapply pf_consistent_super_strong_easy_promise_consistent in CONSISTENT0; eauto. }
      { ss. eapply Memory.closed_timemap_bot. eapply CLOSED. }
    }
    { eapply good_future_mon with (tm1:=tm0); auto.
      eapply write_not_in_good_future_traced in STEPS2; eauto.
      { ss. eapply Memory.closed_timemap_bot; eauto. eapply CLOSED. }
      { eapply Forall_app.
        { eapply Forall_app_inv in EVENTS. des. ss.
          eapply List.Forall_impl; eauto. i. ss. des.
          eapply write_not_in_mon; eauto. ii. des. split; auto.
          ii. eapply PROM. eapply memory_le_covered; eauto. eapply LOCAL. }
        { eapply List.Forall_impl; eauto. i. ss. des.
          eapply write_not_in_mon; eauto. ii. des. split; auto.
          ii. eapply PROM. eapply memory_le_covered; eauto. eapply LOCAL. }
      }
    }
    { ss. eapply no_sc_same_sc_traced in STEPS3; eauto. }
  }
  { ii. exploit BOUND; eauto. i. des. splits; auto. etrans; eauto. }
  { eapply good_future_mon with (tm1:=tm0); auto.
    eapply write_not_in_good_future_traced in STEPS0; eauto.
    { ss. eapply Memory.closed_timemap_bot; eauto. eapply CLOSED. }
    { eapply List.Forall_impl; eauto. i. ss. des. splits; auto.
      eapply write_not_in_mon; eauto. ii. des. split; auto.
      ii. eapply PR0. eapply memory_le_covered; eauto. eapply LOCAL. }
  }
  { eapply no_sc_same_sc_traced in STEPS1; eauto.
    eapply List.Forall_impl; eauto. i. ss. des. auto. }
  { ss. eapply Local.bot_promise_consistent; eauto. }
  { ss. splits; auto.
    i. eapply steps_promise_decrease_promise_writing_event in STEPS1; eauto.
    des; eauto. ss. erewrite PROMISES in *. erewrite Memory.bot_get in *. ss. }
Qed.


Lemma pf_consistent_super_strong_not_easy lang (th: Thread.t lang)
      tr times
      (LOCAL: Local.wf (Thread.local th) (Thread.memory th))
      (MEM: Memory.closed (Thread.memory th))
      (CONSISTENT: pf_consistent_super_strong_easy th tr times)
      (CANCELNORMAL: cancel_normal_trace tr)
      (MWF: memory_times_wf times (Thread.memory th))
      (DIVERGE: forall loc n, times loc (incr_time_seq n))
  :
    pf_consistent_super_strong th tr times.
Proof.
  eapply pf_consistent_super_strong_aux2_super_strong; eauto.
  eapply pf_consistent_super_strong_aux_aux2; eauto.
  eapply pf_consistent_super_strong_easy_aux; eauto.
  eapply pf_consistent_flex_super_strong_easy_split; eauto.
Qed.

Lemma consistent_pf_consistent_super_strong lang (th: Thread.t lang)
      (LOCAL: Local.wf (Thread.local th) (Thread.memory th))
      (MEM: Memory.closed (Thread.memory th))
      (SC: Memory.closed_timemap (Thread.sc th) (Thread.memory th))
      (CONSISTENT: Thread.consistent th)
  :
    (<<FAILURE: Thread.steps_failure th>>) \/
    exists tr certimes,
      (<<WO: forall loc, well_ordered (certimes loc)>>) /\
      <<CONSISTENT: pf_consistent_super_strong th tr certimes>>.
Proof.
  eapply consistent_pf_consistent in CONSISTENT; eauto. des; eauto. right.
  eapply pf_consistent_pf_consistent_strong in CONSISTENT0; eauto.
  eapply pf_consistent_strong_pf_consistent_strong_aux in CONSISTENT0; eauto.
  eapply pf_consistent_strong_aux_pf_consistent_flex in CONSISTENT0; eauto. des.
  eapply pf_consistent_flex_super_strong_easy in CONSISTENT; eauto. des.
  eapply pf_consistent_super_strong_not_easy in CONSISTENT; eauto.
Qed.

Lemma pf_consistent_super_strong_consistent lang (th: Thread.t lang)
      (LOCAL: Local.wf (Thread.local th) (Thread.memory th))
      (MEM: Memory.closed (Thread.memory th))
      tr certimes
      (CONSISTENT: pf_consistent_super_strong th tr certimes)
  :
    Thread.consistent th.
Proof.
  hexploit (@concrete_promise_max_timemap_exists
              ((Thread.memory th))
              ((Local.promises (Thread.local th)))).
  { eapply MEM. } intros [max MAX]. des.
  ii. exploit (CONSISTENT mem1 max).
  { eapply Memory.cap_future_weak; eauto. }
  { eapply Memory.cap_closed; eauto. }
  { eapply Local.cap_wf; eauto. }
  { eauto. }
  i. des.
  eapply pred_steps_trace_steps2 in STEPS; cycle 1.
  { instantiate (1:=fun _ => True). eapply List.Forall_impl; eauto.
    i. ss. des. splits; auto. }
  eapply thread_steps_pred_steps in STEPS.
  right. esplits; eauto.
Qed.

Definition pf_consistent_super_strong_mon lang e0 tr certimes0 certimes1
           (CONSISTENT: @pf_consistent_super_strong
                          lang e0 tr certimes0)
           (LE: certimes0 <2= certimes1)
  :
    pf_consistent_super_strong e0 tr certimes1.
Proof.
  ii. exploit CONSISTENT; eauto. i. des. esplits; eauto.
  { eapply List.Forall_impl; eauto. i. ss. des. splits; auto.
    eapply wf_time_evt_mon; eauto. }
  { i. exploit SPLIT; eauto. i. des. exists ftr_reserve, ftr_cancel, e2. splits; ss.
    { eapply List.Forall_impl; eauto. i. ss. des. splits; auto.
      eapply wf_time_evt_mon; eauto. }
    { eapply List.Forall_impl; eauto. i. ss. des. splits; auto.
      eapply wf_time_evt_mon; eauto. }
    { eapply pf_consistent_super_strong_easy_mon; eauto. }
  }
Qed.

Lemma promises_bot_certify_nil_easy times lang (th: Thread.t lang)
      (PROMISES: (Local.promises (Thread.local th)) = Memory.bot)
  :
    pf_consistent_super_strong_easy th [] times.
Proof.
  ii. eexists [], _, bot3. esplits; eauto.
  { exists [], []. splits; ss. }
  { ii. ss. }
  { ii. ss. }
  { ii. ss. }
Qed.

Lemma promises_bot_certify_nil times lang (th: Thread.t lang)
      (PROMISES: (Local.promises (Thread.local th)) = Memory.bot)
  :
    pf_consistent_super_strong th [] times.
Proof.
  ii. eexists [], _, bot3. esplits; eauto.
  { exists [], []. splits; ss. }
  { i. destruct ftr0; ss. subst. esplits; eauto.
    { ss. eapply promises_bot_certify_nil_easy; ss. }
    { ss. ii. erewrite PROMISES in *. erewrite Memory.bot_get in *. ss. }
    { exists [], []. splits; ss. }
    { refl. }
  }
  { ii. ss. }
  { ii. ss. }
  { ii. ss. }
  { refl. }
  { eapply Local.bot_promise_consistent; eauto. }
  { ss. splits; auto. i.
    rewrite PROMISES in *. erewrite Memory.bot_get in *. ss. }
Qed.

Lemma certify_nil_promises_bot_or_failure times lang (th: Thread.t lang)
      (CONSISTENT: pf_consistent_super_strong th [] times)
      (CLOSED: Memory.closed (Thread.memory th))
      (LOCAL: Local.wf (Thread.local th) (Thread.memory th))
  :
    (<<PROMISES: (Local.promises (Thread.local th)) = Memory.bot>>) \/
    exists st',
      (<<FAILURE: Language.step lang ProgramEvent.failure (@Thread.state lang th) st'>>) /\
      (<<LOCAL: Local.failure_step (Thread.local th)>>).
Proof.
  exploit concrete_promise_max_timemap_exists.
  { eapply CLOSED. } i. des.
  exploit (CONSISTENT (Thread.memory th) TimeMap.bot (Thread.sc th) tm); eauto.
  { refl. } i. des. inv TRACE. inv STEPS; ss.
  unguard. des; eauto.
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
    apply GOOD in GET. des; auto.
    destruct (classic (msg = Message.reserve)); auto. right.
    eapply Memory.future_weak_get1 in GET; eauto.
    2:{ inv MSG; inv MSGLE; ss. }
    des. esplits; cycle 3.
    { eauto. }
    { eapply IDENT; eauto. }
    { eapply message_map_incr; eauto. }
    { etrans; eauto. }
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
      max_tgt
      (MAXTGT: concrete_promise_max_timemap mem_tgt (Local.promises lc_tgt) max_tgt)
      (MWF: memory_times_wf times mem_src)
      (DIVERGE: forall loc n, times loc (incr_time_seq n))
  :
    exists tr_good f_good,
      (<<MAPLT: mapping_map_lt_iff f_good>>) /\
      (<<MAPIDENT: forall loc ts fts
                          (TS: Time.le fts (max_tgt loc))
                          (MAP: f_good loc ts fts),
          ts = fts>>) /\
      (<<BOUND: forall loc ts fts (TS: Time.lt (max_tgt loc) fts) (MAP: f_good loc ts fts),
          Time.lt (max_tgt loc) ts /\ Time.lt (Memory.max_ts loc mem_tgt) fts>>) /\
      (<<TRACE: List.Forall2 (fun em fem => tevent_map_weak f_good (snd fem) (snd em)) tr tr_good>>) /\
      (<<CONSISTENT:
         pf_consistent_super_strong (Thread.mk lang st lc_src sc_src mem_src) tr_good times>>)
.
Proof.
  hexploit (CONSISTENT mem_tgt (fun loc => Time.incr (Time.join (Memory.max_ts loc mem_tgt) (Memory.max_ts loc mem_src))) sc_tgt); eauto.
  { refl. } ss.
  intros [tr_good [e1_good [f_good [STEPSGOOD [EVENTSGOOD [CANCELNORMALGOOD [SPLITGOOD [MAPLTGOOD [IDENTGOOD [BOUNDGOOD [TRACEGOOD [GOODFUTURE [SCGOOD GOODEND]]]]]]]]]]]]]. des.
  exists tr_good, f_good. splits; auto.
  { i. eapply BOUNDGOOD in MAP; eauto. des. splits; eauto.
    eapply TimeFacts.lt_le_lt; eauto. eapply TimeFacts.le_lt_lt.
    { eapply Time.join_l. }
    { eapply Time.incr_spec. }
  }
  eapply pf_consistent_super_strong_not_easy; eauto. ii. ss.
  assert (MAXMAP: TimeMap.le max_tgt max).
  { eapply memory_ident_map_concrete_promise_max_timemap; eauto.
    eapply LOCAL. }

  set (tm0 := TimeMap.join (fun loc => incr_time_seq (tm loc))
                           (fun loc => Time.incr
                                         (Time.join
                                            (max loc)
                                            (Time.join
                                               (Memory.max_ts loc cap)
                                               (Memory.max_ts loc mem_tgt))))).
  assert (TM0: forall loc, Time.lt (Memory.max_ts loc cap) (tm0 loc)).
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
  assert (TM2: TimeMap.le (fun loc => incr_time_seq (tm loc)) tm0).
  { eapply TimeMap.join_l. }
  assert (TM3: forall loc, Time.lt (max loc) (tm0 loc)).
  { i. unfold tm0. eapply TimeFacts.le_lt_lt.
    { eapply Time.join_l. } eapply TimeFacts.lt_le_lt.
    { eapply Time.incr_spec. }
    { eapply Time.join_r. }
  }
  exploit (@good_future_future_future mem_tgt mem_src cap); eauto.
  { eapply cap_flex_future_weak; eauto. }
  i. des.

  exploit (CONSISTENT mem1 tm0 TimeMap.bot); eauto.
  { ss. eapply cap_flex_future_weak; eauto. }
  { eapply cap_flex_closed; eauto. }
  { ss. eapply cap_flex_wf; eauto. }
  ss. i. des. destruct e1. ss.
  hexploit trace_steps_map.
  { eapply ident_map_le; eauto. }
  { eapply ident_map_bot; eauto. }
  { eapply ident_map_eq; eauto. }
  { eapply ident_map_lt; eauto. }
  { eapply List.Forall_forall. i. eapply ident_map_mappable_evt. }
  { eauto. }
  { ss. }
  { ss. }
  { ss. }
  { eapply cap_flex_wf; eauto. }
  { eapply cap_flex_wf; try apply CAP; eauto. }
  { eapply cap_flex_closed; eauto. }
  { eapply cap_flex_closed; eauto. }
  { eapply Memory.closed_timemap_bot.
    eapply cap_flex_closed; eauto. }
  { eapply Memory.closed_timemap_bot.
    eapply cap_flex_closed; eauto. }
  { eapply local_map_incr; eauto. eapply ident_map_lt_iff; eauto. }
  { eauto. }
  { eapply mapping_map_lt_iff_collapsable_unwritable; eauto. eapply ident_map_lt_iff. }
  { eapply ident_map_timemap. }
  { refl. }
  i. des.
  eexists ftr0, _, (fun loc ts0 ts2 => exists ts1, <<TS0: f_good loc ts1 ts0>> /\ <<TS1: f0 loc ts1 ts2>>).
  esplits; eauto; ss.
  { eapply List.Forall_forall. i. eapply list_Forall2_in in H; eauto. des.
    eapply List.Forall_forall in IN; eauto. ss. des. destruct a, x. ss.
    inv EVENT; splits; ss.
    { inv KIND; ss. inv MSG; ss. inv MAP0; ss. }
    { inv FROM. inv TO. auto. }
    { inv FROM. inv TO. auto. }
    { des. inv FROM. inv TO. splits; auto.
      eapply List.Forall_forall. i. eapply list_Forall2_in in H; eauto. des.
      eapply List.Forall_forall in IN; [|eapply MSGS0]. ss.
      destruct a, x. destruct p, p0. ss. inv SAT0. inv SAT5. des; auto.
    }
    { inv FROM. inv TO. auto. }
  }
  { clear - CANCELNORMAL TRACE0. unfold cancel_normal_trace in *. des. subst.
    eapply List.Forall2_app_inv_l in TRACE0. des. subst. esplits; eauto.
    { eapply List.Forall_forall. i. eapply list_Forall2_in in H; eauto. des.
      eapply List.Forall_forall in IN; eauto. destruct a, x. ss. inv EVENT; ss.
      inv KIND; ss; des_ifs; inv MSG. }
    { eapply List.Forall_forall. i. eapply list_Forall2_in in H; eauto. des.
      eapply List.Forall_forall in IN; eauto. destruct a, x. ss. inv EVENT; ss.
      inv KIND; ss; des_ifs; inv MSG. }
  }
  { ii. des. erewrite <- (MAPLTGOOD loc ts0 ts1 t0 t1); eauto. }
  { ii. des.
    destruct (Time.le_lt_dec fts (max_tgt loc)).
    { dup l. eapply MAPIDENT in l; cycle 1; eauto. subst.
      destruct (Time.le_lt_dec ts (max_tgt loc)).
      { dup l. eapply IDENTGOOD in l; eauto. }
      { dup l. eapply BOUNDGOOD in l; eauto. des. timetac. }
    }
    { dup l. eapply BOUND in l; cycle 1; eauto. des.
      exfalso. eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt.
      { eapply l1. } eapply TimeFacts.le_lt_lt.
      { eapply TS. }
      auto.
    }
  }
  { ii. des.
    destruct (Time.le_lt_dec fts (max_tgt loc)).
    { dup l. eapply MAPIDENT in l; cycle 1; eauto. subst.
      exfalso. eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt.
      { eapply l0. } eapply TimeFacts.le_lt_lt.
      { eapply MAXMAP. }
      auto.
    }
    { dup l. eapply BOUND in l; cycle 1; eauto. des. splits; eauto.
      destruct (Time.le_lt_dec ts (max_tgt loc)).
      { dup l2. eapply IDENTGOOD in l2; eauto. subst. timetac. }
      { dup l2. eapply BOUNDGOOD in l2; eauto. des.
        eapply TimeFacts.le_lt_lt.
        { eapply concrete_promise_max_ts_max_ts; eauto. eapply LOCALSRC. } eapply TimeFacts.le_lt_lt.
        { eapply Time.join_r. } eapply TimeFacts.lt_le_lt.
        { eapply Time.incr_spec. }
        eauto.
      }
    }
  }
  { dup TRACEGOOD. dup TRACE. dup TRACE0.
    eapply list_Forall2_compose.
    { eapply list_Forall2_rev. eapply TRACEGOOD. }
    { eapply list_Forall2_compose.
      { eapply TRACE. }
      { eapply TRACE0. }
      simpl. instantiate (1:=fun the fthe => tevent_map_weak f0 (snd fthe) (snd the)).
      i. ss. des. eapply tevent_map_tevent_map_weak in EVENT.
      eapply tevent_map_weak_compose; eauto.
      i. inv MAP1. auto.
    }
    i. ss. eapply tevent_map_weak_rev in SAT0.
    { instantiate (1:=fun loc ts fts => f_good loc fts ts) in SAT0.
      eapply tevent_map_weak_compose; eauto.
      i. ss. eauto. }
    { i. ss. }
  }
  { inv LOCAL0. rewrite PROMISES0 in *.
    eapply bot_promises_map in PROMISES1; eauto.
  }
Qed.


Inductive relaxed_writing_event
          (loc: Loc.t) (to: Time.t)
  : forall (msg: Message.t) (e: ThreadEvent.t), Prop :=
| relaxed_writing_event_write
    from released ord val val0
    (ORD: Ordering.le ord Ordering.relaxed)
    (VAL: Const.le val val0)
  :
    relaxed_writing_event
      loc to (Message.concrete val released)
      (ThreadEvent.write loc from to val0 released ord)
| relaxed_writing_event_update
    from releasedw valr releasedr ordr ordw val val0
    (ORD: Ordering.le ordw Ordering.relaxed)
    (VAL: Const.le val val0)
  :
    relaxed_writing_event
      loc to (Message.concrete val releasedw)
      (ThreadEvent.update loc from to valr val0 releasedr releasedw ordr ordw)
| relaxed_writing_event_na_write_exact
    msgs from released val ord val0
    (ORD: Ordering.le ord Ordering.relaxed)
    (VAL: Const.le val val0)
  :
    relaxed_writing_event
      loc to (Message.concrete val released)
      (ThreadEvent.write_na loc msgs from to val0 ord)
| relaxed_writing_event_na_write_msgs
    msgs from msg msg0 ord from1 to1 val1
    (ORD: Ordering.le ord Ordering.relaxed)
    (IN: List.In (from, to, msg0) msgs)
    (MSG: Message.le msg0 msg)
  :
    relaxed_writing_event
      loc to msg
      (ThreadEvent.write_na loc msgs from1 to1 val1 ord)
.
Hint Constructors relaxed_writing_event.

Lemma pf_consistent_super_strong_same_sc lang (e0: Thread.t lang) tr times sc
      (CONSISTENT: pf_consistent_super_strong e0 tr times)
  :
    pf_consistent_super_strong (Thread.mk _ (Thread.state e0) (Thread.local e0) sc (Thread.memory e0)) tr times.
Proof.
  ii. exploit CONSISTENT; eauto.
Qed.


Fixpoint map_somes A B (f: A -> option B) (l: list A): list B :=
  match l with
  | [] => []
  | hd :: tl =>
    match (f hd) with
    | Some b => b :: map_somes f tl
    | None => map_somes f tl
    end
  end.

Lemma map_somes_in A B (f: A -> option B) l a b
      (IN: List.In a l)
      (APP: f a = Some b)
  :
    List.In b (map_somes f l).
Proof.
  ginduction l; eauto. i. ss. des.
  { subst. erewrite APP. ss. auto. }
  { eapply IHl in IN; eauto. destruct (f a); ss; auto. }
Qed.

Lemma map_somes_in_rev A B (f: A -> option B) l b
      (IN: List.In b (map_somes f l))
  :
    exists a,
      (<<IN: List.In a l>>) /\
      (<<APP: f a = Some b>>).
Proof.
  ginduction l; eauto; ss. i. destruct (f a) eqn:EQ.
  { ss. des; subst.
    { esplits; eauto. }
    { eapply IHl in IN. des. esplits; eauto. }
  }
  { eapply IHl in IN. des. esplits; eauto. }
Qed.

Lemma map_somes_split A B (f: A -> option B) l0 l1
  :
    map_somes f (l0 ++ l1) =
    map_somes f l0 ++ map_somes f l1.
Proof.
  ginduction l0; ss; eauto. i. destruct (f a); ss.
  f_equal. eapply IHl0; eauto.
Qed.

Lemma map_somes_split_inv A B (f: A -> option B) l fl0 fl1
      (MAP: map_somes f l = fl0 ++ fl1)
  :
    exists l0 l1,
      (<<EQ: l = l0 ++ l1>>) /\
      (<<MAP0: map_somes f l0 = fl0>>) /\
      (<<MAP1: map_somes f l1 = fl1>>).
Proof.
  ginduction l; eauto.
  { i. ss. destruct fl0; ss. destruct fl1; ss. exists [], []. splits; auto. }
  { i. ss. destruct (f a) eqn:EQ.
    { destruct fl0; ss.
      { destruct fl1; ss. inv MAP.
        exists [], (a::l). splits; auto.
        ss. rewrite EQ. auto.
      }
      { inv MAP. eapply IHl in H1. des. subst.
        exists (a::l0), l1. splits; auto.
        ss. rewrite EQ. auto.
      }
    }
    { eapply IHl in MAP. des. subst.
      exists (a::l0), l1. splits; ss. rewrite EQ. auto. }
  }
Qed.

Lemma map_somes_one A B (f: A -> option B) l b
      (MAP: map_somes f l = [b])
  :
    exists l0 a l1,
      (<<EQ: l = l0 ++ a :: l1>>) /\
      (<<MAP0: map_somes f l0 = []>>) /\
      (<<MAP1: f a = Some b>>) /\
      (<<MAP2: map_somes f l1 = []>>).
Proof.
  ginduction l; eauto.
  { i. ss. }
  { i. ss. destruct (f a) eqn:EQ.
    { inv MAP. exists [], a, l. splits; auto. }
    { eapply IHl in MAP. des. subst.
      exists (a::l0), a0, l1. splits; ss.
      rewrite EQ. auto.
    }
  }
Qed.

Lemma map_somes_split_inv_one A B (f: A -> option B) l fl0 fl1 b
      (MAP: map_somes f l = fl0 ++ b :: fl1)
  :
    exists l0 a l1,
      (<<EQ: l = (l0 ++ [a]) ++ l1>>) /\
      (<<MAP0: map_somes f l0 = fl0>>) /\
      (<<MAP1: f a = Some b>>) /\
      (<<MAP2: map_somes f l1 = fl1>>).
Proof.
  eapply map_somes_split_inv in MAP. des. subst.
  replace (b::fl1) with ([b]++fl1) in MAP2; auto.
  eapply map_somes_split_inv in MAP2. des. subst.
  eapply map_somes_one in MAP1. des. subst.
  exists (l0 ++ l1), a, (l4 ++ l3). splits; auto.
  { repeat erewrite <- List.app_assoc. auto. }
  { erewrite map_somes_split. erewrite MAP1.
    erewrite List.app_nil_end. auto. }
  { erewrite map_somes_split. erewrite MAP3. ss. }
Qed.


Definition writing_locs
           (te: ThreadEvent.t): option (list (Loc.t * Time.t)) :=
  match te with
  | ThreadEvent.write loc _ to _ _ ord =>
    if Ordering.le ord Ordering.relaxed then Some [(loc, to)] else None
  | ThreadEvent.update loc _ to _ _ _ _ _ ord =>
    if Ordering.le ord Ordering.relaxed then Some [(loc, to)] else None
  | ThreadEvent.write_na loc msgs from to _ ord =>
    if Ordering.le ord Ordering.relaxed then Some ((loc, to)::List.map (fun '(from, to, msg) => (loc, to)) msgs) else None
  | _ => None
  end.

Definition check_in_promise prom :=
  fun '(loc, to) =>
    match Memory.get loc to prom with
    | Some (_, msg) =>
      match msg with
      | Message.reserve => false
      | _ => true
      end
    | _ => false
    end.

Definition writing_locs_prom (prom: Memory.t)
           (te: ThreadEvent.t): option (list (Loc.t * Time.t)) :=
  match writing_locs te with
  | Some l => Some (List.filter (check_in_promise prom) l)
  | None => None
  end.

Lemma final_event_trace_post te tr0 tr1
      (FINAL: final_event_trace te tr1)
  :
    final_event_trace te (tr0 ++ tr1).
Proof.
  ginduction tr0; eauto. i. ss. econs; eauto.
Qed.

Lemma cancel_normal_normals_after_normal tr0 lc te tr1
      (CANCELNORMAL: cancel_normal_trace (tr0 ++ (lc, te) :: tr1))
      (NORMAL: ~ ThreadEvent.is_cancel te)
  :
    List.Forall (fun em => <<SAT: (fun e => ~ ThreadEvent.is_cancel e) (snd em)>>) tr1.
Proof.
  unfold cancel_normal_trace in *. des.
  eapply List.Forall_forall. ii.
  eapply List.in_split in H. des. subst.
  ginduction tr_cancel.
  { i. ss. subst. eapply List.Forall_forall in NORMAL0; eauto.
    eapply List.in_or_app. right. ss. right.
    eapply List.in_or_app. right. ss. auto. }
  { i. inv CANCEL. destruct tr0.
    { ss. inv EQ. ss. }
    ss. inv EQ. eapply IHtr_cancel; eauto.
  }
Qed.

Lemma no_concrete_promise_concrete_decrease_write prom0 mem0 loc from to msg prom1 mem1 kind
      (WRITE: Memory.write prom0 mem0 loc from to msg prom1 mem1 kind)
      loc0 ts0 from0 msg0
      (GET: Memory.get loc0 ts0 prom1 = Some (from0, msg0))
      (NRESERVE: msg0 <> Message.reserve)
  :
    exists from1,
      (<<GET: Memory.get loc0 ts0 prom0 = Some (from1, msg0)>>).
Proof.
  inv WRITE. erewrite Memory.remove_o in GET; eauto. des_ifs. guardH o.
  inv PROMISE.
  { erewrite Memory.add_o in GET; eauto. des_ifs.
    { ss. unguard. des; clarify. }
    { esplits; eauto. }
  }
  { erewrite Memory.split_o in GET; eauto. des_ifs.
    { ss. unguard. des; clarify. }
    { ss. unguard. des; clarify. eapply Memory.split_get0 in PROMISES. des.
      eapply Memory.remove_get1 in GET2; eauto. }
    { esplits; eauto. }
  }
  { erewrite Memory.lower_o in GET; eauto. des_ifs.
    { ss. unguard. des; clarify. }
    { esplits; eauto. }
  }
 { erewrite Memory.remove_o in GET; eauto. des_ifs. guardH o0.
   esplits; eauto.
 }
Qed.

Lemma no_concrete_promise_concrete_decrease_write_na prom0 mem0 loc from to msg prom1 mem1 kind
      ts msgs kinds
      (WRITE: Memory.write_na ts prom0 mem0 loc from to msg prom1 mem1 msgs kinds kind)
      loc0 ts0 from0 msg0
      (GET: Memory.get loc0 ts0 prom1 = Some (from0, msg0))
      (NRESERVE: msg0 <> Message.reserve)
  :
    exists from1,
      (<<GET: Memory.get loc0 ts0 prom0 = Some (from1, msg0)>>).
Proof.
  revert loc0 ts0 from0 msg0 GET NRESERVE. induction WRITE; i.
  { eapply no_concrete_promise_concrete_decrease_write; eauto. }
  { hexploit IHWRITE; eauto. i. des.
    hexploit no_concrete_promise_concrete_decrease_write; eauto.
  }
Qed.

Lemma no_concrete_promise_concrete_decrease_steps lang (th0 th1: Thread.t lang) tr
      (STEPS: Trace.steps tr th0 th1)
      (NOPROMISE: List.Forall (fun em => <<SAT: (promise_free \1/ ThreadEvent.is_reserve) (snd em)>>) tr)
      loc ts from msg1
      (GET: Memory.get loc ts (Local.promises (Thread.local th1)) =
            Some (from, msg1))
      (NRESERVE: msg1 <> Message.reserve)
  :
    exists from0 msg0,
      (<<GET: Memory.get loc ts (Local.promises (Thread.local th0)) =
              Some (from0, msg0)>>) /\
      (<<MSG: Message.le msg1 msg0>>).
Proof.
  ginduction STEPS; eauto; i; subst.
  { esplits; eauto. refl. }
  inv NOPROMISE. guardH H1. ss.
  eapply IHSTEPS in GET; eauto. des. inv STEP.
  { unguard. inv STEP0; ss. inv LOCAL. inv PROMISE; ss.
    { des_ifs; des; ss. erewrite Memory.add_o in GET0; eauto. des_ifs.
      { inv MSG; ss. }
      { esplits; eauto. }
    }
    { des; ss; clarify. des_ifs. }
    { clear H1. erewrite Memory.lower_o in GET0; eauto. des_ifs; eauto.
      ss. des; clarify. eapply Memory.lower_get0 in PROMISES; eauto.
      des. esplits; eauto. etrans; eauto. }
    { des; ss. erewrite Memory.remove_o in GET0; eauto. des_ifs; eauto. }
  }
  { inv STEP0. inv LOCAL; eauto.
    { inv LOCAL0; ss; eauto. }
    { inv LOCAL0; ss; eauto.
      hexploit no_concrete_promise_concrete_decrease_write; eauto.
      { inv MSG; ss. }
      i. des. esplits; eauto.
    }
    { inv LOCAL1; ss; eauto. inv LOCAL2; ss; eauto.
      hexploit no_concrete_promise_concrete_decrease_write; eauto.
      { inv MSG; ss. }
      i. des. esplits; eauto.
    }
    { inv LOCAL0; ss; eauto. }
    { inv LOCAL0; ss; eauto. }
    { inv LOCAL0; ss; eauto.
      hexploit no_concrete_promise_concrete_decrease_write_na; eauto.
      { inv MSG; ss. }
      i. des. esplits; eauto.
    }
  }
Qed.

Lemma write_become_unchangable prom0 mem0 loc from to msg prom1 mem1 kind
      (WRITE: Memory.write prom0 mem0 loc from to msg prom1 mem1 kind)
      (NRESERVE: msg <> Message.reserve)
  :
    unchangable mem1 prom1 loc to from msg.
Proof.
  inv WRITE. eapply Memory.remove_get0 in REMOVE. des.
  eapply Memory.promise_get0 in PROMISE.
  { des. econs; eauto. }
  { inv PROMISE; ss. }
Qed.

Lemma write_na_become_unchangable prom0 mem0 loc from to val prom1 mem1 kind ts msgs kinds
      (WRITE: Memory.write_na ts prom0 mem0 loc from to val prom1 mem1 msgs kinds kind)
  :
    (<<EXACT: unchangable mem1 prom1 loc to from (Message.concrete val None)>>) /\
    (<<FORALL: List.Forall (fun '(from, to, msg) => unchangable mem1 prom1 loc to from msg) msgs>>).
Proof.
  induction WRITE.
  { splits; ss. eapply write_become_unchangable; eauto; ss. }
  { des. splits; auto. econs; auto.
    eapply unchangable_write_na; eauto.
    eapply write_become_unchangable; eauto. unguard. des; clarify.
  }
Qed.

Lemma writed_unchangable lang (th0 th1: Thread.t lang) tr lc we ws loc ts
      (STEPS: Trace.steps tr th0 th1)
      (IN: List.In (lc, we) tr)
      (WRITING: writing_locs we = Some ws)
      (WIN: List.In (loc, ts) ws)
  :
    exists from msg,
      (<<UNCH: unchangable (Thread.memory th1) (Local.promises (Thread.local th1)) loc ts from msg>>).
Proof.
  ginduction STEPS; eauto; ss. i. subst. ss. des.
  { clarify. inv STEP; inv STEP0; inv LOCAL; ss; clarify.
    { inv LOCAL0. des_ifs. eapply write_become_unchangable in WRITE; ss. des; clarify.
      eapply unchangable_trace_steps_increase in STEPS; eauto. }
    { inv LOCAL2. des_ifs. eapply write_become_unchangable in WRITE; ss. des; clarify.
      eapply unchangable_trace_steps_increase in STEPS; eauto. }
    { inv LOCAL0. destruct (Ordering.le ord Ordering.relaxed); ss. inv WRITING.
      eapply write_na_become_unchangable in WRITE; eauto. ss. des.
      { inv WIN. esplits. eapply unchangable_trace_steps_increase in STEPS; eauto. }
      { eapply List.in_map_iff in WIN. des. destruct x as [[from0 to0] msg0]; ss. inv WIN.
        eapply List.Forall_forall in FORALL; eauto. ss.
        eapply unchangable_trace_steps_increase in STEPS; eauto.
      }
    }
  }
  { exploit IHSTEPS; eauto. }
Qed.



Definition pf_consistent_super_strong_promises_list lang (e0:Thread.t lang)
           (tr : Trace.t)
           (times: Loc.t -> (Time.t -> Prop))
           (pl: list (list (Loc.t * Time.t)))
  : Prop :=
  (<<COMPLETE: forall loc from to msg
                      (GET: Memory.get loc to e0.(Thread.local).(Local.promises) =
                            Some (from, msg))
                      (NRESERVE: msg <> Message.reserve),
      exists ws,
        (<<IN: List.In ws pl>>) /\
        (<<WIN: List.In (loc, to) ws>>)>>) /\
  (<<CONSISTENT: forall
      pl0 ws pl1
      (PROMISES: pl = pl0 ++ ws :: pl1)
      mem1 tm sc max
      (FUTURE: Memory.future_weak (Thread.memory e0) mem1)
      (CLOSED: Memory.closed mem1)
      (LOCAL: Local.wf (Thread.local e0) mem1)
      (MWF: memory_times_wf times mem1)
      (MAX: concrete_promise_max_timemap
              ((Thread.memory e0))
              ((Local.promises (Thread.local e0)))
              max),
      (exists ftr0 ftr1 ftr_reserve ftr_cancel e1 f we,
          (<<STEPS: Trace.steps (ftr0 ++ ftr_reserve) (Thread.mk _ (Thread.state e0) (Thread.local e0) sc mem1) e1>>) /\
          (<<EVENTS: List.Forall (fun em => <<SAT: ((promise_free \1/ ThreadEvent.is_reserve)
                                                      /1\ no_sc
                                                      /1\ no_read_msgs (fun loc ts => ~ (covered loc ts (Local.promises (Thread.local e0)) \/ concrete_promised (Thread.memory e0) loc ts \/ Time.lt (tm loc) ts))
                                                      /1\ write_not_in (fun loc ts => (<<TS: Time.le ts (tm loc)>>) /\ (<<PROM: ~ covered loc ts (Local.promises (Thread.local e0))>>))
                                                      /1\ wf_time_evt times) (snd em)>> /\ <<TAU: ThreadEvent.get_machine_event (snd em) = MachineEvent.silent>>) (ftr0 ++ ftr_reserve) >>) /\

          (<<RESERVE: List.Forall (fun em => <<SAT: (ThreadEvent.is_reserve
                                                       /1\ wf_time_evt times
                                                       /1\ write_not_in (fun loc ts => (<<TS: Time.le ts (tm loc)>>) /\ (<<PROM: ~ covered loc ts (Local.promises (Thread.local e0))>>))) (snd em)>>) ftr_reserve>>) /\
          (<<CANCEL: List.Forall (fun em => <<SAT: (ThreadEvent.is_cancel /1\ wf_time_evt times) (snd em)>>) ftr_cancel>>) /\

          (<<EVENTSCERT: List.Forall (fun em => <<SAT: ((promise_free \1/ ThreadEvent.is_reserve)
                                                          /1\ no_sc
                                                          /1\ no_read_msgs (fun loc ts => ~ (covered loc ts (Local.promises (Thread.local e0)) \/ concrete_promised (Thread.memory e0) loc ts \/ Time.lt (tm loc) ts))
                                                          /1\ write_not_in (fun loc ts => (<<TS: Time.le ts (tm loc)>>) /\ (<<PROM: ~ covered loc ts (Local.promises (Thread.local e0))>>))
                                                          /1\ wf_time_evt times) (snd em)>> /\ <<TAU: ThreadEvent.get_machine_event (snd em) = MachineEvent.silent>>) (ftr_cancel ++ ftr1) >>) /\

          (<<CONSISTENT: pf_consistent_super_strong e1 (ftr_cancel ++ ftr1) times>>) /\

          (<<PROMCONSISTENT: Local.promise_consistent (Thread.local e1)>>) /\

          (<<MAPLT: mapping_map_lt_iff f>>) /\
          (<<MAPIDENT: forall loc ts fts
                              (TS: Time.le fts (max loc))
                              (MAP: f loc ts fts),
              ts = fts>>) /\
          (<<BOUND: forall loc ts fts (TS: Time.lt (max loc) fts) (MAP: f loc ts fts),
              Time.lt (max loc) ts /\ Time.le (tm loc) fts>>) /\
          (<<TRACE: List.Forall2 (fun em fem => tevent_map_weak f (snd fem) (snd em)) tr (ftr0 ++ ftr1)>>) /\
          (<<GOOD: good_future tm mem1 (Thread.memory e1)>>) /\
          (<<SC: (Thread.sc e1) = sc>>) /\

          (<<FINAL: final_event_trace we (ftr0 ++ ftr_reserve)>>) /\
          (<<ISWRITE: __guard__(exists loc to val, relaxed_writing_event loc to val we)>>) /\
          (<<WRITING: forall loc to (WIN: List.In (loc, to) ws), exists val, relaxed_writing_event loc to val we>>) /\
          (<<SOUND: forall loc0 from0 to0 msg0
                           (GET: Memory.get loc0 to0 (Local.promises (Thread.local e1)) = Some (from0, msg0))
                           (NRESERVE: msg0 <> Message.reserve),
              exists from0' msg0',
                (<<GET: Memory.get loc0 to0 (Local.promises (Thread.local e0)) = Some (from0', msg0')>>) /\
                (<<MSG: Message.le msg0 msg0'>>)>>) /\
          (<<WRITTEN: forall loc0 to0 ws0
                             (IN: List.In ws0 (pl0 ++ [ws]))
                             (WIN: List.In (loc0, to0) ws0),
              Memory.get loc0 to0 (Local.promises (Thread.local e1)) = None>>))>>)
.


Lemma promise_writing_event_writing_locs loc from to msg te
      (WRITE: promise_writing_event loc from to msg te)
  :
    exists ws,
      (<<WRITE: writing_locs te = Some ws>>) /\
      (<<WIN: List.In (loc, to) ws>>).
Proof.
  inv WRITE.
  { ss. des_ifs. esplits; eauto. ss. auto. }
  { ss. des_ifs. esplits; eauto. ss. auto. }
  { ss. des_ifs. esplits; eauto. ss. auto. }
  { ss. des_ifs. esplits; eauto. ss. right.
    eapply List.in_map with (f:= (fun '(_, to, _) => (loc, to))) in IN. ss.
  }
Qed.

Lemma tevent_map_weak_writing_locs f fe e
      (EVENT: tevent_map_weak f fe e)
  :
    option_rel
      (List.Forall2 (fun '(loc0, to0) '(loc1, to1) => loc0 = loc1 /\ f loc0 to1 to0))
      (writing_locs fe) (writing_locs e).
Proof.
  inv EVENT; ss.
  { des_ifs. ss. econs; eauto. }
  { des_ifs. ss. econs; eauto.
    induction MSGS; ss. econs; eauto.
    destruct x as [[from0 to0] msg0], y as [[from1 to1] msg1]; ss.
    des. splits; eauto.
  }
  { des_ifs. ss. econs; eauto. }
Qed.

Lemma writing_locs_relaxed_writing
      e loc ts ws
      (WRITE: writing_locs e = Some ws)
      (IN: List.In (loc, ts) ws)
  :
    exists msg,
      (<<WRITE: relaxed_writing_event loc ts msg e>>).
Proof.
  i. unfold writing_locs in WRITE. des_ifs; ss; des; clarify.
  { esplits.
    { econs; eauto. refl. }
  }
  { esplits.
    { econs 3; eauto. refl. }
  }
  { eapply List.in_map_iff in IN. des.
    destruct x as [[from1 to1] msg1]. clarify. esplits.
    { econs 4; eauto. refl. }
  }
  { esplits.
    { econs; eauto. refl. }
  }
  Unshelve. try exact None.
Qed.

Lemma pf_consistent_super_strong_promises_list_exists lang (e0: Thread.t lang)
      (tr : Trace.t)
      (times: Loc.t -> (Time.t -> Prop))
      (CONSISTENT: pf_consistent_super_strong e0 tr times)
      (CLOSED: Memory.closed (Thread.memory e0))
      (LOCAL: Local.wf (Thread.local e0) (Thread.memory e0))
      (DIVERGE: forall loc n, times loc (incr_time_seq n))
  :
    exists pl,
      (<<PROMISES: pf_consistent_super_strong_promises_list e0 tr times pl>>)
.
Proof.
  assert (exists dom,
             (<<SOUND: forall loc to
                              (IN: List.In (loc, to) dom),
                 exists from msg,
                   (<<GET: Memory.get loc to (Local.promises (Thread.local e0)) = Some (from, msg)>>) /\
                   (<<NRESERVE: msg <> Message.reserve>>)>>) /\
             (<<COMPLETE: forall loc from to msg
                                 (GET: Memory.get loc to (Local.promises (Thread.local e0)) = Some (from, msg))
                                 (NRESERVE: msg <> Message.reserve),
                 List.In (loc, to) dom>>)).
  { inv LOCAL. inv FINITE.
    hexploit (list_filter_exists
                (fun (locto: Loc.t * Time.t) =>
                   let (loc, to) := locto in
                   exists from msg,
                     Memory.get loc to (Local.promises (Thread.local e0)) = Some (from, msg) /\ msg <> Message.reserve) x).
    { i. des. exists l'. splits.
      { i. eapply COMPLETE in IN. des. esplits; eauto. }
      { i. eapply COMPLETE. esplits; eauto. }
    }
  }
  des.
  set (pl := map_somes (fun lce => writing_locs_prom (Local.promises (Thread.local e0)) (snd lce)) tr).
  destruct (classic (exists loc ts,
                        (<<IN: List.In (loc, ts) dom>>) /\
                        (<<NIN: forall ws (IN: List.In ws pl),
                            ~ List.In (loc, ts) ws>>))) as [EXIST|ALL].
  { exists [dom]. repeat red. splits.
    { ii. eapply COMPLETE in GET; eauto. esplits; eauto. ss. auto. }
    ii. exploit CONSISTENT; eauto. i. des. exfalso.
    eapply SOUND in IN. des.
    exploit WRITES; eauto. i. des.
    eapply list_Forall2_in in IN; eauto. des. destruct a. ss.
    eapply promise_writing_event_writing_locs in WRITING. des.
    pose proof (tevent_map_weak_writing_locs SAT) as WLOCS.
    rewrite WRITE in WLOCS. destruct (writing_locs t0) eqn:EQ; ss.
    eapply NIN.
    { eapply map_somes_in.
      { eauto. }
      { ss. unfold writing_locs_prom. rewrite EQ. eauto. }
    }
    eapply List.filter_In. split.
    { eapply list_Forall2_in2 in WLOCS; eauto. des.
      destruct b. des; subst. eapply MAPIDENT in SAT1; eauto.
      { subst. auto. }
      { eapply MAX in GET; eauto. }
    }
    { unfold check_in_promise. rewrite GET. destruct msg; ss. }
  }
  exists pl. split.
  { ii. eapply COMPLETE in GET; auto. eapply NNPP. ii.
    eapply ALL. esplits; eauto. }
  ii. exploit (@CONSISTENT mem1 tm sc max); eauto.
  hexploit map_somes_split_inv_one; try apply PROMISES. i. des. subst.
  dup TRACE.
  eapply List.Forall2_app_inv_l in TRACE. des. subst.
  dup TRACE. eapply List.Forall2_app_inv_l in TRACE. des. subst.
  inv TRACE3. inv H3. destruct y, a. ss.
  assert (TO: forall loc to (WIN: List.In (loc, to) ws),
             forall fto (MAP: f loc to fto), to = fto).
  { i. destruct (Time.le_lt_dec fto (max loc)).
    { eapply MAPIDENT; eauto. }
    dup l. eapply BOUND in l; eauto. des.
    exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
    { eapply l. }
    unfold writing_locs_prom in MAP1. des_ifs.
    eapply List.filter_In in WIN. des.
    unfold check_in_promise in WIN0. des_ifs.
    { eapply MAX in Heq0. auto. }
    { eapply MAX in Heq0. auto. }
  }
  assert (WRITING: forall loc to (WIN: List.In (loc, to) ws),
             exists val0,
               (<<WRITING: relaxed_writing_event loc to val0 t0>>)).
  { i. pose proof (TO _ _ WIN) as TO0.
    unfold writing_locs_prom in MAP1. des_ifs.
    eapply List.filter_In in WIN. des.
    pose proof (tevent_map_weak_writing_locs H1) as WLOCS.
    rewrite Heq in WLOCS. destruct (writing_locs t0) eqn:EQ; ss.
    eapply list_Forall2_in in WLOCS; eauto. des. destruct a as [loc1 to1].
    des. subst. eapply TO0 in SAT0. subst.
    eapply writing_locs_relaxed_writing; eauto.
  }
  des.
  hexploit SPLIT; eauto.
  { clear - WRITING CANCELNORMAL MAP1 H1.
    erewrite <- List.app_assoc in CANCELNORMAL.
    eapply cancel_normal_normals_after_normal; eauto.
    inv MAP1; inv H1; ss. } i. des.
  eexists (l1'0 ++ [(t, t0)]), l2', ftr_reserve, ftr_cancel. esplits; eauto.
  { eapply Forall_app.
    { eapply Forall_app_inv in EVENTS. des.
      eapply List.Forall_impl; eauto. i. ss. des. splits; auto. }
    { eapply List.Forall_impl; eauto. i. ss. des. destruct a. ss. splits; auto.
      { destruct t4; ss. }
      { destruct t4; ss. }
      { destruct t4; ss. }
    }
  }
  { eapply Forall_app.
    { eapply List.Forall_impl; eauto. i. ss. des. destruct a. ss. splits; auto.
      { destruct t4; ss. destruct kind; ss; des_ifs. auto. }
      { destruct t4; ss. }
      { destruct t4; ss. }
      { destruct t4; ss. des_ifs. }
      { destruct t4; ss. }
    }
    { eapply Forall_app_inv in EVENTS. des.
      eapply List.Forall_impl; eauto. i. ss. des. splits; auto. }
  }
  { destruct e2. eapply no_sc_any_sc_traced in STEPS0; ss.
    { des. exploit Trace.steps_future; try apply STEPS1; eauto; ss.
      { instantiate (1:=TimeMap.bot). ss.
        eapply Memory.closed_timemap_bot; eauto. eapply CLOSED0. }
      i. des. hexploit pf_consistent_super_strong_same_sc.
      { eapply pf_consistent_super_strong_not_easy; try apply CONSISTENT0; eauto.
        { ss. eapply memory_times_wf_traced in STEPS1; eauto. eapply Forall_app.
          { eapply Forall_app_inv in EVENTS. des. eapply List.Forall_impl; eauto.
            i. ss. des; auto. }
          { eapply List.Forall_impl; eauto. i. ss. des; auto. }
        }
      }
      i. eauto. }
    { eapply Forall_app.
      { eapply Forall_app_inv in EVENTS. des. eapply List.Forall_impl; eauto.
        i. ss. des; auto. }
      { eapply List.Forall_impl; eauto. i. ss. des; auto.
        destruct a. ss. destruct t4; ss. }
    }
  }
  { erewrite <- List.app_assoc. eapply final_event_trace_post.
    econs. eapply List.Forall_impl; eauto. i. ss.
    des. destruct a. unfold ThreadEvent.is_reserve in *. des_ifs. }
  { clear - MAP1 H1. unfold writing_locs_prom in MAP1. des_ifs. inv H1; ss.
    { des_ifs. red. esplits; econs; eauto. refl. }
    { des_ifs. red. esplits; econs; eauto. refl. }
    { des_ifs. red. esplits; econs; eauto. refl. }
  }
  { i. eapply no_concrete_promise_concrete_decrease_steps in STEPS0; eauto.
    eapply Forall_app.
    { eapply Forall_app_inv in EVENTS. des.
      eapply List.Forall_impl; eauto. i. ss. des. splits; auto. }
    { eapply List.Forall_impl; eauto. i. ss. des. destruct a. ss. splits; auto. }
  }
  { i. assert (WRITED: exists flc fwe ws,
                  (<<IN: List.In (flc, fwe) (l0 ++ [(t1, t2)])>>) /\
                  (<<WRITING: writing_locs_prom (Local.promises (Thread.local e0)) fwe = Some ws>>) /\
                  (<<WIN: List.In (loc0, to0) ws>>)).
    { apply List.in_app_or in IN. des.
      { eapply map_somes_in_rev in IN. des. destruct a. ss. esplits; eauto.
        eapply List.in_or_app; eauto. }
      { inv IN; clarify. esplits; eauto.
        eapply List.in_or_app; ss; eauto. }
    } des.
    assert (TO0: forall fto (MAP: f loc0 to0 fto), to0 = fto).
    { i. destruct (Time.le_lt_dec fto (max loc0)).
      { eapply MAPIDENT; eauto. }
      dup l. eapply BOUND in l; eauto. des.
      exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
      { eapply l. }
      clear - WRITING0 MAX WIN0.
      unfold writing_locs_prom in WRITING0. des_ifs.
      eapply List.filter_In in WIN0. des.
      unfold check_in_promise in WIN1. des_ifs.
      { eapply MAX in Heq0. auto. }
      { eapply MAX in Heq0. auto. }
    }
    assert (WRITED: exists lc we ws,
               (<<IN: List.In (lc, we) (l1'0 ++ [(t, t0)])>>) /\
               (<<WRITING: writing_locs we = Some ws>>) /\
               (<<WIN: List.In (loc0, to0) ws>>)).
    { eapply list_Forall2_in2 in IN0; eauto. des. destruct b.
      ss. unfold writing_locs_prom in WRITING0. des_ifs.
      eapply List.filter_In in WIN0. des.
      pose proof (tevent_map_weak_writing_locs SAT) as WLOCS.
      rewrite Heq in WLOCS.
      destruct (writing_locs t4) eqn:EQ; ss. esplits; eauto.
      eapply list_Forall2_in in WLOCS; eauto.
      des. destruct a as [loc1 to1]. des; subst.
      hexploit TO0; eauto. i. subst. auto.
    }
    des. eapply writed_unchangable in STEPS0; cycle 1.
    { eapply List.in_or_app. left. eauto. }
    { eauto. }
    { eauto. }
    { des. inv UNCH. auto. }
  }
  Unshelve. all: eauto. all: try exact None.
Qed.
