Require Import RelationClasses.
Require Import List.

From Paco Require Import paco.
From sflib Require Import sflib.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import Language.
From PromisingLib Require Import Loc.
Require Import Time.
Require Import Event.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import MemoryFacts.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.
Require Import Progress.
Require Import Behavior.
Require Import Cover.
Require Import PromiseConsistent.
Require Import Pred.
Require Import Trace.
Require Import JoinedView.
Require Import Single.
Require Import Shorter.

Require Import MemoryProps.
Require Import OrderedTimes.
Require SimMemory.

Require Import LocalPF.
Require Import LocalPFThread.
Require Import TimeTraced.
Require Import PFConsistentStrong.
Require Import Mapping.
Require Import GoodFuture.
Require Import CapMap.
Require Import CapFlex.
Require Import Pred.

Require Import LocalPFSim.
Require Import CapMapTime.
Require Import LocalPFThreadTime.

Set Implicit Arguments.

Section RECOVER.

  Variable L: Loc.t -> bool.
  Variable times: Loc.t -> Time.t -> Prop.
  Hypothesis WO: forall loc, well_ordered (times loc).
  Hypothesis INCR: forall nat loc, times loc (incr_time_seq nat).

  Inductive sim_thread
            (views: Loc.t -> Time.t -> list View.t)
            (prom_self prom_others: Loc.t -> Time.t -> Prop)
            (extra_self extra_others: Loc.t -> Time.t -> Time.t -> Prop):
    forall lang (th_src th_mid th_tgt: Thread.t lang), Prop :=
  | sim_thread_intro
      lang st lc_src lc_mid lc_tgt
      mem_src mem_mid mem_tgt sc_src sc_tgt
      (LOCALPF: sim_local L times prom_self extra_self lc_src lc_mid)
      (LOCALJOIN: JSim.sim_local views lc_mid lc_tgt)
      (MEMPF: sim_memory L times (prom_others \\2// prom_self) (extra_others \\3// extra_self) mem_src mem_mid)
      (MEMJOIN: SimMemory.sim_memory mem_mid mem_tgt)
      (SC: TimeMap.le sc_src sc_tgt)
    :
      sim_thread
        views prom_self prom_others extra_self extra_others
        (Thread.mk lang st lc_src sc_src mem_src)
        (Thread.mk lang st lc_mid sc_src mem_mid)
        (Thread.mk lang st lc_tgt sc_tgt mem_tgt)
  .
  Hint Constructors sim_thread.

  Inductive sim_thread_strong
            (views: Loc.t -> Time.t -> list View.t)
            (prom_self prom_others: Loc.t -> Time.t -> Prop)
            (extra_self extra_others: Loc.t -> Time.t -> Time.t -> Prop):
    forall lang (th_src th_mid th_tgt: Thread.t lang), Prop :=
  | sim_thread_strong_intro
      lang st lc_src lc_mid lc_tgt
      mem_src mem_mid mem_tgt sc_src sc_tgt
      (LOCALPF: sim_local_strong L times prom_self extra_self (extra_others \\3// extra_self) lc_src lc_mid)
      (LOCALJOIN: JSim.sim_local views lc_mid lc_tgt)
      (MEMPF: sim_memory L times (prom_others \\2// prom_self) (extra_others \\3// extra_self) mem_src mem_mid)
      (MEMJOIN: SimMemory.sim_memory mem_mid mem_tgt)
      (SC: TimeMap.le sc_src sc_tgt)
    :
      sim_thread_strong
        views prom_self prom_others extra_self extra_others
        (Thread.mk lang st lc_src sc_src mem_src)
        (Thread.mk lang st lc_mid sc_src mem_mid)
        (Thread.mk lang st lc_tgt sc_tgt mem_tgt)
  .
  Hint Constructors sim_thread_strong.

  Lemma sim_thread_strong_sim_thread
    :
      sim_thread_strong <9= sim_thread.
  Proof.
    ii. dep_inv PR. econs; eauto.
    eapply sim_local_strong_sim_local; eauto.
  Qed.

  Lemma sim_thread_jsim_thread
        views prom_self prom_others extra_self extra_others
        lang th_src th_mid th_tgt
        (THREAD: @sim_thread
                   views prom_self prom_others extra_self extra_others
                   lang th_src th_mid th_tgt)
    :
      JSim.sim_thread views th_mid th_tgt.
  Proof.
    dep_inv THREAD.
  Qed.

  Lemma sim_thread_step_silent
        views0 prom_self0 prom_others extra_self0 extra_others
        lang th_src0 th_mid0 th_tgt0 th_tgt1 pf_tgt e_tgt
        (STEPTGT: Thread.step pf_tgt e_tgt th_tgt0 th_tgt1)
        (THREAD: @sim_thread
                   views0 prom_self0 prom_others extra_self0 extra_others
                   lang th_src0 th_mid0 th_tgt0)
        (WFTIME: wf_time_evt times e_tgt)
        (NOREAD: no_read_msgs prom_others e_tgt)
        (EVENT: ThreadEvent.get_machine_event e_tgt = MachineEvent.silent)

        (SCSRC: Memory.closed_timemap th_src0.(Thread.sc) th_src0.(Thread.memory))
        (SCMID: Memory.closed_timemap th_mid0.(Thread.sc) th_mid0.(Thread.memory))
        (SCTGT: Memory.closed_timemap th_tgt0.(Thread.sc) th_tgt0.(Thread.memory))
        (MEMSRC: Memory.closed th_src0.(Thread.memory))
        (MEMMID: Memory.closed th_mid0.(Thread.memory))
        (MEMTGT: Memory.closed th_tgt0.(Thread.memory))
        (LOCALSRC: Local.wf th_src0.(Thread.local) th_src0.(Thread.memory))
        (LOCALMID: Local.wf th_mid0.(Thread.local) th_mid0.(Thread.memory))
        (LOCALTGT: Local.wf th_tgt0.(Thread.local) th_tgt0.(Thread.memory))

        (MEMWF: memory_times_wf times th_mid0.(Thread.memory))
        (MEMWFTGT: memory_times_wf times th_tgt0.(Thread.memory))
        (CONSISTENT: Local.promise_consistent th_tgt1.(Thread.local))

        (EXCLUSIVE: forall loc ts (OTHER: prom_others loc ts),
            exists from msg, <<UNCH: unchangable th_src0.(Thread.memory) th_src0.(Thread.local).(Local.promises) loc ts from msg>>)
        (EXCLUSIVEEXTRA: forall loc ts from (OTHER: extra_others loc ts from),
            (<<UNCH: unchangable th_src0.(Thread.memory) th_src0.(Thread.local).(Local.promises) loc ts from Message.reserve>>))
        (JOINED: forall loc ts, List.Forall (fun vw => semi_closed_view vw th_src0.(Thread.memory) loc ts) (views0 loc ts))

        (REL: joined_released
                views0 th_mid0.(Thread.local).(Local.promises) th_mid0.(Thread.local).(Local.tview).(TView.rel))
        (JOINEDMEM: joined_memory views0 th_mid0.(Thread.memory))
        (VIEWS: wf_views views0)
    :
      exists th_mid1 th_src1 views1 prom_self1 extra_self1 pf_mid e_mid tr,
        (<<STEPMID: JThread.step pf_mid e_mid th_mid0 th_mid1 views0 views1>>) /\
        (<<STEPSRC: Trace.steps tr th_src0 th_src1>>) /\
        (<<THREAD: sim_thread_strong
                     views1 prom_self1 prom_others extra_self1 extra_others
                     th_src1 th_mid1 th_tgt1>>) /\
        (<<EVENTJOIN: JSim.sim_event e_mid e_tgt>>) /\
        (<<JOINED: forall loc ts, List.Forall (fun vw => semi_closed_view vw th_src1.(Thread.memory) loc ts) (views1 loc ts)>>) /\
        (<<MEMWF: memory_times_wf times th_mid1.(Thread.memory)>>) /\
        (<<MEMWFTGT: memory_times_wf times th_tgt1.(Thread.memory)>>) /\
        (<<SILENT: List.Forall (fun lce => ThreadEvent.get_machine_event (snd lce) = MachineEvent.silent) tr>>)
  .
  Proof.
    hexploit sim_thread_jsim_thread; eauto. intros JTHREAD.
    exploit JSim.sim_thread_step; eauto. i. des.
    dep_inv THREAD. destruct th1_src. ss.
    hexploit sim_thread_step_silent; try apply STEP; eauto.
    { inv EVENT0; ss. }
    { inv STEP. ss. hexploit step_memory_times_wf; eauto. inv EVENT0; ss. }
    { dep_inv SIM. eapply JSim.sim_local_promise_consistent; eauto. }
    { inv EVENT0; ss. }
    i. des. dep_inv SIM. esplits; eauto.
    { inv STEP. ss. hexploit step_memory_times_wf; eauto. inv EVENT0; ss. }
    { hexploit step_memory_times_wf; try apply STEPTGT; eauto. }
  Qed.

  Lemma sim_thread_steps_silent
        views0 prom_self0 prom_others extra_self0 extra_others
        lang th_src0 th_mid0 th_tgt0 th_tgt1 tr_tgt
        (STEPTGT: Trace.steps tr_tgt th_tgt0 th_tgt1)
        (THREAD: @sim_thread
                   views0 prom_self0 prom_others extra_self0 extra_others
                   lang th_src0 th_mid0 th_tgt0)

        (EVENTS: List.Forall (fun the => <<SAT: (wf_time_evt times /1\ no_read_msgs prom_others) (snd the)>> /\ <<TAU: ThreadEvent.get_machine_event (snd the) = MachineEvent.silent>>) tr_tgt)

        (SCSRC: Memory.closed_timemap th_src0.(Thread.sc) th_src0.(Thread.memory))
        (SCMID: Memory.closed_timemap th_mid0.(Thread.sc) th_mid0.(Thread.memory))
        (SCTGT: Memory.closed_timemap th_tgt0.(Thread.sc) th_tgt0.(Thread.memory))
        (MEMSRC: Memory.closed th_src0.(Thread.memory))
        (MEMMID: Memory.closed th_mid0.(Thread.memory))
        (MEMTGT: Memory.closed th_tgt0.(Thread.memory))
        (LOCALSRC: Local.wf th_src0.(Thread.local) th_src0.(Thread.memory))
        (LOCALMID: Local.wf th_mid0.(Thread.local) th_mid0.(Thread.memory))
        (LOCALTGT: Local.wf th_tgt0.(Thread.local) th_tgt0.(Thread.memory))

        (MEMWF: memory_times_wf times th_mid0.(Thread.memory))
        (MEMWFTGT: memory_times_wf times th_tgt0.(Thread.memory))
        (CONSISTENT: Local.promise_consistent th_tgt1.(Thread.local))

        (EXCLUSIVE: forall loc ts (OTHER: prom_others loc ts),
            exists from msg, <<UNCH: unchangable th_src0.(Thread.memory) th_src0.(Thread.local).(Local.promises) loc ts from msg>>)
        (EXCLUSIVEEXTRA: forall loc ts from (OTHER: extra_others loc ts from),
            (<<UNCH: unchangable th_src0.(Thread.memory) th_src0.(Thread.local).(Local.promises) loc ts from Message.reserve>>))
        (JOINED: forall loc ts, List.Forall (fun vw => semi_closed_view vw th_src0.(Thread.memory) loc ts) (views0 loc ts))

        (REL: joined_released
                views0 th_mid0.(Thread.local).(Local.promises) th_mid0.(Thread.local).(Local.tview).(TView.rel))
        (JOINEDMEM: joined_memory views0 th_mid0.(Thread.memory))
        (VIEWS: wf_views views0)
    :
      exists th_mid1 th_src1 views1 prom_self1 extra_self1 tr_src,
        (<<STEPMID: JThread.rtc_tau th_mid0 th_mid1 views0 views1>>) /\
        (<<STEPSRC: Trace.steps tr_src th_src0 th_src1>>) /\
        (<<THREAD: sim_thread_strong
                     views1 prom_self1 prom_others extra_self1 extra_others
                     th_src1 th_mid1 th_tgt1>>) /\
        (<<JOINED: forall loc ts, List.Forall (fun vw => semi_closed_view vw th_src1.(Thread.memory) loc ts) (views1 loc ts)>>) /\
        (<<MEMWF: memory_times_wf times th_mid1.(Thread.memory)>>) /\
        (<<MEMWFTGT: memory_times_wf times th_tgt1.(Thread.memory)>>) /\
        (<<SILENT: List.Forall (fun lce => ThreadEvent.get_machine_event (snd lce) = MachineEvent.silent) tr_src>>)
  .
  Proof.
    ginduction STEPTGT.
    { i. dep_inv THREAD. inv LOCALPF. exploit sim_promise_weak_strengthen; eauto.
      { eapply LOCALMID. }
      { eapply LOCALSRC. }
      { eapply LOCALSRC. }
      { eapply LOCALSRC. }
      i. des. exploit reserve_future_memory_steps; eauto. i. des. ss. esplits; eauto.
      { econs; eauto. econs; eauto. }
      { i. ss. eapply List.Forall_impl; eauto.
        ii. ss. eapply semi_closed_view_future; eauto.
        eapply Memory.future_future_weak. eapply reserve_future_future; eauto. }
      { eapply reserving_trace_silent; eauto. }
    }
    i. subst. inv EVENTS. ss. des.
    hexploit Thread.step_future; try apply STEP; eauto. i. des.
    hexploit sim_thread_step_silent; eauto.
    { eapply Trace.steps_promise_consistent; eauto. } i. des.
    hexploit JThread.step_future; try apply STEPMID; eauto. i. des.
    hexploit Trace.steps_future; try apply STEPSRC; eauto. i. des.
    eapply sim_thread_strong_sim_thread in THREAD0. exploit IHSTEPTGT; eauto.
    { i. eapply EXCLUSIVE in OTHER. des.
      eapply unchangable_trace_steps_increase in UNCH; eauto. }
    { i. eapply EXCLUSIVEEXTRA in OTHER. des.
      eapply unchangable_trace_steps_increase in OTHER; eauto. }
    i. des. esplits; try apply THREAD1; try by assumption.
    { econs; eauto. inv EVENTJOIN; ss. }
    { eapply Trace.steps_trans; eauto. }
    { eapply Forall_app; eauto. }
  Qed.

  Lemma sim_thread_consistent
        views prom_self prom_others extra_self extra_others
        lang th_src th_mid th_tgt
        (CONSISTENTTGT: past_consistent times th_src.(Thread.memory) th_tgt)
        (THREAD: @sim_thread_strong
                   views prom_self prom_others extra_self extra_others
                   lang th_src th_mid th_tgt)
        (SCSRC: Memory.closed_timemap th_src.(Thread.sc) th_src.(Thread.memory))
        (SCMID: Memory.closed_timemap th_mid.(Thread.sc) th_mid.(Thread.memory))
        (SCTGT: Memory.closed_timemap th_tgt.(Thread.sc) th_tgt.(Thread.memory))
        (MEMSRC: Memory.closed th_src.(Thread.memory))
        (MEMMID: Memory.closed th_mid.(Thread.memory))
        (MEMTGT: Memory.closed th_tgt.(Thread.memory))
        (LOCALSRC: Local.wf th_src.(Thread.local) th_src.(Thread.memory))
        (LOCALMID: Local.wf th_mid.(Thread.local) th_mid.(Thread.memory))
        (LOCALTGT: Local.wf th_tgt.(Thread.local) th_tgt.(Thread.memory))
        (MEMWF: memory_times_wf times th_mid.(Thread.memory))
        (MEMWFTGT: memory_times_wf times th_tgt.(Thread.memory))
        (EXCLUSIVE: forall loc ts (OTHER: prom_others loc ts),
            exists from msg, <<UNCH: unchangable th_src.(Thread.memory) th_src.(Thread.local).(Local.promises) loc ts from msg>>)
        (EXCLUSIVEEXTRA: forall loc ts from (OTHER: extra_others loc ts from),
            (<<UNCH: unchangable th_src.(Thread.memory) th_src.(Thread.local).(Local.promises) loc ts from Message.reserve>>))
        (EXCLUSIVE2: forall loc to (OTHER: prom_others loc to), ~ covered loc to th_mid.(Thread.local).(Local.promises))
        (JOINED: forall loc ts, List.Forall (fun vw => semi_closed_view vw th_src.(Thread.memory) loc ts) (views loc ts))

        (REL: joined_released
                views th_mid.(Thread.local).(Local.promises) th_mid.(Thread.local).(Local.tview).(TView.rel))
        (JOINEDMEM: joined_memory views th_mid.(Thread.memory))
        (VIEWS: wf_views views)
    :
      Thread.consistent th_src.
  Proof.
    dup THREAD. dep_inv THREAD.
    hexploit sim_memory_strong_exists; eauto. i. des.
    assert (MEMSRCSTRONG: Memory.closed mem_src').
    { eapply sim_memory_same_closed; eauto.
      eapply sim_memory_strong_sim_memory; eauto. }

    hexploit (later_timemap_exists
                times
                INCR
                (TimeMap.join
                   (Memory.max_timemap mem_src')
                   (TimeMap.join
                      (Memory.max_timemap mem_src)
                      (TimeMap.join
                         (Memory.max_timemap mem_mid)
                         (Memory.max_timemap mem_tgt))))). intros [tm ?]. des.

    assert (TM0': forall loc,
               Time.lt (Memory.max_ts loc mem_src') (tm loc)).
    { i. eapply TimeFacts.le_lt_lt; eauto.
      repeat ((try eapply Time.join_l); ((etrans; cycle 1); [eapply Time.join_r|])). }
    assert (TM0: forall loc,
               Time.lt (Memory.max_ts loc mem_src) (tm loc)).
    { i. eapply TimeFacts.le_lt_lt; eauto.
      repeat ((try eapply Time.join_l); ((etrans; cycle 1); [eapply Time.join_r|])). }
    assert (TM1: forall loc,
               Time.lt (Memory.max_ts loc mem_mid) (tm loc)).
    { i. eapply TimeFacts.le_lt_lt; eauto.
      repeat ((try eapply Time.join_l); ((etrans; cycle 1); [eapply Time.join_r|])). }
    assert (TM2: forall loc,
               Time.lt (Memory.max_ts loc mem_tgt) (tm loc)).
    { i. eapply TimeFacts.le_lt_lt; eauto.
      repeat ((try eapply Time.join_l); ((etrans; cycle 1); [eapply Time.join_r|])). refl. }

    hexploit (@cap_flex_exists mem_src' tm); eauto.
    intros [cap_src' CAPSRCSTRONG].
    hexploit (@cap_flex_exists mem_mid tm); eauto.
    intros [cap_mid CAPMID].
    hexploit (@cap_flex_exists mem_tgt tm); eauto.
    intros [cap_tgt CAPTGT].
    hexploit (@Memory.max_concrete_timemap_exists mem_src); try apply MEMSRC.
    intros [max MAX].

    hexploit (@Memory.cap_exists mem_src); eauto. intros [mem1 CAP]. des.
    hexploit (@Memory.max_concrete_timemap_exists mem1); eauto.
    { eapply Memory.cap_closed in MEMSRC; eauto. eapply MEMSRC. } intros [sc1 SC_MAX].
    assert (SCSRC0: Memory.closed_timemap sc1 mem_src).
    { eapply concrete_promised_le_closed_timemap.
      { eapply concrete_messages_le_concrete_promised_le.
        eapply cap_flex_concrete_messages_le.
        { eapply cap_cap_flex; eauto. }
        { eauto. }
        { i. ss. eapply Time.incr_spec. }
      }
      eapply Memory.max_concrete_timemap_closed; eauto.
    }
    assert (SCSRC1: Memory.closed_timemap sc1 mem_src').
    { eapply concrete_promised_le_closed_timemap; eauto.
      eapply concrete_messages_le_concrete_promised_le.
      eapply sim_memory_same_concrete_messages_le; eauto.
      eapply sim_memory_strong_sim_memory; eauto. }
    assert (SCMID0: Memory.closed_timemap sc1 mem_mid).
    { eapply concrete_promised_le_closed_timemap; try apply SCSRC0; eauto.
      eapply concrete_messages_le_concrete_promised_le.
      eapply sim_memory_concrete_messages_le; eauto. }
    exploit (@Memory.max_concrete_timemap_exists mem_tgt).
    { eapply MEMTGT. } intros [sctgt MAXTGT]. des.

    hexploit (@concrete_promise_max_timemap_exists mem_tgt (Local.promises lc_tgt)).
    { eapply MEMTGT. } intros [maxconcete MAXCONCRETE].

    exploit (CONSISTENTTGT).
    { instantiate (1:= cap_tgt). ss. eapply cap_flex_future_weak; eauto. }
    { eapply cap_flex_closed; eauto. }
    { eapply cap_flex_memory_times_wf; eauto. }
    { eapply cap_flex_wf; eauto. }
    i. des. ss.
    instantiate (1:=sctgt) in STEPS.
    instantiate (1:=Memory.max_timemap mem_src) in EVENTS.

    hexploit sim_thread_steps_silent; simpl.
    { eapply STEPS. }
    { econs.
      { eapply sim_local_strong_sim_local; eauto. }
      { eauto. }
      { eapply sim_memory_strong_cap; eauto. }
      { eapply (@cap_flex_sim_memory mem_mid mem_tgt); eauto. }
      { instantiate (1:=sc1).
        eapply Memory.max_concrete_timemap_spec.
        { instantiate (1:=mem_mid).
          exploit (@Memory.max_concrete_timemap_exists mem_mid); eauto.
          { eapply MEMMID. } i. des.
          exploit (@SimMemory.sim_memory_max_concrete_timemap mem_mid mem_tgt); eauto.
          i. subst. auto.
        }
        auto.
      }
    }
    { eapply Forall_impl; eauto. i. ss. des. splits; auto.
      eapply no_read_msgs_mon; eauto. ii. des.
      { inv LOCALJOIN. erewrite <- jsim_joined_promises_covered in H; eauto.
        eapply EXCLUSIVE2; eauto.
      }
      { inv H.  set (MEM0:=MEMPF.(sim_memory_contents) x0 x1).
        rewrite GET in *. inv MEM0; ss. eapply NPROM. left. auto.
      }
      { eapply EXCLUSIVE in PR. des. inv UNCH.
        eapply Memory.max_ts_spec in GET. des. timetac.
      }
    }
    { ss. eapply Memory.future_weak_closed_timemap.
      { eapply cap_flex_future_weak; eauto. } eauto. }
    { ss. eapply Memory.future_weak_closed_timemap.
      { eapply cap_flex_future_weak; eauto. } eauto. }
    { ss. eapply Memory.future_weak_closed_timemap.
      { eapply cap_flex_future_weak; eauto. }
      eapply Memory.max_concrete_timemap_closed; eauto. }
    { ss. eapply cap_flex_closed; eauto. }
    { ss. eapply cap_flex_closed; eauto. }
    { ss. eapply cap_flex_closed; eauto. }
    { ss. eapply cap_flex_wf; eauto.
      eapply sim_memory_strong_sim_local; eauto.
      { eapply sim_local_strong_sim_local; eauto. }
      { inv LOCALPF. ss. }
    }
    { ss. eapply cap_flex_wf; eauto. }
    { ss. eapply cap_flex_wf; eauto. }
    { ss. eapply cap_flex_memory_times_wf; cycle 1; eauto. }
    { ss. eapply cap_flex_memory_times_wf; cycle 1; eauto. }
    { destruct FINAL.
      { des. inv LOCAL. auto. }
      { des. ii. erewrite H in *. erewrite Memory.bot_get in *. ss. }
    }
    { ss. ii. exploit EXCLUSIVE; eauto. i. des. inv UNCH.
      set (CNT:=MEM.(sim_memory_strong_contents) loc ts).
      inv CNT; ss; try by (exfalso; eapply NPROM0; left; auto).
      symmetry in H0. eapply CAPSRCSTRONG in H0. esplits. econs; eauto. }
    { ss. ii. exploit EXCLUSIVEEXTRA; eauto. i. des. inv x.
      set (CNT:=MEM.(sim_memory_strong_contents) loc ts).
      exploit (MEM.(sim_memory_strong_wf) loc from ts).
      { left. auto. } i. des.
      inv CNT; ss; try by (exfalso; eapply NEXTRA; left; eauto).
      eapply UNIQUE in EXTRA. subst.
      symmetry in H0. eapply CAPSRCSTRONG in H0. esplits. econs; eauto. }
    { ss. i. eapply List.Forall_impl; eauto. i. ss.
      eapply semi_closed_view_future.
      2: { eapply cap_flex_future_weak; eauto. }
      { eapply concrete_promised_le_semi_closed_view; eauto.
        eapply concrete_messages_le_concrete_promised_le.
        eapply sim_memory_same_concrete_messages_le; eauto.
        eapply sim_memory_strong_sim_memory; eauto. }
    }
    { ss. }
    { ss. eapply joined_memory_cap_flex; eauto. }
    { ss. }

    i. des. hexploit (trace_times_list_exists tr_src). i. des.

    hexploit (@cap_flex_map_exists
                (Memory.max_timemap mem_src')
                tm
                (fun loc : Loc.t => Time.incr (Memory.max_ts loc mem_src))
                times0); auto.
    { i. erewrite (@sim_memory_same_max_ts_eq L times mem_src mem_src'); eauto.
      { apply Time.incr_spec. }
      { eapply sim_memory_strong_sim_memory; eauto. }
    } i. des.

    exploit (@Memory.max_concrete_timemap_exists mem_src').
    { eapply MEMSRCSTRONG. } i. des.
    hexploit concrete_messages_le_cap_flex_memory_map; try apply MAP.
    { eapply sim_memory_same_concrete_messages_le.
      { eapply sim_memory_strong_sim_memory; eauto. }
      { eapply MEMPF. }
    }
    { eauto. }
    { ii. ss. eapply max_concrete_ts_le_max_ts; eauto. }
    { auto. }
    { i. ss. eapply Time.incr_spec. }
    { eauto. }
    { eapply cap_cap_flex; eauto. }
    { eauto. }
    { eauto. }
    intros MEMORYMAP. destruct th_src1. ss.
    hexploit trace_steps_map; try apply MEMORYMAP.
    { eapply mapping_map_lt_map_le. eapply MAP. }
    { eapply MAP. }
    { eapply mapping_map_lt_map_eq. eapply MAP. }
    { eapply wf_time_mapped_mappable; eauto.
      i. ss. eapply MAP in IN0. eauto. }
    { eauto. }
    { ss. }
    { ss. }
    { ss. }
    { eapply cap_flex_wf; eauto.
      eapply sim_memory_strong_sim_local; eauto.
      { eapply sim_local_strong_sim_local; eauto. }
      { inv LOCALPF. ss. }
    }
    { eapply Local.cap_wf; eauto. }
    { eapply Memory.cap_closed; eauto. }
    { eapply cap_flex_closed; eauto. }
    { eapply Memory.max_concrete_timemap_closed; eauto. }
    { eapply Memory.future_weak_closed_timemap.
      { eapply cap_flex_future_weak; eauto. }
      { eauto. }
    }
    { eapply map_ident_in_memory_local; eauto.
      { ii. eapply MAP; auto.
        erewrite (@sim_memory_same_max_ts_eq L times mem_src mem_src') in TS; eauto.
        eapply sim_memory_strong_sim_memory; eauto. }
      { eapply MAP. }
    }
    { eapply mapping_map_lt_collapsable_unwritable. eapply MAP. }
    { eapply map_ident_in_memory_closed_timemap.
      { ii. eapply MAP; auto.
        erewrite (@sim_memory_same_max_ts_eq L times mem_src mem_src') in TS; eauto.
        eapply sim_memory_strong_sim_memory; eauto. }
      { eauto. }
    }
    { refl. }

    i. des.
    assert (SILENT0: List.Forall
                      (fun the =>
                         ThreadEvent.get_machine_event (snd the) = MachineEvent.silent) ftr0).
    { eapply List.Forall_forall. i.
      eapply list_Forall2_in in H; eauto. i. des.
      eapply Forall_forall in IN0; try apply SILENT. ss.
      destruct a, x. ss. inv EVENT; ss.
    }
    eapply Trace.consistent_thread_consistent.
    instantiate (1:=ftr0).

    dep_inv THREAD.
    { ii. ss. eapply Memory.cap_inj in CAP; eauto. subst.
      eapply Memory.max_concrete_timemap_inj in SC_MAX; eauto. subst.
      esplits; eauto. ss. unguard. des.
      { left. esplits. econs 2. econs; eauto. econs.
        eapply failure_step_map; eauto.
        { eapply mapping_map_lt_map_le. eapply MAP. }
        { eapply mapping_map_lt_map_eq. eapply MAP. }
        eapply sim_failure_step; cycle 1.
        { eapply sim_local_strong_sim_local; eauto. }
        eapply JSim.sim_local_failure; eauto.
      }
      { right. esplits; eauto. ss. inv LOCAL.
        cut (local.(Local.promises) = Memory.bot).
        { i. eapply bot_promises_map; eauto. erewrite <- H. eauto. }
        eapply JSim.sim_local_memory_bot in LOCALJOIN0; auto.
        inv LOCALPF0. ss.
        eapply sim_promise_bot; eauto. eapply sim_promise_strong_sim_promise; eauto.
      }
    }
  Qed.

  Inductive sim_configuration
            (views: Loc.t -> Time.t -> list View.t)
            (prom: Ident.t -> Loc.t -> Time.t -> Prop)
            (extra: Ident.t -> Loc.t -> Time.t -> Time.t -> Prop)
            (proml: Ident.t -> list (Loc.t * Time.t))
    :
      forall (c_src c_mid c_tgt: Configuration.t), Prop :=
  | sim_configuration_intro
      ths_src sc_src mem_src
      ths_mid mem_mid
      ths_tgt sc_tgt mem_tgt
      (THSPF: forall tid,
          option_rel
            (sim_statelocal L times (prom tid) (extra tid))
            (IdentMap.find tid ths_src)
            (IdentMap.find tid ths_mid))
      (THSJOIN: forall tid,
          option_rel
            (JSim.sim_statelocal views)
            (IdentMap.find tid ths_mid)
            (IdentMap.find tid ths_tgt))
      (BOT: forall tid (NONE: IdentMap.find tid ths_src = None),
          (<<PROM: forall loc ts, ~ prom tid loc ts>>) /\
          (<<EXTRA: forall loc ts from, ~ extra tid loc ts from>>))
      (MEMPF: sim_memory L times (all_promises (fun _ => True) prom) (all_extra (fun _ => True) extra) mem_src mem_mid)
      (SCPF: TimeMap.le sc_src sc_tgt)

      (JOINED: forall loc ts, List.Forall (fun vw => semi_closed_view vw mem_src loc ts) (views loc ts))
      (MEMJOIN: SimMemory.sim_memory mem_mid mem_tgt)
      (MEMWF: memory_times_wf times mem_mid)
      (MEMWFTGT: memory_times_wf times mem_tgt)
      (PAST: forall tid lang st lc
                    (GET: IdentMap.find tid ths_tgt = Some (existT _ lang st, lc)),
          (<<CONSISTENT: past_consistent times mem_src (Thread.mk lang st lc sc_tgt mem_tgt)>>) \/
          ((<<PROM: forall loc ts, ~ prom tid loc ts>>) /\
           (<<EXTRA: forall loc ts from, ~ extra tid loc ts from>>) /\
           (<<EQ: IdentMap.find tid ths_src = IdentMap.find tid ths_mid>>)))
      (PROML: forall tid loc ts (PROM: prom tid loc ts), List.In (loc, ts) (proml tid))
    :
      sim_configuration
        views prom extra proml
        (Configuration.mk ths_src sc_src mem_src)
        (Configuration.mk ths_mid sc_src mem_mid)
        (Configuration.mk ths_tgt sc_tgt mem_tgt)
  .
  Hint Constructors sim_configuration.

  Lemma non_time_time_sim_promise self extra prom_src prom_tgt
        (SIM: LocalPFThread.sim_promise L times self extra prom_src prom_tgt)
    :
      LocalPFThreadTime.sim_promise L times self extra prom_src prom_tgt.
  Proof.
    inv SIM. econs; eauto. i.
    specialize (sim_promise_contents loc ts).
    inv sim_promise_contents; econs; eauto.
  Qed.

  Lemma non_time_time_sim_configuration c_src c_mid c_tgt
        views prom extra proml
        (SIM: LocalPFSim.sim_configuration L times (fun _ => True) views prom extra proml c_src c_mid c_tgt)
    :
      sim_configuration views prom extra proml c_src c_mid c_tgt.
  Proof.
    inv SIM. econs; eauto.
    { i. clear - THSPF. specialize (THSPF tid). unfold option_rel in *. des_ifs.
      dep_inv THSPF. econs; eauto. inv LOCAL. econs.
      eapply non_time_time_sim_promise; eauto. }
    { i. exploit BOT; eauto. i. des. split; auto. }
    { i. destruct (IdentMap.find tid ths_tgt) eqn:TIDTGT.
      { destruct p as [[lang st] lc]. exploit CONSISTENT; eauto. i.
        eapply x in PROM. eauto. }
      { specialize (THSPF tid). specialize (THSJOIN tid).
        unfold option_rel in *. des_ifs. eapply BOT in Heq1.
        des. exfalso. eapply PROM0; eauto. }
    }
  Qed.

  Definition remember_first_promise_thread lang st
             prom_self extra_self lc_src lc_mid views sc
             loc to mem_src mem_mid extra_others prom_others
             (LOCAL: sim_local L times prom_self extra_self lc_src lc_mid)
             (WF: Local.wf lc_src mem_src)
             (MEMORY: sim_memory L times (prom_others \\2// prom_self) (extra_others \\3// extra_self) mem_src mem_mid)
             (FORGET: prom_self loc to)
             (FIRST: forall ts (FORGET: (prom_others \\2// prom_self) loc ts), Time.le to ts)
             (JOINEDMEM: joined_memory views mem_mid)
             (JOINED: forall loc ts, List.Forall (fun vw => semi_closed_view vw mem_src loc ts) (views loc ts))

             (EXCLUSIVE: forall loc' ts' (OTHER: prom_others loc' ts'),
                 exists from msg, <<UNCH: unchangable mem_src lc_src.(Local.promises) loc' ts' from msg>>)
             (EXCLUSIVEEXTRA: forall loc' ts' from' (OTHER: extra_others loc' ts' from'),
                 (<<UNCH: unchangable mem_src lc_src.(Local.promises) loc' ts' from' Message.reserve>>))

             (MWFSRC: Memory.closed mem_src)
             (MWFTGT: Memory.closed mem_mid)
             (WFTGT: Local.wf lc_mid mem_mid)
    :
      exists lc_src' mem_src' prom_self' extra_self' tr,
        (<<PROM: prom_self' = fun l t => prom_self l t /\ (loc, to) <> (l, t)>>) /\
        (<<STEPS: @Trace.steps lang tr (Thread.mk _ st lc_src sc mem_src) (Thread.mk _ st lc_src' sc mem_src')>>) /\
        (<<LOCAL: sim_local L times prom_self' extra_self' lc_src' lc_mid>>) /\
        (<<MEMORY: sim_memory L times (prom_others \\2// prom_self') (extra_others \\3// extra_self') mem_src' mem_mid>>) /\
        (<<SILENT: List.Forall (fun lce => ThreadEvent.get_machine_event (snd lce) = MachineEvent.silent) tr>>) /\
        (<<NNIL: tr <> []>>)
  .
  Proof.
    inv LOCAL.
    set (MEM := MEMORY.(sim_memory_contents) loc to).
    set (PROM := PROMS.(sim_promise_contents) loc to).
    inv PROM; clarify; try by (exfalso; eapply NPROM; right; eauto).
    symmetry in H0. symmetry in H.
    dup H. eapply WFTGT in H1.

    assert (MLE0: Memory.le prom_src mem_src).
    { eapply WF. }
    assert (NBOT: to <> Time.bot).
    { dup H0. eapply memory_get_ts_strong in H0. des; clarify.
      inv WF. erewrite BOT in H2. ss. }

    assert (NSELF: ~ (prom_others \\2// prom_self) loc from_src).
    { ii. dup H2. hexploit FIRST; eauto.
      i. eapply memory_get_ts_strong in H0. des; clarify. timetac.
    }

    exploit PROMS.(sim_promise_extra); eauto. i. des.
    exploit Memory.remove_exists; try apply GET. intros [prom_src1 REMOVEPROM1].
    exploit Memory.remove_exists_le; try apply REMOVEPROM1; eauto. intros [mem_src1 REMOVEMEM1].
    hexploit PreReserve.memory_remove_le_preserve; try apply MLE0; eauto. intros MLE1.
    assert (PROMISE1: Local.promise_step (Local.mk tvw prom_src) mem_src loc to to0 Message.reserve (Local.mk tvw prom_src1) mem_src1 Memory.op_kind_cancel).
    { econs; eauto. }

    exploit (@Memory.remove_exists prom_src1 loc from_src to Message.reserve).
    { eapply Memory.remove_get1 in H0; eauto. des; clarify.
      dup GET. eapply memory_get_ts_strong in GET0. des; clarify. timetac.
    } intros [prom_src2 REMOVEPROM2].
    exploit Memory.remove_exists_le; try apply REMOVEPROM2; eauto. intros [mem_src2 REMOVEMEM2].
    hexploit PreReserve.memory_remove_le_preserve; try apply MLE1; eauto. intros MLE2.
    assert (PROMISE2: Local.promise_step (Local.mk tvw prom_src1) mem_src1 loc from_src to Message.reserve (Local.mk tvw prom_src2) mem_src2 Memory.op_kind_cancel).
    { econs; eauto. }

    exploit (@Memory.add_exists mem_src2 loc from_tgt to (Message.concrete val released)).
    { ii. inv LHS. inv RHS. ss.
      erewrite Memory.remove_o in GET2; eauto.
      erewrite Memory.remove_o in GET2; eauto. des_ifs. guardH o. guardH o0.
      destruct (Time.le_lt_dec x from_src).
      { hexploit memory_get_disjoint_strong.
        { eapply GET2. }
        { eapply WF. eapply H0. }
        i. des.
        { subst. ss. destruct o; ss. }
        { ss. set (MEM0:=MEMORY.(sim_memory_contents) loc to2).
          rewrite GET2 in MEM0. inv MEM0.
          - exploit Memory.get_disjoint.
            { symmetry. eapply H5. }
            { eapply H1. }
            i. des; clarify.
            + timetac.
            + eapply x1.
              * instantiate (1:=to2). econs; ss.
                { eapply TimeFacts.le_lt_lt.
                  { eapply FROM1. } eapply TimeFacts.lt_le_lt.
                  { eapply FROM0. }
                  { eapply TO0. }
                }
                { refl. }
              * econs; ss.
                { eapply TimeFacts.lt_le_lt.
                  { eapply FROM. }
                  { eapply TO0. }
                }
                { left. auto. }
          - eapply FIRST in PROM. timetac.
          - eapply MEMORY in EXTRA. des.
            eapply FIRST in FORGET0. eapply Time.lt_strorder.
            eapply TimeFacts.lt_le_lt.
            { eapply TS2. } etrans.
            { left. eapply TS1. }
            { eauto. }
        }
        { eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
          { eapply FROM0. } etrans.
          { eapply TO. }
          { eauto. }
        }
      }
      { hexploit Memory.get_disjoint.
        { eapply GET2. }
        { eapply WF. eapply H0. }
        i. des; subst; ss.
        { destruct o; ss. }
        { eapply H2; econs; eauto. }
      }
    }
    { eapply memory_get_ts_strong in H. des; clarify. }
    { eapply WFTGT in H. eapply MWFTGT in H. des. auto. } intros [mem_src3 ADDMEM3].
    exploit Memory.add_exists_le; try apply ADDMEM3; eauto. intros [prom_src3 ADDPROM3].
    hexploit PreReserve.memory_add_le_preserve; try apply MLE2; eauto. intros MLE3.
    assert (PROMISE3': Memory.promise prom_src2 mem_src2 loc from_tgt to (Message.concrete val released) prom_src3 mem_src3 Memory.op_kind_add).
    { econs; eauto.
      - eapply MWFTGT in H1. des. auto.
      - i. clarify. erewrite Memory.remove_o in GET0; eauto. des_ifs.
        erewrite Memory.remove_o in GET0; eauto. des_ifs. ss. des; clarify.
        exploit memory_get_from_inj.
        { eapply GET0. }
        { eapply WF in GET. eapply GET. }
        i. des; clarify.
    }

    assert (PROMISE3: Local.promise_step (Local.mk tvw prom_src2) mem_src2 loc from_tgt to (Message.concrete val released) (Local.mk tvw prom_src3) mem_src3 Memory.op_kind_add).
    { econs; eauto. econs; eauto. destruct released; eauto. econs.
      eapply JOINEDMEM in H1. des.
      eapply joined_view_semi_closed in JOINED0; eauto.
      2: { eapply MWFSRC. }
      eapply semi_closed_view_add; cycle 1; eauto.
      eapply concrete_promised_le_semi_closed_view in JOINED0; eauto. ii.
      eapply concrete_promised_increase_promise; eauto.
      eapply concrete_promised_increase_promise; eauto.
    }

    destruct (classic (extra_self loc to0 to)) as [EXTRA|NEXTRA0].
    { exists (Local.mk tvw prom_src3), mem_src3,
      (fun l t => prom_self l t /\ (loc, to) <> (l, t)),
      (fun l t => if (loc_ts_eq_dec (l, t) (loc, to0)) then (fun _ => False) else (extra_self l t)).
      esplits; try eassumption.
      { auto. }
      { econs 2; [..|ss].
        { econs; eauto. econs; eauto. }
        econs 2; [..|ss].
        { econs; eauto. econs; eauto. }
        econs 2; [..|ss].
        { econs; eauto. econs; eauto. }
        econs 1.
      }
      { econs. econs.
        - i. erewrite (@Memory.add_o prom_src3); eauto.
          erewrite (@Memory.remove_o prom_src2); eauto.
          erewrite (@Memory.remove_o prom_src1); eauto. des_ifs.
          + ss. des; clarify. exfalso. eapply NEXTRA; eauto.
          + ss. des; clarify.
            set (PROM:=PROMS.(sim_promise_contents) loc to0).
            inv PROM; clarify; try by (exfalso; eapply NEXTRA0; eauto).
            econs; eauto. ii. des; ss.
          + ss. des; clarify. erewrite H. econs 2; eauto. ii. des; clarify.
          + ss. guardH o. guardH o0.
            set (PROM:=PROMS.(sim_promise_contents) loc0 ts). inv PROM; clarify.
            * econs 1; eauto. ii. des; auto.
            * econs 2; eauto. ii. des; auto.
            * econs 3; eauto. ii. des; auto.
            * econs 4; eauto. split; auto. ii. destruct o0; clarify.
            * econs 5; eauto. ii. des; ss.
        - i. des_ifs. guardH o.
          dup EXTRA0. eapply PROMS in EXTRA0. des. splits; auto.
          ii. clarify. ss.
          exploit sim_memory_extra_inj.
          { eauto. }
          { right. eapply EXTRA. }
          { right. eapply EXTRA1. }
          ii. destruct o; clarify.
        - i. des. dup SELF. eapply PROMS in SELF1. des. exists to1. split; auto.
          red. erewrite Memory.add_o; eauto.
          erewrite Memory.remove_o; eauto. erewrite Memory.remove_o; eauto. des_ifs.
          + ss. des; clarify. exfalso. eapply NSELF; eauto. right. auto.
          + ss. des; clarify.
      }
      { econs.
        - i. erewrite (@Memory.add_o mem_src3); eauto.
          erewrite (@Memory.remove_o mem_src2); eauto.
          erewrite (@Memory.remove_o mem_src1); eauto. des_ifs.
          + ss. des; clarify. exfalso. eapply NSELF; eauto. right. auto.
          + ss. des; clarify.
            set (MEM0:=MEMORY.(sim_memory_contents) loc to0). inv MEM0; ss.
            * econs 1; eauto.
              { ii. eapply NPROM. unguard. destruct H2; des; auto. }
              { ii. destruct H2; ss. eapply NEXTRA0. left. eauto. }
            * exfalso. eapply NEXTRA0. right. eauto.
            * exfalso. eapply NEXTRA0. right. eauto.
            * econs 1; eauto.
              { ii. eapply NPROM. unguard. destruct H2; des; auto. }
              { ii. destruct H2; ss.
                eapply EXCLUSIVEEXTRA in H2. inv H2. clarify. }
          + ss. des; clarify. erewrite H1. econs 2; eauto.
            * ii. destruct H2; des; clarify.
              eapply EXCLUSIVE in H2. des. inv UNCH. clarify.
            * ii. destruct H2; clarify.
              { eapply EXCLUSIVEEXTRA in H2. inv H2. clarify. }
              { eapply NEXTRA; eauto. }
            * refl.
            * i. eapply eq_lb_time.
          + guardH o. guardH o0.
            set (MEM0:=MEMORY.(sim_memory_contents) loc0 ts). inv MEM0; ss.
            * econs 1; eauto. ii. eapply NPROM. unguard. destruct H2; des; auto.
            * econs 2; eauto. ii. eapply NPROM. unguard. destruct H2; des; auto.
            * econs 3; eauto. destruct PROM.
              { left. auto. }
              { right. splits; auto. ii. destruct o0; des; clarify. }
            * econs 4; eauto. ii. eapply NPROM. unguard. destruct H2; des; auto.
        - i. des_ifs.
          + ss. des; clarify. destruct EXTRA0; ss.
            eapply EXCLUSIVEEXTRA in H2. inv H2. clarify.
          + guardH o. dup EXTRA0. eapply MEMORY.(sim_memory_wf) in EXTRA0.
            des. splits; auto. destruct FORGET0.
            * left. auto.
            * right. splits; auto. ii. clarify. ss.
              destruct o; ss; clarify.
              exploit sim_memory_extra_inj.
              { eauto. }
              { eapply EXTRA1. }
              { right. eauto. }
              i. clarify.
      }
      { repeat econs; eauto. }
      { ss. }
    }
    { assert (NOEXTRA: forall t, ~ (extra_others \\3// extra_self) loc t to).
      { ii. destruct H2.
        { eapply EXCLUSIVEEXTRA in H2. inv H2. ss.
          dup GET. eapply WF in GET. exploit memory_get_from_inj.
          { eapply GET. }
          { eapply GET0. }
          i. des; clarify.
        }
        set (PROM := PROMS.(sim_promise_contents) loc t).
        inv PROM; try by (eapply NEXTRA1; eauto).
        exploit MEMORY.(sim_memory_wf).
        { right. eapply EXTRA. }
        i. des. exploit UNIQUE.
        { right. eapply H2. } i. clarify.
        exploit memory_get_from_inj.
        { symmetry. eapply H4. }
        { eapply GET. }
        i. des; clarify.
      }

      exploit (@Memory.add_exists mem_src3 loc to to0 Message.reserve).
      { i. erewrite Memory.add_o in GET2; eauto.
        erewrite Memory.remove_o in GET2; eauto.
        erewrite Memory.remove_o in GET2; eauto. des_ifs.
        { ss. des; clarify. symmetry. eapply Interval.disjoint_imm. }
        exploit Memory.get_disjoint.
        { eapply WF. eapply GET. }
        { eapply GET2. } i. des; clarify.
      }
      { eapply memory_get_ts_strong in GET. des; clarify. }
      { econs; eauto. } intros [mem_src4 ADDMEM4].
      exploit Memory.add_exists_le; try apply ADDMEM4; eauto. intros [prom_src4 ADDPROM4].

      assert (PROMISE4: Local.promise_step (Local.mk tvw prom_src3) mem_src3 loc to to0 Message.reserve (Local.mk tvw prom_src4) mem_src4 Memory.op_kind_add).
      { econs; eauto. econs; eauto. ss. }

      exists (Local.mk tvw prom_src4), mem_src4, (fun l t => prom_self l t /\ (loc, to) <> (l, t)), extra_self.
      esplits; try eassumption.
      { auto. }
      { econs 2; [..|ss].
        { econs; eauto. econs; eauto. }
        econs 2; [..|ss].
        { econs; eauto. econs; eauto. }
        econs 2; [..|ss].
        { econs; eauto. econs; eauto. }
        econs 2; [..|ss].
        { econs; eauto. econs; eauto. }
        econs 1.
      }
      { econs. econs.
        - i. erewrite (@Memory.add_o prom_src4); eauto.
          erewrite (@Memory.add_o prom_src3); eauto.
          erewrite (@Memory.remove_o prom_src2); eauto.
          erewrite (@Memory.remove_o prom_src1); eauto. des_ifs.
          + ss. des; clarify.
            set (PROM:=PROMS.(sim_promise_contents) loc to0).
            rewrite GET in *. inv PROM; clarify.
            * econs 2; eauto. ii. des; clarify.
            * econs 3; eauto. ii. des; clarify.
            * econs 4; eauto. splits; auto. ii. clarify.
              eapply memory_get_ts_strong in H0. des; clarify. timetac.
          + ss. des; clarify. rewrite H. econs 2; eauto. ii. des; clarify.
          + ss. guardH o. guardH o0.
            set (PROM:=PROMS.(sim_promise_contents) loc0 ts). inv PROM; clarify.
            * econs 1; eauto. ii. des; auto.
            * econs 2; eauto. ii. des; auto.
            * econs 3; eauto. ii. des; auto.
            * econs 4; eauto. split; auto. ii. destruct o0; clarify.
            * econs 5; eauto. ii. des; ss.
        - i. dup EXTRA. eapply PROMS in EXTRA. des. splits; auto.
          ii. clarify. eapply NOEXTRA. right. eauto.
        - i. des. dup SELF. eapply PROMS in SELF. des. exists to1. split; auto.
          red. erewrite Memory.add_o; eauto. erewrite Memory.add_o; eauto.
          erewrite Memory.remove_o; eauto. erewrite Memory.remove_o; eauto. des_ifs.
          + ss. des; clarify.
          + ss. des; clarify. exfalso. eapply NSELF; eauto. right. auto.
      }
      { econs.
        - i. erewrite (@Memory.add_o mem_src4); eauto.
          erewrite (@Memory.add_o mem_src3); eauto.
          erewrite (@Memory.remove_o mem_src2); eauto.
          erewrite (@Memory.remove_o mem_src1); eauto. des_ifs.
          + ss. des; clarify.
            set (MEM0:=MEMORY.(sim_memory_contents) loc to0). inv MEM0; ss.
            * eapply WF in GET. rewrite GET in *. clarify.
            * eapply WF in GET. rewrite GET in *. clarify.
              econs 2; eauto. ii. eapply NPROM. unguard. des; auto.
            * eapply WF in GET. rewrite GET in *. clarify. econs 3; eauto.
              unguard. des; auto. right. splits; auto. ii. clarify.
              eapply memory_get_ts_strong in GET. des; clarify. timetac.
            * eapply WF in GET. rewrite GET in *. clarify.
              exfalso. eapply NOEXTRA. eauto.
          + ss. des; clarify. erewrite H1. econs 2; eauto.
            * ii. destruct H2; des; clarify.
              eapply EXCLUSIVE in H2. des. inv UNCH. clarify.
            * ii. destruct H2; clarify.
              { eapply EXCLUSIVEEXTRA in H2. inv H2. clarify. }
              { eapply NEXTRA; eauto. }
            * refl.
            * i. eapply eq_lb_time.
          + guardH o. guardH o0.
            set (MEM0:=MEMORY.(sim_memory_contents) loc0 ts). inv MEM0; ss.
            * econs 1; eauto. ii. eapply NPROM. unguard. destruct H2; des; auto.
            * econs 2; eauto. ii. eapply NPROM. unguard. destruct H2; des; auto.
            * econs 3; eauto. destruct PROM.
              { left. auto. }
              { right. splits; auto. ii. destruct o0; des; clarify. }
            * econs 4; eauto. ii. eapply NPROM. unguard. destruct H2; des; auto.
        - i. dup EXTRA. eapply MEMORY.(sim_memory_wf) in EXTRA.
          des. splits; auto. destruct FORGET0.
          + left. auto.
          + right. splits; auto. ii. clarify.
            exfalso. eapply NOEXTRA; eauto.
      }
      { repeat econs; eauto. }
      { ss. }
    }
  Qed.

  Lemma sim_configuration_forget_promise_exist
        views prom extra proml c_src c_mid c_tgt
        (SIM: sim_configuration views prom extra proml c_src c_mid c_tgt)
        (WF_SRC: Configuration.wf c_src)
        tid loc ts
        (PROM: prom tid loc ts)
    :
      exists lang st lc_src from msg,
        (<<TID: IdentMap.find tid c_src.(Configuration.threads) = Some (existT _ lang st, lc_src)>>) /\
        (<<PROMISE: Memory.get loc ts lc_src.(Local.promises) = Some (from, msg)>>)
  .
  Proof.
    destruct (IdentMap.find tid c_src.(Configuration.threads)) as
        [[[lang st] lc_src]|] eqn:TID.
    { inv SIM. specialize (THSPF tid). setoid_rewrite TID in THSPF. ss. des_ifs.
      inv THSPF. inv LOCAL. set (CNT:=PROMS.(sim_promise_contents) loc ts).
      inv CNT; ss. esplits; eauto. }
    { exfalso. inv SIM. eapply BOT in TID. des. eapply PROM0; eauto. }
  Qed.

  Lemma sim_configuration_extra_promise_exist
        views prom proml extra c_src c_mid c_tgt
        (SIM: sim_configuration views prom extra proml c_src c_mid c_tgt)
        (WF_SRC: Configuration.wf c_src)
        tid loc ts from
        (PROM: extra tid loc ts from)
    :
      exists lang st lc_src,
        (<<TID: IdentMap.find tid c_src.(Configuration.threads) = Some (existT _ lang st, lc_src)>>) /\
        (<<PROMISE: Memory.get loc ts lc_src.(Local.promises) = Some (from, Message.reserve)>>)
  .
  Proof.
    destruct (IdentMap.find tid c_src.(Configuration.threads)) as
        [[[lang st] lc_src]|] eqn:TID.
    { inv SIM. specialize (THSPF tid). setoid_rewrite TID in THSPF. ss. des_ifs.
      inv THSPF. inv LOCAL. set (CNT:=PROMS.(sim_promise_contents) loc ts).
      inv CNT; try by (exfalso; eapply NEXTRA; eauto).
      exploit (MEMPF.(sim_memory_wf) loc from ts); eauto. i. des.
      exploit (UNIQUE from0); eauto. i. subst. esplits; eauto. }
    { exfalso. inv SIM. eapply BOT in TID. des. eapply EXTRA; eauto. }
  Qed.

  Lemma sim_configuration_forget_exclusive
        views prom extra proml c_src c_mid c_tgt
        tid lang st lc_src
        (SIM: sim_configuration views prom extra proml c_src c_mid c_tgt)
        (WF_SRC: Configuration.wf c_src)
        (TID: IdentMap.find tid c_src.(Configuration.threads) = Some (existT _ lang st, lc_src))
    :
      forall loc ts
             (PROM: all_promises (fun tid' => tid <> tid') prom loc ts),
      exists (from : Time.t) (msg : Message.t),
        (<<UNCH: unchangable c_src.(Configuration.memory) lc_src.(Local.promises) loc ts from msg>>).
  Proof.
    ii. dup WF_SRC. inv WF_SRC.
    inv PROM. exploit sim_configuration_forget_promise_exist; eauto. i. des.
    dup TID1. eapply WF in TID1. inv TID1. esplits. econs.
    { eapply PROMISES. eauto. }
    { inv WF. exploit DISJOINT; eauto. intros DISJ. inv DISJ.
      destruct (Memory.get loc ts (Local.promises lc_src)) as [[from' msg']|] eqn:GET; auto.
      exfalso. inv DISJOINT0. exploit DISJOINT1; eauto. i. des.
      eapply memory_get_ts_strong in GET. des; subst; ss.
      eapply memory_get_ts_strong in  PROMISE. des; subst; ss.
      eapply x; eauto.
      { econs; [|refl]. auto. }
      { econs; ss. refl. }
    }
  Qed.

  Lemma sim_configuration_extra_exclusive
        views prom extra proml c_src c_mid c_tgt
        tid lang st lc_src
        (SIM: sim_configuration views prom extra proml c_src c_mid c_tgt)
        (WF_SRC: Configuration.wf c_src)
        (TID: IdentMap.find tid c_src.(Configuration.threads) = Some (existT _ lang st, lc_src))
    :
      forall loc ts from
             (EXTRA: all_extra (fun tid' => tid <> tid') extra loc ts from),
        (<<UNCH: unchangable c_src.(Configuration.memory) lc_src.(Local.promises) loc ts from Message.reserve>>).
  Proof.
    ii. dup WF_SRC. inv WF_SRC.
    inv EXTRA. exploit sim_configuration_extra_promise_exist; eauto. i. des.
    dup TID1. eapply WF in TID1. inv TID1. esplits. econs.
    { eapply PROMISES. eauto. }
    { inv WF. exploit DISJOINT; eauto. intros DISJ. inv DISJ.
      destruct (Memory.get loc ts (Local.promises lc_src)) as [[from' msg']|] eqn:GET; auto.
      exfalso. inv DISJOINT0. exploit DISJOINT1; eauto. i. des.
      eapply memory_get_ts_strong in GET. des; subst; ss.
      eapply memory_get_ts_strong in  PROMISE. des; subst; ss.
      eapply x; eauto.
      { econs; [|refl]. auto. }
      { econs; ss. refl. }
    }
  Qed.

  Lemma sim_configuration_sim_thread views prom extra proml
        (c_src c_mid c_tgt: Configuration.t)
        tid lang st lc_tgt
        (SIM: sim_configuration views prom extra proml c_src c_mid c_tgt)
        (TIDTGT: IdentMap.find tid c_tgt.(Configuration.threads) = Some (existT _ lang st, lc_tgt))
    :
      exists lc_src lc_mid,
        (<<TIDSRC: IdentMap.find tid c_src.(Configuration.threads) = Some (existT _ lang st, lc_src)>>) /\
        (<<TIDMID: IdentMap.find tid c_mid.(Configuration.threads) = Some (existT _ lang st, lc_mid)>>) /\
        (<<SIM: sim_thread
                  views
                  (prom tid)
                  (all_promises (fun tid' => tid <> tid') prom)
                  (extra tid)
                  (all_extra (fun tid' => tid <> tid') extra)
                  (Thread.mk _ st lc_src c_src.(Configuration.sc) c_src.(Configuration.memory))
                  (Thread.mk _ st lc_mid c_mid.(Configuration.sc) c_mid.(Configuration.memory))
                  (Thread.mk _ st lc_tgt c_tgt.(Configuration.sc) c_tgt.(Configuration.memory))>>).
  Proof.
    inv SIM. ss.
    specialize (THSJOIN tid). specialize (THSPF tid).
    setoid_rewrite TIDTGT in THSJOIN. unfold option_rel in THSJOIN. des_ifs.
    unfold option_rel in THSPF. des_ifs.
    destruct p as [[lang_mid st_mid] lc_mid]. destruct p0 as [[lang_src st_src] lc_src].
    dup THSPF. dup THSJOIN.
    dep_inv THSPF0. dep_inv THSJOIN0. esplits; eauto. econs; eauto.
    replace (all_promises (fun tid' => tid <> tid') prom \\2// prom tid) with
        (all_promises (fun _ => True) prom); cycle 1.
    { extensionality loc. extensionality ts.
      apply Coq.Logic.PropExtensionality.propositional_extensionality. split; i.
      { inv H. destruct (Ident.eq_dec tid tid0).
        { subst. right. auto. }
        { left. econs; eauto. }
      }
      { destruct H.
        { inv H. econs; eauto. }
        { econs; eauto. }
      }
    }
    replace (all_extra (fun tid' => tid <> tid') extra \\3// extra tid) with
        (all_extra (fun _ => True) extra); cycle 1.
    { extensionality loc. extensionality ts. extensionality from.
      apply Coq.Logic.PropExtensionality.propositional_extensionality. split; i.
      { inv H. destruct (Ident.eq_dec tid tid0).
        { subst. right. auto. }
        { left. econs; eauto. }
      }
      { destruct H.
        { inv H. econs; eauto. }
        { econs; eauto. }
      }
    }
    auto.
  Qed.

  Lemma remember_first_promise views prom extra proml
        c_src c_mid c_tgt tid loc ts
        (SIM: sim_configuration views prom extra proml c_src c_mid c_tgt)
        (WFSRC: Configuration.wf c_src)
        (WFMID: JConfiguration.wf views c_mid)
        (WFTGT: Configuration.wf c_tgt)
        (FORGET: prom tid loc ts)
        (FIRST: forall tid' ts' (FORGET: prom tid' loc ts'), Time.le ts ts')
    :
      exists extra' c_src',
        (<<STEP: Configuration.step MachineEvent.silent tid c_src c_src'>>) /\
        (<<SIM: sim_configuration views (fun tid' => if (Ident.eq_dec tid' tid) then (fun l t => prom tid l t /\ (loc, ts) <> (l, t)) else (prom tid')) extra' proml c_src' c_mid c_tgt>>).
  Proof.
    dup SIM. inv SIM0.
    destruct (IdentMap.find tid ths_tgt) eqn:TIDTGT.
    2: {
      specialize (THSJOIN tid). specialize (THSPF tid).
      rewrite TIDTGT in *. unfold option_rel in *. des_ifs.
      eapply BOT in Heq0. des. exfalso. eapply PROM; eauto. }
    destruct p as [[lang st] lc_tgt].
    hexploit PAST; eauto. i. des.
    2: { exfalso. eapply PROM; eauto. }
    hexploit sim_configuration_sim_thread; eauto. i. des. ss. dep_inv SIM0.
    generalize (sim_configuration_forget_exclusive SIM WFSRC TIDSRC). intros EXCLPROM.
    generalize (sim_configuration_extra_exclusive SIM WFSRC TIDSRC). intros EXCLEXTRA.
    exploit remember_first_promise_thread; eauto.
    { eapply WFSRC in TIDSRC. eauto. }
    { ii. destruct FORGET0; eauto. inv H. eapply FIRST; eauto. }
    { eapply WFMID. }
    { eapply WFSRC. }
    { eapply WFMID. }
    { eapply WFMID; eauto. } ss. i. des.

    exploit Trace.steps_future; eauto.
    { eapply WFSRC; eauto. }
    { eapply WFSRC. }
    { eapply WFSRC. } ss. i. des.

    exploit sim_promise_weak_strengthen.
    { eauto. }
    { eapply MEMORY. }
    { eapply WFMID; eauto. }
    { eapply WF2. }
    { eapply WF2. }
    { eapply WF2. }
    { inv LOCAL. eauto. }
    { eauto. } i. des.
    destruct lc_src'. eapply reserve_future_memory_steps in FUTURE. des. ss.

    exploit Trace.steps_trans.
    { eapply STEPS. }
    { eapply STEPS0. }
    intros STEPS1.
    exploit Trace.steps_future; try apply STEPS1; eauto.
    { ss. eapply WFSRC; eauto. }
    { eapply WFSRC. }
    { eapply WFSRC. } ss. i. des.

    assert (SILENT1: List.Forall (fun lce => ThreadEvent.get_machine_event (snd lce) = MachineEvent.silent) (tr ++ tr0)).
    { eapply Forall_app; eauto. eapply reserving_trace_silent; eauto. }

    hexploit (list_match_rev (tr ++ tr0)). i. des.
    { eapply app_eq_nil in H. des; ss. }
    rewrite H in *.
    dup STEPS1. eapply Trace.steps_separate in STEPS1. des.
    inv STEPS4; clarify. inv STEPS1; clarify.
    eapply Forall_app_inv in SILENT1. des. inv FORALL2. ss.
    eapply Trace.silent_steps_tau_steps in STEPS3; eauto.

    hexploit sim_thread_consistent.
    { instantiate (3:=Thread.mk _ st (Local.mk tview prom_src') sc_src mem_src'0).
      eapply past_consistent_mon.
      { eauto. }
      { refl. }
      { eapply Memory.future_future_weak; eauto. }
    }
    { econs.
      { econs; eauto. }
      { destruct lc_mid. ss. inv LOCAL. eauto. }
      { eauto. }
      { eauto. }
      { eapply SC. }
    }
    { ss. }
    { eapply WFMID. }
    { eapply WFTGT. }
    { eauto. }
    { eapply WFMID. }
    { eapply WFTGT. }
    { inv LOCAL. ss. }
    { inv LOCAL. ss. eapply WFMID; eauto. }
    { eapply WFTGT; eauto. }
    { eauto. }
    { eauto. }
    { ss. i. eapply EXCLPROM in OTHER. des.
      eapply unchangable_trace_steps_increase in STEPS2; eauto.
    }
    { ss. i. eapply EXCLEXTRA in OTHER. des.
      eapply unchangable_trace_steps_increase in STEPS2; eauto.
    }
    { s. ii. inv OTHER.
      specialize (THSPF tid0). unfold option_rel in THSPF. des_ifs.
      2: { exfalso. eapply BOT in Heq. des. eapply PROM; eauto. }
      inv THSPF. inv LOCAL0.
      set (PROM:=PROMS0.(sim_promise_contents) loc0 to). inv PROM; clarify.
      destruct st0 as [lang0 st0].
      inv WFMID. inv WF. ss. inv WF1. exploit DISJOINT; eauto. i.
      inv H0. inv x. inv DISJOINT0. hexploit DISJOINT1; eauto. i. des.
      eapply H0; eauto. econs; [|refl]. ss.
      symmetry in H7. eapply memory_get_ts_strong in H7. des; clarify.
      inv ITV. ss. inv FROM.
    }
    { ss. i. eapply Forall_impl; [|eapply JOINED].
      i. ss. eapply semi_closed_view_future; eauto.
      eapply Memory.future_future_weak; eauto.
    }
    { inv LOCAL. ss. eapply WFMID in TIDMID; eauto. }
    { ss. eapply WFMID; eauto. }
    { eapply WFMID; eauto. } i.

    exists (fun tid' => if (Ident.eq_dec tid' tid) then extra_self' else (extra tid')). esplits.
    { replace MachineEvent.silent with (ThreadEvent.get_machine_event e).
      econs 2; eauto. ii. clarify. }
    { econs; eauto.
      - i. erewrite IdentMap.gsspec. des_ifs. setoid_rewrite TIDMID.
        ss. econs; eauto. inv LOCALPF. inv LOCAL. econs; eauto.
        eapply sim_promise_strong_sim_promise; eauto.
      - ss. i. erewrite IdentMap.gsspec in NONE. des_ifs.
        eapply BOT in NONE. des. splits; auto.
      - match goal with
        | _:sim_memory L times ?proms0 ?extra0 mem_src'0 mem_mid
          |- sim_memory L times ?proms1 ?extra1 mem_src'0 mem_mid =>
          (replace proms1 with proms0); [replace extra1 with extra0|]; eauto
        end.
        + extensionality l. extensionality from. extensionality to.
          apply Coq.Logic.PropExtensionality.propositional_extensionality. split; i.
          { destruct H2.
            { inv H2. eapply all_extra_intro with (tid:=tid0); ss. des_ifs. }
            { eapply all_extra_intro with (tid:=tid); ss. des_ifs. }
          }
          { inv H2. unguard. des_ifs; auto. eauto. }
        + extensionality l. extensionality to.
          apply Coq.Logic.PropExtensionality.propositional_extensionality. split; i.
          { destruct H2.
            { inv H2. eapply all_promises_intro with (tid:=tid0); ss. des_ifs. }
            { eapply all_promises_intro with (tid:=tid); ss. des_ifs. }
          }
          { inv H2. unguard. des_ifs; auto. eauto. }
      - ss. i. eapply Forall_impl; [|eapply JOINED].
        i. ss. eapply semi_closed_view_future; eauto.
        eapply Memory.future_future_weak; eauto.
      - i. exploit PAST; eauto. i. des.
        { left. eapply past_consistent_mon; eauto.
          { refl. }
          { eapply Memory.future_future_weak; eauto. }
        }
        { right. rewrite IdentMap.gsspec. des_ifs.
          dep_clarify. exfalso. eapply PROM; eauto.
        }
      - i. eapply PROML. des_ifs. des; auto.
    }
  Qed.

  Lemma first_promise_exists (l: list (Ident.t * Loc.t * Time.t)) (loc: Loc.t):
    (forall tid ts, ~ List.In (tid, loc, ts) l) \/
    (exists tid ts,
        List.In (tid, loc, ts) l /\
        (forall tid' ts' (IN: List.In (tid', loc, ts') l), Time.le ts ts')).
  Proof.
    induction l.
    { left. ii. ss. }
    destruct a as [[tid' loc'] ts']. destruct (Loc.eq_dec loc loc').
    { clarify. des.
      - right. exists tid', ts'. ss. esplits; eauto.
        i. des; clarify.
        + refl.
        + exfalso. eapply IHl; eauto.
      - right. destruct (Time.le_lt_dec ts ts').
        + exists tid, ts. ss. esplits; eauto.
          i. des; clarify. eapply IHl0; eauto.
        + exists tid', ts'. ss. esplits; eauto.
          i. des; clarify.
          * refl.
          * eapply IHl0 in IN. etrans; eauto. left. auto.
    }
    { des.
      - left. ii. ss. des; clarify. eapply IHl; eauto.
      - right. exists tid, ts. ss. esplits; eauto.
        i. des; clarify. eapply IHl0; eauto.
    }
  Qed.

  Lemma filter_length_le A f (l: list A)
    :
      length (filter f l) <= length l.
  Proof.
    induction l; ss. des_ifs; ss.
    - eapply le_n_S; eauto.
    - econs. eauto.
  Qed.

  Lemma filter_length_decrease A f (l: list A) a
        (IN: List.In a l)
        (SAT: f a = false)
    :
      length (filter f l) < length l.
  Proof.
    revert a IN SAT. induction l; i; ss. des.
    - clarify. eapply Lt.le_lt_n_Sm.
      eapply filter_length_le.
    - des_ifs.
      + ss. eapply Lt.lt_n_S; eauto.
      + eapply Lt.le_lt_n_Sm.
        eapply filter_length_le.
  Qed.

  Lemma remember_list_decrease views prom extra proml pl
        c_src c_mid c_tgt
        (SIM: sim_configuration views prom extra proml c_src c_mid c_tgt)
        (COMPLETE: forall tid loc to (PROM: prom tid loc to), List.In (tid, loc, to) pl)
        (WFSRC: Configuration.wf c_src)
        (WFMID: JConfiguration.wf views c_mid)
        (WFTGT: Configuration.wf c_tgt)
    :
      pl = [] \/
      exists tid pl' prom' extra' c_src',
        (<<STEP: Configuration.opt_step MachineEvent.silent tid c_src c_src'>>) /\
        (<<SIM: sim_configuration views prom' extra' proml c_src' c_mid c_tgt>>) /\
        (<<COMPLETE: forall tid loc to (PROM: prom' tid loc to), List.In (tid, loc, to) pl'>>) /\
        (<<DECREASE: length pl' < length pl>>)
  .
  Proof.
    destruct pl as [|[[tid' loc] to'] pl]; auto. right.
    hexploit (first_promise_exists ((tid', loc, to') :: pl) loc); eauto. i. des.
    { exfalso. ss. eapply H; eauto. }
    set (pl':= filter (fun tlt =>
                         match tlt with
                         | (tid0, loc0, to0) =>
                           if Ident.eq_dec tid0 tid then
                             if loc_ts_eq_dec (loc0, to0) (loc, ts) then false else true
                           else
                             true
                         end) ((tid', loc, to') :: pl)).
    assert (DECREASE: length pl' < length ((tid', loc, to') :: pl)).
    { eapply filter_length_decrease.
      { eapply H. }
      des_ifs. ss. des; clarify.
    }
    exists tid, pl'.
    destruct (classic (prom tid loc ts)) as [PROM|NPROM].
    { exploit remember_first_promise; eauto. i. des.
      exists (fun tid' => if LocSet.Facts.eq_dec tid' tid
                          then fun l t => prom tid l t /\ (loc, ts) <> (l, t) else prom tid'), extra', c_src'.
      esplits; eauto. i. eapply filter_In.
      des_ifs; des; ss; clarify; eauto.
    }
    { exists prom, extra, c_src. esplits; eauto. i.
      eapply filter_In. splits; auto. des_ifs. ss. des; clarify. }
  Qed.

  Lemma concat_in A (ls: list (list A)):
    forall a,
      List.In a (concat ls) <-> (exists l, List.In l ls /\ List.In a l).
  Proof.
    induction ls; ss.
    - i. split; i; des; ss.
    - i. split; i.
      + eapply List.in_app_or in H. des.
        * esplits; eauto.
        * eapply IHls in H. des. esplits; eauto.
      + eapply List.in_or_app. des; clarify.
        * auto.
        * right. eapply IHls; eauto.
  Qed.

  Lemma remember_all views prom extra proml
        c_src c_mid c_tgt
        (SIM: sim_configuration views prom extra proml c_src c_mid c_tgt)
        (WFSRC: Configuration.wf c_src)
        (WFMID: JConfiguration.wf views c_mid)
        (WFTGT: Configuration.wf c_tgt)
    :
      exists c_src',
        (<<STEPS: rtc Configuration.tau_step c_src c_src'>>) /\
        (<<SIM: sim_configuration views (fun _ _ _ => False) (fun _ _ _ _ => False) proml c_src' c_mid c_tgt>>).
  Proof.
    assert (exists (pl: list (Ident.t * Loc.t * Time.t)),
               forall tid loc to (PROM: prom tid loc to), List.In (tid, loc, to) pl).
    { set (tids := List.map fst (IdentMap.elements c_tgt.(Configuration.threads))).
      set (promls := List.map (fun tid => List.map (fun locts => (tid, fst locts, snd locts)) (proml tid)) tids).
      exists (concat promls). i.
      inv SIM. destruct (IdentMap.find tid ths_tgt) as [[[lang st] lc]|] eqn:TID.
      2: {
        specialize (THSPF tid). specialize (THSJOIN tid). unfold option_rel in *.
        rewrite TID in *. des_ifs.
        eapply BOT in Heq0. des. exfalso. eapply PROM0; eauto.
      }
      eapply PROML in PROM.
      assert (TIDIN: List.In tid tids).
      { unfold tids. ss. eapply IdentMap.elements_correct in TID.
        eapply List.in_map with (f := fst) in TID; eauto. }
      eapply concat_in.
      exists (List.map (fun locts => (tid, fst locts, snd locts)) (proml tid)). split.
      { eapply List.in_map with (f:= fun tid0 => map (fun locts : Loc.t * Time.t => (tid0, fst locts, snd locts)) (proml tid0)) in TIDIN; eauto. }
      { eapply List.in_map with (f:= fun locts : Loc.t * Time.t => (tid, fst locts, snd locts)) in PROM; eauto. }
    }
    des. remember (S (length pl)).
    assert (LEN: length pl < n).
    { clarify. } clear Heqn.
    revert pl LEN prom H c_src extra SIM WFSRC. induction n.
    { i. destruct pl; inv LEN. }
    { i. exploit remember_list_decrease; eauto. i. des; clarify.
      { exists c_src.
        replace prom with (fun (_: Ident.t) (_: Loc.t) (_: Time.t) => False) in *.
        { esplits; eauto.
          match goal with
          | _:sim_configuration ?views0 ?proms0 ?extra0 ?proml0 ?c_src0 ?c_mid0 ?c_tgt0
            |- sim_configuration ?views1 ?proms1 ?extra1 ?proml1 ?c_src1 ?c_mid1 ?c_tgt1 =>
            (replace extra1 with extra0); eauto
          end.
          extensionality tid. extensionality loc. extensionality from. extensionality ts.
          apply Coq.Logic.PropExtensionality.propositional_extensionality.
          split; i; ss.
          inv SIM. exploit (MEMPF.(sim_memory_wf)).
          { econs; eauto. }
          i. des. inv FORGET. ss.
        }
        extensionality tid. extensionality loc. extensionality ts.
        apply Coq.Logic.PropExtensionality.propositional_extensionality. split; i; ss.
        eapply H; eauto.
      }
      exploit (IHn pl'); eauto.
      { eapply Lt.lt_n_Sm_le in LEN. eapply PeanoNat.Nat.lt_le_trans; eauto. }
      { eapply Configuration.opt_step_future in STEP; eauto. des. auto. }
      i. des. exists c_src'0. splits; eauto.
      inv STEP; eauto. econs; eauto. econs; eauto.
    }
  Qed.

  Lemma sim_promises_bot_eq prom_src prom_tgt
        (SIM: sim_promise_strong L times bot2 bot3 bot3 prom_src prom_tgt)
    :
      prom_src = prom_tgt.
  Proof.
    eapply Memory.ext. i.
    set (PROM:=SIM.(sim_promise_strong_contents) loc ts). inv PROM; auto.
    { des; clarify. }
    { des; clarify. }
    { des; clarify. }
  Qed.

  Inductive sim_configuration_strong
            (tids: Ident.t -> bool)
            (views: Loc.t -> Time.t -> list View.t)
    :
      forall (c_src c_mid c_tgt: Configuration.t), Prop :=
  | sim_configuration_strong_intro
      ths_src sc_src mem_src
      ths_mid mem_mid
      ths_tgt sc_tgt mem_tgt
      (THSPF: forall tid,
          option_rel
            (if tids tid
             then sim_statelocal L times bot2 bot3
             else eq)
            (IdentMap.find tid ths_src)
            (IdentMap.find tid ths_mid))
      (THSJOIN: forall tid,
          option_rel
            (JSim.sim_statelocal views)
            (IdentMap.find tid ths_mid)
            (IdentMap.find tid ths_tgt))
      (MEMPF: sim_memory L times bot2 bot3 mem_src mem_mid)
      (SCPF: TimeMap.le sc_src sc_tgt)

      (JOINED: forall loc ts, List.Forall (fun vw => semi_closed_view vw mem_src loc ts) (views loc ts))
      (MEMJOIN: SimMemory.sim_memory mem_mid mem_tgt)
      (MEMWF: memory_times_wf times mem_mid)
      (MEMWFTGT: memory_times_wf times mem_tgt)
      (PAST: forall tid lang st lc
                    (GET: IdentMap.find tid ths_tgt = Some (existT _ lang st, lc)),
          (<<CONSISTENT: past_consistent times mem_src (Thread.mk lang st lc sc_tgt mem_tgt)>>) \/
           (<<EQ: IdentMap.find tid ths_src = IdentMap.find tid ths_mid>>))
    :
      sim_configuration_strong
        tids views
        (Configuration.mk ths_src sc_src mem_src)
        (Configuration.mk ths_mid sc_src mem_mid)
        (Configuration.mk ths_tgt sc_tgt mem_tgt)
  .
  Hint Constructors sim_configuration_strong.

  Lemma strengthen_one tid views tids
        c_src c_mid c_tgt
        (SIM: sim_configuration_strong tids views c_src c_mid c_tgt)
        (WFSRC: Configuration.wf c_src)
        (WFMID: JConfiguration.wf views c_mid)
        (WFTGT: Configuration.wf c_tgt)
    :
      exists c_src',
        (<<STEP: Configuration.opt_step MachineEvent.silent tid c_src c_src'>>) /\
        (<<SIM: sim_configuration_strong (fun tid' => if Ident.eq_dec tid' tid then false else tids tid') views c_src' c_mid c_tgt>>).
  Proof.
    assert (BOT2: (bot2: Loc.t -> Time.t -> Prop) \\2// bot2 = bot2).
    { extensionality loc. extensionality ts.
      apply Coq.Logic.PropExtensionality.propositional_extensionality.
      unguard. split; i; des; ss.
    }
    assert (BOT3: (bot3: Loc.t -> Time.t -> Time.t -> Prop) \\3// bot3 = bot3).
    { extensionality loc. extensionality from. extensionality to.
      apply Coq.Logic.PropExtensionality.propositional_extensionality.
      unguard. split; i; des; ss.
    }

    inv SIM. dup THSPF. dup THSJOIN.
    specialize (THSPF tid). specialize (THSJOIN tid).
    unfold option_rel in THSPF, THSJOIN. des_ifs.
    { inv THSPF. dep_inv THSJOIN. hexploit PAST; eauto. i. des.
      2: {
        esplits; [econs 1|].
        econs; eauto.
        i. specialize (THSPF0 tid0). des_ifs.
        rewrite EQ. unfold option_rel. des_ifs.
      }
      inv LOCAL.
      exploit (@sim_promise_weak_strengthen L times WO bot2 bot2 bot3 bot3 prom_src prom_tgt mem_src mem_mid).
      { rewrite BOT2. rewrite BOT3. auto. }
      { inv WFMID. ss. eapply WF in Heq; eauto. eapply Heq. }
      { eapply WFSRC in Heq1; eauto. eapply Heq1. }
      { eapply WFSRC in Heq1; eauto. eapply Heq1. }
      { eapply WFSRC in Heq1; eauto. eapply Heq1. }
      { auto. }
      { auto. }
      i. des.
      eapply (@reserve_future_memory_steps lang st0 tvw sc_src) in FUTURE. des.
      exploit Trace.steps_future; eauto; ss.
      { eapply WFSRC in Heq1; eauto. }
      { eapply WFSRC. }
      { eapply WFSRC. } i. des. ss.
      eapply Trace.silent_steps_tau_steps in STEPS.
      2: { eapply reserving_trace_silent; eauto. }
      eapply rtc_tail in STEPS. des.
      { esplits.
        { econs 2. inv STEPS0. inv TSTEP.
          rewrite <- EVENT. econs 2; eauto.
          { destruct e; ss. }
          hexploit sim_thread_consistent.
          { instantiate (1:=Thread.mk _ st0 lc_tgt0 sc_tgt mem_tgt).
            instantiate (1:=Thread.mk _ st0 (Local.mk tvw prom_src') sc_src mem_src').
            eapply past_consistent_mon.
            { eauto. }
            { refl. }
            { eapply Memory.future_future_weak; eauto. }
          }
          { econs; eauto. econs; eauto. }
          { ss. }
          { eapply WFMID. }
          { eapply WFTGT. }
          { eauto. }
          { eapply WFMID. }
          { eapply WFTGT. }
          { eauto. }
          { inv WFMID. eapply WF in Heq. eauto. }
          { eapply WFTGT; eauto. }
          { eauto. }
          { eauto. }
          { ss. }
          { ss. }
          { ss. }
          { i. eapply Forall_impl; eauto. i. ss.
            eapply semi_closed_view_future; eauto.
            eapply Memory.future_future_weak; eauto.
          }
          { inv WFMID. eapply REL in Heq. eauto. }
          { eapply WFMID. }
          { eapply WFMID. }
          eauto.
        }
        { rewrite BOT2 in *. rewrite BOT3 in *. auto.
          econs; eauto.
          { i. specialize (THSPF0 tid0).
            rewrite IdentMap.gsspec. ss. des_ifs.
            rewrite Heq. ss. f_equal. f_equal.
            eapply sim_promises_bot_eq; eauto.
          }
          { i. eapply Forall_impl; eauto. i. ss.
            eapply semi_closed_view_future; eauto.
            eapply Memory.future_future_weak; eauto.
          }
          { i. exploit PAST; eauto. i. des.
            { left. eapply past_consistent_mon; eauto.
              { refl. }
              { eapply Memory.future_future_weak; eauto. }
            }
            { erewrite IdentMap.gsspec. des_ifs; eauto. dep_clarify.
              left. eapply past_consistent_mon; eauto.
              { refl. }
              { eapply Memory.future_future_weak; eauto. }
            }
          }
        }
      }
      { esplits; [econs 1|].
        econs; eauto.
        i. specialize (THSPF0 tid0). unfold option_rel in *. des_ifs.
        f_equal. f_equal. eapply sim_promises_bot_eq; eauto.
        rewrite BOT2 in *. rewrite BOT3 in *. auto.
      }
    }
    { esplits; [econs 1|].
      econs; eauto.
      i. specialize (THSPF0 tid0). unfold option_rel in *. des_ifs.
    }
    { esplits; [econs 1|].
      econs; eauto.
      i. specialize (THSPF0 tid0). unfold option_rel in *. des_ifs.
    }
  Qed.

  Lemma strengthen_finite views tidl tids
        c_src c_mid c_tgt
        (SIM: sim_configuration_strong tids views c_src c_mid c_tgt)
        (COMPLETE: forall tid (TIDS: tids tid = true), List.In tid tidl)
        (WFSRC: Configuration.wf c_src)
        (WFMID: JConfiguration.wf views c_mid)
        (WFTGT: Configuration.wf c_tgt)
    :
      exists c_src',
        (<<STEPS: rtc Configuration.tau_step c_src c_src'>>) /\
        (<<SIM: sim_configuration_strong (fun _ => false) views c_src' c_mid c_tgt>>).
  Proof.
    revert tids COMPLETE c_src SIM WFSRC. induction tidl.
    { i. esplits; [econs 1|]. inv SIM. econs; eauto.
      i. specialize (THSPF tid). des_ifs. exfalso. eapply COMPLETE; eauto. }
    i. exploit (@strengthen_one a); eauto. i. des.
    exploit Configuration.opt_step_future; eauto. i. des.
    exploit IHtidl; eauto.
    { i. ss. des_ifs. eapply COMPLETE in TIDS. des; clarify. }
    i. des. exists c_src'0. splits; eauto. etrans; [|eauto].
    inv STEP; eauto. econs 2; [|refl]. econs; eauto.
  Qed.

  Lemma strengthen_all views proml
        c_src c_mid c_tgt
        (SIM: sim_configuration views (fun _ _ _ => False) (fun _ _ _ _ => False) proml c_src c_mid c_tgt)
        (WFSRC: Configuration.wf c_src)
        (WFMID: JConfiguration.wf views c_mid)
        (WFTGT: Configuration.wf c_tgt)
    :
      exists c_src',
        (<<STEPS: rtc Configuration.tau_step c_src c_src'>>) /\
        (<<SIM: sim_configuration_strong (fun _ => false) views c_src' c_mid c_tgt>>).
  Proof.
    set (tidl := List.map fst (IdentMap.elements c_src.(Configuration.threads))).
    set (tids := fun tid => match IdentMap.find tid c_src.(Configuration.threads) with
                            | Some _ => true
                            | None => false
                            end).
    assert (SIMS: sim_configuration_strong tids views c_src c_mid c_tgt).
    { inv SIM. econs; eauto.
      { i. specialize (THSPF tid). des_ifs.
        unfold tids in Heq. ss. unfold option_rel. des_ifs.
        clear - Heq0 Heq2. setoid_rewrite Heq0 in Heq2. clarify. }
      { clear - MEMPF. econs.
        - i. set (MEM:=MEMPF.(sim_memory_contents) loc ts). inv MEM.
          + econs 1; ss.
          + econs 2; ss.
          + inv PROM. ss.
          + inv EXTRA. ss.
        - i. ss.
      }
      { i. exploit PAST; eauto. i. des; auto. }
    }
    eapply strengthen_finite; eauto.
    instantiate (1:=tidl). i. unfold tids in TIDS. des_ifs.
    eapply IdentMap.elements_correct in Heq.
    eapply List.in_map with (f:=fst) in Heq. eauto.
  Qed.

  Lemma remembered_behavior views c_src c_mid c_tgt
        (SIM: sim_configuration_strong (fun _ => false) views c_src c_mid c_tgt)
        (WFSRC: Configuration.wf c_src)
        (WFMID: JConfiguration.wf views c_mid)
        (WFTGT: Configuration.wf c_tgt)
    :
      behaviors SConfiguration.machine_step c_tgt <1=
      behaviors SConfiguration.machine_step c_src.
  Proof.
    ii. cut (behaviors SConfiguration.machine_step c_mid x0).
    { i. eapply Shorter.shorter_configuration_behavior; cycle 1.
      { eauto. }
      { eapply WFMID. }
      { eauto. }
      { inv SIM. replace ths_mid with ths_src in *.
        { econs; eauto. ii.
          set (MEM:=MEMPF.(sim_memory_contents) loc to). inv MEM; ss.
        }
        { eapply IdentMap.eq_leibniz. ii.
          specialize (THSPF y). unfold option_rel in THSPF. des_ifs.
        }
      }
    }
    { eapply JSim.machine_behavior; eauto. inv SIM. econs; eauto. }
  Qed.

  Lemma sim_configuration_behavior views prom extra proml c_src c_mid c_tgt
        (SIM: LocalPFSim.sim_configuration L times (fun _ => True) views prom extra proml c_src c_mid c_tgt)
        (WFSRC: Configuration.wf c_src)
        (WFMID: JConfiguration.wf views c_mid)
        (WFTGT: Configuration.wf c_tgt)
    :
      behaviors SConfiguration.machine_step c_tgt <1=
      behaviors SConfiguration.machine_step c_src.
  Proof.
    eapply non_time_time_sim_configuration in SIM.
    exploit remember_all; eauto. i. des.
    exploit Configuration.rtc_step_future; eauto. i. des.
    exploit strengthen_all; eauto. i. des.
    exploit Configuration.rtc_step_future; eauto. i. des.
    eapply SConfiguration.multi_step_equiv; eauto.
    eapply rtc_tau_step_behavior.
    { etrans; eauto. }
    eapply SConfiguration.multi_step_equiv; eauto.
    eapply remembered_behavior in PR; eauto.
  Qed.
End RECOVER.
