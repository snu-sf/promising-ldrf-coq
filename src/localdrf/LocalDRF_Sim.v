Require Import RelationClasses.

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

Require Import MemoryProps.
Require Import OrderedTimes.
Require SimMemory.

Require Import LocalDRFDef.
Require Import LocalDRF_PF.
Require Import TimeTraced.

Set Implicit Arguments.

Inductive all_promises
          (tids: Ident.t -> Prop)
          (proms: Ident.t -> Loc.t -> Time.t -> Prop): Loc.t -> Time.t -> Prop :=
| all_promises_intro
    tid loc ts
    (TID: tids tid)
    (PROMS: proms tid loc ts)
  :
    all_promises tids proms loc ts
.
Hint Constructors all_promises.

Inductive all_extra
          (tids: Ident.t -> Prop)
          (extra: Ident.t -> Loc.t -> Time.t -> Time.t -> Prop)
  : Loc.t -> Time.t -> Time.t -> Prop :=
| all_extra_intro
    tid loc ts from
    (TID: tids tid)
    (EXTRA: extra tid loc ts from)
  :
    all_extra tids extra loc ts from
.
Hint Constructors all_extra.

Section SIM.

  Variable L: Loc.t -> bool.
  Variable times: Loc.t -> Time.t -> Prop.
  Hypothesis WO: forall loc, well_ordered (times loc).

  Inductive sim_configuration
            (views: Loc.t -> Time.t -> list View.t)
            (prom: Ident.t -> Loc.t -> Time.t -> Prop)
            (extra: Ident.t -> Loc.t -> Time.t -> Time.t -> Prop)
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
            (IdentMap.find tid ths_tgt))
      (THSJOIN: forall tid,
          option_rel
            (JSim.sim_statelocal views)
            (IdentMap.find tid ths_src)
            (IdentMap.find tid ths_tgt))
      (BOT: forall tid (NONE: IdentMap.find tid ths_src = None),
          (<<PROM: forall loc ts, ~ prom tid loc ts>>) /\
          (<<EXTRA: forall loc ts from, ~ extra tid loc ts from>>))
      (MEMPF: sim_memory L times (all_promises (fun _ => True) prom) (all_extra (fun _ => True) extra) mem_mid mem_tgt)
      (SCPF: TimeMap.le sc_src sc_tgt)

      (JOINED: forall loc ts (NLOC: ~ L loc), List.Forall (fun vw => Memory.closed_view vw mem_src) (views loc ts))
      (MEMJOIN: SimMemory.sim_memory mem_mid mem_tgt)
      (MEMWF: memory_times_wf times mem_mid)
      (CONSISTENT: True)
    :
      sim_configuration
        views prom extra
        (Configuration.mk ths_src sc_src mem_src)
        (Configuration.mk ths_mid sc_src mem_mid)
        (Configuration.mk ths_tgt sc_tgt mem_tgt)
  .
  Hint Constructors sim_configuration.

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

  Ltac dep_clarify :=
    (repeat
       match goal with
       | H:existT ?P ?p ?x = existT ?P ?p ?y |- _ =>
         eapply inj_pair2 in H; subst
       end); ss; clarify.

  Ltac dep_inv H :=
    inv H; dep_clarify.

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
        (WFTIME: wf_time_evt times e_tgt)
        (NOREAD: no_read_msgs prom_others e_tgt)
        (EVENT: ThreadEvent.get_machine_event e_tgt = MachineEvent.silent)

        (THREAD: @sim_thread
                   views0 prom_self0 prom_others extra_self0 extra_others
                   lang th_src0 th_mid0 th_tgt0)

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
        (CONSISTENT: Local.promise_consistent th_tgt1.(Thread.local))

        (EXCLUSIVE: forall loc ts (OTHER: prom_others loc ts),
            exists from msg, <<UNCH: unchangable th_src0.(Thread.memory) th_src0.(Thread.local).(Local.promises) loc ts from msg>>)
        (EXCLUSIVEEXTRA: forall loc ts from (OTHER: extra_others loc ts from),
            (<<UNCH: unchangable th_src0.(Thread.memory) th_src0.(Thread.local).(Local.promises) loc ts from Message.reserve>>))
        (JOINED: forall loc ts (NLOC: ~ L loc), List.Forall (fun vw => Memory.closed_view vw th_src0.(Thread.memory)) (views0 loc ts))

        (REL: joined_released
                views0 th_mid0.(Thread.local).(Local.promises) th_mid0.(Thread.local).(Local.tview).(TView.rel))
        (JOINEDMEM: joined_memory views0 th_mid0.(Thread.memory))
        (VIEWS: wf_views views0)
    :
      exists th_mid1 th_src1 views1 prom_self1 extra_self1 pf_mid e_mid tr,
        (<<STEPMID: JThread.step pf_mid e_mid th_mid0 th_mid1 views0 views1>>) /\
        (<<STEPSRC: Trace.steps tr th_src0 th_src1>>) /\
        (<<THREAD: sim_thread
                     views1 prom_self1 prom_others extra_self1 extra_others
                     th_src1 th_mid1 th_tgt1>>) /\
        (<<EVENTJOIN: JSim.sim_event e_mid e_tgt>>) /\
        (<<JOINED: forall loc ts (NLOC: ~ L loc), List.Forall (fun vw => Memory.closed_view vw th_src1.(Thread.memory)) (views1 loc ts)>>) /\
        (<<TRACE: sim_silent_trace L tr (Some e_mid)>>) /\
        (<<MEMWF: memory_times_wf times th_mid1.(Thread.memory)>>)
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
  Qed.

  Lemma sim_thread_step_event
        views0 prom_self0 prom_others extra_self0 extra_others
        lang th_src0 th_mid0 th_tgt0 th_tgt1 pf_tgt e_tgt
        (STEPTGT: Thread.step pf_tgt e_tgt th_tgt0 th_tgt1)
        (WFTIME: wf_time_evt times e_tgt)
        (NOREAD: no_read_msgs prom_others e_tgt)
        (EVENT: ThreadEvent.get_machine_event e_tgt <> MachineEvent.silent)

        (THREAD: @sim_thread
                   views0 prom_self0 prom_others extra_self0 extra_others
                   lang th_src0 th_mid0 th_tgt0)

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
        (CONSISTENT: Local.promise_consistent th_tgt1.(Thread.local))

        (EXCLUSIVE: forall loc ts (OTHER: prom_others loc ts),
            exists from msg, <<UNCH: unchangable th_src0.(Thread.memory) th_src0.(Thread.local).(Local.promises) loc ts from msg>>)
        (EXCLUSIVEEXTRA: forall loc ts from (OTHER: extra_others loc ts from),
            (<<UNCH: unchangable th_src0.(Thread.memory) th_src0.(Thread.local).(Local.promises) loc ts from Message.reserve>>))
        (JOINED: forall loc ts (NLOC: ~ L loc), List.Forall (fun vw => Memory.closed_view vw th_src0.(Thread.memory)) (views0 loc ts))

        (REL: joined_released
                views0 th_mid0.(Thread.local).(Local.promises) th_mid0.(Thread.local).(Local.tview).(TView.rel))
        (JOINEDMEM: joined_memory views0 th_mid0.(Thread.memory))
        (VIEWS: wf_views views0)
    :
      exists th_mid1 th_src1 views1 prom_self1 extra_self1 pf_mid pf_src,
        (<<STEPMID: JThread.step pf_mid e_tgt th_mid0 th_mid1 views0 views1>>) /\
        (<<STEPSRC: Thread.step pf_src e_tgt th_src0 th_src1>>) /\
        (<<THREAD: sim_thread
                     views1 prom_self1 prom_others extra_self1 extra_others
                     th_src1 th_mid1 th_tgt1>>) /\
        (<<JOINED: forall loc ts (NLOC: ~ L loc), List.Forall (fun vw => Memory.closed_view vw th_src1.(Thread.memory)) (views1 loc ts)>>) /\
        (<<MEMWF: memory_times_wf times th_mid1.(Thread.memory)>>)
  .
  Proof.
    hexploit sim_thread_jsim_thread; eauto. intros JTHREAD.
    exploit JSim.sim_thread_step; eauto. i. des.
    dep_inv THREAD. destruct th1_src. ss.
    hexploit sim_thread_step_event; try apply STEP; eauto.
    { inv EVENT0; ss. }
    { inv STEP. ss. hexploit step_memory_times_wf; eauto. inv EVENT0; ss. }
    { dep_inv SIM. eapply JSim.sim_local_promise_consistent; eauto. }
    { inv EVENT0; ss. }
    assert (e_src = e_tgt).
    { inv EVENT0; ss. } subst.
    i. des. dep_inv SIM. esplits; eauto.
    { inv STEP. ss. hexploit step_memory_times_wf; eauto. }
  Qed.

  Lemma sim_thread_steps_silent
        views0 prom_self0 prom_others extra_self0 extra_others
        lang th_src0 th_mid0 th_tgt0 th_tgt1 tr_tgt
        (STEPTGT: Trace.steps tr_tgt th_tgt0 th_tgt1)

        (EVENTS: List.Forall (fun the => <<SAT: (wf_time_evt times /1\ no_read_msgs prom_others) (snd the)>> /\ <<TAU: ThreadEvent.get_machine_event (snd the) = MachineEvent.silent>>) tr_tgt)

        (THREAD: @sim_thread
                   views0 prom_self0 prom_others extra_self0 extra_others
                   lang th_src0 th_mid0 th_tgt0)

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
        (CONSISTENT: Local.promise_consistent th_tgt1.(Thread.local))

        (EXCLUSIVE: forall loc ts (OTHER: prom_others loc ts),
            exists from msg, <<UNCH: unchangable th_src0.(Thread.memory) th_src0.(Thread.local).(Local.promises) loc ts from msg>>)
        (EXCLUSIVEEXTRA: forall loc ts from (OTHER: extra_others loc ts from),
            (<<UNCH: unchangable th_src0.(Thread.memory) th_src0.(Thread.local).(Local.promises) loc ts from Message.reserve>>))
        (JOINED: forall loc ts (NLOC: ~ L loc), List.Forall (fun vw => Memory.closed_view vw th_src0.(Thread.memory)) (views0 loc ts))

        (REL: joined_released
                views0 th_mid0.(Thread.local).(Local.promises) th_mid0.(Thread.local).(Local.tview).(TView.rel))
        (JOINEDMEM: joined_memory views0 th_mid0.(Thread.memory))
        (VIEWS: wf_views views0)
    :
      exists th_mid1 th_src1 views1 prom_self1 extra_self1 tr_src,
        (<<STEPMID: JThread.rtc_tau th_mid0 th_mid1 views0 views1>>) /\
        (<<STEPSRC: Trace.steps tr_src th_src0 th_src1>>) /\
        (<<THREAD: sim_thread
                     views1 prom_self1 prom_others extra_self1 extra_others
                     th_src1 th_mid1 th_tgt1>>) /\
        (<<JOINED: forall loc ts (NLOC: ~ L loc), List.Forall (fun vw => Memory.closed_view vw th_src1.(Thread.memory)) (views1 loc ts)>>) /\
        (<<TRACE: True>>) /\
        (<<MEMWF: memory_times_wf times th_mid1.(Thread.memory)>>)
  .
  Proof.
    ginduction STEPTGT.
    { i. esplits; eauto. } i. subst. inv EVENTS. ss. des.
    hexploit Thread.step_future; try apply STEP; eauto. i. des.
    exploit sim_thread_step_silent; eauto.
    { eapply Trace.steps_promise_consistent; eauto. } i. des.
    hexploit JThread.step_future; try apply STEPMID; eauto. i. des.
    hexploit Trace.steps_future; try apply STEPSRC; eauto. i. des.
    exploit IHSTEPTGT; eauto.
    { i. eapply EXCLUSIVE in OTHER. des.
      eapply unchangable_trace_steps_increase in UNCH; eauto. }
    { i. eapply EXCLUSIVEEXTRA in OTHER. des.
      eapply unchangable_trace_steps_increase in OTHER; eauto. }
    i. des. esplits; try apply THREAD1; eauto.
    { econs; eauto. inv EVENTJOIN; ss. }
    { eapply Trace.steps_trans; eauto. }
  Qed.

  Lemma step_sim_configuration views0 prom0 extra0
        c_src0 c_mid0 c_tgt0 c_tgt1 e tid lang tr tr_cert
        (STEP: @times_configuration_step times lang tr tr_cert e tid c_tgt0 c_tgt1)
        (NOREAD: no_read_msgs

        (SIM: sim_configuration views0 prom0 extra0 c_src0 c_mid0 c_tgt0)

        (WF_SRC: Configuration.wf c_src0)
        (WF_MID: JConfiguration.wf views0 c_mid0)
        (WF_TGT: Configuration.wf c_tgt0)
    :
      exists c_src1 c_mid1 views1 prom1 extra1,
        (<<STEP: JConfiguration.step e tid c_src0 c_src1 views0 views1>>) /\
        (<<SIM: sim_configuration views1 prom1 extra1 c_src1 c_mid1 c_tgt1>>).
  Proof.
  Admitted.

End SIM.
