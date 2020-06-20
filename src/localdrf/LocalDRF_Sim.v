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
Require Import PFConsistentStrong.
Require Import Mapping.
Require Import GoodFuture.

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

  Lemma sim_memory_concrte_promised F extra mem_src mem_tgt
        (MEM: sim_memory L times F extra mem_src mem_tgt)
        loc ts
    :
      concrete_promised mem_src loc ts
      <->
      concrete_promised mem_tgt loc ts /\ ~ F loc ts.
  Proof.
    set (CNT:= MEM.(sim_memory_contents) loc ts). split; i.
    { inv H. erewrite GET in *. inv CNT. split; auto. econs; eauto. }
    { des. inv H. erewrite GET in *. inv CNT; ss. econs; eauto. }
  Qed.

  Definition pi_consistent (mem_src: Memory.t) lang (e0:Thread.t lang)
    : Prop :=
    forall mem1 tm sc
           (FUTURE: Memory.future_weak e0.(Thread.memory) mem1)
           (CLOSED: Memory.closed mem1)
           (LOCAL: Local.wf e0.(Thread.local) mem1),
    exists ftr e1,
      (<<STEPS: Trace.steps ftr (Thread.mk _ e0.(Thread.state) e0.(Thread.local) sc mem1) e1>>) /\
      (<<EVENTS: List.Forall (fun em => <<SAT: (promise_free
                                                  /1\ no_sc
                                                  /1\ no_read_msgs (fun loc ts => ~ (covered loc ts e0.(Thread.local).(Local.promises) \/ concrete_promised mem_src loc ts \/ Time.lt (tm loc) ts))
                                                  /1\ wf_time_evt times) (snd em)>> /\ <<TAU: ThreadEvent.get_machine_event (snd em) = MachineEvent.silent>>) ftr >>) /\
      (<<GOOD: good_future tm mem1 e1.(Thread.memory)>>) /\
      (<<SC: e1.(Thread.sc) = sc>>) /\
      (<<PROMISES: e1.(Thread.local).(Local.promises) = Memory.bot>>) /\
      (<<WRITES: forall loc from to val released
                        (GET: Memory.get loc to e0.(Thread.local).(Local.promises) = Some (from, Message.concrete val released)),
          exists th e,
            (<<WRITING: promise_writing_event loc from to val released e>>) /\
            (<<IN: List.In (th, e) ftr>>)>>).

  Lemma pi_consistent_mon mem_src0 mem_src1 lang
        st lc sc0 mem0 sc1 mem1
        (CONSISTENT: pi_consistent mem_src0 (Thread.mk lang st lc sc0 mem0))
        (FUTURE: Memory.future_weak mem0 mem1)
        (CONCRETE: concrete_promised mem_src0 <2= concrete_promised mem_src1)
    :
      pi_consistent mem_src1 (Thread.mk lang st lc sc1 mem1).
  Proof.
    ii. ss. exploit CONSISTENT.
    { transitivity mem1; eauto. }
    { eauto. }
    { eauto. }
    i. des. ss. esplits; eauto.
    eapply List.Forall_impl; eauto. i. ss. des. splits; auto.
    eapply no_read_msgs_mon; eauto. ii. des; eauto.
  Qed.

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

      (JOINED: forall loc ts (NLOC: ~ L loc), List.Forall (fun vw => Memory.closed_view vw mem_src) (views loc ts))
      (MEMJOIN: SimMemory.sim_memory mem_mid mem_tgt)
      (MEMWF: memory_times_wf times mem_mid)
      (CONSISTENT: forall tid lang st lc
                          (GET: IdentMap.find tid ths_src = Some (existT _ lang st, lc)),
          pi_consistent mem_src (Thread.mk lang st lc sc_tgt mem_tgt))
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
        (<<TRACE: sim_trace L tr (Some (th_mid0, e_mid))>>) /\
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

  Global Program Instance sim_event_Equivalence: Equivalence sim_event.
  Next Obligation.
  Proof. ii. destruct x; econs. Qed.
  Next Obligation.
  Proof. ii. inv H; econs. Qed.
  Next Obligation.
  Proof. ii. inv H; inv H0; econs. Qed.

  Lemma jsim_event_sim_event
    :
      JSim.sim_event <2= sim_event.
  Proof. ii. inv PR; econs. Qed.

  Lemma sim_event_racy_event e_src e_tgt
        (RACY: racy_event e_tgt)
        (EVENT: sim_event e_src e_tgt)
    :
      racy_event e_src.
  Proof.
    inv EVENT; ss.
  Qed.

  Lemma sim_trace_sim_event_sim_trace lang (tr_src: Trace.t lang) th_mid th_tgt e_mid e_tgt
        (TRACE: sim_trace L tr_src (Some (th_mid, e_mid)))
        (THREAD: TView.le th_mid.(Thread.local).(Local.tview) th_tgt.(Thread.local).(Local.tview))
        (EVENT: sim_event e_mid e_tgt)
    :
      sim_trace L tr_src (Some (th_tgt, e_tgt)).
  Proof.
    remember (Some (th_mid, e_mid)) as e. ginduction TRACE; i; clarify.
    { econs 2; eauto.
      { etrans; eauto. }
      { etrans; eauto. }
    }
    { econs 3; eauto. ii. eapply NONRACY. eapply sim_event_racy_event; eauto. }
    { econs 4; eauto. }
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
        (<<TRACE: sim_traces L tr_src tr_tgt>>) /\
        (<<MEMWF: memory_times_wf times th_mid1.(Thread.memory)>>)
  .
  Proof.
    ginduction STEPTGT.
    { i. esplits; eauto. econs. } i. subst. inv EVENTS. ss. des.
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
    { econs 2; eauto. eapply sim_trace_sim_event_sim_trace; eauto.
      { dep_inv THREAD. inv LOCALJOIN. ss. }
      { eapply jsim_event_sim_event; eauto. }
    }
  Qed.

  Lemma sim_configuration_sim_thread views prom extra (c_src c_mid c_tgt: Configuration.t)
        tid lang st lc_tgt
        (SIM: sim_configuration views prom extra c_src c_mid c_tgt)
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

  Lemma sim_configuration_forget_promise_exist
        views prom extra c_src c_mid c_tgt
        (SIM: sim_configuration views prom extra c_src c_mid c_tgt)
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
        views prom extra c_src c_mid c_tgt
        (SIM: sim_configuration views prom extra c_src c_mid c_tgt)
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
        views prom extra c_src c_mid c_tgt
        tid lang st lc_src
        (SIM: sim_configuration views prom extra c_src c_mid c_tgt)
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
        views prom extra c_src c_mid c_tgt
        tid lang st lc_src
        (SIM: sim_configuration views prom extra c_src c_mid c_tgt)
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

  Lemma step_sim_configuration views0 prom0 extra0
        c_src0 c_mid0 c_tgt0 c_tgt1 e tid lang tr_tgt tr_cert
        (STEPTGT: @times_configuration_step times lang tr_tgt tr_cert e tid c_tgt0 c_tgt1)
        (NOREAD: List.Forall
                   (fun the => no_read_msgs
                                 (all_promises (fun tid' => tid <> tid') prom0)
                                 (snd the)) (tr_tgt++tr_cert))
        (SIM: sim_configuration views0 prom0 extra0 c_src0 c_mid0 c_tgt0)
        (WF_SRC: Configuration.wf c_src0)
        (WF_MID: JConfiguration.wf views0 c_mid0)
        (WF_TGT: Configuration.wf c_tgt0)
    :
      exists tr_src c_src1 c_mid1 views1 prom1 extra1,
        (<<STEPSRC: @Trace.configuration_step lang tr_src e tid c_src0 c_src1>>) /\
        (<<STEPMID: JConfiguration.step e tid c_mid0 c_mid1 views0 views1>>) /\
        (<<SIM: sim_configuration views1 prom1 extra1 c_src1 c_mid1 c_tgt1>>) /\
        (<<TRACE: sim_traces L tr_src tr_tgt>>)
  .
  Proof.
    dep_inv STEPTGT.
    exploit sim_configuration_sim_thread; eauto. i. des.
    generalize (sim_configuration_forget_exclusive SIM WF_SRC TIDSRC).
    intros EXCLUSIVE.
    generalize (sim_configuration_extra_exclusive SIM WF_SRC TIDSRC).
    intros EXCLUSIVEEXTRA.
    inv WF_SRC. inv WF_MID. inv WF_TGT. inv SIM.
    eapply Forall_app_inv in NOREAD. des.
    eapply Forall_app_inv in FORALL1. des.
    eapply Forall_app_inv in TIMES. des.
    exploit Trace.steps_future; eauto.
    { ss. eapply WF1; eauto. } i. des.
    exploit Thread.step_future; eauto. i. des. ss.
    assert (CONSISTENT1: Local.promise_consistent lc3).
    { destruct (classic (e0 = ThreadEvent.failure)) as [EQ|NEQ].
      { subst. inv STEP; inv STEP0. ss. inv LOCAL. inv LOCAL0. auto. }
      specialize (CONSISTENT NEQ).
      eapply pf_consistent_super_strong_consistent in CONSISTENT; eauto.
      eapply consistent_promise_consistent in CONSISTENT; eauto. }
    assert (CONSTSIENT0: Local.promise_consistent e2.(Thread.local)).
    { eapply step_promise_consistent in STEP; eauto. }
    exploit sim_thread_steps_silent; eauto; ss.
    { eapply list_Forall_sum.
      { eapply list_Forall_sum.
        { eapply FORALL0. }
        { eapply SILENT. }
        { i. eapply (conj SAT0 SAT1). }
      }
      { eapply FORALL1. }
      { i. ss. des. splits; auto. }
    }
    { eapply WF0. }
    { eapply WF0. }
    { eapply WF; eauto. }
    { eapply WF0; eauto. }
    { eapply WF1; eauto. }
    i. des.
    { admit. }
  Admitted.

End SIM.
