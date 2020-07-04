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

Lemma jsim_event_sim_event
  :
    JSim.sim_event <2= sim_event.
Proof. ii. inv PR; econs. Qed.

Lemma promise_writing_event_racy
      loc from ts val released e (lc: Local.t)
      (WRITING : promise_writing_event loc from ts val released e)
  :
    racy_write loc ts lc e.
Proof.
  inv WRITING; econs; eauto.
Qed.

Lemma jsim_memory_concrete_promised mem_src mem_tgt
      (MEM: SimMemory.sim_memory mem_src mem_tgt)
  :
    concrete_promised mem_tgt <2= concrete_promised mem_src.
Proof.
  ii. inv PR. eapply MEM in GET.  des. inv MSG. econs; eauto.
Qed.

Lemma sim_memory_concrete_promised_later mem_src mem_tgt loc ts
      (MEM: SimMemory.sim_memory mem_src mem_tgt)
      (CLOSED: Memory.closed mem_tgt)
      (PROMISED: concrete_promised mem_src loc ts)
  :
    exists ts_tgt,
      (<<PROMISED: concrete_promised mem_tgt loc ts_tgt>>) /\
      (<<TS: Time.le ts ts_tgt>>).
Proof.
  inv PROMISED. dup GET. apply memory_get_ts_strong in GET. des; subst.
  { exists Time.bot. splits.
    { econs. eapply CLOSED. }
    { refl. }
  }
  inv MEM. exploit (proj1 (COVER loc ts)).
  { econs; eauto. econs; ss. refl. }
  i. inv x0. destruct msg.
  { inv ITV. ss. exists to. splits; auto. econs; eauto. }
  { eapply RESERVE in GET. exploit Memory.get_disjoint.
    { eapply GET. }
    { eapply GET0. }
    i. des; clarify. exfalso. eapply x0; eauto. econs; ss. refl.
  }
Qed.

Lemma jsim_joined_promises_covered prom_src prom_tgt view
      (SIM: JSim.sim_joined_promises view prom_src prom_tgt)
  :
    forall loc ts, covered loc ts prom_src <-> covered loc ts prom_tgt.
Proof.
  split; i.
  { inv H. specialize (SIM loc to). rewrite GET in *. inv SIM; ss.
    { econs; eauto. }
    { econs; eauto. }
  }
  { inv H. specialize (SIM loc to). rewrite GET in *. inv SIM; ss.
    { econs; eauto. }
    { econs; eauto. }
  }
Qed.

Lemma cap_flex_sim_memory mem_src mem_tgt cap_src cap_tgt tm
      (TMSRC: forall loc : Loc.t, Time.lt (Memory.max_ts loc mem_src) (tm loc))
      (MEM: SimMemory.sim_memory mem_src mem_tgt)
      (CAPSRC: cap_flex mem_src cap_src tm)
      (CAPTGT: cap_flex mem_tgt cap_tgt tm)
      (MEMSRC: Memory.closed mem_src)
      (MEMTGT: Memory.closed mem_tgt)
  :
    SimMemory.sim_memory cap_src cap_tgt.
Proof.
  assert (TMTGT: forall loc : Loc.t, Time.lt (Memory.max_ts loc mem_tgt) (tm loc)).
  { i. erewrite <- SimMemory.sim_memory_max_ts; eauto. }
  dup MEM. inv MEM.
  econs.
  { i. erewrite <- (@cap_flex_covered mem_src cap_src); eauto.
    erewrite <- (@cap_flex_covered mem_tgt cap_tgt); eauto. }
  { i. eapply cap_flex_inv in GET; eauto. des; subst.
    { exploit MSG; eauto. i. des.
      eapply CAPSRC in GET0. esplits; eauto. }
    { exploit SimMemory.sim_memory_adjacent_tgt; eauto. i. des.
      eapply CAPSRC in x0; eauto. }
    { esplits; eauto.
      erewrite CAPSRC.(cap_flex_back); eauto. }
  }
  { i. split; intros GET.
    { eapply (@cap_flex_inv mem_src cap_src) in GET; eauto. des; subst.
      { erewrite RESERVE in GET; eauto.
        eapply CAPTGT.(cap_flex_le); eauto. }
      { exploit SimMemory.sim_memory_adjacent_src; eauto. i. des.
        eapply CAPTGT in x0; eauto. }
      { erewrite SimMemory.sim_memory_max_ts; eauto.
        eapply CAPTGT.(cap_flex_back). }
    }
    { eapply (@cap_flex_inv mem_tgt cap_tgt) in GET; eauto. des; subst.
      { erewrite <- RESERVE in GET; eauto.
        eapply CAPSRC.(cap_flex_le); eauto. }
      { exploit SimMemory.sim_memory_adjacent_tgt; eauto. i. des.
        eapply CAPSRC in x0; eauto. }
      { erewrite <- SimMemory.sim_memory_max_ts; eauto.
        eapply CAPSRC.(cap_flex_back). }
    }
  }
Qed.

Lemma joined_memory_cap_flex views mem cap tm
      (JOINED: joined_memory views mem)
      (TM: forall loc, Time.lt (Memory.max_ts loc mem) (tm loc))
      (CAP: cap_flex mem cap tm)
      (CLOSED: Memory.closed mem)
  :
    joined_memory views cap.
Proof.
  inv JOINED. econs.
  - i. eapply cap_flex_inv in GET; eauto. des; eauto; clarify.
  - i. exploit ONLY; eauto. i. des.
    eapply CAP in GET; eauto.
  - i. eapply List.Forall_impl; try apply CLOSED0; eauto.
    i. ss. eapply Memory.future_weak_closed_view; eauto.
    eapply cap_flex_future_weak; eauto.
Qed.

Lemma sim_memory_concrete_promise_max_timemap mem_src mem_tgt
      views prom_src prom_tgt max
      (MAX: concrete_promise_max_timemap mem_src prom_src max)
      (MEM: SimMemory.sim_memory mem_src mem_tgt)
      (PROM: JSim.sim_joined_promises views prom_src prom_tgt)
      (PROMSRC: Memory.le prom_src mem_src)
      (PROMTGT: Memory.le prom_tgt mem_tgt)
      (MEMSRC: Memory.closed mem_src)
      (MEMTGT: Memory.closed mem_tgt)
  :
    concrete_promise_max_timemap mem_tgt prom_tgt max.
Proof.
  ii. specialize (MAX loc). inv MAX. guardH EXISTS. econs.
  { unguard. des.
    { left. exploit sim_memory_concrete_promised_later; eauto.
      { econs; eauto. }
      i. des. inv PROMISED. inv TS.
      { exfalso. eapply MEM in GET0. des. inv MSG.
        eapply CONCRETE in GET1. timetac. }
      { inv H. esplits; eauto.  }
    }
    { specialize (PROM loc (max loc)). rewrite GET in *. inv PROM; eauto. }
  }
  { i. eapply MEM in GET. des; eauto. inv MSG. eauto. }
  { i. specialize (PROM loc to). rewrite GET in *. inv PROM; eauto. }
Qed.

Lemma jsim_event_write_not_in e_src e_tgt (P_src P_tgt: Loc.t -> Time.t -> Prop)
      (WRITE: write_not_in P_tgt e_tgt)
      (EVENT: JSim.sim_event e_src e_tgt)
      (IMPL: forall loc ts (SAT: P_src loc ts), P_tgt loc ts)
  :
    write_not_in P_src e_src.
Proof.
  inv EVENT; ss.
  { des_ifs.
    { inv KIND; ss. }
    ii. eapply WRITE; eauto.
  }
  { ii. eapply WRITE; eauto. }
  { ii. eapply WRITE; eauto. }
Qed.

Lemma tevent_ident_map f e fe
      (MAP: tevent_map f fe e)
      (IDENT: forall loc to fto (MAP: f loc to fto), to = fto)
  :
    sim_event e fe.
Proof.
  inv MAP; try econs; eauto.
  { eapply IDENT in FROM. eapply IDENT in TO. subst. econs; eauto. }
  { eapply IDENT in TO. subst. econs; eauto. }
  { eapply IDENT in FROM. eapply IDENT in TO. subst. econs; eauto. }
  { eapply IDENT in FROM. eapply IDENT in TO. subst. econs; eauto. }
Qed.

Lemma readable_not_exist_racy lc mem loc ts released ord
      (READABLE: TView.readable (TView.cur (Local.tview lc)) loc ts released ord)
      (CLOSED: TView.closed lc.(Local.tview) mem)
      (NOTEXIST: ~ concrete_promised mem loc ts)
  :
    Time.lt
      (if Ordering.le Ordering.relaxed ord
       then View.rlx (TView.cur (Local.tview lc)) loc
       else View.pln (TView.cur (Local.tview lc)) loc) ts.
Proof.
  inv READABLE. des_ifs.
  { specialize (RLX eq_refl). destruct RLX; auto. inv H.
    inv CLOSED. inv CUR. specialize (RLX loc).
    des. exfalso. eapply NOTEXIST. econs; eauto. }
  { destruct PLN; auto. inv H.
    inv CLOSED. inv CUR. specialize (PLN loc).
    des. exfalso. eapply NOTEXIST. econs; eauto. }
Qed.

Lemma racy_read_mon loc ts lc0 lc1 e0 e1
      (RACY: racy_read loc ts lc1 e1)
      (LOCAL: TView.le lc0.(Local.tview) lc1.(Local.tview))
      (EVENT: sim_event e0 e1)
  :
    racy_read loc ts lc0 e0.
Proof.
  inv RACY; inv EVENT; econs; eauto.
  { des_ifs.
    { eapply TimeFacts.le_lt_lt; eauto. eapply LOCAL. }
    { eapply TimeFacts.le_lt_lt; eauto. eapply LOCAL. }
  }
  { des_ifs.
    { eapply TimeFacts.le_lt_lt; eauto. eapply LOCAL. }
    { eapply TimeFacts.le_lt_lt; eauto. eapply LOCAL. }
  }
Qed.


Section SIM.

  Variable L: Loc.t -> bool.
  Variable times: Loc.t -> Time.t -> Prop.
  Hypothesis WO: forall loc, well_ordered (times loc).
  Hypothesis INCR: forall nat loc, times loc (incr_time_seq nat).

  Lemma later_timemap_exists (tm: TimeMap.t)
    :
      exists max,
        (<<LT: forall loc, Time.lt (tm loc) (max loc)>>) /\
        (<<IN: forall loc, times loc (max loc)>>).
  Proof.
    hexploit (@choice
                Loc.t Time.t
                (fun loc ts =>
                   (<<LT: Time.lt (tm loc) ts>>) /\
                   (<<IN: times loc ts>>))).
    { i. hexploit (incr_time_seq_diverge (tm x)). i. des. esplits; eauto. }
    intros [max SPEC]. des. exists max. splits; auto.
    { eapply SPEC; eauto. }
    { eapply SPEC; eauto. }
  Qed.

  Lemma cap_flex_memory_times_wf mem cap tm
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

  Record pi_consistent
         (self: Loc.t -> Time.t -> Prop)
         (pl: list (Loc.t * Time.t))
         (mem_src: Memory.t)
         lang (e0:Thread.t lang)
    : Prop :=
    {
      pi_consistent_promises:
        forall loc ts, self loc ts <-> List.In (loc, ts) pl;
      pi_consistent_no_dup:
        NoDup pl;
      pi_consistent_certify:
        forall mem1 tm sc
               (pl0 pl1: list (Loc.t * Time.t))
               (ploc: Loc.t) (pts: Time.t)
               (FUTURE: Memory.future_weak e0.(Thread.memory) mem1)
               (CLOSED: Memory.closed mem1)
               (LOCAL: Local.wf e0.(Thread.local) mem1)
               (PLIST: pl = pl0 ++ (ploc, pts) :: pl1)
        ,
        exists ftr e1,
          (<<STEPS: Trace.steps ftr (Thread.mk _ e0.(Thread.state) e0.(Thread.local) sc mem1) e1>>) /\
          (<<EVENTS: List.Forall (fun em => <<SAT: (promise_free
                                                      /1\ no_sc
                                                      /1\ no_read_msgs (fun loc ts => ~ (covered loc ts e0.(Thread.local).(Local.promises) \/ concrete_promised mem_src loc ts \/ Time.lt (tm loc) ts))
                                                      /1\ wf_time_evt times
                                                      /1\ write_not_in (fun loc ts => (<<TS: Time.le ts (tm loc)>>) /\ (<<PROM: ~ covered loc ts e0.(Thread.local).(Local.promises)>>))
                                                   ) (snd em)>> /\ <<TAU: ThreadEvent.get_machine_event (snd em) = MachineEvent.silent>>) ftr >>) /\
          (<<GOOD: good_future tm mem1 e1.(Thread.memory)>>) /\
          (<<SC: e1.(Thread.sc) = sc>>) /\
          (__guard__((exists st',
                         (<<LOCAL: Local.failure_step e1.(Thread.local)>>) /\
                         (<<FAILURE: Language.step lang ProgramEvent.failure (@Thread.state lang e1) st'>>)) \/
                     ((<<PROMISES: forall loc ts (PROM: List.In (loc, ts) (pl0 ++ [(ploc, pts)])),
                          Memory.get loc ts e1.(Thread.local).(Local.promises) = None>>) /\
                      (exists e_write,
                          (<<FINAL: final_event_trace e_write ftr>>) /\
                          (<<WRITING: writing_event ploc pts e_write>>)))));
    }.

  Lemma pi_consistent_mon self pl mem_src0 mem_src1 lang
        st lc sc0 mem0 sc1 mem1
        (CONSISTENT: pi_consistent pl self mem_src0 (Thread.mk lang st lc sc0 mem0))
        (FUTURETGT: Memory.future_weak mem0 mem1)
        (FUTURESRC: Memory.future_weak mem_src0 mem_src1)
    :
      pi_consistent pl self mem_src1 (Thread.mk lang st lc sc1 mem1).
  Proof.
    inv CONSISTENT. ss. econs; eauto.
    ii. ss. exploit pi_consistent_certify0.
    { transitivity mem1; eauto. }
    { eauto. }
    { eauto. }
    { eauto. }
    i. des. ss. esplits; eauto.
    eapply List.Forall_impl; eauto. i. ss. des. splits; auto.
    eapply no_read_msgs_mon; eauto. ii. des; eauto.
    eapply memory_future_concrete_promised in H; eauto.
  Qed.

  Inductive sim_configuration
            (tids: Ident.t -> Prop)
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
          (<<EXTRA: forall loc ts from, ~ extra tid loc ts from>>) /\
          (<<PLS: proml tid = []>>))
      (MEMPF: sim_memory L times (all_promises (fun _ => True) prom) (all_extra (fun _ => True) extra) mem_src mem_mid)
      (SCPF: TimeMap.le sc_src sc_tgt)

      (JOINED: forall loc ts (NLOC: ~ L loc), List.Forall (fun vw => Memory.closed_view vw mem_src) (views loc ts))
      (MEMJOIN: SimMemory.sim_memory mem_mid mem_tgt)
      (MEMWF: memory_times_wf times mem_mid)
      (CONSISTENT: forall tid lang st lc
                          (IN: tids tid)
                          (GET: IdentMap.find tid ths_tgt = Some (existT _ lang st, lc)),
          pi_consistent (prom tid) (proml tid) mem_src (Thread.mk lang st lc sc_tgt mem_tgt))
    :
      sim_configuration
        tids views prom extra proml
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
        (<<THREAD: sim_thread_strong
                     views1 prom_self1 prom_others extra_self1 extra_others
                     th_src1 th_mid1 th_tgt1>>) /\
        (<<EVENTJOIN: JSim.sim_event e_mid e_tgt>>) /\
        (<<JOINED: forall loc ts (NLOC: ~ L loc), List.Forall (fun vw => Memory.closed_view vw th_src1.(Thread.memory)) (views1 loc ts)>>) /\
        (<<TRACE: sim_trace L tr (Some (th_tgt0.(Thread.local), e_tgt))>>) /\
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
    { eapply sim_trace_sim_event_sim_trace; eauto.
      { dep_inv JTHREAD. inv LOCAL0. ss. }
      { eapply jsim_event_sim_event; eauto. }
    }
    { inv STEP. ss. hexploit step_memory_times_wf; eauto. inv EVENT0; ss. }
  Qed.

  Lemma sim_thread_step_event
        views0 prom_self0 prom_others extra_self0 extra_others
        lang th_src0 th_mid0 th_tgt0 th_tgt1 pf_tgt e_tgt
        (STEPTGT: Thread.step pf_tgt e_tgt th_tgt0 th_tgt1)
        (THREAD: @sim_thread_strong
                   views0 prom_self0 prom_others extra_self0 extra_others
                   lang th_src0 th_mid0 th_tgt0)
        (WFTIME: wf_time_evt times e_tgt)
        (NOREAD: no_read_msgs prom_others e_tgt)
        (EVENT: ThreadEvent.get_machine_event e_tgt <> MachineEvent.silent)

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
        (<<THREAD: sim_thread_strong
                     views1 prom_self1 prom_others extra_self1 extra_others
                     th_src1 th_mid1 th_tgt1>>) /\
        (<<JOINED: forall loc ts (NLOC: ~ L loc), List.Forall (fun vw => Memory.closed_view vw th_src1.(Thread.memory)) (views1 loc ts)>>) /\
        (<<MEMWF: memory_times_wf times th_mid1.(Thread.memory)>>)
  .
  Proof.
    hexploit sim_thread_jsim_thread; eauto.
    { eapply sim_thread_strong_sim_thread; eauto. }
    intros JTHREAD.
    exploit JSim.sim_thread_step; eauto. i. des.
    dep_inv THREAD. destruct th1_src. ss.
    hexploit sim_thread_step_event_strong; try apply STEP; eauto.
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
      exists th_mid1 th_src1 views1 prom_self1 extra_self1 tr_src tr_mid,
        (<<STEPMID: JThread.rtc_tau th_mid0 th_mid1 views0 views1>>) /\
        (<<STEPMIDTRACE: Trace.steps tr_mid th_mid0 th_mid1>>) /\
        (<<TRACEMID: List.Forall2 (fun lce_mid lce_tgt => JSim.sim_event (snd lce_mid) (snd lce_tgt)) tr_mid tr_tgt>>) /\
        (<<STEPSRC: Trace.steps tr_src th_src0 th_src1>>) /\
        (<<THREAD: sim_thread_strong
                     views1 prom_self1 prom_others extra_self1 extra_others
                     th_src1 th_mid1 th_tgt1>>) /\
        (<<JOINED: forall loc ts (NLOC: ~ L loc), List.Forall (fun vw => Memory.closed_view vw th_src1.(Thread.memory)) (views1 loc ts)>>) /\
        (<<TRACE: sim_traces L tr_src tr_tgt>>) /\
        (<<MEMWF: memory_times_wf times th_mid1.(Thread.memory)>>)
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
      { i. ss. eapply JOINED in NLOC. eapply List.Forall_impl; eauto.
        ii. ss. eapply Memory.future_closed_view in H; eauto.
        eapply reserve_future_future; eauto. }
      { replace tr with (tr ++ []); auto.
        { econs 3.
          { econs. }
          { eapply reserving_r_sim_trace with (tr_src:=[]); eauto. econs. }
        }
        { eapply List.app_nil_r. }
      }
    }
    i. subst. inv EVENTS. ss. des.
    hexploit Thread.step_future; try apply STEP; eauto. i. des.
    exploit sim_thread_step_silent; eauto.
    { eapply Trace.steps_promise_consistent; eauto. } i. des.
    hexploit JThread.step_future; try apply STEPMID; eauto. i. des.
    hexploit Trace.steps_future; try apply STEPSRC; eauto. i. des.
    eapply sim_thread_strong_sim_thread in THREAD0. exploit IHSTEPTGT; eauto.
    { i. eapply EXCLUSIVE in OTHER. des.
      eapply unchangable_trace_steps_increase in UNCH; eauto. }
    { i. eapply EXCLUSIVEEXTRA in OTHER. des.
      eapply unchangable_trace_steps_increase in OTHER; eauto. }
    i. des. esplits; try apply THREAD1; eauto.
    { econs; eauto. inv EVENTJOIN; ss. }
    { econs 2.
      { eapply JThread.step_thread_step; eauto. }
      { apply STEPMIDTRACE. }
      { ss. }
    }
    { econs; eauto. }
    { eapply Trace.steps_trans; eauto. }
    { econs 2; eauto. }
  Qed.

  Lemma sim_configuration_sim_thread tids views prom extra
        (c_src c_mid c_tgt: Configuration.t)
        tid lang st lc_tgt
        (SIM: sim_configuration tids views prom extra c_src c_mid c_tgt)
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
        tids views prom extra c_src c_mid c_tgt
        (SIM: sim_configuration tids views prom extra c_src c_mid c_tgt)
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
        tids views prom extra c_src c_mid c_tgt
        (SIM: sim_configuration tids views prom extra c_src c_mid c_tgt)
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
        tids views prom extra c_src c_mid c_tgt
        tid lang st lc_src
        (SIM: sim_configuration tids views prom extra c_src c_mid c_tgt)
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
        tids views prom extra c_src c_mid c_tgt
        tid lang st lc_src
        (SIM: sim_configuration tids views prom extra c_src c_mid c_tgt)
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

  Lemma pf_consistent_pi_consistent
        (prom_others prom_self: Time.t -> Time.t -> Prop)
        lang (st_src st_mid st_tgt: Language.state lang)
        lc_tgt mem_src mem_tgt sc_tgt
        tr_cert ths_tgt
        (CONFIGTGT: Configuration.wf (Configuration.mk ths_tgt sc_tgt mem_tgt))
        (CONSISTENT: pf_consistent_super_strong
                       (Thread.mk _ st_tgt lc_tgt sc_tgt mem_tgt)
                       tr_cert
                       times)
        (PROMOTHERS: forall loc ts (PROM: (prom_others \\2// prom_self) loc ts),
            exists from to val released,
              (<<GET: Memory.get loc to mem_tgt = Some (from, Message.concrete val released)>>) /\
              (<<TS: Time.le ts to>>))
        (PROMSELF: forall loc ts (PROM: prom_self loc ts),
            exists from val released,
              (<<GET: Memory.get loc ts lc_tgt.(Local.promises) = Some (from, Message.concrete val released)>>))
        (FORGET: forall loc ts
                        (PROMISED: concrete_promised mem_tgt loc ts),
            (<<PROMISED: concrete_promised mem_src loc ts>>) \/
            <<FORGET: (prom_others \\2// prom_self) loc ts>>)
        (NOREAD: List.Forall
                   (fun the => no_read_msgs
                                 prom_others
                                 (snd the)) tr_cert)
    :
      pi_consistent
        prom_self mem_src
        (Thread.mk lang st_tgt lc_tgt sc_tgt mem_tgt).
  Proof.
    exploit (@concrete_promise_max_timemap_exists mem_tgt (Local.promises lc_tgt)).
    { eapply CONFIGTGT. } intros [max MAX].
    ii. exploit CONSISTENT; eauto. i. ss. des. esplits; eauto.
    { eapply list_Forall_sum.
      { eapply EVENTS. }
      { instantiate (1:= fun the => no_read_msgs prom_others (snd the)).
        eapply List.Forall_forall. i.
        eapply list_Forall2_in in H; eauto. des.
        eapply List.Forall_forall in IN; eauto. ss.
        destruct x, a. ss. inv SAT; ss.
        { ii. replace fto with to in *; auto.
          eapply MAPIDENT; eauto.
          exploit PROMOTHERS.
          { left. eauto. } i. des.
          eapply MAX in GET; eauto.
        }
        { ii. replace ffrom with from in *; auto.
          eapply MAPIDENT; eauto.
          exploit PROMOTHERS.
          { left. eauto. } i. des.
          eapply MAX in GET; eauto.
        }
      }
      { ii. ss. des. splits; auto. eapply no_read_msgs_sum.
        { eapply SAT3. }
        { eapply SAT1. }
        i. ss. apply not_or_and in PR. des. apply not_or_and in PR0. des.
        destruct (classic (concrete_promised mem_tgt x1 x2)).
        { eapply FORGET in H. des; ss. right. destruct FORGET0; ss.
          exfalso. eapply PR. eapply PROMSELF in H. des.
          dup GET. econs; eauto. econs; eauto.
          eapply memory_get_ts_strong in GET. des; subst; auto.
          { inv LOCAL. erewrite BOT in GET0. ss. }
          { refl. }
        }
        { left. ii. des; ss. }
      }
    }
    { unguard. des; eauto. right. splits; auto. i.
      eapply PROMSELF in PROM. des. eapply WRITES in GET.
      des. esplits; eauto. eapply promise_writing_event_racy; eauto.
    }
  Qed.

  Lemma sim_thread_steps_mid
        views0
        lang (th_mid0 th_tgt0 th_tgt1: Thread.t lang) tr_tgt
        (STEPTGT: Trace.steps tr_tgt th_tgt0 th_tgt1)
        (THREAD: JSim.sim_thread views0 th_mid0 th_tgt0)

        (SCMID: Memory.closed_timemap th_mid0.(Thread.sc) th_mid0.(Thread.memory))
        (SCTGT: Memory.closed_timemap th_tgt0.(Thread.sc) th_tgt0.(Thread.memory))
        (MEMMID: Memory.closed th_mid0.(Thread.memory))
        (MEMTGT: Memory.closed th_tgt0.(Thread.memory))
        (LOCALMID: Local.wf th_mid0.(Thread.local) th_mid0.(Thread.memory))
        (LOCALTGT: Local.wf th_tgt0.(Thread.local) th_tgt0.(Thread.memory))

        (CONSISTENT: Local.promise_consistent th_tgt1.(Thread.local))

        (REL: joined_released
                views0 th_mid0.(Thread.local).(Local.promises) th_mid0.(Thread.local).(Local.tview).(TView.rel))
        (JOINEDMEM: joined_memory views0 th_mid0.(Thread.memory))
        (VIEWS: wf_views views0)
    :
      exists th_mid1 views1 tr_mid,
        (<<STEPMIDTRACE: Trace.steps tr_mid th_mid0 th_mid1>>) /\
        (<<TRACEMID: List.Forall2 (fun lce_mid lce_tgt => TView.le (fst lce_mid).(Local.tview) (fst lce_tgt).(Local.tview) /\ JSim.sim_event (snd lce_mid) (snd lce_tgt)) tr_mid tr_tgt>>) /\
        (<<THREAD: JSim.sim_thread views1 th_mid1 th_tgt1>>) /\

        (<<REL: joined_released
                views1 th_mid1.(Thread.local).(Local.promises) th_mid1.(Thread.local).(Local.tview).(TView.rel)>>) /\
        (<<JOINEDMEM: joined_memory views1 th_mid1.(Thread.memory)>>) /\
        (<<VIEWS: wf_views views1>>)
  .
  Proof.
    ginduction STEPTGT; i.
    { exists th_mid0, views0, []. splits; auto. }
    { subst. exploit Thread.step_future; eauto. i. des.
      exploit JSim.sim_thread_step; eauto.
      { eapply Trace.steps_promise_consistent; eauto. } i. des.
      exploit JThread.step_future; eauto. i. des.
      exploit IHSTEPTGT; try apply SIM; auto. i. des.
      eexists th_mid1, views2, _. esplits; eauto.
      { econs 2; eauto. eapply JThread.step_thread_step; eauto. }
      { econs; eauto. splits; auto. ss.
        dep_inv THREAD. inv LOCAL. ss. }
    }
  Qed.

  Lemma sim_thread_pf_consistent_super_strong
        lang (th_mid th_tgt: Thread.t lang)
        views tr
        (CONSISTENT: pf_consistent_super_strong th_tgt tr times)
        (MEMMID: Memory.closed th_mid.(Thread.memory))
        (MEMTGT: Memory.closed th_tgt.(Thread.memory))
        (LOCALMID: Local.wf th_mid.(Thread.local) th_mid.(Thread.memory))
        (LOCALTGT: Local.wf th_tgt.(Thread.local) th_tgt.(Thread.memory))
        (SCMID: Memory.closed_timemap th_mid.(Thread.sc) th_mid.(Thread.memory))
        (SCTGT: Memory.closed_timemap th_tgt.(Thread.sc) th_tgt.(Thread.memory))
        (JSIM: JSim.sim_thread views th_mid th_tgt)
        (JOINEDREL: joined_released views th_mid.(Thread.local).(Local.promises) th_mid.(Thread.local).(Local.tview).(TView.rel))
        (JOINEDMEM: joined_memory views th_mid.(Thread.memory))
        (WFVIEWS: wf_views views)
    :
      pf_consistent_super_strong th_mid tr times.
  Proof.
    eapply pf_consistent_super_strong_not_easy; eauto. ii.
    assert (CAPTMTGT: forall loc,
               Time.lt (Memory.max_ts loc (Thread.memory th_tgt)) (incr_time_seq (tm loc))).
    { i. erewrite <- SimMemory.sim_memory_max_ts; eauto. dep_inv JSIM. }
    exploit (@cap_flex_exists th_tgt.(Thread.memory) (fun loc => incr_time_seq (tm loc))); eauto.
    intros [cap_tgt CAPTGT]. des.
    exploit (@CONSISTENT cap_tgt (fun loc => incr_time_seq (tm loc)) TimeMap.bot max).
    { eapply cap_flex_future_weak; eauto. }
    { eapply cap_flex_closed; eauto. }
    { eapply cap_flex_wf; eauto. }
    { dep_inv JSIM. inv LOCAL.
      eapply sim_memory_concrete_promise_max_timemap; eauto.
      { eapply LOCALMID. }
      { eapply LOCALTGT. }
    }
    i. des. exploit sim_thread_steps_mid.
    { eauto. }
    { instantiate (1:=Thread.mk _ (Thread.state th_mid) (Thread.local th_mid) TimeMap.bot cap).
      dep_inv JSIM. econs; eauto.
      eapply cap_flex_sim_memory; eauto; ss. refl. }
    { ss. eapply Memory.closed_timemap_bot.
      eapply cap_flex_closed; eauto. }
    { ss. eapply Memory.closed_timemap_bot.
      eapply cap_flex_closed; eauto. }
    { eapply cap_flex_closed; eauto. }
    { eapply cap_flex_closed; eauto. }
    { eapply cap_flex_wf; eauto. }
    { eapply cap_flex_wf; eauto. }
    { eauto. }
    { ss. }
    { eapply joined_memory_cap_flex; eauto. ss. }
    { ss. }
    i. des. esplits; eauto.
    { eapply List.Forall_forall. i.
      eapply list_Forall2_in2 in H; eauto. des.
      eapply List.Forall_forall in IN; eauto. ss. des.
      destruct b, x. ss. inv SAT0; ss.
      inv KIND; ss. inv MSG0; ss. inv MSG; ss. inv RELEASED0; ss. }
    { eapply list_Forall2_compose.
      { eapply TRACE. }
      { eapply list_Forall2_rev. eapply TRACEMID. }
      i. ss. destruct a, b, c. ss. des.
      inv SAT2; inv SAT0; econs; ss. }
    { dep_inv THREAD. unguard. des.
      { left. esplits; eauto.
        eapply JSim.sim_local_failure; eauto. }
      { right. eapply JSim.sim_local_memory_bot; eauto. }
    }
  Qed.

  Lemma sim_thread_sim_configuration
        (consistent: bool)
        tids views0 prom extra
        (c_src c_mid c_tgt: Configuration.t)
        tid lang (st_src st_mid st_tgt: Language.state lang)
        lc_src lc_mid lc_tgt mem_src mem_mid mem_tgt sc_src sc_mid sc_tgt
        (CONFIG: sim_configuration tids views0 prom extra c_src c_mid c_tgt)
        views1 prom_self extra_self tr_cert ths_src ths_mid ths_tgt
        (VIEWSLE: views_le views0 views1)
        (JOINED: forall loc ts (NLOC: ~ L loc), List.Forall (fun vw => Memory.closed_view vw mem_src) (views1 loc ts))
        (MEMWF: memory_times_wf times mem_mid)
        (FUTURESRC: Memory.future_weak c_src.(Configuration.memory) mem_src)
        (FUTUREMID: Memory.future_weak c_mid.(Configuration.memory) mem_mid)
        (FUTURETGT: Memory.future_weak c_tgt.(Configuration.memory) mem_tgt)
        (CONFIGTGT: Configuration.wf (Configuration.mk ths_tgt sc_tgt mem_tgt))
        (CONFIGMID: JConfiguration.wf views1 (Configuration.mk ths_mid sc_mid mem_mid))
        (CONSISTENT: ternary consistent (pf_consistent_super_strong
                                           (Thread.mk _ st_tgt lc_tgt sc_tgt mem_tgt)
                                           tr_cert
                                           times) True)
        (NOREAD: ternary consistent (List.Forall
                                       (fun the => no_read_msgs
                                                     (all_promises (fun tid' => tid <> tid') prom)
                                                     (snd the)) tr_cert) True)
        (THREAD:
           sim_thread
             views1
             prom_self
             (all_promises (fun tid' => tid <> tid') prom)
             extra_self
             (all_extra (fun tid' => tid <> tid') extra)
             (Thread.mk _ st_src lc_src sc_src mem_src)
             (Thread.mk _ st_mid lc_mid sc_mid mem_mid)
             (Thread.mk _ st_tgt lc_tgt sc_tgt mem_tgt))
        (THSSRC:
           forall tid',
             IdentMap.find tid' ths_src =
             if (Ident.eq_dec tid' tid)
             then Some (existT _ lang st_src, lc_src)
             else IdentMap.find tid' c_src.(Configuration.threads))
        (THSMID:
           forall tid',
             IdentMap.find tid' ths_mid =
             if (Ident.eq_dec tid' tid)
             then Some (existT _ lang st_mid, lc_mid)
             else IdentMap.find tid' c_mid.(Configuration.threads))
        (THSTGT:
           forall tid',
             IdentMap.find tid' ths_tgt =
             if (Ident.eq_dec tid' tid)
             then Some (existT _ lang st_tgt, lc_tgt)
             else IdentMap.find tid' c_tgt.(Configuration.threads))
    :
      sim_configuration
        (ternary consistent tids (fun tid' => tids tid' /\ tid' <> tid))
        views1
        (fun tid' => if (Ident.eq_dec tid' tid) then prom_self else (prom tid'))
        (fun tid' => if (Ident.eq_dec tid' tid) then extra_self else (extra tid'))
        (Configuration.mk ths_src sc_src mem_src)
        (Configuration.mk ths_mid sc_mid mem_mid)
        (Configuration.mk ths_tgt sc_tgt mem_tgt)
  .
  Proof.
    dep_inv THREAD. dep_inv CONFIG. econs; auto.
    { i. erewrite THSSRC. erewrite THSMID. des_ifs. }
    { i. erewrite THSMID. erewrite THSTGT. des_ifs.
      eapply option_rel_mon; try apply THSJOIN.
      i. eapply JSim.sim_statelocal_le; eauto. }
    { ii. erewrite THSSRC in NONE. des_ifs. eauto. }
    { replace (all_promises
                 (fun _ => True)
                 (fun tid' => if LocSet.Facts.eq_dec tid' tid then prom_self else prom tid'))
        with
          (all_promises (fun tid' => tid <> tid') prom \\2// prom_self); cycle 1.
      { extensionality loc. extensionality ts.
        apply Coq.Logic.PropExtensionality.propositional_extensionality. split; i.
        { destruct H.
          { inv H. eapply all_promises_intro with (tid:=tid0); ss. des_ifs. }
          { eapply all_promises_intro with (tid:=tid); ss. des_ifs. }
        }
        { inv H. unguard. des_ifs; auto. econs; eauto. }
      }
      replace (all_extra
                 (fun _ => True)
                 (fun tid' => if LocSet.Facts.eq_dec tid' tid then extra_self else extra tid'))
        with
          (all_extra (fun tid' => tid <> tid') extra \\3// extra_self); cycle 1.
      { extensionality loc. extensionality ts. extensionality from.
        apply Coq.Logic.PropExtensionality.propositional_extensionality. split; i.
        { destruct H.
          { inv H. eapply all_extra_intro with (tid:=tid0); ss. des_ifs. }
          { eapply all_extra_intro with (tid:=tid); ss. des_ifs. }
        }
        { inv H. unguard. des_ifs; auto. econs; eauto. }
      }
      auto.
    }
    { i. erewrite THSTGT in GET. unfold ternary in IN. des_ifs.
      { dep_clarify.
        eapply pf_consistent_pi_consistent; eauto.
        { i. exploit sim_memory_forget_concrete_promised.
          { eapply MEMPF. }
          { eapply PROM. }
          i. eapply sim_memory_concrete_promised_later in x0; eauto; cycle 1.
          { eapply CONFIGTGT. }
          des. inv PROMISED. esplits; eauto.
        }
        { i. inv LOCALPF. inv LOCALJOIN.
          set (CNT:=PROMS.(sim_promise_contents) loc ts). inv CNT; ss.
          specialize (PROMISES loc ts).  rewrite <- H in *. inv PROMISES. eauto. }
        { i. eapply jsim_memory_concrete_promised in PROMISED; cycle 1; eauto.
          apply NNPP. ii. apply not_or_and in H. des. eapply H.
          eapply sim_memory_concrete_promised; eauto. }
      }
      { dep_clarify. unguard. des; ss. }
      { eapply pi_consistent_mon; eauto. }
      { unguard. des. eapply pi_consistent_mon; eauto. }
    }
    { i. erewrite THSMID in GET. unfold ternary in IN. des_ifs.
      { dep_clarify.
        eapply pf_consistent_pi_consistent; eauto.
        { eapply CONFIGMID. }
        { eapply sim_thread_pf_consistent_super_strong; eauto; ss.
          { eapply CONFIGMID. }
          { eapply CONFIGTGT. }
          { eapply CONFIGMID; eauto. ss.
            instantiate (3:=tid). rewrite THSMID. des_ifs. }
          { eapply CONFIGTGT; eauto. ss.
            instantiate (3:=tid). rewrite THSTGT. des_ifs. }
          { eapply CONFIGMID. }
          { eapply CONFIGTGT. }
          { eapply CONFIGMID; eauto. ss.
            instantiate (3:=tid). rewrite THSMID. des_ifs. }
          { eapply CONFIGMID. }
          { eapply CONFIGMID. }
        }
        { i. exploit sim_memory_forget_concrete_promised.
          { eapply MEMPF. }
          { eapply PROM. }
          i. inv x0. esplits; eauto. refl. }
        { i. inv LOCALPF.
          set (CNT:=PROMS.(sim_promise_contents) loc ts). inv CNT; ss.
          esplits; eauto. }
        { i. apply NNPP. ii. apply not_or_and in H. des. eapply H.
          eapply sim_memory_concrete_promised; eauto. }
      }
      { dep_clarify. unguard. des. ss. }
      { eapply pi_consistent_mon; eauto. }
      { unguard. des. eapply pi_consistent_mon; eauto. }
    }
  Qed.

  Lemma sim_configuration_forget_src_not_concrete tids c_src c_mid c_tgt prom extra views
        (SIM: sim_configuration tids views prom extra c_src c_mid c_tgt)
        (WF_SRC: Configuration.wf c_src)
        (WF_MID: JConfiguration.wf views c_mid)
        (WF_TGT: Configuration.wf c_tgt)
        tid lang st lc_tgt
        (TID: IdentMap.find tid c_tgt.(Configuration.threads) = Some (existT _ lang st, lc_tgt))
    :
      forall loc ts
             (PROMISE: all_promises (fun tid': Ident.t => tid <> tid') prom loc ts),
        ~ ((covered loc ts lc_tgt.(Local.promises)) \/
           concrete_promised c_src.(Configuration.memory) loc ts \/ Time.lt (Memory.max_ts loc c_tgt.(Configuration.memory)) ts).
  Proof.
    inv SIM. ss. ii. inv PROMISE.
    assert (PROMISE: all_promises (fun _ => True) prom loc ts).
    { econs; eauto. }
    des.
    { exploit sim_configuration_forget_promise_exist; eauto. i. des. ss.
      dup THSJOIN. specialize (THSJOIN0 tid).
      specialize (THSPF tid0). specialize (THSJOIN tid0).
      unfold option_rel in *. unfold language in *. des_ifs.
      inv THSPF. inv LOCAL.
      set (CNT:=PROMS0.(sim_promise_contents) loc ts). inv CNT; ss.
      dep_inv THSJOIN. inv LOCAL.
      specialize (PROMISES loc ts). rewrite <- H2 in *. inv PROMISES.
      inv H. dep_inv THSJOIN0.
      assert (exists msg_tgt, <<GET: Memory.get loc to lc_src.(Local.promises) = Some (from0, msg_tgt)>>).
      { inv LOCAL. specialize (PROMISES loc to). ss.
        rewrite GET in PROMISES. inv PROMISES; eauto. } des.
      inv WF_MID. inv WF. ss. inv WF0.
      hexploit DISJOINT; eauto. i. inv H. ss. inv DISJOINT0.
      hexploit DISJOINT1; eauto. i. des.
      { eapply H; eauto. econs; ss; [|refl].
        symmetry in H6. apply memory_get_ts_strong in H6. des; auto. subst.
        inv ITV. ss. clear - FROM. exfalso.
        eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt; eauto. eapply Time.bot_spec. }
    }
    { erewrite sim_memory_concrete_promised in H; eauto. des. ss. }
    { erewrite <- SimMemory.sim_memory_max_ts in H; eauto.
      { set (CNT:=MEMPF.(sim_memory_contents) loc ts). inv CNT; ss.
        symmetry in H2. eapply Memory.max_ts_spec in H2. des. timetac. }
      { eapply WF_MID. }
      { eapply WF_TGT. }
    }
  Qed.

  Lemma sim_thread_consistent
        views prom_self prom_others extra_self extra_others
        lang th_src th_mid th_tgt tr
        (CONSISTENTTGT: pf_consistent_super_strong th_tgt tr times)
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
        (NOREAD: List.Forall (fun the => no_read_msgs prom_others (snd the)) tr)
        (EXCLUSIVE: forall loc ts (OTHER: prom_others loc ts),
            exists from msg, <<UNCH: unchangable th_src.(Thread.memory) th_src.(Thread.local).(Local.promises) loc ts from msg>>)
        (EXCLUSIVEEXTRA: forall loc ts from (OTHER: extra_others loc ts from),
            (<<UNCH: unchangable th_src.(Thread.memory) th_src.(Thread.local).(Local.promises) loc ts from Message.reserve>>))
        (JOINED: forall loc ts (NLOC: ~ L loc), List.Forall (fun vw => Memory.closed_view vw th_src.(Thread.memory)) (views loc ts))

        (REL: joined_released
                views th_mid.(Thread.local).(Local.promises) th_mid.(Thread.local).(Local.tview).(TView.rel))
        (JOINEDMEM: joined_memory views th_mid.(Thread.memory))
        (VIEWS: wf_views views)
    :
      pf_consistent L th_src.
  Proof.
    dup THREAD. dep_inv THREAD.
    hexploit sim_memory_strong_exists; eauto. i. des.
    assert (MEMSRCSTRONG: Memory.closed mem_src').
    { eapply sim_memory_same_closed; eauto.
      eapply sim_memory_strong_sim_memory; eauto. }

    hexploit (later_timemap_exists
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

    exploit (CONSISTENTTGT cap_tgt (Memory.max_timemap mem_src) sctgt); simpl.
    { ss. eapply cap_flex_future_weak; eauto. }
    { eapply cap_flex_closed; eauto. }
    { eapply cap_flex_wf; eauto. }
    { eauto. }
    i. des. ss.

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
    { eapply List.Forall_forall. i.
      cut (no_read_msgs prom_others (snd x)).
      { eapply List.Forall_forall in EVENTS; eauto. i. des. splits; auto. }
      destruct x. dup H. eapply list_Forall2_in in H; eauto. des. destruct a. ss.
      eapply List.Forall_forall in IN0; eauto. ss.
      eapply List.Forall_forall in H0; eauto. ss. des. inv SAT; auto; s.
      { intros PROM. replace fto with to in PROM; ss. eapply MAPIDENT; eauto.
        exploit sim_memory_forget_concrete_promised.
        { eapply MEMPF. }
        { left. eauto. }
        i. eapply sim_memory_concrete_promised_later in x0; eauto. des.
        inv PROMISED. etrans; eauto. eapply MAXCONCRETE in GET. auto.
      }
      { intros PROM. replace ffrom with from in PROM; ss. eapply MAPIDENT; eauto.
        exploit sim_memory_forget_concrete_promised.
        { eapply MEMPF. }
        { left. eauto. }
        i. eapply sim_memory_concrete_promised_later in x0; eauto. des.
        inv PROMISED. etrans; eauto. eapply MAXCONCRETE in GET. auto.
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
    { ss. eapply cap_flex_memory_times_wf; eauto. }
    { destruct x1.
      { des. inv LOCAL. auto. }
      { des. ii. erewrite PROMISES in *. erewrite Memory.bot_get in *. ss. }
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
    { ss. i. eapply JOINED in NLOC. eapply List.Forall_impl; eauto. i. ss.
      eapply Memory.future_weak_closed_view.
      { eapply cap_flex_future_weak; eauto. }
      eapply concrete_promised_le_closed_view; eauto.
      eapply concrete_messages_le_concrete_promised_le.
      eapply sim_memory_same_concrete_messages_le; eauto.
      eapply sim_memory_strong_sim_memory; eauto. }
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
    assert (SILENT: List.Forall
                      (fun the =>
                         ThreadEvent.get_machine_event (snd the) = MachineEvent.silent) ftr0).
    { eapply List.Forall_forall. i.
      eapply list_Forall2_in in H; eauto. i. des.
      eapply sim_traces_silent in TRACE0; eauto.
      { eapply tevent_map_same_machine_event in EVENT. erewrite EVENT.
        eapply List.Forall_forall in TRACE0; eauto. }
      { eapply List.Forall_impl; eauto. i. ss. des. auto. }
    }

    exists ftr0. dep_inv THREAD. esplits.
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
    { eapply sim_traces_pf in TRACE0; eauto.
      eapply List.Forall_forall. i.
      eapply list_Forall2_in in H; eauto. des. destruct a, x; ss.
      eapply List.Forall_forall in IN0; try apply TRACE0; eauto.
      inv EVENT; ss. ii. ss. clarify.
      exploit IN0; ss; eauto. i. inv MSG; ss. }
  Qed.


  Lemma configuration_step_not_consistent_future
        c1 tid tr lang st1 lc1 th2
        (TID: IdentMap.find tid (Configuration.threads c1) =
              Some (existT _ lang st1, lc1))
        (WF: Configuration.wf c1)
        (STEPS: Trace.steps
                  tr
                  (Thread.mk _ st1 lc1 c1.(Configuration.sc) c1.(Configuration.memory))
                  th2)
    :
      Configuration.wf
        (Configuration.mk
           (IdentMap.add
              tid
              (existT _ lang th2.(Thread.state), th2.(Thread.local))
              (Configuration.threads c1))
           th2.(Thread.sc) th2.(Thread.memory))
  .
  Proof.
    inv WF. inv WF0.
    exploit THREADS; ss; eauto. i.
    exploit Trace.steps_future; eauto. s. i. des.
    econs; ss. econs; i.
    { erewrite IdentMap.gsspec in TH1.
      erewrite IdentMap.gsspec in TH2. des_ifs; dep_clarify.
      { symmetry. eapply Trace.steps_disjoint; eauto. }
      { eapply Trace.steps_disjoint; eauto. }
      { eapply DISJOINT; [|eauto|eauto]. auto. }
    }
    { erewrite IdentMap.gsspec in TH. des_ifs; dep_clarify.
      eapply Trace.steps_disjoint; eauto.
    }
  Qed.

  Lemma step_sim_configuration consistent tids views0 prom0 extra0
        c_src0 c_mid0 c_tgt0 c_tgt1 e tid tr_tgt tr_cert
        (STEPTGT: @times_configuration_step times tr_tgt tr_cert e tid c_tgt0 c_tgt1)
        (SIM: sim_configuration tids views0 prom0 extra0 c_src0 c_mid0 c_tgt0)
        (NOREAD: List.Forall
                   (fun the => no_read_msgs
                                 (all_promises (fun tid' => tid <> tid') prom0)
                                 (snd the)) tr_tgt)
        (NOREADCERT: ternary consistent (List.Forall
                                           (fun the => no_read_msgs
                                                         (all_promises (fun tid' => tid <> tid') prom0)
                                                         (snd the)) tr_cert) True)
        (WF_SRC: Configuration.wf c_src0)
        (WF_MID: JConfiguration.wf views0 c_mid0)
        (WF_TGT: Configuration.wf c_tgt0)
    :
      exists tr_src c_src1 c_mid1 views1 prom1 extra1,
        (<<STEPMID: JConfiguration.step e tid c_mid0 c_mid1 views0 views1>>) /\
        (<<STEPSRC: ternary consistent
                            (pf_opt_step_trace L tr_src e tid c_src0 c_src1)
                            (Configuration.wf c_src1)>>) /\
        (<<MID:__guard__(
                   exists tr_mid,
                     (<<STEPMIDTIMED:
                        @times_configuration_step times tr_mid tr_cert e tid c_mid0 c_mid1>>) /\
                     (*                 exists lang st0 lc0 st1 lc1 tr_mid, *)
                     (* (<<TIDMID0: IdentMap.find tid c_mid0.(Configuration.threads) = Some (existT _ lang st0, lc0)>>) /\ *)
                     (* (<<TIDMID1: IdentMap.find tid c_mid1.(Configuration.threads) = Some (existT _ lang st1, lc1)>>) /\ *)
                     (* (<<STEPS: Trace.steps *)
                     (*             tr_mid *)
                     (*             (Thread.mk _ st0 lc0 c_mid0.(Configuration.sc) c_mid0.(Configuration.memory)) *)
                     (*             (Thread.mk _ st1 lc1 c_mid1.(Configuration.sc) c_mid1.(Configuration.memory))>>) /\ *)
                     (<<TRACEMID: List.Forall2 (fun lce flce => JSim.sim_event (snd lce) (snd flce)) tr_mid tr_tgt>>))>>) /\
        (<<TRACE: sim_traces L tr_src tr_tgt>>) /\
        __guard__(e = MachineEvent.failure \/
                  (<<SIM: sim_configuration (ternary consistent tids (fun tid' => tids tid' /\ tid' <> tid)) views1 prom1 extra1 c_src1 c_mid1 c_tgt1>>) /\
                  (<<PROM: forall tid' (NEQ: tid <> tid'), prom1 tid' = prom0 tid'>>) /\
                  (<<EXTRA: forall tid' (NEQ: tid <> tid'), extra1 tid' = extra0 tid'>>))
  .
  Proof.
    hexploit times_configuration_step_future; eauto. i. des.
    dep_inv STEPTGT.
    exploit sim_configuration_sim_thread; eauto. i. des.
    generalize (sim_configuration_forget_exclusive SIM WF_SRC TIDSRC).
    intros EXCLUSIVE.
    generalize (sim_configuration_extra_exclusive SIM WF_SRC TIDSRC).
    intros EXCLUSIVEEXTRA.
    dup WF_MID. dup WF_SRC. inv WF_SRC. inv WF_MID. inv WF_TGT. inv SIM.
    eapply Forall_app_inv in NOREAD. des.
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
    exploit JThread.tau_steps_future; eauto; ss.
    { eapply WF0; eauto. }
    { eapply WF0. }
    { eapply WF0. }
    i. des.
    exploit Trace.steps_future; eauto; ss.
    { eapply WF; eauto. }
    i. des.
    destruct (classic (ThreadEvent.get_machine_event e0 = MachineEvent.silent)) as [EQ|NEQ].
    { eapply sim_thread_strong_sim_thread in THREAD.
      exploit sim_thread_step_silent; eauto.
      { inv FORALL3. auto. }
      { inv FORALL2. auto. }
      { i. eapply EXCLUSIVE in OTHER. des. esplits.
        eapply unchangable_trace_steps_increase; eauto. }
      { i. eapply EXCLUSIVEEXTRA in OTHER. des. esplits.
        eapply unchangable_trace_steps_increase; eauto. }
      i. des. exists (tr_src ++ tr).
      hexploit JThread.step_future; eauto. i. des.
      hexploit Trace.steps_future; eauto. i. des.
      assert (SIMTRACE: sim_traces L (tr_src++tr) (tr' ++ [(e2.(Thread.local), e0)])).
      { eapply sim_traces_trans; eauto. replace tr with (tr++[]).
        { econs; eauto. econs. }
        { apply List.app_nil_r. }
      }
      assert (JSTEP: JConfiguration.step
                       (ThreadEvent.get_machine_event e0) tid
                       (Configuration.mk ths_mid sc_src mem_mid)
                       (Configuration.mk
                          (IdentMap.add
                             tid
                             (existT _ _ th_mid0.(Thread.state), th_mid0.(Thread.local)) ths_mid)
                          th_mid0.(Thread.sc) th_mid0.(Thread.memory)) views0 views2).
      { erewrite <- JSim.sim_event_machine_event; eauto. econs; eauto.
        { destruct th_mid0. eauto. }
        { i. dep_inv THREAD0. eapply JSim.sim_thread_consistent; eauto; ss.
          eapply pf_consistent_super_strong_consistent; eauto.
          eapply CONSISTENT. ii. subst. ss. }
      }
      assert (MID: List.Forall2 (fun lce flce => JSim.sim_event (snd lce) (snd flce)) (tr_mid ++ [(th_mid1.(Thread.local), e_mid)]) (tr' ++ [(Thread.local e2, e0)])).
      { eapply list_Forall2_app; eauto. }
      assert (STEPMIDTIMED: times_configuration_step
                              times
                              (tr_mid ++ [(th_mid1.(Thread.local), e_mid)])
                              tr_cert
                              (ThreadEvent.get_machine_event e0) tid
                              (Configuration.mk ths_mid sc_src mem_mid)
                              (Configuration.mk
                                 (IdentMap.add
                                    tid
                                    (existT _ _ th_mid0.(Thread.state), th_mid0.(Thread.local)) ths_mid)
                                 th_mid0.(Thread.sc) th_mid0.(Thread.memory))).
      { erewrite <- JSim.sim_event_machine_event; eauto.
        econs; try apply STEPMIDTRACE; eauto.
        { eapply List.Forall_forall. i.
          eapply list_Forall2_in2 in H; eauto. des.
          eapply List.Forall_forall in IN; try apply SILENT; eauto. ss.
          erewrite JSim.sim_event_machine_event; eauto. }
        { destruct th_mid0. eapply JThread.step_thread_step; eauto. }
        { i. hexploit CONSISTENT.
          { ii. subst. inv EVENTJOIN; ss. }
          i. eapply sim_thread_pf_consistent_super_strong in H; eauto.
          dep_inv THREAD0. }
        { i. subst. eapply CERTNIL; eauto. inv EVENTJOIN; auto. }
        { eapply List.Forall_forall. i.
          eapply list_Forall2_in2 in H; eauto. des. destruct b, x. ss.
          eapply List.in_app_or in IN. des.
          { eapply List.Forall_forall in IN; eauto. ss. inv SAT; auto. }
          { eapply List.Forall_forall in IN; eauto. ss. inv SAT; auto. }
        }
      }
      hexploit (list_match_rev (tr_src++tr)). i. des.
      { assert (tr_src = [] /\ tr = []).
        { split.
          { destruct tr_src; auto. ss. }
          { destruct tr; auto. destruct tr_src; ss. }
        } des. subst. inv STEPSRC; ss. inv STEPSRC0; ss.
        destruct th_mid0. esplits.
        { eauto. }
        { destruct consistent; ss.
          { rewrite EQ. econs 2; eauto. }
          { eauto. }
        }
        { unguard. ss. esplits; eauto. }
        { exploit sim_traces_trans; eauto. }
        { right. splits.
          { eapply (@sim_thread_sim_configuration consistent) with (tr_cert := tr_cert); eauto.
            { etrans; eauto. }
            { refl. }
            { ss. eapply Memory.future_future_weak. etrans; eauto. }
            { ss. eapply Memory.future_future_weak. etrans; eauto. }
            { ss. eapply JConfiguration.step_future; eauto. }
            { destruct consistent; ss.
              i. eapply CONSISTENT. ii. subst. ss. }
            { eapply sim_thread_strong_sim_thread. eauto. }
            { i. des_ifs. }
            { i. erewrite IdentMap.gsspec. des_ifs; eauto. }
            { i. erewrite IdentMap.gsspec. des_ifs; eauto. }
          }
          { i. ss. des_ifs. }
          { i. ss. des_ifs. }
        }
      }
      { hexploit Trace.steps_trans.
        { eapply STEPSRC. }
        { eapply STEPSRC0. } intros ALLSTEPS. rewrite H in ALLSTEPS. dup ALLSTEPS.
        eapply Trace.steps_separate in ALLSTEPS. des. inv STEPS1; clarify.
        inv STEPS2; ss. destruct th_src0, th_mid0. ss.
        assert (ALLSILENT: List.Forall
                             (fun the => ThreadEvent.get_machine_event (snd the) = MachineEvent.silent)
                             (tl_rev ++ [(th1.(Thread.local), e)])).
        { rewrite <- H. eapply Forall_app.
          { eapply sim_traces_silent; eauto. }
          { eapply sim_trace_silent; eauto. i. clarify. }
        }
        eapply Forall_app_inv in ALLSILENT. des. inv FORALL5; ss.
        assert (VSTEP: ternary consistent (pf_step_trace
                                             L
                                             (tr_src ++ tr)
                                             (ThreadEvent.get_machine_event e0) tid
                                             (Configuration.mk ths_src sc_src mem_src)
                                             (Configuration.mk
                                                (IdentMap.add
                                                   tid
                                                   (existT _ _ state, local) ths_src)
                                                sc memory)) True).
        { destruct consistent; ss. rewrite EQ.
          replace MachineEvent.silent with (ThreadEvent.get_machine_event e); auto.
          exploit sim_thread_consistent; eauto.
          { eapply CONSISTENT. ii. subst. clarify. }
          { i. ss. eapply EXCLUSIVE in OTHER. des.
            eapply unchangable_trace_steps_increase in ALLSTEPS0; eauto. }
          { i. ss. eapply EXCLUSIVEEXTRA in OTHER. des.
            eapply unchangable_trace_steps_increase in ALLSTEPS0; eauto. }
          i. des. econs; try apply STEP0; eauto.
          ii.
          eapply sim_traces_pf; eauto.
        }
        (* exploit pf_step_trace_future; try apply VSTEP; eauto. i. des. ss. *)
        esplits.
        { eauto. }
        { destruct consistent; ss.
          { econs 1; eauto. }
          { exploit configuration_step_not_consistent_future.
            { instantiate (4:=Configuration.mk ths_src sc_src mem_src).
              eapply TIDSRC. }
            { eauto. }
            { eapply Trace.steps_trans.
              { eapply STEPSRC. }
              { eapply STEPSRC0. }
            }
            ss.
          }
        }
        { unguard. ss. esplits; eauto. }
        { auto. }
        { right. splits.
          { eapply (@sim_thread_sim_configuration consistent); eauto.
            { etrans; eauto. }
            { ss. eapply Memory.future_future_weak. etrans; eauto. }
            { ss. eapply Memory.future_future_weak. etrans; eauto. }
            { ss. eapply Memory.future_future_weak. etrans; eauto. }
            { eapply JConfiguration.step_future; eauto. }
            { destruct consistent; ss. eapply CONSISTENT. ii. subst. ss. }
            { dup THREAD0. eapply sim_thread_strong_sim_thread. eauto. }
            { i. erewrite IdentMap.gsspec. des_ifs; eauto. }
            { i. erewrite IdentMap.gsspec. des_ifs; eauto. }
            { i. erewrite IdentMap.gsspec. des_ifs; eauto. }
          }
          { i. ss. des_ifs. }
          { i. ss. des_ifs. }
        }
      }
    }
    { exploit sim_thread_step_event; eauto.
      { inv FORALL3. auto. }
      { inv FORALL2. auto. }
      { i. eapply EXCLUSIVE in OTHER. des. esplits.
        eapply unchangable_trace_steps_increase; eauto. }
      { i. eapply EXCLUSIVEEXTRA in OTHER. des. esplits.
        eapply unchangable_trace_steps_increase; eauto. }
      i. des. hexploit JThread.step_future; eauto. i. des.
      hexploit Thread.step_future; eauto. i. des.
      assert (JSTEP: JConfiguration.step
                       (ThreadEvent.get_machine_event e0) tid
                       (Configuration.mk ths_mid sc_src mem_mid)
                       (Configuration.mk
                          (IdentMap.add
                             tid
                             (existT _ _ th_mid0.(Thread.state), th_mid0.(Thread.local)) ths_mid)
                          th_mid0.(Thread.sc) th_mid0.(Thread.memory)) views0 views2).
      { econs; eauto.
        { destruct th_mid0. eauto. }
        { i. dep_inv THREAD0. eapply JSim.sim_thread_consistent; eauto; ss.
          eapply pf_consistent_super_strong_consistent; eauto. }
      }
      assert (MID: List.Forall2 (fun lce flce => JSim.sim_event (snd lce) (snd flce)) (tr_mid ++ [(th_mid1.(Thread.local), e0)]) (tr' ++ [(Thread.local e2, e0)])).
      { eapply list_Forall2_app; eauto. econs; ss. clear - NEQ. destruct e0; ss. }
      assert (STEPMIDTIMED: times_configuration_step
                              times
                              (tr_mid ++ [(th_mid1.(Thread.local), e0)])
                              tr_cert
                              (ThreadEvent.get_machine_event e0) tid
                              (Configuration.mk ths_mid sc_src mem_mid)
                              (Configuration.mk
                                 (IdentMap.add
                                    tid
                                    (existT _ _ th_mid0.(Thread.state), th_mid0.(Thread.local)) ths_mid)
                                 th_mid0.(Thread.sc) th_mid0.(Thread.memory))).
      { erewrite <- JSim.sim_event_machine_event; eauto.
        econs; try apply STEPMIDTRACE; eauto.
        { eapply List.Forall_forall. i.
          eapply list_Forall2_in2 in H; eauto. des.
          eapply List.Forall_forall in IN; try apply SILENT; eauto. ss.
          erewrite JSim.sim_event_machine_event; eauto. }
        { destruct th_mid0. eapply JThread.step_thread_step; eauto. }
        { i. hexploit CONSISTENT; auto.
          i. eapply sim_thread_pf_consistent_super_strong in H; eauto.
          dep_inv THREAD0. }
        { eapply List.Forall_forall. i.
          eapply list_Forall2_in2 in H; eauto. des. destruct b, x. ss.
          eapply List.in_app_or in IN. des.
          { eapply List.Forall_forall in IN; eauto. ss. inv SAT; auto. }
          { eapply List.Forall_forall in IN; eauto. ss. inv SAT; auto. }
        }
        { clear - NEQ. destruct e0; ss. }
      }
      assert (VSTEP: ternary consistent (pf_step_trace
                                           L
                                           (tr_src ++ [(th_src1.(Thread.local), e0)])
                                           (ThreadEvent.get_machine_event e0) tid
                                           (Configuration.mk ths_src sc_src mem_src)
                                           (Configuration.mk
                                              (IdentMap.add
                                                 tid
                                                 (existT _ _ th_src0.(Thread.state), th_src0.(Thread.local)) ths_src)
                                              th_src0.(Thread.sc) th_src0.(Thread.memory))) True).
      { destruct consistent; ss. econs; eauto.
        { eapply sim_traces_silent; eauto. }
        { destruct th_src0. eauto. }
        { i. destruct th_src0. ss. eapply sim_thread_consistent; eauto.
          { i. ss. eapply EXCLUSIVE in OTHER. des.
            eapply unchangable_trace_steps_increase in STEPSRC; eauto.
            eapply unchangable_increase in STEPSRC0; eauto. }
          { i. ss. eapply EXCLUSIVEEXTRA in OTHER. des.
            eapply unchangable_trace_steps_increase in STEPSRC; eauto.
            eapply unchangable_increase in STEPSRC0; eauto. }
        }
        { eapply Forall_app.
          { eapply sim_traces_pf; eauto. }
          { econs; ss. eapply non_silent_pf in NEQ; eauto. }
        }
      }

      destruct th_src0, th_mid0. ss. esplits.
      { eauto. }
      { destruct consistent; ss.
        { econs 1; eauto. }
        { exploit configuration_step_not_consistent_future.
          { instantiate (4:=Configuration.mk ths_src sc_src mem_src).
            eapply TIDSRC. }
          { eauto. }
          { eapply Trace.steps_trans.
            { eapply STEPSRC. }
            { eapply Trace.steps_one. eapply STEPSRC0. }
          }
          ss.
        }
      }
      { unguard. ss. esplits; eauto. }
      { eapply sim_traces_trans; eauto.
        replace [(th_src1.(Thread.local), e0)] with ([(th_src1.(Thread.local), e0)]++[]); auto. econs 2; auto.
        { econs. }
        { econs 2.
          { eapply non_silent_pf; eauto. }
          { econs. }
          { refl. }
          { dep_inv THREAD. inv LOCALJOIN. inv LOCALPF. eauto. }
        }
      }
      { unguard. destruct (classic (e0 = ThreadEvent.failure)); subst; auto.
        right. splits.
        { eapply sim_thread_sim_configuration; eauto.
          { etrans; eauto. }
          { ss. eapply Memory.future_future_weak. etrans; eauto. }
          { ss. eapply Memory.future_future_weak. etrans; eauto. }
          { ss. eapply Memory.future_future_weak. etrans; eauto. }
          { eapply JConfiguration.step_future; eauto. }
          { destruct consistent; ss. dup THREAD0. eauto. }
          { eapply sim_thread_strong_sim_thread. eauto. }
          { i. erewrite IdentMap.gsspec. des_ifs; eauto. }
          { i. erewrite IdentMap.gsspec. des_ifs; eauto. }
          { i. erewrite IdentMap.gsspec. des_ifs; eauto. }
        }
        { i. ss. des_ifs. }
        { i. ss. des_ifs. }
      }
    }
  Qed.


  Lemma sim_configuration_no_promises_prom_extra_bot
        tids views prom extra
        c_src c_mid c_tgt tid lang st lc_tgt
        (SIM: sim_configuration tids views prom extra c_src c_mid c_tgt)
        (TIDTGT: IdentMap.find tid c_tgt.(Configuration.threads) = Some (existT _ lang st, lc_tgt))
        (PROMISE: lc_tgt.(Local.promises) = Memory.bot)
    :
      (<<PROM: prom tid = bot2>>) /\
      (<<EXTRA: extra tid = bot3>>).
  Proof.
    inv SIM. ss. specialize (THSPF tid). specialize (THSJOIN tid).
    unfold option_rel in *. des_ifs. inv THSPF. dep_inv THSJOIN. inv LOCAL. inv LOCAL0.
    split.
    { red. extensionality loc. extensionality ts.
      apply Coq.Logic.PropExtensionality.propositional_extensionality. split; i; ss.
      set (CNT:=PROMS.(sim_promise_contents) loc ts). inv CNT; ss.
      specialize (PROMISES loc ts). rewrite <- H2 in *. inv PROMISES; ss.
      erewrite Memory.bot_get in *. clarify. }
    { red. extensionality loc. extensionality ts. extensionality from.
      apply Coq.Logic.PropExtensionality.propositional_extensionality. split; i; ss.
      eapply PROMS.(sim_promise_wf) in H. des.
      set (CNT:=PROMS.(sim_promise_contents) loc from). inv CNT; ss.
      specialize (PROMISES loc from). rewrite <- H in *. inv PROMISES; ss.
      erewrite Memory.bot_get in *. clarify. }
  Qed.

  Lemma sim_configuration_certify tids views0 prom extra
        c_src0 c_mid0 c_tgt0 tid tm
        (SIM: sim_configuration tids views0 prom extra c_src0 c_mid0 c_tgt0)
        (WF_SRC: Configuration.wf c_src0)
        (WF_MID: JConfiguration.wf views0 c_mid0)
        (WF_TGT: Configuration.wf c_tgt0)
        (TIDS: tids tid)
    :
      exists tr_src tr_tgt c_src1 c_mid1 c_tgt1 views1 e,
        (<<STEPSRC: pf_opt_step_trace L tr_src e tid c_src0 c_src1>>) /\
        (<<STEPMID: JConfiguration.opt_step e tid c_mid0 c_mid1 views0 views1>>) /\
        (<<STEPTGT: @times_configuration_opt_step times tr_tgt [] e tid c_tgt0 c_tgt1>>) /\
        (<<TRACE: sim_traces L tr_src tr_tgt>>) /\
        __guard__((e = MachineEvent.failure) \/
                  (e = MachineEvent.silent /\
                   (<<FUTURE: good_future tm c_tgt0.(Configuration.memory) c_tgt1.(Configuration.memory)>>) /\
                   (<<SC: c_tgt1.(Configuration.sc) = c_tgt0.(Configuration.sc)>>) /\
                   (<<SIM: sim_configuration
                             tids views1
                             (fun tid' => if (Ident.eq_dec tid' tid) then bot2 else (prom tid'))
                             (fun tid' => if (Ident.eq_dec tid' tid) then bot3 else (extra tid'))
                             c_src1 c_mid1 c_tgt1>>) /\
                   (<<WRITES: forall loc ts (PROM: prom tid loc ts),
                       exists th e_write,
                         (<<INLOCS: L loc>>) /\
                         (<<RACY: racy_write loc ts th e_write>>) /\
                         (<<IN: List.In (th, e_write) tr_src>>)>>)))
  .
  Proof.
    destruct (IdentMap.find tid c_tgt0.(Configuration.threads)) as [[[lang_tgt st_tgt] lc_tgt]|] eqn:TIDTGT.
    { destruct (classic (exists loc ts, (prom tid loc ts))) as [EXIST|NONE]; cycle 1.
      { eexists [], [], c_src0, c_mid0, c_tgt0, views0, MachineEvent.silent.
        splits; auto.
        { econs 2; eauto. }
        { econs 2; eauto. }
        { econs. }
        { right. splits; auto.
          { refl. }
          { replace (fun tid': Ident.t => if (Ident.eq_dec tid' tid) then bot2 else (prom tid')) with prom; cycle 1.
            { extensionality tid'. extensionality loc. extensionality ts.
              apply Coq.Logic.PropExtensionality.propositional_extensionality.
              des_ifs. split; i; ss. eapply NONE; eauto. }
            replace (fun tid': Ident.t => if (Ident.eq_dec tid' tid) then bot3 else (extra tid')) with extra; cycle 1.
            { extensionality tid'. extensionality loc. extensionality ts. extensionality from.
              apply Coq.Logic.PropExtensionality.propositional_extensionality.
              des_ifs. split; i; ss.
              dup SIM. inv SIM. ss. specialize (THSPF tid). specialize (THSJOIN tid).
              rewrite TIDTGT in *. unfold option_rel in *. des_ifs.
              inv THSPF. inv LOCAL. eapply PROMS.(sim_promise_wf) in H. des.
              exfalso. eapply NONE; eauto. }
            auto.
          }
          { ii. exfalso. eapply NONE; eauto. }
        }
      }
      guardH EXIST.
      inv SIM. ss. exploit CONSISTENT; eauto.
      { refl. }
      { eapply WF_TGT. }
      { eapply WF_TGT; eauto. }
      instantiate (2:=TimeMap.join tm (fun loc => Time.incr (Memory.max_ts loc mem_tgt))). i. des. ss.
      assert (NOREAD: List.Forall
                        (fun the => no_read_msgs
                                      (all_promises (fun tid' => tid <> tid') prom)
                                      (snd the)) ftr).
      { eapply List.Forall_impl; eauto. i. ss. des. eapply no_read_msgs_mon; eauto.
        i. ss.
        hexploit sim_configuration_forget_src_not_concrete; eauto. i. ss.
        ii. eapply H. des; auto. right. right. eapply TimeFacts.le_lt_lt; eauto. etrans.
        { left. eapply Time.incr_spec. }
        { eapply Time.join_r. }
      }
      destruct x1; des.
      { destruct e1. ss.
        assert (STEPTGT: @times_configuration_step
                           times
                           (ftr++[(local, ThreadEvent.failure)])
                           []
                           MachineEvent.failure
                           tid
                           (Configuration.mk ths_tgt sc_tgt mem_tgt)
                           (Configuration.mk
                              (IdentMap.add tid (existT _ lang_tgt st', local) ths_tgt)
                              sc
                              memory)).
        { ss. replace MachineEvent.failure with
                  (ThreadEvent.get_machine_event ThreadEvent.failure); auto.
          econs; eauto; ss.
          { eapply List.Forall_impl in EVENTS; eauto. i. ss. des. auto. }
          { eapply Forall_app.
            { eapply List.Forall_impl in EVENTS; eauto. i. ss. des. auto. }
            { econs; ss. }
          }
        }
        exploit (@step_sim_configuration true); eauto.
        { eapply Forall_app.
          { eapply List.Forall_impl in NOREAD; eauto. }
          { econs; ss. }
        }
        { ss. }
        i. des. esplits; eauto.
        { econs 1. eauto. }
        { left. ss. }
      }
      { destruct e1; ss.
        assert (STEPTGT: @times_configuration_step
                           times
                           ftr
                           []
                           MachineEvent.silent
                           tid
                           (Configuration.mk ths_tgt sc_tgt mem_tgt)
                           (Configuration.mk
                              (IdentMap.add tid (existT _ lang_tgt state, local) ths_tgt)
                              sc
                              memory)).
        { hexploit (list_match_rev ftr). i. des; subst.
          { exfalso. unguard. des. exploit WRITES; eauto. i. des. ss. }
          destruct hd_rev as [th e].
          eapply Trace.steps_separate in STEPS. des.
          inv STEPS1; ss; clarify. inv STEPS; clarify.
          dup EVENTS. eapply Forall_app_inv in EVENTS. des.
          replace MachineEvent.silent with (ThreadEvent.get_machine_event e0); cycle 1.
          { inv FORALL2. ss. des. auto. }
          econs; eauto.
          { eapply List.Forall_impl; eauto. i. ss. des; auto. }
          { ii. exists [], (Thread.mk _ state local sc mem1). ss.
            exists (fun loc ts fts => ts = fts /\ Time.le ts (max loc)).
            splits; ss.
            { ii. des; subst. auto. }
            { ii. des. timetac. }
            { i. des; subst. timetac. }
            { refl. }
            { eapply Local.bot_promise_consistent; eauto. }
            { right. splits; auto. i. rewrite PROMISES in *.
              rewrite Memory.bot_get in *. clarify. }
          }
          { eapply List.Forall_impl; eauto. i. ss. des; auto. }
        }
        exploit (step_sim_configuration true); eauto.
        { ss. }
        i. des. eexists _, _, _, _, _, views1, _. esplits; eauto.
        { econs 1. eauto. }
        { unguard. des; ss.
          assert (FORALL:  List.Forall
                             (fun em =>
                                (write_not_in
                                   (fun loc0 ts0 =>
                                      Time.le ts0 (TimeMap.join tm (fun loc1 => Time.incr (Memory.max_ts loc1 mem_tgt)) loc0) /\ ~ covered loc0 ts0 mem_mid) /1\ no_sc) (snd em)) tr_mid).
          { eapply List.Forall_forall. i.
            eapply list_Forall2_in2 in H; eauto. des.
            eapply List.Forall_forall in IN; try apply EVENTS. ss.
            destruct b, x. ss. des. splits.
            { eapply jsim_event_write_not_in; eauto. i. ss. des. split; auto.
              ii. eapply SAT6. eapply memory_le_covered in H; cycle 1.
              { inv WF_TGT. eapply WF; eauto. }
              { ss. eapply MEMJOIN; eauto. }
            }
            { inv SAT; ss. }
          }
          replace (fun tid' : Ident.t => if LocSet.Facts.eq_dec tid' tid then bot2 else prom tid')
            with prom1; cycle 1.
          { extensionality tid'. des_ifs; auto.
            eapply sim_configuration_no_promises_prom_extra_bot; eauto.
            ss. erewrite IdentMap.gss. eauto. }
          replace (fun tid' : Ident.t => if LocSet.Facts.eq_dec tid' tid then bot3 else extra tid')
            with extra1; cycle 1.
          { extensionality tid'. des_ifs; auto.
            eapply sim_configuration_no_promises_prom_extra_bot; eauto.
            ss. erewrite IdentMap.gss. eauto. }
          right. splits; auto.
          { ss. eapply good_future_mon; eauto. eapply TimeMap.join_l. }
          { i. exploit WRITES; eauto. i. des.
            exploit sim_traces_sim_event_exists; eauto.
            { inv RACY; ss. }
            { inv RACY; ss. }
            i. des. exists th0, e_src. split.
            { set (CNT := MEMPF.(sim_memory_contents) loc0 ts0). inv CNT; ss.
              { exfalso. eapply NPROM. econs; eauto. }
              { exfalso. eapply NPROM. econs; eauto. }
            }
            splits; auto.
            clear - RACY EVENT. inv RACY.
            { inv EVENT. econs. auto. }
            { inv EVENT. econs. auto. }
          }
        }
      }
    }
    { eexists [], [], c_src0, c_mid0, c_tgt0,views0, MachineEvent.silent.
      dup SIM. inv SIM. ss. specialize (THSPF tid). specialize (THSJOIN tid).
      rewrite TIDTGT in *. unfold option_rel in *. des_ifs.
      specialize (BOT _ Heq0). des. splits; auto.
      { econs 2; eauto. }
      { econs 2; eauto. }
      { econs. }
      { replace (fun tid': Ident.t => if (Ident.eq_dec tid' tid) then bot2 else (prom tid')) with prom; cycle 1.
        { extensionality tid'. extensionality loc. extensionality ts.
          apply Coq.Logic.PropExtensionality.propositional_extensionality.
          des_ifs. split; i; ss. eapply PROM; eauto. }
        replace (fun tid': Ident.t => if (Ident.eq_dec tid' tid) then bot3 else (extra tid')) with extra; cycle 1.
        { extensionality tid'. extensionality loc. extensionality ts. extensionality from.
          apply Coq.Logic.PropExtensionality.propositional_extensionality.
          des_ifs. split; i; ss. eapply EXTRA; eauto. }
        right. splits; auto.
        { refl. }
        { ii. exfalso. eapply PROM; eauto. }
      }
    }
  Qed.

  Lemma sim_configuration_certify_list
        (tidl: list Ident.t)
        tids views0 prom extra
        c_src0 c_mid0 c_tgt0 tm
        (SIM: sim_configuration tids views0 prom extra c_src0 c_mid0 c_tgt0)
        (WF_SRC: Configuration.wf c_src0)
        (WF_MID: JConfiguration.wf views0 c_mid0)
        (WF_TGT: Configuration.wf c_tgt0)
        (ALL: List.Forall tids tidl)
    :
      exists trs c_src1 c_mid1 c_tgt1 views1,
        (<<WF_SRC: Configuration.wf c_src1>>) /\
        (<<WF_MID: JConfiguration.wf views1 c_mid1>>) /\
        (<<WF_TGT: Configuration.wf c_tgt1>>) /\
        (<<STEPSRC: silent_pf_steps_trace L c_src0 c_src1 trs>>) /\
        (<<THS: forall tid (TID: ~ List.In tid tidl),
            IdentMap.find tid c_tgt0.(Configuration.threads) =
            IdentMap.find tid c_tgt1.(Configuration.threads)>>) /\
        __guard__((<<FAIL: exists tid c_src2,
                      (<<TID: List.In tid tidl>>) /\
                      (<<STEP: pf_step L MachineEvent.failure tid c_src1 c_src2>>)>>) \/
                  ((<<FUTURE: good_future tm c_tgt0.(Configuration.memory) c_tgt1.(Configuration.memory)>>) /\
                   (<<SC: c_tgt1.(Configuration.sc) = c_tgt0.(Configuration.sc)>>) /\
                   (<<SIM: sim_configuration
                             tids views1
                             (fun tid' => if (List.in_dec Ident.eq_dec tid' tidl) then bot2 else (prom tid'))
                             (fun tid' => if (List.in_dec Ident.eq_dec tid' tidl) then bot3 else (extra tid'))
                             c_src1 c_mid1 c_tgt1>>) /\
                   (<<WRITES: forall tid loc ts (TID: List.In tid tidl) (PROM: prom tid loc ts),
                       exists lc e_write,
                         (<<INLOCS: L loc>>) /\
                         (<<RACY: racy_write loc ts lc e_write>>) /\
                         (<<EVENT: List.In (lc, e_write) trs>>)>>))).
  Proof.
    Local Opaque List.in_dec.
    ginduction tidl.
    { i. eexists _, c_src0, c_mid0, c_tgt0, views0. splits; auto.
      { econs. }
      right.
      replace (fun tid':Ident.t => if (List.in_dec Ident.eq_dec tid' (@nil Ident.t)) then bot2 else (prom tid')) with prom; cycle 1.
      { extensionality tid. des_ifs. }
      replace (fun tid':Ident.t => if (List.in_dec Ident.eq_dec tid' (@nil Ident.t)) then bot3 else (extra tid')) with extra; cycle 1.
      { extensionality tid. des_ifs. }
      splits; auto.
      { refl. }
      { i. ss. }
    }
    { i. inv ALL. exploit sim_configuration_certify; eauto.
      i. des. destruct x0; des; subst.
      { subst. dep_inv STEPSRC.
        eexists _, c_src0, c_mid0, c_tgt0, views0. splits; auto.
        { econs. }
        left. esplits.
        { ss. left. auto. }
        { econs. esplits; eauto. }
      }
      exploit IHtidl; eauto.
      { eapply pf_opt_step_trace_future; eauto. }
      { eapply JConfiguration.opt_step_future; eauto. }
      { eapply times_configuration_opt_step_future; eauto. }
      { i. des. dep_inv STEPSRC.
        { eexists _, c_src2, c_mid2, c_tgt2, views2. splits; auto.
          { econs 2; eauto. }
          { i. erewrite <- THS; eauto. dep_inv STEPTGT.
            dep_inv STEP0. erewrite IdentMap.gsspec. des_ifs.
            exfalso. eapply TID; auto. }
          unguard. des.
          { left. esplits; eauto. }
          { right. esplits; eauto.
            { etrans; eauto. }
            { etrans; eauto. }
            { match goal with
              | H:sim_configuration ?tids ?v ?f0 ?g0 ?c0 ?c1 ?c2
                |- sim_configuration tids ?v ?f1 ?g1 ?c ?c1 ?c2 =>
                (replace f1 with f0; [replace g1 with g0; auto|])
              end.
              { extensionality tid. des_ifs; ss; des; exfalso; eauto. }
              { extensionality tid. des_ifs; ss; des; exfalso; eauto. }
            }
            { i. destruct (Ident.eq_dec a tid).
              { clear TID. subst. exploit WRITES; eauto. i. des. esplits; eauto.
                eapply List.in_or_app; eauto. }
              { des; ss. exploit WRITES0; eauto. des_ifs; eauto.
                i. des. esplits; eauto.
                eapply List.in_or_app; eauto. }
            }
          }
        }
        { eexists _, c_src2, c_mid2, c_tgt2, views2. splits; auto.
          { eauto. }
          { i. erewrite <- THS; eauto. dep_inv STEPTGT.
            dep_inv STEP. erewrite IdentMap.gsspec. des_ifs.
            exfalso. eapply TID; auto. }
          unguard. des.
          { left. esplits; eauto. }
          { right. esplits; eauto.
            { etrans; eauto. }
            { etrans; eauto. }
            { match goal with
              | H:sim_configuration ?tids ?v ?f0 ?g0 ?c0 ?c1 ?c2
                |- sim_configuration ?tids ?v ?f1 ?g1 ?c ?c1 ?c2 =>
                (replace f1 with f0; [replace g1 with g0; auto|])
              end.
              { extensionality tid. des_ifs; ss; des; exfalso; eauto. }
              { extensionality tid. des_ifs; ss; des; exfalso; eauto. }
            }
            { i. destruct (Ident.eq_dec a tid).
              { clear TID. subst. exploit WRITES; eauto. i. des. ss. }
              { des; ss. exploit WRITES0; eauto. des_ifs; eauto. }
            }
          }
        }
      }
    }
  Qed.

  Lemma sim_configuration_certify_all
        (ctids: Ident.t -> Prop) (ctids_dec: forall tid, { ctids tid } + { ~ ctids tid})
        (tids: Ident.t -> Prop) views0 prom extra
        (CTIDS: forall tid (CTID: ctids tid), tids tid)
        c_src0 c_mid0 c_tgt0 tm
        (SIM: sim_configuration tids views0 prom extra c_src0 c_mid0 c_tgt0)
        (WF_SRC: Configuration.wf c_src0)
        (WF_MID: JConfiguration.wf views0 c_mid0)
        (WF_TGT: Configuration.wf c_tgt0)
    :
      exists trs c_src1 c_mid1 c_tgt1 views1,
        (<<WF_SRC: Configuration.wf c_src1>>) /\
        (<<WF_MID: JConfiguration.wf views1 c_mid1>>) /\
        (<<WF_TGT: Configuration.wf c_tgt1>>) /\
        (<<STEPSRC: silent_pf_steps_trace L c_src0 c_src1 trs>>) /\
        (<<THS: forall tid (TID: ~ ctids tid),
            IdentMap.find tid c_tgt0.(Configuration.threads) =
            IdentMap.find tid c_tgt1.(Configuration.threads)>>) /\
        __guard__((<<FAIL: exists tid c_src2,
                      (<<TID: ctids tid>>) /\
                      (<<STEP: pf_step L MachineEvent.failure tid c_src1 c_src2>>)>>) \/
                  ((<<FUTURE: good_future tm c_tgt0.(Configuration.memory) c_tgt1.(Configuration.memory)>>) /\
                   (<<SC: c_tgt1.(Configuration.sc) = c_tgt0.(Configuration.sc)>>) /\
                   (<<SIM: sim_configuration
                             tids
                             views1
                             (fun tid' => if (ctids_dec tid') then bot2 else (prom tid'))
                             (fun tid' => if (ctids_dec tid') then bot3 else (extra tid'))
                             c_src1 c_mid1 c_tgt1>>) /\
                   (<<WRITES: forall tid loc ts (TID: ctids tid) (PROM: prom tid loc ts),
                       exists lc e_write,
                         (<<INLOCS: L loc>>) /\
                         (<<RACY: racy_write loc ts lc e_write>>) /\
                         (<<EVENT: List.In (lc, e_write) trs>>)>>))).
  Proof.
    hexploit (@sim_configuration_certify_list
                (List.filter
                   (fun tid => if ctids_dec tid then true else false)
                   (List.map fst (IdentMap.elements c_src0.(Configuration.threads))))); eauto.
    { eapply List.Forall_forall. i.
      eapply List.filter_In in H. des. des_ifs.
      eapply List.in_map_iff in H; eauto. }
    i. des. esplits; try apply STEPSRC; eauto.
    { i. eapply THS. ii. eapply List.filter_In in H. des. des_ifs. }
    unguard. des.
    { left. esplits; eauto.
      eapply List.filter_In in TID. des. des_ifs. }
    { right. esplits; eauto.
      { match goal with
        | H:sim_configuration ?tids ?v ?f0 ?g0 ?c0 ?c1 ?c2
          |- sim_configuration ?tids ?v ?f1 ?g1 ?c ?c1 ?c2 =>
          (replace f1 with f0; [replace g1 with g0; auto|])
        end.
        { extensionality tid. des_ifs.
          { erewrite List.filter_In in i. des. des_ifs. }
          { erewrite List.filter_In in n. apply not_and_or in n. des_ifs. des; ss.
            extensionality loc. extensionality ts. extensionality from.
            apply Coq.Logic.PropExtensionality.propositional_extensionality.
            split; i; ss. eapply n.
            eapply sim_configuration_extra_promise_exist in H; eauto. des.
            eapply IdentMap.elements_correct in TID.
            eapply List.in_map with (f:=fst) in TID. auto. }
        }
        { extensionality tid. des_ifs.
          { erewrite List.filter_In in i. des. des_ifs. }
          { erewrite List.filter_In in n. apply not_and_or in n. des_ifs. des; ss.
            extensionality loc. extensionality ts.
            apply Coq.Logic.PropExtensionality.propositional_extensionality.
            split; i; ss. eapply n.
            eapply sim_configuration_forget_promise_exist in H; eauto. des.
            eapply IdentMap.elements_correct in TID.
            eapply List.in_map with (f:=fst) in TID. auto. }
        }
      }
      { i. exploit WRITES; eauto. eapply List.filter_In. des_ifs. split; auto.
        eapply sim_configuration_forget_promise_exist in PROM; eauto. des.
        eapply IdentMap.elements_correct in TID0.
        eapply List.in_map with (f:=fst) in TID0. auto. }
    }
  Qed.

  Lemma good_future_configuration_step_aux c0 c1 c0' e tid (tr0 tr_cert0: Trace.t) tm
        lang st lc0 lc1 sc_tmp
        (STEP: times_configuration_step times tr0 tr_cert0 e tid c0 c0')
        (WF0: Configuration.wf c0)
        (WF1: Configuration.wf c1)
        (TID0: IdentMap.find tid c0.(Configuration.threads) =
               Some (existT _ lang st, lc0))
        (TID1: IdentMap.find tid c1.(Configuration.threads) =
               Some (existT _ lang st, lc1))
        (LOCAL: local_map
                  (fun loc ts fts => ts = fts /\ Time.lt ts (tm loc))
                  lc0
                  lc1)
        (MEM: memory_map
                (fun loc ts fts => ts = fts /\ Time.lt ts (tm loc))
                (Configuration.memory c0) (Configuration.memory c1))
        (TM: forall loc, Time.lt (Memory.max_ts loc c0.(Configuration.memory)) (tm loc))
        (SCMAP: timemap_map
                  (fun loc ts fts => ts = fts /\ Time.lt ts (tm loc))
                  (Configuration.sc c0) sc_tmp)
        (SCLE: TimeMap.le (Configuration.sc c1) sc_tmp)
        (TIME: List.Forall (fun the => wf_time_evt (fun loc ts => Time.lt ts (tm loc)) (snd the)) (tr0 ++ tr_cert0))
    :
      exists (tr1: Trace.t) tr_cert1 c1',
        (<<STEP: times_configuration_step times tr1 tr_cert1 e tid c1 c1'>>) /\
        (<<TRACE: List.Forall2
                    (fun the0 the1 =>
                       (<<EVT: sim_event (snd the0) (snd the1)>>) /\
                       (<<TVIEW: TView.le (fst the1).(Local.tview) (fst the0).(Local.tview)>>)) tr0 tr1>>) /\
        (<<GOOD:
           __guard__(exists st' lc0' lc1' sc_tmp',
                        (<<TID0: IdentMap.find tid c0'.(Configuration.threads) =
                                 Some (existT _ lang st', lc0')>>) /\
                        (<<TID1: IdentMap.find tid c1'.(Configuration.threads) =
                                 Some (existT _ lang st', lc1')>>) /\
                        (<<LOCAL: local_map
                                    (fun loc ts fts => ts = fts /\ Time.lt ts (tm loc))
                                    lc0'
                                    lc1'>>) /\
                        (<<MEM: memory_map
                                  (fun loc ts fts => ts = fts /\ Time.lt ts (tm loc))
                                  (Configuration.memory c0') (Configuration.memory c1')>>) /\
                        (<<SCMAP: timemap_map
                                    (fun loc ts fts => ts = fts /\ Time.lt ts (tm loc))
                                    (Configuration.sc c0') sc_tmp'>>) /\
                        (<<SCLE: TimeMap.le (Configuration.sc c1') sc_tmp'>>))>>).
  Proof.
    dep_inv STEP. dep_clarify.
    assert (IDENT:
              map_ident_in_memory
                (fun loc ts fts => ts = fts /\ Time.lt ts (tm loc))
                c0.(Configuration.memory)).
    { ii. split; auto. eapply TimeFacts.le_lt_lt; eauto. }
    assert (MAPLT: mapping_map_lt (fun loc ts fts => ts = fts /\ Time.lt ts (tm loc))).
    { ii. des. subst. auto. }
    eapply wf_time_mapped_mappable in TIME; cycle 1.
    { instantiate (1:=(fun loc ts fts => ts = fts /\ Time.lt ts (tm loc))).
      i. esplits; eauto. }
    eapply Forall_app_inv in TIME. des.
    eapply Forall_app_inv in FORALL1. des.
    destruct e2. ss. hexploit trace_steps_map; try apply STEPS; eauto.
    { eapply mapping_map_lt_map_le; eauto. }
    { eapply map_ident_in_memory_bot; eauto. }
    { eapply mapping_map_lt_map_eq; eauto. }
    { eapply WF0; eauto. }
    { eapply WF1; eauto. }
    { eapply WF1. }
    { eapply WF0. }
    { eapply WF1. }
    { eapply WF0. }
    { eapply mapping_map_lt_collapsable_unwritable; eauto. }
    i. des.
    hexploit Trace.steps_future; try apply STEPS; ss; eauto.
    { eapply WF0; eauto. }
    { eapply WF0. }
    { eapply WF0. } i. des.
    hexploit Trace.steps_future; try apply STEPS0; ss; eauto.
    { eapply WF1; eauto. }
    { eapply WF1. }
    { eapply WF1. } i. des.
    hexploit step_map; try apply MEM0; eauto.
    { eapply mapping_map_lt_map_le; eauto. }
    { eapply map_ident_in_memory_bot; eauto. }
    { eapply mapping_map_lt_map_eq; eauto. }
    { inv FORALL3. econs; eauto. econs. eauto. }
    { eapply mapping_map_lt_collapsable_unwritable; eauto. }
    i. des. inv STEP. ss.
    assert (EVENT: ThreadEvent.get_machine_event fe = ThreadEvent.get_machine_event e0).
    { eapply tevent_map_same_machine_event; eauto. }
    hexploit Thread.step_future; try apply STEP0; eauto. ss. i. des.
    hexploit Thread.step_future; try apply STEP1; eauto. ss. i. des.

    assert (CONSISTENT1:
              exists tr_cert1,
                (<<NORMAL:
                   forall (NEQ: ThreadEvent.get_machine_event fe <> MachineEvent.failure),
                     pf_consistent_super_strong
                       (Thread.mk _ st3 flc0 fsc0 fmem0)
                       tr_cert1 times>>) /\
                (<<FAILURE:
                   forall (EQ: ThreadEvent.get_machine_event fe = MachineEvent.failure),
                     tr_cert1 = []>>)).
    { hexploit (@concrete_promise_max_timemap_exists memory3 (Local.promises lc3)); eauto.
      { eapply CLOSED1. } intros [max MAX]. des.
      destruct (classic (e0 = ThreadEvent.failure)).
      { exists []. splits; ss. ii. subst. ss. }
      { specialize (CONSISTENT H).
        hexploit good_future_consistent; eauto.
        { i. ss. des. auto. }
        { eapply map_ident_in_memory_bot; eauto. }
        i. des. esplits; eauto. i. rewrite EQ in *. destruct e0; ss. }
    } des.

    eexists _, tr_cert1. esplits.
    { erewrite <- EVENT. econs.
      { erewrite TID1. eauto. }
      { eauto. }
      { eapply List.Forall_forall. i.
        eapply list_Forall2_in in H; eauto. des.
        destruct a, x. ss.
        eapply List.Forall_forall in IN; try apply SILENT. ss. inv EVENT0; auto. }
      { eauto. }
      { ss. }
      { i. eapply NORMAL. ii. destruct fe; ss. }
      { i. subst. auto. }
      { eapply list_Forall_app. splits.
        { eapply List.Forall_forall. i.
          eapply list_Forall2_in in H; eauto. des.
          eapply wf_time_evt_map in EVENT0; cycle 1.
          { eapply List.Forall_forall in TIMES; eauto.
            eapply List.in_or_app. left. eauto. }
          eapply wf_time_evt_mon; cycle 1; eauto.
          i. ss. des. subst. auto. }
        { econs; ss; eauto.
          eapply wf_time_evt_map in EVT; cycle 1.
          { eapply List.Forall_forall in TIMES; cycle 1.
            { eapply List.in_or_app. right. econs. ss. }
            { ss. eauto. }
          }
          { eapply wf_time_evt_mon; cycle 1; eauto.
            i. ss. des. subst. auto. }
        }
      }
    }
    { eapply list_Forall2_app.
      { eapply list_Forall2_impl; eauto. i. destruct a, b. ss. des. split; auto.
        { eapply tevent_ident_map; eauto. i. ss. des; auto. }
        { inv LOCAL2. eapply tview_ident_map in TVIEW; subst; eauto.
          ii. ss. des. auto. }
      }
      { econs; ss; eauto. split; auto.
        { eapply tevent_ident_map; eauto. i. ss. des; auto. }
        { inv LOCAL0. eapply tview_ident_map in TVIEW; subst; eauto.
          ii. ss. des. auto. }
      }
    }
    { unguard. exists st3, lc3, flc0, fsc1'0. splits; eauto.
      { erewrite IdentMap.gss; eauto. }
      { ss. erewrite IdentMap.gss; eauto. }
    }
  Qed.

  Lemma sim_thread_read_racy (others self: Loc.t -> Time.t -> Prop)
        (extra_others extra_self: Loc.t -> Time.t -> Time.t -> Prop)
        lang st lc_src lc_tgt sc mem_src mem_tgt pf e_tgt
        st' lc_tgt' sc' mem_tgt'
        (STEPTGT: @Thread.step lang pf e_tgt (Thread.mk _ st lc_tgt sc mem_tgt) (Thread.mk _ st' lc_tgt' sc' mem_tgt'))
        (NOREAD: ~ no_read_msgs others e_tgt)
        (MEM: sim_memory L times (others \\2// self) (extra_others \\3// extra_self) mem_src mem_tgt)
        (LOCALSRC: Local.wf lc_src mem_src)
        (SIM: sim_local L times self extra_self lc_src lc_tgt)
    :
      exists loc ts,
        (<<PROM: others loc ts>>) /\
        (<<RACY: racy_read loc ts lc_tgt e_tgt>>).
  Proof.
    unfold no_read_msgs in *. des_ifs.
    { inv STEPTGT; inv STEP; ss. inv LOCAL. inv LOCAL0. ss.
      apply NNPP in NOREAD. esplits; eauto. econs.
      eapply readable_not_exist_racy; eauto.
      { instantiate (1:=mem_src). inv SIM. inv LOCALSRC. ss. }
      ii. inv H. set (CNT := MEM.(sim_memory_contents) loc ts).
      rewrite GET0 in *. inv CNT; clarify. eapply NPROM. left. auto. }
    { inv STEPTGT; inv STEP; ss. inv LOCAL. inv LOCAL1. ss.
      apply NNPP in NOREAD. esplits; eauto. econs.
      eapply readable_not_exist_racy; eauto.
      { instantiate (1:=mem_src). inv SIM. inv LOCALSRC. ss. }
      ii. inv H. set (CNT := MEM.(sim_memory_contents) loc tsr).
      rewrite GET0 in *. inv CNT; clarify. eapply NPROM. left. auto. }
  Qed.

  Lemma sim_configuration_mid_mid tids views0 prom extra
        c_src0 c_mid0 c_tgt0
        (SIM: sim_configuration tids views0 prom extra c_src0 c_mid0 c_tgt0)
        (WF_SRC: Configuration.wf c_src0)
        (WF_MID: JConfiguration.wf views0 c_mid0)
        (WF_TGT: Configuration.wf c_tgt0)
    :
      sim_configuration tids views0 prom extra c_src0 c_mid0 c_mid0.
  Proof.
    inv SIM. econs; eauto.
    { i. specialize (THSJOIN tid). unfold option_rel. unfold option_rel in THSJOIN.
      unfold language in *. des_ifs. inv THSJOIN. econs; eauto.
      inv LOCAL. econs; eauto.
      { refl. }
      { ii. specialize (PROMISES loc ts). inv PROMISES; econs; eauto.
        inv RELEASED; econs; eauto. econs.
        { eapply MAXLE. }
        { refl. }
        { i. auto. }
      }
    }
    { refl. }
    { refl. }
  Qed.

  Lemma first_read_racy tids views0 prom0 extra0
        c_src0 c_mid0 c_tgt0 c_tgt1 e tid tr_tgt tr_cert
        (STEPTGT: @times_configuration_step
                    times
                    tr_tgt
                    tr_cert e tid c_tgt0 c_tgt1)
        (SIM: sim_configuration tids views0 prom0 extra0 c_src0 c_mid0 c_tgt0)
        (NOREAD: ~ List.Forall
                   (fun the => no_read_msgs
                                 (all_promises (fun tid' => tid <> tid') prom0)
                                 (snd the)) tr_tgt)
        (WF_SRC: Configuration.wf c_src0)
        (WF_MID: JConfiguration.wf views0 c_mid0)
        (WF_TGT: Configuration.wf c_tgt0)
    :
      exists loc ts c_mid1 tr_mid lc_race e_race,
        (<<PROM: all_promises (fun tid' => tid <> tid') prom0 loc ts>>) /\
        (<<RACY: racy_read loc ts lc_race e_race>>) /\
        (<<STEPMID: @times_configuration_step
                      times
                      tr_mid
                      tr_cert e tid c_mid0 c_mid1>>) /\
        (<<TRACE: List.In (lc_race, e_race) tr_mid>>)
  .
  Proof.
    destruct (list_first_occurence
                (fun the => no_read_msgs
                              (all_promises (fun tid' => tid <> tid') prom0)
                              (snd the))
                tr_tgt); ss. des. subst.
    hexploit times_configuration_step_future; eauto. i. des.
    dep_inv STEPTGT.
    exploit sim_configuration_sim_thread; eauto. i. des.
    generalize (sim_configuration_forget_exclusive SIM WF_SRC TIDSRC).
    intros EXCLUSIVE.
    generalize (sim_configuration_extra_exclusive SIM WF_SRC TIDSRC).
    intros EXCLUSIVEEXTRA.
    dup WF_MID. dup WF_SRC. inv WF_SRC. inv WF_MID. inv WF_TGT. inv SIM. ss.

    eapply Forall_app_inv in TIMES. des.
    exploit Trace.steps_future; eauto.
    { ss. eapply WF1; eauto. } i. des.
    exploit Thread.step_future; eauto. i. des. ss.

    assert (CONSISTENT1: Local.promise_consistent lc3).
    { destruct (classic (e0 = ThreadEvent.failure)) as [EQ|NEQ].
      { subst. inv STEP; inv STEP0. inv LOCAL. inv LOCAL0. ss. }
      specialize (CONSISTENT NEQ).
      eapply pf_consistent_super_strong_consistent in CONSISTENT; eauto.
      eapply consistent_promise_consistent in CONSISTENT; eauto.
    }
    assert (CONSTSIENT0: Local.promise_consistent e2.(Thread.local)).
    { eapply step_promise_consistent in STEP; eauto. }

    destruct (list_match_rev l1).
    { subst. eapply List.app_inj_tail in TR. des. subst.
      exploit sim_thread_steps_silent; eauto; ss.
      { eapply List.Forall_forall. ii. dup H. dup H.
        eapply List.Forall_forall in H; try apply SILENT. ss.
        eapply List.Forall_forall in H0; try apply ALL. ss.
        eapply List.Forall_forall in H1; try apply FORALL1. ss. }
      { eapply WF0. }
      { eapply WF0. }
      { eapply WF_SRC0; eauto. }
      { eapply WF0; eauto. }
      { eapply WF1; eauto. }
      i. des. dep_inv THREAD.
      exploit JThread.tau_steps_future; eauto; ss.
      { inv WF0. eapply WF5; eauto. }
      { eapply WF0. }
      { eapply WF0. }
      i. des. exploit JSim.sim_thread_step; eauto. i. des.
      exploit Trace.steps_future; try apply STEPSRC; ss.
      { eapply WF_SRC0; eauto. } i. des.
      assert (exists loc ts,
                 (<<PROM: all_promises (fun tid' => tid <> tid') prom0 loc ts>>) /\
                 (<<RACY: racy_read loc ts lc_mid0 e_src>>)).
      { destruct th1_src. ss.
        eapply JThread.step_thread_step in STEP0.
        exploit sim_thread_read_racy; eauto.
        { inv EVENT; eauto. }
        { eapply sim_local_strong_sim_local; eauto. }
      }
      des. destruct th1_src. ss.
      rewrite <- (JSim.sim_event_machine_event EVENT).
      esplits; eauto.
      { econs; simpl.
        { eauto. }
        { eapply STEPMIDTRACE. }
        { eapply List.Forall_forall. i.
          eapply list_Forall2_in2 in H; eauto. des.
          eapply List.Forall_forall in IN; try apply SILENT; eauto.
          destruct b, x. ss. inv SAT; auto. }
        { eapply JThread.step_thread_step; eauto. }
        { ss. }
        { i. hexploit CONSISTENT.
          { ii. subst. inv EVENT; ss. }
          exploit JThread.step_future; eauto. i. des. ss.
          i. eapply sim_thread_pf_consistent_super_strong; eauto.
        }
        { i. subst. inv EVENT; ss. }
        { eapply Forall_app.
          { eapply List.Forall_forall. i.
            eapply list_Forall2_in2 in H; eauto. des.
            eapply List.Forall_forall in IN; try apply FORALL1; eauto.
            destruct b, x. ss. inv SAT; auto. }
          { econs; ss. inv FORALL2. inv EVENT; auto. }
        }
      }
      { eapply List.in_or_app. ss. auto. }
    }
    { des. subst.
      erewrite List.app_comm_cons in TR. erewrite List.app_assoc in TR; eauto.
      eapply List.app_inj_tail in TR. des. clarify.
      eapply Trace.steps_separate in STEPS. des.
      exploit Trace.steps_future; try apply STEPS0; eauto.
      { eapply WF1; eauto. } i. ss. des.
      assert (CONSTSIENT2: Local.promise_consistent th1.(Thread.local)).
      { eapply Trace.steps_promise_consistent; eauto. }
      eapply Forall_app_inv in SILENT. des.
      exploit sim_thread_steps_silent; try apply SIM0; eauto; ss.
      { eapply List.Forall_forall. ii. dup H. dup H.
        eapply List.Forall_forall in H; try apply FORALL0. ss.
        eapply List.Forall_forall in H0; try apply ALL. ss.
        eapply List.Forall_forall in H1; try apply FORALL1. ss. }
      { eapply WF0. }
      { eapply WF0. }
      { eapply WF_SRC0; eauto. }
      { eapply WF0; eauto. }
      { eapply WF1; eauto. }
      i. des. dep_inv THREAD.
      exploit JThread.tau_steps_future; try apply STEPMIDTRACE; eauto; ss.
      { inv WF0. eapply WF6; eauto. }
      { eapply WF0. }
      { eapply WF0. }
      i. des.
      exploit Trace.steps_future; try apply STEPSRC; eauto; ss.
      { eapply WF_SRC0; eauto. }
      i. des.
      exploit sim_thread_steps_mid; try apply STEPS1; eauto. i. des.
      exploit Trace.steps_future; try apply TRACEMID0; eauto. i. des. ss.

      dup TRACEMID0. inv TRACEMID1.
      dup STEPMIDTRACE0. inv STEPMIDTRACE1; ss. clear STEPS. clarify.
      assert (exists loc ts,
                 (<<PROM: all_promises (fun tid' => tid <> tid') prom0 loc ts>>) /\
                 (<<RACY: racy_read loc ts lc_mid0 e>>)).
      { destruct th1. destruct a. ss. des.
        exploit sim_thread_read_racy; try apply STEP0; eauto.
        { inv H0; eauto. }
        { eapply sim_local_strong_sim_local; eauto. }
      }
      des. exploit JSim.sim_thread_step; try apply THREAD; eauto. i. des.
      rewrite <- (JSim.sim_event_machine_event EVENT).
      destruct th1_src. ss. esplits; eauto.
      { econs; simpl.
        { eauto. }
        { eapply Trace.steps_trans.
          { eauto. }
          { eauto. }
        }
        { eapply Forall_app.
          { eapply List.Forall_forall. i.
            eapply list_Forall2_in2 in H; eauto. des.
            eapply List.Forall_forall in IN; try apply FORALL0; eauto.
            destruct b, x. ss. inv SAT; auto. }
          { eapply List.Forall_forall. i.
            eapply list_Forall2_in2 in H; eauto. des.
            eapply List.Forall_forall in IN; try apply FORALL3; eauto.
            destruct b, x. ss. inv SAT0; auto. }
        }
        { eapply JThread.step_thread_step; eauto. }
        { ss. }
        { exploit JThread.step_future; eauto. i. des. ss.
          i. hexploit CONSISTENT.
          { ii. subst. inv EVENT; ss. }
          i. eapply sim_thread_pf_consistent_super_strong; eauto. }
        { i. subst. inv EVENT; ss. auto. }
        { erewrite List.app_comm_cons in FORALL2.
          eapply Forall_app_inv in FORALL2. des.
          eapply Forall_app.
          { eapply Forall_app.
            { eapply List.Forall_forall. i.
              eapply list_Forall2_in2 in H; eauto. des.
              eapply List.Forall_forall in IN; try apply FORALL1; eauto.
              destruct b, x. ss. inv SAT; auto. }
            { eapply List.Forall_forall. i.
              eapply list_Forall2_in2 in H; eauto. des.
              eapply List.Forall_forall in IN; try apply FORALL4; eauto.
              destruct b, x. ss. inv SAT0; ss. }
          }
          { econs; ss. inv FORALL5. inv EVENT; auto. }
        }
      }
      { eapply List.in_or_app. left.
        eapply List.in_or_app. ss. auto. }
    }
  Qed.

  Lemma configuration_step_certify c0 c1 e tid (tr tr_cert: Trace.t)
        (WF: Configuration.wf c0)
        (STEP: times_configuration_step times tr tr_cert e tid c0 c1)
    :
      exists c2 tr' f e',
        (<<STEP: times_configuration_opt_step times tr' [] e' tid c1 c2>>) /\
        (<<MAPLT: mapping_map_lt f>>) /\
        (<<MAPIDENT:
           forall loc ts fts to
                  (CONCRETE: concrete_promised c1.(Configuration.memory) loc to)
                  (TS: Time.le ts to)
                  (MAP: f loc ts fts),
             ts = fts>>) /\
        __guard__((<<TRACE: List.Forall2 (fun em fem => tevent_map_weak f (snd fem) (snd em)) tr_cert tr'>>) \/
                  (<<TRACE: exists lc, List.Forall2 (fun em fem => tevent_map_weak f (snd fem) (snd em)) (tr_cert++[(lc, ThreadEvent.failure)]) tr'>>)) /\
        __guard__(e = MachineEvent.failure \/ e' = MachineEvent.failure \/
                  ((<<NEQ: e' <> MachineEvent.failure>>) /\
                   (<<BOT: forall lang st lc
                                  (TID: IdentMap.find tid c2.(Configuration.threads) = Some (existT _ lang st, lc)),
                       lc.(Local.promises) = Memory.bot>>)))
  .
  Proof.
    hexploit times_configuration_step_future; eauto. i. des.
    destruct (classic (e = MachineEvent.failure)) as [EQ|NEQ].
    { subst. exists c1, [], ident_map, MachineEvent.silent. splits; auto.
      { econs 2. }
      { eapply ident_map_lt. }
      { dep_inv STEP. exploit CERTNIL; eauto.
        { destruct e; ss. }
        { i. subst. left. econs. }
      }
      { left. auto. }
    }
    { dep_inv STEP.
      exploit (@concrete_promise_max_timemap_exists memory3 (Local.promises lc3)).
      { eapply WF2. } i. des.
      exploit CONSISTENT.
      { ii. subst. ss. }
      { refl. }
      { eapply WF2. }
      { eapply WF2; eauto. ss. erewrite IdentMap.gss; eauto. }
      { eauto. }
      i. des. ss. instantiate (1:=fun loc => Time.incr (Memory.max_ts loc memory3)) in GOOD.
      assert (MAPIDENT0: forall loc ts fts to
                                (CONCRETE: concrete_promised memory3 loc to)
                                (TS: Time.le ts to)
                                (MAP: f loc ts fts),
                 ts = fts).
      { i. destruct (Time.le_lt_dec fts (tm loc)).
        { eapply MAPIDENT; eauto. }
        { dup l. eapply BOUND in l; eauto. des.
          inv CONCRETE. eapply MAX in GET.
          exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
          { eapply l. } etrans.
          { eapply TS. }
          eauto.
        }
      }
      destruct e1. ss. destruct x0; des.
      { des. esplits.
        { econs 1. econs.
          { ss. erewrite IdentMap.gss. eauto. }
          { eapply STEPS0. }
          { eapply List.Forall_impl; eauto. i. ss. des. auto. }
          { econs 2. instantiate (5:=ThreadEvent.failure). eauto. }
          { ss. }
          { ss. }
          { ss. }
          { eapply Forall_app.
            { eapply List.Forall_impl; eauto. i. ss. des. auto. }
            { econs; ss. }
          }
        }
        { eauto. }
        { eauto. }
        { right. esplits. eapply List.Forall2_app; eauto.
          instantiate (1:=local). econs; ss. econs. }
        { right. left. auto. }
      }
      { hexploit (list_match_rev ftr). i. des; subst.
        { inv STEPS0; ss.
          eexists _, [], f, MachineEvent.silent. splits; eauto.
          { econs 2. }
          { left. eauto. }
          { right. right. splits; ss. erewrite IdentMap.gss. i. dep_clarify. }
        }
        { eapply Trace.steps_separate in STEPS0. des.
          inv STEPS2; ss. clarify. inv STEPS0; ss. esplits.
          { econs 1. econs.
            { ss. erewrite IdentMap.gss. eauto. }
            { eapply STEPS1. }
            { eapply Forall_app_inv in EVENTS. des.
              eapply List.Forall_impl; eauto. i. ss. des. auto. }
            { eauto. }
            { ss. }
            { i. eapply promises_bot_certify_nil. ss. }
            { ss. }
            { eapply List.Forall_impl; eauto. i. ss. des. auto. }
          }
          { eauto. }
          { eauto. }
          { left. eauto. }
          { right. right. ss. split; auto.
            { eapply Forall_app_inv in EVENTS. ss. des.
              inv FORALL2; ss. des. rewrite TAU. ss. }
            { i. erewrite IdentMap.gss in *. dep_clarify. }
          }
        }
      }
    }
  Qed.

  Lemma promise_read_race views0 prom0 extra0
        c_src0 c_mid0 c_tgt0 c_tgt1 e tid tr_tgt tr_cert
        (STEPTGT: @times_configuration_step times tr_tgt tr_cert e tid c_tgt0 c_tgt1)
        (SIM: sim_configuration (fun _ => True) views0 prom0 extra0 c_src0 c_mid0 c_tgt0)
        (READ: ~ List.Forall
                 (fun the => no_read_msgs
                               (all_promises (fun tid' => tid <> tid') prom0)
                               (snd the)) tr_tgt)
        (WF_SRC: Configuration.wf c_src0)
        (WF_MID: JConfiguration.wf views0 c_mid0)
        (WF_TGT: Configuration.wf c_tgt0)
        (RACEFREE: pf_racefree L c_src0)
    :
      (<<BEH: forall beh, behaviors (pf_step L) c_src0 beh>>) \/
      (exists s, (<<EVENT: e = MachineEvent.syscall s>>) /\
                 (<<BEH: forall beh,
                     behaviors (pf_step L) c_src0 (s :: beh)>>)).
  Proof.
    exploit times_configuration_step_future; eauto. i. des.
    hexploit sim_configuration_mid_mid; eauto. intros SIMMID.

    hexploit first_read_racy; eauto.
    i. des.
    assert (DEC: forall (tid'': Ident.t), { (fun tid' => tid <> tid') tid'' } + { ~ (fun tid' => tid <> tid') tid''}).
    { i. destruct (Ident.eq_dec tid tid''); auto. }

    exploit times_configuration_step_future; eauto.
    { eapply WF_MID. } i. des.

    hexploit (@trace_times_list_exists (tr_mid ++ tr_cert)). i. des.
    exploit (@Memory.max_concrete_timemap_exists (Configuration.memory c_mid1)); eauto.
    { eapply WF0. } intros [max MAX].

    assert (exists (maxmap: TimeMap.t),
               (<<TIMES: forall loc' ts (IN: List.In ts (times0 loc')), Time.lt ts (maxmap loc')>>) /\
               (<<MAX: forall loc', Time.lt (Memory.max_ts loc' c_mid0.(Configuration.memory)) (maxmap loc')>>)).
    { hexploit (@choice
                  Loc.t
                  Time.t
                  (fun loc' max =>
                     (<<TIMES: forall ts (IN: List.In ts (times0 loc')), Time.lt ts (max)>>) /\
                     (<<MAX: Time.lt (Memory.max_ts loc' c_mid0.(Configuration.memory)) (max)>>))).
      { i. hexploit (finite_greatest (fun _ => True) (times0 x)). i. des.
        { exists (Time.incr (Time.join
                               (Memory.max_ts x (Configuration.memory c_mid0))
                               to)).
          splits.
          { i. eapply GREATEST in IN0; auto. eapply TimeFacts.le_lt_lt; eauto.
            eapply TimeFacts.le_lt_lt.
            { eapply Time.join_r. }
            { eapply  Time.incr_spec. }
          }
          { eapply TimeFacts.le_lt_lt.
            { eapply Time.join_l. }
            { eapply  Time.incr_spec. }
          }
        }
        { exists (Time.incr (Memory.max_ts x (Configuration.memory c_mid0))). splits.
          { i. eapply EMPTY in IN. ss. }
          { eapply Time.incr_spec. }
        }
      }
      i. des. exists f. split.
      { ii. specialize (H loc'). des. auto. }
      { ii. specialize (H loc'). des. auto. }
    } i. des.

    exploit (@sim_configuration_certify_all _ DEC); eauto; ss.
    { eapply WF_MID. }
    i. des. destruct x1; des.
    { left. ii. eapply silent_pf_steps_trace_behaviors; eauto.
      econs 3; eauto. }

    assert (IDENT: map_ident_in_memory (fun loc ts fts => ts = fts /\ Time.lt ts (maxmap loc))
                                       (Configuration.memory c_mid0)).
    { ii. splits; auto. eapply TimeFacts.le_lt_lt; eauto. }
    assert (MAPLT: mapping_map_lt (fun loc ts fts => ts = fts /\ Time.lt ts (maxmap loc))).
    { ii. des. subst. auto. }

    dup STEPMID. dep_inv STEPMID0.
    exploit good_future_configuration_step_aux; eauto.
    { eapply WF_MID. }
    { erewrite <- THS; eauto. }
    { eapply map_ident_in_memory_local; eauto.
      { eapply WF_MID; eauto. }
      { eapply WF_MID; eauto. }
    }
    { eapply max_good_future_map; eauto. eapply WF_MID. }
    { eapply map_ident_in_memory_closed_timemap; eauto. eapply WF_MID. }
    { erewrite SC. refl. }
    { eapply List.Forall_impl; eauto. i. ss. eapply wf_time_evt_mon; eauto.
      i. ss. eauto. }

    i. des.
    inv PROM. exploit WRITES; eauto. i. des.
    exploit (@step_sim_configuration true).
    { eapply STEP0. }
    { eauto. }
    { eapply List.Forall_forall. i. destruct x. ss. destruct t0; ss.
      { ii. inv H0. des_ifs. }
      { ii. inv H0. des_ifs. }
    }
    { ss. eapply List.Forall_forall. i. eapply bot_no_read.
      i. inv MSGS; eauto. des_ifs. }
    { auto. }
    { auto. }
    { auto. }
    i. des. destruct x0; des.
    { ss. rewrite H in *. dep_inv STEPSRC0; clarify.
      left. ii. eapply silent_pf_steps_trace_behaviors; eauto.
      econs 3. econs; eauto. }

    exploit list_Forall2_in2.
    { eapply TRACE0. }
    { eapply TRACE. }
    i. des. destruct b. ss.
    dup TRACE1. eapply sim_traces_sim_event_exists in TRACE1; eauto; cycle 1.
    { dup RACY. inv RACY1; inv EVT; ss. }
    { dup RACY. inv RACY1; inv EVT; ss. }
    i. des.

    dep_inv STEPSRC0.
    exfalso. eapply RACEFREE.
    { eapply silent_pf_steps_trace_pf_steps_trace; eauto. }
    { eauto. }
    { eauto. }
    { eauto. }
    { econs 2.
      { econs 1. }
      { eauto. }
    }
    { erewrite List.app_nil_r. eauto. }
    { eapply racy_read_mon.
      { eauto. }
      { etrans; eauto.  }
      { etrans; eauto. symmetry. auto. }
    }
  Qed.

  Lemma promise_read_race_certfication views0 prom0 extra0
        c_src0 c_mid0 c_tgt0 c_tgt1 e tid tr_tgt tr_cert
        (STEPTGT: @times_configuration_step times tr_tgt tr_cert e tid c_tgt0 c_tgt1)
        (SIM: sim_configuration (fun _ => True) views0 prom0 extra0 c_src0 c_mid0 c_tgt0)
        (NOREAD: List.Forall
                   (fun the => no_read_msgs
                                 (all_promises (fun tid' => tid <> tid') prom0)
                                 (snd the)) tr_tgt)
        (READ: ~ List.Forall
                 (fun the => no_read_msgs
                               (all_promises (fun tid' => tid <> tid') prom0)
                               (snd the)) tr_cert)
        (WF_SRC: Configuration.wf c_src0)
        (WF_MID: JConfiguration.wf views0 c_mid0)
        (WF_TGT: Configuration.wf c_tgt0)
        (RACEFREE: pf_racefree L c_src0)
    :
      (<<BEH: forall beh, behaviors (pf_step L) c_src0 beh>>) \/
      (exists s, (<<EVENT: e = MachineEvent.syscall s>>) /\
                 (<<BEH: forall beh,
                     behaviors (pf_step L) c_src0 (s :: beh)>>)).
  Proof.
    exploit times_configuration_step_future; eauto. i. des.
    hexploit sim_configuration_mid_mid; eauto. intros SIMMID.
    exploit configuration_step_certify; try apply STEPTGT; eauto. i. des.
    inv STEP; cycle 1.
    { exfalso. destruct x1; des; ss.
      { inv H. eapply READ; eauto. }
      { inv H. destruct tr_cert; ss. }
    }
    hexploit (@step_sim_configuration false); try apply STEPTGT; eauto; ss. i. des.
    destruct MID as [tr_mid ?]. des.
    destruct H1; des.
    { subst. exfalso. dep_inv STEPTGT. hexploit CERTNIL.
      { destruct e; ss. }
      i. subst. eapply READ. eauto. }
    exploit JConfiguration.step_future; eauto. i. des.
    hexploit first_read_racy; try eapply STEP0; eauto.
    { assert (FORGET: forall tid0 loc to fto
                             (PROM: prom0 tid0 loc to)
                             (MAP: f loc to fto),
                 to = fto).
      { inv SIM. ss. i.
        exploit sim_memory_forget_concrete_promised.
        { eauto. }
        { econs; eauto. }
        i. eapply sim_memory_concrete_promised_later in x2; eauto; cycle 1.
        { eapply WF_TGT. } des.
        eapply memory_future_concrete_promised in PROMISED; cycle 1.
        { eapply Memory.future_future_weak. eauto. }
        eapply MAPIDENT in PROMISED; eauto.
      }
      ii. eapply READ. eapply List.Forall_forall. i. destruct x1.
      { eapply list_Forall2_in2 in H0; eauto. des.
        eapply List.Forall_forall in IN; eauto. ss.
        destruct b, x. ss. inv SAT; eauto.
        { ss. ii. eapply IN. inv H0. econs; eauto.
          eapply FORGET in TO; eauto. subst. erewrite PROM; eauto. }
        { ss. ii. eapply IN. inv H0. econs; eauto.
          eapply FORGET in FROM; eauto. subst. erewrite PROM; eauto. }
      }
      { des. exploit list_Forall2_in2.
        { eapply H1. }
        { eapply List.in_or_app. eauto. }
        i. des.
        eapply List.Forall_forall in IN; eauto. ss.
        destruct b, x. ss. inv SAT; eauto.
        { ss. ii. eapply IN. inv H2. econs; eauto.
          eapply FORGET in TO; eauto. subst. erewrite PROM; eauto. }
        { ss. ii. eapply IN. inv H2. econs; eauto.
          eapply FORGET in FROM; eauto. subst. erewrite PROM; eauto. }
      }
    }
    i. des.
    exploit times_configuration_step_future; eauto.
    { eapply WF0. } i. des.

    assert (DEC: forall (tid'': Ident.t), { (fun tid' => tid <> tid') tid'' } + { ~ (fun tid' => tid <> tid') tid''}).
    { i. destruct (Ident.eq_dec tid tid''); auto. }

    hexploit (@trace_times_list_exists ((tr_mid ++ tr_cert) ++ (tr_mid0 ++ []))). i. des.
    eapply Forall_app_inv in WFTIME. des.
    exploit (@Memory.max_concrete_timemap_exists (Configuration.memory c_mid1)); eauto.
    { eapply WF0. } intros [max0 MAX0].
    exploit (@Memory.max_concrete_timemap_exists (Configuration.memory c_mid2)); eauto.
    { eapply WF1. } intros [max1 MAX1].

    assert (exists (maxmap: TimeMap.t),
               (<<TIMES: forall loc' ts (IN: List.In ts (times0 loc')), Time.lt ts (maxmap loc')>>) /\
               (<<MAX0: forall loc', Time.lt (Memory.max_ts loc' c_mid0.(Configuration.memory)) (maxmap loc')>>) /\
               (<<MAX1: forall loc', Time.lt (Memory.max_ts loc' c_mid1.(Configuration.memory)) (maxmap loc')>>)).
    { hexploit (@choice
                  Loc.t
                  Time.t
                  (fun loc' max =>
                     (<<TIMES: forall ts (IN: List.In ts (times0 loc')), Time.lt ts (max)>>) /\
                     (<<MAX0: Time.lt (Memory.max_ts loc' c_mid0.(Configuration.memory)) (max)>>) /\
                     (<<MAX1: Time.lt (Memory.max_ts loc' c_mid1.(Configuration.memory)) (max)>>))).
      { i. hexploit (finite_greatest (fun _ => True) (times0 x)). i. des.
        { exists (Time.incr (Time.join
                               (Time.join
                                  (Memory.max_ts x (Configuration.memory c_mid0))
                                  (Memory.max_ts x (Configuration.memory c_mid1)))
                               to)).
          splits.
          { i. eapply GREATEST in IN0; auto. eapply TimeFacts.le_lt_lt; eauto.
            eapply TimeFacts.le_lt_lt.
            { eapply Time.join_r. }
            { eapply Time.incr_spec. }
          }
          { eapply TimeFacts.le_lt_lt.
            { eapply Time.join_l. } eapply TimeFacts.le_lt_lt.
            { eapply Time.join_l. }
            { eapply Time.incr_spec. }
          }
          { eapply TimeFacts.le_lt_lt.
            { eapply Time.join_r. } eapply TimeFacts.le_lt_lt.
            { eapply Time.join_l. }
            { eapply Time.incr_spec. }
          }
        }
        { exists (Time.incr (Time.join (Memory.max_ts x (Configuration.memory c_mid0)) (Memory.max_ts x (Configuration.memory c_mid1)))). splits.
          { i. eapply EMPTY in IN. ss. }
          { eapply TimeFacts.le_lt_lt.
            { eapply Time.join_l. }
            { eapply Time.incr_spec. }
          }
          { eapply TimeFacts.le_lt_lt.
            { eapply Time.join_r. }
            { eapply Time.incr_spec. }
          }
        }
      }
      i. des. exists f0. splits.
      { ii. specialize (H loc'). des. auto. }
      { ii. specialize (H loc'). des. auto. }
      { ii. specialize (H loc'). des. auto. }
    } i. des.

    exploit (@sim_configuration_certify_all _ DEC); try apply SIMMID; eauto; ss.
    { eapply WF_MID. }
    i. des. destruct x3; des.
    { left. ii. eapply silent_pf_steps_trace_behaviors; eauto.
      econs 3; eauto. }

    assert (IDENT: map_ident_in_memory (fun loc ts fts => ts = fts /\ Time.lt ts (maxmap loc))
                                       (Configuration.memory c_mid0)).
    { ii. splits; auto. eapply TimeFacts.le_lt_lt; eauto. }
    assert (MAPLT0: mapping_map_lt (fun loc ts fts => ts = fts /\ Time.lt ts (maxmap loc))).
    { ii. des. subst. auto. }

    dup STEPMIDTIMED. dep_inv STEPMIDTIMED0.
    exploit good_future_configuration_step_aux; try apply STEPMIDTIMED; eauto.
    { eapply WF_MID. }
    { erewrite <- THS; eauto. }
    { eapply map_ident_in_memory_local; eauto.
      { eapply WF_MID; eauto. }
      { eapply WF_MID; eauto. }
    }
    { eapply max_good_future_map; eauto. eapply WF_MID. }
    { eapply map_ident_in_memory_closed_timemap; eauto. eapply WF_MID. }
    { erewrite SC. refl. }
    { eapply List.Forall_impl; eauto. i. ss. eapply wf_time_evt_mon; eauto.
      i. ss. eauto. }
    i. des. ss. destruct GOOD as [st' ?]. des.

    exploit (@step_sim_configuration true).
    { eapply STEP1. }
    { eauto. }
    { eapply List.Forall_forall. i. eapply bot_no_read.
      i. inv MSGS; eauto. des_ifs. }
    { ss. eapply List.Forall_forall. i. eapply bot_no_read.
      i. inv MSGS; eauto. des_ifs. }
    { auto. }
    { auto. }
    { auto. }
    i. des. ss. destruct x2; des.
    { ss. rewrite H in *. dep_inv STEPSRC1; clarify.
      left. ii. eapply silent_pf_steps_trace_behaviors; eauto.
      econs 3. econs; eauto. }
    hexploit times_configuration_step_future; try apply STEP1; eauto. i. des.
    hexploit JConfiguration.step_future; try apply STEPMID1; eauto. i. des.
    hexploit pf_opt_step_trace_future; try apply STEPSRC1; eauto. i. des.

    erewrite IdentMap.gss in TID0; eauto.
    dup STEPMID0. dep_inv STEPMID1. dep_clarify.
    exploit good_future_configuration_step_aux; try apply STEPMID0.
    { eapply WF0. }
    { eapply WF3. }
    { ss. erewrite IdentMap.gss. eauto. }
    { erewrite TID1. eauto. }
    { eauto. }
    { eauto. }
    { eauto. }
    { eauto. }
    { eauto. }
    { eapply List.Forall_impl; eauto. i. ss. eapply wf_time_evt_mon; eauto.
      i. ss. auto. }
    i. des.

    exploit (@step_sim_configuration true); try apply SIM2; eauto.
    { eapply List.Forall_forall. i. eapply bot_no_read.
      i. inv MSGS; eauto. erewrite PROM1 in PROMS; eauto. des_ifs. }
    { eapply List.Forall_forall. i. eapply bot_no_read.
      i. inv MSGS; eauto. erewrite PROM1 in PROMS; eauto. des_ifs. }
    i. des. ss.

    destruct (classic (e0 = ThreadEvent.failure)).
    { subst. left. ii. eapply silent_pf_steps_trace_behaviors; eauto.
      ss. inv STEPSRC1. econs 3; eauto. econs; eauto. }
    destruct (classic (e' = MachineEvent.failure)).
    { subst. destruct (ThreadEvent.get_machine_event e0) eqn:EVENT.
      { subst. left. ii. eapply silent_pf_steps_trace_behaviors; eauto.
        inv STEPSRC1.
        { econs 4; eauto.
          { econs; eauto. }
          { inv STEPSRC2. econs 3; eauto. econs; eauto. }
        }
        { inv STEPSRC2. econs 3; eauto. econs; eauto. }
      }
      { right. rewrite H0 in *. esplits; eauto. i.
        eapply silent_pf_steps_trace_behaviors; eauto.
        inv STEPSRC1. econs 2; eauto.
        { econs; eauto. }
        { inv STEPSRC2. econs 3; eauto. econs; eauto. }
      }
      { clear - EVENT H. destruct e0; ss. }
    }
    destruct x2; ss. des.
    exfalso. inv PROM0. rewrite PROM in PROMS; auto.
    exploit WRITES; eauto. i. des.

    exploit list_Forall2_in2.
    { eapply TRACE3. }
    { eauto. }
    i. des. destruct b. ss.
    dup TRACE4. eapply sim_traces_sim_event_exists in TRACE4; eauto; cycle 1.
    { dup RACY. inv RACY1; inv EVT; ss. }
    { dup RACY. inv RACY1; inv EVT; ss. }
    des.

    eapply RACEFREE.
    { eapply silent_pf_steps_trace_pf_steps_trace; eauto. }
    { eauto. }
    { eauto. }
    { eauto. }
    { eapply pf_steps_trace_trans.
      { eapply pf_opt_step_trace_pf_steps_trace; eauto. }
      { eapply pf_opt_step_trace_pf_steps_trace; eauto. }
    }
    { eapply List.in_or_app. eauto. }
    { eapply racy_read_mon.
      { eauto. }
      { etrans; eauto.  }
      { etrans; eauto. symmetry. auto. }
    }
  Qed.

End SIM.
