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

Require Import PFStep.
Require Import LocalPFThread.
Require Import TimeTraced.
Require Import PFConsistentStrong.
Require Import Mapping.
Require Import GoodFuture.
Require Import CapMap.
Require Import CapFlex.
Require Import Pred.

Set Implicit Arguments.



Lemma reserving_trace_sim_trace_none L tr
      (TRACE: sim_trace L tr None)
  :
    reserving_trace tr.
Proof.
  ginduction tr.
  { i. ss. }
  { i. inv TRACE. econs; eauto. eapply IHtr; eauto. }
Qed.

Lemma reserving_trace_sim_trace_reserving L tr lc e
      (TRACE: sim_trace L tr (Some (lc, e)))
      (RESERVING: ThreadEvent.is_reservation_event e)
  :
    reserving_trace tr.
Proof.
  remember (Some (lc, e)). ginduction TRACE; eauto; i; clarify.
  { econs; eauto.
    { ss. unfold ThreadEvent.is_reservation_event in RESERVING. des_ifs.
      inv EVENT. des. rewrite RESERVE0; ss. }
    { eapply reserving_trace_sim_trace_none; eauto. }
  }
  { eapply reserving_trace_sim_trace_none; eauto. }
  { econs; eauto. eapply IHTRACE; eauto. }
Qed.

Lemma reserving_trace_sim_traces_reserving L tr_src tr_tgt
      (TRACE: sim_traces L tr_src tr_tgt)
      (RESERVING: reserving_trace tr_tgt)
  :
    reserving_trace tr_src.
Proof.
  ginduction TRACE; eauto.
  { i. inv RESERVING. eapply Forall_app.
    { eapply reserving_trace_sim_trace_reserving; eauto. }
    { eapply IHTRACE; eauto. }
  }
  { i. eapply Forall_app.
    { eapply reserving_trace_sim_trace_none; eauto. }
    { eapply IHTRACE; eauto. }
  }
Qed.

Lemma sim_trace_relaxed_writing_event L tr lc ploc pts val we_tgt
      (WRITING : relaxed_writing_event ploc pts val we_tgt)
      (TRACE : sim_trace L tr (Some (lc, we_tgt)))
  :
    exists we_src : ThreadEvent.t,
      (<<FINAL: final_event_trace we_src tr>>) /\
      (<<WRITING: PFRace.writing_event ploc pts we_src>>).
Proof.
  remember (Some (lc, we_tgt)). ginduction TRACE; eauto; i; clarify.
  { inv WRITING; inv EVENT.
    { esplits; eauto.
      { econs; eauto. eapply reserving_trace_sim_trace_none; eauto. }
      { econs; eauto. }
    }
    { esplits; eauto.
      { econs; eauto. eapply reserving_trace_sim_trace_none; eauto. }
      { econs; eauto. }
    }
  }
  { inv WRITING; ss. }
  { exploit IHTRACE; eauto. i. des. esplits; eauto. econs; eauto. }
Qed.

Lemma final_event_trace_post_reserve e tr0 tr1
      (FINAL: final_event_trace e tr0)
      (RESERVING: reserving_trace tr1)
  :
    final_event_trace e (tr0 ++ tr1).
Proof.
  ginduction FINAL; eauto.
  { i. ss. erewrite List.app_comm_cons. ss. econs; eauto.
    eapply Forall_app; eauto.
  }
  { i. eapply IHFINAL in RESERVING. ss. econs; eauto. }
Qed.

Lemma sim_traces_relaxed_writing_event L tr_src tr_tgt ploc pts val we_tgt
      (WRITING : relaxed_writing_event ploc pts val we_tgt)
      (TRACE : sim_traces L tr_src tr_tgt)
      (FINAL: final_event_trace we_tgt tr_tgt)
  :
    exists we_src : ThreadEvent.t,
      (<<FINAL: final_event_trace we_src tr_src>>) /\
      (<<WRITING: PFRace.writing_event ploc pts we_src>>).
Proof.
  ginduction TRACE; eauto.
  { i. inv FINAL. }
  { i. inv FINAL.
    { exploit sim_trace_relaxed_writing_event; eauto. i. des. esplits; eauto.
      eapply final_event_trace_post_reserve; eauto.
      eapply reserving_trace_sim_traces_reserving; eauto. }
    { exploit IHTRACE; eauto. i. des. esplits; eauto.
      eapply final_event_trace_post; eauto. }
  }
  { i. exploit IHTRACE; eauto. i. des. esplits; eauto.
    eapply final_event_trace_post; eauto.
  }
Qed.

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
Proof. ii. inv PR; econs. inv MSG; ss. Qed.

Lemma promise_writing_event_racy
      loc from ts val released e
      (WRITING : promise_writing_event loc from ts val released e)
  :
    PFRace.writing_event loc ts e.
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
      erewrite (cap_flex_back CAPSRC); eauto. }
  }
  { i. split; intros GET.
    { eapply (@cap_flex_inv mem_src cap_src) in GET; eauto. des; subst.
      { erewrite RESERVE in GET; eauto.
        eapply (cap_flex_le CAPTGT); eauto. }
      { exploit SimMemory.sim_memory_adjacent_src; eauto. i. des.
        eapply CAPTGT in x0; eauto. }
      { erewrite SimMemory.sim_memory_max_ts; eauto.
        eapply (cap_flex_back CAPTGT). }
    }
    { eapply (@cap_flex_inv mem_tgt cap_tgt) in GET; eauto. des; subst.
      { erewrite <- RESERVE in GET; eauto.
        eapply (cap_flex_le CAPSRC); eauto. }
      { exploit SimMemory.sim_memory_adjacent_tgt; eauto. i. des.
        eapply CAPSRC in x0; eauto. }
      { erewrite <- SimMemory.sim_memory_max_ts; eauto.
        eapply (cap_flex_back CAPSRC). }
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
  { eapply IDENT in FROM. eapply IDENT in TO. subst. econs; eauto. inv MSG; ss. }
  { eapply IDENT in TO. subst. econs; eauto. }
  { eapply IDENT in FROM. eapply IDENT in TO. subst. econs; eauto. }
  { eapply IDENT in FROM. eapply IDENT in TO. subst. econs; eauto. }
Qed.

Lemma readable_not_exist_racy lc mem loc ts released ord
      (READABLE: TView.readable (TView.cur (Local.tview lc)) loc ts released ord)
      (CLOSED: TView.closed (Local.tview lc) mem)
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
      (RACY: PFRace.racy_read loc ts lc1 e1)
      (LOCAL: TView.le (Local.tview lc0) (Local.tview lc1))
      (EVENT: sim_event e0 e1)
  :
    PFRace.racy_read loc ts lc0 e0.
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

  Record pi_consistent
         (self: Loc.t -> Time.t -> Prop)
         (pl: list (Loc.t * Time.t))
         (mem_src: Memory.t)
         lang (e0:Thread.t lang)
    : Prop :=
    {
      pi_consistent_promises:
        forall loc ts (PROM: self loc ts),
          List.In (loc, ts) pl;
      pi_consistent_certify:
        forall mem1 tm sc
               (pl0 pl1: list (Loc.t * Time.t))
               (ploc: Loc.t) (pts: Time.t)
               (FUTURE: Memory.future_weak (Thread.memory e0) mem1)
               (CLOSED: Memory.closed mem1)
               (MWF: memory_times_wf times mem1)
               (LOCAL: Local.wf (Thread.local e0) mem1)
               (PLIST: pl = pl0 ++ (ploc, pts) :: pl1)
        ,
        exists ftr e1,
          (<<STEPS: Trace.steps ftr (Thread.mk _ (Thread.state e0) (Thread.local e0) sc mem1) e1>>) /\
          (<<EVENTS: List.Forall (fun em => <<SAT: (no_read_msgs (fun loc ts => ~ (covered loc ts (Local.promises (Thread.local e0)) \/ concrete_promised mem_src loc ts \/ Time.lt (tm loc) ts))
                                                                 /1\ wf_time_evt times
                                                   ) (snd em)>> /\ <<TAU: ThreadEvent.get_machine_event (snd em) = MachineEvent.silent>>) ftr >>) /\

          (<<PROMCONSISTENT: Local.promise_consistent (Thread.local e1)>>) /\
          (<<GOOD: good_future tm mem1 (Thread.memory e1)>>) /\
          (<<SC: (Thread.sc e1) = sc>>) /\

          __guard__((exists val we ftr_cert,
                        (<<CONSISTENT: pf_consistent_super_strong e1 ftr_cert times>>) /\
                        (<<EVENTSCERT: List.Forall (fun em => <<SAT: (no_read_msgs (fun loc ts => ~ (covered loc ts (Local.promises (Thread.local e0)) \/ concrete_promised mem_src loc ts \/ Time.lt (tm loc) ts))) (snd em)>>) ftr_cert>>) /\
                        (<<FINAL: final_event_trace we ftr>>) /\
                        (<<WRITING: relaxed_writing_event ploc pts val we>>) /\
                        (<<SOUND: forall loc0 from0 to0 val0 released0
                                         (GET: Memory.get loc0 to0 (Local.promises (Thread.local e1)) = Some (from0, Message.concrete val0 released0)),
                            exists from0' released0',
                              (<<GET: Memory.get loc0 to0 (Local.promises (Thread.local e0)) = Some (from0', Message.concrete val0 released0')>>)>>) /\
                        (<<WRITTEN: forall loc0 to0
                                           (IN: List.In (loc0, to0) (pl0 ++ [(ploc, pts)])),
                            Memory.get loc0 to0 (Local.promises (Thread.local e1)) = None>>)) \/
                    (exists st',
                        (<<LOCAL: Local.failure_step (Thread.local e1)>>) /\
                        (<<FAILURE: Language.step lang ProgramEvent.failure (@Thread.state lang e1) st'>>)));
    }.

  Definition past_consistent
             (mem_src: Memory.t)
             lang (e0:Thread.t lang)
    : Prop :=
    forall mem1 tm sc
           (FUTURE: Memory.future_weak (Thread.memory e0) mem1)
           (CLOSED: Memory.closed mem1)
           (MWF: memory_times_wf times mem1)
           (LOCAL: Local.wf (Thread.local e0) mem1)
    ,
    exists ftr e1,
      (<<STEPS: Trace.steps ftr (Thread.mk _ (Thread.state e0) (Thread.local e0) sc mem1) e1>>) /\
      (<<EVENTS: List.Forall (fun em => <<SAT: (no_read_msgs (fun loc ts => ~ (covered loc ts (Local.promises (Thread.local e0)) \/ concrete_promised mem_src loc ts \/ Time.lt (tm loc) ts))
                                                             /1\ wf_time_evt times
                                               ) (snd em)>> /\ <<TAU: ThreadEvent.get_machine_event (snd em) = MachineEvent.silent>>) ftr >>) /\
      (<<FINAL:__guard__((exists st',
                             (<<LOCAL: Local.failure_step (Thread.local e1)>>) /\
                             (<<FAILURE: Language.step lang ProgramEvent.failure (@Thread.state lang e1) st'>>)) \/
                         (<<PROMISES: (Local.promises (Thread.local e1)) = Memory.bot>>))>>).

  Lemma pi_consistent_mon self0 self1 pl mem_src0 mem_src1 lang
        st lc sc0 mem0 sc1 mem1
        (CONSISTENT: pi_consistent self0 pl mem_src0 (Thread.mk lang st lc sc0 mem0))
        (SELFLE: self1 <2= self0)
        (FUTURETGT: Memory.future_weak mem0 mem1)
        (FUTURESRC: Memory.future_weak mem_src0 mem_src1)
    :
      pi_consistent self1 pl mem_src1 (Thread.mk lang st lc sc1 mem1).
  Proof.
    inv CONSISTENT. ss. econs; eauto.
    { ii. ss. exploit pi_consistent_certify0.
      { transitivity mem1; eauto. }
      { eauto. }
      { eauto. }
      { eauto. }
      { eauto. }
      i. unguard. des.
      { ss. esplits; eauto.
        { eapply List.Forall_impl; eauto. i. ss. des. splits; auto.
          eapply no_read_msgs_mon; eauto. ii. des; eauto.
          eapply memory_future_concrete_promised in H; eauto. }
        { left. unguard. esplits; eauto.
          eapply List.Forall_impl; eauto. i. ss. des. splits; auto.
          eapply no_read_msgs_mon; eauto. ii. des; eauto.
          eapply memory_future_concrete_promised in H0; eauto. }
      }
      { ss. esplits; eauto.
        { eapply List.Forall_impl; eauto. i. ss. des. splits; auto.
          eapply no_read_msgs_mon; eauto. ii. des; eauto.
          eapply memory_future_concrete_promised in H; eauto. }
      }
    }
  Qed.

  Lemma past_consistent_mon mem_src0 mem_src1 lang
        st lc sc0 mem0 sc1 mem1
        (CONSISTENT: past_consistent mem_src0 (Thread.mk lang st lc sc0 mem0))
        (FUTURETGT: Memory.future_weak mem0 mem1)
        (FUTURESRC: Memory.future_weak mem_src0 mem_src1)
    :
      past_consistent mem_src1 (Thread.mk lang st lc sc1 mem1).
  Proof.
    ii. exploit (CONSISTENT mem2 tm sc); eauto.
    { etrans; eauto. }
    i. des. esplits; eauto.
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

      (JOINED: forall loc ts, List.Forall (fun vw => semi_closed_view vw mem_src loc ts) (views loc ts))
      (MEMJOIN: SimMemory.sim_memory mem_mid mem_tgt)
      (MEMWF: memory_times_wf times mem_mid)
      (MEMWFTGT: memory_times_wf times mem_tgt)
      (CONSISTENT: forall tid lang st lc
                          (IN: tids tid)
                          (GET: IdentMap.find tid ths_tgt = Some (existT _ lang st, lc)),
          pi_consistent (prom tid) (proml tid) mem_src (Thread.mk lang st lc sc_tgt mem_tgt))
      (PAST: forall tid lang st lc
                    (GET: IdentMap.find tid ths_tgt = Some (existT _ lang st, lc)),
          (<<CONSISTENT: past_consistent mem_src (Thread.mk lang st lc sc_tgt mem_tgt)>>) \/
          ((<<PROM: forall loc ts, ~ prom tid loc ts>>) /\
           (<<EXTRA: forall loc ts from, ~ extra tid loc ts from>>) /\
           (<<EQ: IdentMap.find tid ths_src = IdentMap.find tid ths_mid>>)))
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

        (SCSRC: Memory.closed_timemap (Thread.sc th_src0) (Thread.memory th_src0))
        (SCMID: Memory.closed_timemap (Thread.sc th_mid0) (Thread.memory th_mid0))
        (SCTGT: Memory.closed_timemap (Thread.sc th_tgt0) (Thread.memory th_tgt0))
        (MEMSRC: Memory.closed (Thread.memory th_src0))
        (MEMMID: Memory.closed (Thread.memory th_mid0))
        (MEMTGT: Memory.closed (Thread.memory th_tgt0))
        (LOCALSRC: Local.wf (Thread.local th_src0) (Thread.memory th_src0))
        (LOCALMID: Local.wf (Thread.local th_mid0) (Thread.memory th_mid0))
        (LOCALTGT: Local.wf (Thread.local th_tgt0) (Thread.memory th_tgt0))

        (MEMWF: memory_times_wf times (Thread.memory th_mid0))
        (MEMWFTGT: memory_times_wf times (Thread.memory th_tgt0))
        (CONSISTENT: Local.promise_consistent (Thread.local th_tgt1))

        (EXCLUSIVE: forall loc ts (OTHER: prom_others loc ts),
            exists from msg, <<UNCH: unchangable (Thread.memory th_src0) (Local.promises (Thread.local th_src0)) loc ts from msg>>)
        (EXCLUSIVEEXTRA: forall loc ts from (OTHER: extra_others loc ts from),
            (<<UNCH: unchangable (Thread.memory th_src0) (Local.promises (Thread.local th_src0)) loc ts from Message.reserve>>))
        (JOINED: forall loc ts, List.Forall (fun vw => semi_closed_view vw (Thread.memory th_src0) loc ts) (views0 loc ts))

        (REL: joined_released
                views0 (Local.promises (Thread.local th_mid0)) (Local.tview (Thread.local th_mid0)).(TView.rel))
        (JOINEDMEM: joined_memory views0 (Thread.memory th_mid0))
        (VIEWS: wf_views views0)
    :
      exists th_mid1 th_src1 views1 prom_self1 extra_self1 pf_mid e_mid tr,
        (<<STEPMID: JThread.step pf_mid e_mid th_mid0 th_mid1 views0 views1>>) /\
        (<<STEPSRC: Trace.steps tr th_src0 th_src1>>) /\
        (<<THREAD: sim_thread_strong
                     views1 prom_self1 prom_others extra_self1 extra_others
                     th_src1 th_mid1 th_tgt1>>) /\
        (<<EVENTJOIN: JSim.sim_event e_mid e_tgt>>) /\
        (<<JOINED: forall loc ts, List.Forall (fun vw => semi_closed_view vw (Thread.memory th_src1) loc ts) (views1 loc ts)>>) /\
        (<<TRACE: sim_trace L tr (Some ((Thread.local th_tgt0), e_tgt))>>) /\
        (<<MEMWF: memory_times_wf times (Thread.memory th_mid1)>>) /\
        (<<MEMWFTGT: memory_times_wf times (Thread.memory th_tgt1)>>)
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
    { hexploit step_memory_times_wf; try apply STEPTGT; eauto. }
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

        (SCSRC: Memory.closed_timemap (Thread.sc th_src0) (Thread.memory th_src0))
        (SCMID: Memory.closed_timemap (Thread.sc th_mid0) (Thread.memory th_mid0))
        (SCTGT: Memory.closed_timemap (Thread.sc th_tgt0) (Thread.memory th_tgt0))
        (MEMSRC: Memory.closed (Thread.memory th_src0))
        (MEMMID: Memory.closed (Thread.memory th_mid0))
        (MEMTGT: Memory.closed (Thread.memory th_tgt0))
        (LOCALSRC: Local.wf (Thread.local th_src0) (Thread.memory th_src0))
        (LOCALMID: Local.wf (Thread.local th_mid0) (Thread.memory th_mid0))
        (LOCALTGT: Local.wf (Thread.local th_tgt0) (Thread.memory th_tgt0))

        (MEMWF: memory_times_wf times (Thread.memory th_mid0))
        (MEMWFTGT: memory_times_wf times (Thread.memory th_tgt0))
        (CONSISTENT: Local.promise_consistent (Thread.local th_tgt1))

        (EXCLUSIVE: forall loc ts (OTHER: prom_others loc ts),
            exists from msg, <<UNCH: unchangable (Thread.memory th_src0) (Local.promises (Thread.local th_src0)) loc ts from msg>>)
        (EXCLUSIVEEXTRA: forall loc ts from (OTHER: extra_others loc ts from),
            (<<UNCH: unchangable (Thread.memory th_src0) (Local.promises (Thread.local th_src0)) loc ts from Message.reserve>>))
        (JOINED: forall loc ts, List.Forall (fun vw => semi_closed_view vw (Thread.memory th_src0) loc ts) (views0 loc ts))

        (REL: joined_released
                views0 (Local.promises (Thread.local th_mid0)) (Local.tview (Thread.local th_mid0)).(TView.rel))
        (JOINEDMEM: joined_memory views0 (Thread.memory th_mid0))
        (VIEWS: wf_views views0)
    :
      exists th_mid1 th_src1 views1 prom_self1 extra_self1 pf_mid pf_src,
        (<<STEPMID: JThread.step pf_mid e_tgt th_mid0 th_mid1 views0 views1>>) /\
        (<<STEPSRC: Thread.step pf_src e_tgt th_src0 th_src1>>) /\
        (<<THREAD: sim_thread_strong
                     views1 prom_self1 prom_others extra_self1 extra_others
                     th_src1 th_mid1 th_tgt1>>) /\
        (<<JOINED: forall loc ts, List.Forall (fun vw => semi_closed_view vw (Thread.memory th_src1) loc ts) (views1 loc ts)>>) /\
        (<<MEMWF: memory_times_wf times (Thread.memory th_mid1)>>) /\
        (<<MEMWFTGT: memory_times_wf times (Thread.memory th_tgt1)>>)
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

        (SCSRC: Memory.closed_timemap (Thread.sc th_src0) (Thread.memory th_src0))
        (SCMID: Memory.closed_timemap (Thread.sc th_mid0) (Thread.memory th_mid0))
        (SCTGT: Memory.closed_timemap (Thread.sc th_tgt0) (Thread.memory th_tgt0))
        (MEMSRC: Memory.closed (Thread.memory th_src0))
        (MEMMID: Memory.closed (Thread.memory th_mid0))
        (MEMTGT: Memory.closed (Thread.memory th_tgt0))
        (LOCALSRC: Local.wf (Thread.local th_src0) (Thread.memory th_src0))
        (LOCALMID: Local.wf (Thread.local th_mid0) (Thread.memory th_mid0))
        (LOCALTGT: Local.wf (Thread.local th_tgt0) (Thread.memory th_tgt0))

        (MEMWF: memory_times_wf times (Thread.memory th_mid0))
        (MEMWFTGT: memory_times_wf times (Thread.memory th_tgt0))
        (CONSISTENT: Local.promise_consistent (Thread.local th_tgt1))

        (EXCLUSIVE: forall loc ts (OTHER: prom_others loc ts),
            exists from msg, <<UNCH: unchangable (Thread.memory th_src0) (Local.promises (Thread.local th_src0)) loc ts from msg>>)
        (EXCLUSIVEEXTRA: forall loc ts from (OTHER: extra_others loc ts from),
            (<<UNCH: unchangable (Thread.memory th_src0) (Local.promises (Thread.local th_src0)) loc ts from Message.reserve>>))
        (JOINED: forall loc ts, List.Forall (fun vw => semi_closed_view vw (Thread.memory th_src0) loc ts) (views0 loc ts))

        (REL: joined_released
                views0 (Local.promises (Thread.local th_mid0)) (Local.tview (Thread.local th_mid0)).(TView.rel))
        (JOINEDMEM: joined_memory views0 (Thread.memory th_mid0))
        (VIEWS: wf_views views0)
    :
      exists th_mid1 th_src1 views1 prom_self1 extra_self1 tr_src,
        (<<STEPMID: JThread.rtc_tau th_mid0 th_mid1 views0 views1>>) /\
        (<<STEPSRC: Trace.steps tr_src th_src0 th_src1>>) /\
        (<<THREAD: sim_thread_strong
                     views1 prom_self1 prom_others extra_self1 extra_others
                     th_src1 th_mid1 th_tgt1>>) /\
        (<<JOINED: forall loc ts, List.Forall (fun vw => semi_closed_view vw (Thread.memory th_src1) loc ts) (views1 loc ts)>>) /\
        (<<TRACE: sim_traces L tr_src tr_tgt>>) /\
        (<<MEMWF: memory_times_wf times (Thread.memory th_mid1)>>) /\
        (<<MEMWFTGT: memory_times_wf times (Thread.memory th_tgt1)>>)
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
    hexploit sim_thread_step_silent; eauto.
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
    { eapply Trace.steps_trans; eauto. }
    { econs 2; eauto. }
  Qed.

  Lemma sim_configuration_sim_thread tids views prom extra proml
        (c_src c_mid c_tgt: Configuration.t)
        tid lang st lc_tgt
        (SIM: sim_configuration tids views prom extra proml c_src c_mid c_tgt)
        (TIDTGT: IdentMap.find tid (Configuration.threads c_tgt) = Some (existT _ lang st, lc_tgt))
    :
      exists lc_src lc_mid,
        (<<TIDSRC: IdentMap.find tid (Configuration.threads c_src) = Some (existT _ lang st, lc_src)>>) /\
        (<<TIDMID: IdentMap.find tid (Configuration.threads c_mid) = Some (existT _ lang st, lc_mid)>>) /\
        (<<SIM: sim_thread
                  views
                  (prom tid)
                  (all_promises (fun tid' => tid <> tid') prom)
                  (extra tid)
                  (all_extra (fun tid' => tid <> tid') extra)
                  (Thread.mk _ st lc_src (Configuration.sc c_src) (Configuration.memory c_src))
                  (Thread.mk _ st lc_mid (Configuration.sc c_mid) (Configuration.memory c_mid))
                  (Thread.mk _ st lc_tgt (Configuration.sc c_tgt) (Configuration.memory c_tgt))>>).
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
        tids views prom extra proml c_src c_mid c_tgt
        (SIM: sim_configuration tids views prom extra proml c_src c_mid c_tgt)
        (WF_SRC: Configuration.wf c_src)
        tid loc ts
        (PROM: prom tid loc ts)
    :
      exists lang st lc_src from msg,
        (<<TID: IdentMap.find tid (Configuration.threads c_src) = Some (existT _ lang st, lc_src)>>) /\
        (<<PROMISE: Memory.get loc ts (Local.promises lc_src) = Some (from, msg)>>)
  .
  Proof.
    destruct (IdentMap.find tid (Configuration.threads c_src)) as
        [[[lang st] lc_src]|] eqn:TID.
    { inv SIM. specialize (THSPF tid). setoid_rewrite TID in THSPF. ss. des_ifs.
      inv THSPF. inv LOCAL. set (CNT:=(sim_promise_contents PROMS) loc ts).
      inv CNT; ss. esplits; eauto. }
    { exfalso. inv SIM. eapply BOT in TID. des. eapply PROM0; eauto. }
  Qed.

  Lemma sim_configuration_extra_promise_exist
        tids views prom extra proml c_src c_mid c_tgt
        (SIM: sim_configuration tids views prom extra proml c_src c_mid c_tgt)
        (WF_SRC: Configuration.wf c_src)
        tid loc ts from
        (PROM: extra tid loc ts from)
    :
      exists lang st lc_src,
        (<<TID: IdentMap.find tid (Configuration.threads c_src) = Some (existT _ lang st, lc_src)>>) /\
        (<<PROMISE: Memory.get loc ts (Local.promises lc_src) = Some (from, Message.reserve)>>)
  .
  Proof.
    destruct (IdentMap.find tid (Configuration.threads c_src)) as
        [[[lang st] lc_src]|] eqn:TID.
    { inv SIM. specialize (THSPF tid). setoid_rewrite TID in THSPF. ss. des_ifs.
      inv THSPF. inv LOCAL. set (CNT:=(sim_promise_contents PROMS) loc ts).
      inv CNT; try by (exfalso; eapply NEXTRA; eauto).
      exploit ((sim_memory_wf MEMPF) loc from ts); eauto. i. des.
      exploit (UNIQUE from0); eauto. i. subst. esplits; eauto. }
    { exfalso. inv SIM. eapply BOT in TID. des. eapply EXTRA; eauto. }
  Qed.

  Lemma sim_configuration_forget_exclusive
        tids views prom extra proml c_src c_mid c_tgt
        tid lang st lc_src
        (SIM: sim_configuration tids views prom extra proml c_src c_mid c_tgt)
        (WF_SRC: Configuration.wf c_src)
        (TID: IdentMap.find tid (Configuration.threads c_src) = Some (existT _ lang st, lc_src))
    :
      forall loc ts
             (PROM: all_promises (fun tid' => tid <> tid') prom loc ts),
      exists (from : Time.t) (msg : Message.t),
        (<<UNCH: unchangable (Configuration.memory c_src) (Local.promises lc_src) loc ts from msg>>).
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
        tids views prom extra proml c_src c_mid c_tgt
        tid lang st lc_src
        (SIM: sim_configuration tids views prom extra proml c_src c_mid c_tgt)
        (WF_SRC: Configuration.wf c_src)
        (TID: IdentMap.find tid (Configuration.threads c_src) = Some (existT _ lang st, lc_src))
    :
      forall loc ts from
             (EXTRA: all_extra (fun tid' => tid <> tid') extra loc ts from),
        (<<UNCH: unchangable (Configuration.memory c_src) (Local.promises lc_src) loc ts from Message.reserve>>).
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
        tr_cert ths_tgt pl
        (CONFIGTGT: Configuration.wf (Configuration.mk ths_tgt sc_tgt mem_tgt))
        (CONSISTENT: pf_consistent_super_strong_promises_list
                       (Thread.mk _ st_tgt lc_tgt sc_tgt mem_tgt)
                       tr_cert
                       times pl)
        (PROMOTHERS: forall loc ts (PROM: (prom_others \\2// prom_self) loc ts),
            exists from to val released,
              (<<GET: Memory.get loc to mem_tgt = Some (from, Message.concrete val released)>>) /\
              (<<TS: Time.le ts to>>))
        (PROMSELF: forall loc ts (PROM: prom_self loc ts),
            exists from val released,
              (<<GET: Memory.get loc ts (Local.promises lc_tgt) = Some (from, Message.concrete val released)>>))
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
        prom_self pl mem_src
        (Thread.mk lang st_tgt lc_tgt sc_tgt mem_tgt).
  Proof.
    unfold pf_consistent_super_strong_promises_list in *. des. ss. econs.
    { i. eapply PROMSELF in PROM. des. eapply COMPLETE; eauto. }
    { exploit (@concrete_promise_max_timemap_exists mem_tgt (Local.promises lc_tgt)).
      { eapply CONFIGTGT. } intros [max MAX].
      ii. exploit CONSISTENT0; eauto. i. ss. des.
      { exists (ftr0 ++ ftr_reserve), e1.
        assert (NOREADTGT:
                  Forall
                    (fun em =>
                       (no_read_msgs
                          (fun (loc : Loc.t) (ts : Time.t) =>
                             ~
                               (covered loc ts (Local.promises lc_tgt) \/
                                concrete_promised mem_tgt loc ts \/ Time.lt (tm loc) ts)) (snd em)))
                    (ftr0 ++ ftr1)).
        { eapply Forall_app.
          { eapply Forall_app_inv in EVENTS. des.
            eapply List.Forall_impl; try apply FORALL1; eauto. i. ss. des; eauto. }
          { eapply Forall_app_inv in EVENTSCERT. des.
            eapply List.Forall_impl; try apply FORALL2; eauto. i. ss. des; eauto. }
        }
        assert (NOREADSRC:
                  Forall
                    (fun em =>
                       (no_read_msgs
                          (fun (loc : Loc.t) (ts : Time.t) =>
                             ~
                               (covered loc ts (Local.promises lc_tgt) \/
                                concrete_promised mem_src loc ts \/ Time.lt (tm loc) ts)) (snd em)))
                    (ftr0 ++ ftr1)).
        { eapply List.Forall_forall. i. dup H.
          eapply List.Forall_forall in H0; try apply NOREADTGT; eauto. ss.
          eapply list_Forall2_in in H; eauto. des.
          eapply List.Forall_forall in IN; eauto. ss.
          destruct x, a. ss. inv SAT; ss.
          { ii. eapply H0. ii. eapply H. des; auto.
            eapply FORGET in H1. des; ss; auto. destruct FORGET0; ss.
            { replace fto with to in *; ss.
              eapply MAPIDENT; eauto.
              exploit PROMOTHERS.
              { left. eauto. } i. des.
              eapply MAX in GET; eauto.
            }
            { eapply PROMSELF in H1. des. left. econs; eauto. econs; ss; [|refl].
              dup GET. apply memory_get_ts_strong in GET0. des; auto.
              subst. inv LOCAL. erewrite BOT in GET. ss. }
          }
          { ii. eapply H0. ii. eapply H. des; auto.
            eapply FORGET in H1. des; ss; auto. destruct FORGET0; ss.
            { replace ffrom with from in *; ss.
              eapply MAPIDENT; eauto.
              exploit PROMOTHERS.
              { left. eauto. } i. des.
              eapply MAX in GET; eauto.
            }
            { eapply PROMSELF in H1. des. left. econs; eauto. econs; ss; [|refl].
              dup GET. apply memory_get_ts_strong in GET0. des; auto.
              subst. inv LOCAL. erewrite BOT in GET. ss. }
          }
        }
        splits; eauto.
        { eapply Forall_app_inv in NOREADSRC. des. eapply list_Forall_sum.
          { instantiate (1:=fun em => wf_time_evt times (snd em) /\ ThreadEvent.get_machine_event (snd em) = MachineEvent.silent).
            eapply List.Forall_impl; eauto. i. ss. des; auto. }
          { eapply Forall_app; try apply FORALL1. eapply List.Forall_impl; eauto.
            i. ss. des. destruct a. ss. destruct t0; ss. }
          { i. ss. des. splits; auto. }
        }
        { left. exists val, we, (ftr_cancel ++ ftr1). splits; auto.
          eapply Forall_app_inv in NOREADSRC. des. eapply list_Forall_sum.
          { instantiate (1:=fun em => wf_time_evt times (snd em) /\ ThreadEvent.get_machine_event (snd em) = MachineEvent.silent).
            eapply List.Forall_impl; eauto. i. ss. des; auto. }
          { eapply Forall_app; try apply FORALL2. eapply List.Forall_impl; eauto.
            i. ss. des. destruct a. ss. destruct t0; ss. }
          { i. ss. }
        }
      }
      { unguard. exists ftr, e1. splits; auto.
        eapply List.Forall_forall. i. dup H.
        eapply List.Forall_forall in H0; try apply EVENTS; eauto. ss.
        eapply list_Forall2_in in H; eauto. des.
        eapply List.Forall_forall in IN; eauto. ss.
        destruct x, a. ss. splits; auto. inv SAT; ss.
        { ii. eapply SAT3. ii. eapply H. des; auto.
          eapply FORGET in H0. des; ss; auto.
          { replace fto with to in *; ss.
            eapply MAPIDENT; eauto.
            exploit PROMOTHERS.
            { left. eauto. } i. des.
            eapply MAX in GET; eauto.
          }
          { eapply PROMSELF in FORGET0. des. left. econs; eauto. econs; ss; [|refl].
            dup GET. apply memory_get_ts_strong in GET0. des; auto.
            subst. inv LOCAL. erewrite BOT in GET. ss. }
        }
        { ii. eapply SAT3. ii. eapply H. des; auto.
          eapply FORGET in H0. des; ss; auto.
          { replace ffrom with from in *; ss.
            eapply MAPIDENT; eauto.
            exploit PROMOTHERS.
            { left. eauto. } i. des.
            eapply MAX in GET; eauto.
          }
          { eapply PROMSELF in FORGET0. des. left. econs; eauto. econs; ss; [|refl].
            dup GET. apply memory_get_ts_strong in GET0. des; auto.
            subst. inv LOCAL. erewrite BOT in GET. ss. }
        }
      }
    }
  Qed.

  Lemma pf_consistent_past_consistent
        (prom_others prom_self: Time.t -> Time.t -> Prop)
        lang (st_src st_mid st_tgt: Language.state lang)
        lc_tgt mem_src mem_tgt sc_tgt
        tr_cert ths_tgt
        (CONFIGTGT: Configuration.wf (Configuration.mk ths_tgt sc_tgt mem_tgt))
        (CONSISTENTS: pf_consistent_super_strong
                       (Thread.mk _ st_tgt lc_tgt sc_tgt mem_tgt)
                       tr_cert
                       times)
        (PROMOTHERS: forall loc ts (PROM: (prom_others \\2// prom_self) loc ts),
            exists from to val released,
              (<<GET: Memory.get loc to mem_tgt = Some (from, Message.concrete val released)>>) /\
              (<<TS: Time.le ts to>>))
        (PROMSELF: forall loc ts (PROM: prom_self loc ts),
            exists from val released,
              (<<GET: Memory.get loc ts (Local.promises lc_tgt) = Some (from, Message.concrete val released)>>))
        (FORGET: forall loc ts
                        (PROMISED: concrete_promised mem_tgt loc ts),
            (<<PROMISED: concrete_promised mem_src loc ts>>) \/
            <<FORGET: (prom_others \\2// prom_self) loc ts>>)
        (NOREAD: List.Forall
                   (fun the => no_read_msgs
                                 prom_others
                                 (snd the)) tr_cert)
    :
      past_consistent
        mem_src
        (Thread.mk lang st_tgt lc_tgt sc_tgt mem_tgt).
  Proof.
    exploit (@concrete_promise_max_timemap_exists mem_tgt (Local.promises lc_tgt)).
    { eapply CONFIGTGT. } intros [max MAX].
    ii. exploit CONSISTENTS; eauto. i. ss. des.
    exists ftr, e1. esplits; eauto.
    { eapply List.Forall_forall. i. dup H.
      eapply List.Forall_forall in H0; try apply NOREADTGT; eauto. ss.
      eapply list_Forall2_in in H; eauto. des.
      eapply List.Forall_forall in IN; eauto. ss.
      destruct x, a. ss. splits; auto. inv SAT; ss.
      { ii. eapply SAT3. ii. eapply H. des; eauto.
        eapply FORGET in H0. des; ss; auto. destruct FORGET0; ss.
        { replace fto with to in *; ss.
          eapply MAPIDENT; eauto.
          exploit PROMOTHERS.
          { left. eauto. } i. des.
          eapply MAX in GET; eauto.
        }
        { eapply PROMSELF in H0. des. left. econs; eauto. econs; ss; [|refl].
          dup GET. apply memory_get_ts_strong in GET0. des; auto.
          subst. inv LOCAL. erewrite BOT in GET. ss. }
      }
      { ii. eapply SAT3. ii. eapply H. des; eauto.
        eapply FORGET in H0. des; ss; auto. destruct FORGET0; ss.
        { replace ffrom with from in *; ss.
          eapply MAPIDENT; eauto.
          exploit PROMOTHERS.
          { left. eauto. } i. des.
          eapply MAX in GET; eauto.
        }
        { eapply PROMSELF in H0. des. left. econs; eauto. econs; ss; [|refl].
          dup GET. apply memory_get_ts_strong in GET0. des; auto.
          subst. inv LOCAL. erewrite BOT in GET. ss. }
      }
    }
    { unguard. des; eauto. }
  Qed.

  Lemma sim_thread_sim_configuration
        (consistent: bool)
        tids views0 prom extra proml
        (c_src c_mid c_tgt: Configuration.t)
        tid lang (st_src st_mid st_tgt: Language.state lang)
        lc_src lc_mid lc_tgt mem_src mem_mid mem_tgt sc_src sc_mid sc_tgt
        (CONFIG: sim_configuration tids views0 prom extra proml c_src c_mid c_tgt)
        views1 prom_self extra_self tr_cert ths_src ths_mid ths_tgt pl
        (VIEWSLE: views_le views0 views1)
        (JOINED: forall loc ts, List.Forall (fun vw => semi_closed_view vw mem_src loc ts) (views1 loc ts))
        (MEMWF: memory_times_wf times mem_mid)
        (MEMWFTGT: memory_times_wf times mem_tgt)
        (FUTURESRC: Memory.future_weak (Configuration.memory c_src) mem_src)
        (FUTUREMID: Memory.future_weak (Configuration.memory c_mid) mem_mid)
        (FUTURETGT: Memory.future_weak (Configuration.memory c_tgt) mem_tgt)
        (CONFIGTGT: Configuration.wf (Configuration.mk ths_tgt sc_tgt mem_tgt))
        (CONFIGMID: JConfiguration.wf views1 (Configuration.mk ths_mid sc_mid mem_mid))
        (CONSISTENT: ternary consistent (pf_consistent_super_strong_promises_list
                                           (Thread.mk _ st_tgt lc_tgt sc_tgt mem_tgt)
                                           tr_cert
                                           times pl) True)
        (CONSISTENTS: pf_consistent_super_strong
                        (Thread.mk _ st_tgt lc_tgt sc_tgt mem_tgt)
                        tr_cert
                        times)
        (NOREAD: List.Forall
                   (fun the => no_read_msgs
                                 (all_promises (fun tid' => tid <> tid') prom)
                                 (snd the)) tr_cert)
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
             else IdentMap.find tid' (Configuration.threads c_src))
        (THSMID:
           forall tid',
             IdentMap.find tid' ths_mid =
             if (Ident.eq_dec tid' tid)
             then Some (existT _ lang st_mid, lc_mid)
             else IdentMap.find tid' (Configuration.threads c_mid))
        (THSTGT:
           forall tid',
             IdentMap.find tid' ths_tgt =
             if (Ident.eq_dec tid' tid)
             then Some (existT _ lang st_tgt, lc_tgt)
             else IdentMap.find tid' (Configuration.threads c_tgt))
    :
      sim_configuration
        (ternary consistent tids (fun tid' => tids tid' /\ tid' <> tid))
        views1
        (fun tid' => if (Ident.eq_dec tid' tid) then prom_self else (prom tid'))
        (fun tid' => if (Ident.eq_dec tid' tid) then extra_self else (extra tid'))
        (fun tid' => if (Ident.eq_dec tid' tid) then pl else (proml tid'))
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
          set (CNT:=(sim_promise_contents PROMS) loc ts). inv CNT; ss.
          specialize (PROMISES loc ts).  rewrite <- H in *. inv PROMISES. eauto. }
        { i. eapply jsim_memory_concrete_promised in PROMISED; cycle 1; eauto.
          apply NNPP. ii. apply not_or_and in H. des. eapply H.
          eapply sim_memory_concrete_promised; eauto. }
      }
      { dep_clarify. unguard. des; ss. }
      { eapply pi_consistent_mon; eauto. }
      { unguard. des. eapply pi_consistent_mon; eauto. }
    }
    { i. rewrite THSTGT in GET. des_ifs.
      { dep_clarify. left.
        eapply pf_consistent_past_consistent; try apply CONSISTENTS; eauto.
        { i. exploit sim_memory_forget_concrete_promised.
          { eapply MEMPF. }
          { eapply PROM. }
          i. eapply sim_memory_concrete_promised_later in x0; eauto; cycle 1.
          { eapply CONFIGTGT. }
          des. inv PROMISED. esplits; eauto.
        }
        { i. inv LOCALPF. inv LOCALJOIN.
          set (CNT:=(sim_promise_contents PROMS) loc ts). inv CNT; ss.
          specialize (PROMISES loc ts).  rewrite <- H in *. inv PROMISES. eauto. }
        { i. eapply jsim_memory_concrete_promised in PROMISED; cycle 1; eauto.
          apply NNPP. ii. apply not_or_and in H. des. eapply H.
          eapply sim_memory_concrete_promised; eauto. }
      }
      { exploit PAST; eauto. i. des.
        { left. eapply past_consistent_mon; eauto. }
        { right. splits; auto. rewrite THSSRC. rewrite THSMID. des_ifs. }
      }
    }
  Qed.

  Lemma sim_configuration_forget_src_not_concrete tids c_src c_mid c_tgt prom extra views pls
        (SIM: sim_configuration tids views prom extra pls c_src c_mid c_tgt)
        (WF_SRC: Configuration.wf c_src)
        (WF_MID: JConfiguration.wf views c_mid)
        (WF_TGT: Configuration.wf c_tgt)
        tid lang st lc_tgt
        (TID: IdentMap.find tid (Configuration.threads c_tgt) = Some (existT _ lang st, lc_tgt))
    :
      forall loc ts
             (PROMISE: all_promises (fun tid': Ident.t => tid <> tid') prom loc ts),
        ~ ((covered loc ts (Local.promises lc_tgt)) \/
           concrete_promised (Configuration.memory c_src) loc ts \/ Time.lt (Memory.max_ts loc (Configuration.memory c_tgt)) ts).
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
      set (CNT:=(sim_promise_contents PROMS0) loc ts). inv CNT; ss.
      dep_inv THSJOIN. inv LOCAL.
      specialize (PROMISES loc ts). rewrite <- H2 in *. inv PROMISES.
      inv H. dep_inv THSJOIN0.
      assert (exists msg_tgt, <<GET: Memory.get loc to (Local.promises lc_src) = Some (from0, msg_tgt)>>).
      { inv LOCAL. specialize (PROMISES loc to). ss.
        rewrite GET in PROMISES. inv PROMISES; eauto. } clear NIL. des.
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
      { set (CNT:=(sim_memory_contents MEMPF) loc ts). inv CNT; ss.
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
        (SCSRC: Memory.closed_timemap (Thread.sc th_src) (Thread.memory th_src))
        (SCMID: Memory.closed_timemap (Thread.sc th_mid) (Thread.memory th_mid))
        (SCTGT: Memory.closed_timemap (Thread.sc th_tgt) (Thread.memory th_tgt))
        (MEMSRC: Memory.closed (Thread.memory th_src))
        (MEMMID: Memory.closed (Thread.memory th_mid))
        (MEMTGT: Memory.closed (Thread.memory th_tgt))
        (LOCALSRC: Local.wf (Thread.local th_src) (Thread.memory th_src))
        (LOCALMID: Local.wf (Thread.local th_mid) (Thread.memory th_mid))
        (LOCALTGT: Local.wf (Thread.local th_tgt) (Thread.memory th_tgt))
        (MEMWF: memory_times_wf times (Thread.memory th_mid))
        (MEMWFTGT: memory_times_wf times (Thread.memory th_tgt))
        (NOREAD: List.Forall (fun the => no_read_msgs prom_others (snd the)) tr)
        (EXCLUSIVE: forall loc ts (OTHER: prom_others loc ts),
            exists from msg, <<UNCH: unchangable (Thread.memory th_src) (Local.promises (Thread.local th_src)) loc ts from msg>>)
        (EXCLUSIVEEXTRA: forall loc ts from (OTHER: extra_others loc ts from),
            (<<UNCH: unchangable (Thread.memory th_src) (Local.promises (Thread.local th_src)) loc ts from Message.reserve>>))
        (JOINED: forall loc ts, List.Forall (fun vw => semi_closed_view vw (Thread.memory th_src) loc ts) (views loc ts))

        (REL: joined_released
                views (Local.promises (Thread.local th_mid)) (Local.tview (Thread.local th_mid)).(TView.rel))
        (JOINEDMEM: joined_memory views (Thread.memory th_mid))
        (VIEWS: wf_views views)
    :
      PF.pf_consistent L th_src.
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
    { ss. eapply cap_flex_memory_times_wf; cycle 1; eauto. }
    { ss. eapply cap_flex_memory_times_wf; cycle 1; eauto. }
    { destruct x1.
      { des. inv LOCAL. auto. }
      { des. ii. erewrite PROMISES in *. erewrite Memory.bot_get in *. ss. }
    }
    { ss. ii. exploit EXCLUSIVE; eauto. i. des. inv UNCH.
      set (CNT:=(sim_memory_strong_contents MEM) loc ts).
      inv CNT; ss; try by (exfalso; eapply NPROM0; left; auto).
      symmetry in H0. eapply CAPSRCSTRONG in H0. esplits. econs; eauto. }
    { ss. ii. exploit EXCLUSIVEEXTRA; eauto. i. des. inv x.
      set (CNT:=(sim_memory_strong_contents MEM) loc ts).
      exploit ((sim_memory_strong_wf MEM) loc from ts).
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
      esplits. eauto. eauto.
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
      cut ((Local.promises local) = Memory.bot).
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
      inv EVENT; ss. ii. ss. clarify. destruct msg; ss.
      - exploit IN0; ss.
      - inv MSG; ss. }
  Qed.


  Lemma configuration_step_not_consistent_future
        c1 tid tr lang st1 lc1 th2
        (TID: IdentMap.find tid (Configuration.threads c1) =
              Some (existT _ lang st1, lc1))
        (WF: Configuration.wf c1)
        (STEPS: Trace.steps
                  tr
                  (Thread.mk _ st1 lc1 (Configuration.sc c1) (Configuration.memory c1))
                  th2)
    :
      Configuration.wf
        (Configuration.mk
           (IdentMap.add
              tid
              (existT _ lang (Thread.state th2), (Thread.local th2))
              (Configuration.threads c1))
           (Thread.sc th2) (Thread.memory th2))
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

  Lemma step_sim_configuration tids views0 prom0 extra0 proml0
        c_src0 c_mid0 c_tgt0 c_tgt1 e tid tr_tgt tr_cert
        (STEPTGT: @times_configuration_step times tr_tgt tr_cert e tid c_tgt0 c_tgt1)
        (SIM: sim_configuration tids views0 prom0 extra0 proml0 c_src0 c_mid0 c_tgt0)
        (NOREAD: List.Forall
                   (fun the => no_read_msgs
                                 (all_promises (fun tid' => tid <> tid') prom0)
                                 (snd the)) tr_tgt)
        (NOREADCERT: List.Forall
                       (fun the => no_read_msgs
                                     (all_promises (fun tid' => tid <> tid') prom0)
                                     (snd the)) tr_cert)
        (WF_SRC: Configuration.wf c_src0)
        (WF_MID: JConfiguration.wf views0 c_mid0)
        (WF_TGT: Configuration.wf c_tgt0)
    :
      exists tr_src c_src1 c_mid1 views1 prom1 extra1 proml1,
        (<<STEPMID: JConfiguration.step e tid c_mid0 c_mid1 views0 views1>>) /\
        (<<STEPSRC: PFConfiguration.opt_step_trace L tr_src e tid c_src0 c_src1>>) /\
        (<<TRACE: sim_traces L tr_src tr_tgt>>) /\
        __guard__(e = MachineEvent.failure \/
                  (<<SIM: sim_configuration tids views1 prom1 extra1 proml1 c_src1 c_mid1 c_tgt1>>) /\
                  (<<PROM: forall tid' (NEQ: tid <> tid'), prom1 tid' = prom0 tid'>>) /\
                  (<<EXTRA: forall tid' (NEQ: tid <> tid'), extra1 tid' = extra0 tid'>>) /\
                  (<<PROML: forall tid' (NEQ: tid <> tid'), proml1 tid' = proml0 tid'>>))
  .
  Proof.
    hexploit times_configuration_step_future; eauto. i. des.
    dep_inv STEPTGT.
    assert (CONSISTENTLIST: exists pl,
               forall (EQ: e0 <> ThreadEvent.failure),
                 pf_consistent_super_strong_promises_list
                   (Thread.mk _ st3 lc3 sc3 memory3) tr_cert times pl).
    { destruct (classic (e0 = ThreadEvent.failure)).
      { exists []. ii. ss. }
      { hexploit CONSISTENT; eauto. i.
        eapply pf_consistent_super_strong_promises_list_exists in H0; eauto.
        { des. eauto. }
        { ss. eapply WF2. }
        { ss. eapply WF2; eauto. ss. erewrite IdentMap.gss. ss. }
      }
    }
    hexploit sim_configuration_sim_thread; eauto. i. des.
    generalize (sim_configuration_forget_exclusive SIM WF_SRC TIDSRC).
    intros EXCLUSIVE.
    generalize (sim_configuration_extra_exclusive SIM WF_SRC TIDSRC).
    intros EXCLUSIVEEXTRA.
    dup SIM. dup WF_MID. dup WF_SRC. inv WF_SRC. inv WF_MID. inv WF_TGT. inv SIM.
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
    assert (CONSTSIENT0: Local.promise_consistent (Thread.local e2)).
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
      hexploit sim_thread_step_silent; eauto.
      { inv FORALL3. auto. }
      { inv FORALL2. auto. }
      { i. eapply EXCLUSIVE in OTHER. des. esplits.
        eapply unchangable_trace_steps_increase; eauto. }
      { i. eapply EXCLUSIVEEXTRA in OTHER. des. esplits.
        eapply unchangable_trace_steps_increase; eauto. }
      i. des. exists (tr_src ++ tr).
      hexploit JThread.step_future; eauto. i. des.
      hexploit Trace.steps_future; eauto. i. des.
      assert (SIMTRACE: sim_traces L (tr_src++tr) (tr' ++ [((Thread.local e2), e0)])).
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
                             (existT _ _ (Thread.state th_mid0), (Thread.local th_mid0)) ths_mid)
                          (Thread.sc th_mid0) (Thread.memory th_mid0)) views0 views2).
      { erewrite <- JSim.sim_event_machine_event; eauto. econs; eauto.
        { destruct th_mid0. eauto. }
        { i. dep_inv THREAD0. eapply JSim.sim_thread_consistent; eauto; ss.
          eapply pf_consistent_super_strong_consistent; eauto.
          eapply CONSISTENT. ii. subst. ss. }
      }
      hexploit (list_match_rev (tr_src++tr)). i. des.
      { assert (tr_src = [] /\ tr = []).
        { split.
          { destruct tr_src; auto. ss. }
          { destruct tr; auto. destruct tr_src; ss. }
        } des. subst. inv STEPSRC; ss. inv STEPSRC0; ss.
        destruct th_mid0. esplits.
        { eauto. }
        { rewrite EQ. econs 2; eauto. }
        { exploit sim_traces_trans; eauto. }
        { right. splits.
          { eapply (@sim_thread_sim_configuration true) with (tr_cert := tr_cert); eauto.
            { etrans; eauto. }
            { refl. }
            {ss. eapply Memory.future_future_weak. etrans; eauto. }
            { ss. eapply Memory.future_future_weak. etrans; eauto. }
            { ss. eapply JConfiguration.step_future; eauto. }
            { i. eapply CONSISTENTLIST. ii. subst. ss. }
            { i. eapply CONSISTENT. ii. subst. ss. }
            { eapply sim_thread_strong_sim_thread. eauto. }
            { i. des_ifs. }
            { i. erewrite IdentMap.gsspec. des_ifs; eauto. }
            { i. erewrite IdentMap.gsspec. des_ifs; eauto. }
          }
          { i. ss. des_ifs. }
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
                             (tl_rev ++ [((Thread.local th1), e)])).
        { rewrite <- H. eapply Forall_app.
          { eapply sim_traces_silent; eauto. }
          { eapply sim_trace_silent; eauto. i. clarify. }
        }
        eapply Forall_app_inv in ALLSILENT. des. inv FORALL5; ss.
        assert (VSTEP: PFConfiguration.step_trace
                         L
                         (tr_src ++ tr)
                         (ThreadEvent.get_machine_event e0) tid
                         (Configuration.mk ths_src sc_src mem_src)
                         (Configuration.mk
                            (IdentMap.add
                               tid
                               (existT _ _ state, local) ths_src)
                            sc memory)).
        { rewrite EQ.
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
        { econs 1; eauto. }
        { ss. }
        { right. splits.
          { eapply (@sim_thread_sim_configuration true); eauto.
            { etrans; eauto. }
            { ss. eapply Memory.future_future_weak. etrans; eauto. }
            { ss. eapply Memory.future_future_weak. etrans; eauto. }
            { ss. eapply Memory.future_future_weak. etrans; eauto. }
            { eapply JConfiguration.step_future; eauto. }
            { ss. eapply CONSISTENTLIST. ii. subst. ss. }
            { ss. eapply CONSISTENT. ii. subst. ss. }
            { dup THREAD0. eapply sim_thread_strong_sim_thread. eauto. }
            { i. erewrite IdentMap.gsspec. des_ifs; eauto. }
            { i. erewrite IdentMap.gsspec. des_ifs; eauto. }
            { i. erewrite IdentMap.gsspec. des_ifs; eauto. }
          }
          { i. ss. des_ifs. }
          { i. ss. des_ifs. }
          { i. ss. des_ifs. }
        }
      }
    }
    { hexploit sim_thread_step_event; eauto.
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
                             (existT _ _ (Thread.state th_mid0), (Thread.local th_mid0)) ths_mid)
                          (Thread.sc th_mid0) (Thread.memory th_mid0)) views0 views2).
      { econs; eauto.
        { destruct th_mid0. eauto. }
        { i. dep_inv THREAD0. eapply JSim.sim_thread_consistent; eauto; ss.
          eapply pf_consistent_super_strong_consistent; eauto. }
      }
      assert (VSTEP: PFConfiguration.step_trace
                       L
                       (tr_src ++ [((Thread.local th_src1), e0)])
                       (ThreadEvent.get_machine_event e0) tid
                       (Configuration.mk ths_src sc_src mem_src)
                       (Configuration.mk
                          (IdentMap.add
                             tid
                             (existT _ _ (Thread.state th_src0), (Thread.local th_src0)) ths_src)
                          (Thread.sc th_src0) (Thread.memory th_src0))).
      { ss. econs; eauto.
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
      { ss.
        { econs 1; eauto. }
      }
      { eapply sim_traces_trans; eauto.
        replace [((Thread.local th_src1), e0)] with ([((Thread.local th_src1), e0)]++[]); auto. econs 2; auto.
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
        { eapply (sim_thread_sim_configuration true); eauto.
          { etrans; eauto. }
          { ss. eapply Memory.future_future_weak. etrans; eauto. }
          { ss. eapply Memory.future_future_weak. etrans; eauto. }
          { ss. eapply Memory.future_future_weak. etrans; eauto. }
          { eapply JConfiguration.step_future; eauto. }
          { ss. dup THREAD0. eauto. }
          { eapply sim_thread_strong_sim_thread. eauto. }
          { i. erewrite IdentMap.gsspec. des_ifs; eauto. }
          { i. erewrite IdentMap.gsspec. des_ifs; eauto. }
          { i. erewrite IdentMap.gsspec. des_ifs; eauto. }
        }
        { i. ss. des_ifs. }
        { i. ss. des_ifs. }
        { i. ss. des_ifs. }
      }
    }
  Qed.


  Lemma sim_configuration_no_promises_prom_extra_bot
        tids views prom extra proml
        c_src c_mid c_tgt tid lang st lc_tgt
        (SIM: sim_configuration tids views prom extra proml c_src c_mid c_tgt)
        (TIDTGT: IdentMap.find tid (Configuration.threads c_tgt) = Some (existT _ lang st, lc_tgt))
        (PROMISE: (Local.promises lc_tgt) = Memory.bot)
    :
      (<<PROM: prom tid = bot2>>) /\
      (<<EXTRA: extra tid = bot3>>).
  Proof.
    inv SIM. ss. specialize (THSPF tid). specialize (THSJOIN tid).
    unfold option_rel in *. des_ifs. inv THSPF. dep_inv THSJOIN. inv LOCAL. inv LOCAL0.
    split.
    { red. extensionality loc. extensionality ts.
      apply Coq.Logic.PropExtensionality.propositional_extensionality. split; i; ss.
      set (CNT:=(sim_promise_contents PROMS) loc ts). inv CNT; ss.
      specialize (PROMISES loc ts). rewrite <- H2 in *. inv PROMISES; ss.
      erewrite Memory.bot_get in *. clarify. }
    { red. extensionality loc. extensionality ts. extensionality from.
      apply Coq.Logic.PropExtensionality.propositional_extensionality. split; i; ss.
      eapply (sim_promise_wf PROMS) in H. des.
      set (CNT:=(sim_promise_contents PROMS) loc from). inv CNT; ss.
      specialize (PROMISES loc from). rewrite <- H in *. inv PROMISES; ss.
      erewrite Memory.bot_get in *. clarify. }
  Qed.

  Lemma sim_thread_forget
        views prom_self prom_others extra_self extra_others
        lang th_src th_mid th_tgt
        (THREAD: @sim_thread
                   views prom_self prom_others extra_self extra_others
                   lang th_src th_mid th_tgt)
        (LOCAL: Local.wf (Thread.local th_src) (Thread.memory th_src))
        loc ts
    :
      prom_self loc ts <->
      (<<MEMSRC: ~ concrete_promised (Thread.memory th_src) loc ts>>) /\
      (<<PROMTGT: concrete_promised (Local.promises (Thread.local th_tgt)) loc ts>>).
  Proof.
    dep_inv THREAD. inv LOCALPF. inv LOCALJOIN. split; i.
    { split.
      { set (CNT0:=(sim_memory_contents MEMPF) loc ts).
        inv CNT0; ss; try by (exfalso; try apply NPROM; right; eauto).
        ii. inv H0. rewrite GET in *. ss. }
      { set (CNT0:=(sim_promise_contents PROMS) loc ts).
        set (CNT1:=PROMISES loc ts).
        inv CNT0; ss. rewrite <- H2 in *. inv CNT1. econs; eauto. }
    }
    { des. ss. inv PROMTGT.
      set (CNT0:=(sim_promise_contents PROMS) loc ts).
      set (CNT1:=PROMISES loc ts).
      erewrite GET in *. inv CNT1.
      rewrite <- H0 in *. inv CNT0; ss.
      eapply LOCAL in H2. exfalso. eapply MEMSRC. econs; eauto.
    }
  Qed.

  Lemma sim_configuration_certify_partial tids tid ploc pts pl0 pl1
        views0 prom extra proml
        c_src0 c_mid0 c_tgt0 tm
        (SIM: sim_configuration tids views0 prom extra proml c_src0 c_mid0 c_tgt0)
        (WF_SRC: Configuration.wf c_src0)
        (PFSRC: PF.pf_configuration L c_src0)
        (WF_MID: JConfiguration.wf views0 c_mid0)
        (WF_TGT: Configuration.wf c_tgt0)
        (TIDS: tids tid)
        (EQ: proml tid = pl0 ++ (ploc, pts) :: pl1)
    :
      exists tr_src tr_tgt tr_cert c_src1 c_mid1 c_tgt1
             views1 e prom_self extra1 proml1 we,
        (<<STEPSRC: PFConfiguration.opt_step_trace L tr_src e tid c_src0 c_src1>>) /\
        (<<STEPMID: JConfiguration.opt_step e tid c_mid0 c_mid1 views0 views1>>) /\
        (<<STEPTGT: @times_configuration_opt_step times tr_tgt tr_cert e tid c_tgt0 c_tgt1>>) /\
        (<<TRACE: sim_traces L tr_src tr_tgt>>) /\
        __guard__((e = MachineEvent.failure) \/
                  (e = MachineEvent.silent /\
                   (<<FUTURE: good_future tm (Configuration.memory c_tgt0) (Configuration.memory c_tgt1)>>) /\
                   (<<SC: (Configuration.sc c_tgt1) = (Configuration.sc c_tgt0)>>) /\
                   (<<SIM: sim_configuration
                             tids views1
                             (fun tid' => if (Ident.eq_dec tid' tid) then prom_self else (prom tid'))
                             extra1
                             proml1
                             c_src1 c_mid1 c_tgt1>>) /\
                   (<<WRITE: PFRace.writing_event ploc pts we>>) /\
                   (<<FINAL: final_event_trace we tr_src>>) /\
                   (<<DECR: prom_self <2= prom tid>>) /\
                   (<<WRITTEN: forall loc ts (IN: List.In (loc, ts) (pl0 ++ [(ploc, pts)])),
                       ~ prom_self loc ts>>) /\
                   (<<PROML: forall tid' (NEQ: tid <> tid'), proml1 tid' = proml tid'>>)))
  .
  Proof.
    destruct (IdentMap.find tid (Configuration.threads c_tgt0)) as [[[lang_tgt st_tgt] lc_tgt]|] eqn:TIDTGT.
    { dup SIM. inv SIM. ss. hexploit CONSISTENT; eauto.
      intros CONSISTENT0. exploit (pi_consistent_certify CONSISTENT0).
      { refl. }
      { eapply WF_TGT. }
      { auto. }
      { eapply WF_TGT; eauto. }
      { erewrite EQ. eauto. }
      instantiate (3:=TimeMap.join tm (fun loc => Time.incr (Memory.max_ts loc mem_tgt))).
      i. des. ss.
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
      destruct x1; des; cycle 1.
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
        exploit (step_sim_configuration); eauto.
        { eapply Forall_app.
          { eapply List.Forall_impl in NOREAD; eauto. }
          { econs; ss. }
        }
        i. des. esplits; eauto.
        { econs 1. eauto. }
        { left. ss. }
        Unshelve.
        { eapply (prom1 tid). }
        { eapply extra1. }
        { eapply proml1. }
        { eapply ThreadEvent.failure. }
      }
      { destruct e1; ss.
        assert (STEPTGT: @times_configuration_step
                           times
                           ftr
                           ftr_cert
                           MachineEvent.silent
                           tid
                           (Configuration.mk ths_tgt sc_tgt mem_tgt)
                           (Configuration.mk
                              (IdentMap.add tid (existT _ lang_tgt state, local) ths_tgt)
                              sc
                              memory)).
        { hexploit (list_match_rev ftr). i. des; subst.
          { exfalso. inv FINAL; ss. }
          destruct hd_rev as [th e].
          eapply Trace.steps_separate in STEPS. des.
          inv STEPS1; ss; clarify. inv STEPS; clarify.
          dup EVENTS. eapply Forall_app_inv in EVENTS. des.
          replace MachineEvent.silent with (ThreadEvent.get_machine_event e0); cycle 1.
          { inv FORALL2. ss. des. auto. }
          econs; eauto.
          { eapply List.Forall_impl; eauto. i. ss. des; auto. }
          { ii. exfalso. inv FORALL2. ss. des; clarify. }
          { eapply List.Forall_impl; eauto. i. ss. des; auto. }
        }
        exploit (step_sim_configuration); eauto.
        { ss. eapply List.Forall_impl; eauto. i. ss. des; auto.
          eapply no_read_msgs_mon; eauto.
          i. ss.
          hexploit sim_configuration_forget_src_not_concrete; eauto. i. ss.
          ii. eapply H0. des; auto. right. right. eapply TimeFacts.le_lt_lt; eauto. etrans.
          { left. eapply Time.incr_spec. }
          { eapply Time.join_r. }
        }
        i. des.
        exploit sim_traces_relaxed_writing_event; eauto. i. des.
        eexists _, _, _, _, _, _, views1, _. esplits; eauto.
        { econs 1. eauto. }
        { unguard. des; ss. right. splits; auto.
          { ss. eapply good_future_mon; eauto. eapply TimeMap.join_l. }
          { instantiate (1:=extra1).
            instantiate (1:=prom1 tid).
            replace (fun tid' : Ident.t => if LocSet.Facts.eq_dec tid' tid then prom1 tid else prom tid')
              with prom1; cycle 1.
            { extensionality tid'. des_ifs; auto. }
            eauto.
          }
          { eauto. }
          { eauto. }
          { exploit PFConfiguration.opt_step_trace_future; try apply STEPSRC; eauto. i. des.
            exploit sim_configuration_sim_thread; try apply SIM0; eauto.
            ss. i. des.
            exploit sim_configuration_sim_thread; try apply SIM; eauto.
            { ss. erewrite IdentMap.gss. ss. }
            ss. i. des. eapply sim_thread_forget in PR; try apply SIM2; cycle 1.
            { eapply WF2; eauto. }
            ss. eapply sim_thread_forget; try apply SIM1.
            { eapply WF_SRC; eauto. }
            ss. des. split.
            { ii. eapply MEMSRC. eapply memory_future_concrete_promised; eauto.
              eapply Memory.future_future_weak; eauto. }
            { inv PROMTGT. eapply SOUND in GET. des. econs; eauto. }
          }
          { exploit PFConfiguration.opt_step_trace_future; try apply STEPSRC; eauto. i. des.
            exploit sim_configuration_sim_thread; try apply SIM; eauto.
            { ss. erewrite IdentMap.gss. ss. }
            ss. i. des. ii. eapply sim_thread_forget in H; try apply SIM1; cycle 1.
            { eapply WF2; eauto. }
            ss. des. eapply WRITTEN in IN. inv PROMTGT. clarify. }
        }
      }
    }
    { exfalso. dup SIM. inv SIM. ss. specialize (THSPF tid). specialize (THSJOIN tid).
      rewrite TIDTGT in *. unfold option_rel in *. des_ifs.
      specialize (BOT _ Heq0). des. rewrite PLS in *. destruct pl0; ss.
    }
  Qed.

  Lemma sim_configuration_promises_forget_bot tids tid
        views0 prom extra proml
        c_src0 c_mid0 c_tgt0
        (SIM: sim_configuration tids views0 prom extra proml c_src0 c_mid0 c_tgt0)
        (TIDS: tids tid)
        (PROMBOT: forall loc ts, ~ prom tid loc ts)
    :
      extra tid = bot3.
  Proof.
    destruct (IdentMap.find tid (Configuration.threads c_tgt0)) as [[[lang_tgt st_tgt] lc_tgt]|] eqn:TIDTGT; cycle 1.
    { dup SIM. inv SIM. exploit BOT.
      { specialize (THSPF tid). specialize (THSJOIN tid). ss.
        rewrite TIDTGT in *. unfold option_rel in *. des_ifs. eauto. }
      i. des. esplits; eauto.
      extensionality loc. extensionality ts. extensionality from.
      apply Coq.Logic.PropExtensionality.propositional_extensionality.
      split; i; ss. eapply EXTRA; eauto.
    }
    { extensionality loc. extensionality ts. extensionality from.
      apply Coq.Logic.PropExtensionality.propositional_extensionality. split; i; ss.
      inv SIM. specialize (THSPF tid). specialize (THSJOIN tid). ss.
      rewrite TIDTGT in *. unfold option_rel in *. des_ifs. inv THSPF.
      inv LOCAL. eapply PROMS in H. des. eapply PROMBOT in FORGET. ss. }
  Qed.

  Lemma sim_configuration_promises_list_nil tids tid
        views0 prom extra proml
        c_src0 c_mid0 c_tgt0
        (SIM: sim_configuration tids views0 prom extra proml c_src0 c_mid0 c_tgt0)
        (TIDS: tids tid)
        (NIL: proml tid = [])
    :
      (<<PROM: prom tid = bot2>>) /\
      (<<EXTRA:extra tid = bot3>>).
  Proof.
    destruct (IdentMap.find tid (Configuration.threads c_tgt0)) as [[[lang_tgt st_tgt] lc_tgt]|] eqn:TIDTGT; cycle 1.
    { dup SIM. inv SIM. exploit BOT.
      { specialize (THSPF tid). specialize (THSJOIN tid). ss.
        rewrite TIDTGT in *. unfold option_rel in *. des_ifs. eauto. }
      i. des. esplits; eauto.
      { extensionality loc. extensionality ts.
        apply Coq.Logic.PropExtensionality.propositional_extensionality.
        split; i; ss. eapply PROM; eauto. }
      { extensionality loc. extensionality ts. extensionality from.
        apply Coq.Logic.PropExtensionality.propositional_extensionality.
        split; i; ss. eapply EXTRA; eauto. }
    }
    { assert (PROM: prom tid = bot2).
      { inv SIM. dup TIDTGT. eapply CONSISTENT in TIDTGT; eauto.
        extensionality loc. extensionality ts.
        apply Coq.Logic.PropExtensionality.propositional_extensionality. split; i; ss.
        eapply CONSISTENT in H; eauto. rewrite NIL in *. ss. }
      splits; auto.
      eapply sim_configuration_promises_forget_bot; eauto.
      erewrite PROM. ss.
    }
  Qed.

  Lemma sim_configuration_certify tids views0 prom extra proml
        c_src0 c_mid0 c_tgt0 tid tm
        (SIM: sim_configuration tids views0 prom extra proml c_src0 c_mid0 c_tgt0)
        (WF_SRC: Configuration.wf c_src0)
        (PFSRC: PF.pf_configuration L c_src0)
        (WF_MID: JConfiguration.wf views0 c_mid0)
        (WF_TGT: Configuration.wf c_tgt0)
        (TIDS: tids tid)
    :
      exists tr_src tr_tgt tr_cert c_src1 c_mid1 c_tgt1 views1 e extra1 proml1,
        (<<STEPSRC: PFConfiguration.opt_step_trace L tr_src e tid c_src0 c_src1>>) /\
        (<<STEPMID: JConfiguration.opt_step e tid c_mid0 c_mid1 views0 views1>>) /\
        (<<STEPTGT: @times_configuration_opt_step times tr_tgt tr_cert e tid c_tgt0 c_tgt1>>) /\
        (<<TRACE: sim_traces L tr_src tr_tgt>>) /\
        __guard__((e = MachineEvent.failure) \/
                  (e = MachineEvent.silent /\
                   (<<FUTURE: good_future tm (Configuration.memory c_tgt0) (Configuration.memory c_tgt1)>>) /\
                   (<<SC: (Configuration.sc c_tgt1) = (Configuration.sc c_tgt0)>>) /\
                   (<<SIM: sim_configuration
                             tids views1
                             (fun tid' => if (Ident.eq_dec tid' tid) then bot2 else (prom tid'))
                             extra1
                             proml1
                             c_src1 c_mid1 c_tgt1>>) /\
                   (<<PROML: forall tid' (NEQ: tid <> tid'), proml1 tid' = proml tid'>>)))
  .
  Proof.
    hexploit (list_match_rev (proml tid)). i. des.
    { esplits; eauto.
      { econs 2; eauto. }
      { econs 2; eauto. }
      { econs; eauto. }
      right. splits; auto.
      { refl. }
      hexploit sim_configuration_promises_list_nil; try apply H; eauto. i. des.
      replace (fun tid' : Ident.t => if LocSet.Facts.eq_dec tid' tid then bot2 else prom tid')
        with prom; cycle 1.
      { extensionality tid'. des_ifs. }
      eauto.
    }
    { destruct hd_rev as [ploc pts].
      hexploit (@sim_configuration_certify_partial
                  tids tid ploc pts tl_rev []); eauto.
      i. des. unguard. des.
      { esplits; eauto. }
      destruct (IdentMap.find tid (Configuration.threads c_tgt0)) as [[[lang_tgt st_tgt] lc_tgt]|] eqn:TIDTGT.
      { assert (PROMBOT: prom_self = bot2).
        { extensionality loc. extensionality ts.
          apply Coq.Logic.PropExtensionality.propositional_extensionality. split; i; ss.
          exploit DECR; eauto. i.
          inv SIM. hexploit CONSISTENT; eauto. i.
          hexploit (pi_consistent_promises H0); eauto. i.
          rewrite H in *. eapply WRITTEN; eauto. } subst.
        esplits; eauto. right. splits; eauto.
      }
      { assert (PROMBOT: prom_self = bot2).
        { inv STEPTGT; ss.
          { dep_inv STEP; ss. }
          { inv SIM0. specialize (THSPF tid). specialize (THSJOIN tid). ss.
            rewrite TIDTGT in *. unfold option_rel in *. des_ifs.
            eapply BOT in Heq0. des.
            extensionality loc. extensionality ts.
            apply Coq.Logic.PropExtensionality.propositional_extensionality. split; i; ss.
            eapply PROM. des_ifs; eauto.
          }
        }
        subst. esplits; eauto.
        right. splits; eauto.
      }
    }
    Unshelve.
    { eapply extra1. }
    { eapply proml1. }
  Qed.

  Lemma sim_configuration_certify_list
        (tidl: list Ident.t)
        tids views0 prom extra proml
        c_src0 c_mid0 c_tgt0 tm
        (SIM: sim_configuration tids views0 prom extra proml c_src0 c_mid0 c_tgt0)
        (WF_SRC: Configuration.wf c_src0)
        (PFSRC: PF.pf_configuration L c_src0)
        (WF_MID: JConfiguration.wf views0 c_mid0)
        (WF_TGT: Configuration.wf c_tgt0)
        (ALL: List.Forall tids tidl)
    :
      exists trs c_src1 c_mid1 c_tgt1 views1 extra1 proml1,
        (<<WF_SRC: Configuration.wf c_src1>>) /\
        (<<PFSRC: PF.pf_configuration L c_src1>>) /\
        (<<WF_MID: JConfiguration.wf views1 c_mid1>>) /\
        (<<WF_TGT: Configuration.wf c_tgt1>>) /\
        (<<STEPSRC: PFConfiguration.silent_steps_trace L c_src0 c_src1 trs>>) /\
        (<<THS: forall tid (TID: ~ List.In tid tidl),
            IdentMap.find tid (Configuration.threads c_tgt0) =
            IdentMap.find tid (Configuration.threads c_tgt1)>>) /\
        __guard__((<<FAIL: exists tid c_src2,
                      (<<TID: List.In tid tidl>>) /\
                      (<<STEP: PFConfiguration.multi_step L MachineEvent.failure tid c_src1 c_src2>>)>>) \/
                  ((<<FUTURE: good_future tm (Configuration.memory c_tgt0) (Configuration.memory c_tgt1)>>) /\
                   (<<SC: (Configuration.sc c_tgt1) = (Configuration.sc c_tgt0)>>) /\
                   (<<SIM: sim_configuration
                             tids views1
                             (fun tid' => if (List.in_dec Ident.eq_dec tid' tidl) then bot2 else (prom tid'))
                             extra1 proml1
                             c_src1 c_mid1 c_tgt1>>) /\
                   (<<PROML: forall tid (TID: ~ List.In tid tidl),
                       proml tid = proml1 tid>>)))
  .
  Proof.
    Local Opaque List.in_dec.
    ginduction tidl.
    { i. eexists _, c_src0, c_mid0, c_tgt0, views0. esplits; auto.
      { econs. }
      right.
      replace (fun tid':Ident.t => if (List.in_dec Ident.eq_dec tid' (@nil Ident.t)) then bot2 else (prom tid')) with prom; cycle 1.
      { extensionality tid. des_ifs. }
      splits; auto.
      { refl. }
      { eauto. }
    }
    { i. inv ALL. exploit sim_configuration_certify; eauto.
      i. des. destruct x0; des; subst.
      { subst. dep_inv STEPSRC.
        eexists _, c_src0, c_mid0, c_tgt0, views0. esplits; auto.
        { econs. }
        left. esplits.
        { ss. left. auto. }
        { econs. esplits; eauto. }
      }
      exploit IHtidl; eauto.
      { eapply PFConfiguration.opt_step_trace_future; eauto. }
      { eapply PFConfiguration.opt_step_trace_future; eauto. }
      { eapply JConfiguration.opt_step_future; eauto. }
      { eapply times_configuration_opt_step_future; eauto. }
      { i. des. dep_inv STEPSRC.
        { eexists _, c_src2, c_mid2, c_tgt2, views2. esplits; eauto.
          { econs 2; eauto. }
          { i. erewrite <- THS; eauto. dep_inv STEPTGT.
            dep_inv STEP0. erewrite IdentMap.gsspec. des_ifs.
            exfalso. eapply TID; auto. }
          unguard. des.
          { left. esplits; eauto. }
          { right. instantiate (1:=proml0). esplits; eauto.
            { etrans; eauto. }
            { etrans; eauto. }
            { match goal with
              | H:sim_configuration ?tids ?v ?f0 ?g0 ?h0 ?c0 ?c1 ?c2
                |- sim_configuration tids ?v ?f1 ?g1 ?h1 ?c ?c1 ?c2 =>
                (replace f1 with f0); eauto
              end.
              { extensionality tid. des_ifs; ss; des; exfalso; eauto. }
            }
            { i. apply not_or_and in TID. des. erewrite <- PROML; eauto. }
          }
        }
        { eexists _, c_src2, c_mid2, c_tgt2, views2. esplits; auto.
          { eauto. }
          { i. erewrite <- THS; eauto. dep_inv STEPTGT.
            dep_inv STEP. erewrite IdentMap.gsspec. des_ifs.
            exfalso. eapply TID; auto. }
          unguard. des.
          { left. esplits; eauto. }
          { right. instantiate (1:=proml0). esplits; auto.
            { etrans; eauto. }
            { etrans; eauto. }
            { match goal with
              | H:sim_configuration ?tids ?v ?f0 ?g0 ?h0 ?c0 ?c1 ?c2
                |- sim_configuration ?tids ?v ?f1 ?g1 ?h1 ?c ?c1 ?c2 =>
                (replace f1 with f0); eauto
              end.
              { extensionality tid. des_ifs; ss; des; exfalso; eauto. }
            }
            { i. apply not_or_and in TID. des. erewrite <- PROML; eauto. }
          }
        }
      }
    }
    Unshelve.
    { eapply extra1. }
    { eapply proml1. }
  Qed.

  Lemma sim_configuration_certify_all
        (ctids: Ident.t -> Prop) (ctids_dec: forall tid, { ctids tid } + { ~ ctids tid})
        (tids: Ident.t -> Prop) views0 prom extra proml
        (CTIDS: forall tid (CTID: ctids tid), tids tid)
        c_src0 c_mid0 c_tgt0 tm
        (SIM: sim_configuration tids views0 prom extra proml c_src0 c_mid0 c_tgt0)
        (WF_SRC: Configuration.wf c_src0)
        (PFSRC: PF.pf_configuration L c_src0)
        (WF_MID: JConfiguration.wf views0 c_mid0)
        (WF_TGT: Configuration.wf c_tgt0)
    :
      exists trs c_src1 c_mid1 c_tgt1 views1 extra1 proml1,
        (<<WF_SRC: Configuration.wf c_src1>>) /\
        (<<PFSRC: PF.pf_configuration L c_src1>>) /\
        (<<WF_MID: JConfiguration.wf views1 c_mid1>>) /\
        (<<WF_TGT: Configuration.wf c_tgt1>>) /\
        (<<STEPSRC: PFConfiguration.silent_steps_trace L c_src0 c_src1 trs>>) /\
        (<<THS: forall tid (TID: ~ ctids tid),
            IdentMap.find tid (Configuration.threads c_tgt0) =
            IdentMap.find tid (Configuration.threads c_tgt1)>>) /\
        __guard__((<<FAIL: exists tid c_src2,
                      (<<TID: ctids tid>>) /\
                      (<<STEP: PFConfiguration.multi_step L MachineEvent.failure tid c_src1 c_src2>>)>>) \/
                  ((<<FUTURE: good_future tm (Configuration.memory c_tgt0) (Configuration.memory c_tgt1)>>) /\
                   (<<SC: (Configuration.sc c_tgt1) = (Configuration.sc c_tgt0)>>) /\
                   (<<SIM: sim_configuration
                             tids
                             views1
                             (fun tid' => if (ctids_dec tid') then bot2 else (prom tid'))
                             extra1 proml1
                             c_src1 c_mid1 c_tgt1>>) /\
                    (<<PROML: forall tid (TID: ~ ctids tid),
                       proml tid = proml1 tid>>))).
  Proof.
    hexploit (@sim_configuration_certify_list
                (List.filter
                   (fun tid => if ctids_dec tid then true else false)
                   (List.map fst (IdentMap.elements (Configuration.threads c_src0))))); eauto.
    { eapply List.Forall_forall. i.
      eapply List.filter_In in H. des. des_ifs.
      eapply List.in_map_iff in H; eauto. }
    i. des. esplits; try apply STEPSRC; eauto.
    { i. eapply THS. ii. eapply List.filter_In in H. des. des_ifs. }
    unguard. des.
    { left. esplits; eauto.
      eapply List.filter_In in TID. des. des_ifs. }
    { right. instantiate (1:=proml1). esplits; eauto.
      { match goal with
        | H:sim_configuration ?tids ?v ?f0 ?g0 ?h0 ?c0 ?c1 ?c2
          |- sim_configuration ?tids ?v ?f1 ?g1 ?h1 ?c ?c1 ?c2 =>
          (replace f1 with f0); eauto
        end.
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
      { ii. eapply PROML. ii. eapply List.filter_In in H. des. des_ifs. }
    }
  Qed.

  Lemma tevent_ident_map_weak f e fe
        (MAP: tevent_map_weak f fe e)
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

  Lemma good_future_configuration_step_aux c0 c1 c0' e tid (tr0 tr_cert0: Trace.t) tm
        lang st lc0 lc1 sc_tmp
        (STEP: times_configuration_step times tr0 tr_cert0 e tid c0 c0')
        (WF0: Configuration.wf c0)
        (WF1: Configuration.wf c1)
        (MWFTGT: memory_times_wf times (Configuration.memory c1))
        (TID0: IdentMap.find tid (Configuration.threads c0) =
               Some (existT _ lang st, lc0))
        (TID1: IdentMap.find tid (Configuration.threads c1) =
               Some (existT _ lang st, lc1))
        (LOCAL: local_map
                  (fun loc ts fts => ts = fts /\ Time.lt ts (tm loc))
                  lc0
                  lc1)
        (MEM: memory_map
                (fun loc ts fts => ts = fts /\ Time.lt ts (tm loc))
                (Configuration.memory c0) (Configuration.memory c1))
        (TM: forall loc, Time.lt (Memory.max_ts loc (Configuration.memory c0)) (tm loc))
        (SCMAP: timemap_map
                  (fun loc ts fts => ts = fts /\ Time.lt ts (tm loc))
                  (Configuration.sc c0) sc_tmp)
        (SCLE: TimeMap.le (Configuration.sc c1) sc_tmp)
        (TIME: List.Forall (fun the => wf_time_evt (fun loc ts => Time.lt ts (tm loc)) (snd the)) (tr0 ++ tr_cert0))
    :
      exists (tr1: Trace.t) tr_cert1 c1' f_good,
        (<<STEP: times_configuration_step times tr1 tr_cert1 e tid c1 c1'>>) /\
        (<<TRACE: List.Forall2
                    (fun the0 the1 =>
                       (<<EVT: sim_event (snd the0) (snd the1)>>) /\
                       (<<TVIEW: TView.le (Local.tview (fst the1)) (Local.tview (fst the0))>>)) tr0 tr1>>) /\
        (<<TRACECERT: List.Forall2
                    (fun the0 the1 =>
                       (<<EVT: tevent_map_weak f_good (snd the1) (snd the0)>>)) tr_cert0 tr_cert1>>) /\
        (<<GOOD:
           __guard__(exists st' lc0' lc1' sc_tmp',
                        (<<TID0: IdentMap.find tid (Configuration.threads c0') =
                                 Some (existT _ lang st', lc0')>>) /\
                        (<<TID1: IdentMap.find tid (Configuration.threads c1') =
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
                (Configuration.memory c0)).
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
              exists tr_cert1 f_good,
                (<<NORMAL:
                   forall (NEQ: ThreadEvent.get_machine_event fe <> MachineEvent.failure),
                     pf_consistent_super_strong
                       (Thread.mk _ st3 flc0 fsc0 fmem0)
                       tr_cert1 times>>) /\
                (<<SYSCALL: (exists se, ThreadEvent.get_machine_event fe = MachineEvent.syscall se) -> tr_cert1 = []>>) /\
                (<<FAILURE:
                   forall (EQ: ThreadEvent.get_machine_event fe = MachineEvent.failure),
                     tr_cert1 = []>>) /\
                (<<TRACECERT: List.Forall2
                                (fun the0 the1 =>
                                   (<<EVT: tevent_map_weak f_good (snd the1) (snd the0)>>)) tr_cert0 tr_cert1>>)).
    { hexploit (@concrete_promise_max_timemap_exists memory3 (Local.promises lc3)); eauto.
      { eapply CLOSED1. } intros [max MAX]. des.
      destruct (classic (e0 = ThreadEvent.failure)).
      { exists [], ident_map. splits; ss.
        { ii. subst. ss. }
        { exploit CERTBOT; eauto. i. subst. econs. }
      }
      { specialize (CONSISTENT H).
        hexploit good_future_consistent; eauto.
        { i. ss. des. auto. }
        { eapply map_ident_in_memory_bot; eauto. }
        { eapply Forall_app_inv in TIMES. des. inv FORALL4; ss.
          eapply memory_times_wf_traced in STEPS0; eauto; cycle 1.
          { eapply List.Forall_forall. i.
            eapply list_Forall2_in in H0; eauto. des.
            eapply List.Forall_forall in IN; try apply FORALL1; eauto. ss.
            destruct a, x. ss. inv EVENT0; ss; des; subst; auto. }
          { eapply step_memory_times_wf in STEP1; eauto.
            inv EVT; ss; des; subst; auto. }
        }
        i. des. esplits; eauto.
        { i. des. destruct fe; ss. destruct e0; ss. clarify.
          exploit CERTBOT; eauto. i. subst. inv TRACE0. auto. }
        { i. rewrite EQ in *. clarify. destruct e0; ss. }
      }
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
      { i. subst. des; clarify; eauto. ss. eapply SYSCALL; eauto. }
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
    { eauto. }
    { unguard. exists st3, lc3, flc0, fsc1'0. splits; eauto.
      { erewrite IdentMap.gss; eauto. }
      { ss. erewrite IdentMap.gss; eauto. }
    }
  Qed.

  Lemma configuration_step_certify c0 c1 e tid (tr tr_cert: Trace.t)
        (WF: Configuration.wf c0)
        (STEP: times_configuration_step_strong times tr tr_cert e tid c0 c1)
    :
      exists c2 tr_cert' f e',
        (<<STEP: times_configuration_step times (tr ++ tr_cert') [] e' tid c0 c2>>) /\
        (<<MAPLT: mapping_map_lt f>>) /\
        (<<MAPIDENT:
           forall loc ts fts to
                  (CONCRETE: concrete_promised (Configuration.memory c1) loc to)
                  (TS: Time.le ts to)
                  (MAP: f loc ts fts),
             ts = fts>>) /\
        __guard__((<<TRACE: List.Forall2 (fun em fem => tevent_map_weak f (snd fem) (snd em)) tr_cert tr_cert'>>) \/
                  (<<TRACE: exists lc, List.Forall2 (fun em fem => tevent_map_weak f (snd fem) (snd em)) (tr_cert++[(lc, ThreadEvent.failure)]) tr_cert'>>)) /\
        __guard__(e' = MachineEvent.failure \/
                  ((<<NEQ: e' <> MachineEvent.failure>>) /\
                   (<<BOT: forall lang st lc
                                  (TID: IdentMap.find tid (Configuration.threads c2) = Some (existT _ lang st, lc)),
                       (Local.promises lc) = Memory.bot>>)))
  .
  Proof.
    dup STEP. rename STEP0 into STEPWEAK.
    eapply times_configuration_step_strong_step in STEPWEAK.
    exploit times_configuration_step_future; eauto. i. des.
    dup STEP. dep_inv STEP.
    destruct (ThreadEvent.get_machine_event e0) eqn:EVENT.
    { exploit (@concrete_promise_max_timemap_exists memory3 (Local.promises lc3)).
      { eapply WF2. } i. des.
      exploit CONSISTENT.
      { ii. subst. ss. }
      { refl. }
      { eapply WF2. }
      { eapply WF2; eauto. ss. erewrite IdentMap.gss; eauto. }
      { eauto. }
      i. des. ss. instantiate (1:=fun loc => Time.incr (Memory.max_ts loc memory3)) in GOOD.
      destruct e1. ss. unguard. des.
      { esplits.
        { econs.
          { eauto. }
          { eapply Trace.steps_app.
            { eapply STEPS. }
            { econs 2.
              { eauto. }
              { eapply STEPS0. }
              { ss. }
            }
          }
          { eapply Forall_app; eauto. econs; eauto.
            eapply List.Forall_impl; eauto. i. ss. des. auto. }
          { econs 2. econs; cycle 1.
            { eapply Local.step_failure; eauto. }
            { eauto. }
          }
          { repeat erewrite <- List.app_assoc. ss. }
          { i. ss. }
          { i. ss. }
          { eapply Forall_app; eauto.
            eapply Forall_app; eauto.
            { eapply List.Forall_impl; eauto. i. ss. des; auto. }
            { econs; ss; eauto. }
          }
        }
        { eauto. }
        { ii. destruct (Time.le_lt_dec fts (tm loc)).
          { eapply MAPIDENT; eauto. }
          { dup l. eapply BOUND in l; eauto. des.
            inv CONCRETE. eapply MAX in GET.
            exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
            { eapply l. } etrans.
            { eapply TS. }
            eauto.
          }
        }
        { right. exists local. esplits. eapply List.Forall2_app; eauto.
          econs; eauto. ss. econs. }
        { left. auto. }
      }
      { hexploit (list_match_rev ftr). i. des; subst.
        { inv TRACE. inv STEPS0; ss.
          eexists _, [], ident_map, MachineEvent.silent.
          erewrite List.app_nil_r. splits; eauto.
          { eapply ident_map_lt. }
          right. splits; ss.
          i. erewrite IdentMap.gss in TID0. dep_clarify.
        }
        { eapply Trace.steps_separate in STEPS0. des.
          inv STEPS2; ss. inv TR. inv STEPS0; ss.
          eapply Forall_app_inv in TIMES.
          eapply Forall_app_inv in EVENTS. des. inv FORALL2. ss. des.
          esplits.
          { econs.
            { eauto. }
            { eapply Trace.steps_app.
              { eapply STEPS. }
              { econs 2.
                { eauto. }
                { eapply STEPS1. }
                { ss. }
              }
            }
            { eapply Forall_app; eauto. econs; eauto.
              eapply List.Forall_impl; eauto. i. ss. des. auto. }
            { eauto. }
            { repeat erewrite <- List.app_assoc. ss. }
            { i. ss. eapply promises_bot_certify_nil; eauto. }
            { i. subst. ss. }
            { eapply Forall_app; eauto.
              { eapply Forall_app; eauto. }
              { eapply Forall_app; eauto.
                eapply List.Forall_impl; eauto. i. ss. des; auto. }
            }
          }
          { eauto. }
          { ii. destruct (Time.le_lt_dec fts (tm loc)).
            { eapply MAPIDENT; eauto. }
            { dup l. eapply BOUND in l; eauto. des.
              inv CONCRETE. eapply MAX in GET.
              exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
              { eapply l. } etrans.
              { eapply TS. }
              eauto.
            }
          }
          { ii. auto. }
          { right. splits; auto.
            { ii. erewrite H in *. ss. }
            { i. ss. erewrite IdentMap.gss in TID0. dep_clarify. }
          }
        }
      }
    }
    { assert (BOT: Local.promises lc3 = Memory.bot).
      { destruct e0; ss. inv STEP1; inv STEP; ss. inv LOCAL.
        inv LOCAL0; ss. eauto. }
      hexploit CERTBOTNIL; auto. i. subst.
      eexists _, [], ident_map. erewrite List.app_nil_r. esplits; eauto.
      { eapply ident_map_lt. }
      { left. auto. }
      { right. splits; ss.
        i. ss. erewrite IdentMap.gss in TID0. dep_clarify. }
    }
    { hexploit CERTBOT.
      { destruct e0; ss. auto. } i. subst.
      eexists _, [], ident_map. erewrite List.app_nil_r. esplits; eauto.
      { eapply ident_map_lt. }
      { left. auto. }
      { left. auto. }
    }
  Qed.

  Lemma list_final_exists A (P: A -> Prop) (l: list A)
    :
      (<<ALL: List.Forall P l>>) \/
      (exists l0 a l1,
          (<<EQ: l = l0 ++ a :: l1>>) /\
          (<<SAT: ~ P a>>) /\
          (<<TL: List.Forall P l1>>)).
  Proof.
    induction l.
    { left. econs. }
    { des.
      { destruct (classic (P a)).
        { left. econs; eauto. }
        { right. exists [], a, l. splits; auto. }
      }
      { subst. right. exists (a :: l0), a0, l1. splits; auto. }
    }
  Qed.

  Lemma sim_configuration_forget_tgt_concrete
        tids views prom extra proml c_src c_mid c_tgt
        (SIM: sim_configuration tids views prom extra proml c_src c_mid c_tgt)
        tid loc ts
        (PROM: prom tid loc ts)
        (TID: tids tid)
        (WF: Configuration.wf c_tgt)
    :
      (<<CONCRETE: concrete_promised (Configuration.memory c_tgt) loc ts>>)
      /\ (<<LOC: L loc>>).
  Proof.
    inv SIM. specialize (THSJOIN tid). specialize (THSPF tid).
    unfold option_rel in THSJOIN. unfold option_rel in THSPF. des_ifs.
    { dep_inv THSPF. dep_inv THSJOIN. dep_inv LOCAL. dep_inv LOCAL0.
      set (CNT0:=(sim_promise_contents PROMS) loc ts).
      set (CNT1:=PROMISES loc ts).
      inv CNT0; ss. rewrite <- H in *. inv CNT1; ss.
      inv WF. ss. eapply WF0 in Heq0.
      symmetry in H5. eapply Heq0 in H5. splits; auto. econs; eauto.
    }
    { eapply BOT in Heq1. des. exfalso. eapply PROM0; eauto. }
  Qed.

  Lemma promise_read_race views0 prom0 extra0 proml0
        c_src0 c_mid0 c_tgt0 c_tgt1 e tid tr_tgt tr_cert
        (STEPTGT: @times_configuration_step_strong times tr_tgt tr_cert e tid c_tgt0 c_tgt1)
        (SIM: sim_configuration (fun _ => True) views0 prom0 extra0 proml0 c_src0 c_mid0 c_tgt0)
        (READ: ~ List.Forall
                 (fun the => no_read_msgs
                               (all_promises (fun tid' => tid <> tid') prom0)
                               (snd the)) (tr_tgt ++ tr_cert))
        (WF_SRC: Configuration.wf c_src0)
        (PFSRC: PF.pf_configuration L c_src0)
        (WF_MID: JConfiguration.wf views0 c_mid0)
        (WF_TGT: Configuration.wf c_tgt0)
        (RACEFREE: PFRace.multi_racefree L c_src0)
    :
      (<<BEH: forall beh, behaviors (PFConfiguration.multi_step L) c_src0 beh>>) \/
      (exists s, (<<EVENT: e = MachineEvent.syscall s>>) /\
                 (<<BEH: forall beh,
                     behaviors (PFConfiguration.multi_step L) c_src0 (s :: beh)>>)).
  Proof.
    exploit times_configuration_step_future; eauto.
    { eapply times_configuration_step_strong_step; eauto. } i. des.
    exploit (@Memory.max_concrete_timemap_exists (Configuration.memory c_tgt1)); eauto.
    { eapply WF2. } intros [max MAX].
    eapply configuration_step_certify in STEPTGT; eauto. des.
    hexploit (@trace_times_list_exists (tr_tgt ++ tr_cert')). i. des.
    assert (exists (maxmap: TimeMap.t),
               (<<TIMES: forall loc' ts (IN: List.In ts (times0 loc')), Time.lt ts (maxmap loc')>>) /\
               (<<MAX: forall loc', Time.lt (Memory.max_ts loc' (Configuration.memory c_tgt0)) (maxmap loc')>>)).
    { hexploit (@choice
                  Loc.t
                  Time.t
                  (fun loc' max =>
                     (<<TIMES: forall ts (IN: List.In ts (times0 loc')), Time.lt ts (max)>>) /\
                     (<<MAX: Time.lt (Memory.max_ts loc' (Configuration.memory c_tgt0)) (max)>>))).
      { i. hexploit (finite_greatest (fun _ => True) (times0 x)). i. des.
        { exists (Time.incr (Time.join
                               (Memory.max_ts x (Configuration.memory c_tgt0))
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
        { exists (Time.incr (Memory.max_ts x (Configuration.memory c_tgt0))). splits.
          { i. eapply EMPTY in IN. ss. }
          { eapply Time.incr_spec. }
        }
      }
      i. des. exists f0. split.
      { ii. specialize (H loc'). des. auto. }
      { ii. specialize (H loc'). des. auto. }
    } i. des.
    assert (exists tid0 ploc pts rlc re pl0 pl1,
               (<<READING: PFRace.reading_event ploc pts re>>) /\
               (<<IN: List.In (rlc, re) (tr_tgt ++ tr_cert')>>) /\
               (<<PROMISED: prom0 tid0 ploc pts>>) /\
               (<<NEQ: tid0 <> tid>>) /\
               (<<PROML: proml0 tid0 = pl0 ++ (ploc, pts) :: pl1>>) /\
               (<<NOREAD:
                  List.Forall
                    (fun the =>
                       no_read_msgs (fun loc ts => List.In (loc, ts) pl1 /\ prom0 tid0 loc ts) (snd the)) (tr_tgt ++ tr_cert')>>)).
    { assert (exists tid0 loc ts rlc0 re0,
                 (<<READING0: PFRace.reading_event loc ts re0>>) /\
                 (<<IN0: List.In (rlc0, re0) (tr_tgt ++ tr_cert)>>) /\
                 (<<PROMISED: prom0 tid0 loc ts>>) /\
                 (<<NEQ: tid0 <> tid>>)).
      { apply NNPP. ii. eapply READ. eapply List.Forall_forall. i.
        eapply NNPP. ii. eapply H. unfold no_read_msgs in *. des_ifs.
        { apply NNPP in H1. inv H1. destruct x. ss. subst.
          esplits; eauto. econs; eauto. }
        { apply NNPP in H1. inv H1. destruct x. ss. subst.
          esplits; eauto. econs; eauto. }
      } des.
      assert (CONCRETE: concrete_promised (Configuration.memory c_tgt1) loc ts).
      { eapply memory_future_concrete_promised.
        { eapply Memory.future_future_weak; eauto. }
        eapply sim_configuration_forget_tgt_concrete; eauto; ss.
      }
      assert (exists rlc re,
                 (<<READING0: PFRace.reading_event loc ts re>>) /\
                 (<<IN0: List.In (rlc, re) (tr_tgt ++ tr_cert')>>)).
      { eapply List.in_app_or in IN0. des.
        { esplits; eauto. eapply List.in_or_app. eauto. }
        { destruct STEPTGT0.
          { des. eapply list_Forall2_in2 in IN0; eauto. des. ss.
            destruct b. exists t, t0. ss. splits.
            { inv READING0; inv SAT; eauto.
              { eapply MAPIDENT in TO; eauto.
                { subst. econs; eauto. }
                { refl. }
              }
              { eapply MAPIDENT in FROM; eauto.
                { subst. econs; eauto. }
                { refl. }
              }
            }
            { eapply List.in_or_app; eauto. }
          }
          { des. exploit list_Forall2_in2.
            { eapply H. }
            { eapply List.in_or_app. eauto. }
            i. des. ss.
            destruct b. exists t, t0. ss. splits.
            { inv READING0; inv SAT; eauto.
              { eapply MAPIDENT in TO; eauto.
                { subst. econs; eauto. }
                { refl. }
              }
              { eapply MAPIDENT in FROM; eauto.
                { subst. econs; eauto. }
                { refl. }
              }
            }
            { eapply List.in_or_app; eauto. }
          }
        }
      }
      des.
      assert (LIN: List.In (loc, ts) (proml0 tid0)).
      { destruct (IdentMap.find tid0 (Configuration.threads c_tgt0)) as [[[lang_tgt st_tgt] lc_tgt]|] eqn:TIDTGT.
        { inv SIM. eapply CONSISTENT in TIDTGT; eauto.
          eapply (pi_consistent_promises TIDTGT) in PROMISED. auto. }
        { inv SIM. ss. specialize (THSJOIN tid0). specialize (THSPF tid0).
          unfold option_rel in THSJOIN.
          unfold option_rel in THSPF. des_ifs.
          eapply BOT in Heq1. des. exfalso. eapply PROM; eauto. }
      }
      hexploit (list_final_exists
                  (fun locts =>
                     ~ prom0 tid0 (fst locts) (snd locts) \/
                     List.Forall (fun the =>
                                    no_read_msgs (fun loc0 ts0 => (loc0, ts0) = locts /\ prom0 tid0 loc0 ts0) (snd the)) (tr_tgt ++ tr_cert'))
                  (proml0 tid0)).
      i. des.
      { exfalso. eapply List.Forall_forall in ALL; eauto. des; ss.
        eapply List.Forall_forall in ALL; eauto. ss.
        unfold no_read_msgs in ALL. inv READING1; ss.
        { eapply ALL. splits; auto. }
        { eapply ALL. splits; auto. }
      }
      { apply not_or_and in SAT. des. apply NNPP in SAT. destruct a. ss.
        assert (exists rlc' re',
                   (<<READING: PFRace.reading_event t t0 re'>>) /\
                   (<<IN: List.In (rlc', re') (tr_tgt ++ tr_cert')>>)).
        { apply NNPP. ii. eapply SAT0. eapply List.Forall_forall.
          i. destruct x. ss. unfold no_read_msgs. des_ifs.
          { ii. des; clarify. eapply H. esplits; eauto. econs; eauto. }
          { ii. des; clarify. eapply H. esplits; eauto. econs; eauto. }
        }
        des. esplits; eauto. apply List.Forall_forall. i.
        destruct x. ss. unfold no_read_msgs. des_ifs.
        { ii. des. eapply List.Forall_forall in H0; eauto. ss. des; ss.
          eapply List.Forall_forall in H0; eauto. ss. eapply H0; eauto. }
        { ii. des. eapply List.Forall_forall in H0; eauto. ss. des; ss.
          eapply List.Forall_forall in H0; eauto. ss. eapply H0; eauto. }
      }
    }
    des.

    exploit sim_configuration_forget_tgt_concrete.
    { eapply SIM. }
    { eapply PROMISED. }
    { ss. }
    { auto. }
    i. des.

    assert (DEC: forall (tid'': Ident.t), { (fun tid' => tid <> tid' /\ tid0 <> tid') tid'' } + { ~ (fun tid' => tid <> tid' /\ tid0 <> tid') tid''}).
    { i. destruct (Ident.eq_dec tid tid''), (Ident.eq_dec tid0 tid''); subst; ss.
      { right. ii. des; ss. }
      { right. ii. des; ss. }
      { left. split; auto. }
    }

    exploit (@sim_configuration_certify_all _ DEC); eauto; ss.
    i. des. destruct x0; des.
    { left. ii. eapply PFConfiguration.silent_multi_steps_trace_behaviors; eauto.
      econs 3; eauto. }

    exploit (@sim_configuration_certify_partial
               (fun _ => True) tid0 ploc pts pl0 pl1); eauto.
    { erewrite <- PROML0; eauto. ii. des; ss. }
    i. des. destruct x0; des.
    { left. ii. eapply PFConfiguration.silent_multi_steps_trace_behaviors; eauto.
      inv STEPSRC0; ss. econs 3; eauto. econs; eauto. }

    hexploit times_configuration_opt_step_future; try apply STEPTGT; eauto. i. des.
    hexploit JConfiguration.opt_step_future; try apply STEPMID; eauto. i. des.
    hexploit PFConfiguration.opt_step_trace_future; try apply STEPSRC0; eauto. i. des.

    assert (IDENT: map_ident_in_memory (fun loc ts fts => ts = fts /\ Time.lt ts (maxmap loc))
                                       (Configuration.memory c_tgt0)).
    { ii. splits; auto. eapply TimeFacts.le_lt_lt; eauto. }
    assert (MAPLT0: mapping_map_lt (fun loc ts fts => ts = fts /\ Time.lt ts (maxmap loc))).
    { ii. des. subst. auto. }

    dup STEP. dep_inv STEP.
    exploit good_future_configuration_step_aux.
    { eapply STEP0. }
    { eauto. }
    { eapply WF0. }
    { inv SIM1. auto. }
    { eauto. }
    { erewrite <- TID. erewrite THS; eauto.
      { inv STEPTGT; auto. inv STEP; auto.
        ss. erewrite IdentMap.gso; eauto. }
      { ii. des; ss. }
    }
    { eapply map_ident_in_memory_local; eauto.
      { eapply WF_TGT; eauto. }
      { eapply WF_TGT; eauto. }
    }
    { eapply max_good_future_map; eauto. etrans; eauto. eapply WF_TGT. }
    { eauto. }
    { eapply map_ident_in_memory_closed_timemap; eauto. eapply WF_TGT. }
    { erewrite SC0. erewrite SC. refl. }
    { erewrite app_nil_r.
      eapply List.Forall_impl; try apply WFTIME; eauto. i. ss.
      eapply wf_time_evt_mon; eauto. i. ss. eauto. }
    i. des. ss.

    exploit (@step_sim_configuration); eauto.
    { eapply List.Forall_forall. i.
      eapply list_Forall2_in in H; eauto. des.
      eapply List.Forall_forall in NOREAD; eauto.
      destruct x, a. ss.
      assert (NOREAD0: no_read_msgs
                         (fun loc ts => In (loc, ts) pl1 /\ prom0 tid0 loc ts) t0).
      { inv EVT; ss. }
      eapply no_read_msgs_mon; eauto. i. ss. inv PR.
      clear - SIM DECR WRITTEN TID0 PROMS NEQ TID PROML. des_ifs; ss.
      { eapply DECR in PROMS. ss. }
      { split; auto. dup PROMS. eapply DECR in PROMS.
        destruct (IdentMap.find tid0 (Configuration.threads c_tgt0)) as [[[lang_tgt' st_tgt'] lc_tgt']|] eqn:TIDTGT.
        { dep_inv SIM. eapply CONSISTENT in TIDTGT; ss.
          eapply (pi_consistent_promises TIDTGT) in PROMS.
          rewrite PROML in *.
          clear - PROMS WRITTEN PROMS0.
          eapply List.in_app_or in PROMS. des; ss.
          { exfalso. eapply WRITTEN; eauto. eapply List.in_or_app. eauto. }
          { des; ss. exfalso. eapply WRITTEN; eauto. eapply List.in_or_app.
            ss. eauto. }
        }
        { inv SIM. specialize (THSJOIN tid0). specialize (THSPF tid0).
          setoid_rewrite TIDTGT in THSJOIN. unfold option_rel in *. des_ifs.
          eapply BOT in Heq0. des. exfalso. eapply PROM; eauto. }
      }
      { apply not_and_or in n0. des; ss. }
      { apply not_and_or in n0. des; ss. exfalso. eapply n0. eauto. }
    }
    { ss. inv TRACECERT. ss. }
    i. des. ss.

    assert (exists rlc' re',
               (<<IN: In (rlc', re') (tr_src0)>>) /\
               (<<READING: PFRace.reading_event ploc pts re'>>)).
    { eapply list_Forall2_in2 in IN; eauto. des. ss.
      destruct b. ss. exploit sim_traces_sim_event_exists; eauto.
      { inv READING; inv EVT; ss. }
      { inv READING; inv EVT; ss. }
      i. des. esplits; eauto.
      clear - READING EVT EVENT.
      inv READING; inv EVT; inv EVENT; ss; econs. }
    des.

    exfalso. eapply RACEFREE.
    { eapply PFConfiguration.silent_steps_trace_steps_trace; eauto. }
    { eauto. }
    { eapply NEQ. }
    { inv STEPSRC0; eauto. inv FINAL. }
    { eauto. }
    { eauto. }
    { inv STEPSRC1; eauto. ss. }
    { eauto. }
    { eauto. }
  Qed.

End SIM.
