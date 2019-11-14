Require Import Omega.
Require Import RelationClasses.

From Paco Require Import paco.
From sflib Require Import sflib.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
Require Import Time.
Require Import Event.
From PromisingLib Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import Cover.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.
Require Import Progress.
Require Import PromiseConsistent.
Require Import APromiseConsistent.
From PromisingLib Require Import Loc.

Require Import PF.
Require Import Race.
Require Import Behavior.
Require Import SimMemory.
Require Import yjtac.
Require Import Program.
Require Import Cell.
Require Import Time.

Require Import Pred.
Require Import AMemory.
Require Import ALocal.
Require Import AThread.
Require Import APredStep.
Require Import ADRF_PF0.
Require Import ADRF_PF1.
Require Import ADRF_PF4.

Set Implicit Arguments.

Lemma forget_event_no_promise e_src e_tgt
      (FORGET: forget_event e_src e_tgt)
  :
    no_promise e_src.
Proof.
  unfold forget_event in *. des_ifs.
Qed.

Lemma forget_event_write_not_in L e_src e_tgt
      (FORGET: forget_event e_src e_tgt)
      (WRITENOTIN: write_not_in L e_tgt)
  :
    write_not_in L e_src.
Proof.
  unfold forget_event in *. des_ifs.
Qed.

Lemma pred_step_pred P lang th0 th1 e
      (STEP: @pred_step P lang e th0 th1)
  :
    P e.
Proof.
  inv STEP; auto.
Qed.


Inductive drf_sim_event: ThreadEvent.t -> ThreadEvent.t -> Prop :=
| drf_sim_event_read
    loc to val released ordr
  :
    drf_sim_event
      (ThreadEvent.read loc to val released ordr)
      (ThreadEvent.read loc to val released ordr)
| drf_sim_event_write
    loc from ffrom to val released ordw
    (FROM: Time.le from ffrom)
  :
    drf_sim_event
      (ThreadEvent.write loc ffrom to val released ordw)
      (ThreadEvent.write loc from to val released ordw)
| drf_sim_event_update
    loc from to valr valw releasedr releasedw ordr ordw
  :
    drf_sim_event
      (ThreadEvent.update loc from to valr valw releasedr releasedw ordr ordw)
      (ThreadEvent.update loc from to valr valw releasedr releasedw ordr ordw)
| drf_sim_event_fence
    or ow
  :
    drf_sim_event
      (ThreadEvent.fence or ow)
      (ThreadEvent.fence or ow)
| drf_sim_event_syscall
    e
  :
    drf_sim_event
      (ThreadEvent.syscall e)
      (ThreadEvent.syscall e)
| drf_sim_event_silent
  :
    drf_sim_event
      (ThreadEvent.silent)
      (ThreadEvent.silent)
| drf_sim_event_failure
  :
    drf_sim_event
      (ThreadEvent.failure)
      (ThreadEvent.failure)
| drf_sim_event_promise
    loc from to msg kind
  :
    drf_sim_event
      (ThreadEvent.silent)
      (ThreadEvent.promise loc from to msg kind)
.

Lemma drf_sim_event_same_machine_event e_src e_tgt
      (EVENT: drf_sim_event e_src e_tgt)
  :
    same_machine_event e_src e_tgt.
Proof.
  inv EVENT; ss.
Qed.

Lemma drf_sim_event_shift L
      e_src e_tgt
      (SAT: (write_not_in L /1\ no_promise) e_tgt)
      (EVT: drf_sim_event e_src e_tgt)
  :
    (write_not_in L /1\ no_promise) e_src.
Proof.
  ss. des. inv EVT; ss. split; auto. i.
  eapply SAT. inv IN. econs; ss.
  eapply TimeFacts.le_lt_lt; eauto.
Qed.

Lemma unchangables_not_promises_covered
      prom0 mem0
      (MLE: Memory.le prom0 mem0)
      loc to from msg
      (UNCH: unchangable mem0 prom0 loc to from msg)
  :
    ~ covered loc to prom0.
Proof.
  intros COVERED. inv UNCH. inv COVERED.
  exploit Memory.get_disjoint.
  { eapply GET. }
  { eapply MLE. eapply GET0. }
  i. des; clarify.
  eapply memory_get_ts_strong in GET. des; clarify.
  { inv ITV. ss. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
    - eapply FROM.
    - eapply Time.bot_spec. }
  eapply x0; eauto. econs; ss. refl.
Qed.

Lemma promise_write_not_in_unchangable (L: Loc.t -> Time.t -> Prop)
      prom0 mem0 loc from to msg prom1 mem1 kind
      (MLE: Memory.le prom0 mem0)
      (PROMISE: AMemory.promise prom0 mem0 loc from to msg prom1 mem1 kind)
      (UNCH: forall loc to (SAT: L loc to),
          exists from msg, <<UNCH: unchangable mem0 prom0 loc to from msg>>)
  :
    forall ts (ITV: Interval.mem (from, to) ts), ~ L loc ts.
Proof.
  ii. eapply UNCH in H. des.
  hexploit unchangables_not_promises_covered; eauto. intros NCOVERED.
  inv UNCH0.
  dup GET. eapply memory_get_ts_strong in GET0. des; clarify.
  { inv ITV. ss. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
    - eapply FROM.
    - eapply Time.bot_spec. }
  dup ITV. inv ITV. inv PROMISE.
  - dup PROMISES. apply Memory.add_get0 in PROMISES. des.
    eapply add_succeed_wf in MEM. des. eapply DISJOINT; eauto.
    econs; ss. refl.
  - dup PROMISES. eapply Memory.split_get0 in PROMISES; eauto. des. clarify.
    eapply split_succeed_wf in PROMISES0. des. eapply NCOVERED.
    econs; eauto. econs; ss.
    etrans; eauto. left. auto.
  - dup PROMISES. eapply Memory.lower_get0 in PROMISES; eauto. des. clarify.
    eapply lower_succeed_wf in PROMISES0. des. eapply NCOVERED.
    econs; eauto.
  - dup PROMISES. eapply Memory.remove_get0 in PROMISES; eauto. des. clarify.
    eapply NCOVERED. econs; eauto.
Qed.

Lemma write_write_not_in_unchangable (L: Loc.t -> Time.t -> Prop)
      prom0 mem0 loc from to val released prom1 mem1 kind
      (MLE: Memory.le prom0 mem0)
      (WRITE: AMemory.write prom0 mem0 loc from to val released prom1 mem1 kind)
      (UNCH: forall loc to (SAT: L loc to),
          exists from msg, <<UNCH: unchangable mem0 prom0 loc to from msg>>)
  :
    forall ts (ITV: Interval.mem (from, to) ts), ~ L loc ts.
Proof.
  inv WRITE. eapply promise_write_not_in_unchangable; eauto.
Qed.

Lemma write_not_in_unchangable (L: Loc.t -> Time.t -> Prop) lang(th0 th1: Thread.t lang) e
      (MLE: Memory.le th0.(Thread.local).(Local.promises) th0.(Thread.memory))
      (STEP: AThread.step_allpf e th0 th1)
      (UNCH: forall loc to (SAT: L loc to),
          exists from msg, <<UNCH: unchangable th0.(Thread.memory) th0.(Thread.local).(Local.promises) loc to from msg>>)
  :
    write_not_in L e.
Proof.
  inv STEP; inv STEP0.
  - inv STEP. inv LOCAL; ss. des_ifs. ii.
    eapply promise_write_not_in_unchangable in PROMISE; eauto.
  - inv STEP. inv LOCAL; ss.
    + inv LOCAL0. ii. eapply write_write_not_in_unchangable in WRITE; eauto.
    + inv LOCAL1. inv LOCAL2. ii. eapply write_write_not_in_unchangable in WRITE; eauto.
Qed.

Lemma step_lifting_raw
      lang th_src th_tgt th_tgt' st st' v v' prom prom' sc sc'
      mem_src mem_tgt mem_tgt' e_tgt others updates otherspace
      (STEP: AThread.step_allpf e_tgt th_tgt th_tgt')
      (PRED: ((write_not_in otherspace)
                /1\ (no_update_on updates)
                /1\ (no_read_msgs others)
                /1\ (no_read_msgs prom.(promised))) e_tgt)
      (OTHERS: forall loc to (SAT: others loc to),
          exists from msg, <<UNCH: unchangable mem_tgt prom loc to from msg>>)
      (TH_SRC: th_src = Thread.mk lang st (Local.mk v Memory.bot) sc mem_src)
      (TH_TGT0: th_tgt = Thread.mk lang st (Local.mk v prom) sc mem_tgt)
      (TH_TGT1: th_tgt' = Thread.mk lang st' (Local.mk v' prom') sc' mem_tgt')
      (MEM: pf_sim_memory (others \2/ promised prom) mem_src mem_tgt)
      (NOATTATCH: not_attatched updates mem_src)
      (SC: Memory.closed_timemap sc mem_tgt)
      (CLOSED: Memory.closed mem_tgt)
      (LCWF: Local.wf (Local.mk v prom) mem_tgt)
  :
    exists mem_src' e_src,
      (<<STEP: AThread.opt_step
                 e_src th_src
                 (Thread.mk lang st' (Local.mk v' Memory.bot) sc' mem_src')>>) /\
      (<<EVT: drf_sim_event e_src e_tgt>>) /\
      (<<MEM: pf_sim_memory (others \2/ promised prom') mem_src' mem_tgt'>>) /\
      (<<NOATTATCH: not_attatched updates mem_src'>>) /\
      (<<UNCHANGED: unchanged_on otherspace mem_src mem_src'>>).
Proof.
  ss. des.
  assert (PSTEP: pred_step ((write_not_in otherspace)
                              /1\ (write_not_in others)
                              /1\ (no_update_on updates)
                              /1\ (no_read_msgs others)
                              /1\ (no_read_msgs prom.(promised))) e_tgt th_tgt th_tgt').
  { econs; eauto. splits; auto.
    eapply write_not_in_unchangable; eauto.
    - inv LCWF. ss.
    - clarify. }
  hexploit (forget_exists prom.(promised) mem_tgt); eauto. i. des.
  exploit self_promise_remove; try apply FORGET; try apply PSTEP; eauto.
  { i. ss. des. auto. }
  i. des.

  inv MEM.
  assert (FORGET1: forget_memory others mem_inter mem_src0).
  { eapply forget_compose_middle; eauto. }

  inv STEP0.
  { exists mem_src, ThreadEvent.silent. esplits; eauto.
    - econs 1.
    - unfold forget_event in EVT. des_ifs; econs.
    - econs; eauto. eapply forget_compose; eauto.
    - refl. }

  exploit other_promise_remove; try eapply STEP1; eauto.
  { i. ss. des. splits; auto. }
  i. des.

  exploit shorter_memory_step; try apply STEP0; eauto.
  { ii. erewrite Memory.bot_get in LHS. clarify. }
  i. des.

  exploit no_update_on_step; try apply STEP2; eauto.
  { ii. erewrite Memory.bot_get in LHS. clarify. }
  { i. ss. des. splits; auto. destruct x0; ss. }
  { refl. }
  i. des.

  exists mem_src'2, e_src0. esplits.
  - inv STEP3. econs 2. eapply pred_step_mon; cycle 1; eauto.
  - unfold forget_event in EVT. des_ifs; inv EVT0; econs. auto.
  - econs.
    + eapply forget_compose; eauto.
    + etrans; eauto.
  - eauto.
  - exploit write_not_in_unchanged_on.
    + econs; try apply STEP3.
      instantiate (1:=write_not_in otherspace /1\ no_promise).
      eapply shorter_event_shift; eauto. split.
      * eapply forget_event_write_not_in; eauto.
      * eapply forget_event_no_promise; eauto.
    + i. apply PR.
    + ss.
    + ss.
Qed.

Inductive drf_sim_trace : list ThreadEvent.t -> list ThreadEvent.t -> Prop :=
| drf_sim_trace_nil
  :
    drf_sim_trace [] []
| drf_sim_trace_promise
    tl_src tl_tgt
    hd_tgt
    (TL: drf_sim_trace tl_src tl_tgt)
    (HD: drf_sim_event ThreadEvent.silent hd_tgt)
  :
    drf_sim_trace tl_src (hd_tgt :: tl_tgt)
| drf_sim_trace_cons
    tl_src tl_tgt
    hd_src hd_tgt
    (TL: drf_sim_trace tl_src tl_tgt)
    (HD: drf_sim_event hd_src hd_tgt)
  :
    drf_sim_trace (hd_src :: tl_src) (hd_tgt :: tl_tgt)
.

Lemma step_lifting
      lang (th_src th_tgt th_tgt': Thread.t lang)
      e_tgt others updates otherspace
      (STEP: AThread.step_allpf e_tgt th_tgt th_tgt')
      (PRED: ((no_update_on updates)
                /1\ (no_read_msgs others)) e_tgt)
      (FORGET: forget_thread others th_src th_tgt)
      (OTHERS: forall loc to (SAT: others loc to),
          exists from msg, <<UNCH: unchangable th_tgt.(Thread.memory) th_tgt.(Thread.local).(Local.promises) loc to from msg>>)
      (OTHERSPACE: otherspace <2= unwritable th_tgt.(Thread.memory) th_tgt.(Thread.local).(Local.promises))
      (CONSISTENT: Local.promise_consistent th_tgt'.(Thread.local))
      (NOATTATCH: not_attatched updates th_src.(Thread.memory))
      (SC: Memory.closed_timemap th_tgt.(Thread.sc) th_tgt.(Thread.memory))
      (CLOSED: Memory.closed th_tgt.(Thread.memory))
      (LCWF: Local.wf th_tgt.(Thread.local) th_tgt.(Thread.memory))
  :
    exists th_src' e_src,
      (<<STEP: AThread.opt_step e_src th_src th_src'>>) /\
      (<<FORGET: forget_thread others th_src' th_tgt'>>) /\
      (<<EVT: drf_sim_event e_src e_tgt>>) /\
      (<<NOATTATCH: not_attatched updates th_src'.(Thread.memory)>>) /\
      (<<UNCHANGED: unchanged_on otherspace th_src.(Thread.memory) th_src'.(Thread.memory)>>).
Proof.
  destruct th_tgt, th_tgt', th_src. destruct local, local0, local1. ss.
  exploit step_lifting_raw; eauto.
  { des. splits; auto.
    - inv STEP. eapply step_write_not_in in STEP0; ss.
      + eapply write_not_in_mon; eauto.
      + inv LCWF. auto.
    - inv STEP. eapply consistent_read_no_self_promise in STEP0; eauto. }
  { inv FORGET. auto. }
  i. des. inv FORGET. esplits; eauto. econs; eauto.
Qed.

Lemma all_steps_traced_step lang
      th0 th1
  :
    rtc (@AThread.all_step lang) th0 th1 <->
    exists tr,
      (<<STEPS: traced_step tr th0 th1>>)
.
Proof.
  split; i.
  - ginduction H; i.
    + exists []. splits; eauto. econs 1.
    + des. inv H. exists ((e, x.(Thread.memory))::tr). splits.
      econs; eauto.
  - des. ginduction STEPS; i.
    + refl.
    + econs; eauto. econs; eauto.
Qed.

Lemma traced_step_lifting
      lang (th_src th_tgt th_tgt': Thread.t lang)
      tr_tgt others updates otherspace
      (STEPS: traced_step tr_tgt th_tgt th_tgt')
      (PRED: List.Forall (fun em => ((no_update_on updates)
                                       /1\ (no_read_msgs others)) (fst em)) tr_tgt)
      (FORGET: forget_thread others th_src th_tgt)
      (OTHERS: forall loc to (SAT: others loc to),
          exists from msg, <<UNCH: unchangable th_tgt.(Thread.memory) th_tgt.(Thread.local).(Local.promises) loc to from msg>>)
      (OTHERSPACE: otherspace <2= unwritable th_tgt.(Thread.memory) th_tgt.(Thread.local).(Local.promises))
      (CONSISTENT: Local.promise_consistent th_tgt'.(Thread.local))
      (NOATTATCH: not_attatched updates th_src.(Thread.memory))
      (SC: Memory.closed_timemap th_tgt.(Thread.sc) th_tgt.(Thread.memory))
      (CLOSED: Memory.closed th_tgt.(Thread.memory))
      (LCWF: Local.wf th_tgt.(Thread.local) th_tgt.(Thread.memory))
  :
    exists th_src' tr_src,
      (<<FORGET: forget_thread others th_src' th_tgt'>>) /\
      (<<STEP: traced_step tr_src th_src th_src'>>) /\
      (<<EVT: drf_sim_trace (List.map fst tr_src) (List.map fst tr_tgt)>>) /\
      (<<NOATTATCH: not_attatched updates th_src'.(Thread.memory)>>) /\
      (<<UNCHANGED: unchanged_on otherspace th_src.(Thread.memory) th_src'.(Thread.memory)>>).
Proof.
  ginduction STEPS; i.
  - esplits; eauto.
    + econs 1.
    + econs 1.
    + refl.
  - clarify. inv PRED. ss.
    dup HD. inv HD0.
    exploit AThread.step_future; eauto. i. des. ss. clear STEP.

    assert (OTHERS': forall loc to (SAT: others loc to),
               exists from msg, <<UNCH: unchangable th1.(Thread.memory) th1.(Thread.local).(Local.promises) loc to from msg>>).
    { i. exploit OTHERS; eauto. i. des.
      inv HD. eapply unchangable_increase in STEP; eauto. }

    exploit step_lifting; ss; eauto.
    { hexploit rtc_all_step_promise_consistent.
      { eapply all_steps_traced_step. esplits; eauto. }
      all: auto. }
    i. des.

    exploit IHSTEPS; try eassumption.
    { instantiate (1:=otherspace). i.
      eapply OTHERSPACE in PR. inv HD.
      eapply unwritable_increase in STEP0; eauto. }
    i. des.

    inv STEP.
    + esplits; eauto. econs 2; eauto.
    + esplits; eauto.
      * econs; eauto. econs; eauto.
      * econs 3; eauto.
      * etrans; eauto.
Qed.

Lemma drf_sim_trace_tau tr_src tr_tgt
      (TRACE: drf_sim_trace tr_src tr_tgt)
      (TAU: List.Forall
              (fun em => ThreadEvent.get_machine_event em = MachineEvent.silent) tr_tgt)
  :
    List.Forall
      (fun em => ThreadEvent.get_machine_event em = MachineEvent.silent) tr_src.
Proof.
  ginduction TRACE; i; ss.
  - inv TAU. eauto.
  - inv TAU. econs; eauto. inv HD; eauto.
Qed.

Lemma drf_sim_trace_no_promise tr_src tr_tgt
      (TRACE: drf_sim_trace tr_src tr_tgt)
  :
    List.Forall no_promise tr_src.
Proof.
  ginduction TRACE; i; ss. econs; eauto. inv HD; ss.
Qed.

Lemma pred_steps_traced_step2 P lang
      th0 th1 tr
      (STEPS: traced_step tr th0 th1)
      (EVENTS: List.Forall (fun em => <<SAT: P (fst em)>> /\ <<TAU: ThreadEvent.get_machine_event (fst em) = MachineEvent.silent>>) tr)
  :
    rtc (tau (@pred_step P lang)) th0 th1.
Proof.
  eapply pred_steps_traced_step; eauto.
Qed.

Lemma rtc_tau_step_lifting
      P lang (th_src th_tgt th_tgt': Thread.t lang)
      others updates otherspace
      (STEPS: rtc (tau (@pred_step P lang)) th_tgt th_tgt')
      (PRED: P <1= ((no_update_on updates)
                      /1\ (no_read_msgs others)))
      (FORGET: forget_thread others th_src th_tgt)
      (OTHERS: forall loc to (SAT: others loc to),
          exists from msg, <<UNCH: unchangable th_tgt.(Thread.memory) th_tgt.(Thread.local).(Local.promises) loc to from msg>>)
      (OTHERSPACE: otherspace <2= unwritable th_tgt.(Thread.memory) th_tgt.(Thread.local).(Local.promises))
      (CONSISTENT: Local.promise_consistent th_tgt'.(Thread.local))
      (NOATTATCH: not_attatched updates th_src.(Thread.memory))
      (SC: Memory.closed_timemap th_tgt.(Thread.sc) th_tgt.(Thread.memory))
      (CLOSED: Memory.closed th_tgt.(Thread.memory))
      (LCWF: Local.wf th_tgt.(Thread.local) th_tgt.(Thread.memory))
  :
    exists th_src',
      (<<FORGET: forget_thread others th_src' th_tgt'>>) /\
      (<<STEP: rtc (tau (@AThread.program_step lang)) th_src th_src'>>) /\
      (<<NOATTATCH: not_attatched updates th_src'.(Thread.memory)>>) /\
      (<<UNCHANGED: unchanged_on otherspace th_src.(Thread.memory) th_src'.(Thread.memory)>>).
Proof.
  eapply pred_steps_traced_step in STEPS. des.
  hexploit traced_step_lifting; eauto.
  { eapply List.Forall_impl; eauto.
    i. ss. des. eapply PRED in SAT. des. split; auto. }
  i. des.
  esplits; eauto. eapply pred_steps_traced_step2 in STEP.
  - eapply no_promise_program_step_rtc; eauto.
  - eapply List.Forall_forall. i.
    eapply List.in_map in H.
    split.
    + eapply drf_sim_trace_no_promise in EVT.
      eapply List.Forall_forall in EVT; eauto.
    + eapply drf_sim_trace_tau in EVT; eauto.
      * eapply List.Forall_forall in EVT; eauto.
      * eapply List.Forall_forall. i.
        eapply List.in_map_iff in H0. des. clarify.
        eapply List.Forall_forall in EVENTS; eauto. des. auto.
Qed.

Lemma future_max_full_ts mem0 mem1
      (FUTURE: Memory.future mem0 mem1)
      loc max0 max1
      (MAX0: Memory.max_full_ts mem0 loc max0)
      (MAX1: Memory.max_full_ts mem1 loc max1)
  :
    Time.le max0 max1.
Proof.
  inv MAX0. des.
  eapply Memory.future_get1 in GET; eauto. des. inv MSG_LE.
  eapply Memory.max_full_ts_spec in GET0; eauto.
  des; eauto.
Qed.

Lemma max_full_ts_exists mem0
      loc to from val released
      (GET: Memory.get loc to mem0 = Some (from, Message.full val released))
  :
    exists max, <<MAX: Memory.max_full_ts mem0 loc max>>.
Proof.
  hexploit (@cell_elements_greatest
              (mem0 loc)
              (fun ts => exists from' val' released',
                   Memory.get loc ts mem0 = Some (from', Message.full val' released'))).
  i. des.
  - exists to0. econs; eauto.
  - exfalso. eapply EMPTY; eauto.
Qed.

Lemma concrete_covered_same prom mem0 mem1
      (FUTURE: Memory.future mem0 mem1)
  :
    concrete_covered prom mem0 <2= concrete_covered prom mem1.
Proof.
  i. inv PR. dup MAX. inv MAX0. des.
  eapply Memory.future_get1 in GET; eauto. des. inv MSG_LE.
  eapply max_full_ts_exists in GET0; eauto. des.
  econs; eauto. etrans; eauto.
  eapply future_max_full_ts; eauto.
Qed.

Definition other_promises (c_tgt: Configuration.t) (tid: Ident.t) :=
  all_promises c_tgt.(Configuration.threads) (fun tid' => tid <> tid').

Inductive other_union tid
          (otherlocs: Ident.t -> Loc.t -> Time.t -> Prop)
  : Loc.t -> Time.t -> Prop :=
| other_updates_intro
    loc to tid'
    (NEQ: tid <> tid')
    (OTHERLOCS: otherlocs tid' loc to)
  :
    other_union tid otherlocs loc to
.

Definition other_updates (tid: Ident.t)
           (updates aupdates: Ident.t -> Loc.t -> Time.t -> Prop) :=
  other_union tid updates \2/ other_union tid aupdates.

Definition other_spaces (tid: Ident.t)
           (spaces: Ident.t -> Loc.t -> Time.t -> Prop) :=
  other_union tid spaces.

Lemma race_lemma c tid0 tid1 lang0 lang1 st0 st1 lc0 lc1 th0 th1 e1 e2
      (NEQ: tid0 <> tid1)
      (RACEFREE: pf_racefree c)
      (WF: Configuration.wf c)
      (FIND0: IdentMap.find tid0 (Configuration.threads c) = Some (existT _ lang0 st0, lc0))
      (FIND1: IdentMap.find tid1 (Configuration.threads c) = Some (existT _ lang1 st1, lc1))
      (STEP0: rtc (tau (@AThread.program_step _)) (Thread.mk _ st0 lc0 c.(Configuration.sc) c.(Configuration.memory)) th0)
      (STEP1: rtc (tau (@AThread.program_step _)) (Thread.mk _ st1 lc1 th0.(Thread.sc) th0.(Thread.memory)) th1)
      (PROEVT0: can_step _ th0.(Thread.state) e1)
      (PROEVT1: can_step _ th1.(Thread.state) e2)
      (RACE: pf_race_condition e1 e2)
  :
    False.
Proof.
  eapply rtc_tail in STEP0. des; ss; clarify.
  - eapply rtc_tail in STEP1. des; ss; clarify.
    + inv STEP2. inv STEP3. destruct th0, th1. exploit RACEFREE.
      * econs 2; [|econs 2; [|refl]].
        { econs. econs. econs.
          - eapply FIND0.
          - eapply STEP0.
          - eauto. }
        { econs. econs. econs.
          - ss. erewrite IdentMap.gso.
            + eapply FIND1.
            + eauto.
          - eapply STEP1.
          - eauto. }
      * econs; ss.
        { erewrite IdentMap.gso.
          - erewrite IdentMap.gss. eauto.
          - eauto. }
        { erewrite IdentMap.gss. eauto. }
        { eauto. }
        { eauto. }
        { eauto. }
        { eauto. }
      * ss.
    + inv STEP2. destruct th0. exploit RACEFREE.
      * econs 2; [|refl]. econs. econs. econs.
        { eapply FIND0. }
        { eapply STEP0. }
        { eauto. }
      * econs; ss.
        { erewrite IdentMap.gss. eauto. }
        { erewrite IdentMap.gso.
          - eapply FIND1.
          - eauto. }
        { eauto. }
        { eauto. }
        { eauto. }
        { eauto. }
      * ss.
  - eapply rtc_tail in STEP1. des; ss; clarify.
    + inv STEP0. destruct th1. exploit RACEFREE.
      * econs 2; [|refl]. econs. econs. econs.
        { eapply FIND1. }
        { eapply STEP1. }
        { eauto. }
      * econs; ss.
        { erewrite IdentMap.gso.
          - eapply FIND0.
          - eauto. }
        { erewrite IdentMap.gss. eauto. }
        { eauto. }
        { eauto. }
        { eauto. }
        { eauto. }
      * ss.
    + exploit RACEFREE.
      * refl.
      * econs.
        { eapply FIND0. }
        { eapply FIND1. }
        { eauto. }
        { eauto. }
        { eauto. }
        { eauto. }
      * eauto.
Qed.

Lemma inv_step mem0 mem1 lang (st: Language.state lang)
      lc proms spaces aupdates updates mlast
      (INV: Inv.t mem0 _ st lc proms spaces aupdates updates mlast)
      (FUTURE: Memory.future mem0 mem1)
  :
    Inv.t mem1 _ st lc proms spaces aupdates updates mlast.
Proof.
  inv INV. econs; eauto.
  i. eapply concrete_covered_same; eauto.
Qed.

Lemma forget_config_forget_thread
      c_src c_tgt tid
      (FORGET: forget_config c_src c_tgt)
      lang st_tgt lc_tgt
      (TIDTGT: IdentMap.find tid c_tgt.(Configuration.threads) =
               Some (existT _ lang st_tgt, lc_tgt))
  :
    exists st_src lc_src,
      (<<TIDSRC: IdentMap.find tid c_src.(Configuration.threads) =
                 Some (existT _ lang st_src, lc_src)>>) /\
      (<<FORGET: forget_thread
                   (other_promises c_tgt tid)
                   (Thread.mk _ st_src lc_src c_src.(Configuration.sc) c_src.(Configuration.memory))
                   (Thread.mk _ st_tgt lc_tgt c_tgt.(Configuration.sc) c_tgt.(Configuration.memory))>>).
Proof.
  inv FORGET. specialize (THS tid).
  unfold option_rel in THS. rewrite TIDTGT in *. des_ifs. inv THS.
  esplits; eauto. destruct lc1, lc_tgt. ss. clarify. rewrite SC. econs.
  replace (other_promises c_tgt tid \2/ promised promises0) with
      (all_promises (Configuration.threads c_tgt) (fun _ => True)); auto.
  extensionality loc. extensionality to.
  apply Coq.Logic.PropExtensionality.propositional_extensionality.
  split; i.
  - inv H. destruct (classic (tid = tid0)).
    + right. clarify.
    + left. econs; eauto.
  - des.
    + inv H. econs; eauto.
    + econs; eauto.
Qed.

Lemma sim_pf_other_promise
      c_src0 c_tgt0 tid mlast spaces updates aupdates
      (SIM: sim_pf_minus_one tid mlast spaces updates aupdates c_src0 c_tgt0)
      lang st0 lc0
      (TIDTGT:
         IdentMap.find tid c_tgt0.(Configuration.threads) =
         Some (existT _ lang st0, lc0))
      tid' st1 lc1
      (NEQ: tid <> tid')
      (TIDTGT':
         IdentMap.find tid' c_tgt0.(Configuration.threads) =
         Some (st1, lc1))
      loc from to msg
      (GET: Memory.get loc to lc1.(Local.promises) = Some (from, msg))
  :
    unchangable (Configuration.memory c_tgt0) (Local.promises lc0) loc to from msg.
Proof.
  inv SIM. exploit THREADS; eauto. i.
  inv WFTGT. inv WF. destruct st1 as [lang1 st1].
  exploit THREADS0; try apply TIDTGT'. intros LCWF. inv LCWF.
  dup GET. eapply PROMISES in GET0. esplits. econs; eauto.
  exploit DISJOINT; eauto. intros [].
  destruct (Memory.get loc to (Local.promises lc0)) eqn: GET1; auto.
  destruct p. exfalso.
  eapply Memory.disjoint_get; eauto.
Qed.

Lemma sim_pf_other_promises
      c_src0 c_tgt0 tid mlast spaces updates aupdates
      (SIM: sim_pf_minus_one tid mlast spaces updates aupdates c_src0 c_tgt0)
      lang st0 lc0
      (TIDTGT:
         IdentMap.find tid c_tgt0.(Configuration.threads) =
         Some (existT _ lang st0, lc0))
  :
    forall loc to (SAT: other_promises c_tgt0 tid loc to),
    exists from msg,
      (<<UNCH: unchangable (Configuration.memory c_tgt0) (Local.promises lc0) loc to from msg >>).
Proof.
  dup SIM. inv SIM. i. inv SAT. inv PROMISED.
  destruct msg as [from msg]. eapply sim_pf_other_promise in GET; eauto.
Qed.

Lemma sim_pf_not_attatched
      c_src0 c_tgt0 tid mlast spaces updates aupdates
      (SIM: sim_pf_minus_one tid mlast spaces updates aupdates c_src0 c_tgt0)
  :
    not_attatched (other_updates tid updates aupdates) (Configuration.memory c_src0).
Proof.
  inv SIM. ii. inv SAT.
  - inv H. exploit THREADS; eauto. intros [].
    eapply NOATTATCH; eauto.
  - inv H. exploit THREADS; eauto. intros [].
    eapply NOATTATCH; eauto.
Qed.

Lemma configuration_wf_promises_le c tid lang st lc
      (WF: Configuration.wf c)
      (TID: IdentMap.find tid c.(Configuration.threads) =
            Some (existT _ lang st, lc))
  :
    Memory.le lc.(Local.promises) c.(Configuration.memory).
Proof.
  inv WF. inv WF0. exploit THREADS; eauto. intros []. auto.
Qed.

Lemma sim_pf_other_spaces
      c_src0 c_tgt0 tid mlast spaces updates aupdates
      lang st0 lc0
      (TIDTGT:
         IdentMap.find tid c_tgt0.(Configuration.threads) =
         Some (existT _ lang st0, lc0))
      (SIM: sim_pf_minus_one tid mlast spaces updates aupdates c_src0 c_tgt0)
  :
    other_spaces tid spaces <2= unwritable (Configuration.memory c_tgt0) (Local.promises lc0).
Proof.
  ii. inv PR. inv SIM. exploit THREADS; eauto. intros [].
  inv FORGET. specialize (THS tid').
  unfold option_rel in THS. des_ifs.
  { inv THS. destruct st. exploit INV; eauto. intros [].
    exploit SPACES; eauto. intros CONCRETE.
    inv CONCRETE. inv COVERED. dup GET.
    dup Heq0. eapply configuration_wf_promises_le in Heq0; eauto.
    eapply Heq0 in GET. econs; eauto. econs; eauto.
    inv WFTGT. inv WF.
    destruct (Memory.get x0 to (Local.promises lc0)) eqn: GET1; auto.
    destruct p. exfalso.
    exploit DISJOINT; try eassumption. intros [].
    eapply Memory.disjoint_get; eauto. }
  { exfalso. exploit INVBOT; eauto. i. des. eapply SPACESBOT; eauto. }
Qed.

Lemma already_updated lang (th0 th1: Thread.t lang) (L: Loc.t -> Time.t -> Prop) e
      (MLE: Memory.le th0.(Thread.local).(Local.promises) th0.(Thread.memory))
      (STEP: AThread.step_allpf e th0 th1)
      (UNCH: forall loc from (SAT: L loc from),
          exists to msg,
            (<<TS: Time.lt from to>>) /\
            (<<UNCH: unchangable th0.(Thread.memory) th0.(Thread.local).(Local.promises) loc to from msg>>))
  :
    no_update_on L e.
Proof.
  unfold no_update_on. des_ifs. ii. eapply UNCH in H. des.
  inv STEP. dup STEP0. eapply step_write_not_in in STEP1; auto.
  assert (TSRW: Time.lt tsr tsw).
  { inv STEP0; inv STEP. ss. inv LOCAL. destruct lc3, lc2.
    eapply write_msg_wf in LOCAL2. des. auto. }
  ss. eapply (STEP1 (Time.meet to tsw)).
  - unfold Time.meet. des_ifs; econs; ss. refl.
  - econs; eauto.
    unfold Time.meet. des_ifs; econs; ss.
    + refl.
    + left. auto.
Qed.

Lemma sim_pf_read_promise_race
      P Q c_src0 c_tgt0 tid mlast spaces updates aupdates
      (SIM: sim_pf_minus_one tid mlast spaces updates aupdates c_src0 c_tgt0)
      lang st0 lc0
      (TIDTGT:
         IdentMap.find tid c_tgt0.(Configuration.threads) =
         Some (existT _ lang st0, lc0))
      th0'
      (STEPS0': rtc (tau (@pred_step P lang))
                    (Thread.mk _ st0 lc0 c_tgt0.(Configuration.sc) c_tgt0.(Configuration.memory))
                    th0')
      e' th1' th2'
      (STEP': AThread.step_allpf e' th0' th1')
      (RACE': ~ ((no_update_on (other_updates tid updates aupdates))
                   /1\ (no_read_msgs (other_promises c_tgt0 tid))) e')
      (STEPS1': rtc (tau (@pred_step Q lang)) th1' th2')
      (CONSISTENT': Local.promise_consistent th2'.(Thread.local))
  :
    False.
Proof.
  assert (WF: Configuration.wf c_tgt0).
  { inv SIM. auto. }
  inv WF. inv WF0. exploit THREADS; eauto. intros LOCAL.
  clear DISJOINT THREADS.

  assert (CONSISTENT0: Local.promise_consistent th0'.(Thread.local)).
  { exploit AThread.rtc_tau_step_future.
    { eapply thread_steps_pred_steps; try apply STEPS0'. } all: ss. i. des.
    dup STEP'. inv STEP'. exploit AThread.step_future; eauto. i. des. clear STEP.
    hexploit rtc_tau_step_promise_consistent.
    { eapply thread_steps_pred_steps; try apply STEPS1'. } all: ss.
    intros CONSISTENT1.
    inv STEP'0. hexploit step_promise_consistent; eauto. }

  assert (exists e th1 th2,
             (<<STEPS: rtc (tau (@pred_step ((no_update_on (other_updates tid updates aupdates))
                                               /1\ (no_read_msgs (other_promises c_tgt0 tid))) lang))
                           (Thread.mk _ st0 lc0 c_tgt0.(Configuration.sc) c_tgt0.(Configuration.memory))
                           th1>>) /\
             (<<CONSISTENT: Local.promise_consistent th1.(Thread.local)>>) /\
             (<<STEP: AThread.step_allpf e th1 th2>>) /\
             (<<RACE: ~ ((no_update_on (other_updates tid updates aupdates))
                           /1\ (no_read_msgs (other_promises c_tgt0 tid))) e>>)).
  { hexploit (@hold_or_not P ((no_update_on (other_updates tid updates aupdates))
                                /1\ (no_read_msgs (other_promises c_tgt0 tid))));
      try apply STEPS0'; eauto.
    i. des.
    - esplits.
      + eapply pred_step_rtc_mon; try apply HOLD. i. ss. des. split; auto.
      + ss.
      + eauto.
      + ss.
    - esplits.
      + eapply pred_step_rtc_mon; try apply STEPS0. i. ss. des. split; auto.
      + exploit AThread.rtc_tau_step_future.
        { eapply thread_steps_pred_steps; try apply STEPS0. } all: ss. i. des.
        dup STEP. inv STEP0. exploit AThread.step_future; eauto. i. des. clear STEP1.
        hexploit rtc_tau_step_promise_consistent.
        { eapply thread_steps_pred_steps; try apply STEPS1. } all: ss.
        intros CONSISTENT1.
        inv STEP. hexploit step_promise_consistent; eauto.
      + eauto.
      + ss. }
  clear th0' STEPS0' e' th1' th2' STEP' RACE' STEPS1' CONSISTENT' CONSISTENT0. des.

  generalize (sim_pf_other_promises SIM). intros OTHERPROMISE.

  dup SIM. inv SIM0.
  exploit forget_config_forget_thread; eauto. i. des.
  hexploit rtc_tau_step_lifting; try eassumption.
  { i. ss. des. split; eauto. }
  { eapply OTHERPROMISE; eauto. }
  { ss. eapply sim_pf_other_spaces; eauto. }
  { eapply sim_pf_not_attatched; eauto. }

  i. des. ss. apply not_and_or in RACE. des.

  - unfold no_update_on in RACE. des_ifs. apply NNPP in RACE.
    inv RACE.

    + inv H. exploit THREADS; eauto. intros [].
      inv FORGET. specialize (THS tid').
      unfold option_rel in THS. des_ifs.
      { inv THS. destruct st as [lang0 st].
        exploit INV; ss. intros [].
        exploit UPDATE.
        { eauto. }
        { etrans; eauto.
          eapply unchanged_on_mon; eauto.
          i. econs; eauto. }
        { eapply not_attatched_mon; eauto. i. des.
          - left. econs; eauto.
          - right. econs; eauto. }
        i. des.
        inv FORGET1. ss. unfold is_updating, is_updating in *. des.
        inv STEP. inv STEP1; inv STEP.
        exploit race_lemma; try eassumption; ss.
        - econs; eauto.
        - econs 2; eauto. ss. }
      { exfalso. exploit INVBOT; eauto. i. des. eapply UPDATESBOT; eauto. }

    + inv H. exploit THREADS; eauto. intros [].
      inv FORGET. specialize (THS tid').
      unfold option_rel in THS. des_ifs.
      { inv THS. destruct st as [lang0 st].
        exploit INV; ss. intros [].
        assert (AUALREADY:
                  forall loc from (SAT: (aupdates tid') loc from),
                  exists to msg,
                    (<<TS: Time.lt from to>>) /\
                    (<<UNCH: unchangable c_tgt0.(Configuration.memory) lc0.(Local.promises) loc to from msg>>)).
        { i. exploit AUPDATES; eauto. i. des.
          esplits; eauto.
          hexploit sim_pf_other_promise; eauto. }
        hexploit already_updated; cycle 1.
        - eapply STEP.
        - instantiate (1:=aupdates tid'). i. eapply AUALREADY in SAT. des.
          eapply unchangable_rtc_increase in STEPS; try eassumption.
          esplits; eauto.
        - ss.
        - eapply steps_promises_le in STEPS; auto. ss.
          inv LOCAL. ss. }
      { exfalso. exploit INVBOT; eauto. i. des. eapply AUPDATESBOT; eauto. }

  - assert (exists loc to from val released,
               (<<OPROMS: other_promises c_tgt0 tid loc to>>) /\
               (<<READING: is_reading _ th1.(Thread.state) loc Ordering.seqcst>>) /\
               (<<CONCRETE: Memory.get loc to th1.(Thread.memory) = Some (from, Message.full val released)>>)).
    { unfold no_read_msgs in RACE. des_ifs.
      - apply NNPP in RACE. inv STEP. inv STEP1; inv STEP.
        inv LOCAL0. inv LOCAL1.
        esplits; eauto. ss. econs. esplits.
        + econs; eauto.
        + instantiate (1:=ord). destruct ord; ss.
        + ss.
      - apply NNPP in RACE. inv STEP. inv STEP1; inv STEP.
        inv LOCAL0. inv LOCAL1.
        esplits; eauto. ss. econs. esplits.
        + econs; eauto.
        + instantiate (1:=ordr). destruct ordr; ss.
        + ss. } des.

    exploit OTHERPROMISE; [eauto|eauto|]. i. des.
    eapply unchangable_rtc_increase in STEPS; [|eauto].
    inv UNCH. inv STEPS. clarify.

    inv OPROMS. destruct st as [lang0 st].
    exploit forget_config_forget_thread.
    { eauto. }
    { eapply TID1. }
    i. des.
    dup TID1. eapply configuration_wf_promises_le in TID1; auto.
    inv PROMISED. destruct msg as [from0 msg].
    dup GET1. eapply TID1 in GET1; auto. clarify.

    inv SIM. exploit THREADS0; [eauto|]. intros [].
    exploit INV.
    { eapply TIDSRC0. }
    { eapply TID0. }
    intros []. ss.
    clear UPDATE AUPDATE INV INVBOT. exploit PROMS.
    { econs; eauto. }
    { etrans; eauto.
      eapply unchanged_on_mon; eauto.
      i. econs; eauto. }
    { eapply not_attatched_mon; eauto. i. des.
      - left. econs; eauto.
      - right. econs; eauto. }
    i. des.
    inv FORGET1. ss. unfold is_reading, is_writing in *. des.
    exploit race_lemma; try eassumption; ss.
    econs; eauto.
Qed.


Require Import AProp.

Lemma sim_pf_step_minus
      c_src0 c_tgt0 c_tgt1 tid e mlast spaces updates aupdates
      (SIM: sim_pf_minus_one tid mlast spaces updates aupdates c_src0 c_tgt0)
      (STEP: Configuration.step e tid c_tgt0 c_tgt1)
  :
    (exists c_src1,
        (<<STEP: opt_pftstep e tid c_src0 c_src1>>) /\
        (<<FORGET: forget_config c_src1 c_tgt1>>) /\
        (<<SIM: forall tid' (NEQ: tid <> tid'),
            sim_pf_one tid' (mlast tid') (spaces tid') (updates tid')
                       (aupdates tid') c_src1 c_tgt1>>)) /\
    __guard__((<<CONSISTENT: forall lang st_tgt lc_tgt
                                    (FIND: IdentMap.find tid c_tgt1.(Configuration.threads) = Some (existT _ lang st_tgt, lc_tgt)),
                  pf_consistent_drf (Thread.mk _ st_tgt lc_tgt c_tgt1.(Configuration.sc) c_tgt1.(Configuration.memory))>>) \/
              (<<ABORT: e = MachineEvent.failure>>))
.
Proof.
  dup STEP. rename STEP0 into CSTEP. eapply configuration_step_equivalent in STEP. inv STEP; ss.
  eapply thread_steps_athread_steps in STEPS.
  assert (STEP: AThread.step_allpf e0 e2 (Thread.mk _ st3 lc3 sc3 memory3)).
  { eapply thread_step_athread_step. econs; eauto. }
  assert (WF: Configuration.wf c_tgt0).
  { inv SIM. auto. }
  inv WF. inv WF0. exploit THREADS; eauto. intros LOCAL.
  clear DISJOINT THREADS.

  exploit AThread.rtc_tau_step_future; try apply STEPS; ss. i. des.
  exploit Thread.step_future; eauto. i. des. ss. clear STEP0.
  assert (CONSISTENT1: Local.promise_consistent lc3).
  { destruct (classic (e0 = ThreadEvent.failure)).
    - clarify. inv STEP. inv STEP0; inv STEP.
      inv LOCAL0. inv LOCAL1. auto.
    - hexploit CONSISTENT; eauto. intros CONSISTENT2.
      eapply PromiseConsistent.consistent_promise_consistent in CONSISTENT2; eauto. }
  assert (CONSISTENT0: Local.promise_consistent e2.(Thread.local)).
  { inv STEP. eapply step_promise_consistent; eauto. }

  split; cycle 1.
  { destruct (classic (e0 = ThreadEvent.failure)).
    - right. clarify.
    - left. red. i. rewrite IdentMap.gss in FIND. dependent destruction FIND.
      eapply pf_consistent_pf_consistent_drf; eauto.
      + eapply PFConsistent.consistent_pf_consistent; eauto.
      + inv SIM. eapply memory_reserve_wf_configuration_step in CSTEP; ss. }

  destruct (classic (((no_update_on (other_updates tid updates aupdates))
                        /1\ (no_read_msgs (other_promises c_tgt0 tid))) e0)); cycle 1.
  { exfalso. exploit sim_pf_read_promise_race.
    - eauto.
    - eauto.
    - eapply pred_steps_thread_steps; eauto.
    - eauto.
    - ss.
    - instantiate (2:=fun _ => True). refl.
    - eauto.
    - ss. }

  hexploit (@hold_or_not (fun _ => True) ((no_update_on (other_updates tid updates aupdates))
                                            /1\ (no_read_msgs (other_promises c_tgt0 tid)))).
  { eapply pred_steps_thread_steps. eapply STEPS. }
  i. des; cycle 1.
  { exfalso. exploit sim_pf_read_promise_race.
    - eauto.
    - eauto.
    - eapply STEPS0.
    - eauto.
    - ss.
    - eapply STEPS1.
    - eauto.
    - ss. }

  generalize (sim_pf_other_promises SIM). intros OTHERPROMISE.

  dup SIM. inv SIM0.
  exploit forget_config_forget_thread; eauto. i. des.
  hexploit rtc_tau_step_lifting; try eassumption.
  { i. ss. des. split; eauto. }
  { eapply OTHERPROMISE; eauto. }
  { ss. eapply sim_pf_other_spaces; eauto. }
  { eapply sim_pf_not_attatched; eauto. }
  i. des.

  exploit step_lifting; try eassumption.
  { eauto. }
  { i. eapply OTHERPROMISE in SAT. des.
    hexploit unchangable_rtc_increase.
    - eapply HOLD.
    - eauto.
    - i. esplits; eauto.
    - eauto. }
  { instantiate (1:= other_spaces tid spaces).
    i. eapply sim_pf_other_spaces in SIM; eauto.
    eapply rtc_unwritable_increase; eauto. }
  i. des.

  assert (NEWPROMS: all_promises
                      (IdentMap.add tid (existT _ lang st3, lc3)
                                    c_tgt0.(Configuration.threads)) (fun _ => True) =
                    (other_promises c_tgt0 tid \2/ promised lc3.(Local.promises))).
  { extensionality loc. extensionality to.
    apply Coq.Logic.PropExtensionality.propositional_extensionality.
    split; i.
    - inv H0. erewrite IdentMap.gsspec in TID1. des_ifs; eauto.
      left. econs; eauto.
    - des.
      + inv H0. econs; eauto. erewrite IdentMap.gso; eauto.
      + econs; eauto. erewrite IdentMap.gss. ss.
  }

  inv STEP1.
  { eapply rtc_tail in STEP0. des.

    { inv STEP1. erewrite <- drf_sim_event_same_machine_event; eauto. ss.
      rewrite <- EVENT. inv FORGET. inv FORGET2. esplits.
      - econs; eauto. econs; eauto.
      - econs; ss.
        + i. repeat erewrite IdentMap.gsspec. des_ifs.
        + rewrite NEWPROMS. auto.
      - i. exploit THREADS; eauto. intros []. econs; ss.
        + etrans; eauto.
          eapply unchanged_on_mon.
          * etrans; eauto.
          * i. econs; eauto.
        + eapply not_attatched_mon; eauto. i. des.
          * left. econs; eauto.
          * right. econs; eauto.
        + i. erewrite IdentMap.gso in TIDTGT, TIDSRC0; auto.
          exploit INV; eauto. i.
          eapply inv_step; eauto.
          eapply Configuration.step_future in CSTEP; eauto. ss. des. auto.
        + i. erewrite IdentMap.gso in TIDSRC0; auto. }

    { clarify. ss.
      erewrite <- drf_sim_event_same_machine_event; eauto. ss.
      inv FORGET. inv FORGET2. exists c_src0. splits.
      - econs.
      - econs; ss.
        + i. erewrite IdentMap.gsspec. des_ifs.
          rewrite TIDSRC. econs; eauto.
        + rewrite NEWPROMS. auto.
      - i. exploit THREADS; eauto. intros []. econs; ss.
        i. erewrite IdentMap.gso in TIDTGT; auto.
        exploit INV; eauto. i.
        eapply inv_step; eauto.
        eapply Configuration.step_future in CSTEP; eauto. ss. des; auto. }
  }


  { dup STEP2. inv STEP2.
    { inv EVT; inv STEP3. }
    erewrite <- drf_sim_event_same_machine_event; eauto.
    inv FORGET. inv FORGET2. esplits.
    - econs; eauto. econs; eauto.
    - econs; ss.
      + i. repeat erewrite IdentMap.gsspec. des_ifs.
      + rewrite NEWPROMS. auto.
    - i. exploit THREADS; eauto. intros []. econs; ss.
      + etrans; eauto.
        eapply unchanged_on_mon.
        * etrans; eauto.
        * i. econs; eauto.
      + eapply not_attatched_mon; eauto. i. des.
        * left. econs; eauto.
        * right. econs; eauto.
      + i. erewrite IdentMap.gso in TIDTGT, TIDSRC0; auto.
        exploit INV; eauto. i.
        eapply inv_step; eauto.
        eapply Configuration.step_future in CSTEP; eauto. ss. des. auto.
      + i. erewrite IdentMap.gso in TIDSRC0; auto. }
Qed.




        , TIDSRC0; auto.
        ex

        econs;


          etrans; eauto.

        etrans; eauto.




    -

            exfalso. eapply SAT; eauto. }
            rewrite

      + econs; eauto.


        * inv H0. destruct (classic (tid = tid0)).
          right. clarify.
      + left. econs; eauto.
    - des.
      + inv H. econs; eauto.
      + econs; eauto.



  with



      + eauto.
      + eapply STEP0.
      + eapply STEP3.
    -

  rtc

{|
                      Configuration.threads := IdentMap.add tid
                                                 (existT (Language.state (E:=ProgramEvent.t))
                                                    lang st3, lc3) (Configuration.threads c1);
                      Configuration.sc := sc3;
                      Configuration.memory := memory3 |}


  assert (opt_pftstep e tid c_src0 c_src1

      in HOLD; ss.

    ; ss. ss.


             ; eauto.

  (RACE': ~ ((no_update_on (other_updates tid updates aupdates))
                   /1\ (no_read_msgs (other_promises c_tgt0 tid))) e')



       (<<SAT: forall tid' (NEQ: tid <> tid') lang_src st_src lc_src lang_tgt st_tgt lc_tgt
                      (TIDSRC: IdentMap.find tid' c_src1.(Configuration.threads) =
                               Some (existT _ lang_src st_src, lc_src))
                      (TIDTGT: IdentMap.find tid' c_tgt1.(Configuration.threads) =
                               Some (existT _ lang_tgt st_tgt, lc_tgt)),
           (<<FUTURE: unchanged_on (spaces tid') (mlast tid') c_src1.(Configuration.memory)>>) /\
           (<<NOATTATCH: not_attatched (updates tid') c_src1.(Configuration.memory)>>) /\
           (<<INV: Inv.t c_tgt1.(Configuration.memory) _ st_src lc_src lc_tgt.(Local.promises) (spaces tid') (updates tid') (aupdates tid') (mlast tid')>>)>>))
.
Proof.
  inv SIM. inv FORGET. dup THS. specialize (THS tid).
  eapply configuration_step_equivalent in STEP. inv STEP; ss.

  rewrite TID in THS. unfold option_rel in *. des_ifs. inv THS.
  dup WFTGT. inv WFTGT.
  exploit Thread.rtc_tau_step_future; eauto; ss.
  { inv WF. eauto. }
  i. des.
  exploit Thread.step_future; eauto.
  i. des. ss.

  assert (CONSISTENT1: Local.promise_consistent lc3).
  { destruct (classic (e0 = ThreadEvent.failure)).
    - inv STEP0; inv STEP; ss. inv LOCAL. inv LOCAL0. ss.
    - hexploit PromiseConsistent.consistent_promise_consistent; eauto. }
  assert (CONSISTENT0: Local.promise_consistent e2.(Thread.local)).
  { hexploit PromiseConsistent.step_promise_consistent; eauto. }

  set (oproms := all_promises c_tgt0.(Configuration.threads) (fun tid' => tid <> tid')).
  (* set (oproms := other_promises tid (Configuration.threads c_tgt0)). *)
  set (oupdates := other_updates tid updates \2/ other_updates tid aupdates).
  set (ospace := other_space tid (Configuration.threads c_tgt0) (Configuration.memory c_tgt0)).

  assert (OPROMS: (oproms \2/ promised lc1.(Local.promises)) = (all_promises c_tgt0.(Configuration.threads) (fun _ => True))).
  { extensionality loc. extensionality to.
    apply Coq.Logic.PropExtensionality.propositional_extensionality.
    unfold oproms. split; i.
    - des.
      + inv H. econs; eauto.
      + econs; eauto.
    - inv H. destruct (classic (tid = tid0)).
      + right. clarify.
      + left. econs; eauto. }

  assert (OSPACE: oproms <2= unwritable (Configuration.memory c_tgt0) lc1.(Local.promises)).
  { admit. }

    (* i. des. *)
    (* - inv PR. inv WF. destruct st. *)
    (*   exploit THREADS; eauto. i. inv x2. *)
    (*   inv PROMISED. destruct msg. *)
    (*   exploit Memory.get_ts; eauto. i. des. *)
    (*   { clarify. erewrite BOT in GET. clarify. } *)
    (*   econs. *)
    (*   + red. econs; eauto. econs; eauto; ss. refl. *)
    (*   + ii. inv H. exploit DISJOINT; try eassumption. *)
    (*     i. inv x2. ss. inv DISJOINT0. *)
    (*     exploit DISJOINT1; try eassumption. i. des. *)
    (*     eapply x2; eauto. econs; ss; eauto. refl. *)
    (* - inv PR. inv WF. *)
    (*   exploit THREADS; eauto. i. inv x. *)
    (*   inv SPACE. *)
    (*   + econs. *)
    (*     * red. econs; eauto. *)
    (*     * ii. inv H. exploit DISJOINT; try eassumption. *)
    (*       i. inv x. ss. inv DISJOINT0. *)
    (*       exploit DISJOINT1; try eassumption. i. des. *)
    (*       eapply x; eauto. *)
    (*   + econs. *)
    (*     * red. econs; [eapply PROMISES|]; eauto. *)
    (*     * ii. inv H. exploit DISJOINT; try eassumption. *)
    (*       i. inv x. ss. inv DISJOINT0. *)
    (*       exploit DISJOINT1; try eassumption. i. des. *)
    (*       eapply x; eauto. } *)

    hexploit (@hold_or_not (fun _ => True) ((no_update_on oupdates) /1\ (no_read_msgs oproms))).
    { eapply pred_steps_thread_steps. eapply STEPS. }
    i. des.

    - exploit step_lifting_rtc.
      + eapply pred_step_rtc_mon; [|apply HOLD]. i. ss. des.
        instantiate (1:=oproms). instantiate (1:=oupdates). eauto.
      + instantiate (1:=Thread.mk _ st1 (Local.mk tview0 Memory.bot) (Configuration.sc c_src0) (Configuration.memory c_src0)).
        rewrite SC. econs. rewrite OPROMS. auto.
      + ss. unfold oupdates. ii. inv SAT.
        eapply NOATTATCH; eauto.
      + inv WF. econs; eauto.
      + eauto.
      + eauto.
      + i. des. inv FORGET. destruct lc3. ss.
        destruct (classic (((no_update_on oupdates) /1\ (no_read_msgs oproms)) e0)).
        * exploit step_lifting.
          { econs. econs. eapply STEP0.
            splits; ss; eapply H. }
          { ss. }
          { ss. }
          { ss. }
          { eauto. }
          { eauto. }
          { eauto. }
          { i. eapply rtc_unchangables_increase in STEPS; ss; eauto. }
          { eauto. }
          { eauto. }
          { eauto. }
          { i. des.
            assert (OPROMS': (oproms \2/ promised promises) =
                             (all_promises
                                (IdentMap.add
                                   tid
                                   (existT (Language.state (E:=ProgramEvent.t)) lang st3,
                                    (Local.mk tview promises))
                                   (Configuration.threads c_tgt0)))
                               (fun _ => True)).
            { extensionality loc. extensionality to.
              apply Coq.Logic.PropExtensionality.propositional_extensionality.
              unfold oproms. split; i.
              - des.
                + inv H1. econs; eauto. ss.
                  erewrite IdentMap.gso; eauto.
                + econs; eauto. ss.
                  erewrite IdentMap.gss; eauto. ss.
              - inv H1. ss. rewrite IdentMap.gsspec in *. des_ifs.
                + right. ss.
                + left. econs; eauto. }
            inv STEP1.
            - eapply rtc_tail in STEP. des; ss.
              + inv STEP1. esplits.
                * rewrite <- EVT. rewrite <- EVENT0.
                  econs 2. econs.
                  { eauto. }
                  { eapply no_promise_program_step_rtc; eauto. }
                  { eapply no_promise_program_step; eauto. }
                * econs; ss.
                  { i. repeat rewrite IdentMap.gsspec. des_ifs.
                    eapply THS0. }
                  { rewrite OPROMS' in *. ss. }
                * i. ss.
                  rewrite IdentMap.gso in TIDSRC; auto.
                  rewrite IdentMap.gso in TIDTGT; auto.
                  exploit INV; eauto. i.
                  splits.
                  { etrans; eauto.
                    eapply unchanged_on_mon; eauto. i.
                    eapply x.(Inv.SPACES) in PR.
                    econs; eauto. }
                  { eapply not_attatched_mon; eauto.
                    i. econs; eauto. }
                  { eapply inv_step; eauto. etrans; eauto. }
              + clarify. esplits.
                * rewrite <- EVT. econs.
                * econs; ss.
                  { i. rewrite IdentMap.gsspec. des_ifs.
                    - rewrite Heq. ss.
                    - eapply THS0. }
                  { rewrite OPROMS' in *. ss. }
                * i. splits.
                  { etrans; eauto. refl. }
                  { i. eapply not_attatched_mon; eauto.
                    i. econs; eauto. }
                  { i. rewrite IdentMap.gso in TIDTGT; eauto.
                    exploit INV; eauto. i.
                    eapply inv_step; eauto. etrans; eauto. }
            - esplits.
              * rewrite <- EVT. econs 2. econs.
                { eauto. }
                { eapply no_promise_program_step_rtc; eauto. }
                { eapply no_promise_program_step; eauto. }
              * econs; ss.
                { i. repeat rewrite IdentMap.gsspec. des_ifs.
                  eapply THS0. }
                { rewrite OPROMS' in *. ss. }
              * i. ss.
                rewrite IdentMap.gso in TIDSRC; auto.
                rewrite IdentMap.gso in TIDTGT; auto.
                exploit INV; eauto. i.
                splits.
                { etrans; eauto.
                  eapply unchanged_on_mon.
                  - etrans; eauto.
                  - i. eapply x.(Inv.SPACES) in PR.
                    econs; eauto. }
                { eapply not_attatched_mon; eauto.
                  i. econs; eauto. }
                { eapply inv_step; eauto. etrans; eauto. }
          }
        * apply not_and_or in H. des.
          { unfold no_update_on in H. des_ifs.
            apply NNPP in H. inv H.
            destruct (IdentMap.find tid' (Configuration.threads c_src0)) as
                [[[? ?] lc]|] eqn:FIND; cycle 1.
            { exfalso. eapply INVBOT in FIND. des.
              eapply UPDATESBOT; eauto. }
            specialize (THS0 tid'). rewrite FIND in *. des_ifs. inv THS0.
            exploit INV; eauto. i. inv x0.

            exploit AUPDATE.
            { eauto. }
            { etrans; eauto. eapply unchanged_on_mon; eauto.
              i. econs; eauto. }
            { eapply not_attatched_sum.
              - admit.
              - eapply not_attatched_mon; eauto.
                i. econs; eauto. }
            i. des. exfalso. eapply race_lemma; try eassumption.
            - eapply no_promise_program_step_rtc. eapply STEP.
            -
Admitted.



Lemma sim_pf_step
      c_src0 c_tgt0 c_tgt1 tid e mlast spaces updates aupdates
      (SIM: sim_pf mlast spaces updates aupdates c_src0 c_tgt0)
      (STEP: Configuration.step e tid c_tgt0 c_tgt1)
  :
    exists c_src1,
      (<<STEP: opt_pftstep e tid c_src0 c_src1>>) /\
      (<<FORGET: forget_config c_src1 c_tgt1>>) /\


       (<<SAT: forall tid' (NEQ: tid <> tid') lang_src st_src lc_src lang_tgt st_tgt lc_tgt
                      (TIDSRC: IdentMap.find tid' c_src1.(Configuration.threads) =
                               Some (existT _ lang_src st_src, lc_src))
                      (TIDTGT: IdentMap.find tid' c_tgt1.(Configuration.threads) =
                               Some (existT _ lang_tgt st_tgt, lc_tgt)),
           (<<FUTURE: unchanged_on (spaces tid') (mlast tid') c_src1.(Configuration.memory)>>) /\
           (<<NOATTATCH: not_attatched (updates tid') c_src1.(Configuration.memory)>>) /\
           (<<INV: Inv.t c_tgt1.(Configuration.memory) _ st_src lc_src lc_tgt.(Local.promises) (spaces tid') (updates tid') (aupdates tid') (mlast tid')>>)>>))
.
Proof.
  inv SIM. inv FORGET. dup THS. specialize (THS tid).
  eapply configuration_step_equivalent in STEP. inv STEP; ss.

  rewrite TID in THS. unfold option_rel in *. des_ifs. inv THS.
  dup WFTGT. inv WFTGT.
  exploit Thread.rtc_tau_step_future; eauto; ss.
  { inv WF. eauto. }
  i. des.
  exploit Thread.step_future; eauto.
  i. des. ss.

  assert (CONSISTENT1: Local.promise_consistent lc3).
  { destruct (classic (e0 = ThreadEvent.failure)).
    - inv STEP0; inv STEP; ss. inv LOCAL. inv LOCAL0. ss.
    - hexploit PromiseConsistent.consistent_promise_consistent; eauto. }
  assert (CONSISTENT0: Local.promise_consistent e2.(Thread.local)).
  { hexploit PromiseConsistent.step_promise_consistent; eauto. }

  set (oproms := all_promises c_tgt0.(Configuration.threads) (fun tid' => tid <> tid')).
  (* set (oproms := other_promises tid (Configuration.threads c_tgt0)). *)
  set (oupdates := other_updates tid updates \2/ other_updates tid aupdates).
  set (ospace := other_space tid (Configuration.threads c_tgt0) (Configuration.memory c_tgt0)).

  assert (OPROMS: (oproms \2/ promised lc1.(Local.promises)) = (all_promises c_tgt0.(Configuration.threads) (fun _ => True))).
  { extensionality loc. extensionality to.
    apply Coq.Logic.PropExtensionality.propositional_extensionality.
    unfold oproms. split; i.
    - des.
      + inv H. econs; eauto.
      + econs; eauto.
    - inv H. destruct (classic (tid = tid0)).
      + right. clarify.
      + left. econs; eauto. }

  assert (OSPACE: oproms <2= unwritable (Configuration.memory c_tgt0) lc1.(Local.promises)).
  { admit. }

    (* i. des. *)
    (* - inv PR. inv WF. destruct st. *)
    (*   exploit THREADS; eauto. i. inv x2. *)
    (*   inv PROMISED. destruct msg. *)
    (*   exploit Memory.get_ts; eauto. i. des. *)
    (*   { clarify. erewrite BOT in GET. clarify. } *)
    (*   econs. *)
    (*   + red. econs; eauto. econs; eauto; ss. refl. *)
    (*   + ii. inv H. exploit DISJOINT; try eassumption. *)
    (*     i. inv x2. ss. inv DISJOINT0. *)
    (*     exploit DISJOINT1; try eassumption. i. des. *)
    (*     eapply x2; eauto. econs; ss; eauto. refl. *)
    (* - inv PR. inv WF. *)
    (*   exploit THREADS; eauto. i. inv x. *)
    (*   inv SPACE. *)
    (*   + econs. *)
    (*     * red. econs; eauto. *)
    (*     * ii. inv H. exploit DISJOINT; try eassumption. *)
    (*       i. inv x. ss. inv DISJOINT0. *)
    (*       exploit DISJOINT1; try eassumption. i. des. *)
    (*       eapply x; eauto. *)
    (*   + econs. *)
    (*     * red. econs; [eapply PROMISES|]; eauto. *)
    (*     * ii. inv H. exploit DISJOINT; try eassumption. *)
    (*       i. inv x. ss. inv DISJOINT0. *)
    (*       exploit DISJOINT1; try eassumption. i. des. *)
    (*       eapply x; eauto. } *)

    hexploit (@hold_or_not (fun _ => True) ((no_update_on oupdates) /1\ (no_read_msgs oproms))).
    { eapply pred_steps_thread_steps. eapply STEPS. }
    i. des.

    - exploit step_lifting_rtc.
      + eapply pred_step_rtc_mon; [|apply HOLD]. i. ss. des.
        instantiate (1:=oproms). instantiate (1:=oupdates). eauto.
      + instantiate (1:=Thread.mk _ st1 (Local.mk tview0 Memory.bot) (Configuration.sc c_src0) (Configuration.memory c_src0)).
        rewrite SC. econs. rewrite OPROMS. auto.
      + ss. unfold oupdates. ii. inv SAT.
        eapply NOATTATCH; eauto.
      + inv WF. econs; eauto.
      + eauto.
      + eauto.
      + i. des. inv FORGET. destruct lc3. ss.
        destruct (classic (((no_update_on oupdates) /1\ (no_read_msgs oproms)) e0)).
        * exploit step_lifting.
          { econs. econs. eapply STEP0.
            splits; ss; eapply H. }
          { ss. }
          { ss. }
          { ss. }
          { eauto. }
          { eauto. }
          { eauto. }
          { i. eapply rtc_unchangables_increase in STEPS; ss; eauto. }
          { eauto. }
          { eauto. }
          { eauto. }
          { i. des.
            assert (OPROMS': (oproms \2/ promised promises) =
                             (all_promises
                                (IdentMap.add
                                   tid
                                   (existT (Language.state (E:=ProgramEvent.t)) lang st3,
                                    (Local.mk tview promises))
                                   (Configuration.threads c_tgt0)))
                               (fun _ => True)).
            { extensionality loc. extensionality to.
              apply Coq.Logic.PropExtensionality.propositional_extensionality.
              unfold oproms. split; i.
              - des.
                + inv H1. econs; eauto. ss.
                  erewrite IdentMap.gso; eauto.
                + econs; eauto. ss.
                  erewrite IdentMap.gss; eauto. ss.
              - inv H1. ss. rewrite IdentMap.gsspec in *. des_ifs.
                + right. ss.
                + left. econs; eauto. }
            inv STEP1.
            - eapply rtc_tail in STEP. des; ss.
              + inv STEP1. esplits.
                * rewrite <- EVT. rewrite <- EVENT0.
                  econs 2. econs.
                  { eauto. }
                  { eapply no_promise_program_step_rtc; eauto. }
                  { eapply no_promise_program_step; eauto. }
                * econs; ss.
                  { i. repeat rewrite IdentMap.gsspec. des_ifs.
                    eapply THS0. }
                  { rewrite OPROMS' in *. ss. }
                * i. ss.
                  rewrite IdentMap.gso in TIDSRC; auto.
                  rewrite IdentMap.gso in TIDTGT; auto.
                  exploit INV; eauto. i.
                  splits.
                  { etrans; eauto.
                    eapply unchanged_on_mon; eauto. i.
                    eapply x.(Inv.SPACES) in PR.
                    econs; eauto. }
                  { eapply not_attatched_mon; eauto.
                    i. econs; eauto. }
                  { eapply inv_step; eauto. etrans; eauto. }
              + clarify. esplits.
                * rewrite <- EVT. econs.
                * econs; ss.
                  { i. rewrite IdentMap.gsspec. des_ifs.
                    - rewrite Heq. ss.
                    - eapply THS0. }
                  { rewrite OPROMS' in *. ss. }
                * i. splits.
                  { etrans; eauto. refl. }
                  { i. eapply not_attatched_mon; eauto.
                    i. econs; eauto. }
                  { i. rewrite IdentMap.gso in TIDTGT; eauto.
                    exploit INV; eauto. i.
                    eapply inv_step; eauto. etrans; eauto. }
            - esplits.
              * rewrite <- EVT. econs 2. econs.
                { eauto. }
                { eapply no_promise_program_step_rtc; eauto. }
                { eapply no_promise_program_step; eauto. }
              * econs; ss.
                { i. repeat rewrite IdentMap.gsspec. des_ifs.
                  eapply THS0. }
                { rewrite OPROMS' in *. ss. }
              * i. ss.
                rewrite IdentMap.gso in TIDSRC; auto.
                rewrite IdentMap.gso in TIDTGT; auto.
                exploit INV; eauto. i.
                splits.
                { etrans; eauto.
                  eapply unchanged_on_mon.
                  - etrans; eauto.
                  - i. eapply x.(Inv.SPACES) in PR.
                    econs; eauto. }
                { eapply not_attatched_mon; eauto.
                  i. econs; eauto. }
                { eapply inv_step; eauto. etrans; eauto. }
          }
        * apply not_and_or in H. des.
          { unfold no_update_on in H. des_ifs.
            apply NNPP in H. inv H.
            destruct (IdentMap.find tid' (Configuration.threads c_src0)) as
                [[[? ?] lc]|] eqn:FIND; cycle 1.
            { exfalso. eapply INVBOT in FIND. des.
              eapply UPDATESBOT; eauto. }
            specialize (THS0 tid'). rewrite FIND in *. des_ifs. inv THS0.
            exploit INV; eauto. i. inv x0.

            exploit AUPDATE.
            { eauto. }
            { etrans; eauto. eapply unchanged_on_mon; eauto.
              i. econs; eauto. }
            { eapply not_attatched_sum.
              - admit.
              - eapply not_attatched_mon; eauto.
                i. econs; eauto. }
            i. des. exfalso. eapply race_lemma; try eassumption.
            - eapply no_promise_program_step_rtc. eapply STEP.
            -
Admitted.


(*               eapply pred_step_rtc_mon; cycle 1. *)
(*               + eapply STEP. *)

(*                 [|eapply HOLD0]. *)


(*               eapply HOLD. *)
(*             - eauto. *)
(*             - eauto. *)
(*             - eauto. *)
(*             - eauto. *)

(*             exfaslo. *)


(*             - *)

(*                     eauto. } *)
(*                   { rewrite IdentMap.gso in TIDTGT; eauto. } *)




(*                   { *)

(*                     replace (oproms \2/ promised promises) with *)
(*                         (all_promises *)
(*                            (Configuration.mk *)
(*                               (IdentMap.add *)
(*                                  tid *)
(*                                  (existT (Language.state (E:=ProgramEvent.t)) lang st3, *)
(*                                   (Local.mk tview promises)) *)
(*                                  (Configuration.threads c_tgt0)) *)
(*                               (Configuration.sc c_src0) *)
(*                               memory3) (fun _ => True)) in MEM1; auto. *)



(*                   econsss. *)
(*                   inv STEP. *)


(*             inv FORGET. ss. ss. *)


(*             instantiate (1:=e0). *)

(*           admit. *)
(*         * *)


(*     - *)

(*           inv PR. *)


(*         inv WFSRC. inv WF1. econs; ss; eauto. *)
(*         eapply THREADS; eauto. *)


(*         eauto. *)


(*           { *)
(*         * eauto. *)
(*         * *)



(*         econs. *)

(*         instantiate (1:=Thread.mk _ st1 lc0 Configuration.sc c_src0 (Configuration.memory c_src0)). *)

(*         eauto. *)
(*       + *)

(*         instan *)

(*     ((fun _ => True) *)
(*                             /1\ (no_update_on updates) *)
(*                             /1\ (no_read_msgs others)) *)



(*         (Configuration.threads c_tgt0)). *)


(*                             /1\ (no_update_on updates) *)
(*                             /1\ (no_read_msgs others)) lang)) th_tgt th_tgt') *)


(*       (OTHERSPACE: others \2/ otherspace <2= unchangables th_tgt.(Thread.memory) th_tgt.(Thread.local).(Local.promises)) *)




(*       hexploit consistent_promise_consistent; eauto; ss. } *)


(*       - *)

(*     { inv WFTGT. eauto. } *)
(*     { inv WFTGT. eauto. } *)

(*       inv WFTGT. *)

(*     exploit rtc_tau_step_promise_consistent; eauto. *)


(*     assert (CONSISTENT1: Local.promise_consistent lc3). *)
(*     { exploit consistent_promise_consistent; eauto; ss. *)
(*       - *)


(*          (RACEFREE: pf_racefree c_src) *)
(*          (WFSRC: Configuration.wf c_src) *)
(*          (WFTGT: Configuration.wf c_tgt) *)




(*       (Configuration.init s) (Configuration.init s) *)
(* . *)
(* Proof. *)
(* Admitted. *)

Inductive sim_pf
          (mlast: Ident.t -> Memory.t)
          (spaces : Ident.t -> (Loc.t -> Time.t -> Prop))
          (updates: Ident.t -> (Loc.t -> Time.t -> Prop))
          (aupdates: Ident.t -> (Loc.t -> Time.t -> Prop))
          (c_src c_tgt: Configuration.t) : Prop :=
| sim_pf_intro
    (FORGET: forget_config c_src c_tgt)

    (FUTURE:
       forall tid,
         unchanged_on (spaces tid) (mlast tid) c_src.(Configuration.memory))
    (NOATTATCH:
       forall tid,
         not_attatched (updates tid) c_src.(Configuration.memory))

    (INV:
       forall
         tid lang_src st_src lc_src lang_tgt st_tgt lc_tgt
         (TIDSRC: IdentMap.find tid c_src.(Configuration.threads) =
                  Some (existT _ lang_src st_src, lc_src))
         (TIDTGT: IdentMap.find tid c_tgt.(Configuration.threads) =
                  Some (existT _ lang_tgt st_tgt, lc_tgt)),
         Inv.t c_tgt.(Configuration.memory) _ st_src lc_src lc_tgt.(Local.promises) (spaces tid) (updates tid) (aupdates tid) (mlast tid))

    (RACEFREE: pf_racefree c_src)
    (WFSRC: Configuration.wf c_src)
    (WFTGT: Configuration.wf c_tgt)
.




Lemma updates_list_exists
      P lang th0 th1
      (BOT: th0.(Thread.local).(Local.promises) = Memory.bot)
      (STEPS: rtc (tau (@pred_step (P /1\ no_promise) lang)) th0 th1)
  :
    exists (updates: Loc.t -> Prop),
      (<<COMPLETE:
         rtc (tau (@pred_step (P /1\ no_update_on (fun loc ts => Memory.max_ts loc th0.(Thread.memory) = ts /\ ~ updates loc)
                                 /1\ no_promise) lang)) th0 th1>>) /\
      (<<SOUND:
         forall loc (SAT: updates loc),
         exists th' th'' to valr valw releasedr releasedw ordr ordw,
           (<<STEPS: rtc (tau (@pred_step (P /1\ no_update_on (fun loc ts => Memory.max_ts loc th0.(Thread.memory) = ts /\ ~ updates loc)
                                             /1\ no_promise) lang)) th0 th'>>) /\
           (<<STEP: (@pred_step (P /1\ no_promise) lang)
                      (ThreadEvent.update loc (Memory.max_ts loc th0.(Thread.memory)) to valr valw releasedr releasedw ordr ordw)
                      th' th''>>)>>)
.
Proof.
  eapply Operators_Properties.clos_rt_rt1n_iff in STEPS.
  eapply Operators_Properties.clos_rt_rtn1_iff in STEPS.
  induction STEPS.
  - exists (fun _ => False). esplits; eauto. i. clarify.
  - des. inv H.
    destruct (classic (no_update_on (fun loc ts => Memory.max_ts loc th0.(Thread.memory) = ts /\ ~ updates loc) e)).
    + exists updates. esplits; eauto.
      eapply rtc_n1; eauto. econs; eauto. inv TSTEP. econs; eauto. des. esplits; eauto.
    + unfold no_update_on in H. des_ifs. apply NNPP in H.
      exists (fun l => l = loc \/ updates l).
      esplits; eauto.
      * eapply rtc_n1.
        { eapply pred_step_rtc_mon; eauto. i. ss. des. esplits; eauto.
          eapply no_update_on_mon; eauto. i. ss. des; eauto. }
        { econs; eauto. inv TSTEP. econs; eauto.
          des. esplits; eauto. ss. ii. des. eauto. }
      * i. des.
        { clarify. exists y, z. esplits; eauto.
          eapply pred_step_rtc_mon; eauto. i. ss. des. esplits; eauto.
          eapply no_update_on_mon; eauto. i. ss. des; eauto. }
        { exploit SOUND; eauto. i. des.
          exists th', th''. esplits; eauto.
          eapply pred_step_rtc_mon; eauto. i. ss. des. esplits; eauto.
          eapply no_update_on_mon; eauto. i. ss. des; eauto. }
Qed.


(* Lemma updates_list_exists *)
(*       P lang th0 th1 *)
(*       (BOT: th0.(Thread.local).(Local.promises) = Memory.bot) *)
(*       (STEPS: rtc (tau (@pred_step (P /1\ no_promise) lang)) th0 th1) *)
(*   : *)
(*     exists (updates: Loc.t -> Time.t -> Prop), *)
(*       (<<COMPLETE: *)
(*          rtc (tau (@pred_step (P /1\ no_update_on (fun loc ts => promised th0.(Thread.memory) loc ts /\ ~ updates loc ts) *)
(*                                  /1\ no_promise) lang)) th0 th1>>) /\ *)
(*       (<<SOUND: *)
(*          forall loc ts (SAT: updates loc ts), *)
(*          exists th' th'' to valr valw releasedr releasedw ordr ordw, *)
(*            (<<STEPS: rtc (tau (@pred_step (P /1\ no_update_on (fun loc ts => promised th0.(Thread.memory) loc ts /\ ~ updates loc ts) *)
(*                                              /1\ no_promise) lang)) th0 th'>>) /\ *)
(*            (<<STEP: (@pred_step (P /1\ no_promise) lang) *)
(*                       (ThreadEvent.update loc ts to valr valw releasedr releasedw ordr ordw) *)
(*                       th' th''>>)>>) /\ *)

(*       (<<NOATTATCHED: not_attatched updates th0.(Thread.memory)>>) *)
(* . *)
(* Proof. *)
(*   eapply Operators_Properties.clos_rt_rt1n_iff in STEPS. *)
(*   eapply Operators_Properties.clos_rt_rtn1_iff in STEPS. *)
(*   induction STEPS. *)
(*   - exists (fun _ _ => False). esplits; eauto. *)
(*     + i. clarify. *)
(*     + ii. clarify. *)
(*   - des. inv H. *)
(*     destruct (classic (no_update_on (fun loc ts => promised th0.(Thread.memory) loc ts /\ ~ updates loc ts) e)). *)
(*     + exists updates. esplits; eauto. *)
(*       eapply rtc_n1; eauto. econs; eauto. inv TSTEP. econs; eauto. des. esplits; eauto. *)
(*     + unfold no_update_on in H. des_ifs. apply NNPP in H. *)
(*       exists (fun l t => (l = loc /\ t = tsr) \/ updates l t). *)
(*       esplits; eauto. *)

(*       * eapply rtc_n1. *)
(*         { eapply pred_step_rtc_mon; eauto. i. ss. des. esplits; eauto. *)
(*           eapply no_update_on_mon; eauto. i. ss. des; eauto. } *)
(*         { econs; eauto. inv TSTEP. econs; eauto. *)
(*           des. esplits; eauto. ss. ii. des. eauto. } *)
(*       * i. des. *)
(*         { clarify. exists y, z. esplits; eauto. *)
(*           eapply pred_step_rtc_mon; eauto. i. ss. des. esplits; eauto. *)
(*           eapply no_update_on_mon; eauto. i. ss. des; eauto. } *)
(*         { exploit SOUND; eauto. i. des. *)
(*           exists th', th''. esplits; eauto. *)
(*           eapply pred_step_rtc_mon; eauto. i. ss. des. esplits; eauto. *)
(*           eapply no_update_on_mon; eauto. i. ss. des; eauto. } *)
(*       * eapply not_attatched_sum; eauto. *)
(*         eapply attatched_preserve_rtc; try apply COMPLETE; eauto. *)
(*         { eapply update_not_attatched; eauto. *)
(*           eapply promise_bot_no_promise_rtc; try apply COMPLETE; eauto. } *)
(*         { i. des. clarify. } *)
(* Qed. *)



Inductive shifted_map mlast mcert
          (updates: Loc.t -> Prop)
          (sky gap: TimeMap.t)
          (f: Loc.t -> Time.t -> Time.t): Prop :=
| shifted_map_intro
    (PRSV: map_preserving (times_in_memory mcert) f)
    (SAME: forall l t (TLE: Time.le t (Memory.max_ts l mlast)),
        f l t = t)
    (INGAP: forall l t (TLT: Time.lt (Memory.max_ts l mcert) t),
        Time.lt (f l t) (gap l))
    (AFTERSKY: forall l t (TLT: Time.lt (Memory.max_ts l mcert) t),
        Time.lt (sky l) (f l t))
.

Lemma shifted_map_exists mlast mcert updates
      (MLE: Memory.le mlast mcert)
      (sky gap: TimeMap.t)
      (SKY: forall l, Time.lt (Memory.max_ts l mlast) (sky l))
      (GAP: forall l, Time.lt (Memory.max_ts l mlast) (gap l))
  :
    exists f, (<<SHIFTED: shifted_map mlast mcert updates sky gap f>>).
Proof.
  (* may be very hard... *)
Admitted.

Lemma shifted_map_preserving_last_mem  mlast mcert updates sky gap f
      (CLOSED: Memory.closed mlast)
      (SHIFTED: shifted_map mlast mcert updates sky gap f)
  :
    memory_map f mlast mlast.
Proof.
  inv SHIFTED. inv PRSV. econs; i.
  - exploit Memory.max_ts_spec; eauto. i. des.
    repeat erewrite SAME; eauto.
    + rewrite GET. unfold msg_map. des_ifs. repeat f_equal.
      inv CLOSED. exploit CLOSED0; try apply GET; eauto. i. des.
      inv MSG_CLOSED. inv CLOSED; ss. f_equal.
      destruct view. inv CLOSED1. unfold view_map, timemap_map. ss. f_equal.
      * extensionality l. erewrite SAME; auto.
        specialize (PLN l). des.
        exploit Memory.max_ts_spec; eauto. i. des. auto.
      * extensionality l. erewrite SAME; auto.
        specialize (RLX l). des.
        exploit Memory.max_ts_spec; eauto. i. des. auto.
    + exploit Memory.get_ts; try apply GET; eauto. i. des.
      * clarify.
      * left. eapply TimeFacts.lt_le_lt; eauto.
  - destruct msg_src as [from msg]. exploit Memory.max_ts_spec; eauto. i. des.
    esplits.
    + erewrite SAME; eauto.
    + eauto.
Qed.

(* Lemma future_lifting *)
(*       P lang th0 th1 *)
(*       (BOT: th0.(Thread.local).(Local.promises) = Memory.bot) *)
(*       (STEPS: rtc (tau (@pred_step (P /1\ no_promise) lang)) th0 th1) *)
(*   : *)
(*     exists (updates: Loc.t -> Time.t -> Prop), *)
(*       (<<COMPLETE: *)
(*          rtc (tau (@pred_step (P /1\ no_update_on (fun loc ts => promised th0.(Thread.memory) loc ts /\ ~ updates loc ts) *)
(*                                  /1\ no_promise) lang)) th0 th1>>) /\ *)





(* Lemma inv_monotone st proms sky updates mlast v0 v1 *)
(*       (LE: TimeMap.le v0 v1) *)
(*       (INV: Inv.t st proms sky updates mlast v1) *)
(*   : *)
(*     Inv.t st proms sky updates mlast v0. *)
(* Proof. *)
(*   inv INV. econs; i. *)
(*   - eapply PROMS; ss. *)
(*     inv FUTURE. econs; ss. *)
(*     i. etrans; eauto. *)
(*   - eapply UPDATE; ss. *)
(*     inv FUTURE. econs; ss. *)
(*     i. etrans; eauto. *)
(* Qed. *)

(* Lemma inv_hold_self *)
(*       st locked proms sky mem *)
(*       (SKY: TimeMap.le (Memory.max_timemap mem) sky) *)
(*       (PROM: forall l t, covered proms l t -> covered mem l t -> False) *)
(*   : *)
(*     Inv.hold st locked proms sky mem mem *)
(* . *)
(* Proof. *)
(*   ii. econs; i; ss; eauto. *)
(*   revert INV. induction FUTURE; ss; i.     *)
(*   clarify. unfold TimeMap.add in *. ss. *)
(*   des_ifs. *)
(*   - left. eapply TimeFacts.le_lt_lt; cycle 1; eauto. *)
(*     eapply IHFUTURE; ss. *)
(*     eapply inv_monotone; eauto. *)
(*     ii. des_ifs. *)
(*     + left. eauto. *)
(*     + right. ss. *)
(*   - eapply IHFUTURE; eauto. *)
(*     eapply inv_monotone; eauto. *)
(*     ii. des_ifs. *)
(*     + left. eauto. *)
(*     + right. ss. *)
(* Qed. *)

(* (* TODO *) *)
(* Lemma consistent_inhabited *)
(*       mlast skylast c_src c_tgt tid *)
(*       (FORGET: forget_config c_src c_tgt) *)
(*       (RACEFREE: pf_racefree c_src) *)
(*       (INHABITED: forall tid' (NEQ: tid'<>tid), *)
(*           Inv.inhabited *)
(*             (Threads.find tid' c_src.(Configuration.threads)) *)
(*             (Locked.t (c_tgt.(Configuration.mpreds) tid')) *)
(*             ((Threads.find tid' c_tgt.(Configuration.threads)).(StateLocal.local).(Local.promises)) *)
(*             (skylast tid') (mlast tid')) *)
(*       (HOLD: forall tid' (NEQ: tid'<>tid), *)
(*           Inv.hold *)
(*             (Threads.find tid' c_src.(Configuration.threads)) *)
(*             (Locked.t (c_tgt.(Configuration.mpreds) tid')) *)
(*             ((Threads.find tid' c_tgt.(Configuration.threads)).(StateLocal.local).(Local.promises)) *)
(*             (skylast tid') (mlast tid') c_src.(Configuration.memory)) *)
(*       (CONSISTENT: Thread.consistent *)
(*                      (c_tgt.(Configuration.mpreds) tid) *)
(*                      bot2 *)
(*                      (to_thread *)
(*                         (Threads.find tid c_tgt.(Configuration.threads)) *)
(*                         (c_tgt.(Configuration.sc)) *)
(*                         (c_tgt.(Configuration.memory)))) *)
(*   : *)
(*     Inv.inhabited *)
(*       (Threads.find tid c_src.(Configuration.threads)) *)
(*       (Locked.t (c_tgt.(Configuration.mpreds) tid)) *)
(*       ((Threads.find tid c_tgt.(Configuration.threads)).(StateLocal.local).(Local.promises)) *)
(*       (Memory.max_timemap c_tgt.(Configuration.memory)) c_src.(Configuration.memory). *)
(* Admitted. *)


(* Definition not_stuck lang (st: Language.state lang) := *)
(*   exists st' e, Language.step _ e st st'. *)

(* Lemma same_add_same ths tid st *)
(*       (FIND: Threads.find tid ths = st) *)
(*       (STEP: not_stuck _ st.(StateLocal.state)) *)
(*   : *)
(*     Threads.add tid st ths = ths. *)
(* Proof. *)
(*   eapply IdentMap.eq_leibniz. ii. *)
(*   unfold Threads.find, Threads.add in *. *)
(*   rewrite IdentMap.Facts.add_o. des_ifs. *)
(*   exfalso. inv STEP. des. inv H. *)
(* Qed. *)

(* Ltac etatac := match goal with *)
(*                  [|- ?x = ?y] => *)
(*                  (try (destruct x; ss; clarify; eauto; fail));              *)
(*                  (try (destruct y; ss; clarify; eauto; fail)); *)
(*                  (try (dependent destruction x; ss; clarify; eauto; fail)); *)
(*                  (try (dependent destruction y; ss; clarify; eauto; fail)) *)
(*                end. *)


(* Lemma sim_pf_step *)
(*       c1_src c1_tgt *)
(*       c3_tgt e tid tf *)
(*       (SIM: sim_pf_all c1_src c1_tgt) *)
(*       (STEP_TGT: Configuration.step tf e tid c1_tgt c3_tgt) *)
(*   : *)
(*     exists c3_src, *)
(*       (<<STEP_SRC: opt pftstep e tid c1_src c3_src>>) /\ *)
(*       (<<SIM: sim_pf_all c3_src c3_tgt>>) *)
(* . *)
(* Proof. *)
(*   assert (NOABORT: e <> Some MachineEvent.abort). *)
(*   { eapply no_abort; eauto. } *)
(*   inv SIM. exploit pf_step_hold_other; eauto. *)
(*   inv SIM0. i. des. *)

(*   assert (SIMPF: sim_pf_all *)
(*                    (Configuration.mk *)
(*                       (Threads.add tid (StateLocal.mk _ (th3_src.(Thread.state)) *)
(*                                                       (th3_src.(Thread.local)))  *)
(*                                    (Configuration.threads c1_src)) *)
(*                       (Configuration.sc c3_tgt) *)
(*                       th3_src.(Thread.memory) MPreds.init) *)
(*                    c3_tgt). *)

(*   { *)
(*       destruct th3_src. econs. *)
(*       instantiate (1:= fun tid' => if (Ident.eq_dec tid tid') then Memory.max_timemap c3_tgt.(Configuration.memory) else skylast tid'). *)
(*       instantiate (1:= fun tid' => if (Ident.eq_dec tid tid') then memory else mlast tid'). *)
(*       assert (RACEFREE0: pf_racefree *)
(*     {| *)
(*     Configuration.threads := Threads.add tid *)
(*                                {| *)
(*                                StateLocal.lang := StateLocal.lang *)
(*                                                 (Threads.find tid *)
(*                                                 (Configuration.threads *)
(*                                                 c1_src)); *)
(*                                StateLocal.state := state; *)
(*                                StateLocal.local := local |} *)
(*                                (Configuration.threads c1_src); *)
(*     Configuration.sc := sc; *)
(*     Configuration.memory := memory; *)
(*     Configuration.mpreds := MPreds.init |}). *)
(*       { eapply pf_racefree_step; eauto. ss. clarify. *)
(*         admit. *)
(*         (* inv STEPS_SRC0. *) *)
(*         (* econs; [|left]. econs. econs. econs; ss; eauto. *) *)
(*         (* etatac. *) *)
(*       } *)
(*       econs; ss; clarify; eauto. *)
(*       * econs; i; ss. *)
(*         inv FORGET. addtac. *)
(*         inv STEP_TGT; ss; addtac. *)
(*       * i. des_ifs; addtac. *)
(*         -- Opaque Inv.inhabited. *)
(*           set *)
(*              (C:= @consistent_inhabited *)
(*                 (fun tid' => if (Ident.eq_dec tid0 tid') then memory else mlast tid') *)
(*                 (fun tid' => if (Ident.eq_dec tid0 tid') then Memory.max_timemap c3_tgt.(Configuration.memory) else skylast tid') *)
(*                 (Configuration.mk *)
(*                    (Threads.add tid0 (StateLocal.mk _ state local)  *)
(*                                 (Configuration.threads c1_src)) *)
(*                    (Configuration.sc c3_tgt) memory MPreds.init) *)
(*                 c3_tgt tid0); ss; i; eauto. *)
(*           addtac. *)
(*           eapply C; eauto; clear C. *)
(*            ++ inv FORGET. econs; i; ss; addtac. *)
(*               replace (Threads.find tid (Configuration.threads c3_tgt)) with *)
(*                   (Threads.find tid (Configuration.threads c1_tgt)); eauto. *)
(*               inv STEP_TGT; addtac; addtac. *)
(*            ++ i. addtac. ss. *)
(*               replace (Locked.t (Configuration.mpreds c3_tgt tid')) with *)
(*                   (Locked.t (Configuration.mpreds c1_tgt tid')); cycle 1. *)
(*               { inv STEP_TGT; repeat addtac. } *)
(*               replace (Threads.find tid' (Configuration.threads c3_tgt)) with *)
(*                   (Threads.find tid' (Configuration.threads c1_tgt)); eauto. *)
(*               { inv STEP_TGT; repeat addtac. } *)
(*            ++ i. addtac. *)
(*               replace (Locked.t (Configuration.mpreds c3_tgt tid')) with *)
(*                   (Locked.t (Configuration.mpreds c1_tgt tid')); eauto. *)
(*               { inv STEP_TGT; repeat addtac. } *)
(*            ++ inv STEP_TGT; repeat addtac; unfold to_thread; ss; eauto. *)
(*               ** eapply Thread.consistent_le; eauto. clarify. *)
(*               ** destruct (Threads.find tid0 (Configuration.threads c1_tgt)). *)
(*                  dependent destruction TID. ss. *)
(*                  eapply Thread.consistent_le; eauto. clarify. *)

(*         -- replace (Locked.t (Configuration.mpreds c3_tgt tid0)) with *)
(*                   (Locked.t (Configuration.mpreds c1_tgt tid0)); cycle 1. *)
(*            { inv STEP_TGT; repeat addtac. } *)
(*            replace (Threads.find tid0 (Configuration.threads c3_tgt)) with *)
(*                (Threads.find tid0 (Configuration.threads c1_tgt)); eauto. *)
(*            { inv STEP_TGT; repeat addtac. } *)
(*       * i. addtac. *)
(*         -- eapply inv_hold_self. *)
(*            ++ clear - MEM. admit. *)
(*            ++ clear - MEM. i. inv MEM. *)
(*               exploit FORGET; eauto. *)
(*               econs. eauto. *)
(*         -- replace (Locked.t (Configuration.mpreds c3_tgt tid0)) with *)
(*                   (Locked.t (Configuration.mpreds c1_tgt tid0)); eauto. *)
(*            { inv STEP_TGT; repeat addtac. } *)
(*       * eapply finite_hole_preserve; eauto. *)
(*       * i. clarify. des_ifs. rewrite <- UNCHANGED. *)
(*         { inv STEP_TGT; eauto; ss. *)
(*           inv RELY. addtac. *)
(*           specialize (WRITABLE l). des; eauto. *)
(*           exfalso. dup LK. *)
(*           inv LK; destruct hd; *)
(*             specialize (WRITABLE tid0 t t0 tl n0 (eq_sym H0)); *)
(*             rewrite <- H0 in *; *)
(*             eapply Locked.locked_non_writable; eauto. *)
(*         } *)
(*         inv STEP_TGT; eauto; addtac; ss; des_ifs. *)
(*       * eapply Configuration.step_future; eauto. *)
(*       * eapply Configuration.step_future; eauto. *)
(*       * eapply Configuration.step_future; eauto. *)
(*     } *)

(*   eapply rtc_tail in STEPS_SRC. des. des; inv STEP_SRC. *)
(*   - exists (Configuration.mk *)
(*                    (Threads.add tid (StateLocal.mk _ (th3_src.(Thread.state)) *)
(*                                                     (th3_src.(Thread.local)))  *)
(*                                 (Configuration.threads c1_src)) *)
(*                    (Configuration.sc c3_tgt) *)
(*                    th3_src.(Thread.memory) MPreds.init). *)
(*     split. *)
(*     + inv STEPS_SRC0. rewrite <- EVENT. *)
(*       right. *)
(*       destruct (Threads.find tid (Configuration.threads c1_src)) eqn: TEQ. *)
(*       econs; ss; eauto. *)
(*       destruct th3_src. rewrite <- SC. ss. *)

(*     +  *)
(*     { *)
(*       destruct th3_src. econs. *)
(*       instantiate (1:= fun tid' => if (Ident.eq_dec tid tid') then Memory.max_timemap c3_tgt.(Configuration.memory) else skylast tid'). *)
(*       instantiate (1:= fun tid' => if (Ident.eq_dec tid tid') then memory else mlast tid'). *)
(*       assert (RACEFREE0: pf_racefree *)
(*     {| *)
(*     Configuration.threads := Threads.add tid *)
(*                                {| *)
(*                                StateLocal.lang := StateLocal.lang *)
(*                                                 (Threads.find tid *)
(*                                                 (Configuration.threads *)
(*                                                 c1_src)); *)
(*                                StateLocal.state := state; *)
(*                                StateLocal.local := local |} *)
(*                                (Configuration.threads c1_src); *)
(*     Configuration.sc := sc; *)
(*     Configuration.memory := memory; *)
(*     Configuration.mpreds := MPreds.init |}). *)
(*       { eapply pf_racefree_step; eauto. ss. clarify. *)
(*         inv STEPS_SRC0. *)
(*         econs; [|left]. econs. econs. econs; ss; eauto. *)
(*         etatac. } *)
(*       econs; ss; clarify; eauto. *)
(*       * econs; i; ss. *)
(*         inv FORGET. addtac. *)
(*         inv STEP_TGT; ss; addtac. *)
(*       * i. des_ifs; addtac. *)
(*         -- Opaque Inv.inhabited. *)
(*           set *)
(*              (C:= @consistent_inhabited *)
(*                 (fun tid' => if (Ident.eq_dec tid0 tid') then memory else mlast tid') *)
(*                 (fun tid' => if (Ident.eq_dec tid0 tid') then Memory.max_timemap c3_tgt.(Configuration.memory) else skylast tid') *)
(*                 (Configuration.mk *)
(*                    (Threads.add tid0 (StateLocal.mk _ state local)  *)
(*                                 (Configuration.threads c1_src)) *)
(*                    (Configuration.sc c3_tgt) memory MPreds.init) *)
(*                 c3_tgt tid0); ss; i; eauto. *)
(*           addtac. *)
(*           eapply C; eauto; clear C. *)
(*            ++ inv FORGET. econs; i; ss; addtac. *)
(*               replace (Threads.find tid (Configuration.threads c3_tgt)) with *)
(*                   (Threads.find tid (Configuration.threads c1_tgt)); eauto. *)
(*               inv STEP_TGT; addtac; addtac. *)
(*            ++ i. addtac. ss. *)
(*               replace (Locked.t (Configuration.mpreds c3_tgt tid')) with *)
(*                   (Locked.t (Configuration.mpreds c1_tgt tid')); cycle 1. *)
(*               { inv STEP_TGT; repeat addtac. } *)
(*               replace (Threads.find tid' (Configuration.threads c3_tgt)) with *)
(*                   (Threads.find tid' (Configuration.threads c1_tgt)); eauto. *)
(*               { inv STEP_TGT; repeat addtac. } *)
(*            ++ i. addtac. *)
(*               replace (Locked.t (Configuration.mpreds c3_tgt tid')) with *)
(*                   (Locked.t (Configuration.mpreds c1_tgt tid')); eauto. *)
(*               { inv STEP_TGT; repeat addtac. } *)
(*            ++ inv STEP_TGT; repeat addtac; unfold to_thread; ss; eauto. *)
(*               ** eapply Thread.consistent_le; eauto. clarify. *)
(*               ** destruct (Threads.find tid0 (Configuration.threads c1_tgt)). *)
(*                  dependent destruction TID. ss. *)
(*                  eapply Thread.consistent_le; eauto. clarify. *)

(*         -- replace (Locked.t (Configuration.mpreds c3_tgt tid0)) with *)
(*                   (Locked.t (Configuration.mpreds c1_tgt tid0)); cycle 1. *)
(*            { inv STEP_TGT; repeat addtac. } *)
(*            replace (Threads.find tid0 (Configuration.threads c3_tgt)) with *)
(*                (Threads.find tid0 (Configuration.threads c1_tgt)); eauto. *)
(*            { inv STEP_TGT; repeat addtac. } *)
(*       * i. addtac. *)
(*         -- eapply inv_hold_self. *)
(*            ++ clear - MEM. admit. *)
(*            ++ clear - MEM. i. inv MEM. *)
(*               exploit FORGET; eauto. *)
(*               econs. eauto. *)
(*         -- replace (Locked.t (Configuration.mpreds c3_tgt tid0)) with *)
(*                   (Locked.t (Configuration.mpreds c1_tgt tid0)); eauto. *)
(*            { inv STEP_TGT; repeat addtac. } *)
(*       * eapply finite_hole_preserve; eauto. *)
(*       * i. clarify. des_ifs. rewrite <- UNCHANGED. *)
(*         { inv STEP_TGT; eauto; ss. *)
(*           inv RELY. addtac. *)
(*           specialize (WRITABLE l). des; eauto. *)
(*           exfalso. dup LK. *)
(*           inv LK; destruct hd; *)
(*             specialize (WRITABLE tid0 t t0 tl n0 (eq_sym H0)); *)
(*             rewrite <- H0 in *; *)
(*             eapply Locked.locked_non_writable; eauto. *)
(*         } *)
(*         inv STEP_TGT; eauto; addtac; ss; des_ifs. *)
(*       * eapply Configuration.step_future; eauto. *)
(*       * eapply Configuration.step_future; eauto. *)
(*       * eapply Configuration.step_future; eauto. *)
(*     } *)
(*   -  *)
(* Admitted. *)







(* Lemma sim_pf_step *)
(*       c1_src c1_tgt *)
(*       c3_tgt e tid tf mlast skylast *)
(*       (SIM: sim_pf c1_src c1_tgt mlast skylast) *)
(*       (STEP_TGT: Configuration.step tf e tid c1_tgt c3_tgt) *)
(*   : *)
(*     exists c3_src, *)
(*       (<<STEP_SRC: opt pftstep e tid c1_src c3_src>>) /\ *)
(*       (<<SIM: sim_pf *)
(*                 c3_src c3_tgt *)
(*                 (fun tid' => if (Ident.eq_dec tid tid') then c3_src.(Configuration.memory) else skylast tid') *)
(*                 (fun tid' => if (Ident.eq_dec tid tid') then Memory.max_timemap c3_tgt.(Configuration.memory) else skylast tid') *)


(* (fun tid' => if (Ident.eq_dec tid tid') then Memory.max_timemap c3_tgt.(Configuration.memory) else skylast tid') *)

(*                          >>) *)
(* . *)
(* Proof. *)
(*   assert (NOABORT: e <> Some MachineEvent.abort). *)
(*   { eapply no_abort; eauto. } *)
(*   inv SIM. exploit pf_step_hold_other; eauto. *)
(*   inv SIM0. i. des. *)
(*   eapply rtc_tail in STEPS_SRC. des; inv STEP_SRC. *)
(*   - exists (Configuration.mk *)
(*                    (Threads.add tid (StateLocal.mk _ (th3_src.(Thread.state)) *)
(*                                                     (th3_src.(Thread.local)))  *)
(*                                 (Configuration.threads c1_src)) *)
(*                    (Configuration.sc c3_tgt) *)
(*                    th3_src.(Thread.memory) MPreds.init). *)
(*     split. *)
(*     + inv STEPS_SRC0. rewrite <- EVENT. *)
(*       right. *)
(*       destruct (Threads.find tid (Configuration.threads c1_src)) eqn: TEQ. *)
(*       econs; ss; eauto. *)
(*       destruct th3_src. rewrite <- SC. ss. *)

(*     +  *)
(*     { *)
(*       destruct th3_src. econs. *)
(*       instantiate (1:= fun tid' => if (Ident.eq_dec tid tid') then Memory.max_timemap c3_tgt.(Configuration.memory) else skylast tid'). *)
(*       instantiate (1:= fun tid' => if (Ident.eq_dec tid tid') then memory else mlast tid'). *)
(*       assert (RACEFREE0: pf_racefree *)
(*     {| *)
(*     Configuration.threads := Threads.add tid *)
(*                                {| *)
(*                                StateLocal.lang := StateLocal.lang *)
(*                                                 (Threads.find tid *)
(*                                                 (Configuration.threads *)
(*                                                 c1_src)); *)
(*                                StateLocal.state := state; *)
(*                                StateLocal.local := local |} *)
(*                                (Configuration.threads c1_src); *)
(*     Configuration.sc := sc; *)
(*     Configuration.memory := memory; *)
(*     Configuration.mpreds := MPreds.init |}). *)
(*       { eapply pf_racefree_step; eauto. ss. clarify. *)
(*         inv STEPS_SRC0. *)
(*         econs; [|left]. econs. econs. econs; ss; eauto. *)
(*         etatac. } *)
(*       econs; ss; clarify; eauto. *)
(*       * econs; i; ss. *)
(*         inv FORGET. addtac. *)
(*         inv STEP_TGT; ss; addtac. *)
(*       * i. des_ifs; addtac. *)
(*         -- Opaque Inv.inhabited. *)
(*           set *)
(*              (C:= @consistent_inhabited *)
(*                 (fun tid' => if (Ident.eq_dec tid0 tid') then memory else mlast tid') *)
(*                 (fun tid' => if (Ident.eq_dec tid0 tid') then Memory.max_timemap c3_tgt.(Configuration.memory) else skylast tid') *)
(*                 (Configuration.mk *)
(*                    (Threads.add tid0 (StateLocal.mk _ state local)  *)
(*                                 (Configuration.threads c1_src)) *)
(*                    (Configuration.sc c3_tgt) memory MPreds.init) *)
(*                 c3_tgt tid0); ss; i; eauto. *)
(*           addtac. *)
(*           eapply C; eauto; clear C. *)
(*            ++ inv FORGET. econs; i; ss; addtac. *)
(*               replace (Threads.find tid (Configuration.threads c3_tgt)) with *)
(*                   (Threads.find tid (Configuration.threads c1_tgt)); eauto. *)
(*               inv STEP_TGT; addtac; addtac. *)
(*            ++ i. addtac. ss. *)
(*               replace (Locked.t (Configuration.mpreds c3_tgt tid')) with *)
(*                   (Locked.t (Configuration.mpreds c1_tgt tid')); cycle 1. *)
(*               { inv STEP_TGT; repeat addtac. } *)
(*               replace (Threads.find tid' (Configuration.threads c3_tgt)) with *)
(*                   (Threads.find tid' (Configuration.threads c1_tgt)); eauto. *)
(*               { inv STEP_TGT; repeat addtac. } *)
(*            ++ i. addtac. *)
(*               replace (Locked.t (Configuration.mpreds c3_tgt tid')) with *)
(*                   (Locked.t (Configuration.mpreds c1_tgt tid')); eauto. *)
(*               { inv STEP_TGT; repeat addtac. } *)
(*            ++ inv STEP_TGT; repeat addtac; unfold to_thread; ss; eauto. *)
(*               ** eapply Thread.consistent_le; eauto. clarify. *)
(*               ** destruct (Threads.find tid0 (Configuration.threads c1_tgt)). *)
(*                  dependent destruction TID. ss. *)
(*                  eapply Thread.consistent_le; eauto. clarify. *)

(*         -- replace (Locked.t (Configuration.mpreds c3_tgt tid0)) with *)
(*                   (Locked.t (Configuration.mpreds c1_tgt tid0)); cycle 1. *)
(*            { inv STEP_TGT; repeat addtac. } *)
(*            replace (Threads.find tid0 (Configuration.threads c3_tgt)) with *)
(*                (Threads.find tid0 (Configuration.threads c1_tgt)); eauto. *)
(*            { inv STEP_TGT; repeat addtac. } *)
(*       * i. addtac. *)
(*         -- eapply inv_hold_self. *)
(*            ++ clear - MEM. admit. *)
(*            ++ clear - MEM. i. inv MEM. *)
(*               exploit FORGET; eauto. *)
(*               econs. eauto. *)
(*         -- replace (Locked.t (Configuration.mpreds c3_tgt tid0)) with *)
(*                   (Locked.t (Configuration.mpreds c1_tgt tid0)); eauto. *)
(*            { inv STEP_TGT; repeat addtac. } *)
(*       * eapply finite_hole_preserve; eauto. *)
(*       * i. clarify. des_ifs. rewrite <- UNCHANGED. *)
(*         { inv STEP_TGT; eauto; ss. *)
(*           inv RELY. addtac. *)
(*           specialize (WRITABLE l). des; eauto. *)
(*           exfalso. dup LK. *)
(*           inv LK; destruct hd; *)
(*             specialize (WRITABLE tid0 t t0 tl n0 (eq_sym H0)); *)
(*             rewrite <- H0 in *; *)
(*             eapply Locked.locked_non_writable; eauto. *)
(*         } *)
(*         inv STEP_TGT; eauto; addtac; ss; des_ifs. *)
(*       * eapply Configuration.step_future; eauto. *)
(*       * eapply Configuration.step_future; eauto. *)
(*       * eapply Configuration.step_future; eauto. *)
(*     } *)
(*   -  *)
(* Admitted. *)


(* Lemma sim_pf_step *)
(*       c1_src c1_tgt *)
(*       c3_tgt e tid tf *)
(*       (SIM: sim_pf_all c1_src c1_tgt) *)
(*       (STEP_TGT: Configuration.step tf e tid c1_tgt c3_tgt) *)
(*   : *)
(*     exists c3_src, *)
(*       (<<STEP_SRC: opt pftstep e tid c1_src c3_src>>) /\ *)
(*       (<<SIM: sim_pf_all c3_src c3_tgt>>) *)
(* . *)
(* Proof. *)
(*   assert (NOABORT: e <> Some MachineEvent.abort). *)
(*   { eapply no_abort; eauto. } *)
(*   inv SIM. exploit pf_step_hold_other; eauto. *)
(*   inv SIM0. i. des. *)
(*   eapply rtc_tail in STEPS_SRC. des; inv STEP_SRC. *)
(*   - exists (Configuration.mk *)
(*                    (Threads.add tid (StateLocal.mk _ (th3_src.(Thread.state)) *)
(*                                                     (th3_src.(Thread.local)))  *)
(*                                 (Configuration.threads c1_src)) *)
(*                    (Configuration.sc c3_tgt) *)
(*                    th3_src.(Thread.memory) MPreds.init). *)
(*     split. *)
(*     + inv STEPS_SRC0. rewrite <- EVENT. *)
(*       right. *)
(*       destruct (Threads.find tid (Configuration.threads c1_src)) eqn: TEQ. *)
(*       econs; ss; eauto. *)
(*       destruct th3_src. rewrite <- SC. ss. *)

(*     +  *)
(*     { *)
(*       destruct th3_src. econs. *)
(*       instantiate (1:= fun tid' => if (Ident.eq_dec tid tid') then Memory.max_timemap c3_tgt.(Configuration.memory) else skylast tid'). *)
(*       instantiate (1:= fun tid' => if (Ident.eq_dec tid tid') then memory else mlast tid'). *)
(*       assert (RACEFREE0: pf_racefree *)
(*     {| *)
(*     Configuration.threads := Threads.add tid *)
(*                                {| *)
(*                                StateLocal.lang := StateLocal.lang *)
(*                                                 (Threads.find tid *)
(*                                                 (Configuration.threads *)
(*                                                 c1_src)); *)
(*                                StateLocal.state := state; *)
(*                                StateLocal.local := local |} *)
(*                                (Configuration.threads c1_src); *)
(*     Configuration.sc := sc; *)
(*     Configuration.memory := memory; *)
(*     Configuration.mpreds := MPreds.init |}). *)
(*       { eapply pf_racefree_step; eauto. ss. clarify. *)
(*         inv STEPS_SRC0. *)
(*         econs; [|left]. econs. econs. econs; ss; eauto. *)
(*         etatac. } *)
(*       econs; ss; clarify; eauto. *)
(*       * econs; i; ss. *)
(*         inv FORGET. addtac. *)
(*         inv STEP_TGT; ss; addtac. *)
(*       * i. des_ifs; addtac. *)
(*         -- Opaque Inv.inhabited. *)
(*           set *)
(*              (C:= @consistent_inhabited *)
(*                 (fun tid' => if (Ident.eq_dec tid0 tid') then memory else mlast tid') *)
(*                 (fun tid' => if (Ident.eq_dec tid0 tid') then Memory.max_timemap c3_tgt.(Configuration.memory) else skylast tid') *)
(*                 (Configuration.mk *)
(*                    (Threads.add tid0 (StateLocal.mk _ state local)  *)
(*                                 (Configuration.threads c1_src)) *)
(*                    (Configuration.sc c3_tgt) memory MPreds.init) *)
(*                 c3_tgt tid0); ss; i; eauto. *)
(*           addtac. *)
(*           eapply C; eauto; clear C. *)
(*            ++ inv FORGET. econs; i; ss; addtac. *)
(*               replace (Threads.find tid (Configuration.threads c3_tgt)) with *)
(*                   (Threads.find tid (Configuration.threads c1_tgt)); eauto. *)
(*               inv STEP_TGT; addtac; addtac. *)
(*            ++ i. addtac. ss. *)
(*               replace (Locked.t (Configuration.mpreds c3_tgt tid')) with *)
(*                   (Locked.t (Configuration.mpreds c1_tgt tid')); cycle 1. *)
(*               { inv STEP_TGT; repeat addtac. } *)
(*               replace (Threads.find tid' (Configuration.threads c3_tgt)) with *)
(*                   (Threads.find tid' (Configuration.threads c1_tgt)); eauto. *)
(*               { inv STEP_TGT; repeat addtac. } *)
(*            ++ i. addtac. *)
(*               replace (Locked.t (Configuration.mpreds c3_tgt tid')) with *)
(*                   (Locked.t (Configuration.mpreds c1_tgt tid')); eauto. *)
(*               { inv STEP_TGT; repeat addtac. } *)
(*            ++ inv STEP_TGT; repeat addtac; unfold to_thread; ss; eauto. *)
(*               ** eapply Thread.consistent_le; eauto. clarify. *)
(*               ** destruct (Threads.find tid0 (Configuration.threads c1_tgt)). *)
(*                  dependent destruction TID. ss. *)
(*                  eapply Thread.consistent_le; eauto. clarify. *)

(*         -- replace (Locked.t (Configuration.mpreds c3_tgt tid0)) with *)
(*                   (Locked.t (Configuration.mpreds c1_tgt tid0)); cycle 1. *)
(*            { inv STEP_TGT; repeat addtac. } *)
(*            replace (Threads.find tid0 (Configuration.threads c3_tgt)) with *)
(*                (Threads.find tid0 (Configuration.threads c1_tgt)); eauto. *)
(*            { inv STEP_TGT; repeat addtac. } *)
(*       * i. addtac. *)
(*         -- eapply inv_hold_self. *)
(*            ++ clear - MEM. admit. *)
(*            ++ clear - MEM. i. inv MEM. *)
(*               exploit FORGET; eauto. *)
(*               econs. eauto. *)
(*         -- replace (Locked.t (Configuration.mpreds c3_tgt tid0)) with *)
(*                   (Locked.t (Configuration.mpreds c1_tgt tid0)); eauto. *)
(*            { inv STEP_TGT; repeat addtac. } *)
(*       * eapply finite_hole_preserve; eauto. *)
(*       * i. clarify. des_ifs. rewrite <- UNCHANGED. *)
(*         { inv STEP_TGT; eauto; ss. *)
(*           inv RELY. addtac. *)
(*           specialize (WRITABLE l). des; eauto. *)
(*           exfalso. dup LK. *)
(*           inv LK; destruct hd; *)
(*             specialize (WRITABLE tid0 t t0 tl n0 (eq_sym H0)); *)
(*             rewrite <- H0 in *; *)
(*             eapply Locked.locked_non_writable; eauto. *)
(*         } *)
(*         inv STEP_TGT; eauto; addtac; ss; des_ifs. *)
(*       * eapply Configuration.step_future; eauto. *)
(*       * eapply Configuration.step_future; eauto. *)
(*       * eapply Configuration.step_future; eauto. *)
(*     } *)
(*   -  *)
(* Admitted. *)






(* Lemma self_promise_remove *)
(*       P th_src th_tgt lang st v prom sc mem_src mem_tgt *)
(*       (TH_SRC: th_src = to_thread Thread.mk lang st (Local.mk v Memory.bot) sc mem_src) *)
(*       (TH_TGT: th_tgt = Thread.mk lang st (Local.mk v prom) sc mem_tgt) *)
(*       (MEM: forget_memory (covered prom) mem_src mem_tgt) *)
(*       (STEP: pred_step P lang e th_tgt th_tgt') *)
(*   : *)
(*     exists th_src', *)
(*       (<<STEP: opt (pred_step P lang) e th_src th_src'>>) /\ *)
(*       (<<MEM: forget_memory (covered opt (pred_step P lang) e th_src th_src'>>) /\ *)
(*       (<<STEP: opt (pred_step P lang) e th_src th_src'>>) *)

(* Lemma self_promise_remove *)
(*       P th_src th_tgt lang st v prom sc mem_src mem_tgt *)
(*       (TH_SRC: th_src = Thread.mk lang st (Local.mk v Memory.bot) sc mem_src) *)
(*       (TH_TGT: th_tgt = Thread.mk lang st (Local.mk v prom) sc mem_tgt) *)
(*       (MEM: forget_memory (covered prom) mem_src mem_tgt) *)
(*       (STEP: pred_step P lang e th_tgt th_tgt') *)
(*   : *)
(*     exists th_src', *)
(*       (<<STEP: opt (pred_step P lang) e th_src th_src'>>) /\ *)
(*       (<<MEM: forget_memory (covered opt (pred_step P lang) e th_src th_src'>>) /\ *)
(*       (<<STEP: opt (pred_step P lang) e th_src th_src'>>) *)


(*       AThread.step Thread.t st lc sc mem1  *)

(*       Thread.t *)
(*       AThread.step *)
(* Configuration.step *)

(* opt (AThread.step *)


(* Lemma sim_pf_sim_whole: *)
(*   sim_pf_all <2= (sim_whole (fun _ => pftstep) Configuration.step). *)
(* Proof. *)
(*   pcofix CIH. ii. *)
(*   pfold. econs. *)
(*   - esplits; eauto. *)
(*     inv PR. inv SIM. inv FORGET. *)
(*     ii. specialize (THS tid). inv THS. *)
(*     rewrite FIND in *. ss. econs; eauto. *)
(*     specialize (TERMINAL_TGT tid). *)
(*     destruct (Threads.find tid (Configuration.threads x1)). ss. *)
(*     dependent destruction STATE. eapply TERMINAL_TGT; eauto. *)
(*   - i. exploit sim_pf_step; eauto. i. des. esplits; eauto. *)
(* Qed. *)

(* Theorem drf_pf *)
(*       s *)
(*       (RACEFREE: pf_racefree (Configuration.init s)) *)
(*   : *)
(*     behaviors Configuration.step (Configuration.init s) <1= *)
(*     behaviors (fun _ => pftstep) (Configuration.init s) *)
(* . *)
(* Proof. *)
(*   apply sim_whole_adequacy, sim_pf_sim_whole, sim_pf_init. ss. *)
(* Qed. *)

(* Lemma self_promise_remove_lifting *)
(*       lang st1 st2 lc1_src lc1_tgt lc2_tgt mem1_tgt mem2_tgt mem1_src sc1 sc2 P  *)
(*       (STATE1 : forget_local lc1_src lc1_tgt) *)
(*       (MEM1 : forget_memory (Local.is_promised_loc lc1_src) *)
(*                                   mem1_src mem1_tgt) *)
(*       (TGT_STEP : tau (@pred_step P _)  *)
(*                       (Thread.mk lang st1 lc1_tgt sc1 mem1_tgt) *)
(*                       (Thread.mk _ st2 lc2_tgt sc2 mem2_tgt)) *)
(*       (CONSISTENT : promise_view_consistent lc2_tgt) *)
(*   : *)
(*     exists lc2_src mem2_src, *)
(*       <<SRC_STEP : (rc (tau (@pred_step P _))) *)
(*                        (Thread.mk _ st1 lc1_src sc1 mem1_src) *)
(*                        (Thread.mk _ st2 lc2_src sc2 mem2_src)>> /\ *)
(*       <<STATE1 : forget_local lc2_src lc2_tgt>> /\ *)
(*       <<MEM1 : forget_memory (Local.is_promised_loc lc2_src) *)
(*                                     mem2_src mem2_tgt>> *)
(* . *)
(* Proof. *)
(*   destruct TGT_STEP, TSTEP, STEP. *)
(*   dependent destruction STEP. dependent destruction STEP. *)
(*   - exists lc1_src, mem1_src. destruct LOCAL. subst. *)
(*     econs; eauto; [| econs]. *)
(*     + apply Relation_Operators.r_refl. *)
(*     + destruct STATE1; econs; eauto. *)
(*     + destruct MEM1. econs; eauto. admit. *)
(*   - admit. *)
(* Admitted. *)

(* Lemma other_promise_remove_lifting *)
(*       lang st1 st2 lc1 lc2 mem1_tgt mem2_tgt mem1_src sc1 sc2 P proms *)
(*       (MEM1 : forget_memory proms mem1_src mem1_tgt) *)
(*       (TGT_STEP : tau (@pred_step (P /1\ no_read_msgs proms /1\ *)
(*                                      no_read_msgs proms) _)  *)
(*                       (Thread.mk lang st1 lc1 sc1 mem1_tgt) *)
(*                       (Thread.mk _ st2 lc2 sc2 mem2_tgt)) *)
(*   : *)
(*     exists mem2_src, *)
(*       <<SRC_STEP : tau (@pred_step (P /1\ no_read_msgs proms /1\ *)
(*                                       no_read_msgs proms) _)   *)
(*                        (Thread.mk _ st1 lc1 sc1 mem1_src) *)
(*                        (Thread.mk _ st2 lc2 sc2 mem2_src)>> /\ *)
(*       <<MEM1 : forget_memory proms mem2_src mem2_tgt>> *)
(* . *)
(* Admitted. *)

(* Lemma future_lifting *)
(*       lang st1 st2 lc1 lc2 mem1_tgt mem2_tgt mem1_src sc1 sc2 P v1 v2 *)
(*       (TGT_STEP : rtc (tau (@pred_step (P /1\ write_between v1 v2) _))  *)
(*                       (Thread.mk lang st1 lc1 sc1 mem1_tgt) *)
(*                       (Thread.mk _ st2 lc2 sc2 mem2_tgt)) *)
(*       (INTERVAL_EMPTY : empty_interval v1 v2 (fun _ => True) mem1_src) *)
(*       (FUTURE : Memory.le mem1_src mem1_tgt) *)
(*   : *)
(*     exists mem2_src, *)
(*       <<SRC_STEP : rtc (tau (@pred_step (P /1\ write_between v1 v2) _)) *)
(*                        (Thread.mk _ st1 lc1 sc1 mem1_src) *)
(*                        (Thread.mk _ st2 lc2 sc2 mem2_src)>> *)
(* . *)
(* Admitted. *)
