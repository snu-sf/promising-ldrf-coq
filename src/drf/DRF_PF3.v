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
From PromisingLib Require Import Loc.

Require Import PF.
Require Import Race.
Require Import Behavior.
Require Import SimMemory.
Require Import yjtac.
Require Import Program.
Require Import Cell.
Require Import Time.
Require Import PredStep.
Require Import ReorderPromises2.
Require Import AbortProp.

Require Import DRF_PF.

Require Import PFConsistent.

Set Implicit Arguments.



(* Inductive my_caps (mem0 prom : Memory.t) (l : Loc.t) (t from : Time.t) (msg : Message.t) := *)
(*   (<<CAPS: caps mem0 prom l t from msg>>) /\ *)
(*   (<< *)


Definition wf_time_evt (P: Loc.t -> Time.t -> Prop) (e: ThreadEvent.t) : Prop :=
  match e with
  | ThreadEvent.promise loc from to msg kind =>
    (<<FROM: P loc from>>) /\ (<<TO: P loc to>>)
  | ThreadEvent.write loc from to val released ordw =>
    (<<FROM: P loc from>>) /\ (<<TO: P loc to>>)
  | ThreadEvent.update loc from to valr valw releasedr releasedw ordr ordw =>
    (<<TO: P loc to>>)
  | _ => True
  end.

Lemma wf_time_evt_mon P0 P1
      (LE: P0 <2= P1)
  :
    wf_time_evt P0 <1= wf_time_evt P1.
Proof.
  ii. unfold wf_time_evt in *. des_ifs; des; splits; eauto.
Qed.

Lemma step_times_list_exists P lang th0 th1 e
      (STEPS: (@pred_step P lang) e th0 th1)
  :
    exists times,
      (@pred_step (P /1\ wf_time_evt (fun loc to => List.In to (times loc))) lang) e th0 th1.
Proof.
  inv STEPS. destruct e.
  - exists (fun l => if Loc.eq_dec l loc then
                       [from; to] else []).
    econs; eauto.
    ss. splits; auto; des_ifs; ss; eauto.
  - exists (fun _ => []). econs; eauto. ss.
  - exists (fun _ => []). econs; eauto. ss.
  - exists (fun l => if Loc.eq_dec l loc then
                       [from; to] else []).
    econs; eauto.
    ss. splits; auto; des_ifs; ss; eauto.
  - exists (fun l => if Loc.eq_dec l loc then
                       [tsw] else []).
    econs; eauto.
    ss. splits; auto; des_ifs; ss; eauto.
  - exists (fun _ => []). econs; eauto. ss.
  - exists (fun _ => []). econs; eauto. ss.
  - exists (fun _ => []). econs; eauto. ss.
Qed.

Lemma times_list_exists P lang th0 th1
      (STEPS: rtc (tau (@pred_step P lang)) th0 th1)
  :
    exists times,
      rtc (tau (@pred_step (P /1\ wf_time_evt (fun loc to => List.In to (times loc))) lang)) th0 th1.
Proof.
  ginduction STEPS.
  - exists (fun _ => []). refl.
  - dup H. inv H0.
    eapply step_times_list_exists in TSTEP. des.
    exists (fun loc => times loc ++ times0 loc). econs 2.
    + econs; eauto. eapply pred_step_mon; eauto.
      i. ss. des. split; auto.
      eapply wf_time_evt_mon; eauto.
      i. ss. eapply List.in_or_app; eauto.
    + eapply pred_step_rtc_mon; eauto.
      i. ss. des. split; auto.
      eapply wf_time_evt_mon; eauto.
      i. ss. eapply List.in_or_app; eauto.
Qed.

(* Definition self_latest_reseves_loc (mem prom: Memory.t) (loc: Loc.t): Prop := *)
(*   Memory.latest_reserve loc mem prom. *)

Definition other_latest_reserves (L: Loc.t -> Prop)
           (mem: Memory.t) (loc: Loc.t) (to: Time.t) (from: Time.t) :=
  (<<LATEST: to = Memory.max_ts loc mem>>) /\
  (<<RESERVE: Memory.get loc to mem = Some (from, Message.reserve)>>) /\
  (<<OTHER: L loc>>)
.

Definition other_latest_reserves_times (L: Loc.t -> Prop)
           (mem: Memory.t) (loc: Loc.t) (to: Time.t): Prop :=
  exists from,
    (<<RESERVE: other_latest_reserves L mem loc to from>>).

Definition other_caps (L: Loc.t -> Prop)
           (mem0 mem1: Memory.t) (loc: Loc.t) (to: Time.t) (from: Time.t) :=
  (<<FULL: Memory.max_full_ts mem0 loc from>>) /\
  (<<LATEST: exists from0 val released,
      (<<CAP: caps mem0 mem1 loc to from0 (Message.full val released)>>)>>) /\
  (<<OTHER: L loc>>)
.

Definition other_caps_times (L: Loc.t -> Prop)
           (mem0 mem1: Memory.t) (loc: Loc.t) (to: Time.t) :=
  exists from,
    (<<CAP: other_caps L mem0 mem1 loc to from>>).

Definition times_in_memory (mem: Memory.t) (L: Loc.t -> list Time.t): Prop :=
  forall loc t,
    (<<SAT: List.In t (L loc)>>) <->
    (<<INMEMORY:
       (exists from msg, (<<GET: Memory.get loc t mem = Some (from, msg)>>)) \/
       (exists to msg, (<<GET: Memory.get loc to mem = Some (t, msg)>>))>>).

Lemma times_in_memory_exists mem
  :
    exists l, times_in_memory mem l.
Proof.
  hexploit (choice
              (fun loc tl =>
                 forall t,
                   (<<SAT: List.In t tl>>) <->
                   (<<INMEMORY:
                      (exists from msg, (<<GET: Memory.get loc t mem = Some (from, msg)>>)) \/
                      (exists to msg, (<<GET: Memory.get loc to mem = Some (t, msg)>>))>>))); auto.
  intros loc.
  hexploit (wf_cell_msgs_exists (mem loc)). i. des.
  exists ((List.map (fun ftm =>
                       match ftm with
                       | (from, _, _) => from
                       end) l)
            ++
            (List.map (fun ftm =>
                         match ftm with
                         | (_, to, _) => to
                         end) l)).
  i. split; i.
  - red in H. eapply List.in_app_or in H. des.
    + eapply List.in_map_iff in H. des.
      destruct x as [[from to] msg]. clarify.
      eapply COMPLETE in H0. right. eauto.
    + eapply List.in_map_iff in H. des.
      destruct x as [[from to] msg]. clarify.
      eapply COMPLETE in H0. left. eauto.
  - eapply List.in_or_app.  des.
    + right. eapply COMPLETE in GET.
      eapply List.in_map_iff. esplits; eauto. ss.
    + left. eapply COMPLETE in GET.
      eapply List.in_map_iff. esplits; eauto. ss.
Qed.

Inductive other_collapsing (L: Loc.t -> Prop)
          (mem: Memory.t): Loc.t -> Time.t -> Time.t -> Prop :=
| other_collapsing_not_in
    loc t
    (NSAT: ~ L loc)
  :
    other_collapsing L mem loc t t
| other_collapsing_in_memory
    loc t max
    (SAT: L loc)
    (FULL: Memory.max_full_ts mem loc max)
    (TLE: Time.le t max)
  :
    other_collapsing L mem loc t t
| other_collapsing_latest_reserve
    loc t max
    (SAT: L loc)
    (FULL: Memory.max_full_ts mem loc max)
    (MAX: t = Memory.max_ts loc mem)
  :
    other_collapsing L mem loc max t
| other_collapsing_cap
    loc t max
    (SAT: L loc)
    (FULL: Memory.max_full_ts mem loc max)
    (CAP: t = Time.incr (Memory.max_ts loc mem))
  :
    other_collapsing L mem loc max t
| other_collapsing_outer_memory
    loc t
    (SAT: L loc)
    (TLE: Time.lt (Time.incr (Memory.max_ts loc mem)) t)
  :
    other_collapsing L mem loc t t
.

Lemma forget_memory_get P mem0 mem1 loc to msg
      (FORGET: forget_memory P mem0 mem1)
      (GET: Memory.get loc to mem0 = Some msg)
  :
    (<<NOT: ~ P loc to>>) /\ (<<GET: Memory.get loc to mem1 = Some msg>>).
Proof.
  inv FORGET. destruct (classic (P loc to)).
  - exfalso. rewrite FORGET0 in GET; auto. clarify.
  - esplits; eauto.
    rewrite <- COMPLETE; auto.
Qed.

Lemma caps_get_reserve mem0 prom mem1 loc to from
      (RESERVE: Memory.reserve_wf prom mem0)
      (INHABITED: Memory.inhabited mem0)
      (CLOSED: Memory.closed mem0)
      (CAP: Memory.cap prom mem0 mem1)
      (CAPS: caps mem0 mem1 loc to from Message.reserve)
  :
    exists from0 to1 msg0 msg1,
      (<<GET0: Memory.get loc from mem0 = Some (from0, msg0)>>) /\
      (<<GET1: Memory.get loc to1 mem0 = Some (to, msg1)>>) /\
      (<<SPACE: forall t (ITV: Interval.mem (from, to) t), ~ covered loc t mem0>>)
.
Proof.
  unfold caps in CAPS. des. inv CAP.
  exploit COMPLETE; eauto. i. des.
  set (@cell_elements_least
         (mem0 loc)
         (fun t => Time.lt from t)). des.
  - hexploit (MIDDLE loc f from from0 to0).
    { econs; eauto. i.
      destruct (Memory.get loc ts mem0) eqn:GET2; auto. destruct p.
      exfalso. exploit LEAST.
      - eapply GET2.
      - eauto.
      - i. exploit Memory.get_ts; try apply GET.
        i. des; clarify.
        + eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
          * eapply SAT.
          * eapply Time.bot_spec.
        + eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt.
          * etrans.
            { eapply x1. }
            { eapply TS2. }
          * eauto. }
    { exploit memory_get_from_mon.
      - eapply x.
      - eapply GET.
      - eauto.
      - i. destruct x2; auto. destruct H. exfalso.
        exploit memory_get_from_inj.
        { eapply SOUND. eapply GET. }
        { eapply GET1. }
        i. des; clarify.
        + setoid_rewrite GET0 in GET. clarify.
        + eapply Time.lt_strorder; eauto. }
    i. exploit memory_get_from_inj.
    { eapply H. }
    { eapply GET1. }
    i. des; clarify.
    + esplits; eauto. ii. inv H0.
      exploit Memory.get_disjoint.
      * eapply SOUND. eapply GET2.
      * eapply H.
      * i. des; clarify. eapply x2; eauto.
    + specialize (INHABITED loc).
      eapply SOUND in INHABITED. clarify.
  - exploit Memory.max_ts_spec.
    { eapply x. }
    i. des. destruct MAX.
    + exfalso. eapply EMPTY; eauto.
    + unfold Time.eq in *. subst. exploit x0; auto. intros LATEST.
      exploit Memory.latest_val_exists; eauto. i. des.
      exploit Memory.max_full_view_exists; eauto. i. des.
      exploit BACK; eauto. i.
      exploit memory_get_from_inj.
      * eapply x1.
      * eapply GET1.
      * i. des; clarify.
        { exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
          - eapply Time.incr_spec.
          - rewrite BOT0. eapply Time.bot_spec. }
        { erewrite INHABITED in GET0. clarify. }
Qed.

Definition memory_concrete_le (lhs rhs: Memory.t): Prop :=
  forall loc to from val released
         (GET: Memory.get loc to lhs = Some (from, Message.full val released)),
    Memory.get loc to rhs = Some (from, Message.full val released).

Lemma memory_concrete_le_le
  :
    Memory.le <2= memory_concrete_le.
Proof.
  ii. eauto.
Qed.
Hint Resolve memory_concrete_le_le.

Lemma memory_concrete_le_closed_timemap tm mem0 mem1
      (MLE: memory_concrete_le mem0 mem1)
      (TM: Memory.closed_timemap tm mem0)
  :
    Memory.closed_timemap tm mem1.
Proof.
  ii. hexploit (TM loc). i. des.
  esplits; eauto.
Qed.

Lemma memory_concrete_le_closed_view vw mem0 mem1
      (MLE: memory_concrete_le mem0 mem1)
      (VW: Memory.closed_view vw mem0)
  :
    Memory.closed_view vw mem1.
Proof.
  inv VW. econs.
  - eapply memory_concrete_le_closed_timemap; eauto.
  - eapply memory_concrete_le_closed_timemap; eauto.
Qed.

Lemma memory_concrete_le_closed_opt_view vw mem0 mem1
      (MLE: memory_concrete_le mem0 mem1)
      (VW: Memory.closed_opt_view vw mem0)
  :
    Memory.closed_opt_view vw mem1.
Proof.
  inv VW; econs.
  eapply memory_concrete_le_closed_view; eauto.
Qed.

Lemma memory_concrete_le_closed_msg msg mem0 mem1
      (MLE: memory_concrete_le mem0 mem1)
      (MSG: Memory.closed_message msg mem0)
  :
    Memory.closed_message msg mem1.
Proof.
  inv MSG; econs.
  eapply memory_concrete_le_closed_opt_view; eauto.
Qed.

Lemma memory_concrete_le_closed_tview vw mem0 mem1
      (MLE: memory_concrete_le mem0 mem1)
      (VW: TView.closed vw mem0)
  :
    TView.closed vw mem1.
Proof.
  inv VW. econs.
  - i. eapply memory_concrete_le_closed_view; eauto.
  - eapply memory_concrete_le_closed_view; eauto.
  - eapply memory_concrete_le_closed_view; eauto.
Qed.

Lemma memory_concrete_le_reserve_wf prom mem0 mem1
      (MLE: memory_concrete_le mem0 mem1)
      (RESERVE: Memory.reserve_wf prom mem0)
  :
    Memory.reserve_wf prom mem1.
Proof.
  ii. eapply RESERVE in GET. des.
  esplits; eauto.
Qed.

Lemma memory_concrete_le_local_wf lc mem0 mem1
      (MLE: memory_concrete_le mem0 mem1)
      (PROM: Memory.le (Local.promises lc) mem1)
      (LOCAL: Local.wf lc mem0)
  :
    Local.wf lc mem1.
Proof.
  inv LOCAL. econs; eauto.
  - eapply memory_concrete_le_closed_tview; eauto.
  - eapply memory_concrete_le_reserve_wf; eauto.
Qed.

Lemma partial_cap_closed prom mem0 mem1 mem2
      (MLE: Memory.le prom mem0)
      (CLOSED: Memory.closed mem0)
      (RESERVEWF: Memory.reserve_wf prom mem0)
      (INHABITED: Memory.inhabited mem0)
      (CAP: Memory.cap prom mem0 mem2)
      (MLE0: Memory.le mem0 mem1)
      (MLE1: Memory.le mem1 mem2)
  :
    Memory.closed mem1.
Proof.
  exploit Memory.max_full_timemap_exists; eauto. intros [tm MAX].
  inv CLOSED. econs; eauto.
  i. destruct (Memory.get loc to mem0) as [[from0 msg0]|] eqn:GET.
  - dup GET. eapply MLE0 in GET. clarify.
    eapply CLOSED0 in GET0. des. esplits; eauto.
    eapply memory_concrete_le_closed_msg; eauto.
  - destruct msg.
    + eapply MLE1 in MSG.
      exploit caps_max_view; eauto.
      * econs; eauto.
      * i. des; clarify. esplits; eauto.
        { econs; eauto. econs; eauto. econs. refl. }
        { econs; eauto. ss. transitivity (Memory.max_ts loc mem0).
          - specialize (MAX loc). inv MAX. des.
            eapply Memory.max_ts_spec in GET0. des. eauto.
          - left. eapply Time.incr_spec. }
        { eapply memory_concrete_le_closed_msg; eauto.
          econs. econs. econs.
          - eapply Memory.max_full_timemap_closed; eauto.
          - eapply Memory.max_full_timemap_closed; eauto. }
    + esplits; eauto. econs.
Qed.

Lemma other_caps_forget_le
      mem0 mem1 mem2 prom (L: Loc.t -> Prop)
      (CAP: Memory.cap prom mem0 mem2)
      (FORGET: forget_memory (other_latest_reserves_times L mem0 \2/ other_caps_times L mem0 mem1) mem1 mem2)
  :
    memory_concrete_le mem0 mem1.
Proof.
  inv FORGET. ii.
  erewrite COMPLETE.
  - eapply Memory.cap_le in CAP; eauto. refl.
  - ii. des.
    + unfold other_latest_reserves_times in *. des.
      inv RESERVE. des. clarify.
    + unfold other_caps_times in *. des.
      inv CAP0. des. unfold caps in CAP0. des. clarify.
Qed.

Lemma other_caps_forget_prom_le
      mem0 mem1 mem2 prom (L: Loc.t -> Prop)
      (OTHERS: forall loc (SAT: L loc), Memory.latest_reserve loc prom mem0)
      (MLE: Memory.le prom mem0)
      (CLOSED: Memory.closed mem0)
      (RESERVEWF: Memory.reserve_wf prom mem0)
      (INHABITED: Memory.inhabited mem0)
      (CAP: Memory.cap prom mem0 mem2)
      (FORGET: forget_memory (other_latest_reserves_times L mem0 \2/ other_caps_times L mem0 mem1) mem1 mem2)
  :
    Memory.le prom mem1.
Proof.
  inv FORGET. ii.
  erewrite COMPLETE.
  - eapply Memory.cap_le in CAP; eauto.
  - ii. des.
    + unfold other_latest_reserves_times in *. des.
      inv RESERVE. des. clarify.
      dup LHS. eapply MLE in LHS0. clarify.
      eapply OTHERS in OTHER. unfold Memory.latest_reserve in OTHER.
      rewrite LHS in *. clarify.
    + unfold other_caps_times in *. des.
      inv CAP0. des. unfold caps in CAP0. des.
      eapply MLE in LHS; eauto. clarify.
Qed.

Lemma identity_mapped_view tm maxmap (f: Loc.t -> Time.t -> Time.t -> Prop)
      (TM: TimeMap.le tm maxmap)
      (IDENT: forall loc ts (TS: Time.le ts (maxmap loc)), f loc ts ts)
  :
    timemap_map f tm tm.
Proof.
  ii. eapply IDENT; eauto.
Qed.

Lemma other_collapsing_ident L mem loc maxts ts
      (MAX: Memory.max_full_ts mem loc maxts)
      (TS: Time.le ts maxts)
  :
    (other_collapsing L mem) loc ts ts.
Proof.
  i. destruct (classic (L loc)).
  - econs 2; eauto.
  - econs 1; eauto.
Qed.

Definition memory_reserve_wf mem := Memory.reserve_wf mem mem.

Lemma memory_reserve_wf_promise
      prom0 mem0 loc from to msg prom1 mem1 kind
      (PROMISE: Memory.promise prom0 mem0 loc from to msg prom1 mem1 kind)
      (RESERVE: memory_reserve_wf mem0)
  :
    memory_reserve_wf mem1.
Proof.
  inv PROMISE.
  - ii. erewrite Memory.add_o in GET; eauto. des_ifs.
    + ss; des; clarify. exploit RESERVE0; eauto.
      i. des. eapply Memory.add_get1 in x; eauto.
    + eapply RESERVE in GET; eauto. clear o. des.
      eapply Memory.add_get1 in GET; eauto.
  - ii. des. clarify. erewrite Memory.split_o in GET; eauto. des_ifs.
    + ss; des; clarify. eapply Memory.split_get0 in MEM. des.
      esplits; eauto.
    + eapply RESERVE in GET; eauto. clear o o0. des.
      eapply Memory.split_get1 in GET; eauto. des. esplits; eauto.
  - ii. erewrite Memory.lower_o in GET; eauto. des_ifs.
    + ss; des; clarify. inv MEM. inv LOWER. inv MSG_LE.
    + eapply RESERVE in GET; eauto. clear o. des.
      eapply Memory.lower_get1 in GET; eauto. des.
      inv MSG_LE. esplits; eauto.
  - ii. erewrite Memory.remove_o in GET; eauto. des_ifs. guardH o.
    dup MEM. eapply Memory.remove_get0 in MEM0. des.
    eapply RESERVE in GET; eauto. des. dup GET.
    eapply Memory.remove_get1 in GET2; eauto. ss. des; clarify.
    esplits; eauto.
Qed.

Lemma memory_reserve_wf_tstep lang (th0 th1: Thread.t lang) tf e
      (RESERVE: memory_reserve_wf th0.(Thread.memory))
      (STEP: Thread.step tf e th0 th1)
  :
    memory_reserve_wf th1.(Thread.memory).
Proof.
  inv STEP; inv STEP0; ss.
  - inv LOCAL. eapply memory_reserve_wf_promise; eauto.
  - inv LOCAL; eauto.
    + inv LOCAL0. inv WRITE.
      eapply memory_reserve_wf_promise; eauto.
    + inv LOCAL1. inv LOCAL2. inv WRITE.
      eapply memory_reserve_wf_promise; eauto.
Qed.

Lemma memory_reserve_wf_tsteps lang (th0 th1: Thread.t lang)
      (RESERVE: memory_reserve_wf th0.(Thread.memory))
      (STEP: rtc (tau (@Thread.step_allpf lang)) th0 th1)
  :
    memory_reserve_wf th1.(Thread.memory).
Proof.
  ginduction STEP; eauto.
  i. eapply IHSTEP; eauto. inv H. inv TSTEP.
  eapply memory_reserve_wf_tstep; eauto.
Qed.

Lemma memory_reserve_wf_init
  :
    memory_reserve_wf Memory.init.
Proof.
  ii. unfold Memory.get, Memory.init in *. ss.
  rewrite Cell.init_get in GET. des_ifs.
Qed.

Lemma memory_reserve_wf_configuration_step c0 c1 e tid
      (RESERVE: memory_reserve_wf c0.(Configuration.memory))
      (STEP: Configuration.step e tid c0 c1)
  :
    memory_reserve_wf c1.(Configuration.memory).
Proof.
  eapply configuration_step_equivalent in STEP. inv STEP. ss.
  eapply memory_reserve_wf_tstep in STEP0; eauto.
  eapply memory_reserve_wf_tsteps in STEPS; eauto.
Qed.

Lemma not_latest_reserve_le_max_full_ts loc mem ts to from msg
      (RESERVEWF : memory_reserve_wf mem)
      (INHABITED : Memory.inhabited mem)
      (MAX : Memory.max_full_ts mem loc ts)
      (GET: Memory.get loc to mem = Some (from, msg))
  :
    (<<TLE: Time.le to ts>>) \/
    ((<<TO: to = Memory.max_ts loc mem>>) /\
     (<<FROM: from = ts>>) /\
     (<<MSG: msg = Message.reserve>>)).
Proof.
  inv MAX. des.
  destruct msg.
  - left. eapply MAX0; eauto.
  - exploit RESERVEWF; eauto. i. des.
    destruct (TimeFacts.le_lt_dec to ts); auto.
    dup x. eapply MAX0 in x; eauto. destruct x.
    + exfalso. exploit memory_get_from_mon.
      { eapply GET0. }
      { eapply GET. }
      { auto. }
      i. eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt.
      * eapply x1.
      * eapply H.
    + unfold Time.eq in *. subst. right. esplits; eauto.
      setoid_rewrite GET0 in x0. clarify.
      dup GET. eapply Memory.max_ts_spec in GET1. des.
      destruct MAX; auto. exfalso.
      destruct msg.
      * eapply MAX0 in GET2. eapply Time.lt_strorder.
        eapply TimeFacts.lt_le_lt.
        { etrans.
          - eapply l.
          - eapply H. }
        { eauto. }
      * dup GET2. eapply RESERVEWF in GET2. des.
        eapply MAX0 in GET2.
        exploit memory_get_from_mon.
        { eapply GET. }
        { eapply GET1. }
        { eapply H. }
        i. eapply Time.lt_strorder.
        eapply TimeFacts.lt_le_lt.
        { eapply l. }
        { etrans.
          - eapply x0.
          - eapply Memory.get_ts in GET1. des; clarify. }
Qed.

Lemma max_full_ts_le_max_ts mem loc ts
      (MAX: Memory.max_full_ts mem loc ts)
  :
    Time.le ts (Memory.max_ts loc mem).
Proof.
  inv MAX. des.
  eapply Memory.max_ts_spec in GET. des; auto.
Qed.

Lemma max_full_ts_max_ts loc mem ts
      (RESERVEWF : memory_reserve_wf mem)
      (INHABITED : Memory.inhabited mem)
      (MAX : Memory.max_full_ts mem loc ts)
  :
    (<<FULL: ts = Memory.max_ts loc mem>>) \/
    ((<<TLT: Time.lt ts (Memory.max_ts loc mem)>>) /\
     (<<GET: Memory.get loc (Memory.max_ts loc mem) mem = Some (ts, Message.reserve)>>)).
Proof.
  dup MAX. inv MAX. des.
  eapply Memory.max_ts_spec in GET. des.
  dup GET0. eapply not_latest_reserve_le_max_full_ts in GET0; eauto.
  des; clarify.
  - left. eapply TimeFacts.antisym; eauto.
  - right. split; eauto. dup GET1.
    eapply memory_get_ts_strong in GET1. des; clarify.
    erewrite GET2 in *.
    erewrite INHABITED in GET0. clarify.
Qed.

Lemma other_collapsing_ident2 L mem maxts loc ts fts
      (MAX: Memory.max_full_ts mem loc maxts)
      (TS: Time.le fts maxts)
      (MAP: (other_collapsing L mem) loc ts fts)
  :
    ts = fts.
Proof.
  inv MAP; eauto.
  - exploit Memory.max_full_ts_inj.
    { eapply FULL. }
    { eapply MAX. }
    i. clarify. eapply TimeFacts.antisym; auto.
    eapply max_full_ts_le_max_ts in FULL; auto.
  - exfalso. eapply max_full_ts_le_max_ts in FULL. exfalso.
    eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
    + eapply DenseOrder.DenseOrder.incr_spec.
    + etrans.
      * eapply TS.
      * eapply max_full_ts_le_max_ts; eauto.
Qed.

Lemma other_collapsing_ident3 L mem maxts loc ts fts
      (RESERVEWF : memory_reserve_wf mem)
      (INHABITED : Memory.inhabited mem)
      (MAX: Memory.max_full_ts mem loc maxts)
      (TS: Time.lt ts maxts)
      (MAP: (other_collapsing L mem) loc ts fts)
  :
    ts = fts.
Proof.
  inv MAP; eauto.
  - exploit Memory.max_full_ts_inj.
    { eapply FULL. }
    { eapply MAX. }
    i. clarify. exfalso. eapply Time.lt_strorder; eauto.
  - exploit Memory.max_full_ts_inj.
    { eapply FULL. }
    { eapply MAX. }
    i. clarify. exfalso. eapply Time.lt_strorder; eauto.
Qed.

Lemma other_collapsing_timemap L mem tm
      (INHABITED: Memory.inhabited mem)
      (TM: Memory.closed_timemap tm mem)
  :
    timemap_map (other_collapsing L mem) tm tm.
Proof.
  exploit Memory.max_full_timemap_exists; eauto. intros [maxmap MAX].
  eapply identity_mapped_view.
  - eapply Memory.max_full_timemap_spec; eauto.
  - i. eapply other_collapsing_ident; eauto.
Qed.

Lemma other_collapsing_view L mem vw
      (INHABITED: Memory.inhabited mem)
      (VW: Memory.closed_view vw mem)
  :
    view_map (other_collapsing L mem) vw vw.
Proof.
  inv VW. econs.
  - eapply other_collapsing_timemap; eauto.
  - eapply other_collapsing_timemap; eauto.
Qed.

Lemma other_collapsing_opt_view L mem vw
      (INHABITED: Memory.inhabited mem)
      (VW: Memory.closed_opt_view vw mem)
  :
    opt_view_map (other_collapsing L mem) vw vw.
Proof.
  inv VW; econs.
  eapply other_collapsing_view; eauto.
Qed.

Lemma other_collapsing_message L mem msg
      (INHABITED: Memory.inhabited mem)
      (MSG: Memory.closed_message msg mem)
  :
    msg_map (other_collapsing L mem) msg msg.
Proof.
  inv MSG; econs.
  eapply other_collapsing_opt_view; eauto.
Qed.

Lemma other_collapsing_tview L mem vw
      (INHABITED: Memory.inhabited mem)
      (VW: TView.closed vw mem)
  :
    tview_map (other_collapsing L mem) vw vw.
Proof.
  inv VW. econs.
  - i. eapply other_collapsing_view; eauto.
  - eapply other_collapsing_view; eauto.
  - eapply other_collapsing_view; eauto.
Qed.


Lemma other_collapsing_promises (L: Loc.t -> Prop) mem prom
      (MLE: Memory.le prom mem)
      (CLOSED: Memory.closed mem)
      (RESERVEWF: memory_reserve_wf mem)
      (INHABITED: Memory.inhabited mem)
      (OTHERS: forall loc (SAT: L loc), Memory.latest_reserve loc prom mem)
  :
    promises_map (other_collapsing L mem) prom prom.
Proof.
  exploit Memory.max_full_timemap_exists; eauto. intros [tm MAX].
  dup CLOSED. inv CLOSED0. econs.
  - i. dup GET. eapply MLE in GET0. eapply CLOSED1 in GET0. des.
    exists to, from, msg.
    destruct (classic (L loc)).
    + dup GET. eapply MLE in GET0.
      eapply not_latest_reserve_le_max_full_ts in GET0; eauto.
      eapply or_strengthen in GET0. des; clarify.
      * esplits; eauto.
        { ii. unfold collapsed in *. des.
          eapply other_collapsing_ident3 in MAP0; eauto; cycle 1.
          { eapply TimeFacts.lt_le_lt; eauto. } clarify.
          assert (TO: to = ft).
          { destruct TLE.
            - eapply other_collapsing_ident3 in MAP1; eauto.
            - unfold Time.eq in *. clarify. inv MAP1; clarify.
              + exfalso. eapply Time.lt_strorder.
                eapply TimeFacts.lt_le_lt.
                * eapply TLE0.
                * eapply max_full_ts_le_max_ts; eauto.
              + exfalso. eapply Time.lt_strorder.
                eapply TimeFacts.lt_le_lt.
                * etrans.
                  { eapply Time.incr_spec. }
                  { eapply TLE0. }
                * eapply max_full_ts_le_max_ts; eauto. }
          clarify. eapply Time.lt_strorder; eauto. }
        { econs 2; eauto. }
        { eapply other_collapsing_message; eauto. }
      * exfalso. exploit OTHERS; eauto.
        unfold Memory.latest_reserve. rewrite GET. auto.
    + splits; auto.
      * ii. unfold collapsed in *. des.
        inv MAP0; clarify. inv MAP1; clarify.
        eapply Time.lt_strorder. eauto.
      * econs 1; eauto.
      * eapply other_collapsing_message; eauto.

  - i. exists fto, ffrom, fmsg.
    destruct (classic (L loc)).
    + dup GET. eapply MLE in GET.
      eapply not_latest_reserve_le_max_full_ts in GET; eauto.
      des; clarify.
      * splits; auto.
        { eapply other_collapsing_ident; eauto. }
        { eapply other_collapsing_ident; eauto.
          etrans; eauto.
          eapply memory_get_ts_strong in GET0. des; clarify.
          { refl. }
          { left. auto. } }
      * exfalso. exploit OTHERS; eauto.
        unfold Memory.latest_reserve. rewrite GET0. auto.
    + splits; auto.
      * econs 1; eauto.
      * econs 1; eauto.
Qed.

Inductive self_collapsing (L: Loc.t -> Prop)
          (mem: Memory.t): Loc.t -> Time.t -> Time.t -> Prop :=
| self_collapsing_not_in
    loc t
    (NSAT: ~ L loc)
  :
    self_collapsing L mem loc t t
| self_collapsing_in_memory
    loc t
    (SAT: L loc)
    (TLE: Time.le t (Memory.max_ts loc mem))
  :
    self_collapsing L mem loc t t
| self_collapsing_cap
    loc t max
    (SAT: L loc)
    (FULL: max = Memory.max_ts loc mem)
    (CAP: t = Time.incr (Memory.max_ts loc mem))
  :
    self_collapsing L mem loc max t
| self_collapsing_outer_memory
    loc t
    (SAT: L loc)
    (TLE: Time.lt (Time.incr (Memory.max_ts loc mem)) t)
  :
    self_collapsing L mem loc t t
.

Lemma other_collapsing_memory
      mem0 mem1 mem2 prom (L: Loc.t -> Prop)
      (MLE: Memory.le prom mem0)
      (CLOSED: Memory.closed mem0)
      (RESERVEWF: Memory.reserve_wf prom mem0)
      (INHABITED: Memory.inhabited mem0)
      (OTHERS: forall loc (SAT: L loc), Memory.latest_reserve loc prom mem0)
      (CAP: Memory.cap prom mem0 mem1)
      (FORGET: forget_memory (other_latest_reserves_times L mem0 \2/ other_caps_times L mem0 mem1) mem2 mem1)
  :
    memory_map (other_collapsing L mem0) mem2 mem1.
Proof.
  exploit Memory.max_full_timemap_exists; eauto. intros [tm MAX].
  dup CLOSED. inv CLOSED0. econs.
  - i. destruct (classic (L loc)).
    + dup GET. eapply forget_memory_get in GET0; eauto. des.
Admitted.

(* Inductive diff_after_promises (caps: Loc.t -> option (Time.t * Time.t * Message.t)) *)
(*           (prom mem0 mem1: Memory.t): Prop := *)
(* | diff_after_promises_intro *)
(*     (MLE: Memory.le mem0 mem1) *)
(*     (DIFF: forall loc to from msg *)
(*                   (GET: Memory.get loc to mem1 = Some (from, msg)) *)
(*                   (NONE: Memory.get loc to mem0 = None), *)
(*         caps loc = Some (from, to, msg)) *)
(*     (CAPS: forall loc to from msg *)
(*                   (CAPS: caps loc = Some (from, to, msg)), *)
(*         exists  *)
(*           (<<PROMNONE: Memory.get prom loc to = None>>) /\ *)
(*           (<<GETTGT: Memory.get mem1 loc to = Some (from, msg)>>) /\ *)
(*           (<<GETPROM:  *)

(*     ) *)
(* . *)


Inductive diff_after_promises (caps: Loc.t -> option (Time.t * Time.t * Message.t))
          (prom mem0 mem1: Memory.t): Prop :=
| diff_after_promises_intro
    (MLE: Memory.le mem0 mem1)
    (DIFF: forall loc to from msg
                  (GET: Memory.get loc to mem1 = Some (from, msg))
                  (NONE: Memory.get loc to mem0 = None),
        (<<CAP: caps loc = Some (from, to, msg)>>) /\
        (exists from' to' val released,
            (<<PROM: Memory.get loc to' prom = Some (from', Message.full val released)>>) /\
            (<<TLE: Time.le to' from>>)))
.


Inductive add_cap (caps: Loc.t -> option (Time.t * Time.t * Message.t)): Memory.t -> Memory.t -> Prop :=
| add_cap_refl mem0
  :
    add_cap caps mem0 mem0
| add_cap_add
    loc from to msg mem0 mem1
    (CAP: caps loc = Some (from, to, msg))
    (ADD: Memory.add mem0 loc from to msg mem1)
  :
    add_cap caps mem0 mem1
.
Hint Constructors add_cap.

Lemma memory_op_le mem_src0 mem_tgt0 loc from to msg mem_src1 mem_tgt1 kind
      (MLE: Memory.le mem_src0 mem_tgt0)
      (OPSRC: Memory.op mem_src0 loc from to msg mem_src1 kind)
      (OPTGT: Memory.op mem_tgt0 loc from to msg mem_tgt1 kind)
  :
    Memory.le mem_src1 mem_tgt1.
Proof.
  inv OPSRC; inv OPTGT.
  - ii. erewrite Memory.add_o in LHS; eauto.
    erewrite Memory.add_o; cycle 1; eauto. des_ifs; eauto.
  - ii. erewrite Memory.split_o in LHS; eauto.
    erewrite Memory.split_o; cycle 1; eauto. des_ifs; eauto.
  - ii. erewrite Memory.lower_o in LHS; eauto.
    erewrite Memory.lower_o; cycle 1; eauto. des_ifs; eauto.
  - ii. erewrite Memory.remove_o in LHS; eauto.
    erewrite Memory.remove_o; cycle 1; eauto. des_ifs; eauto.
Qed.

Lemma diff_after_promise_promise caps prom0 mem_src0 mem_tgt0
      loc from to msg kind prom1 mem_tgt1
      (DIFF: diff_after_promises caps prom0 mem_src0 mem_tgt0)
      (MLE: Memory.le prom0 mem_src0)
      (PROMISE: Memory.promise prom0 mem_tgt0 loc from to msg prom1 mem_tgt1 kind)
      (PF: (Memory.op_kind_is_lower_full kind && Message.is_released_none msg
            || Memory.op_kind_is_cancel kind)%bool)
  :
    exists mem_src1,
      (<<PROMISE: Memory.promise prom0 mem_src0 loc from to msg prom1 mem_src1 kind>>) /\
      (<<DIFF: diff_after_promises caps prom1 mem_src1 mem_tgt1>>).
Proof.
  inv DIFF. inv PROMISE; ss.
  - unfold Message.is_released_none in *. des_ifs. des. clarify.
    dup MEM. eapply lower_succeed_wf in MEM0. des.
    exploit Memory.lower_exists.
    { eapply MLE. eapply lower_succeed_wf in PROMISES. des. eapply GET0. }
    { eauto. }
    { eauto. }
    { eauto. }
    i. des. exists mem2. split.
    + econs; eauto.
    + econs.
      * eapply memory_op_le; eauto.
      * i. erewrite Memory.lower_o in GET0; eauto.
        erewrite Memory.lower_o in NONE; eauto. des_ifs. guardH o.
        exploit DIFF0; eauto. i. des.
        eapply Memory.lower_get1 in PROM; eauto. des. inv MSG_LE0.
        esplits; eauto.
  - exploit Memory.remove_exists.
    { eapply Memory.remove_get0 in PROMISES. des.
      eapply MLE. eauto. }
    i. des. exists mem2. split.
    + econs; eauto.
    + econs.
      * eapply memory_op_le; eauto.
      * i. erewrite Memory.remove_o in GET; eauto.
        erewrite Memory.remove_o in NONE; eauto. des_ifs. guardH o.
        exploit DIFF0; eauto. i. des. splits; auto.
        exists from', to', val, released. splits; auto.
        erewrite Memory.remove_o; eauto. des_ifs. ss. des; clarify.
        eapply Memory.remove_get0 in PROMISES. des. clarify.
Qed.


Lemma diff_after_promise_write caps prom0 mem_src0 mem_tgt0
      loc from to val released kind prom1 mem_tgt1
      (DIFF: diff_after_promises caps prom0 mem_src0 mem_tgt0)
      (MLE: Memory.le prom0 mem_src0)
      (WRITE: Memory.write prom0 mem_tgt0 loc from to val released prom1 mem_tgt1 kind)
  :
    exists mem_src1' mem_src1,
      (<<WRITE: Memory.write prom0 mem_src0 loc from to val released prom1 mem_src1' kind>>) /\
      (<<ADD: add_cap caps mem_src1' mem_src1>>) /\
      (<<DIFF: diff_after_promises caps prom1 mem_src1 mem_tgt1>>).
Proof.
  inv DIFF. inv WRITE; ss. inv PROMISE; ss.
  - exploit Memory.add_exists_le.
    { eapply MLE0. }
    { eapply MEM. }
    intros [mem_src' ADD]. exists mem_src', mem_src'. splits; auto.
    + econs; eauto. econs; eauto. i. clarify.
    + assert (PROM: prom1 = prom0).
      { eapply MemoryFacts.MemoryFacts.add_remove_eq; eauto. } clarify.
      econs.
      * eapply memory_op_le; eauto.
      * i. erewrite Memory.add_o in GET; eauto.
        erewrite Memory.add_o in NONE; eauto. des_ifs. guardH o.
        exploit DIFF0; eauto.
  - exploit Memory.split_exists_le.
    { eapply MLE. }
    { eapply PROMISES. }
    intros [mem_src' SPLIT]. exists mem_src', mem_src'. splits; auto.
    + econs; eauto.
    + econs.
      * eapply memory_op_le; eauto.
      * i. erewrite Memory.split_o in GET; eauto.
        erewrite Memory.split_o in NONE; eauto. des_ifs. guardH o. guardH o0.
        exploit DIFF0; eauto. i. des. splits; auto.
        dup PROM. eapply Memory.split_get1 in PROM0; eauto.
        des. eapply Memory.remove_get1 in GET2; eauto. des; clarify.
        { eapply Memory.split_get0 in PROMISES. des. clarify. }
        { esplits; eauto. }

  - des. clarify.
    exploit Memory.lower_exists_le.
    { eapply MLE. }
    { eapply PROMISES. }
    intros [mem_src' LOWER]. exists mem_src'.

    destruct (classic (exists from' to' val released,
                          (<< Memory.get loc to' prom0 = Some (from', Message.full val released) >> /\
                          << Time.le to' from >>)


    mem_src'. splits; auto.
    + econs; eauto.
    + econs.
      * eapply memory_op_le; eauto.
      * i. erewrite Memory.split_o in GET; eauto.
        erewrite Memory.split_o in NONE; eauto. des_ifs. guardH o. guardH o0.
        exploit DIFF0; eauto. i. des. splits; auto.
        dup PROM. eapply Memory.split_get1 in PROM0; eauto.
        des. eapply Memory.remove_get1 in GET2; eauto. des; clarify.
        { eapply Memory.split_get0 in PROMISES. des. clarify. }
        { esplits; eauto. }


        esplits; eauto.
        erewrite Memory.

        exists f', val0, released0.
        exists





    admit.
  -



        i. des. splits; auto.
        exists from', to', val, released. splits; auto.
        erewrite Memory.remove_o; eauto. des_ifs. ss. des; clarify.
        eapply Memory.remove_get0 in PROMISES. des. clarify.
Memory.le


        ; eauto.


    i. destruc des. exists promises0. e

      Memory


    unfold Message.is_released_none in *. des_ifs. des. clarify.
    dup MEM. eapply lower_succeed_wf in MEM0. des.
    exploit Memory.lower_exists.
    { eapply MLE. eapply lower_succeed_wf in PROMISES. des. eapply GET0. }
    { eauto. }
    { eauto. }
    { eauto. }
    i. des. exists mem2. split.
    + econs; eauto.
    + econs.
      * ii. erewrite Memory.lower_o in LHS; eauto.
        erewrite Memory.lower_o; cycle 1; eauto. des_ifs. eauto.
      * i. erewrite Memory.lower_o in GET0; eauto.
        erewrite Memory.lower_o in NONE; eauto. des_ifs. guardH o.
        exploit DIFF0; eauto. i. des.
        eapply Memory.lower_get1 in PROM; eauto. des. inv MSG_LE0.
        esplits; eauto.
  - exploit Memory.remove_exists.
    { eapply Memory.remove_get0 in PROMISES. des.
      eapply MLE. eauto. }
    i. des. exists mem2. split.
    + econs; eauto.
    + econs.
      * ii. erewrite Memory.remove_o in LHS; eauto.
        erewrite Memory.remove_o; cycle 1; eauto. des_ifs. eauto.
      * i. erewrite Memory.remove_o in GET; eauto.
        erewrite Memory.remove_o in NONE; eauto. des_ifs. guardH o.
        exploit DIFF0; eauto. i. des. splits; auto.
        exists from', to', val, released. splits; auto.
        erewrite Memory.remove_o; eauto. des_ifs. ss. des; clarify.
        eapply Memory.remove_get0 in PROMISES. des. clarify.
Qed.

Memory.write

  add => ez
  split => maybe ez
  lower

        des_ifs.
        { ss. des; clarify.

          in GET

        eapply Memory.remove_get1 in PROM; eauto. des; clarify.
        { splits; eauto.

          admit. }
        {

        inv MSG_LE0.
        esplits; eauto.



      eauto.


        eauto.
        des_ifs.
        { ss. des; clarify.

    assert (GETSRC: Memory.get loc to mem_src0 = Some (from, Message.full val1 released0)).
    { destruct (Memory.get loc to mem_src0) eqn:GET0.
      - dup GET0. destruct p. eapply MLE in GET0. clarify.
      - exploit DIFF0; eauto. i. des.


      inv DIFF.






Lemma diff_after_promises_read caps P lang
      th_src th_tgt th_tgt' st st' v v' prom prom' sc sc'
      mem_src mem_tgt mem_tgt' e
      (STEP: (@pred_step P lang) e th_tgt th_tgt')
      (PROMISEFREE: P <1= promise_free)
      (TH_SRC: th_src = Thread.mk lang st (Local.mk v prom) sc mem_src)
      (TH_TGT0: th_tgt = Thread.mk lang st (Local.mk v prom) sc mem_tgt)
      (TH_TGT1: th_tgt' = Thread.mk lang st' (Local.mk v' prom') sc' mem_tgt')
      (DIFF: diff_after_promises prom mem_src mem_tgt caps)
  :
    exists mem_src' mem_src'',
      (<<STEP: (@pred_step P lang)
                 e th_src
                 (Thread.mk lang st' (Local.mk v' prom') sc' mem_src')>>) /\
      (<<ADD: add_cap caps mem_src' mem_src''>>) /\
      (<<DIFF: diff_after_promises prom' mem_src'' mem_tgt' caps>>)
.
Proof.
  inv STEP. dup SAT. eapply PROMISEFREE in SAT0.
  inv STEP0. inv STEP.
  - inv STEP0. inv LOCAL. ss. clarify. inv PROMISE; ss.
    + unfold Message.is_released_none in *. des_ifs. des. clarify.


          diff

          Memory.promise


      Thread.promise_step

(Memory.op_kind_is_lower_full kind && Message.is_released_none msg
                          || Memory.op_kind_is_cancel kind)%bool

      Memory.promise

      lower_succeed_wf


      destruct msg0; ss.

      destruct msg; ss.

      unfold orb in *. destruct des_ifs. ss. unfo

    admit.
  - inv STEP0. inv LOCAL; ss.
    + exists mem_src, mem_src. splits; eauto.
      * econs; eauto. econs; eauto.
      * econs 1.
    + dup LOCAL0. inv LOCAL1. ss. clarify.
      exists mem_src, mem_src. splits; eauto.
      * econs; eauto. econs; eauto. econs 2; eauto. econs; eauto.
        econs; eauto. econs; eauto. instantiate (1:=from).


      *

      inv LOCAL0. ss. clarify.


promise_consistent_promise_read


Lemma diff_after_promises_step caps P lang
      th_src th_tgt th_tgt' st st' v v' prom prom' sc sc'
      mem_src mem_tgt mem_tgt' e
      (STEP: (@pred_step P lang) e th_tgt th_tgt')
      (NOSC: P <1= promise_free)
      (TH_SRC: th_src = Thread.mk lang st (Local.mk v prom) sc mem_src)
      (TH_TGT0: th_tgt = Thread.mk lang st (Local.mk v prom) sc mem_tgt)
      (TH_TGT1: th_tgt' = Thread.mk lang st' (Local.mk v' prom') sc' mem_tgt')
      (DIFF: diff_after_promises prom mem_src mem_tgt caps)
  :
    exists mem_src' mem_src'',
      (<<STEP: (@pred_step P lang)
                 e th_src
                 (Thread.mk lang st' (Local.mk v' prom') sc' mem_src')>>) /\
      (<<ADD: add_cap caps mem_src' mem_src''>>) /\
      (<<DIFF: diff_after_promises prom' mem_src'' mem_tgt' caps>>)
.
Proof.
  inv STEP. inv STEP0. inv STEP.
  - admit.
  - inv STEP0. inv LOCAL; ss.
    + exists mem_src, mem_src. splits; eauto.
      * econs; eauto. econs; eauto.
      * econs 1.
    +

Memory.add

  add_succeed_wf

               Thread.step pf e (Thread.mk st lc0 sc0 mem0)

                        (STEP:



         (CONSISTENT: Local.promise_consistent th1.(Thread.local))

                        Thread.step




      dup FORGET.

      admit.

    + exists to, from, msg, msg. esplits; eauto.
      * econs 1; eauto.
      * eapply other_collapsing_message; eauto.
        eapply CLOSED1.

               econs 1; eauto.



    admit.

  - i. exists fto, ffrom, fmsg.
    destruct (classic (L loc)).
    + splits; auto.
      * econs 2; eauto.
      * inv FORGET. erewrite COMPLETE; eauto.
        ii. des.
        { unfold other_latest_reserves_times, other_latest_reserves in H0.
          des. clarify. }
        { unfold other_caps_times, other_caps in H0.
          des. clarify. }
      * econs 1; eauto.


      admit.
    + splits; auto.
      * econs 1; eauto.
      * inv FORGET. erewrite COMPLETE; eauto.
        ii. des.
        { unfold other_latest_reserves_times, other_latest_reserves in H0.
          des. clarify. }
        { unfold other_caps_times, other_caps in H0.
          des. clarify. }
      * econs 1; eauto.


        econs 1; eauto.


    + dup GET. eapply MLE in GET.
      eapply not_latest_reserve_le_max_full_ts in GET; eauto.
      des; clarify.
      * splits; auto.
        { eapply other_collapsing_ident; eauto. }
        { eapply other_collapsing_ident; eauto.
          etrans; eauto.
          eapply memory_get_ts_strong in GET0. des; clarify.
          { refl. }
          { left. auto. } }
      * exfalso. exploit OTHERS; eauto.
        unfold Memory.latest_reserve. rewrite GET0. auto.
    + splits; auto.
      * econs 1; eauto.
      * econs 1; eauto.


  - i. dup GET. eapply CLOSED1 in GET0. des.
    exists to, from, msg.
    destruct (classic (L loc)).
    + dup GET. eapply MLE in GET0.
      eapply not_latest_reserve_le_max_full_ts in GET0; eauto.
      eapply or_strengthen in GET0. des; clarify.
      * esplits; eauto.
        { ii. unfold collapsed in *. des.
          eapply other_collapsing_ident3 in MAP0; eauto; cycle 1.
          { eapply TimeFacts.lt_le_lt; eauto. } clarify.
          assert (TO: to = ft).
          { destruct TLE.
            - eapply other_collapsing_ident3 in MAP1; eauto.
            - unfold Time.eq in *. clarify. inv MAP1; clarify.
              + exfalso. eapply Time.lt_strorder.
                eapply TimeFacts.lt_le_lt.
                * eapply TLE0.
                * eapply max_full_ts_le_max_ts; eauto.
              + exfalso. eapply Time.lt_strorder.
                eapply TimeFacts.lt_le_lt.
                * etrans.
                  { eapply Time.incr_spec. }
                  { eapply TLE0. }
                * eapply max_full_ts_le_max_ts; eauto. }
          clarify. eapply Time.lt_strorder; eauto. }
        { econs 2; eauto. }
        { eapply other_collapsing_message; eauto. }
      * exfalso. exploit OTHERS; eauto.
        unfold Memory.latest_reserve. rewrite GET. auto.
    + splits; auto.
      * ii. unfold collapsed in *. des.
        inv MAP0; clarify. inv MAP1; clarify.
        eapply Time.lt_strorder. eauto.
      * econs 1; eauto.
      * eapply other_collapsing_message; eauto.

  - i. exists fto, ffrom, fmsg.
    destruct (classic (L loc)).
    + dup GET. eapply MLE in GET.
      eapply not_latest_reserve_le_max_full_ts in GET; eauto.
      des; clarify.
      * splits; auto.
        { eapply other_collapsing_ident; eauto. }
        { eapply other_collapsing_ident; eauto.
          etrans; eauto.
          eapply memory_get_ts_strong in GET0. des; clarify.
          { refl. }
          { left. auto. } }
      * exfalso. exploit OTHERS; eauto.
        unfold Memory.latest_reserve. rewrite GET0. auto.
    + splits; auto.
      * econs 1; eauto.
      * econs 1; eauto.
Qed.


  exploit Memory.max_full_timemap_exists; eauto. intros [tm MAX].
  dup FORGET. inv FORGET. econs.
  - i. dup GET. eapply forget_memory_get in GET; eauto.
    ss. des. apply not_or_and in NOT. des.
    exists to, from, msg, msg. esplits.
    + destruct (classic (L loc)).
      * econs 2; eauto. specialize (MAX loc). inv MAX.
        destruct msg as [val released|].
        { eapply MAX0; eauto.


        exploit Memory.max_full_ts_exists; eauto.
        instantiate (1:=loc). i. des. econs 2; eauto. inv x0.
        destruct msg as [val released|].
        {

          eapply caps_max_view in


          admit

          eapply MAX in GET1.

        inv x0.



        x

        { eauto

        econs 2; eauto.


        admit.
      * econs 1; eauto.
    + destruct msg; econs.
      destruct released; econs.

               econs.



              r
    ss. des.
    destruct (classic (other_latest_reserves_times L mem0 loc to \/ other_caps_times L mem0 mem1 loc to)); cycle 1.




    forget_memory


    Memory.cap

->


Definition other_latest_reserves_times (L: Loc.t -> Prop)
           (mem: Memory.t) (loc: Loc.t) (to: Time.t) :=
  exists from,
    (<<RESERVE: other_latest_reserves L mem loc to from>>).

Definition other_caps_times (L: Loc.t -> Prop)
           (mem0 mem1: Memory.t) (loc: Loc.t) (to: Time.t) :=
  exists from,
    (<<CAP: other_caps L mem0 mem1 loc to from>>).



Inductive other_collapsing (L: Loc.t -> Prop)
          (mem0 mem1: Memory.t): Loc.t -> Time.t -> Time.t -> Prop :=
| other_collapsing_not_in
    loc t
    (NSAT: ~ L loc)
  :
    other_collapsing L mem0 mem1 loc t t
| other_collapsing_in_memory
    loc t max
    (SAT: L loc)
    (MAX: Memory.max_full_ts mem0 loc max)
    (TLE: Time.le t max)
  :
    other_collapsing L mem0 mem1 loc t t
| other_collapsing_in_memory
    loc t max
    (SAT: L loc)
    (MAX: Memory.max_full_ts mem0 loc max)
    (TLE: Time.le t max)
  :
    other_collapsing L mem0 mem1 loc t t
.




           Variable f: Loc.t -> Time.t -> Time.t -> Prop.
  Hypothesis map_le:
    forall loc t0 t1 ft0 ft1
           (MAP0: f loc t0 ft0)
           (MAP1: f loc t1 ft1),
      Time.le t0 t1 -> Time.le ft0 ft1.
  Hypothesis map_bot:
    forall loc,
      f loc Time.bot Time.bot.
  Hypothesis map_eq:
    forall loc to ft0 ft1
           (MAP0: f loc to ft0)
           (MAP1: f loc to ft1),
      ft0 = ft1.





Definition other_caps (L: Loc.t -> Prop)
           (mem0 mem1: Memory.t) (loc: Loc.t) (to: Time.t) (from: Time.t) :=
  (<<FULL: Memory.max_full_ts mem0 loc from>>) /\
  (<<LATEST: exists from0 val released,
      (<<CAP: caps mem0 mem1 loc to from0 (Message.full val released)>>)>>) /\
  (<<OTHER: L loc>>)
.




  Lemma cell_finite_sound_exists c
    :
      exists dom,
        (<<COMPLETE: forall to,
            (List.In to dom <-> exists from msg,
                (<<GET: Cell.get to c = Some (from, msg)>>))>>).



 (mem0 prom : Memory.t) (l : Loc.t) (t from : Time.t) (msg : Message.t)


  (<<LATEST: to = Memory.max_ts loc mem>>) /\
  (<<RESERVE: exists from, (<<GET: Memory.get loc to mem = Some (from, Message.reserve)>>)>>) /\
  (<<OTHER: L loc>>)
.

Memory.max_full_ts

Memory.get_

     Memory.get loc (Memory.max_ts loc mem) promises>>
  (<<LATEST: Memory.get loc (Memory.max_ts loc mem) promises>>



  forall mem1 (CAP: Memory.cap prom mem0 mem1),
    (<<GET0: Memory.get l t mem0 = None>>) /\
    (<<GET1: Memory.get l t mem1 = Some (from, msg)>>).

Memory.cap

                (forall (loc : Loc.t) (val : Const.t) (view : View.t),
                 Memory.latest_reserve loc promises mem1 ->
                 Memory.latest_val loc mem1 val ->
                 Memory.max_full_view mem1 view ->
                 Memory.get loc (Time.incr (Memory.max_ts loc mem1)) mem2 =
                 Some (Memory.max_ts loc mem1, Message.full val (Some view))) ->


Definition caps (mem0 prom : Memory.t) (l : Loc.t) (t from : Time.t) (msg : Message.t) :=
  forall mem1 (CAP: Memory.cap prom mem0 mem1),
    (<<GET0: Memory.get l t mem0 = None>>) /\
    (<<GET1: Memory.get l t mem1 = Some (from, msg)>>).

Definition partiral_cap (L: Loc.t -> Prop)
      prom mem1 mem2




Memory.cap

Lemma collapsing_other_cap
      (






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



Lemma steps_write_not_in P lang (th0 th1: Thread.t lang)




Lemma collapse_other_cappe

Lemma

Lemma my_



Lemma step_wirte_not_in lang (th_tgt th_tgt': Thread.t lang) e_tgt pf
      (STEP: Thread.step pf e_tgt th_tgt th_tgt')
  :
    write_not_in (unchangables th_tgt.(Thread.memory) th_tgt.(Thread.local).(Local.promises))
                 e_tgt.
Proof.
  unfold unchangables. inv STEP.
  - inv STEP0; ss.
  - inv STEP0; ss. inv LOCAL; ss.
    + inv LOCAL0. ii. exploit step_wirte_not_in_write; eauto.
    + inv LOCAL1. inv LOCAL2. ss. ii. exploit step_wirte_not_in_write; eauto.
Qed.


Definition pf_consistent_strong lang (e0:Thread.t lcapped intrang): Prop :=
  forall mem1 sc1
         (CAP: Memory.cap e0.(Thread.local).(Local.promises) e0.(Thread.memory) mem1),
  exists e1,
    (<<STEPS0: rtc (tau (@pred_step is_cancel lang)) (Thread.mk _ e0.(Thread.state) e0.(Thread.local) sc1 mem1) e1>>) /\
    (<<NORESERVE: no_reserves e1.(Thread.local).(Local.promises)>>) /\
    exists e2,
      (<<STEPS1: rtc (tau (@pred_step ((promise_free /1\ (fun e => ~ is_cancel e) /1\ no_acq_read_msgs (caps_loc e0.(Thread.memory) e0.(Thread.local).(Local.promises))) /1\ no_sc) lang)) e1 e2>>) /\
      ((<<FAILURE: Local.failure_step e2.(Thread.local)>>) \/
       (<<PROMISES: e2.(Thread.local).(Local.promises) = Memory.bot>>)).
