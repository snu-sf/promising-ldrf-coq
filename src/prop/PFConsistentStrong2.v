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


Section TEVENTMAP.

  Inductive tevent_map_weak (f: Loc.t -> Time.t -> Time.t -> Prop)
  : ThreadEvent.t -> ThreadEvent.t -> Prop :=
  | tevent_map_weak_promise
      loc from ffrom to fto msg fmsg kind fkind
      (FROM: f loc from ffrom)
      (TO: f loc to fto)
    :
      tevent_map_weak
        f
        (ThreadEvent.promise loc ffrom fto fmsg fkind)
        (ThreadEvent.promise loc from to msg kind)
  | tevent_map_weak_read
      loc to fto val released freleased ordr
      (TO: f loc to fto)
    :
      tevent_map_weak
        f
        (ThreadEvent.read loc fto val freleased ordr)
        (ThreadEvent.read loc to val released ordr)
  | tevent_map_weak_write
      loc from ffrom to fto val released freleased ordw
      (FROM: f loc from ffrom)
      (TO: f loc to fto)
    :
      tevent_map_weak
        f
        (ThreadEvent.write loc ffrom fto val freleased ordw)
        (ThreadEvent.write loc from to val released ordw)
  | tevent_map_weak_update
      loc from ffrom to fto valr valw releasedr freleasedr
      releasedw freleasedw ordr ordw
      (FROM: f loc from ffrom)
      (TO: f loc to fto)
    :
      tevent_map_weak
        f
        (ThreadEvent.update loc ffrom fto valr valw freleasedr freleasedw ordr ordw)
        (ThreadEvent.update loc from to valr valw releasedr releasedw ordr ordw)
  | tevent_map_weak_fence
      or ow
    :
      tevent_map_weak
        f
        (ThreadEvent.fence or ow)
        (ThreadEvent.fence or ow)
  | tevent_map_weak_syscall
      e
    :
      tevent_map_weak
        f
        (ThreadEvent.syscall e)
        (ThreadEvent.syscall e)
  | tevent_map_weak_silent
    :
      tevent_map_weak
        f
        (ThreadEvent.silent)
        (ThreadEvent.silent)
  | tevent_map_weak_failure
    :
      tevent_map_weak
        f
        (ThreadEvent.failure)
        (ThreadEvent.failure)
  .
  Hint Constructors tevent_map_weak.

  Lemma tevent_map_tevent_map_weak f e fe
        (EVENT: tevent_map f e fe)
    :
      tevent_map_weak f e fe.
  Proof.
    inv EVENT; eauto.
  Qed.

  Lemma tevent_map_weak_compose (f0 f1 f2: Loc.t -> Time.t -> Time.t -> Prop) e0 e1 e2
        (EVENT0: tevent_map_weak f0 e1 e0)
        (EVENT1: tevent_map_weak f1 e2 e1)
        (COMPOSE: forall loc ts0 ts1 ts2 (MAP0: f0 loc ts0 ts1) (MAP1: f1 loc ts1 ts2),
            f2 loc ts0 ts2)
    :
      tevent_map_weak f2 e2 e0.
  Proof.
    inv EVENT0; inv EVENT1; econs; eauto.
  Qed.

  Lemma tevent_map_weak_rev (f0 f1: Loc.t -> Time.t -> Time.t -> Prop) e0 e1
        (EVENT: tevent_map_weak f0 e1 e0)
        (REV: forall loc ts0 ts1 (MAP: f0 loc ts0 ts1), f1 loc ts1 ts0)
    :
      tevent_map_weak f1 e0 e1.
  Proof.
    inv EVENT; econs; eauto.
  Qed.

End TEVENTMAP.

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


Inductive unattachable (mem: Memory.t) (loc: Loc.t) (ts: Time.t): Prop :=
| unattachable_intro
    to msg
    (MSG: Memory.get loc to mem = Some (ts, msg))
    (EMPTY: Memory.get loc ts mem = None)
.

Lemma lower_unattachable mem1 mem0 loc from to msg1 msg2
      (LOWER: Memory.lower mem0 loc from to msg1 msg2 mem1)
  :
    unattachable mem1 = unattachable mem0.
Proof.
  extensionality loc0. extensionality ts0.
  exploit Memory.lower_get0; eauto. i. des.
  apply Coq.Logic.PropExtensionality.propositional_extensionality. split; i.
  { inv H. erewrite Memory.lower_o in EMPTY; eauto.
    erewrite Memory.lower_o in MSG; eauto. des_ifs.
    { ss. des; clarify. econs; eauto. }
    { econs; eauto. }
  }
  { inv H. eapply Memory.lower_get1 in MSG; eauto. des. econs; eauto.
    erewrite Memory.lower_o; eauto. des_ifs. ss. des. clarify. }
Qed.

Lemma split_unattachable mem1 mem0 loc ts1 ts2 ts3 msg2 msg3
      (SPLIT: Memory.split mem0 loc ts1 ts2 ts3 msg2 msg3 mem1)
  :
    unattachable mem1 = unattachable mem0.
Proof.
  extensionality loc0. extensionality ts0.
  exploit split_succeed_wf; eauto. i. des.
  exploit Memory.split_get0; eauto. i. des.
  apply Coq.Logic.PropExtensionality.propositional_extensionality. split; i.
  { inv H. erewrite Memory.split_o in MSG; eauto.
    erewrite Memory.split_o in EMPTY; eauto. des_ifs.
    { ss. des; clarify. econs; eauto. }
    { ss. des; clarify. }
    { econs; eauto. }
  }
  { inv H. generalize (Memory.split_o loc0 to SPLIT). intros MSG0. des_ifs.
    { ss. des; clarify. }
    { ss. des; clarify. econs; eauto.
      erewrite Memory.split_o; eauto. des_ifs.
      { ss. des; clarify. timetac. }
      { ss. des; clarify. }
    }
    { econs.
      { instantiate (2:=to).
        erewrite Memory.split_o; eauto. des_ifs.
        { ss. des; clarify. }
        { ss. des; clarify. }
        { eauto. }
      }
      { erewrite Memory.split_o; eauto. des_ifs.
        { ss. des; clarify. exfalso.
          exploit memory_get_from_inj.
          { eapply GET3. }
          { erewrite MSG0. eauto. }
          i. des; clarify.
        }
        { ss. des; clarify. }
      }
    }
  }
Qed.

Lemma add_unattachable mem1 mem0 loc from to msg
      (ADD: Memory.add mem0 loc from to msg mem1)
  :
    unattachable mem1 =
    (fun loc0 ts0 =>
       if loc_ts_eq_dec (loc0, ts0) (loc, to) then False
       else if loc_ts_eq_dec (loc0, ts0) (loc, from) then
              match Memory.get loc from mem0 with
              | Some _ => False
              | None => True
              end
            else unattachable mem0 loc0 ts0).
Proof.
  extensionality loc0. extensionality ts0.
  exploit add_succeed_wf; eauto. i.  des.
  exploit Memory.add_get0; eauto. i. des.
  apply Coq.Logic.PropExtensionality.propositional_extensionality. split; i.
  { inv H. erewrite Memory.add_o in MSG; eauto.
    erewrite Memory.add_o in EMPTY; eauto. des_ifs.
    { ss. des; clarify. }
    { ss. des; clarify. }
    { ss. des; clarify. }
    { econs; eauto. }
  }
  { des_ifs.
    { ss. des; clarify. econs; eauto.
      erewrite Memory.add_o; eauto. des_ifs. ss. des; clarify. }
    { inv H. econs; eauto.
      { eapply Memory.add_get1; eauto. }
      { erewrite Memory.add_o; eauto. des_ifs. ss. des; clarify. }
    }
  }
Qed.

Lemma remove_unattachable mem1 mem0 loc from to msg
      (REMOVE: Memory.remove mem0 loc from to msg mem1)
      (TS: Time.lt from to)
  :
    unattachable mem1 =
    (fun loc0 ts0 =>
       if loc_ts_eq_dec (loc0, ts0) (loc, from) then False
       else if loc_ts_eq_dec (loc0, ts0) (loc, to) then
              exists ts' msg', (<<GET: Memory.get loc ts' mem0 = Some (to, msg')>>)
            else unattachable mem0 loc0 ts0).
Proof.
  extensionality loc0. extensionality ts0.
  exploit Memory.remove_get0; eauto. i. des.
  apply Coq.Logic.PropExtensionality.propositional_extensionality. split; i.
  { inv H. erewrite Memory.remove_o in MSG; eauto.
    erewrite Memory.remove_o in EMPTY; eauto. des_ifs.
    { ss. des; clarify. timetac. }
    { ss. des; clarify. exploit memory_get_from_inj.
      { eapply MSG. }
      { eapply GET. }
      i. des; clarify.
    }
    { ss. des; clarify. esplits; eauto. }
    { econs; eauto. }
  }
  { des_ifs.
    { ss. des; clarify. econs; eauto.
      erewrite Memory.remove_o; eauto. des_ifs; eauto.
      ss. des; clarify.
    }
    { ss. inv H. econs.
      { instantiate (2:=to0). erewrite Memory.remove_o; eauto. des_ifs; eauto.
        ss. des; clarify. }
      { erewrite Memory.remove_o; eauto. des_ifs. }
    }
  }
Qed.


Lemma step_lifting_promise prom0 prom1 mem0 mem1 cap0
      loc from to msg kind
      (spaces lefts: Loc.t -> Time.t -> Prop)
      (PROMISE: Memory.promise prom0 mem0 loc from to msg prom1 mem1 kind)
      (WRITENOTIN: forall ts (ITV: Interval.mem (from, to) ts), ~ spaces loc ts)
      (WRITENOTTO: ~ lefts loc to)
      (SOUND: Memory.le mem0 cap0)
      (SPACES:
         forall loc ts (COV: covered loc ts cap0),
           <<COV: covered loc ts mem0>> \/ <<SPACE: spaces loc ts>>)
      (UNATTACHABLE:
         forall loc ts (COV: unattachable cap0 loc ts),
           <<COV: unattachable mem0 loc ts>> \/ <<LEFT: lefts loc ts>>)
      (MEM0: Memory.closed mem0)
      (PROM0: Memory.le prom0 mem0)
      (PROM1: Memory.le prom0 cap0)
      (NOTCANCEL: kind <> Memory.op_kind_cancel)
  :
    exists cap1,
      (<<STEP: Memory.promise prom0 cap0 loc from to msg prom1 cap1 kind>>) /\
      (<<SOUND: Memory.le mem1 cap1>>) /\
      (<<SPACES:
         forall loc ts (COV: covered loc ts cap1),
           <<COV: covered loc ts mem1>> \/ spaces loc ts>>) /\
      (<<UNATTACHABLE:
         forall loc ts (COV: unattachable cap1 loc ts),
           <<COV: unattachable mem1 loc ts>> \/ lefts loc ts>>).
Proof.
  inv PROMISE.
  { exploit add_succeed_wf; try apply MEM; eauto. i. des.
    exploit (@Memory.add_exists cap0 loc from to msg); eauto.
    { ii. exploit SPACES.
      { econs; eauto. }
      i. des.
      { inv COV. eapply DISJOINT; eauto. }
      { eapply WRITENOTIN; eauto. }
    }
    i. des. esplits.
    { econs; eauto. i. exploit UNATTACHABLE.
      { econs; eauto. eapply Memory.add_get0; eauto. }
      i. des.
      { inv COV. eapply ATTACH; eauto. }
      { eapply WRITENOTTO; eauto. }
    }
    { ii. erewrite Memory.add_o in LHS; eauto.
      erewrite (@Memory.add_o mem2 cap0); eauto. des_ifs.
      eapply SOUND; eauto. }
    { i. erewrite add_covered in COV; eauto.
      erewrite (@add_covered mem1 mem0); eauto. des; eauto.
      eapply SPACES in COV. des; auto. }
    { i. erewrite add_unattachable in COV; eauto.
      erewrite (@add_unattachable mem1 mem0); eauto. des_ifs; eauto.
      ss. des; clarify. destruct p. eapply SOUND in Heq. clarify. }
  }
  { des. subst.
    exploit (@Memory.split_exists_le prom0 cap0); eauto. i. des. esplits.
    { econs; eauto. }
    { ii. erewrite Memory.split_o in LHS; eauto.
      erewrite (@Memory.split_o mem2 cap0); eauto. des_ifs.
      eapply SOUND; eauto. }
    { i. erewrite (@split_covered mem2 cap0) in COV; eauto.
      erewrite (@split_covered mem1 mem0); eauto. }
    { i. erewrite (@split_unattachable mem2 cap0) in COV; eauto.
      erewrite (@split_unattachable mem1 mem0); eauto. }
  }
  { des. subst.
    exploit (@Memory.lower_exists_le prom0 cap0); eauto. i. des. esplits.
    { econs; eauto. }
    { ii. erewrite Memory.lower_o in LHS; eauto.
      erewrite (@Memory.lower_o mem2 cap0); eauto. des_ifs.
      eapply SOUND; eauto. }
    { i. erewrite (@lower_covered mem2 cap0) in COV; eauto.
      erewrite (@lower_covered mem1 mem0); eauto. }
    { i. erewrite (@lower_unattachable mem2 cap0) in COV; eauto.
      erewrite (@lower_unattachable mem1 mem0); eauto. }
  }
  { ss. }
Qed.

Lemma step_lifting lang st0 st1 lc0 lc1 sc0 sc1 mem0 mem1 cap0 pf e
      (spaces lefts: Loc.t -> Time.t -> Prop)
      (STEP: Thread.step pf e (Thread.mk lang st0 lc0 sc0 mem0) (Thread.mk _ st1 lc1 sc1 mem1))
      (WRITENOTIN: write_not_in spaces e)
      (WRITENOTTO: write_not_to lefts e)
      (NOTCANCEL: ~ is_cancel e)
      (SOUND: Memory.le mem0 cap0)
      (SPACES:
         forall loc ts (COV: covered loc ts cap0),
           <<COV: covered loc ts mem0>> \/ <<SPACE: spaces loc ts>>)
      (UNATTACHABLE:
         forall loc ts (COV: unattachable cap0 loc ts),
           <<COV: unattachable mem0 loc ts>> \/ <<LEFT: lefts loc ts>>)
      (MEM0: Memory.closed mem0)
      (LOCAL0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
  :
    exists cap1,
      (<<STEP: Thread.step pf e (Thread.mk _ st0 lc0 sc0 cap0) (Thread.mk _ st1 lc1 sc1 cap1)>>) /\
      (<<SOUND: Memory.le mem1 cap1>>) /\
      (<<SPACES:
         forall loc ts (COV: covered loc ts cap1),
           <<COV: covered loc ts mem1>> \/ spaces loc ts>>) /\
      (<<UNATTACHABLE:
         forall loc ts (COV: unattachable cap1 loc ts),
           <<COV: unattachable mem1 loc ts>> \/ lefts loc ts>>).
Proof.
  inv STEP.
  { inv STEP0. inv LOCAL. ss.
    destruct (Memory.op_kind_is_cancel kind) eqn:KIND; ss.
    { destruct kind; ss. }
    exploit step_lifting_promise; eauto.
    { eapply LOCAL0. }
    { transitivity mem0; eauto. eapply LOCAL0. }
    { destruct kind; ss. }
    i. des. esplits; eauto. econs. econs.
    { econs; eauto. eapply memory_concrete_le_closed_msg; eauto. }
    { ss. destruct kind; ss. }
  }
  { inv STEP0. inv LOCAL.
    { esplits; eauto. }
    { inv LOCAL1. eapply SOUND in GET. esplits; eauto. }
    { inv LOCAL1. inv WRITE. exploit step_lifting_promise; eauto.
      { eapply LOCAL0. }
      { transitivity mem0; eauto. eapply LOCAL0. }
      { destruct kind; ss. inv PROMISE; ss. }
      i. des. esplits; eauto. econs 2; eauto.
    }
    { inv LOCAL1. eapply SOUND in GET. inv LOCAL2. inv WRITE.
      exploit step_lifting_promise; eauto.
      { eapply LOCAL0. }
      { transitivity mem0; eauto. eapply LOCAL0. }
      { destruct kind; ss. inv PROMISE; ss. }
      i. des. esplits; eauto. econs 2; eauto. econs; eauto. }
    { esplits; eauto. }
    { esplits; eauto. }
    { esplits; eauto. }
  }
Qed.

Lemma traced_step_lifting lang st0 st1 lc0 lc1 sc0 sc1 mem0 mem1 cap0 tr
      (spaces lefts: Loc.t -> Time.t -> Prop)
      (STEPS: Trace.steps tr (Thread.mk lang st0 lc0 sc0 mem0) (Thread.mk _ st1 lc1 sc1 mem1))
      (EVENTS: List.Forall (fun em => <<SAT: (write_not_in spaces /1\ write_not_to lefts /1\ (fun e => ~ is_cancel e)) (snd em)>>) tr)
      (SOUND: Memory.le mem0 cap0)
      (SPACES:
         forall loc ts (COV: covered loc ts cap0),
           <<COV: covered loc ts mem0>> \/ <<SPACE: spaces loc ts>>)
      (UNATTACHABLE:
         forall loc ts (COV: unattachable cap0 loc ts),
           <<COV: unattachable mem0 loc ts>> \/ <<LEFT: lefts loc ts>>)
      (MEM0: Memory.closed mem0)
      (LOCAL0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
  :
    exists cap1,
      (<<STEPS: Trace.steps tr (Thread.mk _ st0 lc0 sc0 cap0) (Thread.mk _ st1 lc1 sc1 cap1)>>) /\
      (<<SOUND: Memory.le mem1 cap1>>) /\
      (<<SPACES:
         forall loc ts (COV: covered loc ts cap1),
           <<COV: covered loc ts mem1>> \/ spaces loc ts>>) /\
      (<<UNATTACHABLE:
         forall loc ts (COV: unattachable cap1 loc ts),
           <<COV: unattachable mem1 loc ts>> \/ lefts loc ts>>).
Proof.
  remember (Thread.mk lang st0 lc0 sc0 mem0).
  remember (Thread.mk lang st1 lc1 sc1 mem1). ginduction STEPS.
  { i. clarify. esplits; eauto. }
  { i. clarify. inv EVENTS. ss. des.
    exploit Thread.step_future; eauto. i. des.
    destruct th1. ss. exploit step_lifting; eauto. i. des.
    exploit IHSTEPS; eauto. i. des. exists cap2. splits; auto. econs; eauto.
  }
Qed.

Lemma promise_not_cancel_covered_increase prom0 prom1 mem0 mem1
      loc from to msg kind
      (PROMISE: Memory.promise prom0 mem0 loc from to msg prom1 mem1 kind)
      (NOTCANCEL: kind <> Memory.op_kind_cancel)
      loc0 ts0
      (COVERED: covered loc0 ts0 mem0)
  :
    covered loc0 ts0 mem1.
Proof.
  inv PROMISE.
  { erewrite (@add_covered mem1 mem0); eauto. }
  { erewrite (@split_covered mem1 mem0); eauto. }
  { erewrite (@lower_covered mem1 mem0); eauto. }
  { ss. }
Qed.

Lemma step_not_cancel_covered_increase lang (th0 th1: Thread.t lang) pf e
      (STEP: Thread.step pf e th0 th1)
      (NOTCANCEL: ~ is_cancel e)
      loc0 ts0
      (COVERED: covered loc0 ts0 th0.(Thread.memory))
  :
    covered loc0 ts0 th1.(Thread.memory).
Proof.
  inv STEP.
  { inv STEP0. inv LOCAL. ss.
    eapply promise_not_cancel_covered_increase; eauto. destruct kind; ss.
  }
  { inv STEP0. inv LOCAL; auto.
    { inv LOCAL0. inv WRITE. eapply promise_not_cancel_covered_increase; eauto.
      destruct kind; ss. inv PROMISE; ss. }
    { inv LOCAL2. inv WRITE. eapply promise_not_cancel_covered_increase; eauto.
      destruct kind; ss. inv PROMISE; ss. }
  }
Qed.

Lemma traced_steps_not_cancel_covered_increase lang (th0 th1: Thread.t lang) tr
      (STEPS: Trace.steps tr th0 th1)
      (EVENTS: List.Forall (fun em => <<SAT: (fun e => ~ is_cancel e) (snd em)>>) tr)
      loc0 ts0
      (COVERED: covered loc0 ts0 th0.(Thread.memory))
  :
    covered loc0 ts0 th1.(Thread.memory).
Proof.
  ginduction STEPS; auto. i. clarify. inv EVENTS.
  eapply step_not_cancel_covered_increase in STEP; eauto.
Qed.

Inductive reservations_added:
  forall (l: list (Loc.t * Interval.t)) (mem0 mem1: Memory.t), Prop :=
| reservations_added_base
    mem0
  :
    reservations_added [] mem0 mem0
| reservations_added_cons
    mem0 mem1 mem2 loc from to tl
    (ADD: Memory.add mem0 loc from to Message.reserve mem1)
    (TL: reservations_added tl mem1 mem2)
    (WF: Time.lt from to)
  :
    reservations_added ((loc, (from, to))::tl) mem0 mem2
.

Lemma reservations_added_cancel
      loc from to mem0 mem1 mem2 tl
      (CANCEL: Memory.remove mem1 loc from to Message.reserve mem0)
      (TL: reservations_added tl mem1 mem2)
      (WF: Time.lt from to)
  :
    reservations_added ((loc, (from, to))::tl) mem0 mem2.
Proof.
  econs; eauto.
  exploit (@Memory.add_exists mem0 loc from to Message.reserve); eauto.
  { i. erewrite Memory.remove_o in GET2; eauto. des_ifs.
    exploit Memory.get_disjoint.
    { eapply GET2. }
    { eapply Memory.remove_get0; eauto. }
    i. ss. des; clarify. symmetry. auto.
  }
  { econs. }
  i. des. replace mem1 with mem3; auto. eapply Memory.ext.
  i. erewrite (@Memory.add_o mem3 mem0); eauto.
  erewrite (@Memory.remove_o mem0 mem1); eauto. des_ifs.
  ss. des; clarify. symmetry. eapply Memory.remove_get0; eauto.
Qed.

Lemma remove_covered_unattachable mem0 loc from to msg mem1
      (REMOVE: Memory.remove mem0 loc from to msg mem1)
      (CLOSED: Memory.closed mem0)
      (TS: Time.lt from to)
  :
    (<<COVERED: forall ts (ITV: Interval.mem (from, to) ts), ~ covered loc ts mem1>>) /\
    (<<UNATTACHABLE: forall ts (TS0: Time.le from ts) (TS1: Time.lt ts to),
        ~ unattachable mem1 loc ts>>).
Proof.
  exploit Memory.remove_get0; eauto. i. des. split.
  { ii. inv H. erewrite Memory.remove_o in GET1; eauto. des_ifs.
    exploit Memory.get_disjoint.
    { eapply GET1. }
    { eapply GET. }
    i. des; clarify. eapply x0; eauto.
  }
  { ii. inv H. erewrite Memory.remove_o in MSG; eauto.
    erewrite Memory.remove_o in EMPTY; eauto. des_ifs.
    { ss. des; clarify. timetac. }
    exploit Memory.get_disjoint.
    { eapply MSG. }
    { eapply GET. }
    i. ss. des; clarify.
    eapply memory_get_ts_strong in MSG. des; clarify.
    { inv CLOSED. erewrite INHABITED in EMPTY. ss. }
    eapply x0.
    { instantiate (1:=Time.meet to to0). unfold Time.meet. des_ifs.
      econs; ss. refl.
    }
    { unfold Time.meet. des_ifs.
      { econs; ss. refl. }
      { econs; ss.
        { eapply TimeFacts.le_lt_lt; eauto. }
        { left. auto. }
      }
    }
  }
Qed.

Fixpoint intervals_sum (l: list (Loc.t * Interval.t)):
  Loc.t -> Time.t -> Prop :=
  match l with
  | [] => bot2
  | (loc, (from, to))::tl =>
    fun loc0 ts0 =>
      (loc0 = loc /\ Interval.mem (from, to) ts0) \/
      intervals_sum tl loc0 ts0
  end.

Definition is_reserving (te: ThreadEvent.t): Prop :=
  match te with
  | ThreadEvent.promise _ _ _ Message.reserve Memory.op_kind_add => True
  | _ => False
  end.

Lemma reservations_added_cancelable l prom0 prom1 cap1
      (ADDEDPROM: reservations_added l prom0 prom1)
      (WF: Memory.le prom1 cap1)
      (CLOSED: Memory.closed cap1)
  :
    exists cap0,
      (<<FUTURE: reservations_added l cap0 cap1>>) /\
      (<<COVERED: forall loc ts
                         (ITV: intervals_sum l loc ts),
          ~ covered loc ts cap0>>) /\
      (* (<<UNATTACHABLE: forall loc from to ts *)
      (*                         (IN: List.In (loc, (from, to)) l) *)
      (*                         (TS0: Time.le from ts) *)
      (*                         (TS1: Time.lt ts to), *)
      (*     ~ unattachable cap0 loc ts>>) /\ *)
      (<<MLE: Memory.le prom0 cap0>>) /\
      (<<SOUND: forall loc ts (NIN: forall from, ~ List.In (loc, (from, ts)) l),
          Memory.get loc ts cap0 = Memory.get loc ts cap1>>) /\
      (<<CLOSED: Memory.closed cap0>>)
.
Proof.
  ginduction l.
  { i. inv ADDEDPROM. exists cap1. splits; eauto.
    { econs 1. }
  }
  { i. inv ADDEDPROM.
    exploit IHl; eauto. i. des.
    hexploit (@Memory.remove_exists mem1 loc from to Message.reserve).
    { eapply Memory.add_get0; eauto. }
    i. des.
    hexploit MemoryMerge.add_remove.
    { eapply ADD. }
    { eapply H. } i. subst.
    hexploit (@Memory.remove_exists_le mem1 cap0); eauto. i. des.
    exploit remove_covered_unattachable; try apply H0; eauto. i. des.
    esplits.
    { eapply reservations_added_cancel; eauto. }
    { i. ss. des; subst; eauto.
      eapply COVERED in ITV; eauto.
      erewrite remove_covered; eauto. ii. eapply ITV. des; auto.
    }
    { ii. erewrite (@Memory.remove_o mem2 mem1) in LHS; eauto.
      erewrite (@Memory.remove_o mem0 cap0); eauto. des_ifs.
      eapply MLE; eauto.
    }
    { i. erewrite (@Memory.remove_o mem0 cap0); eauto. des_ifs.
      { ss. des; clarify. exfalso. eapply NIN; eauto. }
      { eapply SOUND; eauto. ii. eapply NIN; ss. right. eauto. }
    }
    { eapply Memory.cancel_closed; eauto. }
  }
Qed.

Lemma promise_needed_spaces prom0 prom1 mem0 mem1
      loc from to msg kind
      (PROMISE: Memory.promise prom0 mem0 loc from to msg prom1 mem1 kind)
      (WF: kind <> Memory.op_kind_cancel)
  :
    ((<<ALREADY: forall ts (ITV: Interval.mem (from, to) ts), covered loc ts mem0>>) /\
     (<<COVERED: forall loc ts, covered loc ts mem1 <-> covered loc ts mem0>>))
    \/
    ((<<NEW: forall ts (ITV: Interval.mem (from, to) ts), ~ covered loc ts mem0>>) /\
     (<<COVERED: forall loc0 ts0 (COV: covered loc0 ts0 mem1),
         covered loc0 ts0 mem0 \/ (loc0 = loc /\ Interval.mem (from, to) ts0)>>) /\
     (<<WF: Time.lt from to>>))
.
Proof.
  inv PROMISE.
  { right. exploit add_succeed_wf; try apply MEM. i. des. splits; auto.
    { ii. inv H. eapply DISJOINT; eauto. }
    { i. erewrite add_covered in COV; eauto. }
  }
  { left. exploit split_succeed_wf; try apply MEM. i. des. splits; auto.
    { ii. econs; eauto. eapply Interval.le_mem; eauto. econs; ss.
      { refl. }
      { left. auto. }
    }
    { i. eapply split_covered; eauto. }
  }
  { left. exploit lower_succeed_wf; try apply MEM. i. des. splits; auto.
    { ii. econs; eauto. }
    { i. eapply lower_covered; eauto. }
  }
  { ss. }
Qed.

Lemma step_needed_spaces lang (th0 th1: Thread.t lang) pf e
      (times: Loc.t -> Time.t -> Prop)
      (STEP: Thread.step pf e th0 th1)
      (NOTCANCEL: ~ is_cancel e)
      (WFTIME: wf_time_evt times e)
  :
    ((<<ALREADY: write_not_in (fun loc0 ts0 => ~ covered loc0 ts0 th0.(Thread.memory)) e>>) /\
     (<<COVERED: forall loc ts, covered loc ts th1.(Thread.memory) <-> covered loc ts th0.(Thread.memory)>>))
    \/
    exists loc from to,
      (<<NEW: forall ts (ITV: Interval.mem (from, to) ts), ~ covered loc ts th0.(Thread.memory)>>) /\
      (<<COVERED: forall loc0 ts0 (COV: covered loc0 ts0 th1.(Thread.memory)),
          covered loc0 ts0 th0.(Thread.memory) \/ (loc0 = loc /\ Interval.mem (from, to) ts0)>>) /\
      (<<WF: Time.lt from to>>) /\
      (<<TIMES: times loc from /\ times loc to>>) /\
      (<<EVENT: write_not_in (fun loc0 ts0 => ~ (loc0 = loc /\ Interval.mem (from, to) ts0)) e>>).
Proof.
  inv STEP.
  { inv STEP0. inv LOCAL. ss.
    destruct (Memory.op_kind_is_cancel kind) eqn:KIND.
    { destruct kind; ss. }
    exploit promise_needed_spaces; eauto.
    { destruct kind; ss. }
    i. des.
    { left. splits; auto. }
    { right. esplits; eauto. }
  }
  { inv STEP0. inv LOCAL; try by (splits; eauto); ss.
    { ss. inv LOCAL0. inv WRITE.
      exploit promise_needed_spaces; eauto.
      { destruct kind; ss. inv PROMISE; ss. }
      i. des.
      { left. esplits; eauto. }
      { right. esplits; eauto. }
    }
    { ss. inv LOCAL2. inv WRITE.
      exploit promise_needed_spaces; eauto.
      { destruct kind; ss. inv PROMISE; ss. }
      i. des.
      { left. esplits; eauto. }
      { right. esplits; eauto. }
    }
  }
Qed.

Inductive added_intervals
  :
    forall (l: list (Loc.t * Interval.t)) (mem0 mem1: Memory.t), Prop :=
| added_intervals_base
    mem0 mem1
    (COVERED: forall loc ts, covered loc ts mem1 <-> covered loc ts mem0)
  :
    added_intervals [] mem0 mem1
| added_intervals_cons
    mem0 mem1 mem2
    loc from to tl
    (TL: added_intervals tl mem1 mem2)
    (NCOV: forall ts (ITV: Interval.mem (from, to) ts), ~ covered loc ts mem0)
    (COV: forall loc0 ts0 (COVERED: covered loc0 ts0 mem1),
        covered loc0 ts0 mem0 \/ (loc0 = loc /\ Interval.mem (from, to) ts0))
    (TS: Time.lt from to)
  :
    added_intervals ((loc, (from, to)) :: tl) mem0 mem2
.
Hint Constructors added_intervals.

Lemma added_intervals_sum l mem0 mem1
      (ADDED: added_intervals l mem0 mem1)
      loc ts
      (COV: covered loc ts mem1)
  :
    covered loc ts mem0 \/ intervals_sum l loc ts.
Proof.
  ginduction ADDED; i; ss.
  { erewrite <- COVERED; eauto. }
  { exploit IHADDED; eauto. i. des; auto.
    exploit COV; eauto. i. des; auto. }
Qed.

Lemma same_covered_added_intervals l mem0 mem1 mem2
      (ADDED: added_intervals l mem0 mem2)
      (COVERED: forall loc ts, covered loc ts mem1 <-> covered loc ts mem0)
  :
    added_intervals l mem1 mem2.
Proof.
  ginduction ADDED; i; eauto.
  { econs. i. erewrite COVERED0. auto. }
  { econs; eauto.
    { i. erewrite COVERED; eauto. }
    { i. erewrite COVERED; eauto. }
  }
Qed.

Lemma traced_steps_needed_spaces lang (th0 th1: Thread.t lang) tr
      (times: Loc.t -> Time.t -> Prop)
      (STEP: Trace.steps tr th0 th1)
      (EVENTS: List.Forall (fun em => <<SAT: ((fun e => ~ is_cancel e) /1\ wf_time_evt times) (snd em)>>) tr)
  :
    exists l,
      (<<WRITENOTIN:
         List.Forall (fun em => <<SAT: write_not_in (fun loc ts => ~ (covered loc ts th0.(Thread.memory) \/ intervals_sum l loc ts)) (snd em)>>) tr>>) /\
      (<<WF: added_intervals l th0.(Thread.memory) th1.(Thread.memory)>>) /\
      (<<TIMES: List.Forall (fun locitv =>
                               times (fst locitv) (fst (snd locitv)) /\
                               times (fst locitv) (snd (snd locitv))) l>>)
.
Proof.
  ginduction STEP; i.
  { i. exists []. splits; auto. }
  { subst. inv EVENTS. des. exploit IHSTEP; eauto. i. des.
    exploit step_needed_spaces; eauto. i. des.
    { exists l. splits; auto.
      { econs; eauto.
        { eapply write_not_in_mon; eauto. i. ss.
          eapply not_or_and in PR. des. auto. }
        { eapply List.Forall_impl; eauto. i. ss.
          eapply write_not_in_mon; eauto. i. ss.
          erewrite COVERED. auto. }
      }
      { eapply same_covered_added_intervals; eauto.
        i. erewrite COVERED; eauto. }
    }
    { exists ((loc, (from, to)) :: l). splits.
      { econs.
        { eapply write_not_in_mon; eauto. ss. i.
          ii. des. eapply PR. eauto. }
         { eapply List.Forall_impl; try apply WRITENOTIN; eauto. i. ss.
           eapply write_not_in_mon; eauto. i. ss.
           ii. eapply PR. des; auto. eapply COVERED in H3. des; auto. }
      }
      { econs; eauto. }
      { econs; ss. }
    }
  }
Qed.


Lemma can_reserve_all_needed times
      (DIVERGE: forall loc ts,
          exists ts',
            (<<TIMES: times loc ts'>>) /\
            (<<TS: Time.lt ts ts'>>))
      lang
      st0 st1 lc0 lc1 sc0 sc1 mem0 mem1 tr
      (MWF: memory_times_wf times mem0)
      (STEPS: Trace.steps tr (Thread.mk lang st0 lc0 sc0 mem0) (Thread.mk lang st1 lc1 sc1 mem1))
      (EVENTS: List.Forall (fun em => <<SAT: ((fun e => ~ is_cancel e) /1\ wf_time_evt times) (snd em)>>) tr)
      (MEM: Memory.closed mem0)
      (LOCAL: Local.wf lc0 mem0)
      (SC: Memory.closed_timemap sc0 mem0)
  :
    exists lc0' mem0' tr_reserve tr_cancel,
      (<<RESERVESTEPS:
         Trace.steps tr_reserve (Thread.mk lang st0 lc0 sc0 mem0) (Thread.mk lang st0 lc0' sc0 mem0)>>) /\
      (<<RESERVETRACE:
         List.Forall (fun em => <<SAT: (is_reserving /1\ wf_time_evt times) (snd em)>>) tr_reserve>>) /\
      (<<CANCELTRACE:
         List.Forall (fun em => <<SAT: (is_cancel /1\ wf_time_evt times) (snd em)>>) tr_cancel>>) /\
      (<<CAP:
         forall cap0
                (MLE: Memory.le mem0' cap0),
         exists cap1,
           (<<CANCELSTEPS:
              Trace.steps tr_cancel (Thread.mk lang st0 lc0' sc0 cap0) (Thread.mk lang st0 lc0 sc0 mem0)>>) /\
           (<<STEPS:
              Trace.steps tr (Thread.mk lang st0 lc0 sc0 mem0) (Thread.mk lang st1 lc1 sc1 cap1)>>)>>).


Lemma can_reserve_all_needed times
      (DIVERGE: forall loc ts,
          exists ts',
            (<<TIMES: times loc ts'>>) /\
            (<<TS: Time.lt ts ts'>>))
      lang
      st0 st1 tvw0 tvw1 prom0 prom1 sc0 sc1 mem0 mem1 tr
      (MWF: memory_times_wf times mem0)
      (STEPS: Trace.steps tr (Thread.mk lang st0 (Local.mk tvw0 prom0) sc0 mem0) (Thread.mk lang st1 (Local.mk tvw1 prom1) sc1 mem1))
      (EVENTS: List.Forall (fun em => <<SAT: ((fun e => ~ is_cancel e) /1\ wf_time_evt times) (snd em)>>) tr)
      (MEM: Memory.closed mem0)
      (LOCAL: Local.wf (Local.mk tvw0 prom0) mem0)
      (SC: Memory.closed_timemap sc0 mem0)
  :
    exists prom0' mem0' tr_reserve tr_cancel,
      (<<RESERVESTEPS:
         Trace.steps tr_reserve (Thread.mk lang st0 (Local.mk tvw0 prom0) sc0 mem0) (Thread.mk lang st0 (Local.mk tvw0 prom0') sc0 mem0)>>) /\
      (<<RESERVETRACE:
         List.Forall (fun em => <<SAT: (is_reserving /1\ wf_time_evt times) (snd em)>>) tr_reserve>>) /\
      (<<CANCELTRACE:
         List.Forall (fun em => <<SAT: (is_cancel /1\ wf_time_evt times) (snd em)>>) tr_cancel>>) /\
      (<<CAP:
         forall cap0
                (MLE: Memory.le mem0' cap0),
         exists cap1,
           (<<CANCELSTEPS:
              Trace.steps tr_cancel (Thread.mk lang st0 (Local.mk tvw0 prom0') sc0 cap0) (Thread.mk lang st0 (Local.mk tvw0 prom0) sc0 mem0)>>) /\
           (<<STEPS:
              Trace.steps tr (Thread.mk lang st0 (Local.mk tvw0 prom0) sc0 mem0) (Thread.mk lang st1 (Local.mk tvw1 prom1) sc1 cap1)>>)>>).

           (<<CANCELSTEPS:
              Trace.steps tr_cancel (Thread.mk lang st0 (Local.mk tvw0 prom0') sc0 cap0) (Thread.mk lang st0 (Local.mk tvw0 prom0') sc0 mem0)>>) /\



                                                                                             cap0
      (MLE: Memory.le mem0 cap0)



      (<<RESERVEPROM: reservations_added l prom0 prom0'>>) /\
      (<<RESERVEMEM: reservations_added l mem0 mem0'>>) /\


Lemma can_reserve_needed times lang
      st0 st1 tvw0 tvw1 prom0 prom1 sc0 sc1 mem0 mem1 tr
      (MWF: memory_times_wf times mem0)
      (STEPS: Trace.steps tr (Thread.mk lang st0 (Local.mk tvw0 prom0) sc0 mem0) (Thread.mk lang st1 (Local.mk tvw1 prom1) sc1 mem1))
      (EVENTS: List.Forall (fun em => <<SAT: ((fun e => ~ is_cancel e) /1\ wf_time_evt times) (snd em)>>) tr)
      (MEM: Memory.closed mem0)
      (LOCAL: Local.wf (Local.mk tvw0 prom0) mem0)
      (SC: Memory.closed_timemap sc0 mem0)
  :
    exists l prom0' mem0',
      (<<RESERVEPROM: reservations_added l prom0 prom0'>>) /\
      (<<RESERVEMEM: reservations_added l mem0 mem0'>>) /\



         reserve_future_memory

      (STEPS: Trace.steps tr (Thread.mk lang st0 lc0 sc0 mem0) (Thread.mk _ st1 lc1 sc1 mem1))
      (EVENTS: List.Forall (fun em => <<SAT: (write_not_in spaces /1\ write_not_to lefts /1\ (fun e => ~ is_cancel e)) (snd em)>>) tr)
      (SOUND: Memory.le mem0 cap0)
      (SPACES:
         forall loc ts (COV: covered loc ts cap0),
           <<COV: covered loc ts mem0>> \/ <<SPACE: spaces loc ts>>)
      (UNATTACHABLE:
         forall loc ts (COV: unattachable cap0 loc ts),
           <<COV: unattachable mem0 loc ts>> \/ <<LEFT: lefts loc ts>>)
      (MEM0: Memory.closed mem0)
      (LOCAL0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap tm0 mem0)


  :







      eapply

        i.

        eapply same_covered_added_intervals; eauto.
        i. erewrite COVERED; eauto. }
    }

          eapply not_or_and in PR. des.



          ii. eapply PR. des; auto.


          eapply added_intervals_sum; eauto.

          right.


          eapply COVERED0; eauto. }
      }
      { auto.



Lemma wf_empty_intervals_wf spaces mem l
      (WF: wf_empty_intervals spaces mem l)
      loc from to
      (IN: List.In (loc, (from, to)) l)
  :
    (<<SPACES: forall ts (ITV: Interval.mem (from, to) ts), ~ spaces loc ts>>) /\
    (<<TS: Time.lt from to>>).
Proof.
  ginduction l; ss. i. inv WF. des; clarify; eauto.
Qed.

Inductive intervals_sum (l: list (Loc.t * Interval.t))
          (loc: Loc.t) (ts: Time.t): Prop :=
| intervals_sum_intro
    from to
    (IN: List.In (loc, (from, to)) l)
    (ITV: Interval.mem (from, to) ts)
.
Hint Constructors intervals_sum.

Lemma wf_empty_intervals_sum spaces mem l
      (WF: wf_empty_intervals spaces mem l)
      loc ts
      (ITV: intervals_sum l loc ts)
  :
    ~ spaces loc ts.
Proof.
  inv ITV. eapply wf_empty_intervals_wf; eauto.
Qed.


Lemma traced_steps_needed_spaces lang (th0 th1: Thread.t lang) tr
      (spaces: Loc.t -> Time.t -> Prop)
      (STEP: Trace.steps tr th0 th1)
      (EVENTS: List.Forall (fun em => <<SAT: ((fun e => ~ is_cancel e) /1\ write_not_in spaces) (snd em)>>) tr)
  (* (MEM0: Memory.closed mem0) *)
  (* (LOCAL0: Local.wf lc0 mem0) *)
  (* (SC0: Memory.closed_timemap tm0 mem0) *)
  :
    exists l,
      (<<COVERED: forall loc0 ts0 (ITV: intervals_sum l loc0 ts0),
          covered loc0 ts0 th1.(Thread.memory)>>) /\
      (<<WRITENOTIN:
         List.Forall (fun em => write_not_in (fun loc ts => ~ (intervals_sum l loc ts \/ covered loc ts th0.(Thread.memory))) (snd em)) tr>>) /\
      (<<WF: wf_empty_intervals spaces th0.(Thread.memory) l>>)
.
Proof.
  ginduction STEP; i.
  { i. exists []. splits; auto. i. inv ITV. ss. }
  { subst. inv EVENTS. des. exploit IHSTEP; eauto. i. des.
    exploit step_needed_spaces; eauto. i. des.
    { exists l. splits; auto.
      { econs; eauto.
        { eapply write_not_in_mon; eauto. i. ss.
          eapply not_or_and in PR. des. auto. }
        { eapply List.Forall_impl; eauto. i. ss.
          eapply write_not_in_mon; eauto. i. ss.
          ii. eapply PR. des; auto. right.
          eapply COVERED0; eauto. }
      }
      { auto.


           eapply not_or_and in PR. des. auto. }
        {
          eapply write
        ss.



  inv STEP.
  { inv STEP0. inv LOCAL. ss.
    destruct (Memory.op_kind_is_cancel kind) eqn:KIND; ss.
    { destruct kind; ss. }
    exploit promise_needed_spaces; eauto.
    { destruct kind; ss. }
    i. des.
    {


Lemma promise_needed_spaces_list prom0 prom1 mem0 mem1 l
      loc from to msg kind
      (spaces: Loc.t -> Time.t -> Prop)
      (PROMISE: Memory.promise prom0 mem0 loc from to msg prom1 mem1 kind)
      (WRITENOTIN: forall ts (ITV: Interval.mem (from, to) ts), ~ spaces loc ts)
      (NOTCANCEL: kind <> Memory.op_kind_cancel)
      (WFLIST: wf_empty_intervals spaces mem1 l)
  :
    exists l',
      (<<WF: wf_empty_intervals spaces mem0 l>>) /\
      (<<COVERED: forall loc0 ts0 (ITV: intervals_sum l loc0 ts0),
          covered loc0 ts0 mem1>>) /\
      (<<WRITENOTIN: forall ts (ITV: Interval.mem (from, to) ts),
          (<<ALREADY: covered loc ts mem0>>) \/ (<<NEW: intervals_sum l loc ts>>)>>).
Proof.
  exploit promise_needed_spaces; eauto. i. des.
  { exists []. splits.
    { econs. }
    { i. inv ITV. ss. }
    { i. left. exploit promise_not_cancel_covered_increase; eauto. }
  }
  { exists [(loc, (from, to))]. splits; eauto.
    { i. inv ITV; ss. des; clarify. eapply NEW; eauto. }
    { i. right. econs; eauto. ss. auto. }
  }
Qed.

Lemma promise_needed_spaces_list prom0 prom1 mem0 mem1
      loc from to msg kind
      (spaces: Loc.t -> Time.t -> Prop)
      (PROMISE: Memory.promise prom0 mem0 loc from to msg prom1 mem1 kind)
      (WRITENOTIN: forall ts (ITV: Interval.mem (from, to) ts), ~ spaces loc ts)
      (WF: kind <> Memory.op_kind_cancel)
  :
    exists l,
      (<<WF: wf_empty_intervals spaces mem0 l>>) /\
      (<<COVERED: forall loc0 ts0 (ITV: intervals_sum l loc0 ts0),
          covered loc0 ts0 mem1>>) /\
      (<<WRITENOTIN: forall ts (ITV: Interval.mem (from, to) ts),
          (<<ALREADY: covered loc ts mem0>>) \/ (<<NEW: intervals_sum l loc ts>>)>>).
Proof.
  exploit promise_needed_spaces; eauto. i. des.
  { exists []. splits.
    { econs. }
    { i. inv ITV. ss. }
    { i. left. exploit promise_not_cancel_covered_increase; eauto. }
  }
  { exists [(loc, (from, to))]. splits; eauto.
    { i. inv ITV; ss. des; clarify. eapply NEW; eauto. }
    { i. right. econs; eauto. ss. auto. }
  }
Qed.

Lemma step_needed_spaces lang st0 st1 lc0 lc1 tm0 tm1 mem0 mem1 pf e
      (spaces: Loc.t -> Time.t -> Prop)
      (STEP: Thread.step pf e (Thread.mk lang st0 lc0 tm0 mem0) (Thread.mk _ st1 lc1 tm1 mem1))
      (WRITENOTIN: write_not_in spaces e)
      (NOTCANCEL: ~ is_cancel e)
      (MEM0: Memory.closed mem0)
      (LOCAL0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap tm0 mem0)
  :
    exists l,
      (<<COVERED: forall loc0 ts0 (ITV: intervals_sum l loc0 ts0),
          covered loc0 ts0 mem1>>) /\
      (<<WRITENOTIN: forall ts (ITV: Interval.mem (from, to) ts),
          (<<ALREADY: covered loc ts mem0>>) \/ (<<NEW: intervals_sum l loc ts>>)>>)      (<<WF: wf_empty_intervals spaces mem0 l>>)
.
Proof.
  inv STEP.
  { inv STEP0. inv LOCAL. ss.
    destruct (Memory.op_kind_is_cancel kind) eqn:KIND; ss.
    { destruct kind; ss. }
    exploit promise_needed_spaces; eauto.
    { destruct kind; ss. }
    i. des.
    {

  }

    exploit step_lifting_promise; eauto.
    { eapply LOCAL0. }
    { transitivity mem0; eauto. eapply LOCAL0. }
    { destruct kind; ss. }
    i. des. esplits; eauto. econs. econs.
    { econs; eauto. eapply memory_concrete_le_closed_msg; eauto. }
    { ss. destruct kind; ss. }
  }
  { inv STEP0. inv LOCAL.
    { esplits; eauto. }
    { inv LOCAL1. eapply SOUND in GET. esplits; eauto. }
    { inv LOCAL1. inv WRITE. exploit step_lifting_promise; eauto.
      { eapply LOCAL0. }
      { transitivity mem0; eauto. eapply LOCAL0. }
      { destruct kind; ss. inv PROMISE; ss. }
      i. des. esplits; eauto. econs 2; eauto.
    }
    { inv LOCAL1. eapply SOUND in GET. inv LOCAL2. inv WRITE.
      exploit step_lifting_promise; eauto.
      { eapply LOCAL0. }
      { transitivity mem0; eauto. eapply LOCAL0. }
      { destruct kind; ss. inv PROMISE; ss. }
      i. des. esplits; eauto. econs 2; eauto. econs; eauto. }
    { esplits; eauto. }
    { esplits; eauto. }
    { esplits; eauto. }
  }
Qed.

    exists cap1,
      (<<STEP: Thread.step pf e (Thread.mk _ st0 lc0 tm0 cap0) (Thread.mk _ st1 lc1 tm1 cap1)>>) /\
      (<<SOUND: Memory.le mem1 cap1>>) /\
      (<<SPACES:
         forall loc ts (COV: covered loc ts cap1),
           <<COV: covered loc ts mem1>> \/ spaces loc ts>>) /\
      (<<UNATTACHABLE:
         forall loc ts (COV: unattachable cap1 loc ts),
           <<COV: unattachable mem1 loc ts>> \/ lefts loc ts>>).
Proof.
  inv STEP.
  { inv STEP0. inv LOCAL. ss.
    destruct (Memory.op_kind_is_cancel kind) eqn:KIND; ss.
    { destruct kind; ss. }
    exploit step_lifting_promise; eauto.
    { eapply LOCAL0. }
    { transitivity mem0; eauto. eapply LOCAL0. }
    { destruct kind; ss. }
    i. des. esplits; eauto. econs. econs.
    { econs; eauto. eapply memory_concrete_le_closed_msg; eauto. }
    { ss. destruct kind; ss. }
  }
  { inv STEP0. inv LOCAL.
    { esplits; eauto. }
    { inv LOCAL1. eapply SOUND in GET. esplits; eauto. }
    { inv LOCAL1. inv WRITE. exploit step_lifting_promise; eauto.
      { eapply LOCAL0. }
      { transitivity mem0; eauto. eapply LOCAL0. }
      { destruct kind; ss. inv PROMISE; ss. }
      i. des. esplits; eauto. econs 2; eauto.
    }
    { inv LOCAL1. eapply SOUND in GET. inv LOCAL2. inv WRITE.
      exploit step_lifting_promise; eauto.
      { eapply LOCAL0. }
      { transitivity mem0; eauto. eapply LOCAL0. }
      { destruct kind; ss. inv PROMISE; ss. }
      i. des. esplits; eauto. econs 2; eauto. econs; eauto. }
    { esplits; eauto. }
    { esplits; eauto. }
    { esplits; eauto. }
  }
Qed.


Lemma step_needed_space prom0 prom1 mem0 mem1 cap0
      loc from to msg kind
      (spaces lefts: Loc.t -> Time.t -> Prop)
      (PROMISE: Memory.promise prom0 mem0 loc from to msg prom1 mem1 kind)
      (WRITENOTIN: forall ts (ITV: Interval.mem (from, to) ts), ~ spaces loc ts)
      (WRITENOTTO: ~ lefts loc to)
      (SOUND: Memory.le mem0 cap0)
      (SPACES:
         forall loc ts (COV: covered loc ts cap0),
           <<COV: covered loc ts mem0>> \/ <<SPACE: spaces loc ts>>)
      (UNATTACHABLE:
         forall loc ts (COV: unattachable cap0 loc ts),
           <<COV: unattachable mem0 loc ts>> \/ <<LEFT: lefts loc ts>>)
      (MEM0: Memory.closed mem0)
      (PROM0: Memory.le prom0 mem0)
      (PROM1: Memory.le prom0 cap0)
      (WF: kind <> Memory.op_kind_cancel)
  :
    exists cap1,
      (<<STEP: Memory.promise prom0 cap0 loc from to msg prom1 cap1 kind>>) /\
      (<<SOUND: Memory.le mem1 cap1>>) /\
      (<<SPACES:
         forall loc ts (COV: covered loc ts cap1),
           <<COV: covered loc ts mem1>> \/ spaces loc ts>>) /\
      (<<UNATTACHABLE:
         forall loc ts (COV: unattachable cap1 loc ts),
           <<COV: unattachable mem1 loc ts>> \/ lefts loc ts>>).
Proof.
  inv PROMISE.
  { exploit add_succeed_wf; try apply MEM; eauto. i. des.
    exploit (@Memory.add_exists cap0 loc from to msg); eauto.
    { ii. exploit SPACES.
      { econs; eauto. }
      i. des.
      { inv COV. eapply DISJOINT; eauto. }
      { eapply WRITENOTIN; eauto. }
    }
    i. des. esplits.
    { econs; eauto. i. exploit UNATTACHABLE.
      { econs; eauto. eapply Memory.add_get0; eauto. }
      i. des.
      { inv COV. eapply ATTACH; eauto. }
      { eapply WRITENOTTO; eauto. }
    }
    { ii. erewrite Memory.add_o in LHS; eauto.
      erewrite (@Memory.add_o mem2 cap0); eauto. des_ifs.
      eapply SOUND; eauto. }
    { i. erewrite add_covered in COV; eauto.
      erewrite (@add_covered mem1 mem0); eauto. des; eauto.
      eapply SPACES in COV. des; auto. }
    { i. erewrite add_unattachable in COV; eauto.
      erewrite (@add_unattachable mem1 mem0); eauto. des_ifs; eauto.
      ss. des; clarify. destruct p. eapply SOUND in Heq. clarify. }
  }
  { des. subst.
    exploit (@Memory.split_exists_le prom0 cap0); eauto. i. des. esplits.
    { econs; eauto. }
    { ii. erewrite Memory.split_o in LHS; eauto.
      erewrite (@Memory.split_o mem2 cap0); eauto. des_ifs.
      eapply SOUND; eauto. }
    { i. erewrite (@split_covered mem2 cap0) in COV; eauto.
      erewrite (@split_covered mem1 mem0); eauto. }
    { i. erewrite (@split_unattachable mem2 cap0) in COV; eauto.
      erewrite (@split_unattachable mem1 mem0); eauto. }
  }
  { des. subst.
    exploit (@Memory.lower_exists_le prom0 cap0); eauto. i. des. esplits.
    { econs; eauto. }
    { ii. erewrite Memory.lower_o in LHS; eauto.
      erewrite (@Memory.lower_o mem2 cap0); eauto. des_ifs.
      eapply SOUND; eauto. }
    { i. erewrite (@lower_covered mem2 cap0) in COV; eauto.
      erewrite (@lower_covered mem1 mem0); eauto. }
    { i. erewrite (@lower_unattachable mem2 cap0) in COV; eauto.
      erewrite (@lower_unattachable mem1 mem0); eauto. }
  }
  { ss. }
Qed.




Lemma step_lifting lang st0 st1 lc0 lc1 tm0 tm1 mem0 mem1 cap0 pf e
      (spaces lefts: Loc.t -> Time.t -> Prop)
      (STEP: Thread.step pf e (Thread.mk lang st0 lc0 tm0 mem0) (Thread.mk _ st1 lc1 tm1 mem1))
      (WRITENOTIN: write_not_in spaces e)
      (WRITENOTTO: write_not_to lefts e)
      (SOUND: Memory.le mem0 cap0)
      (SPACES:
         forall loc ts (COV: covered loc ts cap0),
           <<COV: covered loc ts mem0>> \/ <<SPACE: spaces loc ts>>)
      (UNATTACHABLE:
         forall loc ts (COV: unattachable cap0 loc ts),
           <<COV: unattachable mem0 loc ts>> \/ <<LEFT: lefts loc ts>>)
      (MEM0: Memory.closed mem0)
      (* (MEM1: Memory.closed cap0) *)
      (LOCAL0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap tm0 mem0)
  :
    exists cap1,
      (<<STEP: Thread.step pf e (Thread.mk _ st0 lc0 tm0 cap0) (Thread.mk _ st1 lc1 tm1 cap1)>>) /\
      (<<SOUND: Memory.le mem1 cap1>>) /\
      (<<SPACES:
         forall loc ts (COV: covered loc ts cap1),
           <<COV: covered loc ts mem1>> \/ spaces loc ts>>) /\
      (<<UNATTACHABLE:
         forall loc ts (COV: unattachable cap1 loc ts),
           <<COV: unattachable mem1 loc ts>> \/ lefts loc ts>>).
Proof.
  assert (LOCAL1: Local.wf lc0 cap0).
  { eapply memory_concrete_le_local_wf; eauto.
    etrans; eauto. eapply LOCAL0. }
  assert (SC1: Memory.closed_timemap tm0 cap0).
  { eapply memory_concrete_le_closed_timemap; eauto. }
  inv STEP.
  { inv STEP0. inv LOCAL. inv PROMISE.
    { exploit add_succeed_wf; eauto. i. des.

      Memory.promise
      exploit Memory.add_exists_le

      Memory.add




         write_not_in

                  ~ write_not_in aaa, ~ covered aaa mem0, ~ covered aa mem1
                                                            ~

      (SOUND: Memory.le mem0 cap0)
      (U

      Thread.mk




           (ADJ: Memory.adjacent



           Memory.adjacent



Definition pf_consistent_strong_aux lang (e0:Thread.t lang): Prop :=
  forall mem1
         (CAP: Memory.cap e0.(Thread.memory) mem1),
  exists tr_cancel tr e1 times,
    (<<STEPS: Trace.steps (tr_cancel ++ tr) (Thread.mk _ e0.(Thread.state) e0.(Thread.local) TimeMap.bot mem1) e1>>) /\
    (<<CANCELS: List.Forall (fun em => <<SAT: is_cancel (snd em)>>) tr_cancel>>) /\
    (<<CANCELS: List.Forall (fun em => <<SAT: (fun e => ~ is_cancel e) (snd em)>>) tr_cancel>>) /\
    (<<EVENTS: List.Forall (fun em => <<SAT: (promise_free /1\ no_sc /1\ (wf_time_evt (fun loc to => List.In to (times loc)))) (snd em)>> /\ <<TAU: ThreadEvent.get_machine_event (snd em) = MachineEvent.silent>>) tr >>) /\
    (__guard__((exists st',
                   (<<LOCAL: Local.failure_step e1.(Thread.local)>>) /\
                   (<<FAILURE: Language.step lang ProgramEvent.failure (@Thread.state lang e1) st'>>)) \/
               ((<<PROMISES: e1.(Thread.local).(Local.promises) = Memory.bot>>)))).

Lemma pf_consistent_strong_pf_consistent_strong_aux lang (th: Thread.t lang)
      (WF: Local.wf th.(Thread.local) th.(Thread.memory))
      (MEM: Memory.closed th.(Thread.memory))
      (CONSISTENT: pf_consistent_strong th)
  :
    pf_consistent_strong_aux th.
Proof.
  ii. exploit CONSISTENT; eauto. i. des.
  hexploit (proj1 (@pred_steps_trace_steps (promise_free /1\ no_sc) _ (Thread.mk _ th.(Thread.state) th.(Thread.local) TimeMap.bot mem1) e1)).



  eapply pred_step_rtc_mon with (Q:=(promise_free /1\ no_sc /1\ is_cancel)) in STEPS0; cycle 1.
  { i. destruct x1; ss. destruct kind; ss. }
  eapply pred_step_rtc_mon with (Q:=(promise_free /1\ no_sc /1\ (fun e => ~ is_cancel e))) in STEPS1; cycle 1.
  { i. des; auto. }
  hexploit (proj1 (@pred_steps_trace_steps (promise_free /1\ no_sc) _ (Thread.mk _ th.(Thread.state) th.(Thread.local) TimeMap.bot mem1) e1)).
  { eauto.

    etrans; eauto. } i. des.


  hexploit (proj1 (@pred_steps_trace_steps (promise_free /1\ no_sc) _ (Thread.mk _ th.(Thread.state) th.(Thread.local) TimeMap.bot mem1) e2)).
  { etrans; eauto. } i. des.
  exploit trace_times_list_exists; eauto. i. des.
  eexists tr, e2, times. esplits; eauto.
  { eapply list_Forall_sum.
    { eapply EVENTS. }
    { eapply WFTIME. }
    i. ss. des. splits; auto. }
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
                                                      /1\ wf_time_evt (fun loc => certification_times times f max (Memory.max_timemap e0.(Thread.memory)) loc)) (snd em)>> /\ <<TAU: ThreadEvent.get_machine_event (snd em) = MachineEvent.silent>>) ftr >>) /\
          (<<TRACE: List.Forall2 (fun em fem => tevent_map (fun loc => f loc (tm loc)) (snd fem) (snd em)) tr ftr>>) /\
          (__guard__((exists st',
                         (<<LOCAL: Local.failure_step e1.(Thread.local)>>) /\
                         (<<FAILURE: Language.step lang ProgramEvent.failure (@Thread.state lang e1) st'>>)) \/
                     (<<PROMISES: e1.(Thread.local).(Local.promises) = Memory.bot>>)))>>).


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
  exists ftr, (Thread.mk _ state flc1 fsc1 fmem1). splits; auto.
  { eapply List.Forall_forall. i.
    cut ((promise_free /1\ no_sc) (snd x) /\ ThreadEvent.get_machine_event (snd x) = MachineEvent.silent).
    { i. des. splits; auto.
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
    }
  }
Qed.


Definition pf_consistent_super_strong_easy lang (e0:Thread.t lang)
           (tr : Trace.t)
           (times: Loc.t -> (Time.t -> Prop))
  : Prop :=
  forall cap (tm: Loc.t -> nat) max
         (CAPTM: forall loc, Time.lt (Memory.max_ts loc e0.(Thread.memory)) (incr_time_seq (tm loc)))
         (CAP: cap_flex e0.(Thread.memory) cap (fun loc => incr_time_seq (tm loc)))
         (MAX: concrete_promise_max_timemap
                 (e0.(Thread.memory))
                 (e0.(Thread.local).(Local.promises))
                 max),
  exists ftr e1 f,
    (<<STEPS: Trace.steps ftr (Thread.mk _ e0.(Thread.state) e0.(Thread.local) TimeMap.bot cap) e1>>) /\
    (<<EVENTS: List.Forall (fun em => <<SAT: (promise_free
                                                /1\ no_sc
                                                /1\ wf_time_evt times) (snd em)>> /\ <<TAU: ThreadEvent.get_machine_event (snd em) = MachineEvent.silent>>) ftr >>) /\
    (<<MAPLT: mapping_map_lt f>>) /\
    (<<MAPIDENT: forall loc ts fts
                        (TS: Time.le fts (max loc))
                        (MAP: f loc ts fts),
        ts = fts>>) /\
    (<<BOUND: forall loc ts fts (TS: Time.lt (max loc) fts) (MAP: f loc ts fts),
        Time.lt (max loc) ts /\ Time.le (incr_time_seq (tm loc)) fts>>) /\
    (<<TRACE: List.Forall2 (fun em fem => tevent_map_weak f (snd fem) (snd em)) tr ftr>>) /\
    (__guard__((exists st',
                   (<<LOCAL: Local.failure_step e1.(Thread.local)>>) /\
                   (<<FAILURE: Language.step lang ProgramEvent.failure (@Thread.state lang e1) st'>>)) \/
               (<<PROMISES: e1.(Thread.local).(Local.promises) = Memory.bot>>))).


Lemma pf_consistent_flex_super_strong_easy
      lang (th: Thread.t lang) tr times f
      (WF: Local.wf th.(Thread.local) th.(Thread.memory))
      (MEM: Memory.closed th.(Thread.memory))
      (CONSISTENT: pf_consistent_flex th tr times f)
  :
    exists certimes,
      (<<WO: forall loc, well_ordered (certimes loc)>>) /\
      (<<CONSISTENT: pf_consistent_super_strong_easy th tr certimes>>).
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
  hexploit CONSISTENT0; eauto. i. des.
  assert (MAPALL: cap_flex_map
                    max
                    (fun loc => Time.incr (Memory.max_ts loc (Thread.memory th)))
                    (fun loc => incr_time_seq (tm loc))
                    times (fun loc => f loc (tm loc))).
  { eapply cap_flex_map_locwise; eauto. }
  eexists _, _, (fun loc => f loc (tm loc)). splits; eauto.
  { eapply MAPALL. }
  { i. eapply MAPALL in TS; eauto.
    eapply mapping_map_lt_inj.
    { eapply MAPALL; eauto. }
    { ss. eauto. }
    { eauto. }
  }
  { i. destruct (Time.le_lt_dec ts (max loc)).
    { dup l. eapply MAPALL in l; eauto.
      exploit mapping_map_lt_map_eq.
      { eapply MAPALL. }
      { eapply MAP0. }
      { eapply l. }
      i. subst. timetac.
    }
    { split; auto. eapply MAPALL.(cap_flex_map_bound) in l; eauto. }
  }
  { eapply list_Forall2_impl; eauto. i. eapply tevent_map_tevent_map_weak; eauto. }
Qed.


Definition pf_consistent_super_strong_aux lang (e0:Thread.t lang)
           (tr : Trace.t)
           (times: Loc.t -> (Time.t -> Prop))
  : Prop :=
  forall cap (tm: Loc.t -> nat) max
         (CAPTM: forall loc, Time.lt (Memory.max_ts loc e0.(Thread.memory)) (incr_time_seq (tm loc)))
         (CAP: cap_flex e0.(Thread.memory) cap (fun loc => incr_time_seq (tm loc)))
         (MAX: concrete_promise_max_timemap
                 (e0.(Thread.memory))
                 (e0.(Thread.local).(Local.promises))
                 max),
  exists ftr e1 f,
    (<<STEPS: Trace.steps ftr (Thread.mk _ e0.(Thread.state) e0.(Thread.local) TimeMap.bot cap) e1>>) /\
    (<<EVENTS: List.Forall (fun em => <<SAT: (promise_free
                                                /1\ no_sc
                                                /1\ no_read_msgs (fun loc ts => ~ (covered loc ts e0.(Thread.local).(Local.promises) \/ concrete_promised e0.(Thread.memory) loc ts \/ Time.lt (incr_time_seq (tm loc)) ts))
                                                /1\ write_not_in (fun loc ts => (<<TS: Time.le ts (incr_time_seq (tm loc))>>) /\ (<<PROM: ~ covered loc ts e0.(Thread.local).(Local.promises)>>))
                                                /1\ wf_time_evt times) (snd em)>> /\ <<TAU: ThreadEvent.get_machine_event (snd em) = MachineEvent.silent>>) ftr >>) /\
    (<<MAPLT: mapping_map_lt f>>) /\
    (<<MAPIDENT: forall loc ts fts
                        (TS: Time.le fts (max loc))
                        (MAP: f loc ts fts),
        ts = fts>>) /\
    (<<BOUND: forall loc ts fts (TS: Time.lt (max loc) fts) (MAP: f loc ts fts),
        Time.lt (max loc) ts /\ Time.le (incr_time_seq (tm loc)) fts>>) /\
    (<<TRACE: List.Forall2 (fun em fem => tevent_map_weak f (snd fem) (snd em)) tr ftr>>) /\
    (__guard__((exists st',
                   (<<LOCAL: Local.failure_step e1.(Thread.local)>>) /\
                   (<<FAILURE: Language.step lang ProgramEvent.failure (@Thread.state lang e1) st'>>)) \/
               (<<PROMISES: e1.(Thread.local).(Local.promises) = Memory.bot>>))).

Lemma pf_consistent_super_strong_easy_aux
      lang (th: Thread.t lang) tr times
      (WF: Local.wf th.(Thread.local) th.(Thread.memory))
      (MEM: Memory.closed th.(Thread.memory))
      (CONSISTENT: pf_consistent_super_strong_easy th tr times)
  :
    pf_consistent_super_strong_aux th tr times.
Proof.
  ii. exploit CONSISTENT; eauto. i. des. esplits; eauto.
  assert (MLE: Memory.le (Local.promises (Thread.local th)) cap).
  { etrans.
    { eapply WF. }
    { eapply CAP. }
  }
  exploit write_not_in_traced; eauto.
  intros WRITENOTIN.
  exploit no_read_unreadable_traced; eauto.
  intros NOREAD. ss.
  eapply list_Forall_sum.
  { eapply list_Forall_sum.
    { eapply WRITENOTIN. }
    { eapply NOREAD. }
    instantiate (1:=fun lce => (no_read_msgs (fun loc ts => ~ (covered loc ts th.(Thread.local).(Local.promises) \/ concrete_promised th.(Thread.memory) loc ts \/ Time.lt (incr_time_seq (tm loc)) ts))
                                             /1\ write_not_in (fun loc ts => (<<TS: Time.le ts (incr_time_seq (tm loc))>>) /\ (<<PROM: ~ covered loc ts th.(Thread.local).(Local.promises)>>))) (snd lce)).
    i. ss. splits.
    { eapply no_read_msgs_mon; eauto. i.
      eapply not_or_and in PR. des.
      eapply not_or_and in PR0. des. econs.
      { eapply unwritable_eq; eauto. econs; eauto.
        eapply cap_flex_covered; eauto. ss. econs; eauto.
        { ss. destruct (Time.bot_spec x2); auto. inv H.
          exfalso. eapply PR0. econs. eapply MEM. }
        { ss. destruct (Time.le_lt_dec x2 (incr_time_seq (tm x0))); ss. }
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
Qed.


Definition pf_consistent_super_strong_aux2 lang (e0:Thread.t lang)
           (tr : Trace.t)
           (times: Loc.t -> (Time.t -> Prop))
  : Prop :=
  forall mem1 tm max
         (FUTURE: Memory.future_weak e0.(Thread.memory) mem1)
         (CLOSED: Memory.closed mem1)
         (LOCAL: Local.wf e0.(Thread.local) mem1)
         (MAX: concrete_promise_max_timemap
                 (e0.(Thread.memory))
                 (e0.(Thread.local).(Local.promises))
                 max),
  exists ftr e1 f,
    (<<STEPS: Trace.steps ftr (Thread.mk _ e0.(Thread.state) e0.(Thread.local) TimeMap.bot mem1) e1>>) /\
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
        Time.lt (max loc) ts /\ Time.le (tm loc) fts>>) /\
    (<<TRACE: List.Forall2 (fun em fem => tevent_map_weak f (snd fem) (snd em)) tr ftr>>) /\
    (__guard__((exists st',
                   (<<LOCAL: Local.failure_step e1.(Thread.local)>>) /\
                   (<<FAILURE: Language.step lang ProgramEvent.failure (@Thread.state lang e1) st'>>)) \/
               ((<<PROMISES: e1.(Thread.local).(Local.promises) = Memory.bot>>)))).

Lemma ident_map_compose_tevent_weak f te0 te1 te2
      (MAP0: tevent_map_weak f te1 te0)
      (MAP1: tevent_map_weak ident_map te2 te1)
  :
    tevent_map_weak f te2 te0.
Proof.
  inv MAP0; inv MAP1; econs.
  { inv FROM0. auto. }
  { inv TO0. auto. }
  { inv TO0. eauto. }
  { inv FROM0. eauto. }
  { inv TO0. eauto. }
  { inv FROM0. eauto. }
  { inv TO0. eauto. }
Qed.

Lemma ident_map_compose_tevent_weak2 f te0 te1 te2
      (MAP0: tevent_map_weak ident_map te1 te0)
      (MAP1: tevent_map_weak f te2 te1)
  :
    tevent_map_weak f te2 te0.
Proof.
  inv MAP0; inv MAP1; econs.
  { inv FROM. auto. }
  { inv TO. auto. }
  { inv TO. eauto. }
  { inv FROM. eauto. }
  { inv TO. eauto. }
  { inv FROM. eauto. }
  { inv TO. eauto. }
Qed.


Lemma pf_consistent_super_strong_aux_aux2
      lang (th: Thread.t lang) tr times
      (WF: Local.wf th.(Thread.local) th.(Thread.memory))
      (MEM: Memory.closed th.(Thread.memory))
      (CONSISTENT: pf_consistent_super_strong_aux th tr times)
  :
    pf_consistent_super_strong_aux2 th tr times.
Proof.
  ii.
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
  des.
  hexploit (@cap_flex_exists th.(Thread.memory) (fun loc => incr_time_seq (ftm loc))); eauto.
  { i. eapply TM. }
  intros [cap CAP]. des.
  exploit CONSISTENT; eauto.
  { i. eapply TM. }
  i. des.
  hexploit (@cap_flex_future_memory_map th.(Thread.memory)); eauto.
  { i. eapply TM. }
  { i. left. eapply TM. }
  intros MEMORY. destruct e1. ss.
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
  { eapply cap_flex_closed; eauto. i. eapply TM. }
  { eapply Memory.closed_timemap_bot; eauto. eapply CLOSED. }
  { eapply Memory.closed_timemap_bot; eauto.
    eapply cap_flex_closed; eauto. i. eapply TM. }
  { eapply ident_map_local. }
  { eauto. }
  { eapply mapping_map_lt_collapsable_unwritable. eapply ident_map_lt. }
  { eapply ident_map_timemap. }
  { refl. }
  i. des. esplits; eauto.
  eapply List.Forall_forall. i.
  eapply list_Forall2_in in H; eauto. des.
  eapply List.Forall_forall in IN; eauto. ss. des.
  destruct a, x. ss. splits; auto.
  { inv EVENT; ss. inv FROM. inv TO. inv KIND; ss.
    inv MSG0; ss. inv MSG; ss. inv MAP0; ss. }
  { inv EVENT; ss. }
  { inv EVENT; ss.
    { inv TO. ii. eapply SAT2. ii. eapply H. des; auto.
      right. right. eapply TimeFacts.le_lt_lt; eauto. apply TM. }
    { inv FROM. ii. eapply SAT2. ii. eapply H. des; auto.
      right. right. eapply TimeFacts.le_lt_lt; eauto. apply TM. }
  }
  { inv EVENT; ss.
    { inv TO. inv FROM. inv KIND; ss. ii. eapply SAT1; eauto.
      des. split; auto. red. etrans; eauto. eapply TM. }
    { inv TO. inv FROM. ii. eapply SAT1; eauto.
      des. split; auto. red. etrans; eauto. eapply TM. }
    { inv TO. inv FROM. ii. eapply SAT1; eauto.
      des. split; auto. red. etrans; eauto. eapply TM. }
  }
  { inv EVENT; ss.
    { inv FROM. inv TO. auto. }
    { inv FROM. inv TO. auto. }
    { inv FROM. inv TO. auto. }
  }
  { inv EVENT; ss. }
  { ii. exploit BOUND; eauto. i. des. split; auto.
    etrans; eauto. eapply TM. }
  { eapply list_Forall2_compose; eauto. i. ss. des.
    eapply ident_map_compose_tevent_weak; eauto.
    eapply tevent_map_tevent_map_weak; eauto.
  }
  { ss. unguard. des.
    { left. esplits; eauto. eapply failure_step_map; eauto.
      { eapply ident_map_le. }
      { eapply ident_map_eq. }
    }
    { right. inv LOCAL0. rewrite PROMISES in *.
      eapply bot_promises_map; eauto. }
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
        Time.lt (max loc) ts /\ Time.le (tm loc) fts>>) /\
    (<<TRACE: List.Forall2 (fun em fem => tevent_map_weak f (snd fem) (snd em)) tr ftr>>) /\
    (<<GOOD: good_future tm mem1 e1.(Thread.memory)>>) /\
    (<<SC: e1.(Thread.sc) = sc>>) /\
    (<<PROMCONSISTENT: Local.promise_consistent e1.(Thread.local)>>) /\
    (__guard__((exists st',
                   (<<LOCAL: Local.failure_step e1.(Thread.local)>>) /\
                   (<<FAILURE: Language.step lang ProgramEvent.failure (@Thread.state lang e1) st'>>)) \/
               ((<<PROMISES: e1.(Thread.local).(Local.promises) = Memory.bot>>) /\
                (<<WRITES: forall loc from to val released
                                  (GET: Memory.get loc to e0.(Thread.local).(Local.promises) = Some (from, Message.concrete val released)),
                    exists th e,
                      (<<WRITING: promise_writing_event loc from to val released e>>) /\
                      (<<IN: List.In (th, e) ftr>>)>>)))).

Lemma pf_consistent_super_strong_aux2_super_strong
      lang (th: Thread.t lang) tr times
      (WF: Local.wf th.(Thread.local) th.(Thread.memory))
      (MEM: Memory.closed th.(Thread.memory))
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
  { unguard. des.
    { inv LOCAL0. ss. }
    { ss. eapply Local.bot_promise_consistent; eauto. }
  }
  { ss. unguard. des; eauto. right. splits; auto.
    i. eapply steps_promise_decrease_promise_writing_event in STEPS1; eauto.
    des; eauto. ss. erewrite PROMISES in *. erewrite Memory.bot_get in *. ss. }
Qed.


Lemma pf_consistent_super_strong_not_easy lang (th: Thread.t lang)
      tr times
      (LOCAL: Local.wf th.(Thread.local) th.(Thread.memory))
      (MEM: Memory.closed th.(Thread.memory))
      (CONSISTENT: pf_consistent_super_strong_easy th tr times)
  :
    pf_consistent_super_strong th tr times.
Proof.
  eapply pf_consistent_super_strong_aux2_super_strong; eauto.
  eapply pf_consistent_super_strong_aux_aux2; eauto.
  eapply pf_consistent_super_strong_easy_aux; eauto.
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
  eapply pf_consistent_flex_super_strong_easy in CONSISTENT0; eauto. des.
  eapply pf_consistent_super_strong_not_easy in CONSISTENT; eauto.
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

Lemma promises_bot_certify_nil times lang (th: Thread.t lang)
      (PROMISES: th.(Thread.local).(Local.promises) = Memory.bot)
  :
    pf_consistent_super_strong th [] times.
Proof.
  ii. eexists [], _, bot3. esplits; eauto.
  { ii. ss. }
  { ii. ss. }
  { ii. ss. }
  { refl. }
  { eapply Local.bot_promise_consistent; eauto. }
  { right. ss. splits; auto. i.
    rewrite PROMISES in *. erewrite Memory.bot_get in *. ss. }
Qed.

Lemma failure_certify_nil times lang (th: Thread.t lang) st'
      (FAILURE: Language.step lang ProgramEvent.failure (@Thread.state lang th) st')
      (LOCAL: Local.failure_step th.(Thread.local))
  :
    pf_consistent_super_strong th [] times.
Proof.
  ii. eexists [], _, bot3. esplits; eauto.
  { ii. ss. }
  { ii. ss. }
  { ii. ss. }
  { refl. }
  { inv LOCAL. ss. }
  { left. ss. esplits; eauto. }
Qed.

Lemma certify_nil_promises_bot_or_failure times lang (th: Thread.t lang)
      (CONSISTENT: pf_consistent_super_strong th [] times)
      (CLOSED: Memory.closed th.(Thread.memory))
      (LOCAL: Local.wf (Thread.local th) (Thread.memory th))
  :
    (<<PROMISES: th.(Thread.local).(Local.promises) = Memory.bot>>) \/
    exists st',
      (<<FAILURE: Language.step lang ProgramEvent.failure (@Thread.state lang th) st'>>) /\
      (<<LOCAL: Local.failure_step th.(Thread.local)>>).
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
      max_tgt
      (MAXTGT: concrete_promise_max_timemap mem_tgt lc_tgt.(Local.promises) max_tgt)
  :
    exists tr_good f_good,
      (<<MAPLT: mapping_map_lt f_good>>) /\
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
  intros [tr_good [e1_good [f_good [STEPSGOOD [EVENTSGOOD [MAPLTGOOD [IDENTGOOD [BOUNDGOOD [TRACEGOOD [GOODFUTURE [SCGOOD GOODEND]]]]]]]]]]]. des.
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
  { eapply local_map_incr; eauto. eapply ident_map_lt; eauto. }
  { eauto. }
  { eapply mapping_map_lt_collapsable_unwritable; eauto. eapply ident_map_lt. }
  { eapply ident_map_timemap. }
  { refl. }
  i. des.
  eexists ftr0, _, (fun loc ts0 ts2 => exists ts1, <<TS0: f_good loc ts1 ts0>> /\ <<TS1: f0 loc ts1 ts2>>).
  esplits; eauto; ss.
  { eapply List.Forall_forall. i. eapply list_Forall2_in in H; eauto. des.
    eapply List.Forall_forall in IN; eauto. ss. des. destruct a, x. ss.
    inv EVENT; splits; ss.
    { inv KIND; ss. inv MSG0; ss. inv MSG; ss. inv MAP1; ss. }
    { inv FROM. inv TO. auto. }
    { inv FROM. inv TO. auto. }
    { inv FROM. inv TO. auto. }
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
  { clear GOODEND0. unguard. des.
    { left. esplits; eauto. eapply failure_step_map; eauto.
      { eapply ident_map_le. }
      { eapply ident_map_eq. }
    }
    { inv LOCAL0. right. rewrite PROMISES in *.
      eapply bot_promises_map in PROMISES0; eauto. }
  }
Qed.
