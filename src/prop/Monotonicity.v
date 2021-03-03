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
Require Import PFConsistentStrong.

Set Implicit Arguments.

Fixpoint times_join (ts: list Time.t): Time.t :=
  match ts with
  | [] => Time.bot
  | thd::ttl => Time.join thd (times_join ttl)
  end.

Lemma times_join_max ts t (IN: List.In t ts):
  Time.le t (times_join ts).
Proof.
  revert t IN. induction ts; ss.
  i. des; subst.
  - eapply Time.join_l.
  - eapply IHts in IN. etransitivity; eauto. eapply Time.join_r.
Qed.

Variant sim_event: ThreadEvent.t -> ThreadEvent.t -> Prop :=
| sim_event_promise
    loc from to msg kind
  :
    sim_event
      (ThreadEvent.promise loc from to msg kind)
      (ThreadEvent.promise loc from to msg kind)
| sim_event_read
    loc to val released released' ordr
    (RELEASEDLE: View.opt_le released released')
  :
    sim_event
      (ThreadEvent.read loc to val released ordr)
      (ThreadEvent.read loc to val released' ordr)
| sim_event_write
    loc from to val released released' ordw
    (RELEASEDLE: View.opt_le released released')
  :
    sim_event
      (ThreadEvent.write loc from to val released ordw)
      (ThreadEvent.write loc from to val released' ordw)
| sim_event_update
    loc from to valr valw releasedr releasedr'
    releasedw releasedw' ordr ordw
    (RELEASEDRLE: View.opt_le releasedr releasedr')
    (RELEASEDWLE: View.opt_le releasedw releasedw')
  :
    sim_event
      (ThreadEvent.update loc from to valr valw releasedr releasedw ordr ordw)
      (ThreadEvent.update loc from to valr valw releasedr' releasedw' ordr ordw)
| sim_event_fence
    or ow
  :
    sim_event
      (ThreadEvent.fence or ow)
      (ThreadEvent.fence or ow)
| sim_event_syscall
    e
  :
    sim_event
      (ThreadEvent.syscall e)
      (ThreadEvent.syscall e)
| sim_event_silent
  :
    sim_event
      (ThreadEvent.silent)
      (ThreadEvent.silent)
| sim_event_failure
  :
    sim_event
      (ThreadEvent.failure)
      (ThreadEvent.failure)
.

Lemma ident_map_sim_event (f: Loc.t -> Time.t -> Time.t -> Prop)
      (IDENT: forall loc to fto (MAP: f loc to fto), to = fto)
      e fe
      (EVENT: tevent_map f e fe)
  :
    sim_event e fe.
Proof.
  assert (MSG: forall msg fmsg, msg_map f msg fmsg -> msg = fmsg).
  { i. inv H; auto. eapply opt_view_ident_map in MAP; auto.
    subst. auto. }
  inv EVENT.
  - eapply IDENT in FROM. eapply IDENT in TO.
    eapply MSG in MSG0. subst. inv KIND.
    + econs; eauto.
    + apply IDENT in TO. eapply MSG in MSG0. subst.
      econs; eauto.
    + eapply MSG in MSG0. subst.
      econs; eauto.
    + econs; eauto.
  - eapply IDENT in TO.
    eapply opt_view_ident_map in RELEASED; auto. subst. econs; eauto.
  - eapply IDENT in FROM. eapply IDENT in TO.
    eapply opt_view_ident_map in RELEASED; auto. subst. econs; eauto.
  - eapply IDENT in FROM. eapply IDENT in TO.
    eapply opt_view_ident_map in RELEASEDR; auto. eapply opt_view_ident_map in RELEASEDW; auto.
    subst. econs; eauto.
  - econs; eauto.
  - econs; eauto.
  - econs; eauto.
  - econs; eauto.
Qed.


Lemma promise_monotonicity lang0 lang1 st0 st1 st2 lc0 lc1 lc2 sc0 sc2 mem0 mem2 loc to tr0
      (CONSISTENT: Thread.consistent (@Thread.mk lang0 st0 lc0 sc0 mem0))
      (LOCAL0: Local.wf lc0 mem0)
      (LOCAL1: Local.wf lc1 mem0)
      (DISJOINT: Local.disjoint lc0 lc1)
      (SC: Memory.closed_timemap sc0 mem0)
      (MEM: Memory.closed mem0)
      (PROMISE: concrete_promised lc0.(Local.promises) loc to)
      (STEPS0: Trace.steps tr0 (@Thread.mk lang1 st1 lc1 sc0 mem0) (@Thread.mk _ st2 lc2 sc2 mem2))
  :
    (exists tr1 st0' lc0' sc0' mem0' we tr0' val lc2' sc2' mem2',
        (<<STEPS1: Trace.steps tr1 (@Thread.mk _ st0 lc0 sc0 mem0) (@Thread.mk _ st0' lc0' sc0' mem0')>>) /\
        (<<CONSISTENT: Thread.consistent (@Thread.mk _ st0' lc0' sc0' mem0')>>) /\
        (<<FINAL: final_event_trace we tr1>>) /\
        (<<WRITE: relaxed_writing_event loc to val we>>) /\
        (<<STEPS0: Trace.steps tr0' (@Thread.mk lang1 st1 lc1 sc0' mem0') (@Thread.mk _ st2 lc2' sc2' mem2')>>) /\
        (<<TRACE: List.Forall2 (fun '(_, e0) '(_, e1) => sim_event e1 e0) tr0 tr0'>>)) \/
    (Thread.steps_failure (@Thread.mk _ st0 lc0 sc0 mem0)).
Proof.
  inv PROMISE.
  hexploit consistent_pf_consistent_super_strong; eauto; ss. i. des.
  hexploit (memory_times_wf_exists mem0). i. des.
  hexploit (@trace_times_list_exists tr0). i. des.
  set (tm := fun loc => Time.incr (Time.join (times_join (times loc)) (Memory.max_ts loc mem0))).
  set (f := (fun loc ts fts => ts = fts /\ Time.lt ts (tm loc))).
  assert (MAPLT: mapping_map_lt f).
  { unfold f. ii. des; subst; auto. }
  assert (IDENT: map_ident_in_memory f mem0).
  { ii. split; auto. eapply TimeFacts.le_lt_lt; eauto.
    eapply TimeFacts.le_lt_lt.
    { eapply Time.join_r. }
    { eapply Time.incr_spec. }
  }
  hexploit concrete_promise_max_timemap_exists.
  { eapply MEM. } i. des.
  eapply pf_consistent_super_strong_mon
    with (certimes1 := certimes \2/ times_mem \2/ fun _ ts => exists n, incr_time_seq n = ts) in CONSISTENT0; eauto.
  hexploit pf_consistent_super_strong_promises_list_exists; eauto.
  { i. right. eauto. }
  i. des. unfold pf_consistent_super_strong_promises_list in *. des. ss.
  hexploit COMPLETE; eauto. i. eapply List.in_split in H. des. subst.
  hexploit CONSISTENT1; eauto.
  { refl. }
  { ii. exploit MWF; eauto.  i. des. splits; eauto. }
  i. clear CONSISTENT1. des.
  - left. eapply max_good_future_map in GOOD; eauto; cycle 1.
    { i. eapply TimeFacts.le_lt_lt.
      - eapply Time.join_r.
      - eapply Time.incr_spec. }
    hexploit Trace.steps_future; eauto. i. des. ss.
    hexploit Trace.steps_disjoint; eauto. i. des.
    hexploit (@trace_steps_map f).
    { unfold f. ii. des; subst; auto. }
    { unfold f. ii. split; auto. eapply TimeFacts.le_lt_lt.
      - eapply Time.bot_spec.
      - eapply Time.incr_spec.
    }
    { unfold f. ii. des; subst; auto. }
    { instantiate (1:=tr0). eapply wf_time_mapped_mappable.
      { instantiate (1:=fun loc to => List.In to (times loc)).
        - eapply List.Forall_impl; eauto. ss. }
      { i. ss. exists to0. split; auto. eapply TimeFacts.le_lt_lt.
        { eapply times_join_max; eauto. }
        { eapply TimeFacts.le_lt_lt.
          { eapply Time.join_l. }
          { eapply Time.incr_spec. }
        }
      }
    }
    { eapply STEPS0. }
    { ss. }
    { ss. }
    { ss. }
    { eapply LOCAL1. }
    { eapply WF. }
    { eauto. }
    { eauto. }
    { eauto. }
    { eauto. }
    { eapply map_ident_in_memory_local; eauto. }
    { eauto. }
    { eapply mapping_map_lt_collapsable_unwritable; eauto. }
    { eapply map_ident_in_memory_closed_timemap; eauto. }
    { rewrite SC0. refl. }
    i. des. destruct e1. ss. esplits; try eassumption.
    { eapply pf_consistent_super_strong_consistent; eauto. }
    eapply list_Forall2_impl; eauto. i. ss. des; auto.
    { clear - EVENT. destruct a, b. ss. eapply ident_map_sim_event; eauto.
      i. eapply MAP. }
  - right. unfold Thread.steps_failure.
    unguard. des. destruct e1. ss. esplits.
    { eapply Trace.silent_steps_tau_steps; eauto.
      eapply List.Forall_impl; eauto. i. ss. des; auto. }
    { econs 2. econs; eauto. }
Qed.
