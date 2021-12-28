Require Import RelationClasses.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import Loc.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Language.

Require Import Event.
Require Import Time.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import MemoryFacts.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.

Require Import Cover.
Require Import MemorySplit.
Require Import MemoryMerge.
Require Import FulfillStep.
Require Import MemoryProps.

Require Import gSimAux.
Require Import LowerMemory.
Require Import JoinedView.

Set Implicit Arguments.

Variant max_readable (mem prom: Memory.t) (loc: Loc.t) (ts: Time.t) (val: Const.t) (released: option View.t): Prop :=
| max_readable_intro
    from
    (GET: Memory.get loc ts mem = Some (from, Message.concrete val released))
    (NONE: Memory.get loc ts prom = None)
    (MAX: forall ts' from' msg
                 (TS: Time.lt ts ts')
                 (GET: Memory.get loc ts' mem = Some (from', msg))
                 (MSG: msg <> Message.reserve),
        Memory.get loc ts' prom = Some (from', msg))
.

Lemma max_readable_inj mem prom loc ts0 ts1 val0 val1 released0 released1
      (MAX0: max_readable mem prom loc ts0 val0 released0)
      (MAX1: max_readable mem prom loc ts1 val1 released1)
  :
    (<<TS: ts0 = ts1>>) /\ (<<VAL: val0 = val1>>) /\ (<<RELEASED: released0 = released1>>).
Proof.
  inv MAX0. inv MAX1.
  assert (ts0 = ts1).
  { apply TimeFacts.antisym.
    { destruct (Time.le_lt_dec ts0 ts1); auto.
      hexploit MAX0; eauto; ss.
      i. clarify.
    }
    { destruct (Time.le_lt_dec ts1 ts0); auto.
      hexploit MAX; eauto; ss.
      i. clarify.
    }
  }
  subst. split; auto. clarify.
Qed.

Lemma read_tview_max tvw loc released
      (WF: TView.wf tvw)
  :
    TView.read_tview tvw loc (View.pln (TView.cur tvw) loc) released Ordering.na = tvw.
Proof.
  unfold TView.read_tview. des_ifs. ss.
  rewrite ! View.le_join_l.
  { destruct tvw; auto. }
  { apply View.singleton_rw_spec.
    { apply WF. }
    { transitivity (View.rlx (TView.cur tvw) loc).
      { apply WF. }
      { apply WF. }
    }
  }
  { apply View.bot_spec. }
  { apply View.singleton_rw_spec.
    { apply WF. }
    { apply WF. }
  }
  { apply View.bot_spec. }
Qed.


Lemma max_readable_view_mon mem prom tvw0 tvw1 loc ts val released
      (MAX: max_readable mem prom loc ts val released)
      (TS: tvw0.(TView.cur).(View.pln) loc = ts)
      (TVIEW: TView.le tvw0 tvw1)
      (CONS: Local.promise_consistent (Local.mk tvw1 prom))
      (WF: Local.wf (Local.mk tvw1 prom) mem)
  :
    max_readable mem prom loc (tvw1.(TView.cur).(View.pln) loc) val released.
Proof.
  subst. replace (tvw1.(TView.cur).(View.pln) loc) with (tvw0.(TView.cur).(View.pln) loc); auto.
  apply TimeFacts.antisym.
  { apply TVIEW. }
  destruct (Time.le_lt_dec (tvw1.(TView.cur).(View.pln) loc) (tvw0.(TView.cur).(View.pln) loc)); auto.
  inv MAX. inv WF.
  inv TVIEW_CLOSED. inv CUR. specialize (PLN loc). des.
  exploit MAX0; eauto; ss.
  i. exploit CONS; eauto; ss. i.
  exfalso. eapply Time.lt_strorder.
  eapply TimeFacts.lt_le_lt; [eapply x0|]. eapply TVIEW_WF.
Qed.

Lemma non_max_readable_future mem0 mem1 prom tvw loc ts
      (MAX: forall val released, ~ max_readable mem0 prom loc ts val released)
      (TS: tvw.(TView.cur).(View.pln) loc = ts)
      (FUTURE: Memory.future_weak mem0 mem1)
      (WF: Local.wf (Local.mk tvw prom) mem0)
  :
    forall val released, ~ max_readable mem1 prom loc ts val released.
Proof.
  subst. ii. inv H.
  inv WF. inv TVIEW_CLOSED. inv CUR. specialize (PLN loc). des. ss.
  hexploit Memory.future_weak_get1; eauto; ss. i. des.
  inv MSG_LE. eapply MAX. econs; eauto. i.
  hexploit Memory.future_weak_get1; eauto; ss. i. des.
  exploit MAX0; eauto.
  { inv MSG_LE; ss. }
  i. eapply PROMISES in x. clarify. auto.
Qed.


Lemma max_readable_read_only mem prom tvw loc ts val released
      ts' val' released' lc
      (MAX: max_readable mem prom loc ts val released)
      (TS: tvw.(TView.cur).(View.pln) loc = ts)
      (READ: Local.read_step (Local.mk tvw prom) mem loc ts' val' released' Ordering.na lc)
      (CONS: Local.promise_consistent lc)
      (WF: Local.wf (Local.mk tvw prom) mem)
  :
    (<<TS: ts' = ts>>) /\ (<<VAL: Const.le val' val>>) /\ (<<RELEASED: released' = released>>) /\ (<<LOCAL: lc = Local.mk tvw prom>>).
Proof.
  inv READ. ss. assert (ts' = tvw.(TView.cur).(View.pln) loc).
  { apply TimeFacts.antisym.
    { destruct (Time.le_lt_dec ts' (tvw.(TView.cur).(View.pln) loc)); auto.
      inv MAX. hexploit MAX0; eauto; ss.
      i. exploit CONS; eauto; ss. i.
      des_ifs. ss.
      change (Ordering.le Ordering.relaxed Ordering.na) with false in x.
      ss. rewrite TimeMap.le_join_l in x.
      2: { eapply TimeMap.bot_spec. }
      unfold TimeMap.join, TimeMap.singleton in x.
      setoid_rewrite LocFun.add_spec_eq in x.
      exfalso. eapply Time.lt_strorder.
      eapply TimeFacts.lt_le_lt; [eapply x|].
      eapply Time.join_r.
    }
    { inv READABLE. auto. }
  }
  subst. inv MAX. clarify. splits; auto. f_equal.
  apply read_tview_max. apply WF.
Qed.

Lemma max_readable_not_racy mem prom tvw loc ts val released ord
      (MAX: max_readable mem prom loc ts val released)
      (TS: tvw.(TView.cur).(View.pln) loc = ts)
      (RACE: Local.is_racy (Local.mk tvw prom) mem loc ord)
      (WF: Local.wf (Local.mk tvw prom) mem)
  :
    False.
Proof.
  inv RACE. inv MAX. ss. exploit MAX0; eauto.
  i. ss. clarify.
Qed.

Lemma max_readable_not_read_race mem prom tvw loc ts val released
      val' ord
      (MAX: max_readable mem prom loc ts val released)
      (TS: tvw.(TView.cur).(View.pln) loc = ts)
      (READ: Local.racy_read_step (Local.mk tvw prom) mem loc val' ord)
      (WF: Local.wf (Local.mk tvw prom) mem)
  :
    False.
Proof.
  inv READ. eapply max_readable_not_racy; eauto.
Qed.

Lemma max_readable_not_write_race mem prom tvw loc ts val released ord
      (MAX: max_readable mem prom loc ts val released)
      (TS: tvw.(TView.cur).(View.pln) loc = ts)
      (WRITE: Local.racy_write_step (Local.mk tvw prom) mem loc ord)
      (WF: Local.wf (Local.mk tvw prom) mem)
  :
    False.
Proof.
  inv WRITE. eapply max_readable_not_racy; eauto.
Qed.

Lemma max_readable_read mem prom tvw loc ts val0 val1 released
      (MAX: max_readable mem prom loc ts val1 released)
      (TS: tvw.(TView.cur).(View.pln) loc = ts)
      (WF: Local.wf (Local.mk tvw prom) mem)
      (VAL: Const.le val0 val1)
  :
    exists released,
      (<<READ: Local.read_step (Local.mk tvw prom) mem loc ts val0 released Ordering.na (Local.mk tvw prom)>>).
Proof.
  inv MAX. esplits. econs; eauto.
  { econs; ss. refl. }
  ss. f_equal. rewrite read_tview_max; auto. apply WF.
Qed.


Variant fulfilled_memory (loc: Loc.t) (mem0 mem1: Memory.t): Prop :=
| fulfilled_memory_intro
    (OTHER: forall loc' (NEQ: loc' <> loc) to,
        Memory.get loc' to mem1 = Memory.get loc' to mem0)
    (GET: forall to from msg1
                 (GET: Memory.get loc to mem1 = Some (from, msg1)),
        exists msg0,
          (<<GET: Memory.get loc to mem0 = Some (from, msg0)>>) /\
          (<<MSG_LE: Message.le msg1 msg0>>))
.

Program Instance fulfilled_memory_PreOrder loc: PreOrder (fulfilled_memory loc).
Next Obligation.
Proof.
  ii. econs; eauto. i. exists msg1. splits; auto. refl.
Qed.
Next Obligation.
Proof.
  ii. inv H. inv H0. econs.
  { i. transitivity (Memory.get loc' to y); eauto. }
  { i. exploit GET0; eauto. i. des.
    exploit GET; eauto. i. des. esplits; eauto. etrans; eauto. }
Qed.

Lemma fulfilled_memory_lower loc from to msg0 msg1 mem0 mem1
      (LOWER: Memory.lower mem0 loc from to msg0 msg1 mem1)
  :
    fulfilled_memory loc mem0 mem1.
Proof.
  econs.
  { i. erewrite (@Memory.lower_o mem1); eauto. des_ifs. des; clarify. }
  { i. erewrite (@Memory.lower_o mem1) in GET; eauto. des_ifs.
    { ss. des; clarify.
      eapply Memory.lower_get0 in LOWER. des. esplits; eauto. }
    { ss. des; clarify. esplits; eauto. refl. }
  }
Qed.

Lemma fulfilled_memory_cancel loc from to msg mem0 mem1
      (CANCEL: Memory.remove mem0 loc from to msg mem1)
  :
    fulfilled_memory loc mem0 mem1.
Proof.
  econs.
  { i. erewrite (@Memory.remove_o mem1); eauto. des_ifs. des; clarify. }
  { i. erewrite (@Memory.remove_o mem1) in GET; eauto. des_ifs.
    ss. des; clarify. esplits; eauto. refl. }
Qed.

Lemma fulfilled_memory_max_ts loc mem0 mem1
      (INHABITED: Memory.inhabited mem1)
      (FULFILLED: fulfilled_memory loc mem0 mem1)
  :
    Time.le (Memory.max_ts loc mem1) (Memory.max_ts loc mem0).
Proof.
  specialize (INHABITED loc).
  apply Memory.max_ts_spec in INHABITED. des.
  apply FULFILLED in GET. des.
  apply Memory.max_ts_spec in GET0. des. auto.
Qed.

Lemma fulfilled_memory_get0 loc mem0 mem1
      (FULFILLED: fulfilled_memory loc mem0 mem1)
      l to from msg1
      (GET: Memory.get l to mem1 = Some (from, msg1))
  :
    exists msg0,
      (<<GET: Memory.get l to mem0 = Some (from, msg0)>>) /\
      (<<MSG_LE: Message.le msg1 msg0>>).
Proof.
  destruct (Loc.eq_dec l loc).
  { subst. eapply FULFILLED in GET. des. eauto. }
  { inv FULFILLED. rewrite OTHER in GET; auto.
    esplits; eauto. refl. }
Qed.

Lemma fulfilled_memory_get1 loc mem0 mem1
      (FULFILLED: fulfilled_memory loc mem0 mem1)
      (FUTURE: Memory.future mem0 mem1)
      l to from msg0
      (GET: Memory.get l to mem0 = Some (from, msg0))
      (RESERVE: msg0 <> Message.reserve)
  :
    exists msg1,
      (<<GET: Memory.get l to mem1 = Some (from, msg1)>>) /\
      (<<MSG_LE: Message.le msg1 msg0>>).
Proof.
  dup GET. eapply Memory.future_get1 in GET; eauto. des.
  dup GET1. destruct (Loc.eq_dec l loc).
  { subst. eapply FULFILLED in GET2. des. clarify. eauto. }
  { inv FULFILLED. rewrite OTHER in GET2; auto. clarify. eauto. }
Qed.

Inductive cancel_future_memory (loc: Loc.t) : Memory.t -> Memory.t -> Memory.t -> Memory.t -> Prop :=
| cancel_future_memory_base
    prom0 mem0
  :
    cancel_future_memory loc prom0 mem0 prom0 mem0
| cancel_future_memory_step
    prom0 mem0 prom1 mem1 prom2 mem2
    from to
    (CANCEL: Memory.promise prom0 mem0 loc from to Message.reserve prom1 mem1 Memory.op_kind_cancel)
    (FUTURE: cancel_future_memory loc prom1 mem1 prom2 mem2)
  :
    cancel_future_memory loc prom0 mem0 prom2 mem2
.

Lemma cancel_future_reserve_future loc prom0 mem0 prom1 mem1
      (CANCEL: cancel_future_memory loc prom0 mem0 prom1 mem1)
  :
    reserve_future_memory prom0 mem0 prom1 mem1.
Proof.
  induction CANCEL; eauto.
  { econs 1; eauto. }
  { econs 2; eauto. }
Qed.

Variant unchanged_loc_memory (loc: Loc.t) (mem0 mem1: Memory.t): Prop :=
| unchanged_loc_memory_intro
    (UNCH: forall to, Memory.get loc to mem1 = Memory.get loc to mem0)
.

Global Program Instance unchanged_loc_memory_Equivalence loc:
  Equivalence (unchanged_loc_memory loc).
Next Obligation.
Proof.
  ii. econs. auto.
Qed.
Next Obligation.
Proof.
  ii. inv H. econs; eauto.
Qed.
Next Obligation.
Proof.
  ii. inv H. inv H0. econs. i. etrans; eauto.
Qed.

Lemma unchanged_loc_max_readable prom0 mem0 prom1 mem1 loc
      (MEM: unchanged_loc_memory loc mem0 mem1)
      (PROM: unchanged_loc_memory loc prom0 prom1)
  :
    forall ts val released,
      max_readable prom0 mem0 loc ts val released
      <->
      max_readable prom1 mem1 loc ts val released.
Proof.
  inv MEM. inv PROM.
  i. split; i.
  { inv H. econs.
    { rewrite UNCH0. eauto. }
    { rewrite UNCH. eauto. }
    { i. rewrite UNCH. rewrite UNCH0 in GET0; eauto. }
  }
  { inv H. econs.
    { rewrite <- UNCH0. eauto. }
    { rewrite <- UNCH. eauto. }
    { i. rewrite <- UNCH. rewrite <- UNCH0 in GET0; eauto. }
  }
Qed.

Lemma add_unchanged_loc mem0 mem1 loc from to msg loc0
      (ADD: Memory.add mem0 loc from to msg mem1)
      (NEQ: loc0 <> loc)
  :
    unchanged_loc_memory loc0 mem0 mem1.
Proof.
  econs. i. erewrite (@Memory.add_o mem1 mem0); eauto.
  des_ifs. ss. des; clarify.
Qed.

Lemma split_unchanged_loc mem0 mem1 loc ts0 ts1 ts2 msg0 msg1 loc0
      (SPLIT: Memory.split mem0 loc ts0 ts1 ts2 msg0 msg1 mem1)
      (NEQ: loc0 <> loc)
  :
    unchanged_loc_memory loc0 mem0 mem1.
Proof.
  econs. i. erewrite (@Memory.split_o mem1 mem0); eauto.
  des_ifs; ss; des; clarify.
Qed.

Lemma lower_unchanged_loc mem0 mem1 loc from to msg0 msg1 loc0
      (LOWER: Memory.lower mem0 loc from to msg0 msg1 mem1)
      (NEQ: loc0 <> loc)
  :
    unchanged_loc_memory loc0 mem0 mem1.
Proof.
  econs. i. erewrite (@Memory.lower_o mem1 mem0); eauto.
  des_ifs; ss; des; clarify.
Qed.

Lemma remove_unchanged_loc mem0 mem1 loc from to msg loc0
      (REMOVE: Memory.remove mem0 loc from to msg mem1)
      (NEQ: loc0 <> loc)
  :
    unchanged_loc_memory loc0 mem0 mem1.
Proof.
  econs. i. erewrite (@Memory.remove_o mem1 mem0); eauto.
  des_ifs; ss; des; clarify.
Qed.

Lemma promise_unchanged_loc prom0 mem0 loc from to msg prom1 mem1 kind
      loc0
      (PROMISE: Memory.promise prom0 mem0 loc from to msg prom1 mem1 kind)
      (NEQ: loc0 <> loc)
  :
    (<<MEM: unchanged_loc_memory loc0 mem0 mem1>>) /\
    (<<PROM: unchanged_loc_memory loc0 prom0 prom1>>).
Proof.
  inv PROMISE.
  { splits.
    { eapply add_unchanged_loc; eauto. }
    { eapply add_unchanged_loc; eauto. }
  }
  { splits.
    { eapply split_unchanged_loc; eauto. }
    { eapply split_unchanged_loc; eauto. }
  }
  { splits.
    { eapply lower_unchanged_loc; eauto. }
    { eapply lower_unchanged_loc; eauto. }
  }
  { splits.
    { eapply remove_unchanged_loc; eauto. }
    { eapply remove_unchanged_loc; eauto. }
  }
Qed.

Lemma write_unchanged_loc prom0 mem0 loc from to msg prom1 mem1 kind
      loc0
      (WRITE: Memory.write prom0 mem0 loc from to msg prom1 mem1 kind)
      (NEQ: loc0 <> loc)
  :
    (<<MEM: unchanged_loc_memory loc0 mem0 mem1>>) /\
    (<<PROM: unchanged_loc_memory loc0 prom0 prom1>>).
Proof.
  inv WRITE. eapply promise_unchanged_loc in PROMISE; eauto.
  eapply remove_unchanged_loc in REMOVE; eauto.
  des. splits; auto. etrans; eauto.
Qed.

Lemma cancel_future_unchanged_loc prom0 mem0 prom1 mem1 loc loc0
      (CANCEL: cancel_future_memory loc prom0 mem0 prom1 mem1)
      (NEQ: loc0 <> loc)
  :
    (<<MEM: unchanged_loc_memory loc0 mem0 mem1>>) /\
    (<<PROM: unchanged_loc_memory loc0 prom0 prom1>>).
Proof.
  induction CANCEL.
  { splits; refl. }
  { eapply promise_unchanged_loc in CANCEL; eauto. des. splits.
    { etrans; eauto. }
    { etrans; eauto. }
  }
Qed.

Lemma na_write_unchanged_loc ts prom0 mem0 loc from to val prom1 mem1 kinds msgs kind
      loc0
      (WRITE: Memory.write_na ts prom0 mem0 loc from to val prom1 mem1 kinds msgs kind)
      (NEQ: loc0 <> loc)
  :
    (<<MEM: unchanged_loc_memory loc0 mem0 mem1>>) /\
    (<<PROM: unchanged_loc_memory loc0 prom0 prom1>>).
Proof.
  induction WRITE.
  { eapply write_unchanged_loc; eauto. }
  { hexploit IHWRITE; eauto. i. des.
    eapply write_unchanged_loc in WRITE_EX; eauto.
    des. splits; etrans; eauto.
  }
Qed.

Lemma remove_reserves_loc prom0 mem0 loc
      (MLE: Memory.le prom0 mem0)
      (FIN: Memory.finite prom0)
      (INHABITED: Memory.inhabited mem0)
  :
    exists prom1 mem1,
      (<<RESERVE: cancel_future_memory loc prom0 mem0 prom1 mem1>>) /\
      (<<MEM: fulfilled_memory loc mem0 mem1>>) /\
      (<<RESERVE: forall to from msg
                         (GET: Memory.get loc to prom1 = Some (from, msg)),
          msg <> Message.reserve>>) /\
      (<<PROMISES: forall loc' to,
          Memory.get loc' to prom1 =
          if Loc.eq_dec loc' loc
          then match (Memory.get loc' to prom0) with
               | Some (from, Message.reserve) => None
               | x => x
               end
          else Memory.get loc' to prom0>>) /\
      (<<INHABITED: Memory.inhabited mem1>>).
Proof.
  hexploit (wf_cell_msgs_exists (prom0 loc)). i. des. clear WFMSGS.
  hexploit (@list_filter_exists _ (fun '(_, _, msg) => msg = Message.reserve) l).
  i. des.
  assert (exists rs,
             forall from to (GET: Memory.get loc to prom0 = Some (from, Message.reserve)),
               List.In to rs).
  { exists (List.map (snd <*> fst) l').  i.
    hexploit (proj1 (COMPLETE0 (from, to, Message.reserve))).
    { split; auto. apply COMPLETE. auto. }
    i. eapply List.in_map with (f:=(snd <*> fst)) in H. auto.
  }
  clear l l' COMPLETE COMPLETE0. des. ginduction rs.
  { i. exists prom0, mem0. splits.
    { econs. }
    { refl. }
    { ii. subst. eapply H in GET; eauto. }
    { i. des_ifs. hexploit H; eauto. ss. }
    { auto. }
  }
  { i. destruct (classic (exists from, Memory.get loc a prom0 = Some (from, Message.reserve))).
    { des.
      hexploit (@Memory.remove_exists prom0 loc from a Message.reserve); auto.
      i. des.
      hexploit (@Memory.remove_exists_le prom0 mem0); eauto. i. des.
      assert (REMOVE: Memory.promise prom0 mem0 loc from a Message.reserve mem2 mem1 Memory.op_kind_cancel).
      { econs; eauto. }
      hexploit (IHrs mem2 mem1 loc); auto.
      { eapply promise_memory_le; eauto. }
      { eapply Memory.remove_finite; eauto. }
      { apply Memory.promise_inhabited in REMOVE; auto. }
      { i. erewrite Memory.remove_o in GET; eauto. des_ifs.
        ss. des; clarify. apply H in GET. des; clarify. }
      { i. des. exists prom1, mem3. splits.
        { econs; eauto. }
        { etrans; eauto. eapply fulfilled_memory_cancel; eauto. }
        { auto. }
        { i. rewrite PROMISES.
          erewrite (@Memory.remove_o mem2); eauto.
          des_ifs; ss; des; clarify.
        }
        { auto. }
      }
    }
    { eapply (IHrs prom0 mem0 loc); eauto. i.
      hexploit H; eauto. i. ss. des; clarify.
      exfalso. eapply H0. eauto.
    }
  }
Qed.

Lemma max_readable_write_na mem0 prom0 loc ts from to val1
      (WF: Memory.le prom0 mem0)
      (BOT: Memory.bot_none prom0)
      (RESERVE: forall to' from' msg'
                       (GET: Memory.get loc to' prom0 = Some (from', msg')),
          (<<RESERVE: msg' <> Message.reserve>>) /\
          (<<NONE: forall val released (MSG: msg' = Message.concrete val released),
              released = None>>) /\
          (<<TS: Time.lt ts to'>>))
      (CLOSED: __guard__ (exists from' msg',
                             (<<GET: Memory.get loc ts mem0 = Some (from', msg')>>) /\ (<<RESERVE: msg' <> Message.reserve>>)))
      (FROM: Time.le (Memory.max_ts loc mem0) from)
      (TO: Time.lt from to)
      (MEM: Memory.closed mem0)
  :
    exists mem1 prom1 mem2 msgs ks,
      (<<MEM: fulfilled_memory loc mem0 mem1>>) /\
      (<<MLE: mem1 = mem0>>) /\
      (<<ADD: Memory.add mem1 loc from to (Message.concrete val1 None) mem2>>) /\
      (<<PROMISES: forall loc' ts',
          Memory.get loc' ts' prom1 =
          if Loc.eq_dec loc' loc
          then None
          else Memory.get loc' ts' prom0>>) /\
      (<<WRITE: Memory.write_na ts prom0 mem0 loc from to val1 prom1 mem2 msgs ks Memory.op_kind_add>>) /\
      (<<NONE: Memory.get loc to prom1 = None>>) /\
      (<<MAX: Memory.max_ts loc mem2 = to>>).
Proof.
  hexploit (wf_cell_msgs_exists (prom0 loc)). i. des.
  red in WFMSGS. des.
  cut (List.Forall (fun '(from', to', msg) => (<<RESERVE: msg <> Message.reserve>>) /\ (<<NONE: forall val released (MSG: msg = Message.concrete val released),
                                                                                           released = None>>) /\ (<<TS: Time.lt ts to'>>)) l); cycle 1.
  { eapply List.Forall_forall.
    intros [[from' to'] msg]. ii. subst.
    eapply COMPLETE in H. eapply RESERVE in H. auto. }
  clear RESERVE. intros RESERVE.
  ginduction l.
  { i. exists mem0, prom0.
    hexploit (@Memory.add_exists mem0 loc from to (Message.concrete val1 None)); eauto.
    { ii. eapply Memory.max_ts_spec in GET2. des.
      inv LHS. inv RHS. ss. eapply Time.lt_strorder.
      eapply TimeFacts.le_lt_lt.
      { eapply FROM. }
      eapply TimeFacts.lt_le_lt.
      { eapply FROM0. }
      etrans.
      { eapply TO1. }
      auto.
    }
    i. des.
    hexploit (@Memory.add_exists_le prom0 mem0); eauto.
    i. des. exists mem2. esplits; eauto.
    { refl. }
    { i. des_ifs. destruct (Memory.get loc ts' prom0) as [[]|] eqn:EQ; auto.
      exfalso. eapply COMPLETE in EQ. ss. }
    { econs 1.
      { red in CLOSED. des. eapply Memory.max_ts_spec in GET. des.
        eapply TimeFacts.le_lt_lt.
        { eapply MAX. }
        eapply TimeFacts.le_lt_lt.
        { eapply FROM. }
        { eapply TO. }
      }
      { econs.
        { econs; eauto.
          { econs; ss. apply Time.bot_spec. }
          { i. hexploit memory_get_ts_le; [apply GET|]. i.
            apply Memory.max_ts_spec in GET. des.
            eapply Time.lt_strorder.
            eapply TimeFacts.le_lt_lt.
            { eapply H1. }
            eapply TimeFacts.le_lt_lt.
            { eapply MAX. }
            eapply TimeFacts.le_lt_lt.
            { eapply FROM. }
            { auto. }
          }
        }
        { hexploit (@Memory.remove_exists promises2).
          { eapply Memory.add_get0; eauto. }
          i. des. hexploit MemoryMerge.add_remove; [apply H0|apply H1|].
          i. subst. auto.
        }
      }
    }
    { eapply Memory.add_get0; eauto. }
    { dup H. eapply Memory.add_get0 in H. des.
      apply Memory.max_ts_spec in GET0. des.
      apply TimeFacts.antisym; auto.
      erewrite Memory.add_o in GET1; eauto. des_ifs.
      { ss. des; clarify. }
      { ss. des; clarify.
        apply Memory.max_ts_spec in GET1. des.
        etrans; eauto. etrans; eauto. left. auto.
      }
    }
  }
  { i. inv DISJOINT. inv MSGSWF.
    hexploit (proj2 (COMPLETE from0 to0 msg)).
    { left. auto. }
    i. red in H. des.
    { subst. exfalso.
      specialize (BOT loc). unfold Memory.get in BOT. rewrite BOT in H. clarify.
    }
    inv RESERVE. des.
    hexploit (@Memory.lower_exists prom0 loc from0 to0 msg msg); auto.
    { refl. }
    i. des.
    hexploit (@Memory.lower_exists_le prom0 mem0); eauto.
    i. des.
    hexploit (@Memory.remove_exists mem2 loc from0 to0 msg).
    { eapply Memory.lower_get0 in H0. des; auto. }
    i. des.
    assert (WRITE: Memory.write prom0 mem0 loc from0 to0 msg mem3 mem1 (Memory.op_kind_lower msg)).
    { econs; eauto. econs; eauto.
      { inv MEM. exploit CLOSED0.
        { eapply Memory.lower_get0 in H1. des; eauto. }
        i. des. auto.
      }
    }
    hexploit (IHl mem1 mem3 loc to0 from to val1); auto.
    { eapply write_promises_le; eauto. }
    { eapply Memory.write_bot_none; eauto. }
    { red. esplits.
      { eapply Memory.lower_get0 in H1. des; eauto. }
      { auto. }
    }
    { replace (Memory.max_ts loc mem1) with (Memory.max_ts loc mem0); auto.
      dup H1. apply Memory.lower_get0 in H1. des. apply TimeFacts.antisym.
      { apply Memory.max_ts_spec in GET. des.
        eapply Memory.lower_get1 in GET1; eauto. des.
        apply Memory.max_ts_spec in GET2. des. auto. }
      { apply Memory.max_ts_spec in GET0. des.
        erewrite Memory.lower_o in GET1; eauto. des_ifs.
        { ss. des; clarify. apply Memory.max_ts_spec in GET. des; auto. }
        { ss. des; clarify. apply Memory.max_ts_spec in GET1. des; auto. }
      }
    }
    { eapply lower_same_same in H1. subst. auto. }
    { i. split.
      { i. red in H5. setoid_rewrite (@Memory.remove_o mem3) in H5; eauto.
        erewrite (@Memory.lower_o mem2) in H5; eauto. des_ifs. ss. des; clarify.
        apply COMPLETE in H5. des; clarify.
      }
      { i. hexploit (proj2 (COMPLETE from1 to1 msg0)).
        { right. auto. }
        i. red. setoid_rewrite (@Memory.remove_o mem3); eauto.
        erewrite (@Memory.lower_o mem2); eauto. des_ifs. exfalso.
        ss. eapply List.Forall_forall in HD; eauto. ss. des; subst.
        rewrite H in *. clarify. timetac.
      }
    }
    { dup H4. eapply List.Forall_forall. intros [[?from ?to] ?msg] IN. splits.
      { eapply List.Forall_forall in H4; eauto. ss. des; auto. }
      { i. clarify.
        eapply List.Forall_forall in HD; eauto. ss.
        eapply List.Forall_forall in H5; eauto. ss. des.
        eapply NONE0; eauto.
      }
      { eapply List.Forall_forall in HD; eauto. ss.
        eapply List.Forall_forall in H2; eauto. ss. des.
        { subst. eapply List.Forall_forall in H5; eauto. ss. des. inv TS1. }
        { eapply TimeFacts.le_lt_lt; eauto. }
      }
    }
    i. des. esplits.
    { etrans; [|eauto]. eapply fulfilled_memory_lower; eauto. }
    { etrans; eauto. eapply lower_same_same; eauto. }
    { eauto. }
    { i. rewrite PROMISES. des_ifs.
      erewrite (@Memory.remove_o mem3); eauto.
      erewrite (@Memory.lower_o mem2); eauto. des_ifs. ss. des; clarify. }
    { econs 2.
      { instantiate (1:=to0). auto. }
      { instantiate (1:=msg). red. destruct msg; ss; auto.
        right. hexploit NONE; eauto. i. subst. eauto.
      }
      { eauto. }
      { eauto. }
    }
    { auto. }
    { auto. }
  }
Qed.

Lemma max_readable_write_na_step mem0 prom0 tvw0 loc ts from to val0 val1 released sc
      (MAX: max_readable mem0 prom0 loc ts val0 released)
      (TS: tvw0.(TView.cur).(View.pln) loc = ts)
      (RESERVE: forall to' from' val' released'
                       (GET: Memory.get loc to' prom0 = Some (from', Message.concrete val' released')),
          released' = None)
      (WF: Local.wf (Local.mk tvw0 prom0) mem0)
      (CLOSED: Memory.closed mem0)
      (CONS: Local.promise_consistent (Local.mk tvw0 prom0))
      (FROM: Time.le (Memory.max_ts loc mem0) from)
      (TO: Time.lt from to)
  :
    exists mem1 mem2 mem3 prom1 prom3 tvw1 msgs ks,
      (<<RESERVE: cancel_future_memory loc prom0 mem0 prom1 mem1>>) /\
      (<<LOWER: fulfilled_memory loc mem0 mem2>>) /\
      (<<MEM: mem2 = mem1>>) /\
      (<<ADD: Memory.add mem2 loc from to (Message.concrete val1 None) mem3>>) /\
      (<<PROMISES: forall loc' ts',
          Memory.get loc' ts' prom3 =
          if Loc.eq_dec loc' loc
          then None
          else Memory.get loc' ts' prom0>>) /\
      (<<WRITE: Local.write_na_step (Local.mk tvw0 prom1) sc mem1 loc from to val1 Ordering.na (Local.mk tvw1 prom3) sc mem3 msgs ks Memory.op_kind_add>>) /\
      (<<VIEW: tvw1.(TView.cur).(View.pln) loc = to>>) /\
      (<<MAXTS: Memory.max_ts loc mem3 = to>>) /\
      (<<MAX: max_readable mem3 prom3 loc to val1 None>>)
.
Proof.
  hexploit (@remove_reserves_loc prom0 mem0 loc).
  { apply WF. }
  { apply WF. }
  { eapply CLOSED. }
  i. des.
  hexploit (@max_readable_na_write mem1 prom1 loc (View.rlx (TView.cur tvw0) loc) from to val1); auto.
  { eapply reserve_future_memory_le;[apply WF|]. eapply cancel_future_reserve_future; eauto. }
  { eapply reserve_future_memory_bot_none; [apply WF|]. eapply cancel_future_reserve_future; eauto. }
  { i. assert (<<RESERE: msg' <> Message.reserve>> /\ <<GET: Memory.get loc to' prom0 = Some (from', msg')>>).
    { rewrite PROMISES in GET. des_ifs. }
    des. split; auto.
    exploit CONS; eauto. i. splits; auto.
    i. subst. eapply RESERVE; eauto.
  }
  { inv WF. inv TVIEW_CLOSED. inv CUR. ss.
    specialize (RLX loc). des.
    eapply fulfilled_memory_get1 in RLX; eauto; ss.
    { des. red. esplits; eauto. inv MSG_LE; ss. }
    { eapply reserve_future_future; eauto. eapply cancel_future_reserve_future; eauto. }
  }
  { etrans; eauto.
    eapply fulfilled_memory_max_ts; eauto. }
  { eapply reserve_future_memory_future; eauto.
    { eapply Memory.closed_timemap_bot. eapply CLOSED. }
    { eapply cancel_future_reserve_future; eauto. }
  }
  i. des. eexists mem1, mem2, mem3, prom1, prom2, _. esplits; auto.
  { etrans; eauto. }
  { i. rewrite PROMISES0. rewrite PROMISES. des_ifs. }
  { econs; ss. subst. eauto. }
  { ss. unfold TimeMap.join. replace (TimeMap.singleton loc to loc) with to.
    { apply TimeFacts.le_join_r.
      inv WF. inv TVIEW_CLOSED. inv CUR. ss.
      specialize (PLN loc). des.
      apply Memory.max_ts_spec in PLN. des.
      etrans; eauto. etrans; eauto. left. auto.
    }
    { symmetry. unfold TimeMap.singleton. apply LocFun.add_spec_eq. }
  }
  { subst. econs.
    { eapply Memory.add_get0; eauto. }
    { auto. }
    { i. eapply Memory.max_ts_spec in GET. des. timetac. }
  }
Qed.

Lemma non_max_readable_race mem prom tvw loc
      (MAX: forall val released, ~ max_readable mem prom loc (tvw.(TView.cur).(View.pln) loc) val released)
      (WF: Local.wf (Local.mk tvw prom) mem)
      (CONS: Local.promise_consistent (Local.mk tvw prom))
  :
    Local.is_racy (Local.mk tvw prom) mem loc Ordering.na.
Proof.
  inv WF. inv TVIEW_CLOSED. inv CUR. ss.
  specialize (PLN loc). des.
  apply NNPP. ii. eapply MAX. econs; eauto.
  { destruct (Memory.get loc (tvw.(TView.cur).(View.pln) loc) prom) as [[from' msg]|] eqn:EQ; auto.
    exfalso. exploit PROMISES; eauto. i. clarify.
    exploit CONS; eauto; ss. i.
    eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt; eauto.
    eapply TVIEW_WF.
  }
  { i. eapply NNPP. ii.
    eapply H. econs; eauto; ss.
    { destruct (Memory.get loc ts' prom) as [[]|] eqn:EQ; auto.
      exploit PROMISES; eauto. i. clarify. }
  }
Qed.

Lemma non_max_readable_read mem prom tvw loc ts val'
      (MAX: forall val released, ~ max_readable mem prom loc ts val released)
      (TS: tvw.(TView.cur).(View.pln) loc = ts)
      (WF: Local.wf (Local.mk tvw prom) mem)
      (CONS: Local.promise_consistent (Local.mk tvw prom))
  :
    Local.racy_read_step (Local.mk tvw prom) mem loc val' Ordering.na.
Proof.
  subst. hexploit non_max_readable_race; eauto.
Qed.

Lemma non_max_readable_write mem prom tvw loc ts
      (MAX: forall val released, ~ max_readable mem prom loc ts val released)
      (TS: tvw.(TView.cur).(View.pln) loc = ts)
      (WF: Local.wf (Local.mk tvw prom) mem)
      (CONS: Local.promise_consistent (Local.mk tvw prom))
  :
    Local.racy_write_step (Local.mk tvw prom) mem loc Ordering.na.
Proof.
  subst. hexploit non_max_readable_race; eauto.
Qed.

Lemma add_max_ts mem0 loc from to msg mem1
      (ADD: Memory.add mem0 loc from to msg mem1)
      (TO: Time.le (Memory.max_ts loc mem0) to)
  :
    Memory.max_ts loc mem1 = to.
Proof.
  hexploit Memory.add_get0; eauto. i. des.
  eapply Memory.max_ts_spec in GET0. des.
  erewrite Memory.add_o in GET1; eauto. des_ifs.
  { ss. des; clarify. }
  { ss. des; clarify.
    apply Memory.max_ts_spec in GET1. des.
    apply TimeFacts.antisym; auto. etrans; eauto.
  }
Qed.

Variant added_memory loc msgs mem0 mem1: Prop :=
| added_memory_intro
    (MLE: Memory.le mem0 mem1)
    (OTHER: forall loc' (NEQ: loc' <> loc) to, Memory.get loc' to mem1 = Memory.get loc' to mem0)
    (COMPLETE: forall from to msg
                      (IN: List.In (from, to, msg) msgs),
        Memory.get loc to mem1 = Some (from, msg))
    (SOUND: forall from to msg
                   (GET: Memory.get loc to mem1 = Some (from, msg)),
        (<<GET: Memory.get loc to mem0 = Some (from, msg)>>) \/
        (<<IN: List.In (from, to, msg) msgs>>))
.

Lemma added_memory_nil loc mem
  :
    added_memory loc [] mem mem.
Proof.
  econs; eauto.
  { refl. }
  { i. ss. }
Qed.

Lemma added_memory_cons loc from to msg msgs mem0 mem1 mem2
      (ADD: Memory.add mem0 loc from to msg mem1)
      (ADDED: added_memory loc msgs mem1 mem2)
  :
    added_memory loc ((from, to, msg)::msgs) mem0 mem2.
Proof.
  inv ADDED. econs; eauto.
  { etrans; eauto. ii. eapply Memory.add_get1 in LHS; eauto. }
  { i. rewrite OTHER; auto.
    erewrite (@Memory.add_o mem1); eauto. des_ifs.
    ss. des; clarify.
  }
  { i. ss. des; clarify.
    { eapply MLE. eapply Memory.add_get0; eauto. }
    { apply COMPLETE; auto. }
  }
  { i. apply SOUND in GET. des; ss; auto.
    erewrite Memory.add_o in GET0; eauto. des_ifs; auto.
    ss. des; clarify. auto.
  }
Qed.

Lemma add_promises_latest lang (st: lang.(Language.state)) tvw sc
      prom0 mem0
      loc msgs
      (WFMSGS: wf_cell_msgs msgs)
      (FORALL: List.Forall (fun '(from, to, msg) => (<<MAX: Time.le (Memory.max_ts loc mem0) from>>) /\ (<<TS: Time.lt from to>>) /\ (<<MSGTO: Memory.message_to msg loc to>>) /\ (<<WF: Message.wf msg>>) /\ (<<CLOSED: semi_closed_message msg mem0 loc to>>)) msgs)
  :
    exists prom1 mem1,
      (<<STEPS: rtc (@Thread.tau_step lang) (Thread.mk _ st (Local.mk tvw prom0) sc mem0) (Thread.mk _ st (Local.mk tvw prom1) sc mem1)>>) /\
      (<<MEM: added_memory loc msgs mem0 mem1>>) /\
      (<<PROMISES: added_memory loc msgs prom0 prom1>>).
Proof.
  ginduction msgs; i.
  { esplits; eauto.
    { eapply added_memory_nil. }
    { eapply added_memory_nil. }
  }
  { inv FORALL. destruct a as [[from to] msg]. des.
    admit.
  }
Admitted.
