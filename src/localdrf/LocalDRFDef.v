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
Require Import Pred.
Require Import Trace.

Require Import MemoryProps.

Set Implicit Arguments.


Inductive step_all A B C D (step: A -> B -> C -> D -> Prop): C -> D -> Prop :=
| step_all_intro
    a b c d
    (STEP: step a b c d)
  :
    step_all step c d.

Section LOCALDRF.

  Variable L: Loc.t -> bool.

  Definition valid_event (e: ThreadEvent.t): Prop :=
    forall loc from to msg kind (PROMISE: e = ThreadEvent.promise loc from to msg kind) (LOC: L loc),
      msg = Message.reserve.

  Definition valid_step (e: MachineEvent.t) (tid: Ident.t)
             (c0 c1: Configuration.t): Prop :=
    exists lang tr,
      (<<STEP: @Trace.configuration_step lang tr e tid c0 c1>>) /\
      (<<VALID: List.Forall (compose valid_event snd) tr>>).

  Inductive configuration_steps_trace:
    forall (c0 c1: Configuration.t) (tr: list (Ident.t * sigT Trace.t)), Prop :=
  | configuration_steps_trace_nil
      c0
    :
      configuration_steps_trace c0 c0 []
  | configuration_steps_trace_cons
      c0 c1 c2 trs lang tr e tid
      (STEPS: configuration_steps_trace c0 c1 trs)
      (STEP: @Trace.configuration_step lang tr e tid c0 c1)
      (VALID: List.Forall (compose valid_event snd) tr)
    :
      configuration_steps_trace c0 c2 (trs ++ [(tid, existT _ _ tr)]) (* add at "last" *)
  .

  Inductive racy_read (loc: Loc.t) (ts: Time.t):
    forall lang (th: Thread.t lang) (e: ThreadEvent.t), Prop :=
  | racy_read_read
      lang (th: Thread.t lang)
      valr releasedr ordr
      (VIEW: Time.lt (th.(Thread.local).(Local.tview).(TView.cur).(View.rlx) loc) ts)
    :
      racy_read loc ts th (ThreadEvent.read loc ts valr releasedr ordr)
  | racy_read_update
      lang (th: Thread.t lang)
      to valr valw releasedr releasedw ordr ordw
      (VIEW: Time.lt (th.(Thread.local).(Local.tview).(TView.cur).(View.rlx) loc) ts)
    :
      racy_read loc ts th (ThreadEvent.update loc ts to valr valw releasedr releasedw ordr ordw)
  .

  Inductive racy_write (loc: Loc.t) (ts: Time.t):
    forall lang (th: Thread.t lang) (e: ThreadEvent.t), Prop :=
  | racy_write_write
      lang (th: Thread.t lang)
      from valw releasedw ordw
      (ORD: Ordering.le ordw Ordering.relaxed)
    :
      racy_write loc ts th (ThreadEvent.write loc from ts valw releasedw ordw)
  | racy_write_update
      lang (th: Thread.t lang)
      from valr valw releasedr releasedw ordr ordw
      (ORD: Ordering.le ordw Ordering.relaxed)
    :
      racy_write loc ts th (ThreadEvent.update loc from ts valr valw releasedr releasedw ordr ordw)
  .

  Definition racefree (s: Threads.syntax): Prop :=
    forall c0 c1 trs
           loc ts
           tid0 tid1 lang0 lang1 tr0 tr1 th0 th1 e0 e1
           (CSTEPS: configuration_steps_trace c0 c1 trs)
           (TRACE0: List.In (tid0, existT _ lang0 tr0) trs)
           (TRACE1: List.In (tid1, existT _ lang1 tr1) trs)
           (EVENT0: List.In (th0, e0) tr0)
           (EVENT1: List.In (th1, e1) tr1)
           (WRITE: racy_write loc ts th0 e0)
           (READ: racy_read loc ts th1 e1),
      False.

  Theorem local_DRF_PF s
          (RACEFRFEE: racefree s)
    :
      behaviors Configuration.step (Configuration.init s) <1=
      behaviors valid_step (Configuration.init s).
  Admitted.

End LOCALDRF.


Section ADDCLOSED.

  Definition add_closed_timemap
             (times: TimeMap.t)
             (mem: Memory.t) (loc: Loc.t) (ts: Time.t): Prop
    :=
      forall loc',
        (<<GET: exists from val released,
            Memory.get loc' (times loc') mem = Some (from, Message.concrete val released)>>) \/
        (<<ADDED: loc' = loc /\ times loc' = ts>>)
  .

  Lemma closed_add_closed_timemap
        times mem loc ts
        (CLOSED: Memory.closed_timemap times mem)
    :
      add_closed_timemap times mem loc ts.
  Proof. ii. eauto. Qed.

  Record add_closed_view (view:View.t) (mem:Memory.t) (loc: Loc.t) (ts: Time.t)
    : Prop :=
    add_closed_view_intro
      {
        add_closed_view_pln: add_closed_timemap view.(View.pln) mem loc ts;
        add_closed_view_rlx: add_closed_timemap view.(View.rlx) mem loc ts;
      }
  .
  Hint Constructors add_closed_view.

  Lemma closed_add_closed_view
        view mem loc ts
        (CLOSED: Memory.closed_view view mem)
    :
      add_closed_view view mem loc ts.
  Proof.
    inv CLOSED. econs.
    - eapply closed_add_closed_timemap; eauto.
    - eapply closed_add_closed_timemap; eauto.
  Qed.

  Inductive add_closed_opt_view: forall (view:option View.t) (mem:Memory.t)
                                        (loc: Loc.t) (ts: Time.t), Prop :=
  | add_closed_opt_view_some
      view mem loc ts
      (CLOSED: add_closed_view view mem loc ts):
      add_closed_opt_view (Some view) mem loc ts
  | add_closed_opt_view_none
      mem loc ts:
      add_closed_opt_view None mem loc ts
  .
  Hint Constructors add_closed_opt_view.

  Lemma closed_add_closed_opt_view
        view mem loc ts
        (CLOSED: Memory.closed_opt_view view mem)
    :
      add_closed_opt_view view mem loc ts.
  Proof.
    inv CLOSED; econs.
    eapply closed_add_closed_view; eauto.
  Qed.

  Inductive add_closed_message: forall (msg:Message.t) (mem:Memory.t)
                                       (loc: Loc.t) (ts: Time.t), Prop :=
  | add_closed_message_concrete
      val released mem loc ts
      (CLOSED: add_closed_opt_view released mem loc ts):
      add_closed_message (Message.concrete val released) mem loc ts
  | add_closed_message_reserve
      mem loc ts:
      add_closed_message Message.reserve mem loc ts
  .
  Hint Constructors add_closed_message.

  Lemma closed_add_closed_message
        msg mem loc ts
        (CLOSED: Memory.closed_message msg mem)
    :
      add_closed_message msg mem loc ts.
  Proof.
    inv CLOSED; econs.
    eapply closed_add_closed_opt_view; eauto.
  Qed.

  Lemma add_closed_timemap_add_closed tm mem0 loc from ts val released mem1
        (ADD: Memory.add mem0 loc from ts (Message.concrete val released) mem1)
        (CLOSED: add_closed_timemap tm mem0 loc ts)
    :
      Memory.closed_timemap tm mem1.
  Proof.
    ii. erewrite Memory.add_o; eauto. specialize (CLOSED loc0). des; clarify.
    - des_ifs; eauto.
    - des_ifs; eauto. ss. des; clarify.
  Qed.

  Lemma add_closed_timemap_split_closed tm mem0 loc from ts ts2 msg val released mem1
        (SPLIT: Memory.split mem0 loc from ts ts2 (Message.concrete val released) msg mem1)
        (CLOSED: add_closed_timemap tm mem0 loc ts)
    :
      Memory.closed_timemap tm mem1.
  Proof.
    ii. erewrite Memory.split_o; eauto. specialize (CLOSED loc0). des; clarify.
    - des_ifs; eauto. ss. des; clarify.
      eapply Memory.split_get0 in SPLIT. des. clarify. eauto.
    - des_ifs; eauto.
      + ss. des; clarify.
      + ss. des; clarify.
  Qed.

  Lemma add_closed_timemap_lower_closed tm mem0 loc from ts msg val released mem1
        (LOWER: Memory.lower mem0 loc from ts msg (Message.concrete val released) mem1)
        (CLOSED: add_closed_timemap tm mem0 loc ts)
    :
      Memory.closed_timemap tm mem1.
  Proof.
    ii. erewrite Memory.lower_o; eauto. specialize (CLOSED loc0). des; clarify.
    - des_ifs; eauto.
    - des_ifs; eauto. ss. des; clarify.
  Qed.

  Lemma add_closed_view_add_closed vw mem0 loc from ts val released mem1
        (ADD: Memory.add mem0 loc from ts (Message.concrete val released) mem1)
        (CLOSED: add_closed_view vw mem0 loc ts)
    :
      Memory.closed_view vw mem1.
  Proof.
    inv CLOSED. econs.
    - eapply add_closed_timemap_add_closed; eauto.
    - eapply add_closed_timemap_add_closed; eauto.
  Qed.

  Lemma add_closed_view_split_closed vw mem0 loc from ts ts2 msg val released mem1
        (SPLIT: Memory.split mem0 loc from ts ts2 (Message.concrete val released) msg mem1)
        (CLOSED: add_closed_view vw mem0 loc ts)
    :
      Memory.closed_view vw mem1.
  Proof.
    inv CLOSED. econs.
    - eapply add_closed_timemap_split_closed; eauto.
    - eapply add_closed_timemap_split_closed; eauto.
  Qed.

  Lemma add_closed_view_lower_closed vw mem0 loc from ts msg val released mem1
        (LOWER: Memory.lower mem0 loc from ts msg (Message.concrete val released) mem1)
        (CLOSED: add_closed_view vw mem0 loc ts)
    :
      Memory.closed_view vw mem1.
  Proof.
    inv CLOSED. econs.
    - eapply add_closed_timemap_lower_closed; eauto.
    - eapply add_closed_timemap_lower_closed; eauto.
  Qed.

  Lemma add_closed_opt_view_add_closed vw mem0 loc from ts val released mem1
        (ADD: Memory.add mem0 loc from ts (Message.concrete val released) mem1)
        (CLOSED: add_closed_opt_view vw mem0 loc ts)
    :
      Memory.closed_opt_view vw mem1.
  Proof.
    inv CLOSED; econs.
    eapply add_closed_view_add_closed; eauto.
  Qed.

  Lemma add_closed_opt_view_split_closed vw mem0 loc from ts ts2 msg val released mem1
        (SPLIT: Memory.split mem0 loc from ts ts2 (Message.concrete val released) msg mem1)
        (CLOSED: add_closed_opt_view vw mem0 loc ts)
    :
      Memory.closed_opt_view vw mem1.
  Proof.
    inv CLOSED; econs.
    eapply add_closed_view_split_closed; eauto.
  Qed.

  Lemma add_closed_opt_view_lower_closed vw mem0 loc from ts msg val released mem1
        (LOWER: Memory.lower mem0 loc from ts msg (Message.concrete val released) mem1)
        (CLOSED: add_closed_opt_view vw mem0 loc ts)
    :
      Memory.closed_opt_view vw mem1.
  Proof.
    inv CLOSED; econs.
    eapply add_closed_view_lower_closed; eauto.
  Qed.

  Lemma add_closed_message_add_closed msg mem0 loc from ts val released mem1
        (ADD: Memory.add mem0 loc from ts (Message.concrete val released) mem1)
        (CLOSED: add_closed_message msg mem0 loc ts)
    :
      Memory.closed_message msg mem1.
  Proof.
    inv CLOSED; econs.
    eapply add_closed_opt_view_add_closed; eauto.
  Qed.

  Lemma add_closed_message_split_closed msg mem0 loc from ts ts2 msg2 val released mem1
        (SPLIT: Memory.split mem0 loc from ts ts2 (Message.concrete val released) msg2 mem1)
        (CLOSED: add_closed_message msg mem0 loc ts)
    :
      Memory.closed_message msg mem1.
  Proof.
    inv CLOSED; econs.
    eapply add_closed_opt_view_split_closed; eauto.
  Qed.

  Lemma add_closed_message_lower_closed msg mem0 loc from ts msg0 val released mem1
        (LOWER: Memory.lower mem0 loc from ts msg0 (Message.concrete val released) mem1)
        (CLOSED: add_closed_message msg mem0 loc ts)
    :
      Memory.closed_message msg mem1.
  Proof.
    inv CLOSED; econs.
    eapply add_closed_opt_view_lower_closed; eauto.
  Qed.

  Lemma add_closed_timemap_future_add_closed tm mem0 loc ts mem1
        (FUTURE: Memory.future_weak mem0 mem1)
        (CLOSED: add_closed_timemap tm mem0 loc ts)
    :
      add_closed_timemap tm mem1 loc ts.
  Proof.
    ii. specialize (CLOSED loc'). des.
    - eapply Memory.future_weak_get1 in GET; eauto.
      des. inv MSG_LE. left. eauto.
    - right. auto.
  Qed.

  Lemma add_closed_view_future_add_closed vw mem0 loc ts mem1
        (FUTURE: Memory.future_weak mem0 mem1)
        (CLOSED: add_closed_view vw mem0 loc ts)
    :
      add_closed_view vw mem1 loc ts.
  Proof.
    inv CLOSED. econs.
    - eapply add_closed_timemap_future_add_closed; eauto.
    - eapply add_closed_timemap_future_add_closed; eauto.
  Qed.

  Lemma add_closed_opt_view_future_add_closed vw mem0 loc ts mem1
        (FUTURE: Memory.future_weak mem0 mem1)
        (CLOSED: add_closed_opt_view vw mem0 loc ts)
    :
      add_closed_opt_view vw mem1 loc ts.
  Proof.
    inv CLOSED; econs.
    eapply add_closed_view_future_add_closed; eauto.
  Qed.

  Lemma add_closed_message_future_add_closed msg mem0 loc ts mem1
        (FUTURE: Memory.future_weak mem0 mem1)
        (CLOSED: add_closed_message msg mem0 loc ts)
    :
      add_closed_message msg mem1 loc ts.
  Proof.
    inv CLOSED; econs.
    eapply add_closed_opt_view_future_add_closed; eauto.
  Qed.

  Lemma join_timemap_add_closed tm0 tm1 mem loc ts
        (CLOSED0: add_closed_timemap tm0 mem loc ts)
        (CLOSED1: add_closed_timemap tm1 mem loc ts)
    :
      add_closed_timemap (TimeMap.join tm0 tm1) mem loc ts.
  Proof.
    ii. specialize (CLOSED0 loc'). specialize (CLOSED1 loc').
    unfold TimeMap.join, Time.join. des_ifs.
  Qed.

  Lemma join_view_add_closed vw0 vw1 mem loc ts
        (CLOSED0: add_closed_view vw0 mem loc ts)
        (CLOSED1: add_closed_view vw1 mem loc ts)
    :
      add_closed_view (View.join vw0 vw1) mem loc ts.
  Proof.
    inv CLOSED0. inv CLOSED1. unfold View.join. econs; ss.
    - eapply join_timemap_add_closed; eauto.
    - eapply join_timemap_add_closed; eauto.
  Qed.

  Lemma bot_timemap_add_closed mem loc ts
        (MEM: Memory.closed mem)
    :
      add_closed_timemap TimeMap.bot mem loc ts.
  Proof.
    ii. left. inv MEM. eauto.
  Qed.

  Lemma bot_view_add_closed mem loc ts
        (MEM: Memory.closed mem)
    :
      add_closed_view View.bot mem loc ts.
  Proof.
    econs.
    - eapply bot_timemap_add_closed; eauto.
    - eapply bot_timemap_add_closed; eauto.
  Qed.

  Lemma unwrap_add_closed vw mem loc ts
        (MEM: Memory.closed mem)
        (CLOSED: add_closed_opt_view vw mem loc ts)
    :
      add_closed_view (View.unwrap vw) mem loc ts.
  Proof.
    inv CLOSED; ss.
    apply bot_view_add_closed; eauto.
  Qed.

  Definition add_weak_closed_timemap
             (times: TimeMap.t)
             (mem: Memory.t) (loc: Loc.t) (ts: Time.t): Prop
    :=
      forall loc',
        (<<GET: exists from val released,
            Memory.get loc' (times loc') mem = Some (from, Message.concrete val released)>>) \/
        (<<ADDED: loc' = loc /\ (<<TS: Time.le (times loc') ts>>)>>)
  .

  Record add_weak_closed_view (view:View.t) (mem:Memory.t) (loc: Loc.t) (ts: Time.t)
    : Prop :=
    add_weak_closed_view_intro
      {
        add_weak_closed_view_pln: add_weak_closed_timemap view.(View.pln) mem loc ts;
        add_weak_closed_view_rlx: add_weak_closed_timemap view.(View.rlx) mem loc ts;
      }
  .
  Hint Constructors add_weak_closed_view.

  Lemma add_closed_add_weak_closed_timemap tm mem loc ts
        (CLOSED: add_closed_timemap tm mem loc ts)
    :
      add_weak_closed_timemap tm mem loc ts.
  Proof.
    ii. specialize (CLOSED loc'). des; subst.
    - left. eauto.
    - right. split; auto. red. refl.
  Qed.

  Lemma add_closed_add_weak_closed_view vw mem loc ts
        (CLOSED: add_closed_view vw mem loc ts)
    :
      add_weak_closed_view vw mem loc ts.
  Proof.
    inv CLOSED; econs.
    - eapply add_closed_add_weak_closed_timemap; eauto.
    - eapply add_closed_add_weak_closed_timemap; eauto.
  Qed.

  Lemma add_weak_closed_timemap_ts_le tm mem loc ts0 ts1
        (CLOSED: add_weak_closed_timemap tm mem loc ts0)
        (TS: Time.le ts0 ts1)
    :
      add_weak_closed_timemap tm mem loc ts1.
  Proof.
    ii. specialize (CLOSED loc'). des.
    - left. eauto.
    - right. split; eauto.
  Qed.

  Lemma add_weak_closed_view_ts_le vw mem loc ts0 ts1
        (CLOSED: add_weak_closed_view vw mem loc ts0)
        (TS: Time.le ts0 ts1)
    :
      add_weak_closed_view vw mem loc ts1.
  Proof.
    inv CLOSED. econs.
    - eapply add_weak_closed_timemap_ts_le; eauto.
    - eapply add_weak_closed_timemap_ts_le; eauto.
  Qed.

  Lemma add_weak_closed_timemap_consistent tm mem loc ts0 ts1
        (CLOSED: add_weak_closed_timemap tm mem loc ts0)
        (TS: Time.le (tm loc) ts1)
    :
      add_weak_closed_timemap tm mem loc ts1.
  Proof.
    ii. specialize (CLOSED loc'). des; subst.
    - left. eauto.
    - right. split; eauto.
  Qed.

  Lemma add_weak_closed_view_consistent vw mem loc ts0 ts1
        (CLOSED: add_weak_closed_view vw mem loc ts0)
        (VWWF: View.wf vw)
        (TS: Time.le (vw.(View.rlx) loc) ts1)
    :
      add_weak_closed_view vw mem loc ts1.
  Proof.
    inv CLOSED. econs.
    - eapply add_weak_closed_timemap_consistent; eauto.
      inv VWWF. etrans; eauto.
    - eapply add_weak_closed_timemap_consistent; eauto.
  Qed.

  Lemma join_timemap_add_weak_closed tm0 tm1 mem loc ts
        (CLOSED0: add_weak_closed_timemap tm0 mem loc ts)
        (CLOSED1: add_weak_closed_timemap tm1 mem loc ts)
    :
      add_weak_closed_timemap (TimeMap.join tm0 tm1) mem loc ts.
  Proof.
    ii. unfold TimeMap.join, Time.join. des_ifs.
  Qed.

  Lemma join_view_add_weak_closed vw0 vw1 mem loc ts
        (CLOSED0: add_weak_closed_view vw0 mem loc ts)
        (CLOSED1: add_weak_closed_view vw1 mem loc ts)
    :
      add_weak_closed_view (View.join vw0 vw1) mem loc ts.
  Proof.
    inv CLOSED0. inv CLOSED1. unfold View.join. econs; ss.
    - eapply join_timemap_add_weak_closed; eauto.
    - eapply join_timemap_add_weak_closed; eauto.
  Qed.

  Lemma singleton_timemap_add_closed mem loc ts
        (MEM: Memory.closed mem)
    :
      add_closed_timemap (TimeMap.singleton loc ts) mem loc ts.
  Proof.
    ii. unfold TimeMap.singleton. destruct (Loc.eq_dec loc' loc).
    - subst. right. split; auto. setoid_rewrite LocFun.add_spec_eq. auto.
    - left. inv MEM. red.
      setoid_rewrite LocFun.add_spec_neq; auto. eauto.
  Qed.

  Lemma singleton_view_add_closed mem loc ts
        (MEM: Memory.closed mem)
    :
      add_closed_view (View.singleton_ur loc ts) mem loc ts.
  Proof.
    econs.
    - eapply singleton_timemap_add_closed; eauto.
    - eapply singleton_timemap_add_closed; eauto.
  Qed.

  Lemma singleton_join_timemap_add_closed mem loc ts tm
        (CLOSED: add_weak_closed_timemap tm mem loc ts)
    :
      add_closed_timemap (TimeMap.join (TimeMap.singleton loc ts) tm) mem loc ts.
  Proof.
    ii. specialize (CLOSED loc'). unfold TimeMap.join, Time.join, TimeMap.singleton.
    des_ifs.
    - des; subst.
      + left. eauto.
      + right. split; auto.
        setoid_rewrite LocFun.add_spec_eq in l. destruct l; auto.
        exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt; eauto.
    - setoid_rewrite LocFun.add_spec in l. des_ifs.
      + right. split; auto.
        setoid_rewrite LocFun.add_spec. des_ifs.
      + exfalso. eapply Time.lt_strorder.
        eapply TimeFacts.lt_le_lt; eauto. eapply Time.bot_spec.
  Qed.

  Lemma singleton_ur_join_view_add_closed mem loc ts vw
        (CLOSED: add_weak_closed_view vw mem loc ts)
    :
      add_closed_view (View.join (View.singleton_ur loc ts) vw) mem loc ts.
  Proof.
    inv CLOSED. unfold View.singleton_ur. econs; ss.
    - eapply singleton_join_timemap_add_closed; eauto.
    - eapply singleton_join_timemap_add_closed; eauto.
  Qed.

  Lemma write_released_add_closed
        mem tvw sc loc to releasedm ord from
        (MEM: Memory.closed mem)
        (TVIEW: TView.closed tvw mem)
        (RELEASEDM: add_closed_opt_view releasedm mem loc from)
        (TS: Time.le from to)
    :
      add_closed_opt_view (TView.write_released tvw sc loc to releasedm ord) mem loc to.
  Proof.
    unfold TView.write_released, TView.write_tview. ss.
    setoid_rewrite LocFun.add_spec_eq. des_ifs.
    - econs. erewrite <- View.join_assoc. erewrite View.join_comm.
      eapply singleton_ur_join_view_add_closed; eauto.
      eapply join_view_add_weak_closed.
      + eapply add_weak_closed_view_ts_le; eauto.
        eapply add_closed_add_weak_closed_view; eauto.
        eapply unwrap_add_closed; eauto.
      + eapply add_closed_add_weak_closed_view; eauto.
        inv TVIEW. eapply closed_add_closed_view; eauto.
    - econs. erewrite <- View.join_assoc. erewrite View.join_comm.
      eapply singleton_ur_join_view_add_closed; eauto.
      eapply join_view_add_weak_closed.
      + eapply add_weak_closed_view_ts_le; eauto.
        eapply add_closed_add_weak_closed_view; eauto.
        eapply unwrap_add_closed; eauto.
      + eapply add_closed_add_weak_closed_view; eauto.
        inv TVIEW. eapply closed_add_closed_view; eauto.
  Qed.

  Lemma write_released_add_closed_relaxed
        mem tvw sc loc to releasedm ord from
        (MEM: Memory.closed mem)
        (TVIEW: add_weak_closed_view (tvw.(TView.rel) loc) mem loc to)
        (RELEASEDM: add_closed_opt_view releasedm mem loc from)
        (TS: Time.le from to)
        (ORD: Ordering.le Ordering.strong_relaxed ord = false)
    :
      add_closed_opt_view (TView.write_released tvw sc loc to releasedm ord) mem loc to.
  Proof.
    unfold TView.write_released, TView.write_tview. ss.
    setoid_rewrite LocFun.add_spec_eq. des_ifs.
    - destruct ord; ss.
    - econs. erewrite <- View.join_assoc. erewrite View.join_comm.
      eapply singleton_ur_join_view_add_closed; eauto.
      eapply join_view_add_weak_closed.
      + eapply add_weak_closed_view_ts_le; eauto.
        eapply add_closed_add_weak_closed_view; eauto.
        eapply unwrap_add_closed; eauto.
      + eauto.
  Qed.

End ADDCLOSED.


Section SIMVIEW.

  Record sim_timemap (past: Memory.t) (loc: Loc.t) (ts: Time.t)
         (tm_src tm_tgt: TimeMap.t): Prop :=
    sim_timemap_intro
      {
        sim_timemap_le: TimeMap.le tm_src tm_tgt;
        sim_timemap_closed: add_closed_timemap tm_src past loc ts;
        sim_timemap_max: forall tm (CLOSED: add_closed_timemap tm past loc ts)
                                (TMLE: TimeMap.le tm tm_tgt)
          ,
            TimeMap.le tm tm_src;
      }.
  Hint Constructors sim_timemap.

  Lemma sim_timemap_exists past loc ts tm_tgt
        (CLOSED: Memory.closed past)
    :
      exists tm_src, <<SIM: sim_timemap past loc ts tm_src tm_tgt>>.
  Proof.
    exploit (@choice _ _ (fun loc' ts_src =>
                            (<<GREATEST:
                               forall ts
                                      (PAST: concrete_promised past loc' ts)
                                      (LE: Time.le ts (tm_tgt loc')),
                                 Time.le ts ts_src>>) /\
                            (<<CLOSED: concrete_promised past loc' ts_src>>) /\
                            (<<TLE: Time.le ts_src (tm_tgt loc')>>))).
    - intros loc'.
      hexploit (cell_elements_greatest (past loc') (fun ts => concrete_promised past loc' ts /\ Time.le ts (tm_tgt loc'))).
      i. des.
      + exists to. split; clarify. ii. splits; auto.
        i. dup PAST. inv PAST. exploit GREATEST; eauto.
      + exfalso. inv CLOSED. eapply EMPTY; eauto. split.
        { econs; eauto. }
        { eapply Time.bot_spec. }
    - intros [f FSPEC]. des.
      set (f' := fun loc' => if (Loc.eq_dec loc loc')
                             then
                               (if (Time.le_lt_dec (f loc') ts)
                                then
                                  (if (Time.le_lt_dec ts (tm_tgt loc')) then ts else f loc')
                                else f loc')
                             else f loc'). exists f'. unfold f'. econs.
      + ii. des_ifs.
        * specialize (FSPEC loc0). des. auto.
        * specialize (FSPEC loc0). des. auto.
        * specialize (FSPEC loc0). des. auto.
      + ii. specialize (FSPEC loc'). des. inv CLOSED0. des_ifs; eauto 10.
      + ii. specialize (FSPEC loc0). des.
        specialize (CLOSED0 loc0). des.
        * exploit GREATEST.
          { econs; eauto. }
          { apply TMLE. }
          i. des_ifs. etrans; eauto.
        * clarify. des_ifs.
          { refl. }
          { exfalso. eapply Time.lt_strorder.
            eapply TimeFacts.lt_le_lt.
            - eapply l0.
            - eauto. }
          { left. auto. }
  Qed.

  Record sim_view (past: Memory.t) (loc: Loc.t) (ts: Time.t)
         (view_src view_tgt: View.t): Prop :=
    sim_view_intro
      {
        sim_view_pln: sim_timemap past loc ts view_src.(View.pln) view_tgt.(View.pln);
        sim_view_rlx: sim_timemap past loc ts view_src.(View.rlx) view_tgt.(View.rlx);
      }
  .
  Hint Constructors sim_view.

  Lemma sim_view_le past loc ts vw_src vw_tgt
        (SIM: sim_view past loc ts vw_src vw_tgt)
    :
      View.le vw_src vw_tgt.
  Proof.
    inv SIM. econs.
    - eapply sim_timemap_le; eauto.
    - eapply sim_timemap_le; eauto.
  Qed.

  Lemma sim_view_exists past vw_tgt loc ts
        (CLOSED: Memory.closed past)
    :
      exists vw_src, <<SIM: sim_view past loc ts vw_src vw_tgt>>.
  Proof.
    exploit (@sim_timemap_exists past loc ts vw_tgt.(View.pln)); auto. i. des.
    exploit (@sim_timemap_exists past loc ts vw_tgt.(View.rlx)); auto. i. des.
    exists (View.mk tm_src tm_src0). econs; eauto.
  Qed.

  Lemma sim_view_closed past loc ts vw_src vw_tgt
        (SIM: sim_view past loc ts vw_src vw_tgt)
    :
      add_closed_view vw_src past loc ts.
  Proof.
    econs.
    - eapply sim_timemap_closed; eauto. eapply sim_view_pln; eauto.
    - eapply sim_timemap_closed; eauto. eapply sim_view_rlx; eauto.
  Qed.

  Lemma sim_view_max past loc ts vw_src vw_tgt vw
        (SIM: sim_view past loc ts vw_src vw_tgt)
        (VWLE: View.le vw vw_tgt)
        (CLOSED: add_closed_view vw past loc ts)
    :
      View.le vw vw_src.
  Proof.
    inv VWLE. inv CLOSED. econs.
    - eapply sim_timemap_max; eauto. eapply sim_view_pln; eauto.
    - eapply sim_timemap_max; eauto. eapply sim_view_rlx; eauto.
  Qed.

  Lemma sim_view_wf past loc ts vw_src vw_tgt
        (SIM: sim_view past loc ts vw_src vw_tgt)
        (WF: View.wf vw_tgt)
    :
      View.wf vw_src.
  Proof.
    inv WF. econs.
    eapply sim_timemap_max.
    - eapply sim_view_rlx; eauto.
    - eapply sim_timemap_closed. eapply sim_view_pln; eauto.
    - etrans; eauto. eapply sim_timemap_le. eapply sim_view_pln; eauto.
  Qed.

  Inductive sim_opt_view (past: Memory.t) (loc: Loc.t) (ts: Time.t)
    : forall (view_src view_tgt: option View.t), Prop :=
  | sim_opt_view_some
      view_src view_tgt
      (SIM: sim_view past loc ts view_src view_tgt):
      sim_opt_view past loc ts (Some view_src) (Some view_tgt)
  | sim_opt_view_none:
      sim_opt_view past loc ts None None
  .
  Hint Constructors sim_opt_view.

  Lemma sim_opt_view_le past loc ts vw_src vw_tgt
        (SIM: sim_opt_view past loc ts vw_src vw_tgt)
    :
      View.opt_le vw_src vw_tgt.
  Proof.
    inv SIM. econs; eauto.
    - eapply sim_view_le; eauto.
    - econs.
  Qed.

  Lemma sim_opt_view_exists past loc ts vw_tgt
        (CLOSED: Memory.closed past)
    :
      exists vw_src, <<SIM: sim_opt_view past loc ts vw_src vw_tgt>>.
  Proof.
    destruct vw_tgt.
    - exploit sim_view_exists; eauto. i. des.
      esplits. econs; eauto.
    - esplits; eauto.
  Qed.

  Lemma sim_opt_view_closed past loc ts vw_src vw_tgt
        (SIM: sim_opt_view past loc ts vw_src vw_tgt)
    :
      add_closed_opt_view vw_src past loc ts.
  Proof.
    inv SIM.
    - econs; eauto. eapply sim_view_closed; eauto.
    - econs; eauto.
  Qed.

  Lemma sim_opt_view_max past loc ts vw_src vw_tgt vw
        (SIM: sim_opt_view past loc ts vw_src vw_tgt)
        (VWLE: View.opt_le vw vw_tgt)
        (CLOSED: add_closed_opt_view vw past loc ts)
    :
      View.opt_le vw vw_src.
  Proof.
    inv VWLE; inv SIM; econs.
    inv CLOSED. eapply sim_view_max; eauto.
  Qed.

  Lemma sim_opt_view_wf past loc ts vw_src vw_tgt
        (SIM: sim_opt_view past loc ts vw_src vw_tgt)
        (WF: View.opt_wf vw_tgt)
    :
      View.opt_wf vw_src.
  Proof.
    inv WF; inv SIM; econs.
    eapply sim_view_wf; eauto.
  Qed.

  Inductive sim_message: forall (past: Memory.t) (loc: Loc.t) (ts: Time.t)
                                (msg_src msg_tgt: Message.t), Prop :=
  | sim_message_concrete
      past loc ts val released_src released_tgt
      (SIM: sim_opt_view past loc ts released_src released_tgt):
      sim_message past loc ts (Message.concrete val released_src) (Message.concrete val released_tgt)
  | sim_message_reserve
      past loc ts
    :
      sim_message past loc ts Message.reserve Message.reserve
  .
  Hint Constructors sim_message.

  Lemma sim_message_le past loc ts msg_src msg_tgt
        (SIM: sim_message past loc ts msg_src msg_tgt)
    :
      Message.le msg_src msg_tgt.
  Proof.
    inv SIM; econs; eauto.
    eapply sim_opt_view_le; eauto.
  Qed.

  Lemma sim_message_exists past loc ts msg_tgt
        (CLOSED: Memory.closed past)
    :
      exists msg_src, <<SIM: sim_message past loc ts msg_src msg_tgt>>.
  Proof.
    destruct msg_tgt; eauto.
    exploit sim_opt_view_exists; eauto. i. des.
    esplits. econs; eauto.
  Qed.

  Lemma sim_message_closed past loc ts msg_src msg_tgt
        (SIM: sim_message past loc ts msg_src msg_tgt)
    :
      add_closed_message msg_src past loc ts.
  Proof.
    inv SIM; econs; eauto.
    eapply sim_opt_view_closed; eauto.
  Qed.

  Lemma sim_message_wf past loc ts msg_src msg_tgt
        (SIM: sim_message past loc ts msg_src msg_tgt)
        (WF: Message.wf msg_tgt)
    :
      Message.wf msg_src.
  Proof.
    inv WF; inv SIM; econs; eauto.
    eapply sim_opt_view_wf; eauto.
  Qed.

End SIMVIEW.

Section PAST.

  Definition all_pasts_memory (mem: Memory.t) (pasts: Loc.t -> Time.t -> option Memory.t): Prop :=
    forall loc from to val released
           (GET: Memory.get loc to mem = Some (from, Message.concrete val released)),
    exists past,
      (<<PAST: pasts loc to = Some past>>) /\
      (<<GET: add_closed_opt_view released past loc to>>) /\
      (<<PREV: forall past' released' (PAST: pasts loc from = Some past')
                      (RELEASED: released = Some released'),
          Memory.future_weak past' past>>).

  Inductive wf_pasts_memory (mem: Memory.t) (pasts: Loc.t -> Time.t -> option Memory.t): Prop :=
  | wf_pasts_memory_intro
      (COMPLETE: all_pasts_memory mem pasts)
      (ONLY: forall loc ts past (PAST: pasts loc ts = Some past),
          (<<CONCRETE: concrete_promised mem loc ts>>) /\
          (<<CURR: Memory.future_weak past mem>>) /\
          (<<CLOSED: Memory.closed past>>)
      )
  .

  Definition pasts_le
             (pasts0: Loc.t -> Time.t -> option Memory.t)
             (pasts1: Loc.t -> Time.t -> option Memory.t): Prop :=
    forall loc to past (PAST0: pasts0 loc to = Some past), pasts1 loc to = Some past.

  Global Program Instance pasts_le_PreOrder: PreOrder pasts_le.
  Next Obligation.
  Proof. ii. auto. Qed.
  Next Obligation.
  Proof. ii. apply H0, H. auto. Qed.

End PAST.


Section ATTACHED.

  Definition promises_not_attached (self prom: Loc.t -> Time.t -> Prop) (mem: Memory.t): Prop :=
    forall loc ts0 ts1 msg
           (PROMISED: self loc ts0)
           (GET: Memory.get loc ts1 mem = Some (ts0, msg)),
      prom loc ts1.

  Definition not_attached_le (others: Loc.t -> Time.t -> Prop)
             (mem0 mem1: Memory.t) :=
    forall loc from (OTHER: others loc from)
           msg to
           (GET: Memory.get loc to mem1 = Some (from, msg)),
    exists to' msg',
      <<GET: Memory.get loc to' mem0 = Some (from, msg')>>.
  Global Program Instance not_attached_le_PreOrder others: PreOrder (not_attached_le others).
  Next Obligation.
  Proof. ii. esplits; eauto. Qed.
  Next Obligation.
  Proof.
    ii. exploit H0; eauto. i. des.
    exploit H; eauto.
  Qed.

End ATTACHED.


Lemma promised_add mem1 loc from to msg mem2
      (ADD: Memory.add mem1 loc from to msg mem2)
  :
    promised mem2 =
    fun loc' =>
      if (Loc.eq_dec loc' loc)
      then fun ts' => if (Time.eq_dec ts' to) then True else promised mem1 loc' ts'
      else promised mem1 loc'.
Proof.
  extensionality loc'. extensionality ts'.
  apply Coq.Logic.PropExtensionality.propositional_extensionality.
  split; i.
  - inv H. destruct msg0. erewrite Memory.add_o in GET; eauto.
    des_ifs.
    + ss. des; clarify.
    + econs; eauto.
    + ss. des; clarify.
    + econs; eauto.
  - des_ifs.
    + ss. des; clarify. econs. eapply Memory.add_get0; eauto.
    + inv H. destruct msg0.
      eapply Memory.add_get1 in GET; eauto. econs; eauto.
    + inv H. destruct msg0.
      eapply Memory.add_get1 in GET; eauto. econs; eauto.
Qed.

Lemma concrete_promised_add mem1 loc from to msg mem2
      (ADD: Memory.add mem1 loc from to msg mem2)
  :
    concrete_promised mem2 =
    fun loc' =>
      if (Loc.eq_dec loc' loc)
      then fun ts' => if (Time.eq_dec ts' to) then (msg <> Message.reserve) else concrete_promised mem1 loc' ts'
      else concrete_promised mem1 loc'.
Proof.
  extensionality loc'. extensionality ts'.
  apply Coq.Logic.PropExtensionality.propositional_extensionality.
  split; i.
  - inv H. erewrite Memory.add_o in GET; eauto.
    des_ifs.
    + ss. des; clarify.
    + ss. des; clarify.
    + econs; eauto.
    + ss. des; clarify.
    + econs; eauto.
  - des_ifs.
    + destruct msg; ss. econs. eapply Memory.add_get0; eauto.
    + inv H.
      eapply Memory.add_get1 in GET; eauto. econs; eauto.
    + inv H.
      eapply Memory.add_get1 in GET; eauto. econs; eauto.
Qed.

Lemma promised_lower mem1 loc from to msg1 msg2 mem2
      (LOWER: Memory.lower mem1 loc from to msg1 msg2 mem2)
  :
    promised mem2 = promised mem1.
Proof.
  extensionality loc'. extensionality ts'.
  apply Coq.Logic.PropExtensionality.propositional_extensionality.
  split; i.
  - inv H. destruct msg. erewrite Memory.lower_o in GET; eauto. des_ifs.
    + ss. des; clarify. econs. eapply (Memory.lower_get0 LOWER); eauto.
    + econs; eauto.
  - inv H. destruct msg. eapply Memory.lower_get1 in GET; eauto.
    des. econs; eauto.
Qed.

Lemma concrete_promised_lower mem1 loc from to msg1 msg2 mem2
      (LOWER: Memory.lower mem1 loc from to msg1 msg2 mem2)
      (MSG: msg1 <> Message.reserve)
  :
    concrete_promised mem2 = concrete_promised mem1.
Proof.
  extensionality loc'. extensionality ts'.
  apply Coq.Logic.PropExtensionality.propositional_extensionality.
  split; i.
  - inv H. erewrite Memory.lower_o in GET; eauto. des_ifs.
    + ss. des; clarify.
      exploit lower_succeed_wf; eauto. i. des. inv MSG_LE; clarify.
      econs; eauto.
    + econs; eauto.
  - inv H. eapply Memory.lower_get1 in GET; eauto.
    des. inv MSG_LE. econs; eauto.
Qed.

Lemma promised_split mem1 loc ts1 ts2 ts3 msg2 msg3 mem2
      (SPLIT: Memory.split mem1 loc ts1 ts2 ts3 msg2 msg3 mem2)
  :
    promised mem2 =
    fun loc' =>
      if (Loc.eq_dec loc' loc)
      then fun ts' => if (Time.eq_dec ts' ts2) then True else promised mem1 loc' ts'
      else promised mem1 loc'.
Proof.
  extensionality loc'. extensionality ts'.
  apply Coq.Logic.PropExtensionality.propositional_extensionality.
  split; i.
  - inv H. destruct msg. erewrite Memory.split_o in GET; eauto.
    des_ifs; try by (des; ss; clarify).
    + ss. des; clarify. econs. eapply (Memory.split_get0 SPLIT); eauto.
    + econs; eauto.
    + econs; eauto.
  - des_ifs.
    + ss. des; clarify. econs. eapply (Memory.split_get0 SPLIT); eauto.
    + inv H. destruct msg. eapply Memory.split_get1 in GET; eauto.
      des. econs; eauto.
    + inv H. destruct msg. eapply Memory.split_get1 in GET; eauto.
      des. econs; eauto.
Qed.

Lemma concrete_promised_split mem1 loc ts1 ts2 ts3 msg2 msg3 mem2
      (SPLIT: Memory.split mem1 loc ts1 ts2 ts3 msg2 msg3 mem2)
  :
    concrete_promised mem2 =
    fun loc' =>
      if (Loc.eq_dec loc' loc)
      then fun ts' => if (Time.eq_dec ts' ts2) then (msg2 <> Message.reserve) else concrete_promised mem1 loc' ts'
      else concrete_promised mem1 loc'.
Proof.
  extensionality loc'. extensionality ts'.
  apply Coq.Logic.PropExtensionality.propositional_extensionality.
  split; i.
  - inv H. erewrite Memory.split_o in GET; eauto.
    des_ifs; try by (des; ss; clarify).
    + ss. des; clarify. econs. eapply (Memory.split_get0 SPLIT); eauto.
    + econs; eauto.
    + econs; eauto.
  - des_ifs.
    + destruct msg2; ss. econs. eapply (Memory.split_get0 SPLIT); eauto.
    + inv H. eapply Memory.split_get1 in GET; eauto.
      des. econs; eauto.
    + inv H. eapply Memory.split_get1 in GET; eauto.
      des. econs; eauto.
Qed.

Lemma promised_remove mem1 loc from to msg mem2
      (REMOVE: Memory.remove mem1 loc from to msg mem2)
  :
    promised mem2 =
    fun loc' =>
      if (Loc.eq_dec loc' loc)
      then fun ts' => if (Time.eq_dec ts' to) then False else promised mem1 loc' ts'
      else promised mem1 loc'.
Proof.
  extensionality loc'. extensionality ts'.
  apply Coq.Logic.PropExtensionality.propositional_extensionality.
  split; i.
  - inv H. destruct msg0. erewrite Memory.remove_o in GET; eauto.
    des_ifs; try by (des; ss; clarify).
    + econs; eauto.
    + econs; eauto.
  - des_ifs.
    + inv H. destruct msg0. eapply Memory.remove_get1 in GET; eauto.
      des; clarify. econs; eauto.
    + inv H. destruct msg0. eapply Memory.remove_get1 in GET; eauto.
      des; clarify. econs; eauto.
Qed.

Lemma concrete_promised_remove mem1 loc from to mem2
      (REMOVE: Memory.remove mem1 loc from to Message.reserve mem2)
  :
    concrete_promised mem2 = concrete_promised mem1.
Proof.
  extensionality loc'. extensionality ts'.
  apply Coq.Logic.PropExtensionality.propositional_extensionality.
  split; i.
  - inv H. erewrite Memory.remove_o in GET; eauto.
    des_ifs; try by (des; ss; clarify). econs; eauto.
  - inv H. dup GET. eapply Memory.remove_get1 in GET; eauto. des.
    + clarify. eapply Memory.remove_get0 in REMOVE. des. clarify.
    + econs; eauto.
Qed.


Inductive reserve_future_memory:
  forall (prom0 mem0 prom1 mem1: Memory.t), Prop :=
| reserve_future_memory_base
    prom0 mem0
  :
    reserve_future_memory
      prom0 mem0 prom0 mem0
| reserve_future_memory_step
    prom0 mem0 prom1 mem1 prom2 mem2
    loc from to kind
    (* (LOC: L loc) *)
    (HD: Memory.promise prom0 mem0 loc from to Message.reserve prom1 mem1 kind)
    (TL: reserve_future_memory prom1 mem1 prom2 mem2)
  :
    reserve_future_memory
      prom0 mem0 prom2 mem2
.
Hint Constructors reserve_future_memory.

Lemma reserve_future_future prom0 mem0 prom1 mem1
      (FUTURE: reserve_future_memory prom0 mem0 prom1 mem1)
  :
    Memory.future mem0 mem1.
Proof.
  ginduction FUTURE; auto. i. transitivity mem1; auto.
  inv HD; clarify.
  - econs; [|refl]. econs; eauto.
  - econs; [|refl]. econs; eauto.
  - econs; [|refl]. econs; eauto.
  - econs; [|refl]. econs; eauto.
Qed.

Lemma reserve_future_concrete_promised prom0 mem0 prom1 mem1
      (FUTURE: reserve_future_memory prom0 mem0 prom1 mem1)
  :
    concrete_promised mem1 <2= concrete_promised mem0.
Proof.
  ginduction FUTURE; auto. i. apply IHFUTURE in PR; auto.
  inv HD; des; clarify.
  - inv PR. erewrite Memory.add_o in GET; eauto.
    des_ifs. econs; eauto.
  - apply lower_succeed_wf in MEM. des. inv MSG_LE.
  - inv PR. erewrite Memory.remove_o in GET; eauto.
    des_ifs. econs; eauto.
Qed.

Lemma reserve_future_wf_pasts_memory prom0 mem0 prom1 mem1 pasts
      (FUTURE: reserve_future_memory prom0 mem0 prom1 mem1)
      (PAST: wf_pasts_memory mem0 pasts)
  :
    wf_pasts_memory mem1 pasts.
Proof.
  ginduction FUTURE; auto. i. eapply IHFUTURE; eauto. inv PAST.
  dup HD. inv HD; des; clarify.
  - econs.
    + ii. erewrite Memory.add_o in GET; eauto.
      des_ifs. exploit COMPLETE; eauto.
    + i. exploit ONLY; eauto. i. des. esplits; eauto.
      * eapply concrete_promised_increase_promise; eauto.
      * etrans; eauto. eapply Memory.future_future_weak.
        econs; [|refl]. econs.
        { econs 1; eauto. }
        { ss. }
        { ss. }
  - apply lower_succeed_wf in MEM. des. inv MSG_LE.
  - econs.
    + ii. erewrite Memory.remove_o in GET; eauto.
      des_ifs. exploit COMPLETE; eauto.
    + i. exploit ONLY; eauto. i. des. esplits; eauto.
      * eapply concrete_promised_increase_promise; eauto.
      * etrans; eauto. eapply Memory.future_future_weak.
        econs; [|refl]. econs.
        { econs 4; eauto. }
        { ss. }
        { ss. }
Qed.

Lemma reserve_future_memory_trans prom0 mem0 prom1 mem1 prom2 mem2
      (FUTURE01: reserve_future_memory prom0 mem0 prom1 mem1)
      (FUTURE12: reserve_future_memory prom1 mem1 prom2 mem2)
  :
    reserve_future_memory prom0 mem0 prom2 mem2.
Proof.
  ginduction FUTURE01; i; eauto.
Qed.

Lemma reserve_future_memory_le prom0 mem0 prom1 mem1
      (MLE: Memory.le prom0 mem0)
      (FUTURE: reserve_future_memory prom0 mem0 prom1 mem1)
  :
    Memory.le prom1 mem1.
Proof.
  ginduction FUTURE; eauto. i.
  eapply IHFUTURE. eapply promise_memory_le; eauto.
Qed.

Lemma reserve_future_memory_bot_none prom0 mem0 prom1 mem1
      (BOTNONE: Memory.bot_none prom0)
      (FUTURE: reserve_future_memory prom0 mem0 prom1 mem1)
  :
    Memory.bot_none prom1.
Proof.
  ginduction FUTURE; eauto. i.
  eapply IHFUTURE. inv HD.
  - eapply Memory.add_bot_none; eauto.
  - eapply Memory.split_bot_none; eauto.
  - eapply Memory.lower_bot_none; eauto.
  - eapply Memory.cancel_bot_none; eauto.
Qed.

Lemma reserve_future_memory_finite prom0 mem0 prom1 mem1
      (FIN: Memory.finite prom0)
      (FUTURE: reserve_future_memory prom0 mem0 prom1 mem1)
  :
    Memory.finite prom1.
Proof.
  ginduction FUTURE; eauto. i.
  eapply IHFUTURE. inv HD.
  - eapply Memory.add_finite; eauto.
  - eapply Memory.split_finite; eauto.
  - eapply Memory.lower_finite; eauto.
  - eapply Memory.remove_finite; eauto.
Qed.
