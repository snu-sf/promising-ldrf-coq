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


Require Import MemoryProps.



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


Section SIM.

  Variable L: Loc.t -> bool.

  Definition in_L (loc: Loc.t) (ts: Time.t) := L loc.

  Inductive sim_memory_content P: option (Time.t * Message.t) -> option (Time.t * Message.t) -> Prop :=
  | sim_memory_content_none
      (NPROM: ~ P)
    :
      sim_memory_content P None None
  | sim_memory_content_normal
      from_src from_tgt msg_src msg_tgt
      (NPROM: ~ P)
      (FROM: Time.le from_tgt from_src)
      (MSG: Message.le msg_src msg_tgt)
      (RESERVE: msg_src = Message.reserve -> msg_tgt = Message.reserve)
    :
      sim_memory_content P (Some (from_src, msg_src)) (Some (from_tgt, msg_tgt))
  | sim_memory_content_forget
      from_src from_tgt msg
      (PROM: P)
      (FROM: Time.le from_tgt from_src)
    :
      sim_memory_content P (Some (from_src, Message.reserve)) (Some (from_tgt, msg))
  .
  Hint Constructors sim_memory_content.

  Definition sim_memory P mem_src mem_tgt : Prop :=
    forall loc ts,
      sim_memory_content (P loc ts) (Memory.get loc ts mem_src) (Memory.get loc ts mem_tgt).

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

  Inductive sim_promise_content (loc: Loc.t) (ts: Time.t)
            (LOC: bool) (others: Time.t -> Prop)
            (rel_src: View.t)
    :
      option Memory.t -> option (Time.t * Message.t) -> option (Time.t * Message.t) -> Prop :=
  | sim_promise_content_none
      past
    :
      sim_promise_content loc ts LOC others rel_src past None None
  | sim_promise_content_normal_concrete
      (NPROM: ~ LOC)
      past from val released_src released_tgt
      (MSG: sim_opt_view past loc ts released_src released_tgt)
      (RELVIEW: forall released (MSG: released_src = Some released),
          add_weak_closed_view rel_src past loc ts)
    :
      sim_promise_content loc ts LOC others rel_src
                          (Some past)
                          (Some (from, Message.concrete val released_src))
                          (Some (from, Message.concrete val released_tgt))
  | sim_promise_content_normal_reserve
      (NPROM: ~ LOC)
      past from
    :
      sim_promise_content loc ts LOC others rel_src
                          past
                          (Some (from, Message.reserve))
                          (Some (from, Message.reserve))
  | sim_promise_content_forget
      (PROM: LOC)
      past from_src from_tgt msg
      (OTHERS: forall (OTHER: others from_tgt), Time.lt from_tgt from_src)
      (NOTHERS: forall (NOTHER: ~ others from_tgt), from_tgt = from_src)
    :
      sim_promise_content loc ts LOC others rel_src
                          past
                          (Some (from_src, Message.reserve))
                          (Some (from_tgt, msg))
  .
  Hint Constructors sim_promise_content.

  Definition sim_promise (others: Loc.t -> Time.t -> Prop)
             (rel_src: LocFun.t View.t)
             (pasts: Loc.t -> Time.t -> option Memory.t)
             (prom_src prom_tgt: Memory.t): Prop :=
    forall loc ts,
      sim_promise_content loc ts (L loc) (others loc) (rel_src loc) (pasts loc ts)
                          (Memory.get loc ts prom_src)
                          (Memory.get loc ts prom_tgt).

  Inductive sim_local (others: Loc.t -> Time.t -> Prop) (pasts: Loc.t -> Time.t -> option Memory.t)
            (lc_src lc_tgt: Local.t): Prop :=
  | forget_local_intro
      (TVIEW : TView.le lc_src.(Local.tview) lc_tgt.(Local.tview))
      (PROMS: sim_promise others lc_src.(Local.tview).(TView.rel) pasts lc_src.(Local.promises) lc_tgt.(Local.promises))
    :
      sim_local others pasts lc_src lc_tgt
  .

  Inductive sim_statelocal P (pasts: Loc.t -> Time.t -> option Memory.t):
    sigT (@Language.state ProgramEvent.t) * Local.t -> sigT (@Language.state ProgramEvent.t) * Local.t -> Prop :=
  | forget_statelocal_intro
      st lc_src lc_tgt
      (LOCAL: sim_local P pasts lc_src lc_tgt)
    :
      sim_statelocal P pasts (st, lc_src) (st, lc_tgt)
  .

  Inductive all_promises (proms: Ident.t -> Loc.t -> Time.t -> Prop): Loc.t -> Time.t -> Prop :=
  | all_promises_intro
      tid loc ts
      (PROMS: proms tid loc ts)
    :
      all_promises proms loc ts
  .
  Hint Constructors all_promises.

  Definition promises_not_attached (prom: Loc.t -> Time.t -> Prop) (mem: Memory.t): Prop :=
    forall loc ts0 ts1 msg
           (LOC: L loc)
           (PROMISED: prom loc ts0)
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

  (* Inductive sim_config *)
  (*           (proms: Ident.t -> Loc.t -> Time.t -> Prop) *)
  (*           (pasts: Loc.t -> Time.t -> option Memory.t) *)
  (*           (c_src c_tgt: Configuration.t) *)
  (*   : Prop := *)
  (* | sim_config_intro *)
  (*     (THS: forall tid, option_rel *)
  (*                         (sim_statelocal (proms tid) pasts) *)
  (*                         (IdentMap.find tid c_src.(Configuration.threads)) *)
  (*                         (IdentMap.find tid c_tgt.(Configuration.threads))) *)
  (*     (PAST: wf_pasts_memory c_src.(Configuration.memory) pasts) *)
  (*     (MEM: sim_memory (all_promises proms) c_src.(Configuration.memory) c_tgt.(Configuration.memory)) *)
  (*     (SC: TimeMap.le c_src.(Configuration.sc) c_tgt.(Configuration.sc)) *)
  (*     (ATTACH: not_attached (all_promises proms) c_src.(Configuration.memory)) *)
  (*     (WFSRC: Configuration.wf c_src) *)
  (*     (WFTGT: Configuration.wf c_tgt) *)
  (* (* TODO: can remove all promises *) *)
  (* . *)

  Lemma sim_read_step P others pasts lc_src lc_tgt mem_src mem_tgt loc to val released_tgt ord
        lc_tgt'
        (STEPTGT: Local.read_step lc_tgt mem_tgt loc to val released_tgt ord lc_tgt')
        (NOREAD: ~ P loc to)
        (MEM: sim_memory P mem_src mem_tgt)
        (LOCAL: sim_local others pasts lc_src lc_tgt)
    :
      exists lc_src' released_src,
        (<<STEPSRC: Local.read_step lc_src mem_src loc to val released_src ord lc_src'>>) /\
        (<<SIM: sim_local others pasts lc_src' lc_tgt'>>) /\
        (<<RELEASEDMLE: View.opt_le released_src released_tgt>>) /\
        (<<GETSRC: exists from, Memory.get loc to mem_src = Some (from, Message.concrete val released_src)>>) /\
        (<<GETSRC: exists from, Memory.get loc to mem_tgt = Some (from, Message.concrete val released_tgt)>>)
  .
  Proof.
    inv LOCAL. inv STEPTGT.
    specialize (MEM loc to). rewrite GET in *. inv MEM; ss. inv MSG.
    esplits.
    - econs; eauto. eapply TViewFacts.readable_mon; eauto.
      + eapply TVIEW.
      + refl.
    - econs; ss; eauto. eapply read_tview_mon; eauto. refl.
    - auto.
    - eauto.
    - eauto.
  Qed.

  Lemma sim_fence_step others pasts lc_src lc_tgt sc_src sc_tgt ordr ordw
        sc_tgt' lc_tgt'
        (STEPTGT: Local.fence_step lc_tgt sc_tgt ordr ordw lc_tgt' sc_tgt')
        (SC: TimeMap.le sc_src sc_tgt)
        (LOCAL: sim_local others pasts lc_src lc_tgt)
    :
      exists lc_src' sc_src',
        (<<STEPSRC: Local.fence_step lc_src sc_src ordr ordw lc_src' sc_src'>>) /\
        (<<SC: TimeMap.le sc_src' sc_tgt'>>) /\
        (<<SIM: sim_local others pasts lc_src' lc_tgt'>>)
  .
  Proof.
    inv LOCAL. inv STEPTGT.
    assert (TVIEWLE:
              TView.le
                (TView.write_fence_tview
                   (TView.read_fence_tview (Local.tview lc_src) ordr) sc_src ordw)
                (TView.write_fence_tview
                   (TView.read_fence_tview (Local.tview lc_tgt) ordr) sc_tgt ordw)).
    { eapply write_fence_tview_mon_same_ord; eauto.
      eapply read_fence_tview_mon_same_ord; eauto. }
    esplits.
    - econs; ss; eauto. ii.
      specialize (PROMS loc t). rewrite GET in *. inv PROMS; ss.
      exploit RELEASE; eauto. ss. ii. inv MSG; ss.
    - eapply write_fence_fc_mon_same_ord; eauto.
      eapply read_fence_tview_mon_same_ord; eauto.
    - econs; ss; eauto. ii.
      specialize (PROMS loc ts). des_ifs.
      + inv PROMS; econs; ss; eauto. i.
        exfalso. inv MSG; ss. exploit RELEASE; eauto; ss.
        destruct ordw; eauto.
      + inv PROMS; econs; ss; eauto. i.
        exfalso. inv MSG; ss. exploit RELEASE; eauto; ss.
        destruct ordw; eauto.
      + inv PROMS; econs; ss; eauto. i.
        exfalso. inv MSG; ss. exploit RELEASE; eauto; ss.
        destruct ordw; eauto.
  Qed.

  Lemma sim_promise_consistent prom_self pasts lc_src lc_tgt
        (CONSISTENT: Local.promise_consistent lc_tgt)
        (SIM: sim_local prom_self pasts lc_src lc_tgt)
    :
      Local.promise_consistent lc_src.
  Proof.
    inv SIM. ii.
    specialize (PROMS loc ts). rewrite PROMISE in *. inv PROMS.
    exploit CONSISTENT; eauto. i. eapply TimeFacts.le_lt_lt; eauto.
    inv TVIEW. inv CUR. auto.
  Qed.

  Lemma sim_failure_step prom_self pasts lc_src lc_tgt
        (STEPTGT: Local.failure_step lc_tgt)
        (SIM: sim_local prom_self pasts lc_src lc_tgt)
    :
      Local.failure_step lc_src.
  Proof.
    inv STEPTGT. econs.
    eapply sim_promise_consistent; eauto.
  Qed.

  (* Lemma sim_memory_max_ts P mem_src mem_tgt loc *)
  (*       (CLOSEDSRC: Memory.closed mem_src) *)
  (*       (SIM: sim_memory P mem_src mem_tgt) *)
  (*   : *)
  (*     Time.le (Memory.max_ts loc mem_src) (Memory.max_ts loc mem_tgt). *)
  (* Proof. *)
  (*   inv SIM. *)
  (*   exploit Memory.max_ts_spec. *)
  (*   { apply CLOSEDSRC. } *)
  (*   i. des. dup GET. apply memory_get_ts_strong in GET0. des; clarify. *)
  (*   - rewrite GET1. apply Time.bot_spec. *)
  (*   - exploit COVERED. *)
  (*     + econs; eauto. econs; eauto. reflexivity. *)
  (*     +  i. inv x. inv ITV. etrans; eauto. ss. *)
  (*        eapply Memory.max_ts_spec; eauto. *)
  (* Qed. *)

  (* Lemma sim_memory_max_concrete_timemap P mem_src mem_tgt sc_src sc_tgt *)
  (*       (SIM: sim_memory P mem_src mem_tgt) *)
  (*       (SCSRC: Memory.max_concrete_timemap mem_src sc_src) *)
  (*       (SCTGT: Memory.max_concrete_timemap mem_tgt sc_tgt) *)
  (*   : *)
  (*     TimeMap.le sc_src sc_tgt. *)
  (* Proof. *)
  (*   inv SIM. ii. specialize (SCSRC loc). specialize (SCTGT loc). *)
  (*   inv SCSRC. inv SCTGT. des. *)
  (*   exploit CONCRETE. *)
  (*   - econs. eapply GET. *)
  (*   - i. inv x. eapply MAX0; eauto. *)
  (* Qed. *)

  (* Lemma sim_memory_cap P mem_src mem_tgt cap_src cap_tgt *)
  (*       (SIM: sim_memory P mem_src mem_tgt) *)
  (*       (CLOSEDSRC: Memory.closed mem_src) *)
  (*       (CLOSEDTGT: Memory.closed mem_tgt) *)
  (*       (CAPSRC: Memory.cap mem_src cap_src) *)
  (*       (CAPTGT: Memory.cap mem_tgt cap_tgt) *)
  (*   : *)
  (*     sim_memory P cap_src cap_tgt. *)
  (* Proof. *)
  (*   dup SIM. inv SIM. econs. *)
  (*   - i. eapply Memory.cap_inv in GETTGT; eauto. des; clarify. *)
  (*     apply COMPLETE in GETTGT; eauto. des. *)
  (*     esplits; eauto. eapply Memory.cap_le; eauto. refl. *)
  (*   - i. inv PR. eapply Memory.cap_inv in GET; try apply CAPSRC; eauto. *)
  (*     des; clarify. exploit CONCRETE; eauto. *)
  (*     + econs; eauto. *)
  (*     + i. inv x. eapply Memory.cap_le in GET0. *)
  (*       * econs; eauto. *)
  (*       * eauto. *)
  (*       * refl. *)
  (*   - i. rewrite <- memory_cap_covered; eauto. *)
  (*     rewrite <- memory_cap_covered in COVERED0; try apply CAPSRC; eauto. *)
  (*     inv COVERED0. econs; eauto. ss. rewrite <- MAXTS. auto. *)
  (*   - i. erewrite (@Memory.cap_max_ts mem_src cap_src); eauto. *)
  (*     erewrite (@Memory.cap_max_ts mem_tgt cap_tgt); eauto. *)
  (*     f_equal. auto. *)
  (* Qed. *)

  (* Lemma future_sim_promise P pasts0 pasts1 vw_src vw_tgt proms_src proms_tgt *)
  (*       (SIM: sim_promise P pasts0 vw_src vw_tgt proms_src proms_tgt) *)
  (*       (PASTLE: pasts_le pasts0 pasts1) *)
  (*   : *)
  (*     sim_promise P pasts1 vw_src vw_tgt proms_src proms_tgt. *)
  (* Proof. *)
  (*   inv SIM. econs; eauto. i. *)
  (*   apply NFORGET in GETSRC; auto. des. des_ifs; des; clarify. *)
  (*   - esplits; eauto. *)
  (*   - esplits; eauto. *)
  (* Qed. *)

  (* Lemma future_sim_local prom pasts0 pasts1 lc_src lc_tgt *)
  (*       (SIM: sim_local prom pasts0 lc_src lc_tgt) *)
  (*       (PASTLE: pasts_le pasts0 pasts1) *)
  (*   : *)
  (*     sim_local prom pasts1 lc_src lc_tgt. *)
  (* Proof. *)
  (*   inv SIM. econs; eauto. eapply future_sim_promise; eauto. *)
  (* Qed. *)

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
      (LOC: L loc)
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

  Lemma sim_promise_step_normal others pasts mem_src mem_tgt rel_src prom_src prom_tgt
        loc from to msg_tgt prom_tgt' mem_tgt' kind_tgt
        (NLOC: ~ L loc)
        (STEPTGT: Memory.promise prom_tgt mem_tgt loc from to msg_tgt prom_tgt' mem_tgt' kind_tgt)
        (MEM: sim_memory (others \2/ (in_L /2\ promised prom_src)) mem_src mem_tgt)
        (MEMSRC: Memory.closed mem_src)
        (MEMTGT: Memory.closed mem_tgt)
        (WFSRC: Memory.le prom_src mem_src)
        (WFTGT: Memory.le prom_tgt mem_tgt)
        (RELWF: View.wf (rel_src loc))
        (RELCONSISTENT: forall val released (MSG: msg_tgt = Message.concrete val released),
            Time.le ((rel_src loc).(View.rlx) loc) to)
        (RELSRC: Memory.closed_view (rel_src loc) mem_src)
        (PROMISE: sim_promise others rel_src pasts prom_src prom_tgt)
        (PAST: wf_pasts_memory mem_src pasts)
        (PROMATTACH: promises_not_attached (promised prom_src) mem_src)
        (OTHERSWF: forall loc' to', others loc' to' -> L loc')
    :
      exists msg_src kind_src pasts' prom_src' mem_src',
        (<<STEPSRC: Memory.promise prom_src mem_src loc from to msg_src prom_src' mem_src' kind_src>>) /\
        (<<MEM: sim_memory (others \2/ (in_L /2\ promised prom_src)) mem_src' mem_tgt'>>) /\
        (<<ATTACHEDLE: not_attached_le others mem_src mem_src'>>) /\
        (<<PROMISE: sim_promise others rel_src pasts' prom_src' prom_tgt'>>) /\
        (<<PAST: wf_pasts_memory mem_src' pasts'>>) /\
        (<<PASTLE: pasts_le pasts pasts'>>) /\
        (<<PROMATTACH: promises_not_attached (promised prom_src') mem_src'>>) /\
        (<<CLOSED: Memory.closed_message msg_src mem_src'>>)
  .
  Proof.
    inv STEPTGT.

    (* add case *)
    - hexploit (@sim_message_exists mem_src loc to msg_tgt); eauto. i. des.

      exploit add_succeed_wf; try apply MEM0. i. des.
      hexploit (@Memory.add_exists mem_src loc from to msg_src); ss.
      { i. specialize (MEM loc to2). rewrite GET2 in *. inv MEM; cycle 1.
        { exfalso. apply NLOC. des; ss. eapply OTHERSWF; eauto. }
        ii. eapply DISJOINT; eauto.
        inv RHS. econs; ss. eapply TimeFacts.le_lt_lt; eauto. }
      { eapply sim_message_wf; eauto. }
      intros [mem_src' ADDMEMSRC].
      exploit Memory.add_exists_le; try apply ADDMEMSRC; eauto.
      intros [prom_src' ADDPROMSRC].

      assert (ATTACHSRC: forall val released to' msg'
                                (MSG: msg_src = Message.concrete val released)
                                (GET: Memory.get loc to' mem_src = Some (to, msg')), False).
      { i. clarify. inv SIM.
        specialize (MEM loc to'). rewrite GET in *. inv MEM; cycle 1.
        { exfalso. apply NLOC. des; ss. eapply OTHERSWF; eauto. }
        inv FROM.
        { exploit DISJOINT; auto.
          - symmetry. eapply H.
          - instantiate (1:=to). econs; ss. refl.
          - econs; ss. eapply memory_get_ts_le; eauto.
        }
        { inv H0. exploit ATTACH; eauto. }
      }

      assert (MSGTO: Memory.message_to msg_src loc to).
      { inv SIM; econs. inv TS. etrans; eauto.
        apply sim_opt_view_le in SIM0. apply View.unwrap_opt_le in SIM0.
        inv SIM0. auto.
      }

      assert (PROMISESRC: Memory.promise prom_src mem_src loc from to msg_src prom_src' mem_src' Memory.op_kind_add).
      { econs; eauto. }

      assert (CLOSEDMSG: Memory.closed_message msg_src mem_src').
      { destruct msg_src; auto.
        eapply add_closed_message_add_closed; eauto.
        eapply sim_message_closed; eauto. }

      assert (FUTURE: Memory.future mem_src mem_src').
      { econs; [|refl]. econs; eauto. }

      exists msg_src, Memory.op_kind_add,
      (fun loc' to' => if loc_ts_eq_dec (loc', to') (loc, to) then (if msg_src then (Some mem_src) else None) else pasts loc' to'),
      prom_src', mem_src'. splits; auto.
      + ii. erewrite (@Memory.add_o mem_src'); eauto.
        erewrite (@Memory.add_o mem_tgt'); eauto. des_ifs.
        ss. des; clarify. econs; eauto.
        * ii. des; ss. eapply OTHERSWF in H; eauto.
        * refl.
        * eapply sim_message_le; eauto.
        * i. clarify. inv SIM.
          auto.
      + ii. erewrite (@Memory.add_o mem_src') in GET; eauto. des_ifs; eauto.
        ss. des; clarify. eapply OTHERSWF in OTHER; ss.
      + ii. erewrite (@Memory.add_o prom_src'); eauto.
        erewrite (@Memory.add_o prom_tgt'); eauto. des_ifs.
        * ss. des; clarify. inv SIM; econs; eauto.
          i. eapply add_closed_add_weak_closed_view, closed_add_closed_view. auto.
        * ss. des; clarify. inv SIM; econs; eauto.
      + inv PAST. econs.
        * ii. erewrite (@Memory.add_o mem_src') in GET; eauto.
          destruct (loc_ts_eq_dec (loc0, to0) (loc, to)).
          { ss. des; clarify. esplits; eauto.
            - eapply sim_message_closed in SIM. inv SIM. inv CLOSED; econs; auto.
            - i. des_ifs.
              { exfalso. ss. des; clarify. eapply Time.lt_strorder; eauto. }
              guardH o. exploit ONLY; eauto. i. des; auto.
          }
          { guardH o. exploit COMPLETE; eauto. i. des.
            esplits; eauto. des_ifs. ss. des; clarify.
            exfalso. inv SIM. eapply ATTACHSRC; eauto.
          }
        * i. des_ifs.
          { ss. des; clarify. splits; auto.
            - econs. eapply Memory.add_get0; eauto.
            - apply Memory.future_future_weak. auto.
          }
          { guardH o. exploit ONLY; eauto. i. des. splits; auto.
            - eapply concrete_promised_increase_promise; eauto.
            - etrans; eauto. apply Memory.future_future_weak. auto. }
      + ii. destruct (loc_ts_eq_dec (loc0, to0) (loc, to)); auto.
        ss. des; clarify. exfalso.
        inv PAST. apply ONLY in PAST0. des. inv CONCRETE.
        apply Memory.add_get0 in ADDMEMSRC. des. clarify.
      + ii. erewrite (@Memory.add_o mem_src' mem_src) in GET; eauto. des_ifs.
        { ss. des; clarify. }
        guardH o. inv PROMISED.
        erewrite (@Memory.add_o prom_src') in GET0; eauto. des_ifs.
        { ss. des; clarify. }
        guardH o0. exploit PROMATTACH; eauto.
        { econs; eauto. }
        i. inv x. destruct msg1. econs. eapply Memory.add_get1; eauto.

    - exploit split_succeed_wf; try apply PROMISES. i. des. clarify.
      dup PROMISE. specialize (PROMISE0 loc ts3). rewrite GET2 in *.
      inv PAST. inv PROMISE0; ss; [destruct released_src as [released_src|]|].

      (* split normal message with non-none view *)
      { exploit ONLY; eauto. i. des.
        hexploit (@sim_message_exists past loc to (Message.concrete val' released')); eauto.
        i. des.

        hexploit (@Memory.split_exists prom_src loc from to ts3 msg_src); ss.
        { eauto. }
        { eapply sim_message_wf; eauto. }
        intros [prom_src' SPLITPROMSRC].
        exploit Memory.split_exists_le; try apply SPLITPROMSRC; eauto.
        intros [mem_src' SPLITMEMSRC].

        assert (MSGTO: Memory.message_to msg_src loc to).
        { inv SIM; econs. inv TS. etrans; eauto.
          apply sim_opt_view_le in SIM0. apply View.unwrap_opt_le in SIM0.
          inv SIM0. auto.
        }

        assert (PROMISESRC: Memory.promise prom_src mem_src loc from to msg_src prom_src' mem_src' (Memory.op_kind_split ts3 (Message.concrete val (Some released_src)))).
        { econs; eauto. inv SIM. eauto. }

        assert (CLOSEDMSG: Memory.closed_message msg_src mem_src').
        { destruct msg_src; auto.
          eapply add_closed_message_split_closed; eauto.
          eapply add_closed_message_future_add_closed; eauto.
          eapply sim_message_closed; eauto. }

        assert (FUTURE: Memory.future mem_src mem_src').
        { econs; [|refl]. econs; eauto. }

        exists msg_src, (Memory.op_kind_split ts3 (Message.concrete val (Some released_src))),
        (fun loc' to' => if loc_ts_eq_dec (loc', to') (loc, to)
                         then (Some past)
                         else pasts loc' to'),
        prom_src', mem_src'. splits; auto.
        + ii. erewrite (@Memory.split_o mem_src'); eauto.
          erewrite (@Memory.split_o mem_tgt'); eauto. des_ifs.
          { ss. des; clarify. econs; eauto.
            * ii. des; ss. eapply OTHERSWF in H1; eauto.
            * refl.
            * eapply sim_message_le; eauto.
            * i. clarify. inv SIM.
          }
          { guardH o. ss. des; clarify. econs; eauto.
            * ii. des; ss. eapply OTHERSWF in H1; eauto.
            * refl.
            * econs. eapply sim_opt_view_le; eauto.
            * i. clarify.
          }
        + ii. erewrite (@Memory.split_o mem_src') in GET; eauto. des_ifs; eauto.
          * ss. des; clarify. eapply OTHERSWF in OTHER; ss.
          * guardH o. ss. des; clarify. eapply OTHERSWF in OTHER; ss.
        + ii. erewrite (@Memory.split_o prom_src'); eauto.
          erewrite (@Memory.split_o prom_tgt'); eauto. des_ifs.
          * ss. des; clarify. inv SIM; econs; eauto.
            i. eapply add_weak_closed_view_consistent; eauto.
          * guardH o. ss. des; clarify. inv SIM.
            rewrite <- H0. econs; eauto.
        + econs.
          * ii. erewrite (@Memory.split_o mem_src') in GET; eauto.
            destruct (loc_ts_eq_dec (loc0, to0) (loc, to)).
            { ss. des; clarify. esplits; eauto.
              - eapply sim_message_closed in SIM. inv SIM. inv CLOSED0; econs; auto.
              - i. des_ifs.
                { exfalso. ss. des; clarify. eapply Time.lt_strorder; eauto. }
                guardH o. exploit COMPLETE; eauto. i. des.
                eapply PREV in PAST; eauto. rewrite PAST0 in *. clarify.
            }
            guardH o. destruct (loc_ts_eq_dec (loc0, to0) (loc, ts3)).
            { ss. des; clarify. rewrite <- H0 in *. esplits; eauto.
              - inv MSG. econs. eapply sim_view_closed; eauto.
              - i. des_ifs.
                + refl.
                + ss. des; clarify.
            }
            { guardH o0. exploit COMPLETE; eauto. i. des.
              esplits; eauto. i. des_ifs.
              - ss. des; clarify. exfalso.
                exploit memory_get_from_inj.
                { eapply Memory.split_get0 in SPLITMEMSRC. des. eapply GET5. }
                { instantiate (1:=Message.concrete val0 (Some released'0)).
                  instantiate (1:=to0). erewrite Memory.split_o; [|eauto]. des_ifs.
                  - ss. unguard. des; clarify.
                  - ss. unguard. des; clarify. }
                { i. des; clarify.
                  - unguard. des; clarify.
                  - eapply Time.lt_strorder; eauto.
                  - eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
                    + eapply TS12.
                    + eapply Time.bot_spec. }
              - guardH o1. exploit COMPLETE; eauto.
            }
          * i. des_ifs.
            { ss. des; clarify. splits; auto.
              - eapply Memory.split_get0 in SPLITMEMSRC. des.
                inv SIM. econs; eauto.
              - etrans; eauto. apply Memory.future_future_weak. auto.
            }
            { guardH o. exploit ONLY; eauto. i. des. splits; auto.
              - eapply concrete_promised_increase_promise; eauto.
              - etrans; eauto. apply Memory.future_future_weak. auto. }
        + ii. destruct (loc_ts_eq_dec (loc0, to0) (loc, to)); auto.
          ss. des; clarify. exfalso.
          apply ONLY in PAST0. des. inv CONCRETE0.
          apply Memory.split_get0 in SPLITMEMSRC. des. clarify.
        + ii. inv PROMISED.
          erewrite (@Memory.split_o mem_src' mem_src) in GET; eauto. des_ifs.
          * ss. des; clarify.
          * guardH o. ss. des; clarify.
          * guardH o. guardH o0.
            ss. erewrite (@Memory.split_o prom_src') in GET0; eauto. des_ifs.
            { ss. des; clarify. }
            { ss. des; clarify. }
            guardH o1. guardH o2. exploit PROMATTACH; eauto.
            { econs; eauto. }
            i. inv x.
            econs. erewrite (@Memory.split_o prom_src'); eauto.
            instantiate (1:=msg1). des_ifs.
            { ss. des; clarify. }
            { ss. des; clarify. }
      }

      (* split normal message with none view *)
      { exploit ONLY; eauto. i. des.
        hexploit (@sim_message_exists mem_src loc to (Message.concrete val' released')); eauto.

        i. des.
        hexploit (@Memory.split_exists prom_src loc from to ts3 msg_src); ss.
        { eauto. }
        { eapply sim_message_wf; eauto. }
        intros [prom_src' SPLITPROMSRC].
        exploit Memory.split_exists_le; try apply SPLITPROMSRC; eauto.
        intros [mem_src' SPLITMEMSRC].

        assert (MSGTO: Memory.message_to msg_src loc to).
        { inv SIM; econs. inv TS. etrans; eauto.
          apply sim_opt_view_le in SIM0. apply View.unwrap_opt_le in SIM0.
          inv SIM0. auto.
        }

        assert (PROMISESRC: Memory.promise prom_src mem_src loc from to msg_src prom_src' mem_src' (Memory.op_kind_split ts3 (Message.concrete val None))).
        { econs; eauto. inv SIM. eauto. }

        assert (CLOSEDMSG: Memory.closed_message msg_src mem_src').
        { destruct msg_src; auto.
          eapply add_closed_message_split_closed; eauto.
          eapply sim_message_closed; eauto. }

        assert (FUTURE: Memory.future mem_src mem_src').
        { econs; [|refl]. econs; eauto. }

        exists msg_src, (Memory.op_kind_split ts3 (Message.concrete val None)),
        (fun loc' to' => if loc_ts_eq_dec (loc', to') (loc, to)
                         then (Some mem_src)
                         else pasts loc' to'),
        prom_src', mem_src'. splits; auto.
        + ii. erewrite (@Memory.split_o mem_src'); eauto.
          erewrite (@Memory.split_o mem_tgt'); eauto. des_ifs.
          { ss. des; clarify. econs; eauto.
            * ii. des; ss. eapply OTHERSWF in H1; eauto.
            * refl.
            * eapply sim_message_le; eauto.
            * i. clarify. inv SIM.
          }
          { guardH o. ss. des; clarify. econs; eauto.
            * ii. des; ss. eapply OTHERSWF in H1; eauto.
            * refl.
            * i. clarify.
          }
        + ii. erewrite (@Memory.split_o mem_src') in GET; eauto. des_ifs; eauto.
          * ss. des; clarify. eapply OTHERSWF in OTHER; ss.
          * guardH o. ss. des; clarify. eapply OTHERSWF in OTHER; ss.
        + ii. erewrite (@Memory.split_o prom_src'); eauto.
          erewrite (@Memory.split_o prom_tgt'); eauto. des_ifs.
          * ss. des; clarify. inv SIM; econs; eauto.
            i. eapply add_closed_add_weak_closed_view, closed_add_closed_view. auto.
          * guardH o. ss. des; clarify. inv SIM.
            rewrite <- H0. econs; eauto.
        + econs.
          * ii. erewrite (@Memory.split_o mem_src') in GET; eauto.
            destruct (loc_ts_eq_dec (loc0, to0) (loc, to)).
            { ss. des; clarify. esplits; eauto.
              - eapply sim_message_closed in SIM. inv SIM. inv CLOSED0; econs; auto.
              - i. des_ifs.
                { exfalso. ss. des; clarify. eapply Time.lt_strorder; eauto. }
                guardH o. eapply ONLY; eauto.
            }
            guardH o. destruct (loc_ts_eq_dec (loc0, to0) (loc, ts3)).
            { ss. des; clarify. esplits; eauto.
              - econs.
              - i. clarify. }
            { guardH o0. exploit COMPLETE; eauto. i. des.
              esplits; eauto. i. des_ifs.
              - ss. des; clarify. exfalso.
                exploit memory_get_from_inj.
                { eapply Memory.split_get0 in SPLITMEMSRC. des. eapply GET5. }
                { instantiate (1:=Message.concrete val0 (Some released'0)).
                  instantiate (1:=to0). erewrite Memory.split_o; [|eauto]. des_ifs.
                  - ss. unguard. des; clarify.
                  - ss. unguard. des; clarify. }
                { i. des; clarify.
                  - unguard. des; clarify.
                  - eapply Time.lt_strorder; eauto.
                  - eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
                    + eapply TS12.
                    + eapply Time.bot_spec. }
              - guardH o1. exploit COMPLETE; eauto.
            }
          * i. des_ifs.
            { ss. des; clarify. splits; auto.
              - eapply Memory.split_get0 in SPLITMEMSRC. des.
                inv SIM. econs; eauto.
              - apply Memory.future_future_weak. auto.
            }
            { guardH o. exploit ONLY; eauto. i. des. splits; auto.
              - eapply concrete_promised_increase_promise; eauto.
              - etrans; eauto. apply Memory.future_future_weak. auto. }
        + ii. destruct (loc_ts_eq_dec (loc0, to0) (loc, to)); auto.
          ss. des; clarify. exfalso.
          apply ONLY in PAST0. des. inv CONCRETE0.
          apply Memory.split_get0 in SPLITMEMSRC. des. clarify.
        + ii. inv PROMISED.
          erewrite (@Memory.split_o mem_src' mem_src) in GET; eauto. des_ifs.
          * ss. des; clarify.
          * guardH o. ss. des; clarify.
          * guardH o. guardH o0.
            ss. erewrite (@Memory.split_o prom_src') in GET0; eauto. des_ifs.
            { ss. des; clarify. }
            { ss. des; clarify. }
            guardH o1. guardH o2. exploit PROMATTACH; eauto.
            { econs; eauto. }
            i. inv x.
            econs. erewrite (@Memory.split_o prom_src'); eauto.
            instantiate (1:=msg1). des_ifs.
            { ss. des; clarify. }
            { ss. des; clarify. }
      }

      (* split reserve *)
      { hexploit (@sim_message_exists mem_src loc to (Message.concrete val' released')); eauto.

        i. des.
        hexploit (@Memory.split_exists prom_src loc from to ts3 msg_src); ss.
        { eauto. }
        { eapply sim_message_wf; eauto. }
        intros [prom_src' SPLITPROMSRC].
        exploit Memory.split_exists_le; try apply SPLITPROMSRC; eauto.
        intros [mem_src' SPLITMEMSRC].

        assert (MSGTO: Memory.message_to msg_src loc to).
        { inv SIM; econs. inv TS. etrans; eauto.
          apply sim_opt_view_le in SIM0. apply View.unwrap_opt_le in SIM0.
          inv SIM0. auto.
        }

        assert (PROMISESRC: Memory.promise prom_src mem_src loc from to msg_src prom_src' mem_src' (Memory.op_kind_split ts3 Message.reserve)).
        { econs; eauto. inv SIM. eauto. }

        assert (CLOSEDMSG: Memory.closed_message msg_src mem_src').
        { destruct msg_src; auto.
          eapply add_closed_message_split_closed; eauto.
          eapply sim_message_closed; eauto. }

        assert (FUTURE: Memory.future mem_src mem_src').
        { econs; [|refl]. econs; eauto. }

        exists msg_src, (Memory.op_kind_split ts3 Message.reserve),
        (fun loc' to' => if loc_ts_eq_dec (loc', to') (loc, to)
                         then (Some mem_src)
                         else pasts loc' to'),
        prom_src', mem_src'. splits; auto.
        + ii. erewrite (@Memory.split_o mem_src'); eauto.
          erewrite (@Memory.split_o mem_tgt'); eauto. des_ifs.
          { ss. des; clarify. econs; eauto.
            * ii. des; ss. eapply OTHERSWF in H; eauto.
            * refl.
            * eapply sim_message_le; eauto.
            * i. clarify. inv SIM.
          }
          { guardH o. ss. des; clarify. econs; eauto.
            * ii. des; ss. eapply OTHERSWF in H; eauto.
            * refl.
          }
        + ii. erewrite (@Memory.split_o mem_src') in GET; eauto. des_ifs; eauto.
          * ss. des; clarify. eapply OTHERSWF in OTHER; ss.
          * guardH o. ss. des; clarify. eapply OTHERSWF in OTHER; ss.
        + ii. erewrite (@Memory.split_o prom_src'); eauto.
          erewrite (@Memory.split_o prom_tgt'); eauto. des_ifs.
          * ss. des; clarify. inv SIM; econs; eauto.
            i. eapply add_closed_add_weak_closed_view, closed_add_closed_view. auto.
          * guardH o. ss. des; clarify. inv SIM. econs; eauto.
        + econs.
          * ii. erewrite (@Memory.split_o mem_src') in GET; eauto.
            destruct (loc_ts_eq_dec (loc0, to0) (loc, to)).
            { ss. des; clarify. esplits; eauto.
              - eapply sim_message_closed in SIM. inv SIM. inv CLOSED; econs; auto.
              - i. des_ifs.
                { exfalso. ss. des; clarify. eapply Time.lt_strorder; eauto. }
                guardH o. eapply ONLY; eauto.
            }
            guardH o. destruct (loc_ts_eq_dec (loc0, to0) (loc, ts3)).
            { ss. }
            { guardH o0. exploit COMPLETE; eauto. i. des.
              esplits; eauto. i. des_ifs.
              - ss. des; clarify. exfalso.
                exploit memory_get_from_inj.
                { eapply Memory.split_get0 in SPLITMEMSRC. des. eapply GET5. }
                { instantiate (1:=Message.concrete val (Some released'0)).
                  instantiate (1:=to0). erewrite Memory.split_o; [|eauto]. des_ifs.
                  - ss. unguard. des; clarify.
                  - ss. unguard. des; clarify. }
                { i. des; clarify.
                  - unguard. des; clarify.
                  - eapply Time.lt_strorder; eauto.
                  - eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
                    + eapply TS12.
                    + eapply Time.bot_spec. }
              - guardH o1. exploit COMPLETE; eauto.
            }
          * i. des_ifs.
            { ss. des; clarify. splits; auto.
              - eapply Memory.split_get0 in SPLITMEMSRC. des.
                inv SIM. econs; eauto.
              - apply Memory.future_future_weak. auto.
            }
            { guardH o. exploit ONLY; eauto. i. des. splits; auto.
              - eapply concrete_promised_increase_promise; eauto.
              - etrans; eauto. apply Memory.future_future_weak. auto. }
        + ii. destruct (loc_ts_eq_dec (loc0, to0) (loc, to)); auto.
          ss. des; clarify. exfalso.
          apply ONLY in PAST0. des. inv CONCRETE.
          apply Memory.split_get0 in SPLITMEMSRC. des. clarify.
        + ii. inv PROMISED.
          erewrite (@Memory.split_o mem_src' mem_src) in GET; eauto. des_ifs.
          * ss. des; clarify.
          * guardH o. ss. des; clarify.
          * guardH o. guardH o0.
            ss. erewrite (@Memory.split_o prom_src') in GET0; eauto. des_ifs.
            { ss. des; clarify. }
            { ss. des; clarify. }
            guardH o1. guardH o2. exploit PROMATTACH; eauto.
            { econs; eauto. }
            i. inv x.
            econs. erewrite (@Memory.split_o prom_src'); eauto.
            instantiate (1:=msg1). des_ifs.
            { ss. des; clarify. }
            { ss. des; clarify. }
      }

    (* lower case *)
    - exploit lower_succeed_wf; try apply PROMISES. i. des. clarify.
      dup PROMISE. specialize (PROMISE0 loc to). rewrite GET in *.
      inv PAST. inv PROMISE0; ss.

      exploit ONLY; eauto. i. des.
      hexploit (@sim_message_exists past loc to msg_tgt); eauto. i. des.

      inv MSG_LE. dup SIM. inv SIM.
      assert (VIEWLE: View.opt_le released_src0 released_src).
      { eapply sim_opt_view_max; eauto.
        - etrans; eauto. eapply sim_opt_view_le; eauto.
        - eapply sim_opt_view_closed; eauto. }

      hexploit (@Memory.lower_exists prom_src loc from to (Message.concrete val released_src) (Message.concrete val released_src0)); ss.
      { eapply sim_message_wf; eauto. }
      { econs; eauto. }

      intros [prom_src' LOWERPROMSRC].
      exploit Memory.lower_exists_le; try apply LOWERPROMSRC; eauto.
      intros [mem_src' LOWERMEMSRC].

      assert (MSGTO: Memory.message_to (Message.concrete val released_src0) loc to).
      { econs. inv TS. etrans; eauto.
        apply sim_opt_view_le in SIM1. apply View.unwrap_opt_le in SIM1.
        inv SIM1. auto.
      }

      assert (PROMISESRC: Memory.promise prom_src mem_src loc from to (Message.concrete val released_src0) prom_src' mem_src' (Memory.op_kind_lower (Message.concrete val released_src))).
      { econs; eauto. }

      assert (CLOSEDMSG: Memory.closed_message (Message.concrete val released_src0) mem_src').
      { eapply add_closed_message_lower_closed; eauto.
        eapply add_closed_message_future_add_closed; eauto.
        eapply sim_message_closed; eauto. }

      assert (FUTURE: Memory.future mem_src mem_src').
      { econs; [|refl]. econs; eauto. }

      exists (Message.concrete val released_src0), (Memory.op_kind_lower (Message.concrete val released_src)), pasts, prom_src', mem_src'. splits; auto.
      + ii. erewrite (@Memory.lower_o mem_src'); eauto.
        erewrite (@Memory.lower_o mem_tgt'); eauto. des_ifs.
        ss. des; clarify. econs; eauto.
        * ii. des; ss. eapply OTHERSWF in H1; eauto.
        * refl.
        * eapply sim_message_le; eauto.
        * i. clarify.
      + ii. erewrite (@Memory.lower_o mem_src') in GET0; eauto. des_ifs; eauto.
        ss. des; clarify. eapply OTHERSWF in OTHER; ss.
      + ii. erewrite (@Memory.lower_o prom_src'); eauto.
        erewrite (@Memory.lower_o prom_tgt'); eauto. des_ifs.
        ss. des; clarify. rewrite <- H0. econs; eauto.
        i. clarify. inv VIEWLE. eapply RELVIEW; eauto.
      + econs.
        * ii. erewrite (@Memory.lower_o mem_src') in GET0; eauto. des_ifs.
          { ss. des; clarify. esplits; eauto.
            - inv SIM1. econs.
              eapply sim_view_closed; eauto. econs.
            - i. exploit COMPLETE; eauto. i. des.
              rewrite PAST0 in *. clarify. inv VIEWLE. eauto.
          }
          { guardH o. exploit COMPLETE; eauto. }
        * i. exploit ONLY; eauto. i. des. splits; auto.
          { eapply concrete_promised_increase_promise; eauto. }
          { etrans; eauto. apply Memory.future_future_weak. auto. }
      + refl.
      + ii. erewrite Memory.lower_o in GET0; eauto. des_ifs.
        { ss. des; clarify. }
        guardH o. exploit PROMATTACH; eauto.
        { inv PROMISED. erewrite Memory.lower_o in GET1; eauto. des_ifs.
          - ss. des; clarify.
          - econs; eauto. }
        i. inv x. destruct msg0. eapply Memory.lower_get1 in GET1; eauto.
        des. econs; eauto.

    (* cancel case *)
    - exploit Memory.remove_get0; try apply PROMISES. i. des.
      dup PROMISE. specialize (PROMISE0 loc to). rewrite GET in *.
      inv PROMISE0; ss.

      hexploit (@Memory.remove_exists prom_src loc from to Message.reserve); ss.
      intros [prom_src' REMOVEPROMSRC].
      exploit Memory.remove_exists_le; try apply REMOVEPROMSRC; eauto.
      intros [mem_src' REMOVEMEMSRC].

      assert (PROMISESRC: Memory.promise prom_src mem_src loc from to Message.reserve prom_src' mem_src' Memory.op_kind_cancel).
      { econs; eauto. }

      assert (FUTURE: Memory.future mem_src mem_src').
      { econs; [|refl]. econs; eauto. }

      exists Message.reserve, Memory.op_kind_cancel, pasts, prom_src', mem_src'.
      splits; auto.
      + ii. erewrite (@Memory.remove_o mem_src'); eauto.
        erewrite (@Memory.remove_o mem_tgt'); eauto. des_ifs.
        ss. des; clarify. econs; eauto.
        * ii. des; ss. eapply OTHERSWF in H; eauto.
      + ii. erewrite (@Memory.remove_o mem_src') in GET1; eauto. des_ifs; eauto.
      + ii. erewrite (@Memory.remove_o prom_src'); eauto.
        erewrite (@Memory.remove_o prom_tgt'); eauto. des_ifs.
      + inv PAST. econs.
        * ii. erewrite (@Memory.remove_o mem_src') in GET1; eauto. des_ifs.
          { exploit COMPLETE; eauto. }
        * i. exploit ONLY; eauto. i. des. splits; auto.
          { eapply concrete_promised_increase_promise; eauto. }
          { etrans; eauto. apply Memory.future_future_weak. auto. }
      + refl.
      + ii. inv PROMISED. erewrite (@Memory.remove_o prom_src') in GET2; eauto.
        erewrite (@Memory.remove_o mem_src' mem_src) in GET1; eauto. des_ifs.
        exploit PROMATTACH; eauto.
        { econs; eauto. }
        i. inv x. econs. instantiate (1:=msg1).
        erewrite Memory.remove_o; eauto. des_ifs.
        ss. des; clarify.
  Qed.

  Lemma sim_write_step_normal
        others pasts lc_src lc_tgt sc_src sc_tgt mem_src mem_tgt
        lc_tgt' sc_tgt' mem_tgt' loc from to val ord releasedm_tgt released_tgt kind_tgt
        releasedm_src
        (NLOC: ~ L loc)
        (STEPTGT: Local.write_step lc_tgt sc_tgt mem_tgt loc from to val releasedm_tgt released_tgt ord lc_tgt' sc_tgt' mem_tgt' kind_tgt)
        (SC: TimeMap.le sc_src sc_tgt)
        (MEM: sim_memory (others \2/ (in_L /2\ promised lc_src.(Local.promises))) mem_src mem_tgt)
        (SCSRC: Memory.closed_timemap sc_src mem_src)
        (SCTGT: Memory.closed_timemap sc_tgt mem_tgt)
        (MEMSRC: Memory.closed mem_src)
        (MEMTGT: Memory.closed mem_tgt)
        (LOCALSRC: Local.wf lc_src mem_src)
        (LOCALTGT: Local.wf lc_tgt mem_tgt)
        (SIM: sim_local others pasts lc_src lc_tgt)
        (PAST: wf_pasts_memory mem_src pasts)
        (PROMATTACH: promises_not_attached (promised lc_src.(Local.promises)) mem_src)
        (OTHERSWF: forall loc' to', others loc' to' -> L loc')
        (CONSISTENT: Local.promise_consistent lc_tgt')

        (RELEASEDMCLOSEDPAST: forall past (PAST: pasts loc from = Some past),
            add_closed_opt_view releasedm_src past loc from)
        (RELEASEDMSOME: forall releasedm_src' (RELEASEDM: releasedm_src = Some releasedm_src'),
            exists past, <<PAST: pasts loc from = Some past>>)
        (RELEASEDMCLOSED: Memory.closed_opt_view releasedm_src mem_src)
        (RELEASEDMLE: View.opt_le releasedm_src releasedm_tgt)
        (RELEASEDMWFSRC: View.opt_wf releasedm_src)
        (RELEASEDMWFTGT: View.opt_wf releasedm_tgt)
    :
      exists pasts' lc_src' sc_src' mem_src' released_src kind_src,
        (<<STEPSRC: Local.write_step lc_src sc_src mem_src loc from to val releasedm_src released_src ord lc_src' sc_src' mem_src' kind_src>>) /\
        (<<MEM: sim_memory (others \2/ (in_L /2\ promised lc_src'.(Local.promises))) mem_src' mem_tgt'>>) /\
        (<<ATTACHEDLE: not_attached_le others mem_src mem_src'>>) /\
        (<<PROMATTACH: promises_not_attached (promised lc_src'.(Local.promises)) mem_src'>>) /\
        (<<SC: TimeMap.le sc_src' sc_tgt'>>) /\
        (<<SIM: sim_local others pasts' lc_src' lc_tgt'>>) /\
        (<<PAST: wf_pasts_memory mem_src' pasts'>>) /\
        (<<PASTLE: pasts_le pasts pasts'>>)
  (* TODO: condition about event *)
  .
  Proof.
    inv STEPTGT. inv WRITE. inv SIM. inv LOCALSRC. inv LOCALTGT.
    set (msg_src := (Message.concrete val (TView.write_released (Local.tview lc_src) sc_src loc to releasedm_src ord))).
    assert (MSGWF: Message.wf msg_src).
    { unfold msg_src. econs.
      eapply TViewFacts.write_future0; eauto. }

    assert (WRITABLESRC: TView.writable (TView.cur (Local.tview lc_src)) sc_src loc to ord).
    { inv TVIEW. eapply TViewFacts.writable_mon; eauto. refl. }

    assert (RELEASESRC: Ordering.le Ordering.strong_relaxed ord -> Memory.nonsynch_loc loc (Local.promises lc_src)).
    { i. hexploit RELEASE; eauto. intros NONSYNC.
      ii. specialize (PROMS loc t).
      erewrite GET in PROMS. inv PROMS; ss.
      inv MSG; ss. exploit NONSYNC; eauto. ss. }

    assert (MSGLE: Message.le
                     msg_src
                     (Message.concrete val (TView.write_released (Local.tview lc_tgt) sc_tgt loc to releasedm_tgt ord))).
    { unfold msg_src. econs. eapply TViewFacts.write_released_mon; eauto. refl. }

    assert (CONSISTENTTGT:
              forall to' val' released' from'
                     (GET: Memory.get loc to' promises2
                           = Some (from', Message.concrete val' released')),
                Time.le to to').
    { i. exploit CONSISTENT; eauto. i. ss. left. eapply TimeFacts.le_lt_lt; eauto.
      unfold TimeMap.join, TimeMap.singleton. setoid_rewrite LocFun.add_spec_eq.
      eapply Time.join_r; eauto. }

    assert (MSGTO: Memory.message_to msg_src loc to).
    { unfold msg_src. econs. ss.
      transitivity (View.rlx
                      (View.unwrap (TView.write_released (Local.tview lc_tgt) sc_tgt loc to releasedm_tgt ord))
                      loc).
      - exploit TViewFacts.write_released_mon; eauto.
        { refl. } i. apply View.unwrap_opt_le in x0. inv x0. eauto.
      - inv PROMISE; ss; eauto.
        + inv TS. auto.
        + inv TS. auto.
        + inv TS. auto. }

    inv PROMISE.

    (* add case *)
    - exploit add_succeed_wf; try apply MEM0. i. des.
      hexploit (@Memory.add_exists mem_src loc from to msg_src); ss.
      { i. specialize (MEM loc to2). rewrite GET2 in *. inv MEM; cycle 1.
        { exfalso. apply NLOC. des; ss. eapply OTHERSWF; eauto. }
        ii. eapply DISJOINT; eauto.
        inv RHS. econs; ss. eapply TimeFacts.le_lt_lt; eauto. }
      intros [mem_src' ADDMEMSRC].
      exploit Memory.add_exists_le; try apply ADDMEMSRC; eauto.
      intros [prom_src' ADDPROMSRC].

      assert (ATTACHSRC: forall to' msg'
                                (GET: Memory.get loc to' mem_src = Some (to, msg')), False).
      { i. specialize (MEM loc to'). rewrite GET in *. inv MEM; cycle 1.
        { exfalso. apply NLOC. des; ss. eapply OTHERSWF; eauto. }
        inv FROM.
        { exploit DISJOINT; auto.
          - symmetry. eapply H.
          - instantiate (1:=to). econs; ss. refl.
          - econs; ss. eapply memory_get_ts_le; eauto.
        }
        { inv H0. exploit ATTACH; eauto. }
      }

      assert (PROMISESRC: Memory.promise lc_src.(Local.promises) mem_src loc from to msg_src prom_src' mem_src' Memory.op_kind_add).
      { econs; eauto. }

      assert (CLOSEDMSG: Memory.closed_message msg_src mem_src').
      { unfold msg_src.
        eapply add_closed_message_add_closed; eauto. econs.
        eapply write_released_add_closed; eauto.
        - eapply closed_add_closed_opt_view; eauto.
        - refl. }

      assert (FUTURE: Memory.future mem_src mem_src').
      { econs; [|refl]. econs; eauto. }

      hexploit (@Memory.remove_exists prom_src' loc from to msg_src).
      { eapply Memory.add_get0; eauto. } intros [prom_src'' REMOVESRC].
      hexploit (@MemoryFacts.add_remove_eq (Local.promises lc_src) prom_src' prom_src''); eauto.
      i. subst.
      hexploit (@MemoryFacts.add_remove_eq (Local.promises lc_tgt) promises0 promises2); eauto.
      i. subst.

      eexists (fun loc' to' => if loc_ts_eq_dec (loc', to') (loc, to) then (if msg_src then (Some mem_src) else None) else pasts loc' to'), _, _, mem_src', _, _.
      splits; auto.
      + econs; eauto.
      + ii. erewrite (@Memory.add_o mem_src'); eauto.
        erewrite (@Memory.add_o mem_tgt'); eauto. des_ifs.
        ss. des; clarify. econs; eauto.
        * ii. des; ss. eapply OTHERSWF in H; eauto.
        * refl.
        * i. unfold msg_src. clarify.
      + ii. erewrite (@Memory.add_o mem_src') in GET; eauto. des_ifs; eauto.
        ss. des; clarify. eapply OTHERSWF in OTHER; ss.
      + ii. ss. erewrite (@Memory.add_o mem_src') in GET; eauto. des_ifs.
        * ss. des; clarify.
        * exploit PROMATTACH; eauto.
      + auto.
      + econs; ss.
        * eapply TViewFacts.write_tview_mon; eauto. refl.
        * ii. specialize (PROMS loc0 ts). dup PROMS.
          setoid_rewrite LocFun.add_spec.
          destruct (LocSet.Facts.eq_dec loc0 loc); clarify.
          { destruct (loc_ts_eq_dec (loc, ts) (loc, to)).
            - ss. des; clarify.
              eapply Memory.add_get0 in PROMISES1.
              eapply Memory.add_get0 in ADDPROMSRC. des.
              erewrite GET. erewrite GET1. econs.
            - inv PROMS0; econs; eauto.
              i. des_ifs.
              + exfalso. exploit RELEASE; eauto.
                { destruct ord; ss. }
                ss. i. subst. inv MSG.
              + eapply join_view_add_weak_closed; eauto.
                eapply add_weak_closed_view_consistent.
                * eapply add_closed_add_weak_closed_view.
                  eapply singleton_view_add_closed; eauto.
                  inv PAST. exploit ONLY; eauto. i. des; auto.
                * apply View.singleton_ur_wf.
                * ss. unfold TimeMap.singleton.
                  setoid_rewrite LocFun.add_spec_eq. eauto.
          }
          { des_ifs. ss. des; clarify. }
      + inv PAST. econs.
        * ii. erewrite (@Memory.add_o mem_src') in GET; eauto.
          destruct (loc_ts_eq_dec (loc0, to0) (loc, to)).
          { ss. des; clarify. esplits; eauto.
            - eapply write_released_add_closed; eauto; cycle 1.
              { left. eauto. }
              destruct releasedm_src; econs.
              exploit RELEASEDMSOME; eauto. i. des.
              exploit RELEASEDMCLOSEDPAST; eauto. i. inv x.
              exploit ONLY; eauto. i. des.
              eapply add_closed_view_future_add_closed; eauto.
            - i. des_ifs.
              { exfalso. ss. des; clarify. eapply Time.lt_strorder; eauto. }
              guardH o. exploit ONLY; eauto. i. des; auto.
          }
          { guardH o. exploit COMPLETE; eauto. i. des.
            esplits; eauto. des_ifs. ss. des; clarify.
            i. clarify. exfalso. eapply ATTACHSRC; eauto.
          }
        * i. des_ifs.
          { ss. des; clarify. splits; auto.
            - econs. eapply Memory.add_get0; eauto.
            - apply Memory.future_future_weak. auto.
          }
          { guardH o. exploit ONLY; eauto. i. des. splits; auto.
            - eapply concrete_promised_increase_promise; eauto.
            - etrans; eauto. apply Memory.future_future_weak. auto. }
      + ii. destruct (loc_ts_eq_dec (loc0, to0) (loc, to)); auto.
        ss. des; clarify. exfalso.
        inv PAST. apply ONLY in PAST0. des. inv CONCRETE.
        apply Memory.add_get0 in ADDMEMSRC. des. clarify.

    - exploit split_succeed_wf; try apply PROMISES1. i. des. clarify.
      dup PROMS. specialize (PROMS0 loc ts3). erewrite GET2 in PROMS0. inv PAST.

      assert (GETSRC: exists msg3_src,
                 Memory.get loc ts3 (Local.promises lc_src) = Some (from, msg3_src)).
      { inv PROMS0; eauto. exploit NOTHERS; eauto. i. subst. eauto. } des.

      hexploit (@Memory.split_exists lc_src.(Local.promises) loc from to ts3 msg_src); ss.
      { eauto. }
      intros [prom_src' SPLITPROMSRC].
      exploit Memory.split_exists_le; try apply SPLITPROMSRC; eauto.
      intros [mem_src' SPLITMEMSRC].

      assert (PROMISESRC: Memory.promise lc_src.(Local.promises) mem_src loc from to msg_src prom_src' mem_src' (Memory.op_kind_split ts3 msg3_src)).
      { econs; eauto. unfold msg_src. eauto. }

      assert (CLOSEDMSG: Memory.closed_message msg_src mem_src').
      { unfold msg_src.
        eapply add_closed_message_split_closed; eauto. econs.
        eapply write_released_add_closed; eauto.
        - eapply closed_add_closed_opt_view; eauto.
        - refl. }

      assert (FUTURE: Memory.future mem_src mem_src').
      { econs; [|refl]. econs; eauto. }

      hexploit (@Memory.remove_exists prom_src' loc from to msg_src).
      { eapply Memory.split_get0 in SPLITPROMSRC. des. auto. }
      intros [prom_src'' REMOVESRC].

      assert (PROMISEDSAME: promised (Local.promises lc_src) = promised prom_src'').
      { extensionality loc'. extensionality ts'.
        apply Coq.Logic.PropExtensionality.propositional_extensionality.
        destruct (loc_ts_eq_dec (loc', ts') (loc, ts3)).
        - split; i.
          + inv H. econs.
            erewrite split_remove_shorten; eauto. des_ifs.
            ss. des; clarify.
          + inv H.
            erewrite split_remove_shorten in GET; eauto. des_ifs.
            * ss. des; clarify. econs; eauto.
            * econs; eauto.
        - split; i.
          + inv H. econs.
            erewrite split_remove_shorten; eauto.
            destruct (loc_ts_eq_dec (loc', ts') (loc, ts3)).
            * exfalso. ss. des; clarify.
            * eauto.
          + inv H.
            erewrite split_remove_shorten in GET; eauto. des_ifs.
            * ss. des; clarify.
            * econs; eauto. }

      set (pasts' := fun loc' to' => if loc_ts_eq_dec (loc', to') (loc, to)
                                     then
                                       (match msg3_src with
                                        | Message.concrete _ (Some _) => pasts loc ts3
                                        | _ => Some mem_src
                                        end)
                                     else pasts loc' to').

      eexists pasts', _, _, mem_src', _, _.
      splits; auto.
      + econs; eauto.
      + ii. erewrite (@Memory.split_o mem_src'); eauto.
        erewrite (@Memory.split_o mem_tgt'); eauto.
        ss. erewrite <- PROMISEDSAME.
        destruct (loc_ts_eq_dec (loc0, ts) (loc, to)).
        { ss. des; clarify. econs; eauto.
          * ii. des; ss. eapply OTHERSWF in H; eauto.
          * refl.
          * unfold msg_src. i. clarify.
        }
        guardH o. destruct (loc_ts_eq_dec (loc0, ts) (loc, ts3)).
        { ss. des; clarify. specialize (MEM loc ts3).
          eapply PROMISES in GETSRC. erewrite GETSRC in *.
          eapply PROMISES0 in GET2. erewrite GET2 in *. inv MEM.
          - econs; eauto. refl.
          - des.
            + eapply OTHERSWF in PROM. clarify.
            + clear - PROM NLOC. clarify. }
        { eauto. }
      + ii. erewrite (@Memory.split_o mem_src') in GET; eauto. des_ifs; eauto.
        * ss. des; clarify. eapply OTHERSWF in OTHER; ss.
        * guardH o. ss. des; clarify. eapply OTHERSWF in OTHER; ss.
      + ii. ss. erewrite <- PROMISEDSAME in *.
        erewrite (@Memory.split_o mem_src') in GET; eauto. des_ifs; eauto.
        * ss. des; clarify.
        * ss. des; clarify.
      + auto.
      + econs; ss.
        * eapply TViewFacts.write_tview_mon; eauto. refl.
        * ii. dup PROMS. specialize (PROMS1 loc0 ts).
          unfold pasts'. setoid_rewrite LocFun.add_spec.
          erewrite (split_remove_shorten REMOVESRC); eauto.
          erewrite (split_remove_shorten REMOVE); eauto.
          destruct (LocSet.Facts.eq_dec loc0 loc); clarify.
          { specialize (CONSISTENTTGT ts).
            erewrite (split_remove_shorten REMOVE) in CONSISTENTTGT; eauto.
            destruct (loc_ts_eq_dec (loc, ts) (loc, ts3)).
            - ss. des; clarify. erewrite GET2 in PROMS1. erewrite GETSRC in PROMS1.
              inv PROMS1; try (econs; eauto); cycle 1.
              { i. apply OTHERSWF in OTHER. clarify. }
              destruct (loc_ts_eq_dec (loc, ts3) (loc, to)).
              { ss. des; clarify. exfalso. eapply Time.lt_strorder; eauto. }
              ss. des; clarify. econs; eauto.
              i. des_ifs.
              + exfalso. exploit RELEASE; eauto.
                { destruct ord; ss. }
                ss. i. subst. inv MSG.
              + eapply join_view_add_weak_closed; eauto.
                eapply add_weak_closed_view_consistent.
                * eapply add_closed_add_weak_closed_view.
                  eapply singleton_view_add_closed; eauto.
                  exploit ONLY; eauto. i. des; auto.
                * apply View.singleton_ur_wf.
                * ss. unfold TimeMap.singleton.
                  setoid_rewrite LocFun.add_spec_eq.
                  exploit CONSISTENTTGT; eauto.
            - ss. des; clarify. inv PROMS1; try (econs; eauto).
              destruct (loc_ts_eq_dec (loc, ts) (loc, to)).
              { ss. des; clarify.
                apply Memory.split_get0 in SPLITPROMSRC. des. erewrite GET in *. clarify. }
              ss. des; clarify. econs; eauto.
              i. subst. des_ifs.
              + exfalso. exploit RELEASE.
                { destruct ord; ss. }
                { symmetry. eapply H2. }
                i. des_ifs. inv MSG.
              + eapply join_view_add_weak_closed; eauto.
                eapply add_weak_closed_view_consistent.
                * eapply add_closed_add_weak_closed_view.
                  eapply singleton_view_add_closed; eauto.
                  exploit ONLY; eauto. i. des; auto.
                * apply View.singleton_ur_wf.
                * ss. unfold TimeMap.singleton.
                  setoid_rewrite LocFun.add_spec_eq.
                  exploit CONSISTENTTGT; eauto.
          }
          { des_ifs; ss; des; clarify. }
      + econs.
        * ii. erewrite (@Memory.split_o mem_src') in GET; eauto.
          unfold pasts'. destruct (loc_ts_eq_dec (loc0, to0) (loc, to)).
          { ss. des; clarify.
            destruct (loc_ts_eq_dec (loc, from0) (loc, to)); ss.
            { des; clarify. exfalso. eapply Time.lt_strorder; eauto. }
            guardH o. rewrite GETSRC in *.
            inv PROMS0; clarify; [destruct released_src as [released_src|]|].
            - exploit ONLY; eauto. i. des.
              assert (ORD: Ordering.le Ordering.strong_relaxed ord = false).
              { destruct (Ordering.le Ordering.strong_relaxed ord) eqn:ORD; ss.
                exfalso. exploit RELEASE; eauto. ss.
                i. inv MSG. ss. }
              exploit COMPLETE.
              { apply PROMISES. eauto. } i. des. rewrite PAST in *. clarify.
              destruct (pasts loc from0) as [past'|] eqn:PAST0.
              + exploit ONLY; eauto. i. des.
                exploit PREV; eauto. i.
                esplits; eauto.
                * eapply write_released_add_closed_relaxed; ss.
                  { inv TVIEW_WF. inv WRITABLE.
                    eapply add_weak_closed_view_consistent; eauto.
                    transitivity (View.rlx (TView.cur (Local.tview lc_tgt)) loc).
                    - transitivity (View.rlx (TView.cur (Local.tview lc_src)) loc).
                      + specialize (REL_CUR loc). inv REL_CUR. auto.
                      + inv TVIEW. inv CUR0. auto.
                    - left. auto. }
                  { eapply add_closed_opt_view_future_add_closed; eauto. }
                  { left. auto. }
              + destruct releasedm_src as [releasedm_src|].
                { exploit RELEASEDMSOME; eauto. i. des. clarify. }
                esplits; eauto.
                eapply write_released_add_closed_relaxed; ss.
                  { inv TVIEW_WF. inv WRITABLE.
                    eapply add_weak_closed_view_consistent; eauto.
                    transitivity (View.rlx (TView.cur (Local.tview lc_tgt)) loc).
                    - transitivity (View.rlx (TView.cur (Local.tview lc_src)) loc).
                      + specialize (REL_CUR loc). inv REL_CUR. auto.
                      + inv TVIEW. inv CUR0. auto.
                    - left. auto. }
                { econs. }
                { refl. }
            - destruct (pasts loc from0) as [past'|] eqn:PAST.
              + exploit ONLY; eauto. i. des.
                esplits; eauto.
                * eapply write_released_add_closed; eauto; cycle 1.
                  { left. eauto. }
                  exploit RELEASEDMCLOSEDPAST; eauto. i.
                  eapply add_closed_opt_view_future_add_closed; eauto.
                * i. clarify.
              + destruct releasedm_src as [releasedm_src|].
                { exploit RELEASEDMSOME; eauto. i. des. clarify. }
                esplits; eauto.
                * eapply write_released_add_closed; eauto; cycle 1.
                  { left. eauto. } econs.
                * i. clarify.
            - destruct (pasts loc from0) as [past'|] eqn:PAST.
              + exploit ONLY; eauto. i. des.
                esplits; eauto.
                * eapply write_released_add_closed; eauto; cycle 1.
                  { left. eauto. }
                  exploit RELEASEDMCLOSEDPAST; eauto. i.
                  eapply add_closed_opt_view_future_add_closed; eauto.
                * i. clarify.
              + destruct releasedm_src as [releasedm_src|].
                { exploit RELEASEDMSOME; eauto. i. des. clarify. }
                esplits; eauto.
                * eapply write_released_add_closed; eauto; cycle 1.
                  { left. eauto. } econs.
                * i. clarify.
          }
          { guardH o.
            destruct (loc_ts_eq_dec (loc0, to0) (loc, ts3)).
            - ss. des; clarify. exploit COMPLETE.
              { eapply PROMISES. eauto. } i. des.
              esplits; eauto. i.
              destruct (loc_ts_eq_dec (loc, from0) (loc, from0)); cycle 1.
              { ss. des; clarify. } des_ifs. refl.
            - guardH o0.
              exploit COMPLETE; eauto. i. des. esplits; eauto.

              i. destruct (loc_ts_eq_dec (loc0, from0) (loc, to)).
              + ss. des; clarify. exfalso.
                exploit memory_get_from_inj.
                { eapply Memory.split_get0 in SPLITMEMSRC. des. eapply GET5. }
                { instantiate (2:=to0). erewrite Memory.split_o; eauto.
                  destruct (loc_ts_eq_dec (loc, to0) (loc, to)).
                  { ss. unguard. des; clarify. }
                  destruct (loc_ts_eq_dec (loc, to0) (loc, ts3)).
                  { simpl in *. unguard. exfalso. guardH o1. des; clarify. }
                  eapply GET. }
                i. des.
                * unguard. des; clarify.
                * clarify. exfalso. eapply Time.lt_strorder; eauto.
                * clarify. exfalso. eapply Time.lt_strorder.
                  eapply TimeFacts.lt_le_lt.
                  { eapply TS12. }
                  { eapply Time.bot_spec; eauto. }
              + guardH o1. eapply PREV; eauto.
          }

        * unfold pasts'. i. des_ifs.
          { ss. des; clarify.
            exploit ONLY; eauto. i. des. splits; auto.
            - eapply Memory.split_get0 in SPLITMEMSRC. des. econs; eauto.
            - etrans; eauto. eapply Memory.future_future_weak; eauto.
          }
          { ss. des; clarify. esplits; eauto.
            - eapply Memory.split_get0 in SPLITMEMSRC. des. econs; eauto.
            - eapply Memory.future_future_weak; eauto.
          }
          { ss. des; clarify. esplits; eauto.
            - eapply Memory.split_get0 in SPLITMEMSRC. des. econs; eauto.
            - eapply Memory.future_future_weak; eauto.
          }
          { guardH o. ss.
            exploit ONLY; eauto. i. des. splits; auto.
            - eapply concrete_promised_increase_promise; eauto.
            - etrans; eauto. eapply Memory.future_future_weak; eauto.
          }

      + unfold pasts'. ii.
        destruct (loc_ts_eq_dec (loc0, to0) (loc, to)); auto.
        ss. des; clarify. exfalso.
        exploit ONLY; eauto. i. des. inv CONCRETE.
        eapply Memory.split_get0 in SPLITMEMSRC. des. clarify.

    - exploit lower_succeed_wf; try apply PROMISES1. i. des. clarify.
      dup PROMS. specialize (PROMS0 loc to). erewrite GET in PROMS0.
      inv PAST. inv PROMS0; clarify. inv MSG_LE.

      exploit COMPLETE; eauto. i. des.
      exploit ONLY; eauto. i. des. rewrite PAST in *. clarify.

      assert (RELEASEDLE:
                View.opt_le
                  (TView.write_released (Local.tview lc_src) sc_src loc to releasedm_src ord)
                  released_src).
      { destruct released_src as [released_src|].
        - eapply sim_opt_view_max; eauto.
          + etrans; eauto.
            eapply TViewFacts.write_released_mon; eauto. refl.
          + eapply write_released_add_closed_relaxed.
            * ss.
            * eapply RELVIEW; eauto.
            * instantiate (1:=from).
              destruct releasedm_src as [releasedm_src|]; [|econs].
              exploit RELEASEDMSOME; eauto. i. des.
              exploit RELEASEDMCLOSEDPAST; eauto. i.
              exploit PREV; eauto. i.
              eapply add_closed_opt_view_future_add_closed; eauto.
            * left. auto.
            * destruct (Ordering.le Ordering.strong_relaxed ord) eqn:ORD; ss.
              exfalso. exploit RELEASE; eauto. ss. i. clarify. inv MSG.
        - inv MSG. etrans; eauto.
          eapply TViewFacts.write_released_mon; eauto. refl.
      }


      hexploit (@lower_remove_exists lc_src.(Local.promises) loc from to (Message.concrete val0 released_src) msg_src); ss.
      { unfold msg_src. econs; eauto. }
      intros [prom_src' [prom_src'' [LOWERPROMSRC [REMOVEPROMSRC SPEC]]]].
      exploit Memory.lower_exists_le; try apply LOWERPROMSRC; eauto.
      intros [mem_src' LOWERMEMSRC].

      assert (PROMISESRC: Memory.promise lc_src.(Local.promises) mem_src loc from to msg_src prom_src' mem_src' (Memory.op_kind_lower (Message.concrete val0 released_src))).
      { econs; eauto. }

      assert (CLOSEDMSG: Memory.closed_message msg_src mem_src').
      { unfold msg_src.
        eapply add_closed_message_lower_closed; eauto. econs.
        eapply write_released_add_closed; eauto.
        - eapply closed_add_closed_opt_view; eauto.
        - refl. }

      assert (FUTURE: Memory.future mem_src mem_src').
      { econs; [|refl]. econs; eauto. }

      assert (PROMISEDDECREASE: promised prom_src'' = promised (Local.promises lc_src) /2\ (fun loc' to' => __guard__(loc' <> loc \/ to' <> to))).
      { extensionality loc'. extensionality to'.
        apply Coq.Logic.PropExtensionality.propositional_extensionality.
        split; i.
        - inv H0. erewrite SPEC in GET1. des_ifs. split; auto. econs; eauto.
        - destruct H0. guardH H1. inv H0.
          econs. erewrite SPEC. des_ifs; eauto.
          exfalso. ss. unguard. des; clarify. }

      eexists pasts, _, _, mem_src', _, _.
      splits; auto.
      + econs; eauto.
      + ss. ii. erewrite PROMISEDDECREASE.
        erewrite (@Memory.lower_o mem_src'); eauto.
        erewrite (@Memory.lower_o mem_tgt'); eauto. des_ifs.
        * ss. des; clarify. econs; eauto.
          { ii. des.
            - eapply OTHERSWF in H0. clarify.
            - unfold in_L in *. clarify. }
          { refl. }
          { unfold msg_src. ii. clarify. }
        * guardH o. dup MEM. specialize (MEM1 loc0 ts). inv MEM1.
          { econs. ii. eapply NPROM0. des; auto. }
          { econs; eauto. ii. eapply NPROM0. des; auto. }
          { econs 3; eauto. des; auto. }
      + ii. erewrite Memory.lower_o in GET1; eauto. des_ifs; eauto.
        ss. eapply Memory.lower_get0 in LOWERMEMSRC. des. clarify. eauto.
      + ss. erewrite PROMISEDDECREASE. ii. des.
        erewrite Memory.lower_o in GET1; eauto. des_ifs.
        * ss. des; clarify.
        * guardH o. exploit PROMATTACH; eauto.
      + eauto.
      + econs; eauto.
        * eapply TViewFacts.write_tview_mon; eauto. refl.
        * ii. ss. dup PROMS. specialize (PROMS0 loc0 ts).
          erewrite SPEC. erewrite (@Memory.remove_o promises2); eauto.
          erewrite (@Memory.lower_o promises0); eauto.
          destruct (loc_ts_eq_dec (loc0, ts) (loc, to)); ss. guardH o.
          setoid_rewrite LocFun.add_spec.
          destruct (LocSet.Facts.eq_dec loc0 loc); eauto. clarify.
          inv PROMS0; econs; eauto. i. clarify. des_ifs.
          { symmetry in H3. exploit RELEASE; try apply H3; eauto.
            { destruct ord; ss. } ss. i. clarify. inv MSG0. }
          { eapply join_view_add_weak_closed; eauto.
            eapply add_weak_closed_view_consistent.
            - eapply add_closed_add_weak_closed_view.
              eapply singleton_view_add_closed; eauto.
              exploit ONLY.
              + symmetry. eapply H1.
              + i. des. auto.
            - apply View.singleton_ur_wf.
            - ss. unfold TimeMap.singleton.
              setoid_rewrite LocFun.add_spec_eq.
              exploit CONSISTENTTGT.
              { instantiate (4:=ts).
                erewrite Memory.remove_o; eauto. erewrite Memory.lower_o; eauto.
                des_ifs.
                - exfalso. ss. unguard. des; clarify.
                - eauto. }
              ss. }
      + econs.
        * ii. erewrite Memory.lower_o in GET1; eauto. des_ifs; eauto.
          ss. des; clarify. exploit COMPLETE; eauto. i. des.
          exploit ONLY; eauto. i. des. clarify.
          destruct released_src as [released_src|].
          { esplits; eauto. eapply write_released_add_closed_relaxed.
            - auto.
            - eauto.
            - instantiate (1:=from0). destruct releasedm_src as [releasedm_src|].
              + exploit RELEASEDMSOME; eauto. i. des.
                exploit ONLY; eauto. i. des.
                eapply add_closed_opt_view_future_add_closed; eauto.
              + econs.
            - left. auto.
            - destruct (Ordering.le Ordering.strong_relaxed ord) eqn:ORD; ss.
              exfalso. exploit RELEASE; eauto. ss. i. clarify.
              clear - ORD RELEASED. destruct ord; ss; inv RELEASED.
          }
          { unfold TView.write_released in RELEASEDLE.
            destruct (Ordering.le Ordering.relaxed ord) eqn:ORD.
            - inv RELEASEDLE.
            - destruct ord; ss. esplits; eauto. }
        * i. exploit ONLY; eauto. i. des. splits; auto.
          { eapply concrete_promised_increase_promise; eauto. }
          { etrans; eauto. eapply Memory.future_future_weak. econs; eauto. }
      + refl.

    - clarify.
  Qed.

  Lemma sim_thread_step others pasts lang st lc_src lc_tgt sc_src sc_tgt mem_src mem_tgt pf e_tgt
        st' lc_tgt' sc_tgt' mem_tgt'
        (STEPTGT: @Thread.step lang pf e_tgt (Thread.mk _ st lc_tgt sc_tgt mem_tgt) (Thread.mk _ st' lc_tgt' sc_tgt' mem_tgt'))
        (NOREAD: no_read_msgs (others \2/ (in_L /2\ promised lc_src.(Local.promises))) e_tgt)
        (SC: TimeMap.le sc_src sc_tgt)
        (MEM: sim_memory (others \2/ (in_L /2\ promised lc_src.(Local.promises))) mem_src mem_tgt)
        (SCSRC: Memory.closed_timemap sc_src mem_src)
        (SCTGT: Memory.closed_timemap sc_tgt mem_tgt)
        (MEMSRC: Memory.closed mem_src)
        (MEMTGT: Memory.closed mem_tgt)
        (LOCALSRC: Local.wf lc_src mem_src)
        (LOCALTGT: Local.wf lc_tgt mem_tgt)
        (SIM: sim_local others pasts lc_src lc_tgt)
        (PAST: wf_pasts_memory mem_src pasts)
        (PROMATTACH: promises_not_attached (promised lc_src.(Local.promises)) mem_src)
        (OTHERSWF: forall loc' to', others loc' to' -> L loc')
        (CONSISTENT: Local.promise_consistent lc_tgt')
    :
      exists tr pasts' lc_src' sc_src' mem_src',
        (<<STEPSRC: Trace.steps tr (Thread.mk _ st lc_src sc_src mem_src) (Thread.mk _ st' lc_src' sc_src' mem_src')>>) /\
        (<<MEM: sim_memory (others \2/ (in_L /2\ promised lc_src'.(Local.promises))) mem_src' mem_tgt'>>) /\
        (<<ATTACHEDLE: not_attached_le others mem_src mem_src'>>) /\
        (<<PROMATTACH: promises_not_attached (promised lc_src'.(Local.promises)) mem_src'>>) /\
        (<<SC: TimeMap.le sc_src' sc_tgt'>>) /\
        (<<SIM: sim_local others pasts' lc_src' lc_tgt'>>) /\
        (<<PAST: wf_pasts_memory mem_src' pasts'>>) /\
        (<<PASTLE: pasts_le pasts pasts'>>)
  (* TODO: condition about event *)
  .
  Proof.
    inv STEPTGT.
    - inv STEP. destruct (classic (L loc)).
      + admit.
      + inv LOCAL. inv SIM. inv LOCALSRC. inv LOCALTGT.
        exploit sim_promise_step_normal; try apply MEM; eauto.
        { inv TVIEW_WF. eauto. }
        { i. clarify. transitivity (View.rlx (TView.cur (Local.tview lc_tgt)) loc).
          - transitivity (View.rlx (TView.rel (Local.tview lc_tgt) loc) loc).
            + inv TVIEW. specialize (REL loc). inv REL. auto.
            + inv TVIEW_WF0. specialize (REL_CUR loc). inv REL_CUR. auto.
          - exploit CONSISTENT; ss; eauto.
            + eapply Memory.promise_get0 in PROMISE.
              * des. eauto.
              * inv PROMISE; clarify.
            + i. left. auto. }
        { inv TVIEW_CLOSED. eauto. }
        i. des.
        replace (fun x0 x1 => others x0 x1 \/ in_L x0 x1 /\ promised lc_src.(Local.promises) x0 x1) with
            (fun x0 x1 => others x0 x1 \/ in_L x0 x1 /\ promised prom_src' x0 x1) in MEM0; cycle 1.
        { extensionality loc'. extensionality to'.
          apply Coq.Logic.PropExtensionality.propositional_extensionality. split; i.
          { des; eauto. right. split; auto.
            inv H1. destruct msg0.
            eapply MemoryFacts.promise_get_promises_inv_diff in GET; eauto.
            - des. econs; eauto.
            - ii. inv H1. unfold in_L in *. ss. }
          { des; auto. right. split; auto. inv H1. destruct msg0. inv STEPSRC.
            - eapply Memory.add_get1 in GET; eauto. econs; eauto.
            - eapply Memory.split_get1 in GET; eauto. des. econs; eauto.
            - eapply Memory.lower_get1 in GET; eauto. des. econs; eauto.
            - eapply Memory.remove_get1 in GET; eauto. des.
              + subst. ss.
              + econs; eauto. }
        }
        eexists [(_, ThreadEvent.promise loc from to msg_src kind_src)], pasts', (Local.mk _ _), _, mem_src'.
        splits; ss.
        * econs 2; [|econs 1|ss]. econs 1. econs; eauto.
        * ss.

    - inv STEP. inv LOCAL.
      + eexists [(_, ThreadEvent.silent)], pasts, lc_src, sc_src, mem_src. splits; ss.
        * econs 2; [|econs 1|ss]. econs 2. econs; eauto.
        * refl.
      + exploit sim_read_step; eauto. i. des.
        eexists [(_, ThreadEvent.read loc ts val released_src ord)],
        pasts, lc_src', sc_src, mem_src. splits; ss.
        * econs 2; [|econs 1|ss]. econs 2. econs; eauto.
        * inv STEPSRC. ss.
        * refl.
        * inv STEPSRC. ss.
      + destruct (classic (L loc)).
        * admit.
        * hexploit sim_write_step_normal; try eassumption.
          { eapply MEM. }
          { i. instantiate (1:=None). econs. }
          { i. clarify. }
          { econs. }
          { econs. }
          { econs. }
          { econs. } i. des.
          eexists [(_, ThreadEvent.write loc from to val _ ord)], pasts', lc_src', _, mem_src'.
          splits; ss.
          econs 2; [|econs 1|ss]. econs 2. econs; eauto.
      + destruct (classic (L loc)).
        * admit.
        * exploit sim_read_step; eauto. i. des.
          dup PAST. inv PAST0. exploit COMPLETE; eauto. i. des.
          exploit Local.read_step_future; try apply LOCAL1; eauto. i. des.
          exploit Local.read_step_future; try apply STEPSRC; eauto. i. des.
          hexploit sim_write_step_normal; try eassumption.
          { inv STEPSRC. ss. }
          { inv STEPSRC. ss. }
          { i. clarify. }
          { i. eauto. } i. des.
          eexists [(_, ThreadEvent.update loc tsr tsw valr valw released_src released_src0 ordr ordw)],
          pasts', lc_src'0, sc_src', mem_src'. splits; ss.
          { econs 2; [|econs 1|ss]. econs 2. econs; eauto. }
      + exploit sim_fence_step; eauto. i. des.
        eexists [(_, ThreadEvent.fence ordr ordw)],
        pasts, lc_src', sc_src', mem_src. splits; ss.
        * econs 2; [|econs 1|ss]. econs 2. econs; eauto.
        * inv STEPSRC. ss.
        * refl.
        * inv STEPSRC. ss.
      + exploit sim_fence_step; eauto. i. des.
        eexists [(_, ThreadEvent.syscall e)],
        pasts, lc_src', sc_src', mem_src. splits; ss.
        * econs 2; [|econs 1|ss]. econs 2. econs; eauto.
        * inv STEPSRC. ss.
        * refl.
        * inv STEPSRC. ss.
      + exploit sim_failure_step; eauto. i. des.
        eexists [(_, ThreadEvent.failure)],
        pasts, lc_src, sc_src, mem_src. splits; ss.
        * econs 2; [|econs 1|ss]. econs 2. econs; eauto.
        * refl.
  Admitted.

  Inductive sim_promise_content_weak (loc: Loc.t) (ts: Time.t)
            (LOC: bool) (others: Time.t -> Prop)
            (rel_src: View.t)
    :
      option Memory.t -> option (Time.t * Message.t) -> option (Time.t * Message.t) -> Prop :=
  | sim_promise_content_weak_none
      past
    :
      sim_promise_content_weak loc ts LOC others rel_src past None None
  | sim_promise_content_weak_normal_concrete
      (NPROM: ~ LOC)
      past from val released_src released_tgt
      (MSG: sim_opt_view past loc ts released_src released_tgt)
      (RELVIEW: forall released (MSG: released_src = Some released),
          add_weak_closed_view rel_src past loc ts)
    :
      sim_promise_content_weak loc ts LOC others rel_src
                               (Some past)
                               (Some (from, Message.concrete val released_src))
                               (Some (from, Message.concrete val released_tgt))
  | sim_promise_content_weak_normal_reserve
      (NPROM: ~ LOC)
      past from
    :
      sim_promise_content_weak loc ts LOC others rel_src
                               past
                               (Some (from, Message.reserve))
                               (Some (from, Message.reserve))
  | sim_promise_content_weak_forget
      (PROM: LOC)
      past from_src from_tgt msg
      (OTHERS: forall (OTHER: others from_tgt), Time.lt from_tgt from_src)
      (NOTHERS: forall (NOTHER: ~ others from_tgt), Time.le from_tgt from_src)
    :
      sim_promise_content_weak loc ts LOC others rel_src
                               past
                               (Some (from_src, Message.reserve))
                               (Some (from_tgt, msg))
  .
  Hint Constructors sim_promise_content_weak.

  Lemma sim_promise_content_sim_promise_content_weak
    :
      sim_promise_content <8= sim_promise_content_weak
  .
  Proof.
    ii. inv PR; econs; eauto.
    ii. right. apply NOTHERS; auto.
  Qed.

  Definition sim_promise_weak (others: Loc.t -> Time.t -> Prop)
             (rel_src: LocFun.t View.t)
             (pasts: Loc.t -> Time.t -> option Memory.t)
             (prom_src prom_tgt: Memory.t): Prop :=
    forall loc ts,
      sim_promise_content_weak loc ts (L loc) (others loc) (rel_src loc) (pasts loc ts)
                               (Memory.get loc ts prom_src)
                               (Memory.get loc ts prom_tgt).

  Lemma sim_promise_sim_promise_weak
    :
      sim_promise <5= sim_promise_weak
  .
  Proof.
    ii. eapply sim_promise_content_sim_promise_content_weak; eauto.
  Qed.

  Definition sim_promise_weak_list (others: Loc.t -> Time.t -> Prop)
             (rel_src: LocFun.t View.t)
             (pasts: Loc.t -> Time.t -> option Memory.t)
             (prom_src prom_tgt: Memory.t)
             (l: list (Loc.t * Time.t)): Prop :=
    forall loc ts,
      (<<NORMAL: sim_promise_content loc ts (L loc) (others loc) (rel_src loc) (pasts loc ts)
                                     (Memory.get loc ts prom_src)
                                     (Memory.get loc ts prom_tgt)>>) \/
      ((<<LIN: List.In (loc, ts) l>>) /\
       (<<WEAK: sim_promise_content_weak loc ts (L loc) (others loc) (rel_src loc) (pasts loc ts)
                                         (Memory.get loc ts prom_src)
                                         (Memory.get loc ts prom_tgt)>>)).

  Lemma sim_promise_weak_list_empty others rel_src pasts prom_src prom_tgt
        (SIM: sim_promise_weak_list others rel_src pasts prom_src prom_tgt [])
    :
      sim_promise others rel_src pasts prom_src prom_tgt.
  Proof.
    ii. exploit SIM; eauto. i. des; eauto. ss.
  Qed.

  Lemma sim_promise_weak_list_exists others rel_src pasts prom_src prom_tgt
        (SIM: sim_promise_weak others rel_src pasts prom_src prom_tgt)
        (FIN: Memory.finite prom_src)
    :
      exists l,
        (<<SIM: sim_promise_weak_list others rel_src pasts prom_src prom_tgt l>>).
  Proof.
    unfold Memory.finite in *. des.
    hexploit (@list_filter_exists
                (Loc.t * Time.t)
                (fun locts =>
                   let (loc, ts) := locts in
                   ~ sim_promise_content loc ts (L loc) (others loc) (rel_src loc) (pasts loc ts)
                     (Memory.get loc ts prom_src)
                     (Memory.get loc ts prom_tgt))
                dom).
    i. des. exists l'.
    ii. destruct (classic (List.In (loc,ts) l')).
    - right. splits; auto.
    - left. specialize (SIM loc ts). red. inv SIM; try by (econs; eauto).
      apply NNPP. ii. exploit FIN; eauto. i.
      hexploit (proj1 (@COMPLETE (loc, ts))); auto.
      splits; auto. ii. rewrite H2 in *. rewrite H3 in *. auto.
  Qed.

  Inductive chained_messages:
    forall (mem: Memory.t) (loc: Loc.t) (ts: Time.t) (l: list (Time.t * Message.t)), Prop :=
  | chained_messages_nil
      mem loc ts
      (EMPTY: forall to msg (GET: Memory.get loc to mem = Some (ts, msg)), False)
    :
      chained_messages mem loc ts []
  | chained_messages_cons
      mem loc ts tl to msg
      (CHAIN: chained_messages mem loc to tl)
      (GET: Memory.get loc to mem = Some (ts, msg))
    :
      chained_messages mem loc ts ((to, msg)::tl)
  .

  Lemma chained_messages_exsists mem loc ts
        (NBOT: Time.lt Time.bot ts)
    :
      exists l, <<CHAIN: chained_messages mem loc ts l>>.
  Proof.
    revert ts NBOT.
    assert (LEMMA: forall
               dom
               (SORTED: times_sorted dom)
               ts
               (NBOT: Time.lt Time.bot ts)
               (COMPLETE: forall
                   to from msg
                   (GET: Memory.get loc to mem = Some (from, msg))
                   (TS: Time.lt ts to), List.In to dom),
               exists l, <<CHAIN: chained_messages mem loc ts l>>).
    { intros dom SORTED. induction SORTED.
      - i. exists []. econs. i. exploit COMPLETE; eauto.
        eapply memory_get_ts_strong in GET.
        des; auto. clarify.
      - i. destruct (Time.le_lt_dec hd ts).
        + exploit IHSORTED; eauto. i. exploit COMPLETE; eauto.
          i. ss. des; auto. clarify.
          exfalso. eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt; eauto.
        + destruct (Memory.get loc hd mem) as [[from msg]|] eqn:GET.
          * destruct (Time.eq_dec ts from).
            { clarify. hexploit (IHSORTED hd); eauto.
              { i. exploit COMPLETE; eauto.
                i. ss. des; auto. clarify.
                exfalso. eapply Time.lt_strorder; eauto. }
              { i. des. exists ((hd, msg)::l0). econs; eauto. }
            }
            { exists []. econs. i.
              exploit COMPLETE; eauto.
              { dup GET0. eapply memory_get_ts_strong in GET1. des; clarify. }
              i. ss. des; clarify.
              eapply List.Forall_forall in x; eauto.
              exploit Memory.get_disjoint.
              - eapply GET.
              - eapply GET0.
              - i. des; clarify. eapply x1.
                + instantiate (1:=hd). econs; ss; [|refl].
                  eapply memory_get_ts_strong in GET. des; auto.
                  clarify. transitivity ts; eauto.
                + econs; ss. left. auto.
            }
          * exploit IHSORTED; eauto. i. exploit COMPLETE; eauto.
            i. ss. des; auto. clarify.
    }
    i.
    hexploit (@cell_finite_sound_exists (mem loc)). i. des.
    hexploit (@sorting_sorted dom). i. des.
    exploit LEMMA; eauto. i.
    eapply COMPLETE0. eapply COMPLETE. esplits; eauto.
  Qed.

  Lemma reserve_future_memory_trans prom0 mem0 prom1 mem1 prom2 mem2
        (FUTURE01: reserve_future_memory prom0 mem0 prom1 mem1)
        (FUTURE12: reserve_future_memory prom1 mem1 prom2 mem2)
    :
      reserve_future_memory prom0 mem0 prom2 mem2.
  Proof.
    ginduction FUTURE01; i; eauto.
  Qed.

  Lemma promises_not_attached_replaces loc ts prom0 mem0
        (LIN: L loc)
        (ATTACHED0: promises_not_attached (promised prom0) mem0)
        (LOC: forall from to msg (GET: Memory.get loc to prom0 = Some (from, msg)),
            msg = Message.reserve)
        (MLE0: Memory.le prom0 mem0)
        (NBOT: Time.lt Time.bot ts)
        (PROMISED: promised prom0 loc ts)
    :
      exists prom1 mem1,
        (<<FUTURE01: reserve_future_memory prom0 mem0 prom1 mem1>>) /\
        (<<UNCH01: forall loc' to (TS: loc' = loc -> Time.le to ts),
            (<<MEM: Memory.get loc' to mem1 = Memory.get loc' to mem0>>) /\
            (<<PROM: Memory.get loc' to prom1 = Memory.get loc' to prom0>>)>>) /\
        (<<ATTACH: forall to msg (GET: Memory.get loc to mem1 = Some (ts, msg)), False>>) /\
        (<<MLE1: Memory.le prom1 mem1>>) /\

        (<<RESTORE:
           forall prom2 mem2
                  (UNCH12: forall loc' to (TS: loc' = loc -> Time.lt ts to),
                      (<<MEM: Memory.get loc' to mem2 = Memory.get loc' to mem1>>) /\
                      (<<PROM: Memory.get loc' to prom2 = Memory.get loc' to prom1>>))
                  (MLE2: Memory.le prom2 mem2)
           ,
           exists prom3 mem3,
             (<<FUTURE23: reserve_future_memory prom2 mem2 prom3 mem3>>) /\
             (<<UNCHANGED: forall loc' to (TS: loc' = loc -> Time.lt ts to),
                 (<<MEM: Memory.get loc' to mem3 = Memory.get loc' to mem0>>) /\
                 (<<PROM: Memory.get loc' to prom3 = Memory.get loc' to prom0>>)>>) /\
             (<<CHANGED: forall to (TS: Time.le to ts),
                 (<<MEM: Memory.get loc to mem3 = Memory.get loc to mem2>>) /\
                 (<<PROM: Memory.get loc to prom3 = Memory.get loc to prom2>>)>>) /\
             (<<MLE3: Memory.le prom3 mem3>>)
               >>).
  Proof.
    hexploit (@chained_messages_exsists prom0 loc ts); auto. i. des.
    ginduction l; i.
    { exists prom0, mem0. splits; eauto.
      - i. exploit ATTACHED0; eauto. i.
        inv x. dup GET0. destruct msg0. eapply MLE0 in GET0. clarify.
        inv CHAIN. eapply EMPTY. eauto.
      - i. exists prom2, mem2. splits; auto. }
    inv CHAIN. hexploit LOC; eauto. i. clarify.

    assert (TSTO: Time.lt ts to).
    { eapply memory_get_ts_strong in GET. des; auto. clarify. }

    hexploit (IHl loc to prom0 mem0); eauto.
    i. des.

    assert (GETPROM1: Memory.get loc to prom1 = Some (ts, Message.reserve)).
    { hexploit (@UNCH01 loc to).
      - i. refl.
      - i. des. erewrite PROM. eapply GET. }
    exploit Memory.remove_exists.
    { eapply GETPROM1. }
    intros [prom1' REMOVEPROM].
    exploit Memory.remove_exists_le; eauto.
    intros [mem1' REMOVEMEM].

    assert (REMOVE: Memory.promise prom1 mem1 loc ts to Message.reserve prom1' mem1' Memory.op_kind_cancel).
    { econs; eauto. }

    exists prom1', mem1'. splits; auto.
    { eapply reserve_future_memory_trans; eauto. }
    { i. hexploit (@UNCH01 loc' to0).
      { i. etrans; eauto. left. auto. }
      i. des.
      erewrite (@Memory.remove_o mem1'); eauto.
      erewrite (@Memory.remove_o prom1'); eauto. des_ifs.
      ss. des; clarify.
      exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt; eauto.
    }
    { i. erewrite Memory.remove_o in GET0; eauto. des_ifs. ss. des; clarify.
      hexploit (@UNCH01 loc to0).
      { i. exploit memory_get_from_inj.
        - eapply MLE1. eapply GETPROM1.
        - eapply GET0.
        - i. des; clarify.
          + exfalso. eapply Time.lt_strorder; eauto.
          + exfalso. eapply Time.lt_strorder; eauto. } i. des.
      erewrite MEM in GET0. eapply MLE0 in GET.
      exploit memory_get_from_inj.
      { eapply GET. }
      { eapply GET0. }
      i. des; clarify.
      { eapply Time.lt_strorder; eauto. }
      { eapply Time.lt_strorder; eauto. }
    }
    { eapply promise_memory_le; eauto. }
    { i. hexploit (@Memory.add_exists mem2 loc ts to Message.reserve).
      { ii. hexploit (@UNCH12 loc to2).
        { i. inv LHS. inv RHS. ss. eapply TimeFacts.lt_le_lt; eauto. }
        i. des. rewrite H in *.
        erewrite (@Memory.remove_o mem1') in GET2; eauto. des_ifs. guardH o.
        exploit Memory.get_disjoint.
        { eapply GET2. }
        { eapply MLE1. eapply GETPROM1. }
        i. des; clarify.
        - ss. unguard. des; clarify.
        - eapply x1; eauto.
      }
      { auto. }
      { econs. }
      intros [mem2' ADDMEM].
      hexploit (Memory.add_exists_le); eauto.
      intros [prom2' ADDPROM].

      assert (ADD: Memory.promise prom2 mem2 loc ts to Message.reserve prom2' mem2' Memory.op_kind_add).
      { econs; eauto. i. clarify. }

      hexploit (RESTORE prom2' mem2').
      { i. erewrite (@Memory.add_o mem2'); eauto.
        erewrite (@Memory.add_o prom2'); eauto.
        hexploit (UNCH12 loc' to0); eauto.
        erewrite (@Memory.remove_o mem1'); eauto.
        erewrite (@Memory.remove_o prom1'); eauto. des_ifs.
        ss. des; clarify. exfalso. eapply Time.lt_strorder; eauto. }
      { eapply promise_memory_le; eauto. }
      i. des.
      exists prom3, mem3. splits; auto.
      { eapply reserve_future_memory_trans; eauto. }

      { i. destruct (classic (loc' = loc -> Time.lt to to0)).
        - exploit UNCHANGED; eauto.
        - apply imply_to_and in H. des. clarify.
          hexploit (CHANGED to0).
          { destruct (Time.le_lt_dec to0 to); auto. exfalso. auto. }
          i. des. rewrite MEM. rewrite PROM.
          erewrite (@Memory.add_o mem2'); eauto.
          erewrite (@Memory.add_o prom2'); eauto. des_ifs.
          + ss. des; clarify. split; auto. symmetry. auto.
          + guardH o. exploit UNCH12; eauto. i. des.
            erewrite x. erewrite x0.
            hexploit (UNCH01 loc to0); eauto.
            { i. destruct (Time.le_lt_dec to0 to); auto. exfalso. auto. }
            i. des. rewrite <- MEM0. rewrite <- PROM0.
            erewrite (@Memory.remove_o mem1'); eauto.
            erewrite (@Memory.remove_o prom1'); eauto. des_ifs.
            ss. unguard. des; clarify.
      }
      { i. hexploit (@CHANGED to0); eauto.
        { etrans; eauto. left. auto. }
        i. des. rewrite MEM. rewrite PROM.
        erewrite (@Memory.add_o mem2'); eauto.
        erewrite (@Memory.add_o prom2'); eauto. des_ifs.
        ss. des; clarify.
        exfalso. eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt; eauto.
      }
    }
  Qed.

  Lemma promises_not_attached_replace_add loc from from' to prom0 mem0
        (LIN: L loc)
        (ATTACHED0: promises_not_attached (promised prom0) mem0)
        (LOC: forall from to msg (GET: Memory.get loc to prom0 = Some (from, msg)),
            msg = Message.reserve)
        (MLE0: Memory.le prom0 mem0)
        (NBOT: Time.lt Time.bot to)
        (GET: Memory.get loc to prom0 = Some (from, Message.reserve))
        (FROM: Time.lt from' to)
        (EMPTY: forall ts (ITV: Interval.mem (from', from) ts), ~ covered loc ts mem0)
    :
      exists prom1 mem1,
        (<<FUTURE01: reserve_future_memory prom0 mem0 prom1 mem1>>) /\
        (<<MEMSPEC: forall loc' ts',
            Memory.get loc' ts' mem1 =
            if loc_ts_eq_dec (loc', ts') (loc, to)
            then Some (from', Message.reserve)
            else Memory.get loc' ts' mem0>>) /\
        (<<PROMSPEC: forall loc' ts',
            Memory.get loc' ts' prom1 =
            if loc_ts_eq_dec (loc', ts') (loc, to)
            then Some (from', Message.reserve)
            else Memory.get loc' ts' prom0>>).
  Proof.
    hexploit promises_not_attached_replaces; eauto.
    { econs; eauto. }
    i. des.
    hexploit (@Memory.remove_exists prom1 loc from to Message.reserve).
    { hexploit (@UNCH01 loc to); eauto.
      { i. refl. }
      i. des. erewrite PROM. eauto. }
    intros [prom2 REMOVEPROM].
    hexploit Memory.remove_exists_le; eauto.
    intros [mem2 REMOVEMEM].
    assert (PROMISE0: Memory.promise prom1 mem1 loc from to Message.reserve prom2 mem2 Memory.op_kind_cancel).
    { econs; eauto. }
    hexploit (@Memory.add_exists mem2 loc from' to Message.reserve); eauto.

    { ii. erewrite Memory.remove_o in GET2; eauto. des_ifs. guardH o.
      hexploit (@Memory.get_disjoint loc from2 from to2 to).
      { eapply GET2. }
      { hexploit (@UNCH01 loc to).
        { i. refl. }
        i. des. rewrite MEM. eauto. }
      i. ss. unguard. des; clarify.
      eapply H; eauto. inv LHS. econs; ss.
      destruct (Time.le_lt_dec x from); auto. exfalso.
      hexploit memory_get_to_mon.
      { eapply GET2. }
      { hexploit (@UNCH01 loc to).
        { i. refl. }
        i. des. rewrite MEM. eauto. }
      { inv RHS. ss. eapply TimeFacts.lt_le_lt; eauto. }
      i. hexploit (@UNCH01 loc to2).
      { i. left. auto. }
      i. des. erewrite MEM in *. eapply (EMPTY x).
      { econs; ss. }
      { econs; eauto. }
    }
    { econs. }
    intros [mem2' ADDMEM].
    hexploit (@Memory.add_exists_le prom2 mem2 loc from' to Message.reserve); eauto.
    { eapply promise_memory_le; eauto. }
    intros [prom2' ADDPROM].
    assert (PROMISE1: Memory.promise prom2 mem2 loc from' to Message.reserve prom2' mem2' Memory.op_kind_add).
    { econs; eauto. i. clarify. }
    hexploit (@RESTORE prom2' mem2'); eauto.
    { i. erewrite (@Memory.add_o mem2'); eauto.
      erewrite (@Memory.add_o prom2'); eauto.
      erewrite (@Memory.remove_o mem2); eauto.
      erewrite (@Memory.remove_o prom2); eauto. des_ifs.
      ss. des; clarify. exfalso. eapply Time.lt_strorder; eauto. }
    { eapply promise_memory_le; cycle 1; eauto.
      eapply promise_memory_le; cycle 1; eauto. }
    i. des. exists prom3, mem3. splits; auto.
    { eapply reserve_future_memory_trans; eauto. }
    { i. destruct (classic (loc' = loc -> Time.lt to ts')).
      - hexploit UNCHANGED; eauto. i. des. rewrite MEM. des_ifs.
        ss. des; clarify. exfalso. eapply Time.lt_strorder; eauto.
      - apply imply_to_and in H. des. clarify.
        hexploit (@CHANGED ts'); eauto.
        { destruct (Time.le_lt_dec ts' to); eauto. exfalso. auto. }
        i. des. rewrite MEM.
        erewrite (@Memory.add_o mem2' mem2); eauto.
        erewrite (@Memory.remove_o mem2 mem1); eauto.
        des_ifs. guardH o. hexploit (@UNCH01 loc ts'); eauto.
        { i. destruct (Time.le_lt_dec ts' to); eauto. exfalso. auto. }
        i. des; clarify.
    }
    { i. destruct (classic (loc' = loc -> Time.lt to ts')).
      - hexploit UNCHANGED; eauto. i. des. rewrite PROM. des_ifs.
        ss. des; clarify. exfalso. eapply Time.lt_strorder; eauto.
      - apply imply_to_and in H. des. clarify.
        hexploit (@CHANGED ts'); eauto.
        { destruct (Time.le_lt_dec ts' to); eauto. exfalso. auto. }
        i. des. rewrite PROM.
        erewrite (@Memory.add_o prom2' prom2); eauto.
        erewrite (@Memory.remove_o prom2 prom1); eauto.
        des_ifs. guardH o. hexploit (@UNCH01 loc ts'); eauto.
        { i. destruct (Time.le_lt_dec ts' to); eauto. exfalso. auto. }
        i. des; clarify.
    }
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

  Lemma sim_promise_weak_stengthen others pasts prom_src prom_tgt mem_src mem_tgt rel_src
        (MEM: sim_memory (others \2/ (in_L /2\ promised prom_src)) mem_src mem_tgt)
        (MLETGT: Memory.le prom_tgt mem_tgt)
        (MLESRC: Memory.le prom_src mem_src)
        (FIN: Memory.finite prom_src)
        (BOTNONE: Memory.bot_none prom_src)
        (PROM: sim_promise_weak others rel_src pasts prom_src prom_tgt)
        (PROMATTACH: promises_not_attached (promised prom_src) mem_src)
    :
      exists prom_src' mem_src',
        (<<FUTURE: reserve_future_memory prom_src mem_src prom_src' mem_src'>>) /\
        (<<MEM: sim_memory (others \2/ (in_L /2\ promised prom_src')) mem_src' mem_tgt>>) /\
        (<<ATTACHEDLE: not_attached_le others mem_src mem_src'>>) /\
        (<<PROMATTACH: promises_not_attached (promised prom_src') mem_src'>>) /\
        (<<PROM: sim_promise others rel_src pasts prom_src' prom_tgt>>).
  Proof.
    exploit sim_promise_weak_list_exists; eauto. i. des.
    clear PROM. ginduction l.
    { i. exists prom_src, mem_src. splits; auto.
      - refl.
      - eapply sim_promise_weak_list_empty; eauto. }
    i. destruct a as [loc ts].
    dup SIM. specialize (SIM0 loc ts). des.
    { exploit IHl; eauto. ii.
      destruct (loc_ts_eq_dec (loc0, ts0) (loc, ts)).
      - ss. des; clarify. left. auto.
      - specialize (SIM loc0 ts0). ss. des; auto; clarify. }

    clear LIN. inv WEAK.
    { exploit IHl; eauto. ii.
      specialize (SIM loc0 ts0). ss. des; auto; clarify.
      left. rewrite <- H1. rewrite <- H2. econs. }
    { exploit IHl; eauto. ii.
      specialize (SIM loc0 ts0). ss. des; auto; clarify.
      left. rewrite <- H. rewrite <- H2. rewrite <- H0. econs; eauto. }
    { exploit IHl; eauto. ii.
      specialize (SIM loc0 ts0). ss. des; auto; clarify.
      left. rewrite <- H1. rewrite <- H2. econs; eauto. }
    destruct (classic (others loc from_tgt)) as [OTHER|NOTHER].
    { exploit IHl; eauto. ii.
      specialize (SIM loc0 ts0). ss. des; auto; clarify.
      left. rewrite <- H1. rewrite <- H2. econs; eauto. i. clarify. }

    symmetry in H1. rename H1 into GETSRC.
    symmetry in H2. rename H2 into GETTGT.
    assert (NBOT: Time.lt Time.bot ts).
    { destruct (Time.le_lt_dec ts Time.bot); auto. destruct l0.
      - exfalso. eapply Time.lt_strorder.
        eapply TimeFacts.lt_le_lt; eauto. eapply Time.bot_spec.
      - inv H. erewrite BOTNONE in GETSRC. clarify. }

    exploit promises_not_attached_replace_add.
    { eauto. }
    { eauto. }
    { ii. specialize (SIM loc to). rewrite GET in SIM. des.
      - inv NORMAL; clarify.
      - inv WEAK; clarify. }
    { eauto. }
    { eapply NBOT. }
    { eauto. }
    { instantiate (1:=from_tgt).
      eapply memory_get_ts_strong in GETTGT. des; clarify. }
    { ii. inv H. specialize (MEM loc to). rewrite GET in MEM.
      inv MEM; clarify.
      - exploit Memory.get_disjoint.
        { symmetry. apply H. }
        { eapply MLETGT. eapply GETTGT. }
        i. des; clarify.
        + eapply MLESRC in GETSRC. clarify.
          inv ITV. inv ITV0. ss. clear - TO FROM1.
          eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt; eauto.
        + eapply x0.
          * instantiate (1:=ts0). econs; ss.
            { inv ITV0. eapply TimeFacts.le_lt_lt; eauto. }
            { inv ITV0. ss. }
          * inv ITV. econs; ss. etrans; eauto.
            eapply memory_get_ts_le; eauto.
      - guardH PROM0. exploit Memory.get_disjoint.
        { symmetry. apply H. }
        { eapply MLETGT. eapply GETTGT. }
        i. des; clarify.
        + eapply MLESRC in GETSRC. clarify.
          inv ITV. inv ITV0. ss. clear - TO FROM1.
          eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt; eauto.
        + eapply x0.
          * instantiate (1:=ts0). econs; ss.
            { inv ITV0. eapply TimeFacts.le_lt_lt; eauto. }
            { inv ITV0. ss. }
          * inv ITV. econs; ss. etrans; eauto.
            eapply memory_get_ts_le; eauto.
    }
    i. des.
    assert (PROMISEDSAME: promised prom1 = promised prom_src).
    { extensionality loc'. extensionality ts'.
      apply Coq.Logic.PropExtensionality.propositional_extensionality.
      split; i.
      - inv H. erewrite PROMSPEC in GET. des_ifs.
        + ss. des; clarify. econs; eauto.
        + econs; eauto.
      - inv H. specialize (PROMSPEC loc' ts'). des_ifs.
        + ss. des; clarify. econs; eauto.
        + erewrite <- PROMSPEC in *. econs; eauto. }

    hexploit (@IHl others pasts prom1 prom_tgt mem1 mem_tgt rel_src); eauto.
    { rewrite PROMISEDSAME.
      ii. specialize (MEM loc0 ts0). erewrite MEMSPEC. des_ifs.
      ss. des; clarify. apply MLETGT in GETTGT. rewrite GETTGT. econs 3; eauto.
      - right. split; auto. econs; eauto.
      - refl. }
    { eapply reserve_future_memory_le; eauto. }
    { eapply reserve_future_memory_finite; eauto. }
    { eapply reserve_future_memory_bot_none; eauto. }
    { rewrite PROMISEDSAME. ii. rewrite MEMSPEC in GET. des_ifs.
      - ss. des; clarify. econs; eauto.
      - exploit PROMATTACH; eauto. }
    { ii. erewrite PROMSPEC. des_ifs.
      - left. ss. des. clarify. erewrite GETTGT. econs 4; eauto.
        i. clarify.
      - guardH o. specialize (SIM loc0 ts0).
        ss. unguard. des; clarify; auto. }
    i. des. exists prom_src', mem_src'. splits; auto.
    - eapply reserve_future_memory_trans; eauto.
    - etrans; eauto. ii.
      erewrite MEMSPEC in GET. des_ifs.
      + ss. des; clarify.
      + eauto.
  Qed.



  Definition aaa := 1 = true.

  Lemma sim_thread_step others pasts lang st lc_src lc_tgt sc_src sc_tgt mem_src mem_tgt pf e_tgt
        st' lc_tgt' sc_tgt' mem_tgt'
        (STEPTGT: @Thread.step lang pf e_tgt (Thread.mk _ st lc_tgt sc_tgt mem_tgt) (Thread.mk _ st' lc_tgt' sc_tgt' mem_tgt'))
        (NOREAD: no_read_msgs (others \2/ (in_L /2\ promised lc_src.(Local.promises))) e_tgt)
        (SC: TimeMap.le sc_src sc_tgt)
        (MEM: sim_memory (others \2/ (in_L /2\ promised lc_src.(Local.promises))) mem_src mem_tgt)
        (SCSRC: Memory.closed_timemap sc_src mem_src)
        (SCTGT: Memory.closed_timemap sc_tgt mem_tgt)
        (MEMSRC: Memory.closed mem_src)
        (MEMTGT: Memory.closed mem_tgt)
        (LOCALSRC: Local.wf lc_src mem_src)
        (LOCALTGT: Local.wf lc_tgt mem_tgt)
        (SIM: sim_local others pasts lc_src lc_tgt)
        (PAST: wf_pasts_memory mem_src pasts)
        (PROMATTACH: promises_not_attached (promised lc_src.(Local.promises)) mem_src)
        (OTHERSWF: forall loc' to', others loc' to' -> L loc')
        (CONSISTENT: Local.promise_consistent lc_tgt')
    :
      exists tr pasts' lc_src' sc_src' mem_src',
        (<<STEPSRC: Trace.steps tr (Thread.mk _ st lc_src sc_src mem_src) (Thread.mk _ st' lc_src' sc_src' mem_src')>>) /\
        (<<MEM: sim_memory (others \2/ (in_L /2\ promised lc_src'.(Local.promises))) mem_src' mem_tgt'>>) /\
        (<<ATTACHEDLE: not_attached_le others mem_src mem_src'>>) /\
        (<<PROMATTACH: promises_not_attached (promised lc_src'.(Local.promises)) mem_src'>>) /\
        (<<SC: TimeMap.le sc_src' sc_tgt'>>) /\
        (<<SIM: sim_local others pasts' lc_src' lc_tgt'>>) /\
        (<<PAST: wf_pasts_memory mem_src' pasts'>>) /\
        (<<PASTLE: pasts_le pasts pasts'>>)
  (* TODO: condition about event *)



  Lemma split_reserve_exists prom1 mem1 loc ts1 ts2 ts3
        (MLE: Memory.le prom1 mem1)
        (GET: Memory.get loc ts3 prom1 = Some (ts1, Message.reserve))
        (TS12: Time.lt ts1 ts2)
        (TS23: Time.lt ts2 ts3)
    :
      exists prom2 mem2,
        (<<FUTURE: reserve_future_memory prom1 mem1 prom2 mem2>>) /\
        (<<SPLITMEM:
           forall l t,
             Memory.get l t mem2 =
             (if loc_ts_eq_dec (l, t) (loc, ts2)
              then Some (ts1, Message.reserve)
              else
                if loc_ts_eq_dec (l, t) (loc, ts3)
                then Some (ts2, Message.reserve)
                else Memory.get l t mem1)>>) /\
        (<<SPLITPROM:
           forall l t,
             Memory.get l t prom2 =
             (if loc_ts_eq_dec (l, t) (loc, ts2)
              then Some (ts1, Message.reserve)
              else
                if loc_ts_eq_dec (l, t) (loc, ts3)
                then Some (ts2, Message.reserve)
                else Memory.get l t prom1)>>)
  .
  Proof.
    exploit Memory.remove_exists.
    { apply GET. } intros [prom_mid0 PROM0].
    exploit Memory.remove_exists_le; eauto. intros [mem_mid0 MEM0].
    assert (STEP0: Memory.promise prom1 mem1 loc ts1 ts3 Message.reserve prom_mid0 mem_mid0 Memory.op_kind_cancel).
    { econs; eauto. }
    hexploit promise_memory_le; eauto. intros MLE0.
    exploit (@Memory.add_exists mem_mid0 loc ts2 ts3 Message.reserve).
    { ii. erewrite Memory.remove_o in GET2; eauto. des_ifs. ss. guardH o.
      exploit Memory.get_disjoint.
      - apply MLE. apply GET.
      - apply GET2.
      - i. des; clarify.
        + unguard. des; auto.
        + eapply x1; eauto. inv LHS. econs; eauto. }
    { auto. }
    { econs. } intros [mem_mid1 MEM1].
    exploit Memory.add_exists_le; eauto. intros [prom_mid1 PROM11].
    assert (STEP1: Memory.promise prom_mid0 mem_mid0 loc ts2 ts3 Message.reserve prom_mid1 mem_mid1 Memory.op_kind_add).
    { econs; eauto. i. clarify.
    }
    hexploit promise_memory_le; eauto. intros MLE1.
    exploit (@Memory.add_exists mem_mid1 loc ts1 ts2 Message.reserve).
    { ii. erewrite Memory.add_o in GET2; eauto. des_ifs.
      { ss. des; clarify. inv LHS. inv RHS. ss.
        eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt.
        - apply TO.
        - apply FROM0.
      } ss. guardH o.
      erewrite Memory.remove_o in GET2; eauto. des_ifs. ss. guardH o0.
      exploit Memory.get_disjoint.
      - apply MLE. apply GET.
      - apply GET2.
      - i. des; clarify.
        + unguard. des; auto.
        + eapply x1; eauto. inv LHS. econs; eauto. etrans; eauto. left. auto.
    }
    { auto. }
    { econs. } intros [mem2 MEM2].
    exploit Memory.add_exists_le; eauto. intros [prom2 PROM2].
    assert (STEP2: Memory.promise prom_mid1 mem_mid1 loc ts1 ts2 Message.reserve prom2 mem2 Memory.op_kind_add).
    { econs; eauto. i. clarify.
    }
    assert (NEQ23: ts2 <> ts3).
    { ii. clarify. eapply Time.lt_strorder. eauto. }
    exists prom2, mem2. splits.
    - eauto.
    - i. erewrite (@Memory.add_o mem2 mem_mid1); eauto.
      erewrite (@Memory.add_o mem_mid1 mem_mid0); eauto. erewrite (@Memory.remove_o mem_mid0 mem1); eauto.
      des_ifs.
    - i. erewrite (@Memory.add_o prom2 prom_mid1); eauto.
      erewrite (@Memory.add_o prom_mid1 prom_mid0); eauto. erewrite (@Memory.remove_o prom_mid0 prom1); eauto.
      des_ifs.
  Admitted.

  Lemma sim_promise_step_forget prom_self prom_others pasts mem_src mem_tgt rel_src rel_tgt prom_src prom_tgt
        loc from to msg prom_tgt' mem_tgt' kind
        (NLOC: L loc)
        (STEPTGT: Memory.promise prom_tgt mem_tgt loc from to msg prom_tgt' mem_tgt' kind)
        (MEM: sim_memory (prom_others \2/ prom_self) mem_src mem_tgt)
        (ATTACH: not_attached (prom_others \2/ prom_self) mem_src)
        (MEMSRC: Memory.closed mem_src)
        (MEMTGT: Memory.closed mem_tgt)
        (WFSRC: Memory.le prom_src mem_src)
        (WFTGT: Memory.le prom_tgt mem_tgt)
        (RELSRC: forall (loc: Loc.t), Memory.closed_view (rel_src loc) mem_src)
        (RELTGT: forall (loc: Loc.t), Memory.closed_view (rel_tgt loc) mem_src)
        (PROMISE: sim_promise prom_self pasts rel_src rel_tgt prom_src prom_tgt)
        (PAST: wf_pasts_memory mem_src pasts)
    :
      exists prom_self' prom_src' mem_src',
        (<<FUTURE: reserve_future_memory prom_src mem_src prom_src' mem_src'>>) /\
        (<<MEM: sim_memory (prom_others \2/ prom_self') mem_src' mem_tgt'>>) /\
        (<<ATTACH: not_attached (prom_others \2/ prom_self') mem_src'>>) /\
        (<<PROMISE: sim_promise prom_self' pasts rel_src rel_tgt prom_src' prom_tgt'>>) /\
        (<<PAST: wf_pasts_memory mem_src' pasts>>)
  .
  Proof.
    inv PROMISE. inv MEM. dup STEPTGT. inv STEPTGT.
    - dup MEM. apply add_succeed_wf in MEM0. des.
      exploit Memory.add_exists; try apply TO1.
      { instantiate (1:=mem_src). instantiate (1:=loc). ii.
        exploit COVERED.
        { econs; eauto. } i. inv x0.
        eapply DISJOINT; eauto. }
      { eapply Message.wf_reserve. } i. des.
      exploit Memory.add_exists_le; try apply x0; eauto. i. des.
      assert (FUTURE: reserve_future_memory prom_src mem_src promises2 mem2).
      { econs.
        - econs 1; eauto. i. clarify.
        - econs 1. }
      destruct msg.
      { exists (fun loc' to' => prom_self loc' to' \/ (loc' = loc /\ to' = to)), promises2, mem2.
        splits; auto.
        + econs.
          * ii. erewrite Memory.add_o in GETTGT; eauto. erewrite Memory.add_o; eauto.
            des_ifs; ss.
            { des; clarify. exfalso. auto. }
            exploit COMPLETE0; eauto. ii. apply NPROMS. des; auto.
          * i. eapply concrete_promised_increase_promise; eauto.
            apply CONCRETE. eapply reserve_future_concrete_promised; eauto.
          * i. erewrite add_covered in COVERED0; eauto.
            eapply add_covered; eauto. des; auto.
        + ii. erewrite Memory.add_o in GET; eauto. des_ifs.
          ss. des; clarify; try by (eapply ATTACH; eauto).
          exploit ATTACH0; eauto.
          admit. (* change it *)
        + econs.
          * i. erewrite Memory.add_o in GETSRC; eauto.
            erewrite Memory.add_o; eauto.
            destruct (loc_ts_eq_dec (loc0, to0) (loc, to)); clarify.
            { des; clarify. exfalso. auto. }
            exploit NFORGET; eauto.
          * i. erewrite Memory.add_o in GETTGT; eauto.
            erewrite Memory.add_o; try eassumption.
            des_ifs; clarify; eauto.
          * i. erewrite (@Memory.add_o promises2 prom_src); eauto.
            erewrite (@Memory.add_o prom_tgt' prom_tgt); eauto. des_ifs; eauto.
            { ss. destruct a. clarify. esplits; eauto. }
            { exploit FORGET; eauto. des; clarify. }
        + eapply reserve_future_wf_pasts_memory; eauto.
      }
      { exists prom_self, promises2, mem2.
        splits; auto.
        + econs.
          * ii. erewrite Memory.add_o in GETTGT; eauto. erewrite Memory.add_o; eauto.
            des_ifs; ss.
            exploit COMPLETE0; eauto.
          * i. eapply concrete_promised_increase_promise; eauto.
            apply CONCRETE. eapply reserve_future_concrete_promised; eauto.
          * i. erewrite add_covered in COVERED0; eauto.
            eapply add_covered; eauto. des; auto.
        + ii. erewrite Memory.add_o in GET; eauto. des_ifs.
          ss. des; clarify; try by (eapply ATTACH; eauto).
        + econs.
          * i. erewrite Memory.add_o in GETSRC; eauto.
            erewrite Memory.add_o; eauto.
            destruct (loc_ts_eq_dec (loc0, to0) (loc, to)); clarify; eauto.
          * i. erewrite Memory.add_o in GETTGT; eauto.
            erewrite Memory.add_o; try eassumption.
            des_ifs; clarify; eauto.
          * i. erewrite (@Memory.add_o promises2 prom_src); eauto.
            erewrite (@Memory.add_o prom_tgt' prom_tgt); eauto. des_ifs; eauto.
            ss. des; clarify. exploit FORGET; eauto. i. des.
            eapply Memory.add_get0 in PROMISES. des. clarify.
        + eapply reserve_future_wf_pasts_memory; eauto.
      }

    - dup PROMISES. apply split_succeed_wf in PROMISES0. des. clarify.
      destruct (classic (prom_self loc ts3)) as [PROM|NPROM].
      { exploit FORGET; eauto. i. des. clarify.
        exploit split_reserve_exists; try apply GETSRC; eauto. i. des.
        exists (fun loc' to' => prom_self loc' to' \/ (loc' = loc /\ to' = to)), prom2, mem2.
        splits; auto.
        + econs.
          * ii. erewrite Memory.split_o in GETTGT0; eauto. erewrite SPLITMEM; eauto.
            des_ifs; ss.
            { des; clarify. exfalso. auto. }
            { des; clarify. exfalso. auto. }
            exploit COMPLETE0; eauto. ii. apply NPROMS. des; auto.
          * i. eapply concrete_promised_increase_promise; eauto.
            apply CONCRETE. eapply reserve_future_concrete_promised; eauto.
          * i. erewrite split_covered; cycle 1; eauto. apply COVERED.
            inv COVERED0. rewrite SPLITMEM in GET. des_ifs; des; ss; clarify; econs; eauto.
            { inv ITV. econs; eauto. ss. etrans; eauto. left. auto. }
            { inv ITV. econs; eauto. }
        + ii. erewrite SPLITMEM in GET. des_ifs. guardH o. guardH o0.
          ss. exploit ATTACH; cycle 1; eauto. des; auto. clarify. exfalso.
          exploit memory_get_ts_strong; try apply GET. i. des; clarify.
          { unguard. des; auto. }
          exfalso. exploit Memory.get_disjoint.
          * apply GET.
          * apply WFSRC. apply GETSRC.
          * i. des; clarify. specialize (x0 (Time.meet to' ts3)).
            unfold Time.meet in *. des_ifs.
            { eapply x0; eauto; econs; ss.
              - refl.
              - etrans; eauto. }
            { eapply x0; eauto; econs; ss.
              - left. auto.
              - etrans; eauto.
              - refl. }
        + econs.
          * i. erewrite SPLITPROM in GETSRC0; eauto.
            erewrite Memory.split_o; eauto.
            destruct (loc_ts_eq_dec (loc0, to0) (loc, to)); clarify.
            { ss. des; clarify. exfalso. auto. }
            destruct (loc_ts_eq_dec (loc0, to0) (loc, ts3)); clarify.
            { ss. des; clarify. exfalso. auto. }
            exploit NFORGET; eauto.
          * i. erewrite Memory.split_o in GETTGT0; eauto.
            erewrite SPLITPROM.
            des_ifs; clarify; eauto.
          * i. apply or_comm in PROM0. apply or_strengthen in PROM0.
            erewrite SPLITPROM; eauto.
            erewrite (@Memory.split_o prom_tgt' prom_tgt); eauto.
            des_ifs; des; ss; clarify; eauto.
            { ss. destruct a. clarify. esplits; eauto. }
            { exfalso. auto. }
            { esplits; eauto. }
        + eapply reserve_future_wf_pasts_memory; eauto.
      }
      { exploit COMPLETE; eauto. i. des.
        exploit NFORGET; eauto. i. des. des_ifs; des; clarify.
        exploit split_reserve_exists; try apply GETSRC; eauto. i. des.
        exists (fun loc' to' => prom_self loc' to' \/ (loc' = loc /\ to' = to)), prom2, mem2.
        splits; auto.
        + econs.
          * ii. erewrite Memory.split_o in GETTGT0; eauto. erewrite SPLITMEM; eauto.
            des_ifs; ss.
            { des; clarify. exfalso. auto. }
            exploit COMPLETE0; eauto. ii. apply NPROMS. des; auto.
          * i. eapply concrete_promised_increase_promise; eauto.
            apply CONCRETE. eapply reserve_future_concrete_promised; eauto.
          * i. erewrite split_covered; cycle 1; eauto. apply COVERED.
            inv COVERED0. rewrite SPLITMEM in GET. des_ifs; des; ss; clarify; econs; eauto.
            { inv ITV. econs; eauto. ss. etrans; eauto. left. auto. }
            { inv ITV. econs; eauto. }
        + ii. erewrite SPLITMEM in GET. des_ifs. guardH o. guardH o0.
          ss. exploit ATTACH; cycle 1; eauto. des; auto. clarify. exfalso.
          exploit memory_get_ts_strong; try apply GET. i. des; clarify.
          { unguard. des; auto. }
          exfalso. exploit Memory.get_disjoint.
          * apply GET.
          * apply WFSRC. apply GETSRC.
          * i. des; clarify. specialize (x0 (Time.meet to' ts3)).
            unfold Time.meet in *. des_ifs.
            { eapply x0; eauto; econs; ss.
              - refl.
              - etrans; eauto. }
            { eapply x0; eauto; econs; ss.
              - left. auto.
              - etrans; eauto.
              - refl. }
        + econs.
          * i. erewrite SPLITPROM in GETSRC0; eauto.
            erewrite Memory.split_o; eauto.
            destruct (loc_ts_eq_dec (loc0, to0) (loc, to)); clarify.
            { ss. des; clarify. exfalso. auto. }
            destruct (loc_ts_eq_dec (loc0, to0) (loc, ts3)); clarify.
            { ss. des; clarify. eauto. }
            exploit NFORGET; eauto.
          * i. erewrite Memory.split_o in GETTGT0; eauto.
            erewrite SPLITPROM.
            des_ifs; clarify; eauto.
          * i. apply or_comm in PROM. apply or_strengthen in PROM.
            erewrite SPLITPROM; eauto.
            erewrite (@Memory.split_o prom_tgt' prom_tgt); eauto.
            des_ifs; des; ss; clarify; eauto.
            { ss. destruct a. clarify. esplits; eauto. }
            { exfalso. auto. }
        + eapply reserve_future_wf_pasts_memory; eauto.
      }

    - dup PROMISES. apply lower_succeed_wf in PROMISES0. des. clarify. inv MSG_LE.
      assert (PROM: prom_self loc to).
      { exploit COMPLETE; eauto. i. des.
        apply NNPP. ii. exploit NFORGET; eauto. i. des. des_ifs. des. clarify. }
      exploit FORGET; eauto. i. des.
      exists prom_self, prom_src, mem_src. esplits; eauto.
      + econs.
        * ii. erewrite Memory.lower_o in GETTGT0; eauto.
          des_ifs; ss.
          { des; clarify. exfalso. apply NPROMS. auto. }
          exploit COMPLETE0; eauto.
        * i. eapply concrete_promised_increase_promise; eauto.
        * i. eapply lower_covered; eauto.
      + econs.
        * i. erewrite Memory.lower_o; eauto.
          destruct (loc_ts_eq_dec (loc0, to0) (loc, to)); clarify.
          { ss. des; clarify. }
          guardH o. exploit NFORGET; eauto.
        * i. erewrite Memory.lower_o in GETTGT0; eauto.
          des_ifs; clarify.
          { ss. des. clarify. eauto. }
          { guardH o. exploit COMPLETE; eauto. }
        * i. erewrite (@Memory.lower_o prom_tgt' prom_tgt); eauto. des_ifs; eauto.
          exploit FORGET; eauto. i. des. ss. clarify. esplits; eauto.

    - dup PROMISES. apply Memory.remove_get0 in PROMISES0. des.
      exploit COMPLETE; eauto. i. des. exploit NFORGET; eauto.
      { ii. exploit FORGET; eauto. i. des. rewrite GET in GETTGT. clarify. }
      i. des. rewrite GETTGT in *. clarify. des_ifs; des; clarify.
      exploit Memory.remove_exists.
      { eapply GETSRC. } i. des.
      exploit Memory.remove_exists_le; try apply x0; eauto. i. des.
      assert (FUTURE: reserve_future_memory prom_src mem_src mem2 mem0).
      { econs.
        - econs 4; eauto.
        - econs 1. }
      exists prom_self, mem2, mem0. splits; auto.
      + econs.
        * ii. erewrite Memory.remove_o in GETTGT0; eauto. erewrite Memory.remove_o; eauto.
          des_ifs. guardH o. exploit COMPLETE0; eauto.
        * i. eapply concrete_promised_increase_promise; eauto.
          apply CONCRETE. eapply reserve_future_concrete_promised; eauto.
        * i. erewrite remove_covered in COVERED0; eauto.
          eapply remove_covered; eauto. des; split; auto.
      + ii. erewrite Memory.remove_o in GET; eauto. des_ifs.
        eapply ATTACH; eauto.
      + econs.
        * i. erewrite Memory.remove_o in GETSRC0; eauto.
          erewrite Memory.remove_o; eauto.
          destruct (loc_ts_eq_dec (loc0, to0) (loc, to)); clarify. guardH o.
          exploit NFORGET; eauto.
        * i. erewrite Memory.remove_o in GETTGT0; eauto.
          erewrite Memory.remove_o; try eassumption.
          des_ifs; clarify. guardH o.
          exploit COMPLETE; eauto.
        * i. erewrite (@Memory.remove_o mem2 prom_src); eauto.
          erewrite (@Memory.remove_o prom_tgt' prom_tgt); eauto. des_ifs; eauto.
          exploit FORGET; eauto. i. des. ss. clarify.
      + eapply reserve_future_wf_pasts_memory; eauto.
        Unshelve. all: auto.
  Admitted.

  Lemma sim_remove_step_forget prom_self prom_others pasts mem_src mem_tgt rel_src rel_tgt prom_src prom_tgt
        loc from_tgt from_src to prom_tgt' val released_tgt released_src
        (NLOC: L loc)
        (REMOVEPROM: Memory.remove prom_tgt loc from_tgt to (Message.concrete val released_tgt) prom_tgt')
        (MEM: sim_memory (prom_others \2/ prom_self) mem_src mem_tgt)
        (ATTACH: not_attached (prom_others \2/ prom_self) mem_src)
        (MEMSRC: Memory.closed mem_src)
        (MEMTGT: Memory.closed mem_tgt)
        (WFSRC: Memory.le prom_src mem_src)
        (WFTGT: Memory.le prom_tgt mem_tgt)
        (RELSRC: forall (loc: Loc.t), Memory.closed_view (rel_src loc) mem_src)
        (RELTGT: forall (loc: Loc.t), Memory.closed_view (rel_tgt loc) mem_src)
        (PROMISE: sim_promise prom_self pasts rel_src rel_tgt prom_src prom_tgt)
        (PAST: wf_pasts_memory mem_src pasts)
        (FROM: Time.le from_tgt from_src)
        (TO: Time.lt from_src to)
        (RELEASEDWF: View.opt_wf released_src)
        (RELEASEDLE: View.opt_le released_src released_tgt)
        (RELEASEDCLOSED: Memory.closed_opt_view released_src mem_src)
        (NREAD: ~ (prom_others \2/ prom_self) loc from_src)
        (OTHERS: forall loc to, prom_others loc to -> prom_self loc to -> False)
    :
      exists prom_mid mem_mid prom_self' pasts' prom_src' mem_src',
        (<<FUTURE: reserve_future_memory prom_src mem_src prom_mid mem_mid>>) /\
        (<<WRITETGT: Memory.write prom_mid mem_mid loc from_src to val released_src prom_src' mem_src' Memory.op_kind_add>>) /\
        (<<MEM: sim_memory (prom_others \2/ prom_self') mem_src' mem_tgt>>) /\
        (<<ATTACH: not_attached (prom_others \2/ prom_self') mem_src'>>) /\
        (<<PROMISE: sim_promise prom_self' pasts' rel_src rel_tgt prom_src' prom_tgt'>>) /\
        (<<PAST: wf_pasts_memory mem_src' pasts'>>) /\
        (<<PASTLE: pasts_le pasts pasts'>>)
  .
  Proof.
    inv PROMISE. inv MEM.
    exploit Memory.remove_get0; eauto. i. des.
    assert (PROM: prom_self loc to).
    { exploit COMPLETE; eauto. i. des.
      apply NNPP. ii. exploit NFORGET; eauto. i. des. des_ifs. des. clarify. }
    exploit FORGET; eauto. i. des.
    i. des. rewrite GETTGT in *. clarify. des_ifs; des; clarify.
    exploit Memory.remove_exists.
    { eapply GETSRC. } i. des.
    exploit Memory.remove_exists_le; try apply x0; eauto. i. des.
    assert (FUTURE: reserve_future_memory prom_src mem_src mem2 mem0).
    { econs.
      - econs 4; eauto.
      - econs 1. }

    exploit Memory.add_exists.
    { instantiate (2:=from_src).
      ii. erewrite Memory.remove_o in GET2; eauto. des_ifs.
      exploit Memory.get_disjoint.
      - apply GET2.
      - apply WFSRC. apply GETSRC.
      - i. ss. des; clarify. eapply x3; eauto.
        inv LHS. econs; eauto. ss. eapply TimeFacts.le_lt_lt; eauto. }
    { apply TO. }
    { econs 1. apply RELEASEDWF. } intros [mem_src' ADDMEM].
    exploit Memory.add_exists_le.
    { instantiate (1:=mem0). instantiate (1:=mem2).
      ii. erewrite Memory.remove_o; eauto.
      erewrite Memory.remove_o in LHS; cycle 1; eauto. des_ifs. auto. }
    { eapply ADDMEM. } intros [prom_mid' ADDPROM].
    exploit Memory.remove_exists.
    { eapply Memory.add_get0. apply ADDPROM. } intros [prom_src' REMOVEPROMSRC].
    exists mem2, mem0, (fun loc' to' => prom_self loc' to' /\ (loc' <> loc \/ to' <> to)),
    (fun loc' to' => if loc_ts_eq_dec (loc', to') (loc, to) then Some mem_src else pasts loc' to'), prom_src', mem_src'.
    exploit MemoryFacts.add_remove_eq.
    { apply ADDPROM. }
    { apply REMOVEPROMSRC. } i. clarify.

    assert (PROMISESRC: Memory.promise mem2 mem0 loc from_src to (Message.concrete val released_src) prom_mid' mem_src' Memory.op_kind_add).
    { econs; eauto.
      - econs. etrans.
        + apply View.unwrap_opt_le in RELEASEDLE.
          inv RELEASEDLE. apply RLX.
        + inv MEMTGT. apply WFTGT in GETTGT.
          eapply CLOSED in GETTGT. des. inv MSG_TS. auto.
      - i. destruct msg'; cycle 1.
        { admit. }
        clarify. erewrite Memory.remove_o in GET; eauto. des_ifs.
        exploit ATTACH; eauto.
    }

    assert (FUTUREMEM: Memory.future mem_src mem_src').
    { etrans.
      - eapply reserve_future_future; eauto.
      - econs; [|refl]. econs.
        + econs. apply ADDMEM.
        + econs; eauto.
          eapply Memory.promise_closed_opt_view; cycle 1.
          { apply PROMISESRC. }
          eapply Memory.promise_closed_opt_view; eauto.
        + econs. etrans.
          * apply View.unwrap_opt_le in RELEASEDLE.
            inv RELEASEDLE. apply RLX.
          * inv MEMTGT. apply WFTGT in GETTGT.
            eapply CLOSED in GETTGT. des. inv MSG_TS. auto.
    }

    splits; auto.
    - econs; eauto.
    - econs; eauto.
      + i. erewrite Memory.add_o; eauto. erewrite Memory.remove_o; eauto. des_ifs.
        * ss. des; clarify. apply WFTGT in GETTGT. clarify.
          esplits; eauto.
        * exploit COMPLETE0.
          { ii. apply NPROMS. des; eauto. }
          { eauto. }
          i. guardH o. des. esplits; eauto.
      + i. inv PR. erewrite Memory.add_o in GET; eauto. des_ifs.
        * ss. des; clarify. econs; eauto.
        * eapply CONCRETE; eauto. erewrite Memory.remove_o in GET; eauto.
          des_ifs. econs; eauto.
      + i. rewrite add_covered in COVERED0; eauto.
        rewrite remove_covered in COVERED0; eauto. apply COVERED.
        apply or_comm in COVERED0. apply or_strengthen in COVERED0. des; clarify; auto.
        econs; eauto. inv COVERED1. econs; ss. eapply TimeFacts.le_lt_lt; eauto.
    - ii.
      erewrite Memory.add_o in GET; eauto.
      erewrite Memory.remove_o in GET; eauto. des_ifs.
      + ss. destruct a; clarify.
        apply NREAD. des; auto.
      + eapply ATTACH; cycle 1; eauto. des; auto.

    - econs; eauto.
      + i. erewrite Memory.remove_o in GETSRC0; try apply x0; eauto.
        erewrite Memory.remove_o; eauto. des_ifs; ss.
        * exploit NFORGET; try apply GETSRC0; eauto.
        * exploit NFORGET; try apply GETSRC0; eauto.
      + i. erewrite Memory.remove_o; try apply x0; eauto.
        erewrite Memory.remove_o in GETTGT0; cycle 1; eauto. des_ifs.
        exploit COMPLETE; eauto.
      + i. erewrite (@Memory.remove_o mem2 prom_src); eauto.
        erewrite (@Memory.remove_o prom_tgt' prom_tgt); eauto. des_ifs.
        * ss. des; clarify.
        * ss. eapply FORGET. des; auto.

    - inv PAST. econs.
      + ii. erewrite Memory.add_o in GET; eauto.
        erewrite Memory.remove_o in GET; eauto.
        destruct (loc_ts_eq_dec (loc0, to0) (loc, to)); ss.
        * des; clarify. esplits; eauto. des_ifs.
          { ss. des; clarify. exfalso. eapply Time.lt_strorder. eauto. }
          { guardH o. i. apply ONLY in PAST. des. auto. }
        * guardH o. exploit COMPLETE1; eauto. i. des. esplits; eauto.
          i. des_ifs.
          { ss. des; clarify. unguard.
            exfalso. exploit ATTACH; eauto. }
          { exploit ONLY; eauto. }
      + ii. des_ifs.
        * ss. des; clarify. splits; auto.
          { econs; eauto. eapply Memory.add_get0; eauto. }
          { apply Memory.future_future_weak; eauto. }
        * guardH o.
          apply ONLY in PAST. des. splits; auto.
          { eapply concrete_promised_increase_promise; eauto.
            eapply concrete_promised_increase_promise; eauto. }
          { etrans; eauto. eapply Memory.future_future_weak. auto. }
    - ii. des_ifs; eauto. ss. des; clarify.
      inv PAST. eapply ONLY in PAST0. des.
      inv CONCRETE0. apply WFSRC in GETSRC. clarify.
  Admitted.

  Lemma sim_write_step_forget prom_self prom_others pasts lc_src lc_tgt sc_src sc_tgt mem_src mem_tgt
        lc_tgt' sc_tgt' mem_tgt' loc from_tgt to val None released_tgt ord kind
        (NLOC: L loc)
        (STEPTGT: Local.write_step lc_tgt sc_tgt mem_tgt loc from_tgt to val None released_tgt ord lc_tgt' sc_tgt' mem_tgt' kind)
        (SC: TimeMap.le sc_src sc_tgt)
        (MEM: sim_memory (prom_others \2/ prom_self) mem_src mem_tgt)
        (ATTACH: not_attached (prom_others \2/ prom_self) mem_src)
        (SCSRC: Memory.closed_timemap sc_src mem_src)
        (SCTGT: Memory.closed_timemap sc_tgt mem_tgt)
        (MEMSRC: Memory.closed mem_src)
        (MEMTGT: Memory.closed mem_tgt)
        (LOCALSRC: Local.wf lc_src mem_src)
        (LOCALTGT: Local.wf lc_tgt mem_tgt)
        (SIM: sim_local prom_self pasts lc_src lc_tgt)
        (PAST: wf_pasts_memory mem_src pasts)
    :
      exists prom_self' prom_src mem_src_mid pasts' lc_src' sc_src' mem_src' from_src released_src,
        (<<FUTURE: reserve_future_memory lc_src.(Local.promises) mem_src prom_src mem_src_mid>>) /\
        (<<STEPSRC: Local.write_step (Local.mk lc_src.(Local.tview) prom_src) sc_src mem_src loc from_src to val None released_src ord lc_src' sc_src' mem_src' kind>>) /\
        (<<MEM: sim_memory (prom_others \2/ prom_self') mem_src' mem_tgt'>>) /\
        (<<ATTACH: not_attached (prom_others \2/ prom_self') mem_src'>>) /\
        (<<SC: TimeMap.le sc_src' sc_tgt'>>) /\
        (<<SIM: sim_local prom_self' pasts' lc_src' lc_tgt'>>) /\
        (<<PAST: wf_pasts_memory mem_src' pasts'>>) /\
        (<<PASTLE: pasts_le pasts pasts'>>)
  (* TODO: condition about event *)
  .
  Proof.
  Admitted.

  Lemma sim_thread_step prom_self prom_others pasts lang st lc_src lc_tgt sc_src sc_tgt mem_src mem_tgt pf e_tgt
        st' lc_tgt' sc_tgt' mem_tgt'
        (STEPTGT: @Thread.step lang pf e_tgt (Thread.mk _ st lc_tgt sc_tgt mem_tgt) (Thread.mk _ st' lc_tgt' sc_tgt' mem_tgt'))
        (NOREAD: no_read_msgs (prom_others \2/ prom_self) e_tgt)
        (SC: TimeMap.le sc_src sc_tgt)
        (MEM: sim_memory (prom_others \2/ prom_self) mem_src mem_tgt)
        (ATTACH: not_attached (prom_others \2/ prom_self) mem_src)
        (SCSRC: Memory.closed_timemap sc_src mem_src)
        (SCTGT: Memory.closed_timemap sc_tgt mem_tgt)
        (MEMSRC: Memory.closed mem_src)
        (MEMTGT: Memory.closed mem_tgt)
        (LOCALSRC: Local.wf lc_src mem_src)
        (LOCALTGT: Local.wf lc_tgt mem_tgt)
        (SIM: sim_local prom_self pasts lc_src lc_tgt)
        (PAST: wf_pasts_memory mem_src pasts)
    :
      exists tr prom_self' pasts' lc_src' sc_src' mem_src',
        (<<STEPSRC: Trace.steps tr (Thread.mk _ st lc_src sc_src mem_src) (Thread.mk _ st' lc_src' sc_src' mem_src')>>) /\
        (<<MEM: sim_memory (prom_others \2/ prom_self') mem_src' mem_tgt'>>) /\
        (<<ATTACH: not_attached (prom_others \2/ prom_self') mem_src'>>) /\
        (<<SC: TimeMap.le sc_src' sc_tgt'>>) /\
        (<<SIM: sim_local prom_self' pasts' lc_src' lc_tgt'>>) /\
        (<<PAST: wf_pasts_memory mem_src' pasts'>>) /\
        (<<PASTLE: pasts_le pasts pasts'>>)
          (* TODO: condition about event *)
  .
  Proof.
  Admitted.

  Lemma sim_promise_step_normal prom_self prom_others pasts mem_src mem_tgt rel_src rel_tgt prom_src prom_tgt
        loc from to msg_tgt prom_tgt' mem_tgt' kind
        (NLOC: ~ L loc)
        (STEPTGT: Memory.promise prom_tgt mem_tgt loc from to msg_tgt prom_tgt' mem_tgt' kind)
        (MEM: sim_memory (prom_others \2/ prom_self) mem_src mem_tgt)
        (ATTACH: not_attached (prom_others \2/ prom_self) mem_src)
        (MEMSRC: Memory.closed mem_src)
        (MEMTGT: Memory.closed mem_tgt)
        (WFSRC: Memory.le prom_src mem_src)
        (WFTGT: Memory.le prom_tgt mem_tgt)
        (RELSRC: forall (loc: Loc.t), Memory.closed_view (rel_src loc) mem_src)
        (RELTGT: forall (loc: Loc.t), Memory.closed_view (rel_tgt loc) mem_src)
        (PROMISE: sim_promise prom_self pasts rel_src rel_tgt prom_src prom_tgt)
        (PAST: wf_pasts_memory mem_src pasts)
        (MSGTGT: Memory.closed_message msg_tgt mem_tgt')
    :
      exists msg_src pasts' prom_src' mem_src',
        (<<STEPTGT: Memory.promise prom_src mem_src loc from to msg_src prom_src' mem_src' kind>>) /\
        (<<MSGSRC: Memory.closed_message msg_src mem_src'>>) /\
        (<<MEM: sim_memory (prom_others \2/ prom_self) mem_src' mem_tgt'>>) /\
        (<<ATTACH: not_attached (prom_others \2/ prom_self) mem_src'>>) /\
        (<<PROMISE: sim_promise prom_self pasts' rel_src rel_tgt prom_src' prom_tgt'>>) /\
        (<<PAST: wf_pasts_memory mem_src' pasts'>>) /\
        (<<PASTLE: pasts_le pasts pasts'>>)
  .
  Proof.
    exploit sim_message_exists.
    { eapply MEMSRC. }
    instantiate (1:=msg_tgt). i. des.

    inv PROMISE. inv MEM. dup STEPTGT. inv STEPTGT.
    - dup MEM. apply add_succeed_wf in MEM0. des.
      exploit Memory.add_exists; try apply TO1.
      { instantiate (1:=mem_src). instantiate (1:=loc). ii.
        exploit COVERED.
        { econs; eauto. } i. inv x0.
        eapply DISJOINT; eauto. }
      { instantiate (1:=msg_src). admit. (* Message.wf *) } intros [mem_src' ADDMEM].
      exploit Memory.add_exists_le; try apply ADDMEM; eauto. intros [prom_src' ADDPROM].
      exists msg_src. inv SIM.

      { exists (fun loc' to' => if loc_ts_eq_dec (loc', to') (loc, to) then Some mem_src else pasts loc' to')
        , prom_src', mem_src'.
        splits; auto.
        - econs; eauto.
          + econs; eauto.
            apply sim_opt_view_le in SIM0.
            apply View.unwrap_opt_le in SIM0.
            inv SIM0. inv TS. etrans; eauto.
          + i. clarify.
            admit.
        - econs.
          admit. (* Memory.closed_opt_view released_src mem_src' *)
        - econs.
          + i. erewrite Memory.add_o in GETTGT; eauto.
            erewrite Memory.add_o; eauto. des_ifs.
            * ss; des; clarify. esplits; eauto.
              eapply sim_opt_view_le; eauto.
            * exploit COMPLETE0; eauto.
          + i. inv PR. erewrite Memory.add_o in GET; eauto. des_ifs.
            * ss. des; clarify. econs.
              eapply Memory.add_get0; eauto.
            * exploit CONCRETE; eauto.
              { econs; eauto. } i. inv x.
              eapply Memory.add_get1 in GET0; eauto. econs; eauto.
          + i. erewrite add_covered in COVERED0; eauto.
            erewrite add_covered; cycle 1; eauto. des; auto.
        - ii.
          admit. (* change it *)
        - econs.
          + i. erewrite Memory.add_o in GETSRC; eauto.
            erewrite Memory.add_o; eauto.
            destruct (loc_ts_eq_dec (loc0, to0) (loc, to)); eauto.
            ss. des; clarify. esplits; eauto.
          + i. erewrite Memory.add_o in GETTGT; eauto.
            erewrite Memory.add_o; cycle 1; eauto. des_ifs; eauto.
          + i. erewrite (@Memory.add_o prom_src'); eauto.
            erewrite (@Memory.add_o prom_tgt'); eauto. des_ifs.
            * ss. des; clarify. exfalso.
              exploit FORGET; eauto. i. des. clarify.
            * exploit FORGET; eauto.
        - inv PAST. econs.
          + ii. erewrite Memory.add_o in GET; eauto.
            destruct (loc_ts_eq_dec (loc0, to0) (loc, to)).
            * ss. des; clarify. esplits; eauto.
              { admit. (* Memory.closed_opt_view released mem_src *) }
              { i. des_ifs.
                - ss. des; clarify. refl.
                - guardH o. apply ONLY in PAST. des. auto. }
            * guardH o. exploit COMPLETE1; eauto. i. des.
              esplits; eauto. i. des_ifs.
              { ss. des; clarify. exfalso.
                exploit ATTACH0; eauto.
                admit. }
              { ss. exploit COMPLETE1; eauto. }
          + i. des_ifs.
            * ss. des; clarify. esplits; eauto.
              { econs. eapply Memory.add_get0. eauto. }
              { apply Memory.future_future_weak.
                admit. }
            * guardH o. exploit ONLY; eauto. i. des. splits; auto.
              { inv CONCRETE0. eapply Memory.add_get1 in GET; eauto. econs; eauto. }
              { etrans; eauto.
                admit. }
        - ii. des_ifs. ss. des; clarify. exfalso.
          inv PAST. exploit ONLY; eauto. i. des. inv CONCRETE0.
          apply Memory.add_get0 in ADDMEM. des. clarify.
      }

      { exists pasts, prom_src', mem_src'.
        splits; auto.
        - econs; eauto. i. clarify.
        - econs.
          + i. erewrite Memory.add_o in GETTGT; eauto.
            erewrite Memory.add_o; eauto. des_ifs.
            exploit COMPLETE0; eauto.
          + i. inv PR. erewrite Memory.add_o in GET; eauto. des_ifs.
            exploit CONCRETE; eauto.
            { econs; eauto. } i. inv x.
            eapply Memory.add_get1 in GET0; eauto. econs; eauto.
          + i. erewrite add_covered in COVERED0; eauto.
            erewrite add_covered; cycle 1; eauto. des; auto.
        - ii.
          admit. (* change it *)
        - econs.
          + i. erewrite Memory.add_o in GETSRC; eauto.
            erewrite Memory.add_o; eauto.
            destruct (loc_ts_eq_dec (loc0, to0) (loc, to)); eauto.
            ss. des; clarify. esplits; eauto.
          + i. erewrite Memory.add_o in GETTGT; eauto.
            erewrite Memory.add_o; cycle 1; eauto. des_ifs; eauto.
          + i. erewrite (@Memory.add_o prom_src'); eauto.
            erewrite (@Memory.add_o prom_tgt'); eauto. des_ifs.
            * ss. des; clarify. exfalso.
              exploit FORGET; eauto. i. des. clarify.
            * exploit FORGET; eauto.
        - inv PAST. econs.
          + ii. erewrite Memory.add_o in GET; eauto.
            destruct (loc_ts_eq_dec (loc0, to0) (loc, to)).
            * ss.
            * guardH o. exploit COMPLETE1; eauto.
          + i. exploit ONLY; eauto. i. des. splits; auto.
            * inv CONCRETE0. eapply Memory.add_get1 in GET; eauto. econs; eauto.
            * etrans; eauto.
              apply Memory.future_future_weak. econs; [|refl]. econs; eauto.
        - refl.
      }

    - dup PROMISES. apply split_succeed_wf in PROMISES0. des. clarify.
      exploit COMPLETE; eauto. i. des.
      exploit NFORGET; eauto.
      { ii. exploit FORGET; eauto. i. des. clarify. } i. des. des_ifs.

      { des. clarify.
        exploit Memory.split_exists.
  Admitted.

End SIM.
