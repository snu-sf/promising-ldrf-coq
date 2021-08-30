From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import Loc.
From PromisingLib Require Import Language.

Require Import Event.
Require Import Time.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.
Require Import Progress.

Require Import LowerPromises.

Require Import SimMemory.
Require Import SimPromises.
Require Import SimLocal.
Require Import SimThread.

Set Implicit Arguments.


Lemma read_step_cur_future
      lc1 mem1 loc val released ord lc2
      (WF1: Local.wf lc1 mem1)
      (ORD: Ordering.le ord Ordering.relaxed)
      (READ: Local.read_step lc1 mem1 loc ((TView.cur (Local.tview lc1)).(View.rlx) loc) val released ord lc2):
  <<PROMISES: (Local.promises lc1) = (Local.promises lc2)>> /\
  <<TVIEW_RLX: (TView.cur (Local.tview lc1)).(View.rlx) = (TView.cur (Local.tview lc2)).(View.rlx)>> /\
  <<TVIEW_PLN: forall l (LOC: l <> loc),
      (TView.cur (Local.tview lc1)).(View.pln) l = (TView.cur (Local.tview lc2)).(View.pln) l>>.
Proof.
  destruct lc1 as [tview1 promises1]. inv READ. ss.
  esplits; eauto.
  - condtac; ss; try by destruct ord.
    apply TimeMap.antisym.
    + etrans; [|apply TimeMap.join_l]. apply TimeMap.join_l.
    + apply TimeMap.join_spec; auto using TimeMap.bot_spec.
      apply TimeMap.join_spec; try refl.
      unfold View.singleton_ur_if. condtac; ss.
      * ii. unfold TimeMap.singleton, LocFun.add, LocFun.init, LocFun.find.
        condtac; try apply Time.bot_spec.
        subst. refl.
      * ii. unfold TimeMap.singleton, LocFun.add, LocFun.init, LocFun.find.
        condtac; try apply Time.bot_spec.
        subst. refl.
  - i. condtac; ss; try by destruct ord.
    unfold TimeMap.join, TimeMap.bot.
    rewrite TimeFacts.le_join_l; try apply Time.bot_spec.
    rewrite TimeFacts.le_join_l; ss.
    etrans; [|apply Time.bot_spec].
    unfold View.singleton_ur_if. condtac; ss; try refl.
    unfold TimeMap.singleton, LocFun.add, LocFun.init. condtac; ss. refl.
Qed.

Lemma fence_step_future
      lc1 sc1 ordr ordw lc2 sc2
      (ORDR: Ordering.le ordr Ordering.relaxed)
      (ORDW: Ordering.le ordw Ordering.acqrel)
      (FENCE: Local.fence_step lc1 sc1 ordr ordw lc2 sc2):
  <<PROMISES: (Local.promises lc1) = (Local.promises lc2)>> /\
  <<TVIEW: (TView.cur (Local.tview lc1)) = (TView.cur (Local.tview lc2))>>.
Proof.
  destruct lc1 as [tview1 promises1]. inv FENCE. split; ss.
  condtac; try by destruct ordw.
  condtac; try by destruct ordr.
Qed.

Lemma write_step_consistent
      lc1 sc1 mem1
      loc val ord
      (WF1: Local.wf lc1 mem1)
      (SC1: Memory.closed_timemap sc1 mem1)
      (MEM1: Memory.closed mem1)
      (PROMISES1: Ordering.le Ordering.strong_relaxed ord -> Memory.nonsynch_loc loc (Local.promises lc1))
      (CONS1: Local.promise_consistent lc1):
  exists from to released lc2 sc2 mem2 kind,
    <<STEP: Local.write_step lc1 sc1 mem1 loc from to val None released ord lc2 sc2 mem2 kind>> /\
    <<CONS2: Local.promise_consistent lc2>>.
Proof.
  destruct (classic (exists f t m, Memory.get loc t (Local.promises lc1) = Some (f, m) /\
                              m <> Message.reserve)).
  { des.
    exploit Memory.min_concrete_ts_exists; eauto. i. des.
    exploit Memory.min_concrete_ts_spec; eauto. i. des.
    exploit Memory.get_ts; try exact GET. i. des.
    { subst. inv WF1. rewrite BOT in *. ss. }
    clear f t m H H0 MIN.
    exploit progress_write_step_split; try exact GET; eauto.
    { ss. unfold TimeMap.bot. apply Time.bot_spec. }
    i. des.
    esplits; eauto. ii.
    assert (TS: loc0 = loc -> Time.le ts ts0).
    { i. subst. inv x2. inv WRITE. inv PROMISE0. ss.
      revert PROMISE.
      erewrite Memory.remove_o; eauto. condtac; ss. des; ss.
      erewrite Memory.split_o; eauto. repeat condtac; ss; i.
      - des; ss. subst. refl.
      - des; ss. 
        exploit Memory.min_concrete_ts_spec; try exact PROMISE; eauto. i. des. ss. }
    inv x2. inv WRITE. inv PROMISE0. ss.
    unfold TimeMap.join, TimeMap.singleton.
    unfold LocFun.add, LocFun.init, LocFun.find.
    condtac; ss.
    - subst. apply TimeFacts.join_spec_lt.
      + eapply TimeFacts.lt_le_lt; try eapply TS; eauto.
      + eapply TimeFacts.lt_le_lt; try eapply TS; eauto.
        apply Time.middle_spec. ss.
    - revert PROMISE.
      erewrite Memory.remove_o; eauto. condtac; ss.
      erewrite Memory.split_o; eauto. repeat condtac; ss; try by des; ss.
      guardH o. guardH o0. guardH o1. i.
      apply TimeFacts.join_spec_lt; eauto.
      destruct (TimeFacts.le_lt_dec ts0 Time.bot); ss.
      inv l; inv H.
      inv WF1. rewrite BOT in *. ss.
  }
  { exploit progress_write_step; eauto.
    { apply Time.incr_spec. }
    i. des.
    esplits; eauto. ii.
    inv x0. inv WRITE. inv PROMISE0. ss.
    revert PROMISE.
    erewrite Memory.remove_o; eauto. condtac; ss.
    erewrite Memory.add_o; eauto. condtac; ss. i.
    destruct (Loc.eq_dec loc0 loc).
    - subst. exfalso. apply H; eauto.
    - unfold TimeMap.join, TimeMap.singleton.
      unfold LocFun.add, LocFun.init, LocFun.find.
      condtac; ss.
      apply TimeFacts.join_spec_lt; eauto.
      destruct (TimeFacts.le_lt_dec ts Time.bot); ss.
      inv l; inv H0.
      inv WF1. rewrite BOT in *. ss.
  }
Qed.
