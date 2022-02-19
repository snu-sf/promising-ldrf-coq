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

Require Import SimMemory.
Require Import SimPromises.
Require Import SimLocal.
Require Import SimThread.

Require Import FulfillStep.
Require Import ReorderStep.

Set Implicit Arguments.


Definition local_relfenced (lc:Local.t) :=
  (Local.mk (TView.mk
               (fun _ => (TView.cur (Local.tview lc)))
               (TView.cur (Local.tview lc))
               (TView.acq (Local.tview lc)))
            (Local.promises lc)).

Lemma local_relfenced_wf
      lc mem
      (WF: Local.wf lc mem):
  Local.wf (local_relfenced lc) mem.
Proof.
  inv WF. econs; ss; eauto.
  - inv TVIEW_WF. econs; ss. refl.
  - inv TVIEW_CLOSED. econs; ss.
Qed.

Lemma sim_local_promise_relfenced
      pview
      lc1_src mem1_src
      lc1_tgt mem1_tgt
      lc2_tgt mem2_tgt
      loc from to msg kind
      (STEP_TGT: Local.promise_step lc1_tgt mem1_tgt loc from to msg lc2_tgt mem2_tgt kind)
      (LOCAL1: sim_local pview lc1_src (local_relfenced lc1_tgt))
      (MEM1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
      (MEM1_SRC: Memory.closed mem1_src)
      (MEM1_TGT: Memory.closed mem1_tgt):
  exists lc2_src mem2_src,
    <<STEP_SRC: Local.promise_step lc1_src mem1_src loc from to (SimPromises.none_if loc to pview msg) lc2_src mem2_src (SimPromises.kind_transf loc to pview kind)>> /\
    <<LOCAL2: sim_local pview lc2_src (local_relfenced lc2_tgt)>> /\
    <<MEM2: sim_memory mem2_src mem2_tgt>>.
Proof.
  inv LOCAL1. inv STEP_TGT.
  exploit SimPromises.promise; eauto.
  { apply WF1_SRC. }
  { apply WF1_TGT. }
  i. des.
  exploit Memory.promise_future; try apply PROMISE_SRC; try apply WF1_SRC; eauto.
  { SimPromises.none_if_tac; econs; ss. inv CLOSED.
    eapply sim_memory_closed_opt_view; eauto. }
  i. des.
  esplits; eauto.
  - econs; eauto.
    SimPromises.none_if_tac; econs; ss. inv CLOSED.
    eapply sim_memory_closed_opt_view; eauto.
  - econs; eauto.
Qed.

Lemma sim_local_read_relfenced
      pview
      lc1_src mem1_src
      lc1_tgt mem1_tgt
      lc2_tgt
      loc ts val released_tgt ord_src ord_tgt
      (STEP_TGT: Local.read_step lc1_tgt mem1_tgt loc ts val released_tgt ord_tgt lc2_tgt)
      (LOCAL1: sim_local pview lc1_src (local_relfenced lc1_tgt))
      (MEM1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
      (MEM1_SRC: Memory.closed mem1_src)
      (MEM1_TGT: Memory.closed mem1_tgt)
      (ORD: Ordering.le ord_src ord_tgt):
  exists released_src lc2_src,
    <<REL: View.opt_le released_src released_tgt>> /\
    <<STEP_SRC: Local.read_step lc1_src mem1_src loc ts val released_src ord_src lc2_src>> /\
    <<LOCAL2: sim_local pview lc2_src (local_relfenced lc2_tgt)>>.
Proof.
  inv LOCAL1. inv STEP_TGT.
  exploit sim_memory_get; try apply GET; try apply MEM1. i. des. inv MSG.
  esplits; eauto.
  - econs; eauto; try by etrans; eauto.
    eapply TViewFacts.readable_mon; eauto. apply TVIEW.
  - econs; eauto. inv TVIEW. ss. econs; s.
    + i. unfold LocFun.find. etrans; [by apply WF1_SRC|].
      eauto using View.join_l.
    + repeat apply View.join_le; ss.
      * unfold View.singleton_ur_if. repeat condtac; viewtac.
      * repeat condtac; viewtac.
    + repeat apply View.join_le; ss.
      * unfold View.singleton_ur_if. repeat condtac; viewtac.
      * repeat condtac; viewtac.
Qed.

Lemma sim_local_fulfill_relfenced
      pview
      lc1_src sc1_src mem1_src
      lc1_tgt sc1_tgt mem1_tgt
      lc2_tgt sc2_tgt
      loc from to val releasedm_src releasedm_tgt released ord_src ord_tgt
      (RELM_LE: View.opt_le releasedm_src releasedm_tgt)
      (RELM_WF: View.opt_wf releasedm_src)
      (RELM_CLOSED: Memory.closed_opt_view releasedm_src mem1_src)
      (WF_RELM_TGT: View.opt_wf releasedm_tgt)
      (ORD: Ordering.le ord_src ord_tgt)
      (PVIEW: (Ordering.le Ordering.acqrel ord_tgt /\ SimPromises.mem loc to pview = false) \/
              Ordering.le ord_tgt Ordering.plain)
      (STEP_TGT: fulfill_step lc1_tgt sc1_tgt loc from to val releasedm_tgt released ord_tgt lc2_tgt sc2_tgt)
      (LOCAL1: sim_local pview lc1_src (local_relfenced lc1_tgt))
      (SC1: TimeMap.le sc1_src sc1_tgt)
      (MEM1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
      (SC1_SRC: Memory.closed_timemap sc1_src mem1_src)
      (SC1_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
      (MEM1_SRC: Memory.closed mem1_src)
      (MEM1_TGT: Memory.closed mem1_tgt):
  exists lc2_src sc2_src,
    <<STEP_SRC: fulfill_step lc1_src sc1_src loc from to val releasedm_src (SimPromises.none_if_released loc to pview released) ord_src lc2_src sc2_src>> /\
    <<LOCAL2: sim_local (SimPromises.unset loc to pview) lc2_src (local_relfenced lc2_tgt)>> /\
    <<SC2: TimeMap.le sc2_src sc2_tgt>>.
Proof.
  guardH PVIEW.
  inv STEP_TGT.
  assert (RELT_LE:
   View.opt_le
     (TView.write_released (Local.tview lc1_src) sc1_src loc to releasedm_src ord_src)
     (TView.write_released (Local.tview lc1_tgt) sc2_tgt loc to releasedm_tgt ord_tgt)).
  { unguardH PVIEW. des.
    - unfold TView.write_released.
      condtac; [|by econs].
      condtac; cycle 1.
      { by destruct ord_src, ord_tgt; inv PVIEW; inv COND0. }
      econs. unfold TView.write_tview. s.
      repeat (condtac; aggrtac); try by apply WF1_TGT.
      + rewrite <- View.join_r. rewrite <- ? View.join_l. apply LOCAL1.
      + rewrite <- View.join_r. rewrite <- ? View.join_l.
        etrans; [|apply LOCAL1]. apply WF1_SRC.
    - unfold TView.write_released. repeat (condtac; viewtac).
  }
  assert (RELT_WF:
   View.opt_wf (TView.write_released (Local.tview lc1_src) sc1_src loc to releasedm_src ord_src)).
  { unfold TView.write_released. condtac; econs.
    repeat (try condtac; viewtac; try apply WF1_SRC).
  }
  exploit SimPromises.remove; try exact REMOVE;
    try exact MEM1; try apply LOCAL1; eauto.
  i. des. esplits.
  - econs; eauto.
    + unfold SimPromises.none_if_released. condtac.
      * unguardH PVIEW. des; ss. unfold TView.write_released. condtac; [|refl].
        destruct ord_src, ord_tgt; inv ORD; inv PVIEW; inv COND0.
      * etrans; eauto.
    + unfold SimPromises.none_if_released. condtac; viewtac.
    + eapply TViewFacts.writable_mon; try exact WRITABLE; eauto. apply LOCAL1.
  - econs; eauto. inv LOCAL1. inv TVIEW. ss. econs; s.
    + i. rewrite LocFun.add_spec. condtac; ss.
      { subst. unfold LocFun.find. condtac; apply View.join_le; viewtac.
        etrans; eauto. refl.
      }
      unfold LocFun.find. etrans; [by apply WF1_SRC|].
      eauto using View.join_l.
    + apply View.join_le; viewtac.
    + apply View.join_le; viewtac.
  - ss.
Qed.

Lemma sim_local_promise_not_lower
      pview
      lc1_src
      lc1_tgt mem1_tgt loc from to msg_tgt lc1 mem2_tgt kind
      (LOCAL: sim_local pview lc1_src (local_relfenced lc1_tgt))
      (STEP: Local.promise_step lc1_tgt mem1_tgt loc from to msg_tgt lc1 mem2_tgt kind)
      (KIND: negb (Memory.op_kind_is_lower kind)):
  SimPromises.mem loc to pview = false.
Proof.
  destruct (SimPromises.mem loc to pview) eqn:X; ss.
  inv LOCAL. inv PROMISES. exploit PVIEW; eauto. i.
  inv STEP. inv PROMISE; ss.
  - exploit Memory.add_get0; try exact PROMISES; eauto. i. des. congr.
  - exploit Memory.split_get0; try exact PROMISES; eauto. i. des. congr.
  - exploit Memory.remove_get0; try exact PROMISES; eauto. i. des. congr.
Qed.

Lemma sim_local_write_relfenced
      pview
      lc1_src sc1_src mem1_src
      lc1_tgt sc1_tgt mem1_tgt
      lc2_tgt sc2_tgt mem2_tgt
      loc from to val releasedm_src releasedm_tgt released_tgt ord_src ord_tgt kind
      (RELM_LE: View.opt_le releasedm_src releasedm_tgt)
      (RELM_SRC_WF: View.opt_wf releasedm_src)
      (RELM_SRC_CLOSED: Memory.closed_opt_view releasedm_src mem1_src)
      (RELM_TGT_WF: View.opt_wf releasedm_tgt)
      (RELM_TGT_CLOSED: Memory.closed_opt_view releasedm_tgt mem1_tgt)
      (ORD: Ordering.le ord_src ord_tgt)
      (ORD_TGT: Ordering.le ord_tgt Ordering.plain \/ Ordering.le Ordering.acqrel ord_tgt)
      (STEP_TGT: Local.write_step lc1_tgt sc1_tgt mem1_tgt loc from to val releasedm_tgt released_tgt ord_tgt lc2_tgt sc2_tgt mem2_tgt kind)
      (LOCAL1: sim_local pview lc1_src (local_relfenced lc1_tgt))
      (SC1: TimeMap.le sc1_src sc1_tgt)
      (MEM1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
      (SC1_SRC: Memory.closed_timemap sc1_src mem1_src)
      (SC1_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
      (MEM1_SRC: Memory.closed mem1_src)
      (MEM1_TGT: Memory.closed mem1_tgt):
  exists released_src lc2_src sc2_src mem2_src,
    <<STEP_SRC: Local.write_step lc1_src sc1_src mem1_src loc from to val releasedm_src released_src ord_src lc2_src sc2_src mem2_src (SimPromises.kind_transf loc to pview kind)>> /\
    <<REL2: View.opt_le released_src released_tgt>> /\
    <<LOCAL2: sim_local (SimPromises.unset loc to pview) lc2_src (local_relfenced lc2_tgt)>> /\
    <<SC2: TimeMap.le sc2_src sc2_tgt>> /\
    <<MEM2: sim_memory mem2_src mem2_tgt>>.
Proof.
  guardH ORD_TGT.
  exploit write_promise_fulfill; eauto. i. des.
  exploit Local.promise_step_future; eauto. i. des.
  exploit sim_local_promise_relfenced; eauto. i. des.
  exploit Local.promise_step_future; eauto. i. des.
  assert (PVIEW: __guard__ ((Ordering.le Ordering.acqrel ord_tgt /\ SimPromises.mem loc to pview = false) \/
                              Ordering.le ord_tgt Ordering.plain)).
  { destruct (Ordering.le ord_tgt Ordering.strong_relaxed) eqn:X.
    - right. unguardH ORD_TGT. destruct ord_tgt; des; ss.
    - left. splits.
      { by destruct ord_tgt; inv X. }
      hexploit ORD0.
      { by destruct ord_tgt; inv X. }
      exploit Local.write_step_strong_relaxed; eauto.
      { by destruct ord_tgt. }
      i. eapply sim_local_promise_not_lower; try exact STEP1; eauto.
  }
  exploit sim_local_fulfill_relfenced; try apply STEP2;
    try apply LOCAL2; try apply MEM2; eauto.
  { eapply Memory.future_closed_opt_view; eauto. }
  i. des.
  exploit promise_fulfill_write_sim_memory; try exact STEP_SRC; try exact STEP_SRC0; eauto.
  { i. hexploit ORD0; eauto.
    i. des. subst. splits; auto. eapply sim_local_nonsynch_loc; eauto.
  }
  i. des. esplits; eauto.
  - unguardH PVIEW. des.
    + unfold SimPromises.none_if_released in *. rewrite PVIEW0 in *. ss.
    + subst. unfold TView.write_released at 1. condtac; [|by econs].
      destruct ord_src, ord_tgt; inv ORD; inv PVIEW; inv COND.
  - etrans; eauto.
Qed.

Lemma sim_local_update_relfenced
      pview
      lc1_src sc1_src mem1_src
      lc1_tgt sc1_tgt mem1_tgt
      lc2_tgt
      lc3_tgt sc3_tgt mem3_tgt
      loc ts1 val1 released1_tgt ord1_src ord1_tgt
      from2 to2 val2 released2_tgt ord2_src ord2_tgt kind
      (STEP1_TGT: Local.read_step lc1_tgt mem1_tgt loc ts1 val1 released1_tgt ord1_tgt lc2_tgt)
      (STEP2_TGT: Local.write_step lc2_tgt sc1_tgt mem1_tgt loc from2 to2 val2 released1_tgt released2_tgt ord2_tgt lc3_tgt sc3_tgt mem3_tgt kind)
      (LOCAL1: sim_local pview lc1_src (local_relfenced lc1_tgt))
      (SC1: TimeMap.le sc1_src sc1_tgt)
      (MEM1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
      (SC1_SRC: Memory.closed_timemap sc1_src mem1_src)
      (SC1_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
      (MEM1_SRC: Memory.closed mem1_src)
      (MEM1_TGT: Memory.closed mem1_tgt)
      (ORD1: Ordering.le ord1_src ord1_tgt)
      (ORD2: Ordering.le ord2_src ord2_tgt)
      (ORD2_TGT: Ordering.le ord2_tgt Ordering.plain \/ Ordering.le Ordering.acqrel ord2_tgt):
  exists released1_src released2_src lc2_src lc3_src sc3_src mem3_src,
    <<REL1: View.opt_le released1_src released1_tgt>> /\
    <<REL2: View.opt_le released2_src released2_tgt>> /\
    <<STEP1_SRC: Local.read_step lc1_src mem1_src loc ts1 val1 released1_src ord1_src lc2_src>> /\
    <<STEP2_SRC: Local.write_step lc2_src sc1_src mem1_src loc from2 to2 val2 released1_src released2_src ord2_src lc3_src sc3_src mem3_src (SimPromises.kind_transf loc to2 pview kind)>> /\
    <<LOCAL3: sim_local (SimPromises.unset loc to2 pview) lc3_src (local_relfenced lc3_tgt)>> /\
    <<SC3: TimeMap.le sc3_src sc3_tgt>> /\
    <<MEM3: sim_memory mem3_src mem3_tgt>>.
Proof.
  guardH ORD2_TGT.
  exploit Local.read_step_future; eauto. i. des.
  exploit sim_local_read_relfenced; eauto. i. des.
  exploit Local.read_step_future; eauto. i. des.
  hexploit sim_local_write_relfenced; eauto. i. des.
  esplits; eauto.
Qed.

Lemma sim_local_fence_relfenced
      pview
      lc1_src sc1_src mem1_src
      lc1_tgt sc1_tgt mem1_tgt
      lc2_tgt sc2_tgt
      ordr_src ordw_src
      ordr_tgt ordw_tgt
      (STEP_TGT: Local.fence_step lc1_tgt sc1_tgt ordr_tgt ordw_tgt lc2_tgt sc2_tgt)
      (LOCAL1: sim_local pview lc1_src (local_relfenced lc1_tgt))
      (SC1: TimeMap.le sc1_src sc1_tgt)
      (MEM1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
      (ORDR: Ordering.le ordr_src ordr_tgt)
      (ORDW: Ordering.le ordw_src ordw_tgt)
      (ORDR_TGT: Ordering.le ordr_tgt Ordering.acqrel)
      (ORDW_TGT: Ordering.le ordw_tgt Ordering.relaxed):
  exists lc2_src sc2_src,
    <<STEP_SRC: Local.fence_step lc1_src sc1_src ordr_src ordw_src lc2_src sc2_src>> /\
    <<LOCAL2: sim_local pview lc2_src (local_relfenced lc2_tgt)>> /\
    <<SC2: TimeMap.le sc2_src sc2_tgt>>.
Proof.
  inv STEP_TGT. esplits; eauto.
  - econs; eauto.
    + i. eapply sim_local_nonsynch; eauto.
    + i. subst. eapply sim_local_memory_bot; eauto.
      eapply PROMISES; eauto. destruct ordw_tgt; ss.
  - inv LOCAL1. inv TVIEW. econs; ss.
    econs; s; unfold LocFun.find; repeat condtac; aggrtac.
    + etrans; eauto. apply WF1_TGT.
    + etrans; eauto. apply WF1_TGT.
    + etrans; eauto. apply WF1_TGT.
  - unfold TView.write_fence_sc.
    repeat (condtac; viewtac).
Qed.

Lemma sim_local_is_racy_relfenced
      pview
      lc1_src mem1_src
      lc1_tgt mem1_tgt
      loc to ord_src ord_tgt
      (STEP_TGT: Local.is_racy lc1_tgt mem1_tgt loc to ord_tgt)
      (LOCAL1: sim_local pview lc1_src (local_relfenced lc1_tgt))
      (MEM1: sim_memory mem1_src mem1_tgt)
      (ORD: Ordering.le ord_src ord_tgt):
    <<STEP_SRC: Local.is_racy lc1_src mem1_src loc to ord_src>>.
Proof.
  inv LOCAL1. inv STEP_TGT.
  exploit sim_memory_get; try apply GET; try apply MEM1. i. des.
  econs; eauto.
  - destruct (Memory.get loc to (Local.promises lc1_src)) as [[]|] eqn:GETP_SRC; ss.
    inv PROMISES. exploit COMPLETE; eauto. i. ss.
  - eapply TViewFacts.racy_view_mon; eauto. apply TVIEW.
  - ii. subst. inv MSG. ss.
  - i. exploit MSG2; try by (destruct ord_src, ord_tgt; ss).
    i. subst. inv MSG. ss.
Qed.

Lemma sim_local_racy_read_relfenced
      pview
      lc1_src mem1_src
      lc1_tgt mem1_tgt
      loc to val ord_src ord_tgt
      (STEP_TGT: Local.racy_read_step lc1_tgt mem1_tgt loc to val ord_tgt)
      (LOCAL1: sim_local pview lc1_src (local_relfenced lc1_tgt))
      (MEM1: sim_memory mem1_src mem1_tgt)
      (ORD: Ordering.le ord_src ord_tgt):
    <<STEP_SRC: Local.racy_read_step lc1_src mem1_src loc to val ord_src>>.
Proof.
  inv STEP_TGT.
  exploit sim_local_is_racy_relfenced; eauto.
Qed.

Lemma sim_local_racy_write_relfenced
      pview
      lc1_src mem1_src
      lc1_tgt mem1_tgt
      loc to ord_src ord_tgt
      (STEP_TGT: Local.racy_write_step lc1_tgt mem1_tgt loc to ord_tgt)
      (LOCAL1: sim_local pview lc1_src (local_relfenced lc1_tgt))
      (MEM1: sim_memory mem1_src mem1_tgt)
      (ORD: Ordering.le ord_src ord_tgt):
    <<STEP_SRC: Local.racy_write_step lc1_src mem1_src loc to ord_src>>.
Proof.
  inv STEP_TGT.
  exploit sim_local_is_racy_relfenced; eauto. i. des.
  econs; eauto.
  eapply sim_local_promise_consistent; try apply LOCAL1.
  ii. ss. eapply CONSISTENT; eauto.
Qed.

Lemma sim_local_racy_update_relfenced
      pview
      lc1_src mem1_src
      lc1_tgt mem1_tgt
      loc to ordr_src ordw_src ordr_tgt ordw_tgt
      (STEP_TGT: Local.racy_update_step lc1_tgt mem1_tgt loc to ordr_tgt ordw_tgt)
      (LOCAL1: sim_local pview lc1_src (local_relfenced lc1_tgt))
      (MEM1: sim_memory mem1_src mem1_tgt)
      (ORDR: Ordering.le ordr_src ordr_tgt)
      (ORDW: Ordering.le ordw_src ordw_tgt):
    <<STEP_SRC: Local.racy_update_step lc1_src mem1_src loc to ordr_src ordw_src>>.
Proof.
  hexploit sim_local_promise_consistent; try exact LOCAL1.
  { ii. ss. inv STEP_TGT; eauto. }
  i. des.
  inv STEP_TGT; eauto.
  exploit sim_local_is_racy_relfenced; eauto.
Qed.

Lemma sim_local_intro_relfenced
      pview
      lc1_src sc1_src mem1_src
      lc1_tgt sc1_tgt mem1_tgt
      (LOCAL1: sim_local pview lc1_src lc1_tgt)
      (SC1: TimeMap.le sc1_src sc1_tgt)
      (MEM1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt):
  <<LOCAL2: sim_local pview lc1_src (local_relfenced lc1_tgt)>>.
Proof.
  esplits. inv LOCAL1. econs; eauto.
  inv TVIEW. econs; ss; eauto.
  etrans; eauto. apply WF1_TGT.
Qed.

Lemma sim_local_fence_src_relfenced
      pview
      lc1_src sc1_src mem1_src
      lc1_tgt sc1_tgt mem1_tgt
      (NONSYNCH: Memory.nonsynch (Local.promises lc1_src))
      (LOCAL1: sim_local pview lc1_src (local_relfenced lc1_tgt))
      (SC1: TimeMap.le sc1_src sc1_tgt)
      (MEM1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt):
  exists lc2_src sc2_src,
    <<STEP_SRC: Local.fence_step lc1_src sc1_src Ordering.plain Ordering.acqrel lc2_src sc2_src>> /\
    <<LOCAL2: sim_local pview lc2_src (local_relfenced lc1_tgt)>> /\
    <<SC2: TimeMap.le sc2_src sc1_tgt>>.
Proof.
  inv LOCAL1. inv TVIEW. ss.
  esplits; eauto.
  - econs; eauto. i. ss.
  - econs; eauto. econs; ss; eauto.
    repeat (condtac; aggrtac).
Qed.

Lemma sim_local_fence_tgt_relfenced
      pview
      lc1_src sc1_src mem1_src
      lc1_tgt sc1_tgt mem1_tgt
      lc2_tgt sc2_tgt
      (STEP_TGT: Local.fence_step lc1_tgt sc1_tgt Ordering.plain Ordering.acqrel lc2_tgt sc2_tgt)
      (LOCAL1: sim_local pview lc1_src (local_relfenced lc1_tgt))
      (SC1: TimeMap.le sc1_src sc1_tgt)
      (MEM1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt):
  <<LOCAL2: sim_local SimPromises.bot lc1_src lc2_tgt>> /\
  <<SC2: TimeMap.le sc1_src sc2_tgt>>.
Proof.
  inv LOCAL1. inv TVIEW. inv STEP_TGT. esplits; ss.
  econs; s.
  - unfold TView.read_fence_tview. condtac; ss.
    unfold TView.write_fence_tview. econs; repeat (condtac; aggrtac).
  - econs; try by apply PROMISES.
    + inv PROMISES. ii. exploit LE; eauto.
      SimPromises.none_if_tac.
      exploit RELEASE; eauto. s. i. subst. ss.
    + i. rewrite SimPromises.bot_spec in *. congr.
Qed.
