From sflib Require Import sflib.
From Paco Require Import paco.

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

Require Import FulfillStep.

Require Import SimMemory.
Require Import SimPromises.
Require Import SimLocal.
Require Import SimThread.

Set Implicit Arguments.


Definition local_acquired (lc:Local.t) :=
  (Local.mk (TView.read_fence_tview (Local.tview lc) Ordering.acqrel) (Local.promises lc)).

Lemma sim_local_promise_acquired
      lc1_src mem1_src
      lc1_tgt mem1_tgt
      lc2_tgt mem2_tgt
      loc from to msg kind
      (STEP_TGT: Local.promise_step lc1_tgt mem1_tgt loc from to msg lc2_tgt mem2_tgt kind)
      (LOCAL1: sim_local SimPromises.bot lc1_src (local_acquired lc1_tgt))
      (MEM1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
      (MEM1_SRC: Memory.closed mem1_src)
      (MEM1_TGT: Memory.closed mem1_tgt):
  exists lc2_src mem2_src,
    <<STEP_SRC: Local.promise_step lc1_src mem1_src loc from to msg lc2_src mem2_src kind>> /\
    <<LOCAL2: sim_local SimPromises.bot lc2_src (local_acquired lc2_tgt)>> /\
    <<MEM2: sim_memory mem2_src mem2_tgt>>.
Proof.
  inv LOCAL1. inv STEP_TGT.
  exploit SimPromises.promise_bot; eauto.
  { apply WF1_SRC. }
  { apply WF1_TGT. }
  i. des.
  exploit Memory.promise_future; try apply PROMISE_SRC; try apply WF1_SRC; eauto.
  { destruct msg; ss. inv CLOSED. econs.
    eapply sim_memory_closed_opt_view; eauto. }
  i. des.
  esplits; eauto.
  - econs; eauto.
    destruct msg; ss. inv CLOSED. econs.
    eapply sim_memory_closed_opt_view; eauto.
  - econs; eauto.
Qed.

Lemma sim_local_fulfill_acquired
      lc1_src sc1_src mem1_src
      lc1_tgt sc1_tgt mem1_tgt
      lc2_tgt sc2_tgt
      loc from to val releasedm_src releasedm_tgt released ord_src ord_tgt
      (RELM_LE: View.opt_le releasedm_src releasedm_tgt)
      (RELM_WF: View.opt_wf releasedm_src)
      (RELM_CLOSED: Memory.closed_opt_view releasedm_src mem1_src)
      (RELM_TGT: Time.le (View.rlx (View.unwrap releasedm_tgt) loc) from)
      (WF_RELM_TGT: View.opt_wf releasedm_tgt)
      (ORD: Ordering.le ord_src ord_tgt)
      (ORD_TGT: Ordering.le ord_tgt Ordering.strong_relaxed)
      (STEP_TGT: fulfill_step lc1_tgt sc1_tgt loc from to val releasedm_tgt released ord_tgt lc2_tgt sc2_tgt)
      (LOCAL1: sim_local SimPromises.bot lc1_src (local_acquired lc1_tgt))
      (ACQUIRED1: View.le (TView.cur (Local.tview lc1_src))
                          (View.join (TView.cur (Local.tview lc1_tgt)) (View.unwrap releasedm_tgt)))
      (SC1: TimeMap.le sc1_src sc1_tgt)
      (MEM1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
      (SC1_SRC: Memory.closed_timemap sc1_src mem1_src)
      (SC1_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
      (MEM1_SRC: Memory.closed mem1_src)
      (MEM1_TGT: Memory.closed mem1_tgt):
  exists lc2_src sc2_src,
    <<STEP_SRC: fulfill_step lc1_src sc1_src loc from to val releasedm_src released ord_src lc2_src sc2_src>> /\
    <<LOCAL2: sim_local SimPromises.bot lc2_src (local_acquired lc2_tgt)>> /\
    <<SC2: TimeMap.le sc2_src sc2_tgt>>.
Proof.
  inv STEP_TGT.
  assert (RELT_LE:
   View.opt_le
     (TView.write_released (Local.tview lc1_src) sc1_src loc to releasedm_src ord_src)
     (TView.write_released (Local.tview lc1_tgt) sc2_tgt loc to releasedm_tgt ord_tgt)).
  { unfold TView.write_released, TView.write_tview. ss. viewtac.
    repeat (condtac; aggrtac;
            try match goal with
                | [|- View.opt_le _ _] => econs
                end);
      try apply WF1_TGT.
    - etrans; eauto. aggrtac.
    - etrans; [apply WF1_SRC|]. etrans; eauto. aggrtac.
    - etrans; [apply LOCAL1|]. aggrtac.
  }
  assert (RELT_WF:
   View.opt_wf (TView.write_released (Local.tview lc1_src) sc1_src loc to releasedm_src ord_src)).
  { unfold TView.write_released. condtac; econs.
    repeat (try condtac; viewtac; try apply WF1_SRC).
  }
  exploit SimPromises.remove_bot; try exact REMOVE;
    try exact MEM1; try apply LOCAL1; eauto.
  i. des. esplits.
  - econs; eauto.
    inv WRITABLE. econs.
    eapply TimeFacts.le_lt_lt; [apply ACQUIRED1|]. viewtac.
    eapply TimeFacts.le_lt_lt; eauto.
  - econs; eauto. s. unfold TView.write_tview, TView.read_fence_tview. ss.
    econs; ss; repeat (try condtac; aggrtac).
    all: try by destruct ord_src, ord_tgt.
    all: try by apply WF1_TGT.
    + etrans; [apply LOCAL1|]. aggrtac.
    + etrans; [apply LOCAL1|]. aggrtac.
    + etrans; [apply WF1_SRC|]. etrans; [apply LOCAL1|]. aggrtac.
    + etrans; [apply LOCAL1|]. aggrtac.
  - ss.
Qed.

Lemma sim_local_write_acquired
      lc1_src sc1_src mem1_src
      lc1_tgt sc1_tgt mem1_tgt
      lc2_tgt sc2_tgt mem2_tgt
      loc from to val releasedm_src releasedm_tgt released_tgt ord_src ord_tgt kind
      (RELM_LE: View.opt_le releasedm_src releasedm_tgt)
      (RELM_SRC_WF: View.opt_wf releasedm_src)
      (RELM_SRC_CLOSED: Memory.closed_opt_view releasedm_src mem1_src)
      (RELM_TGT_WF: View.opt_wf releasedm_tgt)
      (RELM_TGT_CLOSED: Memory.closed_opt_view releasedm_tgt mem1_tgt)
      (RELM_TGT: Time.le (View.rlx (View.unwrap releasedm_tgt) loc) from)
      (ORD: Ordering.le ord_src ord_tgt)
      (ORD_TGT: Ordering.le ord_tgt Ordering.strong_relaxed)
      (STEP_TGT: Local.write_step lc1_tgt sc1_tgt mem1_tgt loc from to val releasedm_tgt released_tgt ord_tgt lc2_tgt sc2_tgt mem2_tgt kind)
      (LOCAL1: sim_local SimPromises.bot lc1_src (local_acquired lc1_tgt))
      (ACQUIRED1: View.le (TView.cur (Local.tview lc1_src))
                          (View.join (TView.cur (Local.tview lc1_tgt)) (View.unwrap releasedm_tgt)))
      (SC1: TimeMap.le sc1_src sc1_tgt)
      (MEM1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
      (SC1_SRC: Memory.closed_timemap sc1_src mem1_src)
      (SC1_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
      (MEM1_SRC: Memory.closed mem1_src)
      (MEM1_TGT: Memory.closed mem1_tgt):
  exists released_src lc2_src sc2_src mem2_src,
    <<STEP_SRC: Local.write_step lc1_src sc1_src mem1_src loc from to val releasedm_src released_src ord_src lc2_src sc2_src mem2_src kind>> /\
    <<REL2: View.opt_le released_src released_tgt>> /\
    <<LOCAL2: sim_local SimPromises.bot lc2_src (local_acquired lc2_tgt)>> /\
    <<SC2: TimeMap.le sc2_src sc2_tgt>> /\
    <<MEM2: sim_memory mem2_src mem2_tgt>>.
Proof.
  exploit write_promise_fulfill; eauto. i. des.
  exploit Local.promise_step_future; eauto. i. des.
  exploit sim_local_promise_acquired; eauto. i. des.
  exploit Local.promise_step_future; eauto. i. des.
  hexploit sim_local_fulfill_acquired; try apply STEP2;
    try apply LOCAL2; try apply MEM2; eauto.
  { eapply Memory.future_closed_opt_view; eauto. }
  { inv STEP_SRC. inv STEP1. ss. }
  i. des.
  exploit promise_fulfill_write_sim_memory; try exact STEP_SRC; try exact STEP_SRC0; eauto.
  { i. hexploit ORD0; eauto.
    i. des. splits; auto. eapply sim_local_nonsynch_loc; eauto.
  }
  i. des. esplits; eauto. etrans; eauto.
Qed.

Lemma sim_local_read_acquired
      lc1_src mem1_src
      lc1_tgt mem1_tgt
      lc2_tgt
      loc ts val released_tgt
      (STEP_TGT: Local.read_step lc1_tgt mem1_tgt loc ts val released_tgt Ordering.relaxed lc2_tgt)
      (LOCAL1: sim_local SimPromises.bot lc1_src lc1_tgt)
      (MEM1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
      (MEM1_SRC: Memory.closed mem1_src)
      (MEM1_TGT: Memory.closed mem1_tgt):
  exists released_src lc2_src,
    <<REL: View.opt_le released_src released_tgt>> /\
    <<STEP_SRC: Local.read_step lc1_src mem1_src loc ts val released_src Ordering.acqrel lc2_src>> /\
    <<LOCAL2: sim_local SimPromises.bot lc2_src (local_acquired lc2_tgt)>>.
Proof.
  inv LOCAL1. inv STEP_TGT.
  exploit sim_memory_get; try apply GET; try apply MEM1. i. des. inv MSG.
  esplits; eauto.
  - econs; eauto; try by (etrans; eauto). inv READABLE. econs; ss; i.
    + rewrite <- PLN. apply TVIEW.
    + rewrite <- RLX; ss. apply TVIEW.
  - econs; eauto. s.
    unfold TView.read_tview, TView.read_fence_tview. ss.
    econs; repeat (condtac; aggrtac).
    all: try by apply TVIEW.
    all: try by apply WF1_TGT.
    + rewrite <- ? View.join_l. etrans; [apply TVIEW|]. apply WF1_TGT.
    + inv MEM1_TGT. exploit CLOSED; eauto. i. des.
      apply View.unwrap_opt_wf. inv MSG_WF. ss.
    + rewrite <- ? View.join_l. apply TVIEW.
    + inv MEM1_TGT. exploit CLOSED; eauto. i. des.
      apply View.unwrap_opt_wf. inv MSG_WF. ss.
Qed.

Lemma sim_local_is_racy_acquired
      lc1_src mem1_src
      lc1_tgt mem1_tgt
      loc to
      (STEP_TGT: Local.is_racy lc1_tgt mem1_tgt loc to Ordering.relaxed)
      (LOCAL1: sim_local SimPromises.bot lc1_src lc1_tgt)
      (MEM1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
      (MEM1_SRC: Memory.closed mem1_src)
      (MEM1_TGT: Memory.closed mem1_tgt):
  <<STEP_SRC: Local.is_racy lc1_src mem1_src loc to Ordering.acqrel>>.
Proof.
  exploit sim_local_is_racy; try exact STEP_TGT;
    try exact LOCAL1; try exact MEM1; try refl; eauto. i. des.
  inv x0. econs; eauto.
Qed.

Lemma sim_local_racy_read_acquired
      lc1_src mem1_src
      lc1_tgt mem1_tgt
      loc to val
      (STEP_TGT: Local.racy_read_step lc1_tgt mem1_tgt loc to val Ordering.relaxed)
      (LOCAL1: sim_local SimPromises.bot lc1_src lc1_tgt)
      (MEM1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
      (MEM1_SRC: Memory.closed mem1_src)
      (MEM1_TGT: Memory.closed mem1_tgt):
  <<STEP_SRC: Local.racy_read_step lc1_src mem1_src loc to val Ordering.acqrel>>.
Proof.
  inv STEP_TGT.
  exploit sim_local_is_racy_acquired; eauto.
Qed.

Lemma sim_local_racy_update_acquired
      lc1_src mem1_src
      lc1_tgt mem1_tgt
      loc to ow
      (STEP_TGT: Local.racy_update_step lc1_tgt mem1_tgt loc to Ordering.relaxed ow)
      (LOCAL1: sim_local SimPromises.bot lc1_src lc1_tgt)
      (MEM1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
      (MEM1_SRC: Memory.closed mem1_src)
      (MEM1_TGT: Memory.closed mem1_tgt):
  <<STEP_SRC: Local.racy_update_step lc1_src mem1_src loc to Ordering.acqrel ow>>.
Proof.
  exploit sim_local_racy_update; try exact STEP_TGT;
    try exact LOCAL1; try exact MEM1; try refl; eauto. i. des.
  inv x0.
  - econs 1; eauto.
  - econs 2; eauto.
  - econs 3; eauto.
    inv RACE. econs; eauto.
Qed.
