Require Import Omega.
Require Import Bool.
Require Import RelationClasses.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
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

Require Import SimMemory.
Require Import MemoryProps.
Require Import JoinedView.
Require Import JoinedViewExist.

Set Implicit Arguments.


Lemma read_tview_plain_cur
      tview loc to released ord
      (WF: TView.wf tview)
      (ORD: Ordering.le ord Ordering.plain)
      (CUR: Time.le to ((View.rlx (TView.cur tview)) loc)):
  TView.read_tview tview loc to released ord = tview.
Proof.
  unfold TView.read_tview. destruct tview. ss. f_equal.
  { condtac; try by destruct ord; ss.
    rewrite View.join_bot_r.
    apply View.antisym; try apply View.join_l.
    apply View.join_spec; try refl.
    unfold View.singleton_ur_if.
    condtac; try by destruct ord; ss.
    unfold View.singleton_rw.
    econs; try apply TimeMap.bot_spec. ss.
    ii. unfold TimeMap.singleton, LocFun.add, LocFun.init, LocFun.find.
    condtac; try apply Time.bot_spec.
    subst. ss.
  }
  { condtac; try by destruct ord; ss.
    rewrite View.join_bot_r.
    apply View.antisym; try apply View.join_l.
    apply View.join_spec; try refl.
    unfold View.singleton_ur_if.
    unfold View.singleton_rw.
    econs; try apply TimeMap.bot_spec. ss.
    ii. unfold TimeMap.singleton, LocFun.add, LocFun.init, LocFun.find.
    condtac; try apply Time.bot_spec.
    subst. etrans; eauto. apply WF.
  }
Qed.

Lemma read_step_plain_cur
      lc1 mem1 loc to val released ord lc2
      (WF: TView.wf (Local.tview lc1))
      (ORD: Ordering.le ord Ordering.plain)
      (CUR: Time.le to ((View.rlx (TView.cur (Local.tview lc1))) loc))
      (STEP: Local.read_step lc1 mem1 loc to val released ord lc2):
  lc2 = lc1.
Proof.
  destruct lc1. inv STEP; ss. f_equal.
  eapply read_tview_plain_cur; eauto.
Qed.

Lemma sim_local_read_na_aux
      views
      lc1_src mem1_src
      lc1_tgt mem1_tgt
      lc2_tgt
      loc ts val released_tgt ord_src ord_tgt
      (STEP_TGT: Local.read_step lc1_tgt mem1_tgt loc ts val released_tgt ord_tgt lc2_tgt)
      (LOCAL1: JSim.sim_local views lc1_src lc1_tgt)
      (MEM1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (ORD: Ordering.le ord_src ord_tgt)
      (NA: Ordering.le ord_src Ordering.na)
      (CONS: Local.promise_consistent lc2_tgt)
  :
    (exists released_src lc2_src,
        (<<REL: View.opt_le released_src released_tgt>>) /\
        (<<STEP_SRC: Local.read_step lc1_src mem1_src loc ts val released_src ord_src lc2_src>>) /\
        (<<CUR: Time.le ts ((View.rlx (TView.cur (Local.tview lc1_src))) loc)>>)) \/
    (<<STEP_SRC: Local.racy_read_step lc1_src mem1_src loc ts val ord_src>>).
Proof.
  inv LOCAL1. inv STEP_TGT.
  exploit sim_memory_get; try apply GET; eauto. i. des. inv MSG. ss.
  destruct (TimeFacts.le_lt_dec ts ((View.rlx (TView.cur vw_src)) loc)).
  { left. esplits.
    - eauto.
    - econs; eauto.
      { etrans; eauto. }
      eapply TViewFacts.readable_mon; try exact READABLE; eauto. apply TVIEW.
    - ss.
  }
  { right. econs. econs; try exact GET0; ss.
    - destruct (Memory.get loc ts prom_src) as [[]|] eqn:GETP; ss.
      inv WF1_SRC. ss.
      exploit PROMISES0; eauto. i.
      rewrite x in *. inv GET0.
      specialize (PROMISES loc ts).
      rewrite GETP in *. inv PROMISES. clear NIL.
      exploit CONS; eauto; ss. i.
      exfalso.
      eapply Time.lt_strorder.
      eapply TimeFacts.le_lt_lt; try eapply x0.
      etrans; [|eapply Time.join_l].
      etrans; [|eapply Time.join_r].
      unfold View.singleton_ur_if. condtac; ss.
      + unfold TimeMap.singleton, LocFun.add. condtac; ss. refl.
      + unfold TimeMap.singleton, LocFun.add. condtac; ss. refl.
    - unfold TView.racy_view.
      eapply TimeFacts.le_lt_lt; eauto. apply WF1_SRC.
    - destruct ord_src; ss.
  }
Qed.

Lemma sim_local_read_na
      views
      lc1_src mem1_src
      lc1_tgt mem1_tgt
      lc2_tgt
      loc ts val released_tgt ord_src ord_tgt
      (STEP_TGT: Local.read_step lc1_tgt mem1_tgt loc ts val released_tgt ord_tgt lc2_tgt)
      (LOCAL1: JSim.sim_local views lc1_src lc1_tgt)
      (MEM1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (ORD: Ordering.le ord_src ord_tgt)
      (NA: Ordering.le ord_src Ordering.na)
      (CONS: Local.promise_consistent lc2_tgt)
  :
    (exists released_src lc2_src,
        (<<REL: View.opt_le released_src released_tgt>>) /\
        (<<STEP_SRC: Local.read_step lc1_src mem1_src loc ts val released_src ord_src lc2_src>>) /\
        (<<LC: lc2_src = lc1_src>>)) \/
    (<<STEP_SRC: Local.racy_read_step lc1_src mem1_src loc ts val ord_src>>).
Proof.
  exploit sim_local_read_na_aux; eauto. i. des; eauto.
  exploit read_step_plain_cur;
    try exact STEP_SRC; try apply WF1_SRC; eauto. i. subst.
  left. esplits; eauto.
Qed.
