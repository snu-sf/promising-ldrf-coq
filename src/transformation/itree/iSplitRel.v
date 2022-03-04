From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Basic.
From PromisingLib Require Import Loc.
From PromisingLib Require Import Language.

From PromisingLib Require Import Event.
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
Require Import iCompatibility.
Require Import SplitRelCommon.

Require Import ITreeLang.

Set Implicit Arguments.


Inductive split_release: forall R (i1: MemE.t R) (i2: MemE.t R), Prop :=
| split_release_store
    l v:
    split_release (MemE.write l v Ordering.acqrel) (MemE.write l v Ordering.strong_relaxed)
| split_release_update
    l rmw or
    (OR: Ordering.le or Ordering.strong_relaxed):
    split_release (MemE.update l rmw or Ordering.acqrel) (MemE.update l rmw or Ordering.strong_relaxed)
.

Inductive sim_released: forall R
                               (st_src:(Language.state (lang R))) (lc_src:Local.t) (sc1_src:TimeMap.t) (mem1_src:Memory.t)
                               (st_tgt:(Language.state (lang R))) (lc_tgt:Local.t) (sc1_tgt:TimeMap.t) (mem1_tgt:Memory.t), Prop :=
| sim_released_intro
    R
    (i_src i_tgt: MemE.t R)
    lc1_src sc1_src mem1_src
    lc1_tgt sc1_tgt mem1_tgt
    (SPLIT: split_release i_src i_tgt)
    (LOCAL: sim_local SimPromises.bot lc1_src lc1_tgt)
    (RELEASED: forall l, View.le (TView.cur (Local.tview lc1_tgt)) ((TView.rel (Local.tview lc1_tgt)) l))
    (SC: TimeMap.le sc1_src sc1_tgt)
    (MEMORY: sim_memory mem1_src mem1_tgt)
    (WF_SRC: Local.wf lc1_src mem1_src)
    (WF_TGT: Local.wf lc1_tgt mem1_tgt)
    (SC_SRC: Memory.closed_timemap sc1_src mem1_src)
    (SC_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
    (MEM_SRC: Memory.closed mem1_src)
    (MEM_TGT: Memory.closed mem1_tgt):
    sim_released
      (Vis i_src (fun r => Ret r)) lc1_src sc1_src mem1_src
      (Vis i_tgt (fun r => Ret r)) lc1_tgt sc1_tgt mem1_tgt
.

Lemma sim_released_mon
      R
      st_src lc_src sc1_src mem1_src
      st_tgt lc_tgt sc1_tgt mem1_tgt
      sc2_src mem2_src
      sc2_tgt mem2_tgt
      (SIM1: sim_released st_src lc_src sc1_src mem1_src
                          st_tgt lc_tgt sc1_tgt mem1_tgt)
      (SC_FUTURE_SRC: TimeMap.le sc1_src sc2_src)
      (SC_FUTURE_TGT: TimeMap.le sc1_tgt sc2_tgt)
      (MEM_FUTURE_SRC: Memory.future_weak mem1_src mem2_src)
      (MEM_FUTURE_TGT: Memory.future_weak mem1_tgt mem2_tgt)
      (SC1: TimeMap.le sc2_src sc2_tgt)
      (MEM1: sim_memory mem2_src mem2_tgt)
      (WF_SRC: Local.wf lc_src mem2_src)
      (WF_TGT: Local.wf lc_tgt mem2_tgt)
      (SC_SRC: Memory.closed_timemap sc2_src mem2_src)
      (SC_TGT: Memory.closed_timemap sc2_tgt mem2_tgt)
      (MEM_SRC: Memory.closed mem2_src)
      (MEM_TGT: Memory.closed mem2_tgt):
  @sim_released R
                st_src lc_src sc2_src mem2_src
                st_tgt lc_tgt sc2_tgt mem2_tgt.
Proof.
  destruct SIM1. econs; eauto.
Qed.

Lemma sim_released_step R
      st1_src lc1_src sc1_src mem1_src
      st1_tgt lc1_tgt sc1_tgt mem1_tgt
      (SIM: @sim_released R
                          st1_src lc1_src sc1_src mem1_src
                          st1_tgt lc1_tgt sc1_tgt mem1_tgt):
  _sim_thread_step (lang R) (lang R)
                   ((@sim_thread (lang R) (lang R) (sim_terminal eq)) \8/ @sim_released R)
                   st1_src lc1_src sc1_src mem1_src
                   st1_tgt lc1_tgt sc1_tgt mem1_tgt.
Proof.
  destruct SIM. ii.
  inv STEP_TGT; [inv STEP|dependent destruction STEP; inv LOCAL0; ss; dependent destruction STATE; inv SPLIT]; ss.
  - (* promise *)
    right.
    exploit Local.promise_step_future; eauto. i. des.
    exploit sim_local_promise; eauto. i. des.
    exploit Local.promise_step_future; eauto. i. des.
    esplits; try apply SC; eauto; ss.
    + econs 2. econs. econs; eauto.
    + eauto.
    + right. econs; eauto.
      inv LOCAL0. ss.
  - dependent destruction H.
    (* update-load *)
    right.
    exploit sim_local_read; (try by etrans; eauto); eauto; try refl. i. des.
    esplits; eauto; ss.
    + econs 2. econs 2. econs; [|econs 2]; eauto. econs; eauto.
    + eauto.
    + left. eapply paco11_mon; [apply sim_itree_ret|]; ss.
  - dependent destruction H.
    (* write *)
    right.
    hexploit sim_local_write_released; (try by etrans; eauto); eauto; try refl; try by econs.
    { by rewrite <- View.join_l. }
    i. des.
    esplits; eauto; ss.
    + econs 2. econs 2. econs; [|econs 3]; eauto. econs. econs.
    + ss.
    + left. eapply paco11_mon; [apply sim_itree_ret|]; ss.
  - dependent destruction H.
    (* update *)
    right.
    exploit Local.read_step_future; eauto. i. des.
    exploit sim_local_read; (try by etrans; eauto); eauto; try refl; try by econs. i. des.
    exploit Local.read_step_future; eauto. i. des.
    hexploit sim_local_write_released; (try by etrans; eauto); eauto; try refl; try by econs.
    { assert (TS: Time.lt tsr tsw).
      { inv LOCAL2. eapply MemoryFacts.MemoryFacts.write_time_lt. eauto. }
      inv LOCAL1. ss. repeat (condtac; aggrtac); try by apply WF_TGT.
      destruct ordr; ss.
    }
    i. des.
    esplits; eauto; ss.
    + econs 2. econs 2. econs; [|econs 4]; eauto. econs; eauto.
    + ss.
    + left. eapply paco11_mon; [apply sim_itree_ret|]; ss.
  - (* na write *)
    inv LOCAL1. inv ORD.
  - (* racy read *)
    right.
    dependent destruction H.
    exploit sim_local_racy_read; try exact LOCAL1; eauto; try refl. i. des.
    esplits; try apply SC; eauto; ss.
    + econs 2. econs 2. econs; [|econs 9]; eauto. econs; eauto.
    + ss.
    + left. eapply paco11_mon; [apply sim_itree_ret|]; ss.
  - (* racy write *)
    left.
    dependent destruction H.
    exploit sim_local_racy_write_released; try exact LOCAL1; eauto. i. des.
    unfold Thread.steps_failure.
    esplits; try refl.
    + econs 2. econs; [|econs 10]; eauto. econs; eauto.
    + ss.
  - (* racy update *)
    left.
    dependent destruction H.
    exploit sim_local_racy_update_released; try exact LOCAL1; eauto. i. des.
    unfold Thread.steps_failure.
    esplits; try refl.
    + econs 2. econs; [|econs 11]; eauto. econs; eauto.
    + ss.
Qed.

Lemma sim_released_sim_thread R:
  @sim_released R <8= @sim_thread (lang R) (lang R) (sim_terminal eq).
Proof.
  pcofix CIH. i. pfold. ii. ss. splits; ss; ii.
  - inv TERMINAL_TGT. inv PR; ss.
  - right. esplits; eauto.
    inv PR. eapply sim_local_memory_bot; eauto.
  - exploit sim_released_mon; eauto. i.
    exploit sim_released_step; eauto. i. des; eauto.
    + right. esplits; eauto.
      left. eapply paco11_mon; eauto. ss.
    + right. esplits; eauto.
Qed.

Lemma split_release_sim_itree R
      (i_src i_tgt: MemE.t R)
      (SPLIT: split_release i_src i_tgt):
  sim_itree eq
            (ITree.trigger i_src)
            (ITree.trigger (MemE.fence Ordering.plain Ordering.acqrel);; ITree.trigger i_tgt).
Proof.
  replace (ITree.trigger i_src) with (Vis i_src (fun r => Ret r)).
  2: { unfold ITree.trigger. grind. }
  replace (ITree.trigger (MemE.fence Ordering.plain Ordering.acqrel);; ITree.trigger i_tgt) with
      (Vis (MemE.fence Ordering.plain Ordering.acqrel) (fun _ => Vis i_tgt (fun r => Ret r))).
  2: { unfold ITree.trigger. grind. repeat f_equal. extensionality u. grind. }
  pcofix CIH. ii. subst. pfold. ii. splits; ii.
  { inv TERMINAL_TGT. eapply f_equal with (f:=observe) in H; ss. }
  { right. esplits; eauto.
    inv LOCAL. apply SimPromises.sem_bot_inv in PROMISES; auto. rewrite PROMISES. auto.
  }
  right.
  inv STEP_TGT; [inv STEP|dependent destruction STEP; inv LOCAL0; ss; dependent destruction STATE]; ss.
  - (* promise *)
    exploit sim_local_promise; eauto. i. des.
    esplits; try apply SC; eauto; ss.
    econs 2. econs 1; eauto. econs; eauto. eauto.
  - (* fence *)
    exploit Local.fence_step_future; eauto. i. des.
    esplits.
    + ss.
    + eauto.
    + econs 1.
    + ss.
    + inv LOCAL1. ss.
    + ss.
    + left. eapply paco11_mon; [apply sim_released_sim_thread|]; ss.
      inv LOCAL1. econs; eauto.
      * inv LOCAL. econs; ss. etrans; eauto.
      * s. i. repeat condtac; ss. refl.
Qed.
