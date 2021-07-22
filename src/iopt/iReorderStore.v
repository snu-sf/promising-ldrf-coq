From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Basic.
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

Require Import FulfillStep.

Require Import SimMemory.
Require Import SimPromises.
Require Import SimLocal.
Require Import SimThread.
Require Import iCompatibility.

Require Import ReorderStep.
Require Import iProgressStep.

Require Import ITreeLang.
Require Import Program.

Set Implicit Arguments.


Inductive reorder_store l1 o1: forall R (i2:MemE.t R), Prop :=
| reorder_store_load
    l2 o2
    (ORD1: Ordering.le o1 Ordering.relaxed)
    (ORD2: Ordering.le o2 Ordering.relaxed)
    (LOC: l1 <> l2):
    reorder_store l1 o1 (MemE.read l2 o2)
| reorder_store_store
    l2 v2 o2
    (ORD1: Ordering.le o1 Ordering.relaxed)
    (LOC: l1 <> l2):
    reorder_store l1 o1 (MemE.write l2 v2 o2)
.

Inductive sim_store: forall R
                            (st_src:itree MemE.t (unit * R)%type) (lc_src:Local.t) (sc1_src:TimeMap.t) (mem1_src:Memory.t)
                            (st_tgt:itree MemE.t (unit * R)%type) (lc_tgt:Local.t) (sc1_tgt:TimeMap.t) (mem1_tgt:Memory.t), Prop :=
| sim_store_intro
    R
    l1 f1 t1 v1 released1 o1 (i2: MemE.t R)
    lc1_src sc1_src mem1_src
    lc1_tgt sc1_tgt mem1_tgt
    lc2_src sc2_src
    (REORDER: reorder_store l1 o1 i2)
    (FULFILL: fulfill_step lc1_src sc1_src l1 f1 t1 v1 None released1 o1 lc2_src sc2_src)
    (LOCAL: sim_local SimPromises.bot lc2_src lc1_tgt)
    (SC: TimeMap.le sc2_src sc1_tgt)
    (MEMORY: sim_memory mem1_src mem1_tgt)
    (WF_SRC: Local.wf lc1_src mem1_src)
    (WF_TGT: Local.wf lc1_tgt mem1_tgt)
    (SC_SRC: Memory.closed_timemap sc1_src mem1_src)
    (SC_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
    (MEM_SRC: Memory.closed mem1_src)
    (MEM_TGT: Memory.closed mem1_tgt):
    sim_store
      (Vis i2 (fun v2 => Vis (MemE.write l1 v1 o1) (fun v1 => Ret (v1, v2)))) lc1_src sc1_src mem1_src
      (Vis i2 (fun r => Ret (tt, r))) lc1_tgt sc1_tgt mem1_tgt
.

Lemma sim_store_mon
      R
      st_src lc_src sc1_src mem1_src
      st_tgt lc_tgt sc1_tgt mem1_tgt
      sc2_src mem2_src
      sc2_tgt mem2_tgt
      (SIM1: sim_store st_src lc_src sc1_src mem1_src
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
  @sim_store R
             st_src lc_src sc2_src mem2_src
             st_tgt lc_tgt sc2_tgt mem2_tgt.
Proof.
  dependent destruction SIM1. exploit future_fulfill_step; try exact FULFILL; eauto; try refl.
  i. des. econs; eauto.
Qed.

Lemma sim_store_step
      R
      st1_src lc1_src sc1_src mem1_src
      st1_tgt lc1_tgt sc1_tgt mem1_tgt
      (SIM: sim_store st1_src lc1_src sc1_src mem1_src
                      st1_tgt lc1_tgt sc1_tgt mem1_tgt):
  _sim_thread_step (lang (unit * R)%type) (lang (unit * R)%type)
                   ((@sim_thread (lang (unit * R)%type) (lang (unit * R)%type) (sim_terminal eq)) \8/ @sim_store R)
                   st1_src lc1_src sc1_src mem1_src
                   st1_tgt lc1_tgt sc1_tgt mem1_tgt.
Proof.
  dependent destruction SIM. ii. right.
  exploit fulfill_step_future; eauto; try viewtac. i. des.
  inv STEP_TGT; [inv STEP|dependent destruction STEP; inv LOCAL0; ss; dependent destruction STATE; inv REORDER].
  - (* promise *)
    exploit Local.promise_step_future; eauto. i. des.
    exploit sim_local_promise; try exact LOCAL0; (try by etrans; eauto); eauto. i. des.
    exploit reorder_fulfill_promise; try exact FULFILL; try exact STEP_SRC; eauto. i. des.
    exploit Local.promise_step_future; eauto. i. des.
    esplits.
    + ss.
    + eauto.
    + econs 2. econs 1. econs; eauto.
    + auto.
    + etrans; eauto.
    + auto.
    + right. econs; eauto.
      eapply Memory.future_closed_timemap; eauto.
  - (* load *)
    exploit sim_local_read; try exact LOCAL0; (try by etrans; eauto); eauto; try refl. i. des.
    exploit reorder_fulfill_read; try exact FULFILL; try exact STEP_SRC; eauto. i. des.
    exploit Local.read_step_future; try exact STEP1; eauto. i. des.
    exploit fulfill_write_sim_memory; eauto; try by viewtac. i. des.
    esplits.
    + ss.
    + econs 2; eauto. econs.
      * econs. econs 2. econs; [|econs 2]; eauto. econs. econs.
      * auto.
    + econs 2. econs 2. econs; [|econs 3]; eauto. econs; eauto.
    + auto.
    + auto.
    + etrans; eauto.
    + left. eapply paco11_mon; [apply sim_itree_ret|]; ss.
  - (* store *)
    hexploit sim_local_write_bot; try exact LOCAL1; eauto; try refl; try by viewtac. i. des.
    hexploit reorder_fulfill_write_sim_memory; try exact FULFILL; try exact STEP_SRC; eauto; try by viewtac. i. des.
    exploit Local.write_step_future; try exact STEP1; eauto; try by viewtac. i. des.
    exploit fulfill_write_sim_memory; eauto; try by viewtac. i. des.
    esplits.
    + ss.
    + econs 2; eauto. econs.
      * econs. econs 2. econs; [|econs 3]; eauto. econs. econs.
      * auto.
    + econs 2. econs 2. econs; [|econs 3]; eauto. econs. econs.
    + auto.
    + etrans; eauto.
    + etrans; eauto. etrans; eauto.
    + left. eapply paco11_mon; [apply sim_itree_ret|]; ss.
      etrans; eauto.
Qed.

Lemma sim_store_sim_thread R:
  @sim_store R <8= @sim_thread (lang (unit * R)%type) (lang (unit * R)%type) (sim_terminal eq).
Proof.
  pcofix CIH. i. pfold. ii. ss. splits; ss; ii.
  - inv TERMINAL_TGT. inv PR; ss.
  - exploit sim_store_mon; eauto. i.
    dup x0. dependent destruction x1. subst.
    exploit (progress_program_step_non_update i2 (fun r => Ret (tt, r))); eauto.
    { dependent destruction PR. inv REORDER0; ss. }
    i. des.
    destruct th2.
    exploit sim_store_step; eauto.
    { econs 2. eauto. }
    i. des; eauto.
    + exploit program_step_promise; eauto. i.
      exploit Thread.rtc_tau_step_future; eauto. s. i. des.
      exploit Thread.opt_step_future; eauto. s. i. des.
      exploit Thread.program_step_future; eauto. s. i. des.
      punfold SIM. exploit SIM; try apply SC3; eauto; try refl.
      { exploit Thread.program_step_promises_bot; eauto. s. i.
        eapply Local.bot_promise_consistent; eauto. }
      s. i. des.
      exploit PROMISES; eauto. i. des.
      * left.
        unfold Thread.steps_failure in *. des.
        esplits; [|eauto].
        etrans; eauto. etrans; [|eauto].
        inv STEP_SRC; eauto. econs 2; eauto. econs; eauto.
        { econs. eauto. }
        { etrans; eauto.
          destruct e; by inv STEP; ss; dependent destruction STATE; inv REORDER. }
      * right.
        esplits; [|eauto].
        etrans; eauto. etrans; [|eauto].
        inv STEP_SRC; eauto. econs 2; eauto. econs; eauto.
        { econs. eauto. }
        { etrans; eauto.
          destruct e; by inv STEP; ss; dependent destruction STATE; inv REORDER. }
    + destruct SIM. dependent destruction STEP; ss; dependent destruction STATE. destruct e; ss.
  - exploit sim_store_mon; eauto. i. des.
    exploit sim_store_step; eauto. i. des; eauto.
    + right. esplits; eauto.
      left. eapply paco11_mon; eauto. ss.
    + right. esplits; eauto.
Qed.