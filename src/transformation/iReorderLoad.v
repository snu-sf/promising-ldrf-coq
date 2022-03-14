From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Basic.
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

Require Import SimMemory.
Require Import SimPromises.
Require Import SimLocal.
Require Import SimThread.
Require Import iCompatibility.

Require Import ReorderStep.

Require Import ITreeLang.
Require Import Program.

Set Implicit Arguments.


Inductive reorder_load l1 o1: forall R (i2:MemE.t R), Prop :=
| reorder_load_load
    l2 o2
    (ORD2: Ordering.le o2 Ordering.relaxed)
    (LOC: l1 = l2 -> Ordering.le o1 Ordering.plain /\ Ordering.le o2 Ordering.plain):
    reorder_load l1 o1 (MemE.read l2 o2)
| reorder_load_store
    l2 v2 o2
    (ORD: Ordering.le o1 Ordering.acqrel \/ Ordering.le o2 Ordering.acqrel)
    (ORD2: Ordering.le Ordering.plain o2)
    (LOC: l1 <> l2):
    reorder_load l1 o1 (MemE.write l2 v2 o2)
| reorder_load_update
    l2 rmw2 or2 ow2
    (ORDR2: Ordering.le or2 Ordering.relaxed)
    (ORDW2: Ordering.le o1 Ordering.acqrel \/ Ordering.le ow2 Ordering.acqrel)
    (LOC: l1 <> l2):
    reorder_load l1 o1 (MemE.update l2 rmw2 or2 ow2)
| reorder_load_fence
    or2 ow2
    (ORDR2: Ordering.le or2 Ordering.relaxed)
    (ORDW2: Ordering.le ow2 Ordering.acqrel):
    reorder_load l1 o1 (MemE.fence or2 ow2)
.

Inductive sim_load: forall R
                      (st_src:itree MemE.t (Const.t * R)%type) (lc_src:Local.t) (sc1_src:TimeMap.t) (mem1_src:Memory.t)
                      (st_tgt:itree MemE.t (Const.t * R)%type) (lc_tgt:Local.t) (sc1_tgt:TimeMap.t) (mem1_tgt:Memory.t), Prop :=
| sim_load_intro
    R
    l1 ts1 v1 released1 o1 (i2: MemE.t R)
    lc1_src sc1_src mem1_src
    lc1_tgt sc1_tgt mem1_tgt
    lc2_src
    (REORDER: reorder_load l1 o1 i2)
    (READ: Local.read_step lc1_src mem1_src l1 ts1 v1 released1 o1 lc2_src)
    (LOCAL: sim_local SimPromises.bot lc2_src lc1_tgt)
    (SC: TimeMap.le sc1_src sc1_tgt)
    (MEMORY: sim_memory mem1_src mem1_tgt)
    (WF_SRC: Local.wf lc1_src mem1_src)
    (WF_TGT: Local.wf lc1_tgt mem1_tgt)
    (SC_SRC: Memory.closed_timemap sc1_src mem1_src)
    (SC_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
    (MEM_SRC: Memory.closed mem1_src)
    (MEM_TGT: Memory.closed mem1_tgt):
    sim_load
      (Vis i2 (fun v2 => Vis (MemE.read l1 o1) (fun v1 => Ret (v1, v2)))) lc1_src sc1_src mem1_src
      (Vis i2 (fun v2 => Ret (v1, v2))) lc1_tgt sc1_tgt mem1_tgt
| sim_load_racy_read
    R
    l1 t1 v1 o1 (i2: MemE.t R)
    lc1_src sc1_src mem1_src
    lc1_tgt sc1_tgt mem1_tgt
    (REORDER: reorder_load l1 o1 i2)
    (READ: Local.racy_read_step lc1_src mem1_src l1 t1 v1 o1)
    (LOCAL: sim_local SimPromises.bot lc1_src lc1_tgt)
    (SC: TimeMap.le sc1_src sc1_tgt)
    (MEMORY: sim_memory mem1_src mem1_tgt)
    (WF_SRC: Local.wf lc1_src mem1_src)
    (WF_TGT: Local.wf lc1_tgt mem1_tgt)
    (SC_SRC: Memory.closed_timemap sc1_src mem1_src)
    (SC_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
    (MEM_SRC: Memory.closed mem1_src)
    (MEM_TGT: Memory.closed mem1_tgt):
    sim_load
      (Vis i2 (fun v2 => Vis (MemE.read l1 o1) (fun v1 => Ret (v1, v2)))) lc1_src sc1_src mem1_src
      (Vis i2 (fun v2 => Ret (v1, v2))) lc1_tgt sc1_tgt mem1_tgt
.

Lemma sim_load_sim_local
      R
      st_src lc_src sc_src mem_src
      st_tgt lc_tgt sc_tgt mem_tgt
      (SIM: @sim_load R st_src lc_src sc_src mem_src st_tgt lc_tgt sc_tgt mem_tgt):
  sim_local SimPromises.bot lc_src lc_tgt.
Proof.
  inv SIM; eauto.
  exploit Local.read_step_future; eauto. i. des.
  inv READ. inv LOCAL. ss.
  econs; eauto. etrans; eauto.
Qed.

Lemma sim_load_mon
      R
      st_src lc_src sc1_src mem1_src
      st_tgt lc_tgt sc1_tgt mem1_tgt
      sc2_src mem2_src
      sc2_tgt mem2_tgt
      (SIM1: sim_load st_src lc_src sc1_src mem1_src
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
  @sim_load R
            st_src lc_src sc2_src mem2_src
            st_tgt lc_tgt sc2_tgt mem2_tgt.
Proof.
  dependent destruction SIM1.
  - exploit future_read_step; try exact READ; eauto. i. des.
    econs; eauto. etrans; eauto.
  - exploit future_racy_read_step; try exact READ; eauto. i. des.
    econs 2; eauto.
Qed.

Lemma sim_load_step
      R
      st1_src lc1_src sc1_src mem1_src
      st1_tgt lc1_tgt sc1_tgt mem1_tgt
      (SIM: sim_load st1_src lc1_src sc1_src mem1_src
                     st1_tgt lc1_tgt sc1_tgt mem1_tgt):
  _sim_thread_step (lang (Const.t * R)%type) (lang (Const.t * R)%type)
                   ((@sim_thread (lang (Const.t * R)%type) (lang (Const.t * R)%type) (sim_terminal eq)) \8/ @sim_load R)
                   st1_src lc1_src sc1_src mem1_src
                   st1_tgt lc1_tgt sc1_tgt mem1_tgt.
Proof.
  exploit sim_load_sim_local; eauto. intro SIM_LC.
  dependent destruction SIM.
  { (* read *)
    ii.
    exploit Local.read_step_future; eauto. i. des.
    inv STEP_TGT; [inv STEP|dependent destruction STEP; inv LOCAL0; ss; dependent destruction STATE; inv REORDER].
    - (* promise *)
      right.
      exploit Local.promise_step_future; eauto. i. des.
      exploit sim_local_promise_bot; try exact LOCAL; eauto. i. des.
      exploit reorder_read_promise; try exact READ; try exact STEP_SRC; eauto. i. des.
      exploit Local.promise_step_future; eauto. i. des.
      esplits; try apply SC; eauto; ss.
      + econs 2. econs. econs; eauto.
      + right. econs; eauto. etrans; eauto.
    - (* load *)
      right.
      exploit sim_local_read; try exact LOCAL; (try by etrans; eauto); eauto; try refl. i. des.
      exploit reorder_read_read; try exact READ; try exact STEP_SRC; eauto. i. des.
      esplits.
      + ss.
      + econs 2; [|econs 1]. econs.
        * econs. econs 2. econs; [|econs 2]; eauto. econs. econs.
        * eauto.
      + econs 2. econs 2. econs; [|econs 2]; eauto. econs. econs.
      + eauto.
      + eauto.
      + eauto.
      + left. eapply paco11_mon; [apply sim_itree_ret|]; ss.
    - (* update-load *)
      right.
      guardH ORDW2.
      exploit sim_local_read; try exact LOCAL; (try by etrans; eauto); eauto; try refl. i. des.
      exploit reorder_read_read; try exact READ; try exact STEP_SRC; try by eauto. i. des.
      esplits.
      + ss.
      + econs 2; [|econs 1]. econs.
        * econs. econs 2. econs; [|econs 2]; eauto. econs; eauto.
        * eauto.
      + econs 2. econs 2. econs; [|econs 2]; eauto. econs. econs.
      + eauto.
      + eauto.
      + eauto.
      + left. eapply paco11_mon; [apply sim_itree_ret|]; ss.
    - (* store *)
      right.
      guardH ORD.
      hexploit sim_local_write_bot; try exact LOCAL1; try exact SC;
        try exact WF2; try refl; eauto; try by viewtac. i. des.
      exploit reorder_read_write; try exact READ; try exact STEP_SRC; eauto; try by viewtac. i. des.
      esplits.
      + ss.
      + econs 2; [|econs 1]. econs.
        * econs. econs 2. econs; [|econs 3]; eauto. econs; eauto.
        * eauto.
      + econs 2. econs 2. econs; [|econs 2]; eauto. econs. econs.
      + eauto.
      + eauto.
      + etrans; eauto.
      + left. eapply paco11_mon; [apply sim_itree_ret|]; ss. etrans; eauto.
    - (* update *)
      right.
      guardH ORDW2.
      exploit Local.read_step_future; try exact LOCAL1; eauto. i. des.
      exploit sim_local_read; try exact LOCAL1; try exact LOCAL; eauto; try refl. i. des.
      exploit Local.read_step_future; try exact STEP_SRC; eauto. i. des.
      hexploit sim_local_write_bot; try exact LOCAL2; try exact SC; eauto; try refl. i. des.
      exploit reorder_read_read; try exact READ; try exact STEP_SRC; eauto; try congr. i. des.
      exploit Local.read_step_future; try exact STEP1; eauto. i. des.
      exploit reorder_read_write; try exact STEP2; try exact STEP_SRC0; eauto; try congr. i. des.
      esplits.
      + ss.
      + econs 2; [|econs 1]. econs.
        * econs. econs 2. econs; [|econs 4]; eauto. econs; eauto.
        * eauto.
      + econs 2. econs 2. econs; [|econs 2]; eauto. econs. econs.
      + eauto.
      + eauto.
      + etrans; eauto.
      + left. eapply paco11_mon; [apply sim_itree_ret|]; ss.
        * etrans; eauto.
    - (* fence *)
      right.
      exploit sim_local_fence; try exact LOCAL1; try exact LOCAL; try exact SC; eauto; try refl. i. des.
      exploit reorder_read_fence; try exact READ; try exact STEP_SRC; eauto. i. des.
      esplits.
      + ss.
      + econs 2; [|econs 1]. econs.
        * econs. econs 2. econs; [|econs 5]; eauto. econs. econs.
        * eauto.
      + econs 2. econs 2. econs; [|econs 2]; eauto. econs. econs.
      + eauto.
      + etrans; eauto.
      + eauto.
      + left. eapply paco11_mon; [apply sim_itree_ret|]; ss.
        etrans; eauto.
    - (* na write *)
      inv LOCAL1. destruct ord; ss.
    - (* racy read *)
      right.
      exploit sim_local_racy_read; try exact LOCAL; eauto; try refl. i. des.
      exploit reorder_read_racy_read; try exact READ; try exact x0; eauto. i. des.
      esplits.
      + ss.
      + econs 2; [|econs 1]. econs.
        * econs. econs 2. econs; [|econs 9]; eauto. econs. econs.
        * eauto.
      + econs 2. econs 2. econs; [|econs 2]; eauto. econs. econs.
      + eauto.
      + eauto.
      + eauto.
      + left. eapply paco11_mon; [apply sim_itree_ret|]; ss.
    - (* racy read *)
      right. guardH ORDW2.
      exploit sim_local_racy_read; try exact LOCAL; eauto; try refl. i. des.
      exploit reorder_read_racy_read; try exact READ; try exact x0; eauto; ss. i. des.
      esplits.
      + ss.
      + econs 2; [|econs 1]. econs.
        * econs. econs 2. econs; [|econs 9]; eauto. econs; eauto.
        * ss.
      + econs 2. econs 2. econs; [|econs 2]; eauto. econs. econs.
      + eauto.
      + eauto.
      + eauto.
      + left. eapply paco11_mon; [apply sim_itree_ret|]; ss.
    - (* racy write *)
      left. guardH ORD.
      exploit sim_local_racy_write; try exact LOCAL1; try exact SIM_LC;
        try match goal with
            | [|- is_true (Ordering.le _ _)] => refl
            end; eauto.
      i. des.
      unfold Thread.steps_failure. esplits; try refl.
      + econs 2. econs; [|econs 10]; eauto. econs. eauto.
      + ss.
    - (* racy update *)
      left. guardH ORDW2.
      exploit sim_local_racy_update; try exact LOCAL1; try exact SIM_LC;
        try match goal with
            | [|- is_true (Ordering.le _ _)] => refl
            end; eauto.
      i. des.
      unfold Thread.steps_failure. esplits; try refl.
      + econs 2. econs; [|econs 11]; eauto. econs; eauto.
      + ss.
  }

  { (* racy read *)
    ii.
    inv STEP_TGT; [inv STEP|dependent destruction STEP; inv LOCAL0; ss; dependent destruction STATE; inv REORDER].
    - (* promise *)
      right.
      exploit Local.promise_step_future; eauto. i. des.
      exploit sim_local_promise_bot; eauto. i. des.
      exploit reorder_racy_read_promise; try exact READ; try exact STEP_SRC; eauto. i. des.
      exploit Local.promise_step_future; try exact STEP_SRC; eauto. i. des.
      esplits; try apply SC; eauto; ss.
      + econs 2. econs. econs; eauto.
      + right. econs 2; eauto.
    - (* load *)
      right.
      exploit sim_local_read; (try by etrans; eauto); eauto; try refl. i. des.
      exploit reorder_racy_read_read; try exact READ; try exact STEP_SRC; eauto. i. des.
      esplits.
      + ss.
      + econs 2; [|econs 1]. econs.
        * econs. econs 2. econs; [|econs 2]; eauto. econs. econs.
        * eauto.
      + econs 2. econs 2. econs; [|econs 9]; eauto. econs. econs.
      + eauto.
      + eauto.
      + eauto.
      + left. eapply paco11_mon; [apply sim_itree_ret|]; ss.
    - (* update-load *)
      right.
      guardH ORDW2.
      exploit sim_local_read; (try by etrans; eauto); eauto; try refl. i. des.
      exploit reorder_racy_read_read; try exact READ; try exact STEP_SRC; try by eauto. i. des.
      esplits.
      + ss.
      + econs 2; [|econs 1]. econs.
        * econs. econs 2. econs; [|econs 2]; eauto. econs; eauto.
        * eauto.
      + econs 2. econs 2. econs; [|econs 9]; eauto. econs. econs.
      + eauto.
      + eauto.
      + eauto.
      + left. eapply paco11_mon; [apply sim_itree_ret|]; ss.
    - (* store *)
      right.
      guardH ORD.
      hexploit sim_local_write_bot; try exact LOCAL1; try exact SC;
        try exact WF_SRC; try exact WF_TGT; try refl; eauto; try by viewtac. i. des.
      exploit reorder_racy_read_write; try exact READ; eauto. i. des.
      esplits.
      + ss.
      + econs 2; [|econs 1]. econs.
        * econs. econs 2. econs; [|econs 3]; eauto. econs. eauto.
        * eauto.
      + econs 2. econs 2. econs; [|econs 9]; eauto. econs. econs.
      + eauto.
      + eauto.
      + ss.
      + left. eapply paco11_mon; [apply sim_itree_ret|]; ss.
    - (* update *)
      right.
      guardH ORDW2.
      exploit Local.read_step_future; try exact LOCAL1; eauto. i. des.
      exploit sim_local_read; try exact LOCAL1; eauto; try refl. i. des.
      exploit Local.read_step_future; try exact STEP_SRC; eauto. i. des.
      hexploit sim_local_write_bot; try exact LOCAL2; try exact SC; eauto; try refl. i. des.
      exploit reorder_racy_read_update; try exact READ; eauto. i. des.
      esplits.
      + ss.
      + econs 2; [|econs 1]. econs.
        * econs. econs 2. econs; [|econs 4]; eauto. econs; eauto.
        * eauto.
      + econs 2. econs 2. econs; [|econs 9]; eauto. econs. econs.
      + eauto.
      + eauto.
      + ss.
      + left. eapply paco11_mon; [apply sim_itree_ret|]; ss.
    - (* fence *)
      right.
      exploit sim_local_fence; try exact LOCAL1; try exact SC; eauto; try refl. i. des.
      exploit reorder_racy_read_fence; try exact READ; try exact STEP_SRC; eauto. i. des.
      esplits.
      + ss.
      + econs 2; [|econs 1]. econs.
        * econs. econs 2. econs; [|econs 5]; eauto. econs. econs.
        * eauto.
      + econs 2. econs 2. econs; [|econs 9]; eauto. econs. econs.
      + eauto.
      + ss.
      + eauto.
      + left. eapply paco11_mon; [apply sim_itree_ret|]; ss.
    - (* na write *)
      inv LOCAL1. destruct ord; ss.
    - (* racy read *)
      right.
      exploit sim_local_racy_read; try exact LOCAL; eauto; try refl. i. des.
      esplits.
      + ss.
      + econs 2; [|econs 1]. econs.
        * econs. econs 2. econs; [|econs 9]; eauto. econs. econs.
        * eauto.
      + econs 2. econs 2. econs; [|econs 9]; try exact READ. econs. econs.
      + eauto.
      + eauto.
      + eauto.
      + left. eapply paco11_mon; [apply sim_itree_ret|]; ss.
    - (* racy read *)
      right. guardH ORDW2.
      exploit sim_local_racy_read; try exact LOCAL; eauto; try refl. i. des.
      esplits.
      + ss.
      + econs 2; [|econs 1]. econs.
        * econs. econs 2. econs; [|econs 9]; eauto. econs; eauto.
        * eauto.
      + econs 2. econs 2. econs; [|econs 9]; try exact READ. econs. econs.
      + eauto.
      + eauto.
      + eauto.
      + left. eapply paco11_mon; [apply sim_itree_ret|]; ss.
    - (* racy write *)
      left. guardH ORD.
      exploit sim_local_racy_write; try exact LOCAL1; try exact SIM_LC;
        try match goal with
            | [|- is_true (Ordering.le _ _)] => refl
            end; eauto.
      i. des.
      unfold Thread.steps_failure. esplits; try refl.
      + econs 2. econs; [|econs 10]; eauto. econs. econs.
      + ss.
    - (* racy update *)
      left. guardH ORDW2.
      exploit sim_local_racy_update; try exact LOCAL1; try exact SIM_LC;
        try match goal with
            | [|- is_true (Ordering.le _ _)] => refl
            end; eauto.
      i. des.
      unfold Thread.steps_failure. esplits; try refl.
      + econs 2. econs; [|econs 11]; eauto. econs; eauto.
      + ss.
  }
Qed.

Lemma sim_load_sim_thread R:
  @sim_load R <8= @sim_thread (lang (Const.t * R)%type) (lang (Const.t * R)%type) (sim_terminal eq).
Proof.
  pcofix CIH. i. pfold. ii. ss. splits; ss; ii.
  - inv TERMINAL_TGT. inv PR; ss.
  - right.
    esplits; eauto.
    inv PR.
    + inv READ. inv LOCAL. ss.
      apply SimPromises.sem_bot_inv in PROMISES; auto. rewrite PROMISES. auto.
    + inv READ. inv LOCAL. ss.
      apply SimPromises.sem_bot_inv in PROMISES; auto. rewrite PROMISES. auto.
  - exploit sim_load_mon; eauto. i.
    exploit sim_load_step; eauto. i. des; eauto.
    + right. esplits; eauto.
      left. eapply paco11_mon; eauto. ss.
    + right. esplits; eauto.
Qed.
