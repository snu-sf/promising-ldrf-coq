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
Require Import LowerPromises.

Require Import SimMemory.
Require Import SimPromises.
Require Import SimLocal.
Require Import SimThread.
Require Import iCompatibility.

Require Import ReorderStep.
Require Import ReorderAbortCommon.
Require Import iProgressStep.

Require Import ITreeLang.
Require Import Program.

Set Implicit Arguments.


Inductive reorder_update l1 or1 ow1: forall R (i2:MemE.t R), Prop :=
| reorder_update_load
    l2 o2
    (ORDW1: Ordering.le ow1 Ordering.relaxed)
    (ORD2: Ordering.le o2 Ordering.relaxed)
    (LOC: l1 <> l2):
    reorder_update l1 or1 ow1 (MemE.read l2 o2)
| reorder_update_store
    l2 v2 o2
    (ORDW1: Ordering.le ow1 Ordering.relaxed)
    (ORD21: Ordering.le or1 Ordering.acqrel \/ Ordering.le o2 Ordering.acqrel)
    (ORD22: Ordering.le Ordering.plain o2)
    (LOC: l1 <> l2):
    reorder_update l1 or1 ow1 (MemE.write l2 v2 o2)
(* reordering update; update is unsound *)
(* | reorder_update_update *)
(*     l2 rmw2 or2 ow2 *)
(*     (ORDW1: Ordering.le ow1 Ordering.relaxed) *)
(*     (ORDR2: Ordering.le or2 Ordering.relaxed) *)
(*     (ORDW2: Ordering.le or1 Ordering.acqrel \/ Ordering.le ow2 Ordering.acqrel) *)
(*     (LOC: l1 <> l2): *)
(*     reorder_update l1 or1 ow1 (MemE.update l2 rmw2 or2 ow2) *)
.

Inductive sim_update: forall R
                        (st_src:itree MemE.t (Const.t * R)%type) (lc_src:Local.t) (sc1_src:TimeMap.t) (mem1_src:Memory.t)
                        (st_tgt:itree MemE.t (Const.t * R)%type) (lc_tgt:Local.t) (sc1_tgt:TimeMap.t) (mem1_tgt:Memory.t), Prop :=
| sim_update_intro
    R
    l1 from1 to1 vr1 vret1 vw1 releasedr1 releasedw1 rmw1 or1 ow1 (i2: MemE.t R)
    lc1_src sc1_src mem1_src
    lc1_tgt sc1_tgt mem1_tgt
    lc2_src
    lc3_src sc3_src
    (RMW: ILang.eval_rmw rmw1 vr1 = (vret1, vw1))
    (REORDER: reorder_update l1 or1 ow1 i2)
    (READ: Local.read_step lc1_src mem1_src l1 from1 vr1 releasedr1 or1 lc2_src)
    (FULFILL: match vw1 with
              | Some val => fulfill_step lc2_src sc1_src l1 from1 to1 val releasedr1 releasedw1 ow1 lc3_src sc3_src
              | None => lc3_src = lc2_src /\ sc3_src = sc1_src
              end)
    (LOCAL: sim_local SimPromises.bot lc3_src lc1_tgt)
    (SC: TimeMap.le sc3_src sc1_tgt)
    (MEMORY: sim_memory mem1_src mem1_tgt)
    (WF_SRC: Local.wf lc1_src mem1_src)
    (WF_TGT: Local.wf lc1_tgt mem1_tgt)
    (SC_SRC: Memory.closed_timemap sc1_src mem1_src)
    (SC_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
    (MEM_SRC: Memory.closed mem1_src)
    (MEM_TGT: Memory.closed mem1_tgt):
    sim_update
      (Vis i2 (fun v2 => Vis (MemE.update l1 rmw1 or1 ow1) (fun v1 => Ret (v1, v2)))) lc1_src sc1_src mem1_src
      (Vis i2 (fun v2 => Ret (vret1, v2))) lc1_tgt sc1_tgt mem1_tgt
| sim_update_racy_update
    R
    l1 vr1 vret1 vw1 rmw1 or1 ow1 (i2: MemE.t R)
    lc1_src sc1_src mem1_src
    lc1_tgt sc1_tgt mem1_tgt
    (RMW: ILang.eval_rmw rmw1 vr1 = (vret1, vw1))
    (REORDER: reorder_update l1 or1 ow1 i2)
    (RACY_UPDATE: match vw1 with
                  | Some val => Local.racy_update_step lc1_src mem1_src l1 or1 ow1
                  | None => Local.racy_read_step lc1_src mem1_src l1 vr1 or1
                  end)
    (LOCAL: sim_local SimPromises.bot lc1_src lc1_tgt)
    (SC: TimeMap.le sc1_src sc1_tgt)
    (MEMORY: sim_memory mem1_src mem1_tgt)
    (WF_SRC: Local.wf lc1_src mem1_src)
    (WF_TGT: Local.wf lc1_tgt mem1_tgt)
    (SC_SRC: Memory.closed_timemap sc1_src mem1_src)
    (SC_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
    (MEM_SRC: Memory.closed mem1_src)
    (MEM_TGT: Memory.closed mem1_tgt):
    sim_update
      (Vis i2 (fun v2 => Vis (MemE.update l1 rmw1 or1 ow1) (fun v1 => Ret (v1, v2)))) lc1_src sc1_src mem1_src
      (Vis i2 (fun v2 => Ret (vret1, v2))) lc1_tgt sc1_tgt mem1_tgt
.

Lemma sim_update_mon
      R
      st_src lc_src sc1_src mem1_src
      st_tgt lc_tgt sc1_tgt mem1_tgt
      sc2_src mem2_src
      sc2_tgt mem2_tgt
      (SIM1: sim_update st_src lc_src sc1_src mem1_src
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
  @sim_update R
              st_src lc_src sc2_src mem2_src
              st_tgt lc_tgt sc2_tgt mem2_tgt.
Proof.
  destruct SIM1.
  - exploit Local.read_step_future; eauto. i. des.
    exploit future_read_step; try exact READ; eauto. i. des.
    exploit Local.read_step_future; eauto. i. des.
    destruct vw1 as [vw1|]; cycle 1.
    { ss; des; subst. econs; [eauto|..]; s; eauto; etrans; eauto. }
    exploit future_fulfill_step; try exact FULFILL; eauto. i. des.
    exploit sim_local_fulfill_bot; try apply x0; try exact LOCAL0; try refl;
      try exact WF0; try by viewtac.
    { econs.
      - apply WF2.
      - eapply TView.future_weak_closed; eauto. apply WF2.
      - inv READ. apply WF_SRC.
      - apply WF2.
      - apply WF2.
    }
    i. des.
    econs; [eauto|..]; s; eauto; etrans; eauto.
  - destruct vw1 as [vw1|].
    + exploit future_racy_update_step; try exact RACY_UPDATE; eauto. i. des.
      econs 2; eauto.
    + exploit future_racy_read_step; try exact RACY_UPDATE; eauto. i. des.
      econs 2; eauto.
Grab Existential Variables.
{ econs 2. }
{ econs. econs 3. }
Qed.

Lemma sim_update_step
      R
      st1_src lc1_src sc1_src mem1_src
      st1_tgt lc1_tgt sc1_tgt mem1_tgt
      (SIM: sim_update st1_src lc1_src sc1_src mem1_src
                       st1_tgt lc1_tgt sc1_tgt mem1_tgt):
  _sim_thread_step (lang (Const.t * R)%type) (lang (Const.t * R)%type)
                   ((@sim_thread (lang (Const.t * R)%type) (lang (Const.t * R)%type) (sim_terminal eq)) \8/ @sim_update R)
                   st1_src lc1_src sc1_src mem1_src
                   st1_tgt lc1_tgt sc1_tgt mem1_tgt.
Proof.
  destruct SIM.
  { (* update *)
    ii.
    exploit Local.read_step_future; eauto. i. des.
    destruct vw1 as [vw1|]; cycle 1.
    { ss. des. subst.
      inv STEP_TGT; [inv STEP|dependent destruction STEP; inv LOCAL0; ss; dependent destruction STATE; inv REORDER]; ss.
      - (* promise *)
        right.
        exploit Local.promise_step_future; eauto. i. des.
        exploit sim_local_promise_bot; eauto. i. des.
        exploit reorder_read_promise; try exact READ; try exact STEP_SRC; eauto. i. des.
        exploit Local.promise_step_future; eauto. i. des.
        esplits; try apply SC; eauto.
        + ss.
        + econs 2. econs. econs; eauto.
        + eauto.
        + right. econs; [eauto|..]; s; eauto. etrans; eauto.
      - (* load *)
        right.
        exploit sim_local_read; (try by etrans; eauto); eauto; try refl. i. des.
        exploit reorder_read_read; try exact READ; try exact STEP_SRC; try by eauto. i. des.
        esplits.
        + ss.
        + econs 2; [|econs 1]. econs.
          * econs. econs 2. econs; [|econs 2]; eauto. econs. econs.
          * eauto.
        + econs 2. econs 2. econs; [|econs 2]; eauto. econs; eauto.
        + eauto.
        + eauto.
        + eauto.
        + left. eapply paco11_mon; [apply sim_itree_ret|]; ss.
      - (* store *)
        right.
        guardH ORD21.
        hexploit sim_local_write_bot; try exact LOCAL1; try exact SC;
          try exact WF2; try refl; eauto; try by viewtac. i. des.
        exploit reorder_read_write; try exact READ; try exact STEP_SRC; eauto; try by viewtac. i. des.
        esplits.
        + ss.
        + econs 2; [|econs 1]. econs.
          * econs. econs 2. econs; [|econs 3]; eauto. econs; eauto.
          * eauto.
        + econs 2. econs 2. econs; [|econs 2]; eauto. econs; eauto.
        + eauto.
        + eauto.
        + etrans; eauto.
        + left. eapply paco11_mon; [apply sim_itree_ret|]; ss. etrans; eauto.
      - (* na write *)
        inv LOCAL1. destruct ord; ss.
      - (* racy read *)
        right.
        exploit sim_local_racy_read; try exact LOCAL; eauto; try refl. i. des.
        exploit reorder_read_racy_read; try exact READ; try exact x0; eauto; ss. i. des.
        esplits.
        + ss.
        + econs 2; [|econs 1]. econs.
          * econs. econs 2. econs; [|econs 9]; eauto. econs. econs.
          * eauto.
        + econs 2. econs 2. econs; [|econs 2]; eauto. econs; eauto.
        + eauto.
        + eauto.
        + eauto.
        + left. eapply paco11_mon; [apply sim_itree_ret|]; ss.
      - (* racy write *)
        left. guardH ORD21.
        assert (SIM_LC: sim_local SimPromises.bot lc1_src lc3_tgt).
        { exploit Local.read_step_future; try exact READ; eauto. i. des.
          inv READ. inv LOCAL. ss.
          econs; eauto. etrans; eauto.
        }
        exploit sim_local_racy_write; try exact SIM_LC;
          try match goal with
              | [|- is_true (Ordering.le _ _)] => refl
              end; eauto.
        i. des.
        unfold Thread.steps_failure. esplits; try refl.
        + econs 2. econs; [|econs 10]; eauto. econs. ss.
        + ss.
    }

    { exploit fulfill_step_future; eauto. i. des.
      inv STEP_TGT; [inv STEP|dependent destruction STEP; inv LOCAL0; ss; dependent destruction STATE; inv REORDER]; ss.
      - (* promise *)
        right.
        exploit Local.promise_step_future; eauto. i. des.
        exploit sim_local_promise; try apply LOCAL0; (try by etrans; eauto); eauto. i. des.
        exploit reorder_update_promise; try exact READ; try exact FULFILL; try exact STEP_SRC; eauto. i. des.
        exploit Local.promise_step_future; eauto. i. des.
        esplits.
        + ss.
        + eauto.
        + econs 2. econs 1. econs; eauto.
        + auto.
        + etrans; eauto.
        + auto.
        + right. econs; [eauto|..]; s; eauto.
          * etrans; eauto.
          * eapply Memory.future_closed_timemap; eauto.
      - (* load *)
        right.
        exploit sim_local_read; try apply LOCAL0; (try by etrans; eauto); eauto; try refl. i. des.
        exploit reorder_update_read; try exact FULFILL; try exact READ; try exact STEP_SRC; eauto. i. des.
        exploit Local.read_step_future; try exact STEP1; eauto. i. des.
        exploit Local.read_step_future; try exact STEP2; eauto. i. des.
        exploit fulfill_write_sim_memory; eauto. i. des.
        esplits.
        + ss.
        + econs 2; eauto. econs.
          * econs. econs 2. econs; [|econs 2]; eauto. econs. econs.
          * auto.
        + econs 2. econs 2. econs; [|econs 4]; eauto. econs; eauto.
        + auto.
        + auto.
        + etrans; eauto.
        + left. eapply paco11_mon; [apply sim_itree_ret|]; ss.
      - (* store *)
        right.
        guardH ORD21.
        hexploit sim_local_write_bot; try exact LOCAL1; try exact LOCAL; try exact SC; try exact WF0; try refl; eauto; try by viewtac. i. des.
        hexploit reorder_update_write; try exact READ; try exact FULFILL; try exact STEP_SRC; eauto; try by viewtac.
        { ii. subst. inv FULFILL. eapply Time.lt_strorder. eauto. }
        i. des.
        exploit Local.write_step_future; try exact STEP1; eauto; try by viewtac. i. des.
        exploit Local.read_step_future; try exact STEP2; eauto; try by viewtac. i. des.
        exploit fulfill_write_sim_memory; eauto. i. des.
        esplits.
        + ss.
        + econs 2; eauto. econs.
          * econs. econs 2. econs; [|econs 3]; eauto. econs; eauto.
          * auto.
        + econs 2. econs 2. econs; [|econs 4]; eauto. econs; eauto.
        + auto.
        + etrans; eauto.
        + etrans; eauto. etrans; eauto.
        + left. eapply paco11_mon; [apply sim_itree_ret|]; ss.
          etrans; eauto.
      - (* na write *)
        inv LOCAL1. destruct ord; ss.
      - (* racy read *)
        right.
        exploit sim_local_racy_read; try exact LOCAL1; eauto; try refl. i. des.
        exploit reorder_fulfill_racy_read; try exact FULFILL; eauto. i. des.
        exploit reorder_read_racy_read; try exact READ; eauto. i. des.
        exploit fulfill_write_sim_memory; eauto. i. des.
        esplits.
        + ss.
        + econs 2; eauto. econs.
          * econs. econs 2. econs; [|econs 9]; eauto. econs. econs.
          * auto.
        + econs 2. econs 2. econs; [|econs 4]; eauto. econs; eauto.
        + auto.
        + auto.
        + etrans; eauto.
        + left. eapply paco11_mon; [apply sim_itree_ret|]; ss.
      - (* racy write *)
        left. guardH ORD21.
        exploit sim_local_racy_write; try exact LOCAL1;
          try match goal with
              | [|- is_true (Ordering.le _ _)] => refl
              end; eauto. i. des.
        exploit reorder_fulfill_racy_write; try exact FULFILL; eauto. i. des.
        exploit reorder_read_racy_write; try exact READ; eauto. i. des.
        unfold Thread.steps_failure.
        esplits; try refl.
        + econs 2. econs; [|econs 10]; eauto. econs. econs.
        + ss.
    }
  }

  { (* racy update *)
    destruct vw1 as [vw1|]; cycle 1.
    { ii. ss.
      inv STEP_TGT; [inv STEP|dependent destruction STEP; inv LOCAL0; ss; dependent destruction STATE; inv REORDER]; ss.
      - (* promise *)
        right.
        exploit Local.promise_step_future; eauto. i. des.
        exploit sim_local_promise_bot; eauto. i. des.
        exploit reorder_racy_read_promise; try exact RACY_UPDATE; try exact STEP_SRC; eauto. i. des.
        exploit Local.promise_step_future; try exact STEP_SRC; eauto. i. des.
        esplits; try apply SC; eauto; ss.
        + econs 2. econs. econs; eauto.
        + eauto.
        + right. econs 2; eauto.
      - (* load *)
        right.
        exploit sim_local_read; (try by etrans; eauto); eauto; try refl. i. des.
        exploit reorder_racy_read_read; try exact RACY_UPDATE; try exact STEP_SRC; eauto; ss. i. des.
        esplits.
        + ss.
        + econs 2; [|econs 1]. econs.
          * econs. econs 2. econs; [|econs 2]; eauto. econs. econs.
          * eauto.
        + econs 2. econs 2. econs; [|econs 9]; eauto. econs; eauto.
        + eauto.
        + eauto.
        + eauto.
        + left. eapply paco11_mon; [apply sim_itree_ret|]; ss.
      - (* store *)
        right.
        guardH ORD21.
        hexploit sim_local_write_bot; try exact LOCAL1; try exact SC;
          try exact WF_SRC; try exact WF_TGT; try refl; eauto; try by viewtac. i. des.
        exploit reorder_racy_read_write; try exact RACY_UPDATE; eauto. i. des.
        esplits.
        + ss.
        + econs 2; [|econs 1]. econs.
          * econs. econs 2. econs; [|econs 3]; eauto. econs. ss.
          * eauto.
        + econs 2. econs 2. econs; [|econs 9]; eauto. econs; eauto.
        + eauto.
        + eauto.
        + ss.
        + left. eapply paco11_mon; [apply sim_itree_ret|]; ss.
      - (* na write *)
        inv LOCAL1. destruct ord; ss.
      - (* racy read *)
        right.
        exploit sim_local_racy_read; try exact LOCAL; eauto; try refl. i. des.
        esplits.
        + ss.
        + econs 2; [|econs 1]. econs.
          * econs. econs 2. econs; [|econs 9]; eauto. econs; eauto.
          * eauto.
        + econs 2. econs 2. econs; [|econs 9]; try exact RACY_UPDATE. econs; eauto.
        + eauto.
        + eauto.
        + eauto.
        + left. eapply paco11_mon; [apply sim_itree_ret|]; ss.
      - (* racy write *)
        left. guardH ORD21.
        exploit sim_local_racy_write; try exact LOCAL1; try apply RACY_UPDATE;
          try match goal with
              | [|- is_true (Ordering.le _ _)] => refl
              end; eauto.
        i. des.
        unfold Thread.steps_failure. esplits; try refl.
        + econs 2. econs; [|econs 10]; eauto. econs. econs.
        + ss.
    }

    { ii. left. unfold Thread.steps_failure.
      inv REORDER.
      - (* load *)
        exploit progress_read_step_cur; try exact WF_SRC; eauto. i. des.
        exploit read_step_cur_future; try exact READ; eauto. i. des.
        esplits.
        + econs 2; try refl. econs.
          * econs. econs 2. econs; [|econs 2]; eauto. econs. econs.
          * ss.
        + econs 2. econs; [|econs 11].
          * econs; eauto.
          * assert (CONS: Local.promise_consistent lc2).
            { ii. rewrite <- PROMISES, <- TVIEW in *. inv RACY_UPDATE; eauto. }
            inv RACY_UPDATE.
            { econs 1; eauto. }
            { econs 2; eauto. }
            { econs 3; eauto; try congr.
              inv RACE. econs. rewrite <- TVIEW. ss.
            }
        + ss.
      - (* store *)
        guardH ORD21.
        exploit (@LowerPromises.steps_promises_rel
                   (lang (Const.t * ()))
                   (Thread.mk (lang (Const.t * ()))
                              (Vis (MemE.write l2 v2 o2) (fun v0 : () => Vis (MemE.update l1 rmw1 or1 ow1) (fun v1 : Const.t => Ret (v1, v0))))
                              lc1_src sc1_src mem1_src)); s; eauto.
        i. des. destruct e2. ss.
        exploit LowerPromises.rtc_opt_promise_step_future; eauto. s. i. des. inv STATE.
        hexploit LowerPromises.promises_rel_promise_consistent; eauto; i.
        { inv RACY_UPDATE; eauto. }
        hexploit LowerPromises.promises_rel_nonsynch; eauto. i.
        exploit Thread.rtc_tau_step_future; try exact STEPS0; eauto. s. i. des.
        exploit write_step_consistent; try exact WF2; eauto. i. des.
        esplits.
        + eapply rtc_n1; eauto. econs.
          * econs. econs 2. econs; [|econs 3; eauto]. econs. econs.
          * ss.
        + econs 2. econs; [|econs 11].
          * econs; eauto.
          * inv RACY_UPDATE.
            { econs 1; eauto. }
            { econs 2; eauto. }
            { exploit Thread.rtc_tau_step_non_promised; try exact STEPS0; eauto. s. i. des.
              exploit Local.program_step_non_promised; [econs 3|..]; try exact STEP; eauto. i. des.
              econs 3; eauto; try congr.
              inv RACE. econs. rewrite TVIEW in TS.
              inv STEP. ss.
              apply TimeFacts.join_spec_lt; auto.
              unfold TimeMap.singleton, Loc.LocFun.add, Loc.LocFun.init, Loc.LocFun.find. condtac; ss.
              eapply TimeFacts.le_lt_lt; eauto. apply Time.bot_spec.
            }
        + ss.
    }
  }
Grab Existential Variables.
{ econs 2. }
{ econs. econs 3. }
Qed.

Lemma sim_update_sim_thread R:
  @sim_update R <8= @sim_thread (lang (Const.t * R)%type) (lang (Const.t * R)%type) (sim_terminal eq).
Proof.
  pcofix CIH. i. pfold. ii. ss. splits; ss; ii.
  - inv TERMINAL_TGT. inv PR; ss.
  - exploit sim_update_mon; eauto. i.
    dup x0. dependent destruction x1.
    { exploit (progress_program_step_non_update
                 i2
                 (fun r => Ret (fst (ILang.eval_rmw rmw1 vr1), r))); eauto.
      { inv REORDER; ss. }
      i. des.
      destruct th2. exploit sim_update_step; eauto.
      { rewrite RMW in *. ss. econs 2. eauto. }
      i. des; eauto.
      + exploit Thread.program_step_promises_bot; eauto. s. i.
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
          esplits; [|eauto|]; ss.
          etrans; eauto. etrans; [|eauto].
          inv STEP_SRC; eauto. econs 2; eauto. econs.
          { econs. eauto. }
          { etrans; eauto.
            destruct e; by inv STEP; ss; dependent destruction STATE; inv REORDER. }
        * right. esplits; [|eauto].
          etrans; eauto. etrans; [|eauto].
          inv STEP_SRC; eauto. econs 2; eauto. econs.
          { econs. eauto. }
          { etrans; eauto.
            destruct e; by inv STEP; ss; dependent destruction STATE; inv REORDER. }
      + inv SIM.
        * inv STEP; ss; dependent destruction STATE. destruct e; ss.
        * inv STEP; ss; dependent destruction STATE. destruct e; ss.
    }
    { exploit (progress_program_step_non_update
                 i2
                 (fun r => Ret (fst (ILang.eval_rmw rmw1 vr1), r))); eauto.
      { inv REORDER; ss. }
      i. des.
      destruct th2. exploit sim_update_step; eauto.
      { rewrite RMW in *. ss. econs 2. eauto. }
      i. des; eauto.
      + exploit Thread.program_step_promises_bot; eauto. s. i.
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
          esplits; [|eauto|]; ss.
          etrans; eauto. etrans; [|eauto].
          inv STEP_SRC; eauto. econs 2; eauto. econs.
          { econs. eauto. }
          { etrans; eauto.
            destruct e; by inv STEP; ss; dependent destruction STATE; inv REORDER. }
        * right. esplits; [|eauto].
          etrans; eauto. etrans; [|eauto].
          inv STEP_SRC; eauto. econs 2; eauto. econs.
          { econs. eauto. }
          { etrans; eauto.
            destruct e; by inv STEP; ss; dependent destruction STATE; inv REORDER. }
      + inv SIM.
        * inv STEP; ss; dependent destruction STATE. destruct e; ss.
        * inv STEP; ss; dependent destruction STATE. destruct e; ss.
    }
  - exploit sim_update_mon; eauto. i. des.
    exploit sim_update_step; eauto. i. des; eauto.
    + right. esplits; eauto.
      left. eapply paco11_mon; eauto. ss.
    + right. esplits; eauto.
Qed.
