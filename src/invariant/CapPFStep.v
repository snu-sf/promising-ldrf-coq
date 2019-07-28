Require Import Omega.
Require Import RelationClasses.

Require Import sflib.

Require Import Axioms.
Require Import Basic.
Require Import DataStructure.
Require Import Time.
Require Import Event.
Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.

Require Import PromiseConsistent.
Require Import PFStep.

Set Implicit Arguments.

Module CapPFStep.
  Definition sim_promises := PFStep.sim_promises.
  Hint Unfold sim_promises.
  Definition sim_local := PFStep.sim_local.
  Hint Unfold sim_local.
  Definition sim_message := PFStep.sim_message.

  Definition cap_src (latests: TimeMap.t) (loc: Loc.t) (promises: Memory.t)
             (msg_src: Message.t) (val: Const.t) (released_tgt: option View.t): Prop :=
    if Memory.get loc (latests loc) promises
    then msg_src = Message.half
    else sim_message msg_src (Message.full val released_tgt).

  Inductive sim_memory (latests caps: TimeMap.t) (promises mem_src mem_tgt: Memory.t): Prop :=
  | sim_memory_intro
      (SOUND: forall loc from to msg_src
                (CAP: to <> caps loc)
                (GETP: Memory.get loc to promises = None)
                (GET_SRC: Memory.get loc to mem_src = Some (from, msg_src)),
          exists msg_tgt,
            <<GET_TGT: Memory.get loc to mem_tgt = Some (from, msg_tgt)>> /\
            <<MSG: sim_message msg_src msg_tgt>>)
      (COMPLETE: forall loc from to msg_tgt
                   (CAP: to <> caps loc)
                   (GETP: Memory.get loc to promises = None)
                   (GET_TGT: Memory.get loc to mem_tgt = Some (from, msg_tgt)),
          exists msg_src,
            <<GET_SRC: Memory.get loc to mem_src = Some (from, msg_src)>> /\
            <<MSG: sim_message msg_src msg_tgt>>)
      (LATESTS: forall loc, Time.lt (latests loc) (caps loc))
      (CAPP: forall loc, Memory.get loc (caps loc) promises = None)
      (CAPS: forall loc,
          exists from_latest from val released msg_src released_tgt,
            <<LATEST: Memory.get loc (latests loc) mem_tgt = Some (from_latest, Message.full val released)>> /\
            <<CAP_SRC: Memory.get loc (caps loc) mem_src = Some (from, msg_src)>> /\
            <<CAP_TGT: Memory.get loc (caps loc) mem_tgt = Some (from, Message.full val released_tgt)>> /\
            <<MSG: cap_src latests loc promises msg_src val released_tgt>>)
  .

  Inductive sim_thread (lang: Language.t) (latests caps: TimeMap.t) (e_src e_tgt: @Thread.t lang): Prop :=
  | sim_thread_intro
      (STATE: e_src.(Thread.state) = e_tgt.(Thread.state))
      (LOCAL: sim_local e_src.(Thread.local) e_tgt.(Thread.local))
      (SC: TimeMap.le e_src.(Thread.sc) e_tgt.(Thread.sc))
      (MEMORY: sim_memory latests caps
                          e_tgt.(Thread.local).(Local.promises)
                          e_src.(Thread.memory) e_tgt.(Thread.memory))
  .


  Definition sim_promises_get_src := PFStep.sim_promises_get_src.

  Lemma sim_memory_get_src
        latests caps
        promises_src promises_tgt
        mem_src mem_tgt
        loc from to msg_src
        (PROMISES: sim_promises promises_src promises_tgt)
        (MEM: sim_memory latests caps promises_tgt mem_src mem_tgt)
        (LE_SRC: Memory.le promises_src mem_src)
        (LE_TGT: Memory.le promises_tgt mem_tgt)
        (GET_SRC: Memory.get loc to mem_src = Some (from, msg_src)):
    exists msg_tgt,
      <<GET_TGT: Memory.get loc to mem_tgt = Some (from, msg_tgt)>> /\
      <<MSG: __guard__ (msg_src = Message.half \/ sim_message msg_src msg_tgt)>>.
  Proof.
    inv PROMISES. inv MEM.
    destruct (Memory.get loc to promises_tgt) as [[f m]|] eqn:GETP.
    - exploit LE_TGT; eauto. i.
      exploit COMPLETE; eauto. i. des.
      exploit LE_SRC; eauto. i.
      rewrite GET_SRC in x1. inv x1.
      esplits; eauto. unguard. des; eauto.
    - destruct (Time.eq_dec to (caps loc)).
      + subst. specialize (CAPS loc). i. des.
        rewrite GET_SRC in CAP_SRC. inv CAP_SRC.
        esplits; eauto.
        unguard. unfold cap_src in *. des_ifs; eauto.
      + exploit SOUND0; eauto. i. des.
        unguard. esplits; eauto.
  Qed.

  Lemma sim_memory_get_tgt
        latests caps
        promises_src promises_tgt
        mem_src mem_tgt
        loc from to msg_tgt
        (PROMISES: sim_promises promises_src promises_tgt)
        (MEM: sim_memory latests caps promises_tgt mem_src mem_tgt)
        (LE_SRC: Memory.le promises_src mem_src)
        (LE_TGT: Memory.le promises_tgt mem_tgt)
        (GET_TGT: Memory.get loc to mem_tgt = Some (from, msg_tgt)):
    exists msg_src,
      <<GET_SRC: Memory.get loc to mem_src = Some (from, msg_src)>> /\
      <<MSG: __guard__ (msg_src = Message.half \/ sim_message msg_src msg_tgt)>>.
  Proof.
    inv PROMISES. inv MEM.
    destruct (Memory.get loc to promises_tgt) as [[f m]|] eqn:GETP.
    - exploit LE_TGT; eauto. i.
      rewrite GET_TGT in x. inv x.
      exploit COMPLETE; eauto. i. des.
      exploit LE_SRC; eauto. i.
      esplits; eauto. unguard. des; eauto.
    - destruct (Time.eq_dec to (caps loc)).
      + subst. specialize (CAPS loc). des.
        rewrite GET_TGT in CAP_TGT. inv CAP_TGT.
        esplits; eauto.
        unguard. unfold cap_src in *. des_ifs; eauto.
      + exploit COMPLETE0; eauto. i. des.
        unguard. esplits; eauto.
  Qed.

  Lemma promise
        msg_src
        latests caps
        promises1_src mem1_src
        promises1_tgt mem1_tgt loc from to msg_tgt promises2_tgt mem2_tgt kind_tgt
        (PROMISES1: sim_promises promises1_src promises1_tgt)
        (MEM1: sim_memory latests caps promises1_tgt mem1_src mem1_tgt)
        (LE1_SRC: Memory.le promises1_src mem1_src)
        (LE1_TGT: Memory.le promises1_tgt mem1_tgt)
        (CLOSED1_SRC: Memory.closed mem1_src)
        (CLOSED1_TGT: Memory.closed mem1_tgt)
        (PROMISE_TGT: Memory.promise promises1_tgt mem1_tgt loc from to msg_tgt promises2_tgt mem2_tgt kind_tgt)
        (MSG_WF_SRC: Message.wf msg_src)
        (MSG_TO_SRC: Memory.message_to msg_src loc to):
    exists promises2_src mem2_src kind_src,
      <<PROMISE_SRC: Memory.promise promises1_src mem1_src loc from to msg_src promises2_src mem2_src kind_src>> /\
      <<HALF: msg_src = Message.half ->
              <<PROMISES2: sim_promises promises2_src promises2_tgt>> /\
              <<MEM2: sim_memory latests caps promises2_tgt mem2_src mem2_tgt>>>> /\
      <<KIND: Memory.op_kind_match kind_src kind_tgt>>.
  Proof.
    inv PROMISE_TGT.
    - (* add *)
      exploit (@Memory.add_exists mem1_src loc from to msg_src); eauto.
      { ii. exploit sim_memory_get_src; eauto. i. des.
        inv MEM. inv ADD. eapply DISJOINT; eauto. }
      { inv MEM. inv ADD. ss. }
      i. des.
      exploit Memory.add_exists_le; try eapply x0; eauto. i. des.
      esplits; eauto; [|econs].
      i. subst. split; econs; i.
      + erewrite Memory.add_o; eauto. condtac; ss.
        * des. subst.
          revert GET_SRC. erewrite Memory.add_o; eauto. condtac; ss; i.
          inv GET_SRC. eauto.
        * revert GET_SRC. erewrite Memory.add_o; eauto. condtac; ss; i.
          inv PROMISES1. eauto.
      + erewrite Memory.add_o; eauto. condtac; ss.
        * des. subst.
          revert GET_TGT. erewrite Memory.add_o; eauto. condtac; ss; i.
          inv GET_TGT. unguard. esplits; eauto.
        * revert GET_TGT. erewrite Memory.add_o; eauto. condtac; ss; i.
          inv PROMISES1. eauto.
      + exploit Memory.add_get0; try exact PROMISES. i. des.
        erewrite Memory.add_o; eauto. condtac; ss.
        * des. subst. congr.
        * revert GET_SRC. erewrite Memory.add_o; eauto. condtac; ss; i.
          inv MEM1. eapply SOUND; eauto.
          destruct (Memory.get loc0 to0 promises1_tgt) as [[]|] eqn:GETP1; eauto.
          exploit Memory.add_get1; try exact GETP1; eauto. i. congr.
      + exploit Memory.add_get0; try exact PROMISES. i. des.
        erewrite Memory.add_o; eauto. condtac; ss.
        * des. subst. congr.
        * revert GET_TGT. erewrite Memory.add_o; eauto. condtac; ss; i.
          inv MEM1. eapply COMPLETE; eauto.
          destruct (Memory.get loc0 to0 promises1_tgt) as [[]|] eqn:GETP1; eauto.
          exploit Memory.add_get1; try exact GETP1; eauto. i. congr.
      + apply MEM1.
      + erewrite Memory.add_o; eauto. condtac; ss.
        * des. subst.
          exploit Memory.add_get0; try exact MEM. i. des.
          inv MEM1. specialize (CAPS loc). des. congr.
        * inv MEM1. specialize (CAPP loc0). ss.
      + inv MEM1. clear SOUND COMPLETE.
        exploit Memory.add_get0; try exact MEM. i. des.
        erewrite Memory.add_o; eauto. condtac; ss.
        * des. subst.
          specialize (CAPS loc). des. congr.
        * guardH o.
          specialize (CAPS loc0). des.
          destruct (loc_ts_eq_dec (loc, to) (loc0, (caps loc0))).
          { ss. des. subst. congr. }
          { ss. guardH o0. esplits; eauto.
            - erewrite Memory.add_o; eauto. condtac; [|eauto].
              ss. des. subst. congr.
            - erewrite Memory.add_o; eauto. condtac; [|eauto].
              ss. des. subst. congr.
            - unfold cap_src in *. des_ifs; eauto.
              + revert Heq. erewrite Memory.add_o; eauto. condtac; ss; congr.
              + revert Heq. erewrite Memory.add_o; eauto. condtac; ss; congr. }
    - (* split *)
      exploit Memory.split_get0; try exact PROMISES. i. des.
      inv PROMISES1. exploit COMPLETE; try exact GET0. i. des.
      exploit (@Memory.split_exists promises1_src loc from to ts3 msg_src Message.half); eauto.
      { inv MEM. inv SPLIT. ss. }
      { inv MEM. inv SPLIT. ss. }
      i. des.
      exploit Memory.split_exists_le; try exact x1; eauto. i. des.
      esplits; eauto; [|econs].
      i. subst. split; econs; i.
      + erewrite Memory.split_o; eauto. repeat condtac; ss.
        * des. subst.
          revert GET_SRC. erewrite Memory.split_o; eauto. repeat condtac; ss; i.
          inv GET_SRC. eauto.
        * guardH o. des. subst.
          revert GET_SRC. erewrite Memory.split_o; eauto. repeat condtac; ss; i.
          inv GET_SRC. eauto.
        * revert GET_SRC. erewrite Memory.split_o; eauto. repeat condtac; ss; i.
          eauto.
      + erewrite Memory.split_o; eauto. repeat condtac; ss.
        * des. subst.
          revert GET_TGT. erewrite Memory.split_o; eauto. repeat condtac; ss; i.
          inv GET_TGT. unguard. esplits; eauto.
        * guardH o. des. subst.
          revert GET_TGT. erewrite Memory.split_o; eauto. repeat condtac; ss; i.
          inv GET_TGT. unguard. esplits; eauto.
        * revert GET_TGT. erewrite Memory.split_o; eauto. repeat condtac; ss; i.
          eauto.
      + erewrite Memory.split_o; eauto. repeat condtac; ss.
        * des. subst. congr.
        * guardH o. des. subst. congr.
        * revert GET_SRC. erewrite Memory.split_o; eauto. repeat condtac; ss; i.
          guardH o. guardH o0. guardH o1. guardH o2.
          inv MEM1. eapply SOUND0; eauto.
          destruct (Memory.get loc0 to0 promises1_tgt) as [[]|] eqn:GETP1; eauto.
          exploit Memory.split_get1; try exact GETP1; eauto. i. des. congr.
      + erewrite Memory.split_o; eauto. repeat condtac; ss.
        * des. subst. congr.
        * guardH o. des. subst. congr.
        * revert GET_TGT. erewrite Memory.split_o; eauto. repeat condtac; ss; i.
          guardH o. guardH o0. guardH o1. guardH o2.
          inv MEM1. eapply COMPLETE0; eauto.
          destruct (Memory.get loc0 to0 promises1_tgt) as [[]|] eqn:GETP1; eauto.
          exploit Memory.split_get1; try exact GETP1; eauto. i. des. congr.
      + apply MEM1.
      + erewrite Memory.split_o; eauto. repeat condtac; ss.
        * des. subst.
          exploit Memory.split_get0; try exact MEM. i. des.
          inv MEM1. specialize (CAPS loc). des. congr.
        * guardH o. des. subst.
          exploit Memory.split_get0; try exact PROMISES. i. des.
          inv MEM1. specialize (CAPP loc). congr.
        * inv MEM1. specialize (CAPP loc0). ss.
      + inv MEM1. clear SOUND COMPLETE SOUND0 COMPLETE0.
        exploit Memory.split_get0; try exact MEM. i. des.
        specialize (CAPS loc0). des.
        erewrite Memory.split_o; eauto. repeat condtac; ss.
        * des. subst. congr.
        * des; subst; ss.
          rewrite LATEST in GET4. inv GET4.
          assert (TO: to <> caps loc).
          { ii. subst. inv MEM. inv SPLIT.
            specialize (LATESTS loc). rewrite LATESTS in TS23. timetac. }
          esplits; eauto.
          { erewrite Memory.split_o; eauto. repeat condtac; [| |eauto].
            - ss. des. subst. congr.
            - guardH o0. ss. des.
              specialize (LATESTS loc). rewrite a0 in LATESTS. timetac. }
          { erewrite Memory.split_o; eauto. repeat condtac; [| |eauto].
            - ss. des. subst. congr.
            - guardH o0. ss. des.
              specialize (LATESTS loc). rewrite a0 in LATESTS. timetac. }
          { unfold cap_src in *. des_ifs; eauto. }
        * destruct (loc_ts_eq_dec (loc, to) (loc0, (caps loc0))); ss.
          { des; subst; congr. }
          destruct (loc_ts_eq_dec (loc, ts3) (loc0, (caps loc0))); ss.
          { des; subst; ss. esplits; eauto.
            - erewrite Memory.split_o; eauto. repeat condtac; [|eauto|].
              + ss. des; subst; congr.
              + ss. des; subst; congr.
            - erewrite Memory.split_o; eauto. repeat condtac.
              + ss. des; subst; congr.
              + ss. rewrite CAP_TGT in GET4. inv GET4. ss.
              + ss. des; subst; congr.
            - unfold cap_src in *. des_ifs; eauto.
              + revert Heq. erewrite Memory.split_o; eauto. repeat condtac; ss; congr.
              + revert Heq. erewrite Memory.split_o; eauto. repeat condtac; ss.
                guardH o2. guardH o3.
                exploit Memory.split_get0; try exact x2. i. des.
                rewrite CAP_SRC in GET8. inv GET8. inv MSG. }
          { guardH o. guardH o0. guardH o1. guardH o2.
            esplits; eauto.
            - erewrite Memory.split_o; eauto. repeat condtac; [| |eauto]; ss.
              + des. subst. congr.
              + unguard. des; subst; congr.
            - erewrite Memory.split_o; eauto. repeat condtac; [| |eauto]; ss.
              + des. subst. congr.
              + unguard. des; subst; congr.
            - unfold cap_src in *. des_ifs; eauto.
              + revert Heq. erewrite Memory.split_o; eauto. repeat condtac; ss; congr.
              + revert Heq. erewrite Memory.split_o; eauto. repeat condtac; ss; congr. }
    - (* lower *)
      exploit Memory.lower_get0; try exact PROMISES. i. des.
      inv PROMISES1. exploit COMPLETE; eauto. i. des.
      exploit (@Memory.lower_exists promises1_src loc from to Message.half msg_src); eauto.
      { inv MEM. inv LOWER. ss. }
      i. des.
      exploit Memory.lower_exists_le; try eapply x1; eauto. i. des.
      esplits; eauto; [|econs].
      i. subst. split; econs; i.
      + erewrite Memory.lower_o; eauto. condtac; ss.
        * des. subst.
          revert GET_SRC. erewrite Memory.lower_o; eauto. condtac; ss; i.
          inv GET_SRC. eauto.
        * revert GET_SRC. erewrite Memory.lower_o; eauto. condtac; ss; i.
          eauto.
      + erewrite Memory.lower_o; eauto. condtac; ss.
        * des. subst.
          revert GET_TGT. erewrite Memory.lower_o; eauto. condtac; ss; i.
          inv GET_TGT. unguard. esplits; eauto.
        * revert GET_TGT. erewrite Memory.lower_o; eauto. condtac; ss; i.
          eauto.
      + erewrite Memory.lower_o; eauto. condtac; ss.
        * des. subst. congr.
        * revert GET_SRC. erewrite Memory.lower_o; eauto. condtac; ss; i.
          guardH o. guardH o0.
          inv MEM1. eapply SOUND0; eauto.
          destruct (Memory.get loc0 to0 promises1_tgt) as [[]|] eqn:GETP1; eauto.
          exploit Memory.lower_get1; try exact GETP1; eauto. i. des. congr.
      + erewrite Memory.lower_o; eauto. condtac; ss.
        * des. subst. congr.
        * revert GET_TGT. erewrite Memory.lower_o; eauto. condtac; ss; i.
          guardH o. guardH o0.
          inv MEM1. eapply COMPLETE0; eauto.
          destruct (Memory.get loc0 to0 promises1_tgt) as [[]|] eqn:GETP1; eauto.
          exploit Memory.lower_get1; try exact GETP1; eauto. i. des. congr.
      + apply MEM1.
      + erewrite Memory.lower_o; eauto. condtac; ss.
        * des. subst.
          exploit Memory.lower_get0; try exact PROMISES. i. des.
          inv MEM1. specialize (CAPP loc). congr.
        * inv MEM1. specialize (CAPP loc0). ss.
      + inv MEM1. clear SOUND COMPLETE SOUND0 COMPLETE0.
        exploit Memory.lower_get0; try exact MEM. i. des.
        specialize (CAPS loc0). des.
        erewrite Memory.lower_o; eauto. condtac; ss.
        * des. subst.
          rewrite LATEST in GET1. inv GET1. inv MSG_LE0.
          esplits; eauto.
          { erewrite Memory.lower_o; eauto. condtac; [|eauto].
            ss. des. specialize (LATESTS loc).
            rewrite a0 in *. timetac. }
          { erewrite Memory.lower_o; eauto. condtac; [|eauto].
            ss. des. specialize (LATESTS loc).
            rewrite a0 in *. timetac. }
          { unfold cap_src in *. des_ifs; eauto. }
        * guardH o.
          destruct (loc_ts_eq_dec (loc, to) (loc0, (caps loc0))).
          { ss. des. subst.
            rewrite CAP_TGT in GET1. inv GET1. inv MSG_LE0.
            esplits; eauto.
            - erewrite Memory.lower_o; eauto. condtac; [eauto|].
              ss. des; congr.
            - unfold cap_src in *. des_ifs; eauto.
              + destruct p.
                exploit Memory.lower_get1; try exact Heq0; eauto. i. des. congr.
              + exploit Memory.lower_get1; try exact CAP_SRC; eauto. i. des.
                exploit Memory.lower_get0; try exact x2. i. des.
                inv MSG. inv MSG_LE0. congr. }
          { ss. guardH o0.
            esplits; eauto.
            - erewrite Memory.lower_o; eauto. condtac;[|eauto].
              ss. unguard. des; subst; ss.
            - erewrite Memory.lower_o; eauto. condtac;[|eauto].
              ss. unguard. des; subst; ss.
            - unfold cap_src in *. des_ifs; eauto.
              + revert Heq. erewrite Memory.lower_o; eauto. condtac; ss. congr.
              + destruct p.
                exploit Memory.lower_get1; try exact Heq0; eauto. i. des. congr. }
  Qed.

  Lemma promise_step
        latests caps
        lc1_src mem1_src
        lc1_tgt mem1_tgt loc from to msg lc2_tgt mem2_tgt kind_tgt
        (LOCAL1: sim_local lc1_src lc1_tgt)
        (MEM1: sim_memory latests caps lc1_tgt.(Local.promises) mem1_src mem1_tgt)
        (WF1_SRC: Local.wf lc1_src mem1_src)
        (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
        (CLOSED1_SRC: Memory.closed mem1_src)
        (CLOSED1_TGT: Memory.closed mem1_tgt)
        (STEP_TGT: Local.promise_step lc1_tgt mem1_tgt loc from to msg lc2_tgt mem2_tgt kind_tgt):
    exists lc2_src mem2_src kind_src,
      <<STEP_SRC: Local.promise_step lc1_src mem1_src loc from to Message.half lc2_src mem2_src kind_src>> /\
      <<LOCAL2: sim_local lc2_src lc2_tgt>> /\
      <<MEM2: sim_memory latests caps lc2_tgt.(Local.promises) mem2_src mem2_tgt>>.
  Proof.
    inv STEP_TGT.
    exploit promise; try exact PROMISE; eauto.
    { apply LOCAL1. }
    { apply WF1_SRC. }
    { apply WF1_TGT. }
    { econs. }
    i. des.
    exploit HALF; eauto. i. des.
    esplits; eauto. econs; eauto. apply LOCAL1.
  Qed.

  Definition read_promise_None := PFStep.read_promise_None.

  Lemma read_cap
        latests caps mem1_src
        lc1 mem1_tgt loc val released ord lc2
        (MEM1: sim_memory latests caps lc1.(Local.promises) mem1_src mem1_tgt)
        (WF1: Local.wf lc1 mem1_tgt)
        (STEP: Local.read_step lc1 mem1_tgt loc (caps loc) val released ord lc2)
        (CONS: promise_consistent lc2):
    Memory.get loc (latests loc) lc1.(Local.promises) = None.
  Proof.
    destruct (Memory.get loc (latests loc) (Local.promises lc1)) as [[]|] eqn:PROMISE; ss.
    exfalso.
    inv STEP. exploit CONS; eauto. i.
    eapply Time.lt_strorder.
    etrans; eauto.
    inv MEM1. clear SOUND COMPLETE CAPS.
    specialize (LATESTS loc).
    eapply TimeFacts.lt_le_lt; eauto. ss.
    etrans; [|apply Time.join_l]. etrans; [|apply Time.join_r].
    unfold View.singleton_ur_if. condtac; ss.
    - unfold TimeMap.singleton.
      exploit LocFun.add_spec_eq. unfold LocFun.find. i.
      rewrite x1. refl.
    - unfold TimeMap.singleton.
      exploit LocFun.add_spec_eq. unfold LocFun.find. i.
      rewrite x1. refl.
  Qed.

  Lemma read_step
        latests caps
        lc1_src mem1_src
        lc1_tgt mem1_tgt loc to val released_tgt ord lc2_tgt
        (LOCAL1: sim_local lc1_src lc1_tgt)
        (MEM1: sim_memory latests caps lc1_tgt.(Local.promises) mem1_src mem1_tgt)
        (WF1_SRC: Local.wf lc1_src mem1_src)
        (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
        (CLOSED1_SRC: Memory.closed mem1_src)
        (CLOSED1_TGT: Memory.closed mem1_tgt)
        (STEP_TGT: Local.read_step lc1_tgt mem1_tgt loc to val released_tgt ord lc2_tgt)
        (CONS_TGT: promise_consistent lc2_tgt):
    exists released_src lc2_src,
      <<STEP_SRC: Local.read_step lc1_src mem1_src loc to val released_src ord lc2_src>> /\
      <<LOCAL2: sim_local lc2_src lc2_tgt>> /\
      <<RELEASED: View.opt_le released_src released_tgt>>.
  Proof.
    exploit read_promise_None; try exact STEP_TGT; eauto. i.
    destruct (Time.eq_dec to (caps loc)).
    - subst. exploit read_cap; eauto. i.
      inv MEM1. clear SOUND COMPLETE LATESTS.
      specialize (CAPS loc). des.
      unfold cap_src in *. rewrite x1 in *. inv MSG.
      inv LOCAL1.
      inv STEP_TGT. rewrite CAP_TGT in GET. inv GET.
      esplits.
      + econs; eauto.
        inv READABLE. inv TVIEW. econs; eauto.
        * etrans; try exact PLN. apply CUR.
        * i. exploit RLX; eauto. i.
          etrans; try exact x. apply CUR.
      + econs; eauto. ss.
        eapply TViewFacts.read_tview_mon; eauto.
        { apply WF1_TGT. }
        { inv CLOSED1_TGT. exploit CLOSED; eauto. i. des.
          inv MSG_WF. ss. }
        { refl. }
      + auto.
    - inv MEM1. inv LOCAL1. inv STEP_TGT.
      exploit COMPLETE; eauto. i. des. inv MSG.
      esplits.
      + econs; eauto.
        inv READABLE. inv TVIEW. econs; eauto.
        * etrans; try exact PLN. apply CUR.
        * i. exploit RLX; eauto. i.
          etrans; try exact x. apply CUR.
      + econs; eauto. ss.
        eapply TViewFacts.read_tview_mon; eauto.
        { apply WF1_TGT. }
        { inv CLOSED1_TGT. exploit CLOSED; eauto. i. des.
          inv MSG_WF. ss. }
        { refl. }
      + auto.
  Qed.

  Lemma promise_remove_sim
        latests caps
        promises1_src mem1_src loc from to msg_src promises2_src mem2_src kind_src
        promises3_src
        promises1_tgt mem1_tgt msg_tgt promises2_tgt mem2_tgt kind_tgt
        promises3_tgt
        (PROMISES1: sim_promises promises1_src promises1_tgt)
        (MEM1: sim_memory latests caps promises1_tgt mem1_src mem1_tgt)
        (LE1_SRC: Memory.le promises1_src mem1_src)
        (LE1_TGT: Memory.le promises1_tgt mem1_tgt)
        (CLOSED1_SRC: Memory.closed mem1_src)
        (CLOSED1_TGT: Memory.closed mem1_tgt)
        (MSG: sim_message msg_src msg_tgt)
        (KIND: Memory.op_kind_match kind_src kind_tgt)
        (PROMISE_SRC: Memory.promise promises1_src mem1_src loc from to msg_src promises2_src mem2_src kind_src)
        (REMOVE_SRC: Memory.remove promises2_src loc from to msg_src promises3_src)
        (PROMISE_TGT: Memory.promise promises1_tgt mem1_tgt loc from to msg_tgt promises2_tgt mem2_tgt kind_tgt)
        (REMOVE_TGT: Memory.remove promises2_tgt loc from to msg_tgt promises3_tgt)
        (TO: to <> latests loc):
    <<PROMISES2: sim_promises promises3_src promises3_tgt>> /\
    <<MEM2: sim_memory latests caps promises3_tgt mem2_src mem2_tgt>>.
  Proof.
    split; econs; i.
    - erewrite Memory.remove_o; eauto. condtac; ss.
      + des. subst.
        revert GET_SRC. erewrite Memory.remove_o; eauto. condtac; ss.
      + revert GET_SRC. erewrite Memory.remove_o; eauto. condtac; ss. i.
        guardH o. guardH o0.
        inv PROMISE_SRC; inv PROMISE_TGT; inv KIND.
        * erewrite Memory.add_o; eauto. condtac; ss.
          revert GET_SRC. erewrite Memory.add_o; eauto. condtac; ss. i.
          inv PROMISES1. eauto.
        * erewrite Memory.split_o; eauto. repeat condtac; ss.
          { guardH o1. des. subst.
            revert GET_SRC. erewrite Memory.split_o; eauto. repeat condtac; ss. i.
            inv GET_SRC. inv PROMISES1. eauto. }
          { guardH o1. guardH o2.
            revert GET_SRC. erewrite Memory.split_o; eauto. repeat condtac; ss. i.
            inv PROMISES1. eauto. }
        * erewrite Memory.lower_o; eauto. condtac; ss.
          revert GET_SRC. erewrite Memory.lower_o; eauto. condtac; ss. i.
          inv PROMISES1. eauto.
    - erewrite Memory.remove_o; eauto. condtac; ss.
      + des. subst.
        revert GET_TGT. erewrite Memory.remove_o; eauto. condtac; ss.
      + revert GET_TGT. erewrite Memory.remove_o; eauto. condtac; ss. i.
        guardH o. guardH o0.
        inv PROMISE_SRC; inv PROMISE_TGT; inv KIND.
        * erewrite Memory.add_o; eauto. condtac; ss.
          revert GET_TGT. erewrite Memory.add_o; eauto. condtac; ss. i.
          inv PROMISES1. eauto.
        * erewrite Memory.split_o; eauto. repeat condtac; ss.
          { guardH o1. des. subst.
            revert GET_TGT. erewrite Memory.split_o; eauto. repeat condtac; ss. i.
            guardH o2.
            exploit Memory.split_get0; try exact PROMISES. i. des.
            exploit sim_promises_get_src; try exact GET0; eauto. i. des. subst.
            inv GET_TGT. inv PROMISES1. eauto. }
          { guardH o1. guardH o2.
            revert GET_TGT. erewrite Memory.split_o; eauto. repeat condtac; ss. i.
            inv PROMISES1. eauto. }
        * erewrite Memory.lower_o; eauto. condtac; ss.
          revert GET_TGT. erewrite Memory.lower_o; eauto. condtac; ss. i.
          inv PROMISES1. eauto.
    - revert GETP. erewrite Memory.remove_o; eauto. condtac; ss; i.
      + des. subst.
        exploit Memory.promise_get0; try exact PROMISE_SRC. i. des.
        exploit Memory.promise_get0; try exact PROMISE_TGT. i. des.
        rewrite GET_MEM, GET_MEM0 in *. inv GET_SRC. eauto.
      + guardH o.
        inv PROMISE_SRC; inv PROMISE_TGT; inv KIND.
        * erewrite Memory.add_o; eauto. condtac; ss.
          revert GET_SRC. erewrite Memory.add_o; eauto. condtac; ss. i.
          revert GETP. erewrite Memory.add_o; eauto. condtac; ss. i.
          inv MEM1. eauto.
        * erewrite Memory.split_o; eauto. repeat condtac; ss.
          { guardH o0. des. subst.
            revert GET_SRC. erewrite Memory.split_o; eauto. repeat condtac; ss. i.
            revert GETP. erewrite Memory.split_o; eauto. repeat condtac; ss. }
          { guardH o0. guardH o1.
            revert GET_SRC. erewrite Memory.split_o; eauto. repeat condtac; ss. i.
            revert GETP. erewrite Memory.split_o; eauto. repeat condtac; ss. i.
            inv MEM1. eauto. }
        * erewrite Memory.lower_o; eauto. condtac; ss.
          revert GET_SRC. erewrite Memory.lower_o; eauto. condtac; ss. i.
          revert GETP. erewrite Memory.lower_o; eauto. condtac; ss. i.
          inv MEM1. eauto.
    - revert GETP. erewrite Memory.remove_o; eauto. condtac; ss; i.
      + des. subst.
        exploit Memory.promise_get0; try exact PROMISE_SRC. i. des.
        exploit Memory.promise_get0; try exact PROMISE_TGT. i. des.
        rewrite GET_MEM, GET_MEM0 in *. inv GET_TGT. eauto.
      + guardH o.
        inv PROMISE_SRC; inv PROMISE_TGT; inv KIND.
        * erewrite Memory.add_o; eauto. condtac; ss.
          revert GET_TGT. erewrite Memory.add_o; eauto. condtac; ss. i.
          revert GETP. erewrite Memory.add_o; eauto. condtac; ss. i.
          inv MEM1. eauto.
        * erewrite Memory.split_o; eauto. repeat condtac; ss.
          { guardH o0. des. subst.
            revert GET_TGT. erewrite Memory.split_o; eauto. repeat condtac; ss. i.
            revert GETP. erewrite Memory.split_o; eauto. repeat condtac; ss. }
          { guardH o0. guardH o1.
            revert GET_TGT. erewrite Memory.split_o; eauto. repeat condtac; ss. i.
            revert GETP. erewrite Memory.split_o; eauto. repeat condtac; ss. i.
            inv MEM1. eauto. }
        * erewrite Memory.lower_o; eauto. condtac; ss.
          revert GET_TGT. erewrite Memory.lower_o; eauto. condtac; ss. i.
          revert GETP. erewrite Memory.lower_o; eauto. condtac; ss. i.
          inv MEM1. eauto.
    - apply MEM1.
    - erewrite Memory.remove_o; eauto. condtac; ss.
      guardH o. inv PROMISE_SRC; inv PROMISE_TGT; inv KIND.
      + erewrite Memory.add_o; eauto. condtac; ss.
        inv MEM1. eauto.
      + erewrite Memory.split_o; eauto. repeat condtac; ss.
        * guardH o0. des. subst.
          exploit Memory.split_get0; try exact PROMISES0. i. des.
          inv MEM1. specialize (CAPP loc). congr.
        * inv MEM1. eauto.
      + erewrite Memory.lower_o; eauto. condtac; ss.
        inv MEM1. eauto.
    - inv MEM1. clear SOUND COMPLETE.
      specialize (CAPS loc0). des.
      inv PROMISE_SRC; inv PROMISE_TGT; inv KIND.
      + erewrite Memory.add_o; eauto. condtac; ss.
        * des. subst. congr.
        * guardH o. esplits; eauto.
          { erewrite Memory.add_o; eauto. condtac; [|eauto].
            ss. des. subst.
            exploit Memory.add_get0; try exact MEM. i. des. congr. }
          { erewrite Memory.add_o; eauto. condtac; [|eauto].
            ss. des. subst.
            exploit Memory.add_get0; try exact MEM. i. des. congr. }
          { unfold cap_src in *. des_ifs; eauto.
            - revert Heq. erewrite Memory.remove_o; eauto. condtac; ss.
              erewrite Memory.add_o; eauto. condtac; ss. congr.
            - revert Heq. erewrite Memory.remove_o; eauto. condtac; ss.
              erewrite Memory.add_o; eauto. condtac; ss. congr. }
      + erewrite Memory.split_o; eauto. repeat condtac; ss.
        * des. subst. congr.
        * guardH o. des. subst.
          exploit Memory.split_get0; try exact MEM0. i. des.
          rewrite LATEST in *. inv GET0.
          esplits; eauto.
          { erewrite Memory.split_o; eauto. repeat condtac; [| |eauto]; ss.
            - des. subst.
              inv MEM0. inv SPLIT. specialize (LATESTS loc).
              rewrite LATESTS in TS23. timetac.
            - guardH o0. des. subst.
              specialize (LATESTS loc). rewrite a0 in *. timetac. }
          { erewrite Memory.split_o; eauto. repeat condtac; [| |eauto]; ss.
            - des. subst.
              inv MEM0. inv SPLIT. specialize (LATESTS loc).
              rewrite LATESTS in TS23. timetac.
            - guardH o0. des. subst.
              specialize (LATESTS loc). rewrite a0 in *. timetac. }
          { unfold cap_src in *. des_ifs; eauto.
            - revert Heq. erewrite Memory.remove_o; eauto. condtac; ss.
              erewrite Memory.split_o; eauto. repeat condtac; ss.
              exploit Memory.split_get0; try exact PROMISES0. i. des; congr.
            - revert Heq. erewrite Memory.remove_o; eauto. condtac; ss.
              erewrite Memory.split_o; eauto. repeat condtac; ss. }
        * guardH o. guardH o0.
          exploit Memory.split_get0; try exact MEM0. i. des.
          esplits; eauto.
          { erewrite Memory.split_o; eauto. repeat condtac; [| |eauto]; ss.
            - des. subst.
              exploit Memory.split_get0; try exact MEM0. i. des. congr.
            - guardH o1. des. subst.
              exploit Memory.split_get0; try exact PROMISES0. i. des. congr. }
          { erewrite Memory.split_o; eauto. repeat condtac; [| |eauto]; ss.
            - des. subst.
              exploit Memory.split_get0; try exact MEM0. i. des. congr.
            - guardH o1. des. subst.
              exploit Memory.split_get0; try exact PROMISES0. i. des. congr. }
          { unfold cap_src in *. des_ifs; eauto.
            - revert Heq. erewrite Memory.remove_o; eauto. condtac; ss.
              erewrite Memory.split_o; eauto. repeat condtac; ss.
              exploit Memory.split_get0; try exact PROMISES0. i. des; congr.
            - revert Heq. erewrite Memory.remove_o; eauto. condtac; ss.
              erewrite Memory.split_o; eauto. repeat condtac; ss. congr. }
      + erewrite Memory.lower_o; eauto. condtac; ss.
        * des. subst. congr.
        * guardH o. esplits; eauto.
          { erewrite Memory.lower_o; eauto. condtac; [|eauto].
            ss. des. subst.
            exploit Memory.lower_get0; try exact PROMISES0. i. des.
            rewrite CAPP in *. congr. }
          { erewrite Memory.lower_o; eauto. condtac; [|eauto].
            ss. des. subst.
            exploit Memory.lower_get0; try exact PROMISES0. i. des.
            rewrite CAPP in *. congr. }
          { unfold cap_src in *. des_ifs; eauto.
            - revert Heq. erewrite Memory.remove_o; eauto. condtac; ss.
              erewrite Memory.lower_o; eauto. condtac; ss. congr.
            - revert Heq. erewrite Memory.remove_o; eauto. condtac; ss.
              erewrite Memory.lower_o; eauto. condtac; ss. congr. }
  Qed.

  Lemma promise_remove_sim_cap
        latests caps
        promises1_src mem1_src loc from msg_src promises2_src mem2_src kind_src
        promises3_src
        promises1_tgt mem1_tgt msg_tgt promises2_tgt mem2_tgt kind_tgt
        promises3_tgt
        (PROMISES1: sim_promises promises1_src promises1_tgt)
        (MEM1: sim_memory latests caps promises1_tgt mem1_src mem1_tgt)
        (LE1_SRC: Memory.le promises1_src mem1_src)
        (LE1_TGT: Memory.le promises1_tgt mem1_tgt)
        (CLOSED1_SRC: Memory.closed mem1_src)
        (CLOSED1_TGT: Memory.closed mem1_tgt)
        (MSG: sim_message msg_src msg_tgt)
        (KIND: Memory.op_kind_match kind_src kind_tgt)
        (PROMISE_SRC: Memory.promise promises1_src mem1_src loc from (latests loc) msg_src promises2_src mem2_src kind_src)
        (REMOVE_SRC: Memory.remove promises2_src loc from (latests loc) msg_src promises3_src)
        (PROMISE_TGT: Memory.promise promises1_tgt mem1_tgt loc from (latests loc) msg_tgt promises2_tgt mem2_tgt kind_tgt)
        (REMOVE_TGT: Memory.remove promises2_tgt loc from (latests loc) msg_tgt promises3_tgt):
    exists from_cap val mem3_src,
      <<MSG: sim_message (Message.full val None) msg_tgt>> /\
      <<LOWER: Memory.lower mem2_src loc from_cap (caps loc) Message.half (Message.full val None) mem3_src>> /\
      <<PROMISES2: sim_promises promises3_src promises3_tgt>> /\
      <<MEM2: sim_memory latests caps promises3_tgt mem3_src mem2_tgt>>.
  Proof.
    inv PROMISE_SRC; inv PROMISE_TGT; inv KIND.
    { inv MEM1. specialize (CAPS loc). des.
      exploit Memory.add_get0; try exact MEM0. i. des. congr. }
    { inv MEM1. specialize (CAPS loc). des.
      exploit Memory.split_get0; try exact MEM0. i. des. congr. }
    dup MEM1. inv MEM2. clear SOUND COMPLETE LATESTS CAPP.
    specialize (CAPS loc). des.
    exploit Memory.lower_get0; try exact MEM0. i. des.
    rewrite LATEST in *. inv GET. inv MSG_LE. inv MSG. clear GET0.
    exploit Memory.lower_get0; try exact PROMISES0. i. des.
    unfold cap_src in *. rewrite GET in *. subst.
    clear GET GET0 MSG_LE.
    exploit (@Memory.lower_exists mem2_src loc from0 (caps loc) Message.half (Message.full val None)).
    { erewrite Memory.lower_o; eauto. condtac; ss. des.
      inv MEM1. specialize (LATESTS loc).
      rewrite a0 in *. timetac. }
    { exploit Memory.get_ts; try exact CAP_SRC. i. des; ss.
      inv MEM1. specialize (LATESTS loc).
      rewrite x1 in *. inv LATESTS. }
    { econs. ss. }
    { econs. }
    i. des.
    rename x0 into LOWER. rename mem2 into mem3_src.
    esplits; eauto; econs; ss; i.
    - erewrite Memory.remove_o; eauto. condtac; ss.
      + des. subst.
        revert GET_SRC. erewrite Memory.remove_o; eauto. condtac; ss.
      + revert GET_SRC. erewrite Memory.remove_o; eauto. condtac; ss. i.
        guardH o. guardH o0.
        erewrite Memory.lower_o; eauto. condtac; ss.
        revert GET_SRC. erewrite Memory.lower_o; eauto. condtac; ss. i.
        inv PROMISES1. eauto.
    - erewrite Memory.remove_o; eauto. condtac; ss.
      + des. subst.
        revert GET_TGT. erewrite Memory.remove_o; eauto. condtac; ss.
      + revert GET_TGT. erewrite Memory.remove_o; eauto. condtac; ss. i.
        guardH o. guardH o0.
        erewrite Memory.lower_o; eauto. condtac; ss.
        revert GET_TGT. erewrite Memory.lower_o; eauto. condtac; ss. i.
        inv PROMISES1. eauto.
    - revert GETP. erewrite Memory.remove_o; eauto. condtac; ss; i.
      + des. subst.
        revert GET_SRC.
        erewrite Memory.lower_o; eauto. condtac; des; ss.
        erewrite Memory.lower_o; eauto. condtac; des; ss. i. inv GET_SRC.
        erewrite Memory.lower_o; eauto. condtac; des; ss.
        esplits; eauto. econs. ss.
      + guardH o.
        erewrite Memory.lower_o; eauto. condtac; ss.
        revert GET_SRC. erewrite Memory.lower_o; eauto. condtac; ss.
        { guardH o0. des. subst. ss. }
        erewrite Memory.lower_o; eauto. condtac; ss; i.
        revert GETP. erewrite Memory.lower_o; eauto. condtac; ss. i.
        inv MEM1. eauto.
    - revert GETP. erewrite Memory.remove_o; eauto. condtac; ss; i.
      + des. subst.
        revert GET_TGT.
        erewrite Memory.lower_o; eauto. condtac; des; ss. i. inv GET_TGT.
        erewrite Memory.lower_o; eauto. condtac; des; ss. i.
        erewrite Memory.lower_o; eauto. condtac; des; ss.
        esplits; eauto. econs. ss.
      + guardH o.
        erewrite Memory.lower_o; eauto. condtac; ss.
        { des. subst. ss. }
        erewrite Memory.lower_o; eauto. condtac; ss.
        revert GET_TGT. erewrite Memory.lower_o; eauto. condtac; ss. i.
        revert GETP. erewrite Memory.lower_o; eauto. condtac; ss. i.
        inv MEM1. eauto.
    - apply MEM1.
    - erewrite Memory.remove_o; eauto. condtac; ss.
      erewrite Memory.lower_o; eauto. condtac; ss.
      inv MEM1. eauto.
    - erewrite Memory.lower_o; eauto. condtac; ss.
      + inv MEM1. clear SOUND COMPLETE CAPS.
        des. subst. specialize (LATESTS loc).
        exploit Memory.lower_get0; try exact LOWER. i. des.
        esplits; eauto.
        * erewrite Memory.lower_o; eauto. condtac; [|eauto].
          ss. des. rewrite a1 in *. timetac.
        * unfold cap_src in *. des_ifs; eauto.
          { revert Heq. erewrite Memory.remove_o; eauto. condtac; ss. }
          { econs. ss. }
      + destruct (Loc.eq_dec loc0 loc).
        { subst. des; ss. }
        clear o COND.
        inv MEM1. clear SOUND COMPLETE.
        specialize (CAPS loc0). des.
        esplits; eauto.
        * erewrite Memory.lower_o; eauto. condtac.
          { simpl in a. des. congr. }
          erewrite Memory.lower_o; eauto. condtac; [|eauto].
          ss. guardH o. des. ss.
        * erewrite Memory.lower_o; eauto. condtac; [|eauto].
          ss. des. congr.
        * unfold cap_src in *. des_ifs; eauto.
          { revert Heq.
            erewrite Memory.remove_o; eauto. condtac; ss.
            erewrite Memory.lower_o; eauto. condtac; ss. congr. }
          { revert Heq.
            erewrite Memory.remove_o; eauto. condtac; ss.
            - des. subst. congr.
            - erewrite Memory.lower_o; eauto. condtac; ss. congr. }
  Qed.

  Definition view_opt_le_time_le := PFStep.view_opt_le_time_le.

  Lemma write_step
        latests caps
        lc1_src sc1_src mem1_src releasedm_src
        lc1_tgt sc1_tgt mem1_tgt loc from to val releasedm_tgt released_tgt ord lc2_tgt sc2_tgt mem2_tgt kind_tgt
        (LOCAL1: sim_local lc1_src lc1_tgt)
        (SC1: TimeMap.le sc1_src sc1_tgt)
        (MEM1: sim_memory latests caps lc1_tgt.(Local.promises) mem1_src mem1_tgt)
        (WF1_SRC: Local.wf lc1_src mem1_src)
        (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
        (SC1_SRC: Memory.closed_timemap sc1_src mem1_src)
        (SC1_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
        (CLOSED1_SRC: Memory.closed mem1_src)
        (CLOSED1_TGT: Memory.closed mem1_tgt)
        (RELEASEDM_SRC: View.opt_wf releasedm_src)
        (RELEASEDM_TGT: View.opt_wf releasedm_tgt)
        (RELEASEDM: View.opt_le releasedm_src releasedm_tgt)
        (STEP_TGT: Local.write_step lc1_tgt sc1_tgt mem1_tgt loc from to val
                                    releasedm_tgt released_tgt ord lc2_tgt sc2_tgt mem2_tgt kind_tgt)
        (TO: to <> latests loc):
    exists released_src lc2_src sc2_src mem2_src kind_src,
      <<STEP_SRC: Local.write_step lc1_src sc1_src mem1_src loc from to val
                                   releasedm_src released_src ord lc2_src sc2_src mem2_src kind_src>> /\
      <<LOCAL2: sim_local lc2_src lc2_tgt>> /\
      <<SC2: TimeMap.le sc2_src sc2_tgt>> /\
      <<MEM2: sim_memory latests caps lc2_tgt.(Local.promises) mem2_src mem2_tgt>>.
  Proof.
    inv STEP_TGT. inv WRITE.
    exploit (@promise (Message.full val (TView.write_released lc1_src.(Local.tview) sc1_src loc to releasedm_src ord)));
      try exact PROMISE; eauto.
    { apply LOCAL1. }
    { apply WF1_SRC. }
    { apply WF1_TGT. }
    { econs. eapply TViewFacts.write_future0; ss. apply WF1_SRC. }
    { econs. etrans; try by (inv PROMISE; inv TS; eauto).
      apply view_opt_le_time_le.
      apply TViewFacts.write_released_mon; try refl; ss.
      - apply LOCAL1.
      - apply WF1_TGT. }
    i. des.
    exploit Memory.promise_get0; try exact PROMISE_SRC. i. des.
    exploit Memory.remove_exists; try exact GET_PROMISES. i. des.
    exploit promise_remove_sim; try eapply LOCAL1; try exact MEM1;
      try exact PROMISE_SRC; try exact PROMISE; eauto.
    { apply WF1_SRC. }
    { apply WF1_TGT. }
    { econs. apply TViewFacts.write_released_mon; try refl; ss.
      - apply LOCAL1.
      - apply WF1_TGT. }
    i. des. esplits.
    - econs; eauto.
      + econs. inv WRITABLE.
        eapply TimeFacts.le_lt_lt; eauto.
        inv LOCAL1. inv TVIEW. inv CUR. ss.
      + ii. inv LOCAL1.
        exploit sim_promises_get_src; eauto. i. des. subst. ss.
    - inv LOCAL1. econs; ss; eauto.
      eapply TViewFacts.write_tview_mon; try refl; ss. apply WF1_TGT.
    - ss.
    - ss.
  Qed.

  Lemma write_step_cap
        latests caps
        lc1_src sc1_src mem1_src releasedm_src
        lc1_tgt sc1_tgt mem1_tgt loc from val releasedm_tgt released_tgt ord lc2_tgt sc2_tgt mem2_tgt kind_tgt
        (LOCAL1: sim_local lc1_src lc1_tgt)
        (SC1: TimeMap.le sc1_src sc1_tgt)
        (MEM1: sim_memory latests caps lc1_tgt.(Local.promises) mem1_src mem1_tgt)
        (WF1_SRC: Local.wf lc1_src mem1_src)
        (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
        (SC1_SRC: Memory.closed_timemap sc1_src mem1_src)
        (SC1_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
        (CLOSED1_SRC: Memory.closed mem1_src)
        (CLOSED1_TGT: Memory.closed mem1_tgt)
        (RELEASEDM_SRC: View.opt_wf releasedm_src)
        (RELEASEDM_TGT: View.opt_wf releasedm_tgt)
        (RELEASEDM: View.opt_le releasedm_src releasedm_tgt)
        (STEP_TGT: Local.write_step lc1_tgt sc1_tgt mem1_tgt loc from (latests loc) val
                                    releasedm_tgt released_tgt ord lc2_tgt sc2_tgt mem2_tgt kind_tgt):
    exists released_src lc2_src sc2_src mem2_src kind_src from_cap mem3_src,
      <<STEP_SRC: Local.write_step lc1_src sc1_src mem1_src loc from (latests loc) val
                                   releasedm_src released_src ord lc2_src sc2_src mem2_src kind_src>> /\
      <<LOWER: Memory.lower mem2_src loc from_cap (caps loc) Message.half (Message.full val None) mem3_src>> /\
      <<LOCAL2: sim_local lc2_src lc2_tgt>> /\
      <<SC2: TimeMap.le sc2_src sc2_tgt>> /\
      <<MEM2: sim_memory latests caps lc2_tgt.(Local.promises) mem3_src mem2_tgt>>.
  Proof.
    inv STEP_TGT. inv WRITE.
    exploit (@promise (Message.full val (TView.write_released lc1_src.(Local.tview) sc1_src loc (latests loc) releasedm_src ord)));
      try exact PROMISE; eauto.
    { apply LOCAL1. }
    { apply WF1_SRC. }
    { apply WF1_TGT. }
    { econs. eapply TViewFacts.write_future0; ss. apply WF1_SRC. }
    { econs. etrans; try by (inv PROMISE; inv TS; eauto).
      apply view_opt_le_time_le.
      apply TViewFacts.write_released_mon; try refl; ss.
      - apply LOCAL1.
      - apply WF1_TGT. }
    i. des.
    exploit Memory.promise_get0; try exact PROMISE_SRC. i. des.
    exploit Memory.remove_exists; try exact GET_PROMISES. i. des.
    exploit promise_remove_sim_cap; try eapply LOCAL1; try exact MEM1;
      try exact PROMISE_SRC; try exact PROMISE; eauto.
    { apply WF1_SRC. }
    { apply WF1_TGT. }
    { econs. apply TViewFacts.write_released_mon; try refl; ss.
      - apply LOCAL1.
      - apply WF1_TGT. }
    i. des. inv MSG. esplits.
    - econs; eauto.
      + econs. inv WRITABLE.
        eapply TimeFacts.le_lt_lt; eauto.
        inv LOCAL1. inv TVIEW. inv CUR. ss.
      + ii. inv LOCAL1.
        exploit sim_promises_get_src; eauto. i. des. subst. ss.
    - eauto.
    - inv LOCAL1. econs; ss; eauto.
      eapply TViewFacts.write_tview_mon; try refl; ss. apply WF1_TGT.
    - ss.
    - ss.
  Qed.

  Definition fence_step := PFStep.fence_step.

  Inductive lower_cap (caps: TimeMap.t): forall (mem1 mem2: Memory.t), Prop :=
  | lower_cap_refl mem:
      lower_cap caps mem mem
  | lower_cap_lower
      mem1 mem2
      loc from to val released
      from_cap
      (GET: Memory.get loc to mem1 = Some (from, Message.full val released))
      (LOWER: Memory.lower mem1 loc from_cap (caps loc) Message.half (Message.full val None) mem2):
      lower_cap caps mem1 mem2
  .
  Hint Constructors lower_cap.

  Program Instance lower_cap_Reflexive: forall caps, Reflexive (lower_cap caps).

  Inductive pf_step (lang: Language.t) (caps: TimeMap.t): forall (e1 e2: Thread.t lang), Prop :=
  | pf_step_intro
      e e1 st2 lc2 sc2 mem2 mem3
      (STEP: @Thread.step lang true e e1 (Thread.mk lang st2 lc2 sc2 mem2))
      (LOWER: @lower_cap caps mem2 mem3):
      pf_step caps e1 (Thread.mk lang st2 lc2 sc2 mem3)
  .
  Hint Constructors pf_step.

  Lemma pf_step_future
        lang
        latests caps e_tgt
        e1 e2
        (SIM: @sim_thread lang latests caps e2 e_tgt)
        (STEP: pf_step caps e1 e2)
        (WF1: Local.wf e1.(Thread.local) e1.(Thread.memory))
        (SC1: Memory.closed_timemap e1.(Thread.sc) e1.(Thread.memory))
        (CLOSED1: Memory.closed e1.(Thread.memory)):
    <<WF2: Local.wf e2.(Thread.local) e2.(Thread.memory)>> /\
    <<SC2: Memory.closed_timemap e2.(Thread.sc) e2.(Thread.memory)>> /\
    <<CLOSED2: Memory.closed e2.(Thread.memory)>> /\
    <<TVIEW_FUTURE: TView.le e1.(Thread.local).(Local.tview) e2.(Thread.local).(Local.tview)>> /\
    <<SC_FUTURE: TimeMap.le e1.(Thread.sc) e2.(Thread.sc)>> /\
    <<MEM_FUTURE: Memory.future e1.(Thread.memory) e2.(Thread.memory)>>.
  Proof.
    destruct e1, e2, e_tgt. ss. inv STEP.
    exploit Thread.step_future; eauto. s. i. des.
    inv LOWER; try by (esplits; eauto).
    assert (FUTURE: Memory.future mem2 memory0).
    { econs; eauto. econs; eauto. econs. ss.
      unfold TimeMap.bot. apply Time.bot_spec. }
    splits; auto.
    - inv WF2. econs; eauto.
      + eapply TView.future_closed; eauto.
      + ii. exploit PROMISES; eauto. i.
        erewrite Memory.lower_o; eauto. condtac; ss.
        des. subst.
        inv SIM. inv MEMORY. ss. specialize (CAPP loc).
        inv LOCAL. inv PROMISES0.
        exploit SOUND0; eauto. i. des. congr.
    - eapply Memory.future_closed_timemap; eauto.
    - eapply Memory.future_closed; eauto.
    - etrans; eauto.
  Qed.

  Lemma program_step
        latests caps
        lc1_src sc1_src mem1_src
        e_tgt lc1_tgt sc1_tgt mem1_tgt lc2_tgt sc2_tgt mem2_tgt
        (LOCAL1: sim_local lc1_src lc1_tgt)
        (SC1: TimeMap.le sc1_src sc1_tgt)
        (MEM1: sim_memory latests caps lc1_tgt.(Local.promises) mem1_src mem1_tgt)
        (WF1_SRC: Local.wf lc1_src mem1_src)
        (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
        (SC1_SRC: Memory.closed_timemap sc1_src mem1_src)
        (SC1_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
        (CLOSED1_SRC: Memory.closed mem1_src)
        (CLOSED1_TGT: Memory.closed mem1_tgt)
        (STEP_TGT: Local.program_step e_tgt lc1_tgt sc1_tgt mem1_tgt lc2_tgt sc2_tgt mem2_tgt)
        (CONS: promise_consistent lc2_tgt):
    exists e_src lc2_src sc2_src mem2_src mem3_src,
      <<STEP_SRC: Local.program_step e_src lc1_src sc1_src mem1_src lc2_src sc2_src mem2_src>> /\
      <<LOWER: lower_cap caps mem2_src mem3_src>> /\
      <<LOCAL2: sim_local lc2_src lc2_tgt>> /\
      <<SC2: TimeMap.le sc2_src sc2_tgt>> /\
      <<MEM2: sim_memory latests caps lc2_tgt.(Local.promises) mem3_src mem2_tgt>> /\
      <<EVENT: ThreadEvent.get_program_event e_src = ThreadEvent.get_program_event e_tgt>>.
  Proof.
    inv STEP_TGT.
    - esplits; eauto.
    - exploit read_step; eauto. i. des.
      esplits; try exact LOCAL2; eauto.
      inv LOCAL. ss.
    - destruct (Time.eq_dec to (latests loc)).
      + subst. exploit write_step_cap; try exact LOCAL; eauto. i. des.
        esplits; try exact LOCAL2; try exact MEM2; eauto.
        inv STEP_SRC. exploit Memory.write_get2; eauto.
        { apply CLOSED1_SRC. }
        { apply WF1_SRC. }
        { apply WF1_SRC. }
        i. des. eauto.
      + exploit write_step; try exact LOCAL; eauto. i. des.
        esplits; try exact LOCAL2; eauto.
    - exploit read_step; eauto.
      { eapply write_step_promise_consistent; eauto. }
      i. des.
      exploit Local.read_step_future; try exact LOCAL0; eauto. i. des.
      exploit Local.read_step_future; try exact STEP_SRC; eauto. i. des.
      destruct (Time.eq_dec tsw (latests loc)).
      + subst. exploit write_step_cap; try exact LOCAL2; eauto.
        { inv LOCAL0. eauto. }
        i. des.
        esplits; try exact LOCAL4; try exact MEM2; eauto.
        inv STEP_SRC0. exploit Memory.write_get2; eauto.
        { apply CLOSED1_SRC. }
        { apply WF0. }
        { apply WF0. }
        i. des. eauto.
      + exploit write_step; try exact LOCAL2; eauto.
        { inv LOCAL0. eauto. }
        i. des.
        esplits; try exact LOCAL4; eauto.
    - exploit fence_step; eauto. i. des.
      esplits; try exact LOCAL2; eauto.
      inv LOCAL. ss.
    - exploit fence_step; eauto. i. des.
      esplits; try exact LOCAL2; eauto.
      inv LOCAL. ss.
  Qed.

  Lemma thread_promise_step
        lang latests caps e1_src
        pf e_tgt e1_tgt e2_tgt
        (SIM1: @sim_thread lang latests caps e1_src e1_tgt)
        (WF1_SRC: Local.wf e1_src.(Thread.local) e1_src.(Thread.memory))
        (WF1_TGT: Local.wf e1_tgt.(Thread.local) e1_tgt.(Thread.memory))
        (SC1_SRC: Memory.closed_timemap e1_src.(Thread.sc) e1_src.(Thread.memory))
        (SC1_TGT: Memory.closed_timemap e1_tgt.(Thread.sc) e1_tgt.(Thread.memory))
        (MEM1_SRC: Memory.closed e1_src.(Thread.memory))
        (MEM1_TGT: Memory.closed e1_tgt.(Thread.memory))
        (STEP_TGT: Thread.promise_step pf e_tgt e1_tgt e2_tgt):
    exists e_src e2_src,
      <<STEP_SRC: Thread.promise_step true e_src e1_src e2_src>> /\
      <<SIM2: sim_thread latests caps e2_src e2_tgt>>.
  Proof.
    destruct e1_src, e1_tgt, e2_tgt. ss.
    inv SIM1. inv STEP_TGT. ss. subst.
    exploit promise_step; try exact LOCAL; try exact MEMORY; eauto. i. des.
    esplits.
    - econs; eauto.
    - econs; eauto.
  Qed.

  Lemma thread_program_step
        lang latests caps e1_src
        e_tgt e1_tgt e2_tgt
        (SIM1: @sim_thread lang latests caps e1_src e1_tgt)
        (WF1_SRC: Local.wf e1_src.(Thread.local) e1_src.(Thread.memory))
        (WF1_TGT: Local.wf e1_tgt.(Thread.local) e1_tgt.(Thread.memory))
        (SC1_SRC: Memory.closed_timemap e1_src.(Thread.sc) e1_src.(Thread.memory))
        (SC1_TGT: Memory.closed_timemap e1_tgt.(Thread.sc) e1_tgt.(Thread.memory))
        (MEM1_SRC: Memory.closed e1_src.(Thread.memory))
        (MEM1_TGT: Memory.closed e1_tgt.(Thread.memory))
        (STEP_TGT: Thread.program_step e_tgt e1_tgt e2_tgt)
        (CONS: promise_consistent e2_tgt.(Thread.local)):
    exists e_src e2_src mem2_src,
      <<STEP_SRC: Thread.program_step e_src e1_src e2_src>> /\
      <<LOWER: lower_cap caps e2_src.(Thread.memory) mem2_src>> /\
      <<SIM2: sim_thread latests caps
                         (Thread.mk lang e2_src.(Thread.state) e2_src.(Thread.local) e2_src.(Thread.sc) mem2_src) e2_tgt>>.
  Proof.
    destruct e1_src, e1_tgt, e2_tgt. ss.
    inv SIM1. inv STEP_TGT. ss. subst.
    exploit program_step; try exact LOCAL; try exact MEMORY; eauto. i. des.
    esplits.
    - econs; try exact STEP_SRC. rewrite EVENT. eauto.
    - eapply LOWER.
    - ss.
  Qed.

  Lemma thread_step
        lang latests caps e1_src
        pf e_tgt e1_tgt e2_tgt
        (SIM1: @sim_thread lang latests caps e1_src e1_tgt)
        (WF1_SRC: Local.wf e1_src.(Thread.local) e1_src.(Thread.memory))
        (WF1_TGT: Local.wf e1_tgt.(Thread.local) e1_tgt.(Thread.memory))
        (SC1_SRC: Memory.closed_timemap e1_src.(Thread.sc) e1_src.(Thread.memory))
        (SC1_TGT: Memory.closed_timemap e1_tgt.(Thread.sc) e1_tgt.(Thread.memory))
        (MEM1_SRC: Memory.closed e1_src.(Thread.memory))
        (MEM1_TGT: Memory.closed e1_tgt.(Thread.memory))
        (STEP_TGT: Thread.step pf e_tgt e1_tgt e2_tgt)
        (CONS: promise_consistent e2_tgt.(Thread.local)):
    exists e2_src,
      <<STEP_SRC: pf_step caps e1_src e2_src>> /\
      <<SIM2: sim_thread latests caps e2_src e2_tgt>>.
  Proof.
    inv STEP_TGT.
    - exploit thread_promise_step; eauto. i. des.
      esplits; eauto.
      destruct e2_src. econs; eauto. econs; eauto.
    - exploit thread_program_step; eauto. i. des.
      esplits; eauto.
      destruct e2_src. econs; eauto. econs 2; eauto.
  Qed.

  Lemma thread_rtc_all_step
        lang latests caps e1_src
        e1_tgt e2_tgt
        (SIM1: @sim_thread lang latests caps e1_src e1_tgt)
        (WF1_SRC: Local.wf e1_src.(Thread.local) e1_src.(Thread.memory))
        (WF1_TGT: Local.wf e1_tgt.(Thread.local) e1_tgt.(Thread.memory))
        (SC1_SRC: Memory.closed_timemap e1_src.(Thread.sc) e1_src.(Thread.memory))
        (SC1_TGT: Memory.closed_timemap e1_tgt.(Thread.sc) e1_tgt.(Thread.memory))
        (MEM1_SRC: Memory.closed e1_src.(Thread.memory))
        (MEM1_TGT: Memory.closed e1_tgt.(Thread.memory))
        (STEPS_TGT: rtc (@Thread.all_step lang) e1_tgt e2_tgt)
        (CONS: promise_consistent e2_tgt.(Thread.local)):
    exists e2_src,
      <<STEPS_SRC: rtc (@pf_step lang caps) e1_src e2_src>> /\
      <<SIM2: sim_thread latests caps e2_src e2_tgt>>.
  Proof.
    revert e1_src SIM1 WF1_SRC SC1_SRC MEM1_SRC.
    induction STEPS_TGT; eauto; i.
    inv H. inv USTEP.
    exploit Thread.step_future; eauto. i. des.
    exploit thread_step; try exact STEP; eauto.
    { eapply rtc_all_step_promise_consistent; eauto. }
    i. des.
    exploit pf_step_future; try exact STEP_SRC; eauto. i. des.
    exploit IHSTEPS_TGT; try exact SIM2; eauto. i. des.
    esplits; try exact SIM0.
    econs 2; eauto.
  Qed.

  Lemma thread_rtc_tau_step
        lang latests caps e1_src
        e1_tgt e2_tgt
        (SIM1: @sim_thread lang latests caps e1_src e1_tgt)
        (WF1_SRC: Local.wf e1_src.(Thread.local) e1_src.(Thread.memory))
        (WF1_TGT: Local.wf e1_tgt.(Thread.local) e1_tgt.(Thread.memory))
        (SC1_SRC: Memory.closed_timemap e1_src.(Thread.sc) e1_src.(Thread.memory))
        (SC1_TGT: Memory.closed_timemap e1_tgt.(Thread.sc) e1_tgt.(Thread.memory))
        (MEM1_SRC: Memory.closed e1_src.(Thread.memory))
        (MEM1_TGT: Memory.closed e1_tgt.(Thread.memory))
        (STEPS_TGT: rtc (@Thread.tau_step lang) e1_tgt e2_tgt)
        (CONS: promise_consistent e2_tgt.(Thread.local)):
    exists e2_src,
      <<STEPS_SRC: rtc (@pf_step lang caps) e1_src e2_src>> /\
      <<SIM2: sim_thread latests caps e2_src e2_tgt>>.
  Proof.
    eapply thread_rtc_all_step; eauto.
    eapply rtc_implies; [|eauto].
    apply tau_union.
  Qed.


  (* existence of sim *)

  Inductive cap_aux_tgt (latests: TimeMap.t) (mem1 mem2: Memory.t): Prop :=
  | cap_aux_tgt_intro
      (SOUND: forall loc from to msg
                (GET1: Memory.get loc to mem1 = Some (from, msg)),
          Memory.get loc to mem2 = Some (from, msg))
      (MIDDLE: forall loc from1 to1 from2 to2
                 (ADJ: Memory.adjacent loc from1 to1 from2 to2 mem1)
                 (TS: Time.lt to1 from2),
          Memory.get loc from2 mem2 = Some (to1, Message.half))
      (BACK: forall loc to
               (TO: to = Time.incr (Memory.max_ts loc mem1)),
          Memory.get loc to mem1 = None /\
          exists f val r released,
            Memory.get loc (latests loc) mem1 = Some (f, Message.full val r) /\
            Memory.get loc to mem2 = Some (Memory.max_ts loc mem1, Message.full val released))
      (COMPLETE: forall loc from to msg
                   (TO: to <> Time.incr (Memory.max_ts loc mem1))
                   (GET2: Memory.get loc to mem2 = Some (from, msg)),
          Memory.get loc to mem1 = Some (from, msg) \/
          Memory.get loc to mem1 = None /\
          Time.lt from to /\
          msg = Message.half /\
          exists from1 to1, Memory.adjacent loc from1 from to to1 mem1)
  .

  Inductive cap_aux_src (latests: TimeMap.t) (promises mem1 mem2: Memory.t): Prop :=
  | cap_aux_src_intro
      (SOUND: forall loc from to msg
                (GET1: Memory.get loc to mem1 = Some (from, msg)),
          Memory.get loc to mem2 = Some (from, msg))
      (MIDDLE: forall loc from1 to1 from2 to2
                 (ADJ: Memory.adjacent loc from1 to1 from2 to2 mem1)
                 (TS: Time.lt to1 from2),
          Memory.get loc from2 mem2 = Some (to1, Message.half))
      (BACK_SOME: forall loc to f m
                    (TO: to = Time.incr (Memory.max_ts loc mem1))
                    (GETP: Memory.get loc (latests loc) promises = Some (f, m)),
          Memory.get loc to mem1 = None /\
          Memory.get loc to mem2 = Some (Memory.max_ts loc mem1, Message.half))
      (BACK_NONE: forall loc to
                    (TO: to = Time.incr (Memory.max_ts loc mem1))
                    (GETP: Memory.get loc (latests loc) promises = None),
          Memory.get loc to mem1 = None /\
          exists from val released,
            Memory.get loc (latests loc) mem1 = Some (from, Message.full val released) /\
            Memory.get loc to mem2 = Some (Memory.max_ts loc mem1, Message.full val None))
      (COMPLETE: forall loc from to msg
                   (TO: to <> Time.incr (Memory.max_ts loc mem1))
                   (GET2: Memory.get loc to mem2 = Some (from, msg)),
          Memory.get loc to mem1 = Some (from, msg) \/
          Memory.get loc to mem1 = None /\
          Time.lt from to /\
          msg = Message.half /\
          exists from1 to1, Memory.adjacent loc from1 from to to1 mem1)
  .

  Lemma sim_memory_max_ts
        promises_src promises_tgt mem_src mem_tgt
        (PROMISES: sim_promises promises_src promises_tgt)
        (MEM: PFStep.sim_memory promises_tgt mem_src mem_tgt)
        (LE_SRC: Memory.le promises_src mem_src)
        (LE_TGT: Memory.le promises_tgt mem_tgt)
        (INHABITED_SRC: Memory.inhabited mem_src)
        (INHABITED_TGT: Memory.inhabited mem_tgt):
    forall loc, Memory.max_ts loc mem_src = Memory.max_ts loc mem_tgt.
  Proof.
    i. inv PROMISES. inv MEM.
    exploit Memory.max_ts_spec; try eapply INHABITED_SRC.
    instantiate (1 := loc). i. des. clear MAX.
    exploit Memory.max_ts_spec; try eapply INHABITED_TGT.
    instantiate (1 := loc). i. des. clear MAX.
    apply TimeFacts.antisym.
    - destruct (Memory.get loc (Memory.max_ts loc mem_src) promises_tgt) as [[]|] eqn:GETP.
      + exploit LE_TGT; eauto. i.
        exploit Memory.max_ts_spec; try exact x. i. des. ss.
      + exploit SOUND0; eauto. i. des.
        exploit Memory.max_ts_spec; try exact GET_TGT. i. des. ss.
    - destruct (Memory.get loc (Memory.max_ts loc mem_tgt) promises_tgt) as [[]|] eqn:GETP.
      + exploit COMPLETE; eauto. i. des.
        exploit LE_SRC; eauto. i.
        exploit Memory.max_ts_spec; try exact x0. i. des. ss.
      + exploit COMPLETE0; eauto. i. des.
        exploit Memory.max_ts_spec; try exact GET_SRC. i. des. ss.
  Qed.

  Lemma sim_memory_adjacent_src
        promises_src promises_tgt mem_src mem_tgt
        loc from1 to1 from2 to2
        (PROMISES: sim_promises promises_src promises_tgt)
        (MEM: PFStep.sim_memory promises_tgt mem_src mem_tgt)
        (LE_SRC: Memory.le promises_src mem_src)
        (LE_TGT: Memory.le promises_tgt mem_tgt)
        (ADJ_SRC: Memory.adjacent loc from1 to1 from2 to2 mem_src):
    Memory.adjacent loc from1 to1 from2 to2 mem_tgt.
  Proof.
    inv ADJ_SRC.
    exploit PFStep.sim_memory_get_src; try exact GET1; eauto. i. des.
    exploit PFStep.sim_memory_get_src; try exact GET2; eauto. i. des.
    econs; eauto. i.
    exploit EMPTY; eauto. i.
    inv PROMISES. inv MEM.
    destruct (Memory.get loc ts mem_tgt) as [[]|] eqn:GET; ss.
    destruct (Memory.get loc ts promises_tgt) as [[]|] eqn:GETP.
    - exploit COMPLETE; eauto. i. des.
      exploit LE_SRC; eauto. i. congr.
    - exploit COMPLETE0; eauto. i. des. congr.
  Qed.

  Lemma sim_memory_adjacent_tgt
        promises_src promises_tgt mem_src mem_tgt
        loc from1 to1 from2 to2
        (PROMISES: sim_promises promises_src promises_tgt)
        (MEM: PFStep.sim_memory promises_tgt mem_src mem_tgt)
        (LE_SRC: Memory.le promises_src mem_src)
        (LE_TGT: Memory.le promises_tgt mem_tgt)
        (ADJ_TGT: Memory.adjacent loc from1 to1 from2 to2 mem_tgt):
    Memory.adjacent loc from1 to1 from2 to2 mem_src.
  Proof.
    inv ADJ_TGT.
    exploit PFStep.sim_memory_get_tgt; try exact GET1; eauto. i. des.
    exploit PFStep.sim_memory_get_tgt; try exact GET2; eauto. i. des.
    econs; eauto; i.
    exploit EMPTY; eauto. i.
    inv PROMISES. inv MEM.
    destruct (Memory.get loc ts mem_src) as [[]|] eqn:GET; ss.
    destruct (Memory.get loc ts promises_tgt) as [[]|] eqn:GETP.
    - exploit LE_TGT; eauto. i. congr.
    - exploit SOUND0; eauto. i. des. congr.
  Qed.

  Lemma cap_aux_sim_memory
        latests
        promises_src promises_tgt
        mem1_src mem2_src mem1_tgt mem2_tgt
        (PROMISES: sim_promises promises_src promises_tgt)
        (MEM1: PFStep.sim_memory promises_tgt mem1_src mem1_tgt)
        (LE_SRC: Memory.le promises_src mem1_src)
        (LE_TGT: Memory.le promises_tgt mem1_tgt)
        (INHABITED_SRC: Memory.inhabited mem1_src)
        (INHABITED_TGT: Memory.inhabited mem1_tgt)
        (CAP_SRC: cap_aux_src latests promises_tgt mem1_src mem2_src)
        (CAP_TGT: cap_aux_tgt latests mem1_tgt mem2_tgt):
    sim_memory latests (fun loc => Time.incr (Memory.max_ts loc mem1_tgt)) promises_tgt mem2_src mem2_tgt.
  Proof.
    assert (MAX: forall loc, Memory.max_ts loc mem1_src = Memory.max_ts loc mem1_tgt).
    { eapply sim_memory_max_ts; eauto. }
    dup MEM1. inv MEM0. inv CAP_SRC. inv CAP_TGT. econs; i.
    { exploit COMPLETE0; eauto.
      { rewrite MAX. ss. }
      i. des.
      - exploit SOUND; eauto. i. des.
        exploit SOUND1; eauto.
      - subst. exploit sim_memory_adjacent_src; try exact x2; eauto. i.
        exploit MIDDLE0; eauto. i.
        esplits; eauto. ss.
    }
    { destruct (Memory.get loc to mem1_tgt) as [[]|] eqn:X.
      - exploit SOUND1; eauto. i.
        rewrite GET_TGT in x. symmetry in x. inv x.
        exploit COMPLETE; eauto. i. des.
        exploit SOUND0; eauto.
      - exploit COMPLETE1; eauto. i. des; try congr. subst.
        exploit sim_memory_adjacent_tgt; try exact x2; eauto. i.
        exploit MIDDLE; eauto. i.
        esplits; eauto. ss.
    }
    { exploit (BACK loc); try refl. i. des.
      exploit Memory.max_ts_spec; try exact x1. i. des.
      eapply TimeFacts.le_lt_lt; eauto.
      apply Time.incr_spec.
    }
    { destruct (Memory.get loc (Time.incr (Memory.max_ts loc mem1_tgt)) promises_tgt) as [[]|] eqn:GETP; ss.
      exploit LE_TGT; eauto. i.
      exploit Memory.max_ts_spec; try exact x. i. des.
      specialize (Time.incr_spec (Memory.max_ts loc mem1_tgt)). i. timetac.
    }
    { exploit (BACK loc); try refl. i. des.
      destruct (Memory.get loc (latests loc) promises_tgt) as [[]|] eqn:GETP.
      - exploit BACK_SOME; eauto. i. des.
        rewrite MAX in *. esplits; eauto.
        unfold cap_src. rewrite GETP. ss.
      - exploit BACK_NONE; eauto. i. des.
        rewrite MAX in *. esplits; eauto.
        unfold cap_src. rewrite GETP.
        exploit SOUND; eauto. i. des.
        rewrite x1 in GET_TGT. inv GET_TGT. inv MSG.
        econs; ss.
    }
  Qed.
End CapPFStep.
