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

Set Implicit Arguments.

Module PFStep.
  Inductive sim_promises (promises_src promises_tgt: Memory.t): Prop :=
  | sim_promises_intro
      (SOUND: forall loc from to msg_src
                (GET_SRC: Memory.get loc to promises_src = Some (from, msg_src)),
          exists msg_tgt,
            <<GET_TGT: Memory.get loc to promises_tgt = Some (from, msg_tgt)>>)
      (COMPLETE: forall loc from to msg
                   (GET_TGT: Memory.get loc to promises_tgt = Some (from, msg)),
          <<GET_SRC: Memory.get loc to promises_src = Some (from, Message.half)>>)
  .

  Inductive sim_local (lc_src lc_tgt: Local.t): Prop :=
  | sim_local_intro
      (TVIEW: lc_src.(Local.tview) = lc_tgt.(Local.tview))
      (PROMISES: sim_promises lc_src.(Local.promises) lc_tgt.(Local.promises))
  .

  Inductive sim_memory (promises mem_src mem_tgt: Memory.t): Prop :=
  | sim_memory_intro
      (SOUND: forall loc from to msg
                (GETP: Memory.get loc to promises = None)
                (GET_SRC: Memory.get loc to mem_src = Some (from, msg)),
          <<GET_TGT: Memory.get loc to mem_tgt = Some (from, msg)>>)
      (COMPLETE: forall loc from to msg
                   (GETP: Memory.get loc to promises = None)
                   (GET_TGT: Memory.get loc to mem_tgt = Some (from, msg)),
          <<GET_SRC: Memory.get loc to mem_src = Some (from, msg)>>)
  .

  Inductive sim_thread (lang: Language.t) (e_src e_tgt: @Thread.t lang): Prop :=
  | sim_thread_intro
      (STATE: e_src.(Thread.state) = e_tgt.(Thread.state))
      (LOCAL: sim_local e_src.(Thread.local) e_tgt.(Thread.local))
      (SC: e_src.(Thread.sc) = e_tgt.(Thread.sc))
      (MEMORY: sim_memory e_tgt.(Thread.local).(Local.promises)
                             e_src.(Thread.memory) e_tgt.(Thread.memory))
  .


  Lemma sim_memory_get_src
        promises_src promises_tgt
        mem_src mem_tgt
        loc from to msg_src
        (PROMISES: sim_promises promises_src promises_tgt)
        (MEM: sim_memory promises_tgt mem_src mem_tgt)
        (LE_SRC: Memory.le promises_src mem_src)
        (LE_TGT: Memory.le promises_tgt mem_tgt)
        (GET_SRC: Memory.get loc to mem_src = Some (from, msg_src)):
    exists msg_tgt,
      <<GET_TGT: Memory.get loc to mem_tgt = Some (from, msg_tgt)>> /\
      <<MSG: __guard__ (msg_src = Message.half \/ msg_src = msg_tgt)>>.
  Proof.
    inv PROMISES. inv MEM.
    destruct (Memory.get loc to promises_tgt) as [[f m]|] eqn:GETP.
    - exploit LE_TGT; eauto. i.
      exploit COMPLETE; eauto. i. des.
      exploit LE_SRC; eauto. i.
      rewrite GET_SRC in x1. inv x1.
      esplits; eauto. unguard. des; eauto.
    - exploit SOUND0; eauto. i. des.
      unguard. esplits; eauto.
  Qed.

  Lemma sim_memory_get_tgt
        promises_src promises_tgt
        mem_src mem_tgt
        loc from to msg_tgt
        (PROMISES: sim_promises promises_src promises_tgt)
        (MEM: sim_memory promises_tgt mem_src mem_tgt)
        (LE_SRC: Memory.le promises_src mem_src)
        (LE_TGT: Memory.le promises_tgt mem_tgt)
        (GET_TGT: Memory.get loc to mem_tgt = Some (from, msg_tgt)):
    exists msg_src,
      <<GET_SRC: Memory.get loc to mem_src = Some (from, msg_src)>> /\
      <<MSG: __guard__ (msg_src = Message.half \/ msg_src = msg_tgt)>>.
  Proof.
    inv PROMISES. inv MEM.
    destruct (Memory.get loc to promises_tgt) as [[f m]|] eqn:GETP.
    - exploit LE_TGT; eauto. i.
      rewrite GET_TGT in x. inv x.
      exploit COMPLETE; eauto. i. des.
      exploit LE_SRC; eauto. i.
      esplits; eauto. unguard. des; eauto.
    - exploit COMPLETE0; eauto. i. des.
      unguard. esplits; eauto.
  Qed.

  Lemma promise
        promises1_src mem1_src
        promises1_tgt mem1_tgt loc from to msg promises2_tgt mem2_tgt kind_tgt
        (PROMISES1: sim_promises promises1_src promises1_tgt)
        (MEM1: sim_memory promises1_tgt mem1_src mem1_tgt)
        (LE1_SRC: Memory.le promises1_src mem1_src)
        (LE1_TGT: Memory.le promises1_tgt mem1_tgt)
        (CLOSED1_SRC: Memory.closed mem1_src)
        (CLOSED1_TGT: Memory.closed mem1_tgt)
        (PROMISE_TGT: Memory.promise promises1_tgt mem1_tgt loc from to msg promises2_tgt mem2_tgt kind_tgt):
    exists promises2_src mem2_src kind_src,
      <<PROMISE_SRC: Memory.promise promises1_src mem1_src loc from to Message.half promises2_src mem2_src kind_src>> /\
      <<PROMISES2: sim_promises promises2_src promises2_tgt>> /\
      <<MEM2: sim_memory promises2_tgt mem2_src mem2_tgt>>.
  Proof.
    inv PROMISE_TGT.
    - (* add *)
      exploit (@Memory.add_exists mem1_src loc from to Message.half).
      { ii. exploit sim_memory_get_src; eauto. i. des.
        inv MEM. inv ADD. eapply DISJOINT; eauto. }
      { inv MEM. inv ADD. ss. }
      { econs. }
      i. des.
      exploit Memory.add_exists_le; try eapply x0; eauto. i. des.
      esplits; eauto; econs; i.
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
    - (* split *)
      exploit Memory.split_get0; try exact PROMISES. i. des.
      inv PROMISES1. exploit COMPLETE; try exact GET0. i. des.
      exploit (@Memory.split_exists promises1_src loc from to ts3 Message.half Message.half); eauto.
      { inv MEM. inv SPLIT. ss. }
      { inv MEM. inv SPLIT. ss. }
      { econs. }
      i. des.
      exploit Memory.split_exists_le; try exact x1; eauto. i. des.
      esplits; eauto; econs; i.
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
    - (* lower *)
      exploit Memory.lower_get0; try exact PROMISES. i. des.
      inv PROMISES1. exploit COMPLETE; eauto. i. des.
      exploit (@Memory.lower_exists promises1_src loc from to Message.half Message.half); eauto.
      { inv MEM. inv LOWER. ss. }
      { econs. }
      i. des.
      exploit Memory.lower_exists_le; try eapply x1; eauto. i. des.
      esplits; eauto; econs; i.
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
  Qed.

  Lemma promise_step
        lc1_src mem1_src
        lc1_tgt mem1_tgt loc from to msg lc2_tgt mem2_tgt kind_tgt
        (LOCAL1: sim_local lc1_src lc1_tgt)
        (MEM1: sim_memory lc1_tgt.(Local.promises) mem1_src mem1_tgt)
        (WF1_SRC: Local.wf lc1_src mem1_src)
        (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
        (CLOSED1_SRC: Memory.closed mem1_src)
        (CLOSED1_TGT: Memory.closed mem1_tgt)
        (STEP_TGT: Local.promise_step lc1_tgt mem1_tgt loc from to msg lc2_tgt mem2_tgt kind_tgt):
    exists lc2_src mem2_src kind_src,
      <<STEP_SRC: Local.promise_step lc1_src mem1_src loc from to Message.half lc2_src mem2_src kind_src>> /\
      <<LOCAL2: sim_local lc2_src lc2_tgt>> /\
      <<MEM2: sim_memory lc2_tgt.(Local.promises) mem2_src mem2_tgt>>.
  Proof.
    inv STEP_TGT.
    exploit promise; try exact PROMISE; eauto.
    { apply LOCAL1. }
    { apply WF1_SRC. }
    { apply WF1_TGT. }
    i. des. esplits; eauto.
    econs; eauto. apply LOCAL1.
  Qed.

  Lemma read_promise_None
        lc1 mem1 loc to val released ord lc2
        (WF1: Local.wf lc1 mem1)
        (STEP: Local.read_step lc1 mem1 loc to val released ord lc2)
        (CONS: promise_consistent lc2):
    Memory.get loc to lc1.(Local.promises) = None.
  Proof.
    destruct (Memory.get loc to lc1.(Local.promises)) as [[from msg]|] eqn:GETP; ss.
    exfalso.
    inv WF1. inv STEP. exploit PROMISES; eauto. i.
    rewrite GET in x. inv x.
    exploit CONS; eauto. ss. i.
    eapply Time.lt_strorder.
    eapply TimeFacts.le_lt_lt; eauto.
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
        lc1_src mem1_src
        lc1_tgt mem1_tgt loc to val released ord lc2_tgt
        (LOCAL1: sim_local lc1_src lc1_tgt)
        (MEM1: sim_memory lc1_tgt.(Local.promises) mem1_src mem1_tgt)
        (WF1_SRC: Local.wf lc1_src mem1_src)
        (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
        (STEP_TGT: Local.read_step lc1_tgt mem1_tgt loc to val released ord lc2_tgt)
        (CONS_TGT: promise_consistent lc2_tgt):
    exists lc2_src,
      <<STEP_SRC: Local.read_step lc1_src mem1_src loc to val released ord lc2_src>> /\
      <<LOCAL2: sim_local lc2_src lc2_tgt>>.
  Proof.
    exploit read_promise_None; try exact STEP_TGT; eauto. i.
    inv MEM1. inv LOCAL1. inv STEP_TGT.
    exploit COMPLETE; eauto. i. des.
    esplits.
    - econs; eauto. rewrite TVIEW. ss.
    - econs; eauto. rewrite TVIEW. ss.
  Qed.

  Lemma write_step
        lc1_src mem1_src
        lc1_tgt sc1 mem1_tgt loc from to val released ord lc3_tgt sc3 mem3_tgt kind_tgt
        (LOCAL1: sim_local lc1_src lc1_tgt)
        (MEM1: sim_memory lc1_tgt.(Local.promises) mem1_src mem1_tgt)
        (WF1_SRC: Local.wf lc1_src mem1_src)
        (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
        (SC1_SRC: Memory.closed_timemap sc1 mem1_src)
        (SC1_TGT: Memory.closed_timemap sc1 mem1_tgt)
        (CLOSED1_SRC: Memory.closed mem1_src)
        (CLOSED1_TGT: Memory.closed mem1_tgt)
        (STEP_TGT: Local.write_step lc1_tgt sc1 mem1_tgt loc from to val None released ord lc3_tgt sc3 mem3_tgt kind_tgt)
        (CONS_TGT: promise_consistent lc3_tgt):
    exists lc2_src mem2_src kind2_src lc3_src mem3_src kind3_src,
      <<STEP1_SRC: Local.promise_step lc1_src mem1_src loc from to (Message.full val released) lc2_src mem2_src kind2_src>> /\
      <<STEP2_SRC: Local.write_step lc2_src sc1 mem2_src loc from to val None released ord lc3_src sc3 mem3_src kind3_src>> /\
      <<LOCAL3: sim_local lc3_src lc3_tgt>> /\
      <<MEM3: sim_memory lc3_tgt.(Local.promises) mem3_src mem3_tgt>>.
  Proof.
  Admitted.
End PFStep.
