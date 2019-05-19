Require Import RelationClasses.

Require Import sflib.
From Paco Require Import paco.

Require Import Axioms.
Require Import Basic.
Require Import DataStructure.
Require Import DenseOrder.
Require Import Event.
Require Import Time.
Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import MemoryFacts.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import MemoryMerge.

Require Import SimMemory.

Set Implicit Arguments.


Module LowerMemory.
  Inductive lower_memory (mem_src mem_tgt: Memory.t): Prop :=
  | lower_memory_intro
      (SOUND: forall loc from to msg
                (GET: Memory.get loc to mem_src = Some (from, msg)),
          exists msg', Memory.get loc to mem_tgt = Some (from, msg'))
      (COMPLETE: forall loc from to msg
                   (GET: Memory.get loc to mem_tgt = Some (from, msg)),
          exists msg', Memory.get loc to mem_src = Some (from, msg'))
      (MSG: forall loc from to msg_src msg_tgt
              (GET_SRC: Memory.get loc to mem_src = Some (from, msg_src))
              (GET_TGT: Memory.get loc to mem_tgt = Some (from, msg_tgt)),
          sim_message msg_src msg_tgt)
  .

  Program Instance lower_memory_PreOrder: PreOrder lower_memory.
  Next Obligation.
    ii. econs; eauto.
    i. rewrite GET_SRC in GET_TGT. inv GET_TGT. refl.
  Qed.
  Next Obligation.
    ii. inv H. inv H0. econs; i.
    - exploit SOUND; eauto. i. des. eauto.
    - exploit COMPLETE0; eauto. i. des. eauto.
    - exploit SOUND; eauto. i. des.
      exploit SOUND0; eauto. i. des.
      exploit MSG; eauto. i.
      exploit MSG0; eauto. i.
      etrans; eauto.
  Qed.

  Lemma lower_memory_closed_timemap
        mem_src mem_tgt tm
        (MEM: lower_memory mem_src mem_tgt)
        (CLOSED: Memory.closed_timemap tm mem_tgt):
    Memory.closed_timemap tm mem_src.
  Proof.
    ii. specialize (CLOSED loc). des.
    inv MEM. exploit COMPLETE; eauto. i. des.
    exploit MSG; eauto. i. inv x0. eauto.
  Qed.

  Lemma lower_memory_closed_view
        mem_src mem_tgt view
        (MEM: lower_memory mem_src mem_tgt)
        (CLOSED: Memory.closed_view view mem_tgt):
    Memory.closed_view view mem_src.
  Proof.
    inv CLOSED; eauto using lower_memory_closed_timemap.
  Qed.

  Lemma lower_memory_closed_opt_view
        mem_src mem_tgt view
        (MEM: lower_memory mem_src mem_tgt)
        (CLOSED: Memory.closed_opt_view view mem_tgt):
    Memory.closed_opt_view view mem_src.
  Proof.
    inv CLOSED; eauto using lower_memory_closed_view.
  Qed.

  Lemma lower_memory_closed_message
        mem_src mem_tgt msg
        (MEM: lower_memory mem_src mem_tgt)
        (CLOSED: Memory.closed_message msg mem_tgt):
    Memory.closed_message msg mem_src.
  Proof.
    inv CLOSED; eauto using lower_memory_closed_opt_view.
  Qed.

  Lemma lower_memory_promise
        promises1_src promises2_src
        mem1_src mem2_src
        promises1_tgt promises2_tgt
        mem1_tgt mem2_tgt
        loc from to msg_src msg_tgt kind
        (MEM1: lower_memory mem1_src mem1_tgt)
        (PROMISE_SRC: Memory.promise promises1_src mem1_src loc from to msg_src promises2_src mem2_src kind)
        (PROMISE_TGT: Memory.promise promises1_tgt mem1_tgt loc from to msg_tgt promises2_tgt mem2_tgt kind)
        (MSG: sim_message msg_src msg_tgt):
    lower_memory mem2_src mem2_tgt.
  Proof.
    inv MEM1. inv PROMISE_SRC; inv PROMISE_TGT.
    - exploit Memory.add_get0; try exact MEM. i. des.
      exploit Memory.add_get0; try exact MEM0. i. des.
      econs; i.
      + revert GET3. erewrite Memory.add_o; eauto. condtac; ss; i.
        * des. subst. inv GET3. eauto.
        * erewrite Memory.add_o; eauto. condtac; ss; eauto.
      + revert GET3. erewrite Memory.add_o; eauto. condtac; ss; i.
        * des. subst. inv GET3. eauto.
        * erewrite Memory.add_o; eauto. condtac; ss. eauto.
      + revert GET_SRC. erewrite Memory.add_o; eauto. condtac; ss; i.
        * des. subst. inv GET_SRC.
          revert GET_TGT. erewrite Memory.add_o; eauto. condtac; ss; i.
          inv GET_TGT. auto.
        * revert GET_TGT. erewrite Memory.add_o; eauto. condtac; ss; eauto.
    - exploit Memory.split_get0; try exact MEM. i. des.
      exploit Memory.split_get0; try exact MEM0. i. des.
      econs; i.
      + revert GET7. erewrite Memory.split_o; eauto. repeat condtac; ss; i.
        * des. subst. inv GET7. eauto.
        * erewrite Memory.split_o; eauto. repeat condtac; ss; eauto.
        * erewrite Memory.split_o; eauto. repeat condtac; ss; eauto.
      + revert GET7. erewrite Memory.split_o; eauto. repeat condtac; ss; i.
        * des. subst. inv GET7. eauto.
        * erewrite Memory.split_o; eauto. repeat condtac; ss; eauto.
        * erewrite Memory.split_o; eauto. repeat condtac; ss; eauto.
      + revert GET_SRC. erewrite Memory.split_o; eauto. repeat condtac; ss; i.
        * des. subst. inv GET_SRC.
          revert GET_TGT. erewrite Memory.split_o; eauto. repeat condtac; ss; i.
          inv GET_TGT. auto.
        * revert GET_TGT. erewrite Memory.split_o; eauto. repeat condtac; ss; i.
          inv GET_SRC. inv GET_TGT. refl.
        * revert GET_TGT. erewrite Memory.split_o; eauto. repeat condtac; ss; eauto.
    - exploit Memory.lower_get0; try exact MEM. i. des.
      exploit Memory.lower_get0; try exact MEM0. i. des.
      econs; i.
      + revert GET3. erewrite Memory.lower_o; eauto. condtac; ss; i.
        * des. subst. inv GET3. eauto.
        * erewrite Memory.lower_o; eauto. condtac; ss. eauto.
      + revert GET3. erewrite Memory.lower_o; eauto. condtac; ss; i.
        * des. subst. inv GET3. eauto.
        * erewrite Memory.lower_o; eauto. condtac; ss. eauto.
      + revert GET_SRC. erewrite Memory.lower_o; eauto. condtac; ss; i.
        * des. subst. inv GET_SRC.
          revert GET_TGT. erewrite Memory.lower_o; eauto. condtac; ss; i.
          inv GET_TGT. auto.
        * revert GET_TGT. erewrite Memory.lower_o; eauto. condtac; ss; eauto.
  Qed.

  Lemma no_half_concrete_none_concrete_lower_memory
        promises mem mem1 mem2
        (LE1: Memory.le promises mem1)
        (LE2: Memory.le promises mem2)
        (CONCRETE1: Memory.concrete_none mem mem1)
        (CONCRETE2: Memory.concrete mem mem2)
        (NO_HALF1: Memory.no_half promises mem1)
        (NO_HALF2: Memory.no_half promises mem2):
    lower_memory mem1 mem2.
  Proof.
    inv CONCRETE1. inv CONCRETE2. econs; i.
    - exploit COMPLETE; eauto. i. des.
      + exploit SOUND0; eauto. i. des; eauto.
      + exploit SOUND0; eauto. i. des; eauto.
    - exploit COMPLETE0; eauto. i. des.
      + exploit SOUND; eauto. i. des; eauto.
      + exploit SOUND; eauto. i. des; eauto.
    - destruct msg_src; destruct msg_tgt; ss.
      + exploit COMPLETE; eauto. i.
        exploit COMPLETE0; eauto. i.
        des; try congr.
        * rewrite x in x0. inv x0. refl.
        * exploit SOUND; try exact x. i. des; try congr.
          exploit SOUND0; try exact x. i. des; try congr.
          rewrite GET_SRC in x3. inv x3.
          rewrite GET_TGT in x6. inv x6.
          rewrite x2 in x5. inv x5.
          econs; eauto.
      + exploit NO_HALF2; eauto. i.
        exploit LE1; eauto. i. congr.
      + exploit NO_HALF1; eauto. i.
        exploit LE2; eauto. i. congr.
  Qed.

  Inductive lower_local (lc_src lc_tgt: Local.t): Prop :=
  | lower_local_intro
      (TVIEW: TView.le lc_src.(Local.tview) lc_tgt.(Local.tview))
      (PROMISES: lc_src.(Local.promises) = lc_tgt.(Local.promises))
  .

  Program Instance lower_local_PreOrder: PreOrder lower_local.
  Next Obligation.
    econs; eauto. refl.
  Qed.
  Next Obligation.
    ii. inv H. inv H0. econs.
    - etrans; eauto.
    - rewrite PROMISES. auto.
  Qed.

  Lemma promise
        promises1_tgt mem1_tgt loc from to msg promises2_tgt mem2_tgt kind
        promises1_src mem1_src
        (MEM1: lower_memory mem1_src mem1_tgt)
        (PROMISES1: promises1_src = promises1_tgt)
        (LE1_SRC: Memory.le promises1_src mem1_src)
        (LE1_TGT: Memory.le promises1_tgt mem1_tgt)
        (CLOSED1_TGT: Memory.closed mem1_tgt)
        (PROMISE_TGT: Memory.promise promises1_tgt mem1_tgt loc from to msg promises2_tgt mem2_tgt kind):
    exists promises2_src mem2_src,
      <<PROMISE_SRC: Memory.promise promises1_src mem1_src loc from to msg promises2_src mem2_src kind>> /\
      <<MEM2: lower_memory mem2_src mem2_tgt>> /\
      <<PROMISES2: promises2_src = promises2_tgt>>.
  Proof.
    cut (exists promises2_src mem2_src,
            <<PROMISE_SRC: Memory.promise promises1_src mem1_src loc from to msg promises2_src mem2_src kind>>).
    { i. des. esplits; eauto.
      - eapply lower_memory_promise; eauto. refl.
      - inv PROMISE_SRC; inv PROMISE_TGT;
          eauto using Memory.add_inj, Memory.split_inj, Memory.lower_inj. }
    subst. inv PROMISE_TGT.
    { exploit Memory.add_get0; try exact MEM. i. des.
      exploit Memory.get_ts; try exact GET0. i. des.
      { subst. inv CLOSED1_TGT. rewrite INHABITED in GET. inv GET. }
      exploit (@Memory.add_exists mem1_src loc from to msg); eauto.
      { i. inv MEM1. exploit SOUND; eauto. i. des.
        inv MEM. inv ADD. eauto. }
      { inv MEM. inv ADD. auto. }
      i. des. esplits.
      econs; eauto.
      i. subst. exploit HALF; eauto. i. des.
      inv MEM1. exploit COMPLETE; eauto. i. des.
      exploit MSG; eauto. i. inv x3. eauto.
    }
    { exploit Memory.split_get0; try exact MEM. i. des.
      exploit Memory.split_get0; try exact PROMISES. i. des.
      exploit Memory.get_ts; try exact GET1. i. des.
      { subst. inv CLOSED1_TGT. rewrite INHABITED in GET. inv GET. }
      exploit Memory.get_ts; try exact GET2. i. des.
      { subst. inv x0. }
      inv MEM1. exploit COMPLETE; try exact GET0. i. des.
      exploit LE1_SRC; eauto. i. rewrite x in x2. inv x2.
      exploit (@Memory.split_exists mem1_src loc from to ts3 msg msg3); eauto.
      { inv MEM. inv SPLIT. auto. }
      i. des. esplits.
      econs 2; eauto.
      i. subst. exploit HALF1; eauto. i. des.
      exploit COMPLETE; eauto. i. des.
      exploit MSG; eauto. i. inv x5. eauto.
    }
    { exploit Memory.lower_get0; try exact MEM. i. des.
      exploit Memory.lower_get0; try exact PROMISES. i. des.
      exploit Memory.get_ts; try exact GET. i. des.
      { subst. inv MEM. inv LOWER. inv TS0. }
      inv MEM1. exploit COMPLETE; eauto. i. des.
      exploit LE1_SRC; eauto. i. rewrite x in x1. inv x1.
      exploit (@Memory.lower_exists mem1_src loc from to msg0 msg); eauto.
      { inv MEM. inv LOWER. auto. }
      i. des. esplits.
      econs 3; eauto.
    }
  Qed.

  Lemma promise_step
        lc1_tgt mem1_tgt loc from to msg lc2_tgt mem2_tgt kind
        lc1_src mem1_src
        (MEM1: lower_memory mem1_src mem1_tgt)
        (LC1: lower_local lc1_src lc1_tgt)
        (CLOSED1_TGT: Memory.closed mem1_tgt)
        (WF1_SRC: Local.wf lc1_src mem1_src)
        (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
        (STEP_TGT: Local.promise_step lc1_tgt mem1_tgt loc from to msg lc2_tgt mem2_tgt kind):
    exists lc2_src mem2_src,
      <<STEP_SRC: Local.promise_step lc1_src mem1_src loc from to msg lc2_src mem2_src kind>> /\
      <<MEM2: lower_memory mem2_src mem2_tgt>> /\
      <<LC2: lower_local lc2_src lc2_tgt>>.
  Proof.
    inv LC1. inv WF1_SRC. inv WF1_TGT. inv STEP_TGT.
    exploit promise; try exact PROMISE; eauto. i. des.
    esplits; eauto.
    - econs; eauto.
      eapply lower_memory_closed_message; eauto.
    - ss.
  Qed.

  Lemma read_step
        lc1_tgt mem1_tgt loc ts val released_tgt ord lc2_tgt
        lc1_src mem1_src
        (MEM1: lower_memory mem1_src mem1_tgt)
        (LC1: lower_local lc1_src lc1_tgt)
        (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
        (CLOSED1_TGT: Memory.closed mem1_tgt)
        (STEP_TGT: Local.read_step lc1_tgt mem1_tgt loc ts val released_tgt ord lc2_tgt):
    exists lc2_src released_src,
      <<STEP_SRC: Local.read_step lc1_src mem1_src loc ts val released_src ord lc2_src>> /\
      <<LC2: lower_local lc2_src lc2_tgt>>.
  Proof.
    inv STEP_TGT. inv MEM1. inv LC1.
    exploit COMPLETE; eauto. i. des.
    exploit MSG; eauto. i. inv x0.
    esplits.
    - econs; eauto.
      eapply TViewFacts.readable_mon; eauto; try refl. apply TVIEW.
    - econs; eauto. ss.
      eapply TViewFacts.read_tview_mon; eauto; try refl.
      + apply WF1_TGT.
      + inv CLOSED1_TGT. exploit CLOSED; eauto. i. des. inv MSG_WF. auto.
  Qed.

  Lemma write_step
        lc1_src sc1_src mem1_src
        lc1_tgt sc1_tgt mem1_tgt
        lc2_tgt sc2_tgt mem2_tgt
        loc from to val releasedm_src releasedm_tgt released_tgt ord kind
        (MEM1: lower_memory mem1_src mem1_tgt)
        (LC1: lower_local lc1_src lc1_tgt)
        (SC1: TimeMap.le sc1_src sc1_tgt)
        (CLOSED1_SRC: Memory.closed mem1_src)
        (CLOSED1_TGT: Memory.closed mem1_tgt)
        (WF1_SRC: Local.wf lc1_src mem1_src)
        (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
        (RELM: View.opt_le releasedm_src releasedm_tgt)
        (RELM_WF_SRC: View.opt_wf releasedm_src)
        (RELM_WF_TGT: View.opt_wf releasedm_tgt)
        (RELM_CLOSED_SRC: Memory.closed_opt_view releasedm_src mem1_src)
        (RELM_CLOSED_TGT: Memory.closed_opt_view releasedm_tgt mem1_tgt)
        (STEP_TGT: Local.write_step lc1_tgt sc1_tgt mem1_tgt loc from to val releasedm_tgt released_tgt ord lc2_tgt sc2_tgt mem2_tgt kind):
    exists lc2_src sc2_src mem2_src released_src,
      <<STEP_SRC: Local.write_step lc1_src sc1_src mem1_src loc from to val releasedm_src released_src ord lc2_src sc2_src mem2_src kind>> /\
      <<MEM2: lower_memory mem2_src mem2_tgt>> /\
      <<LC2: lower_local lc2_src lc2_tgt>> /\
      <<SC2: TimeMap.le sc2_src sc2_tgt>>.
  Proof.
    inv WF1_SRC. inv WF1_TGT. inv LC1. inv STEP_TGT. inv WRITE.
    exploit promise; try exact PROMISE; eauto. i. des.
    exploit Memory.promise_get0; try exact PROMISE_SRC. i. des.
    assert (REL: View.opt_le (TView.write_released (Local.tview lc1_src) sc1_src loc to releasedm_src ord)
                             (TView.write_released (Local.tview lc1_tgt) sc1_tgt loc to releasedm_tgt ord)).
    { apply TViewFacts.write_released_mon; auto. refl. }
    exploit (@Memory.lower_exists promises2_src loc from to
                                  (Message.full val (TView.write_released lc1_tgt.(Local.tview) sc1_tgt loc to releasedm_tgt ord))
                                  (Message.full val (TView.write_released lc1_src.(Local.tview) sc1_src loc to releasedm_src ord)));
      auto.
    { exploit Memory.get_ts; try exact GET_MEM. i. des; auto.
      subst. inv PROMISE; inv MEM.
      - inv ADD. inv TO.
      - inv SPLIT. inv TS12.
      - inv LOWER. inv TS0. }
    { econs. eapply TViewFacts.write_future0; eauto. }
    i. des.
    exploit Memory.promise_future0; try exact PROMISE_SRC; eauto.
    { apply CLOSED1_SRC. }
    i. des.
    exploit Memory.lower_exists_le; try exact x0; eauto. i. des.
    exploit MemoryMerge.promise_promise_promise; try exact PROMISE_SRC.
    { econs 3; eauto. econs.
      inv PROMISE; inv TS; etrans; eauto; inv REL; viewtac; inv LE; ss. }
    i.
    exploit Memory.promise_get0; try exact x2. i. des.
    exploit (@Memory.remove_exists mem2 loc from to
                                   (Message.full val (TView.write_released (Local.tview lc1_src) sc1_src loc to releasedm_src ord)));
      auto.
    i. des.
    esplits.
    - econs; eauto.
      + eapply TViewFacts.writable_mon; eauto; try refl. apply TVIEW.
      + rewrite PROMISES1 in *. auto.
    - eapply lower_memory_promise; try exact x2; try exact PROMISE; eauto.
    - econs; ss.
      + apply TViewFacts.write_tview_mon; auto. refl.
      + apply Memory.ext. i.
        erewrite Memory.remove_o; eauto.
        erewrite Memory.remove_o with (mem2 := promises2); try exact REMOVE.
        condtac; ss.
        erewrite Memory.lower_o; eauto. condtac; subst; ss.
    - auto.
  Qed.

  Lemma fence_step
        lc1_src sc1_src mem1_src
        lc1_tgt sc1_tgt mem1_tgt
        lc2_tgt sc2_tgt
        ordr ordw
        (LC1: lower_local lc1_src lc1_tgt)
        (SC1: TimeMap.le sc1_src sc1_tgt)
        (WF1_SRC: Local.wf lc1_src mem1_src)
        (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
        (STEP_TGT: Local.fence_step lc1_tgt sc1_tgt ordr ordw lc2_tgt sc2_tgt):
    exists lc2_src sc2_src,
      <<STEP_SRC: Local.fence_step lc1_src sc1_src ordr ordw lc2_src sc2_src >> /\
      <<LC2: lower_local lc2_src lc2_tgt>> /\
      <<SC2: TimeMap.le sc2_src sc2_tgt>>.
  Proof.
    inv STEP_TGT. esplits.
    - econs; eauto.
      inv LC1. rewrite PROMISES in *. auto.
    - econs; ss.
      + apply TViewFacts.write_fence_tview_mon; eauto; try refl.
        * apply TViewFacts.read_fence_tview_mon; eauto;
            try apply LC1; try apply WF1_TGT; try refl.
        * eapply TViewFacts.read_fence_future; eauto;
            try apply LC1; try apply WF1_SRC.
      + apply LC1.
    - apply TViewFacts.write_fence_sc_mon; eauto; try refl.
      apply TViewFacts.read_fence_tview_mon; eauto;
        try apply LC1; try apply WF1_TGT; try refl.
  Qed.

  Lemma program_step
        e_tgt
        lc1_src sc1_src mem1_src
        lc1_tgt sc1_tgt mem1_tgt
        lc2_tgt sc2_tgt mem2_tgt
        (MEM1: lower_memory mem1_src mem1_tgt)
        (LC1: lower_local lc1_src lc1_tgt)
        (SC1: TimeMap.le sc1_src sc1_tgt)
        (CLOSED1_SRC: Memory.closed mem1_src)
        (CLOSED1_TGT: Memory.closed mem1_tgt)
        (WF1_SRC: Local.wf lc1_src mem1_src)
        (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
        (STEP_TGT: Local.program_step e_tgt lc1_tgt sc1_tgt mem1_tgt lc2_tgt sc2_tgt mem2_tgt):
    exists e_src lc2_src sc2_src mem2_src,
      <<STEP_SRC: Local.program_step e_src lc1_src sc1_src mem1_src lc2_src sc2_src mem2_src>> /\
      <<EVENT: ThreadEvent.get_program_event e_src = ThreadEvent.get_program_event e_tgt>> /\
      <<MEM2: lower_memory mem2_src mem2_tgt>> /\
      <<LC2: lower_local lc2_src lc2_tgt>> /\
      <<SC2: TimeMap.le sc2_src sc2_tgt>>.
  Proof.
    inv STEP_TGT.
    - esplits; eauto.
    - exploit read_step; eauto. i. des.
      esplits; try exact LC2; eauto.
    - exploit write_step; eauto. i. des.
      esplits; try exact MEM2; eauto.
    - exploit read_step; eauto. i. des.
      exploit Local.read_step_future; try exact LOCAL1; eauto. i. des.
      exploit Local.read_step_future; try exact STEP_SRC; eauto. i. des.
      exploit write_step; try exact LOCAL2; try exact REL_CLOSED0; eauto.
      { inv LOCAL1. inv STEP_SRC. ss.
        inv MEM1. exploit SOUND; eauto. i. des.
        rewrite GET in x. inv x. exploit MSG; eauto. i.
        inv x. auto. }
      i. des.
      esplits; try exact MEM2; try exact LC0; try exact SC2; eauto.
    - exploit fence_step; eauto. i. des.
      esplits; try exact LC2; eauto.
    - exploit fence_step; eauto. i. des.
      esplits; try exact LC2; eauto.
  Qed.

  Lemma thread_promise_step
        lang pf e e1_src e1_tgt e2_tgt
        (STATE1: e1_src.(Thread.state) = e1_tgt.(Thread.state))
        (MEM1: lower_memory e1_src.(Thread.memory) e1_tgt.(Thread.memory))
        (LC1: lower_local e1_src.(Thread.local) e1_tgt.(Thread.local))
        (SC1: TimeMap.le e1_src.(Thread.sc) e1_tgt.(Thread.sc))
        (CLOSED1_SRC: Memory.closed e1_src.(Thread.memory))
        (CLOSED1_tgt: Memory.closed e1_tgt.(Thread.memory))
        (WF1_SRC: Local.wf e1_src.(Thread.local) e1_src.(Thread.memory))
        (WF1_TGT: Local.wf e1_tgt.(Thread.local) e1_tgt.(Thread.memory))
        (STEP_TGT: @Thread.promise_step lang pf e e1_tgt e2_tgt):
    exists e2_src,
      <<STEP_SRC: @Thread.promise_step lang pf e e1_src e2_src>> /\
      <<STATE2: e2_src.(Thread.state) = e2_tgt.(Thread.state)>> /\
      <<MEM2: lower_memory e2_src.(Thread.memory) e2_tgt.(Thread.memory)>> /\
      <<LC2: lower_local e2_src.(Thread.local) e2_tgt.(Thread.local)>> /\
      <<SC2: TimeMap.le e2_src.(Thread.sc) e2_tgt.(Thread.sc)>>.
  Proof.
    destruct e1_src, e1_tgt, e2_tgt. ss. inv STEP_TGT.
    exploit promise_step; eauto. i. des.
    esplits.
    - econs; eauto.
    - auto.
    - auto.
    - auto.
    - auto.
  Qed.

  Lemma thread_program_step
        lang e_tgt e1_src e1_tgt e2_tgt
        (STATE1: e1_src.(Thread.state) = e1_tgt.(Thread.state))
        (MEM1: lower_memory e1_src.(Thread.memory) e1_tgt.(Thread.memory))
        (LC1: lower_local e1_src.(Thread.local) e1_tgt.(Thread.local))
        (SC1: TimeMap.le e1_src.(Thread.sc) e1_tgt.(Thread.sc))
        (CLOSED1_SRC: Memory.closed e1_src.(Thread.memory))
        (CLOSED1_tgt: Memory.closed e1_tgt.(Thread.memory))
        (WF1_SRC: Local.wf e1_src.(Thread.local) e1_src.(Thread.memory))
        (WF1_TGT: Local.wf e1_tgt.(Thread.local) e1_tgt.(Thread.memory))
        (STEP_TGT: @Thread.program_step lang e_tgt e1_tgt e2_tgt):
    exists e_src e2_src,
      <<STEP_SRC: @Thread.program_step lang e_src e1_src e2_src>> /\
      <<EVENT: ThreadEvent.get_program_event e_src = ThreadEvent.get_program_event e_tgt>> /\
      <<STATE2: e2_src.(Thread.state) = e2_tgt.(Thread.state)>> /\
      <<MEM2: lower_memory e2_src.(Thread.memory) e2_tgt.(Thread.memory)>> /\
      <<LC2: lower_local e2_src.(Thread.local) e2_tgt.(Thread.local)>> /\
      <<SC2: TimeMap.le e2_src.(Thread.sc) e2_tgt.(Thread.sc)>>.
  Proof.
    destruct e1_src, e1_tgt, e2_tgt. ss. inv STEP_TGT.
    exploit program_step; eauto. i. des.
    esplits.
    - econs; try exact STEP_SRC. rewrite EVENT. eauto.
    - auto.
    - auto.
    - auto.
    - auto.
    - auto.
  Qed.

  Lemma thread_step
        lang pf e_tgt e1_src e1_tgt e2_tgt
        (STATE1: e1_src.(Thread.state) = e1_tgt.(Thread.state))
        (MEM1: lower_memory e1_src.(Thread.memory) e1_tgt.(Thread.memory))
        (LC1: lower_local e1_src.(Thread.local) e1_tgt.(Thread.local))
        (SC1: TimeMap.le e1_src.(Thread.sc) e1_tgt.(Thread.sc))
        (CLOSED1_SRC: Memory.closed e1_src.(Thread.memory))
        (CLOSED1_tgt: Memory.closed e1_tgt.(Thread.memory))
        (WF1_SRC: Local.wf e1_src.(Thread.local) e1_src.(Thread.memory))
        (WF1_TGT: Local.wf e1_tgt.(Thread.local) e1_tgt.(Thread.memory))
        (STEP_TGT: @Thread.step lang pf e_tgt e1_tgt e2_tgt):
    exists e_src e2_src,
      <<STEP_SRC: @Thread.step lang pf e_src e1_src e2_src>> /\
      <<EVENT: ThreadEvent.get_program_event e_src = ThreadEvent.get_program_event e_tgt>> /\
      <<STATE2: e2_src.(Thread.state) = e2_tgt.(Thread.state)>> /\
      <<MEM2: lower_memory e2_src.(Thread.memory) e2_tgt.(Thread.memory)>> /\
      <<LC2: lower_local e2_src.(Thread.local) e2_tgt.(Thread.local)>> /\
      <<SC2: TimeMap.le e2_src.(Thread.sc) e2_tgt.(Thread.sc)>>.
  Proof.
    inv STEP_TGT.
    - exploit thread_promise_step; eauto. i. des.
      esplits; eauto. econs 1; eauto.
    - exploit thread_program_step; eauto. i. des.
      esplits; eauto. econs 2; eauto.
  Qed.

  Lemma thread_opt_step
        lang e_tgt e1_src e1_tgt e2_tgt
        (STATE1: e1_src.(Thread.state) = e1_tgt.(Thread.state))
        (MEM1: lower_memory e1_src.(Thread.memory) e1_tgt.(Thread.memory))
        (LC1: lower_local e1_src.(Thread.local) e1_tgt.(Thread.local))
        (SC1: TimeMap.le e1_src.(Thread.sc) e1_tgt.(Thread.sc))
        (CLOSED1_SRC: Memory.closed e1_src.(Thread.memory))
        (CLOSED1_tgt: Memory.closed e1_tgt.(Thread.memory))
        (WF1_SRC: Local.wf e1_src.(Thread.local) e1_src.(Thread.memory))
        (WF1_TGT: Local.wf e1_tgt.(Thread.local) e1_tgt.(Thread.memory))
        (STEP_TGT: @Thread.opt_step lang e_tgt e1_tgt e2_tgt):
    exists e_src e2_src,
      <<STEP_SRC: @Thread.opt_step lang e_src e1_src e2_src>> /\
      <<STATE2: e2_src.(Thread.state) = e2_tgt.(Thread.state)>> /\
      <<MEM2: lower_memory e2_src.(Thread.memory) e2_tgt.(Thread.memory)>> /\
      <<LC2: lower_local e2_src.(Thread.local) e2_tgt.(Thread.local)>> /\
      <<SC2: TimeMap.le e2_src.(Thread.sc) e2_tgt.(Thread.sc)>>.
  Proof.
    inv STEP_TGT.
    - esplits; eauto. econs 1; eauto.
    - exploit thread_step; eauto. i. des.
      esplits; eauto. econs 2; eauto.
  Qed.

  Lemma thread_rtc_all_step
        lang e1_src e1_tgt e2_tgt
        (STATE1: e1_src.(Thread.state) = e1_tgt.(Thread.state))
        (MEM1: lower_memory e1_src.(Thread.memory) e1_tgt.(Thread.memory))
        (LC1: lower_local e1_src.(Thread.local) e1_tgt.(Thread.local))
        (SC1: TimeMap.le e1_src.(Thread.sc) e1_tgt.(Thread.sc))
        (CLOSED1_SRC: Memory.closed e1_src.(Thread.memory))
        (CLOSED1_tgt: Memory.closed e1_tgt.(Thread.memory))
        (WF1_SRC: Local.wf e1_src.(Thread.local) e1_src.(Thread.memory))
        (WF1_TGT: Local.wf e1_tgt.(Thread.local) e1_tgt.(Thread.memory))
        (SC1_SRC: Memory.closed_timemap e1_src.(Thread.sc) e1_src.(Thread.memory))
        (SC1_TGT: Memory.closed_timemap e1_tgt.(Thread.sc) e1_tgt.(Thread.memory))
        (HALF_WF1_SRC: Memory.half_wf e1_src.(Thread.memory))
        (HALF_WF1_TGT: Memory.half_wf e1_tgt.(Thread.memory))
        (STEPS_TGT: rtc (@Thread.all_step lang) e1_tgt e2_tgt):
    exists e2_src,
      <<STEPS_SRC: rtc (@Thread.all_step lang) e1_src e2_src>> /\
      <<STATE2: e2_src.(Thread.state) = e2_tgt.(Thread.state)>> /\
      <<MEM2: lower_memory e2_src.(Thread.memory) e2_tgt.(Thread.memory)>> /\
      <<LC2: lower_local e2_src.(Thread.local) e2_tgt.(Thread.local)>> /\
      <<SC2: TimeMap.le e2_src.(Thread.sc) e2_tgt.(Thread.sc)>>.
  Proof.
    revert e1_src STATE1 MEM1 LC1 SC1 CLOSED1_SRC CLOSED1_tgt
           WF1_SRC WF1_TGT SC1_SRC SC1_TGT HALF_WF1_SRC HALF_WF1_TGT.
    induction STEPS_TGT; i.
    - esplits; eauto.
    - inv H. inv USTEP.
      exploit thread_step; eauto. i. des.
      exploit Thread.step_future; try exact STEP; eauto. i. des.
      exploit Thread.step_future; try exact STEP_SRC; eauto. i. des.
      exploit IHSTEPS_TGT; try exact STATE2; eauto. i. des.
      esplits; cycle 1; eauto. econs; eauto. econs. econs. eauto.
  Qed.

  Lemma thread_rtc_tau_step
        lang e1_src e1_tgt e2_tgt
        (STATE1: e1_src.(Thread.state) = e1_tgt.(Thread.state))
        (MEM1: lower_memory e1_src.(Thread.memory) e1_tgt.(Thread.memory))
        (LC1: lower_local e1_src.(Thread.local) e1_tgt.(Thread.local))
        (SC1: TimeMap.le e1_src.(Thread.sc) e1_tgt.(Thread.sc))
        (CLOSED1_SRC: Memory.closed e1_src.(Thread.memory))
        (CLOSED1_tgt: Memory.closed e1_tgt.(Thread.memory))
        (WF1_SRC: Local.wf e1_src.(Thread.local) e1_src.(Thread.memory))
        (WF1_TGT: Local.wf e1_tgt.(Thread.local) e1_tgt.(Thread.memory))
        (SC1_SRC: Memory.closed_timemap e1_src.(Thread.sc) e1_src.(Thread.memory))
        (SC1_TGT: Memory.closed_timemap e1_tgt.(Thread.sc) e1_tgt.(Thread.memory))
        (HALF_WF1_SRC: Memory.half_wf e1_src.(Thread.memory))
        (HALF_WF1_TGT: Memory.half_wf e1_tgt.(Thread.memory))
        (STEPS_TGT: rtc (@Thread.tau_step lang) e1_tgt e2_tgt):
    exists e2_src,
      <<STEPS_SRC: rtc (@Thread.tau_step lang) e1_src e2_src>> /\
      <<STATE2: e2_src.(Thread.state) = e2_tgt.(Thread.state)>> /\
      <<MEM2: lower_memory e2_src.(Thread.memory) e2_tgt.(Thread.memory)>> /\
      <<LC2: lower_local e2_src.(Thread.local) e2_tgt.(Thread.local)>> /\
      <<SC2: TimeMap.le e2_src.(Thread.sc) e2_tgt.(Thread.sc)>>.
  Proof.
    revert e1_src STATE1 MEM1 LC1 SC1 CLOSED1_SRC CLOSED1_tgt
           WF1_SRC WF1_TGT SC1_SRC SC1_TGT HALF_WF1_SRC HALF_WF1_TGT.
    induction STEPS_TGT; i.
    - esplits; eauto.
    - inv H. inv TSTEP.
      exploit thread_step; eauto. i. des.
      exploit Thread.step_future; try exact STEP; eauto. i. des.
      exploit Thread.step_future; try exact STEP_SRC; eauto. i. des.
      exploit IHSTEPS_TGT; try exact STATE2; eauto. i. des.
      esplits; cycle 1; eauto. econs; eauto. econs.
      + econs. eauto.
      + destruct e; destruct e_src; ss.
  Qed.
End LowerMemory.