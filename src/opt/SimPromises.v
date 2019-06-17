Require Import RelationClasses.
Require Import Basics.
Require Import Bool.
Require Import List.

Require Import sflib.
From Paco Require Import paco.

Require Import Axioms.
Require Import Basic.
Require Import Event.
Require Import DenseOrder.
Require Import Time.
Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import MemoryFacts.
Require Import MemoryDomain.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.

Require Import SimMemory.
Require Import MemorySplit.
Require Import MemoryMerge.

Set Implicit Arguments.


Module SimPromises.
  Include MemoryDomain.

  Definition none_if_released loc ts (pview:t) (released:option View.t): option View.t :=
    if mem loc ts pview
    then None
    else released.

  Definition none_if loc ts (pview:t) (msg:Message.t): Message.t :=
    match msg with
    | Message.full val released =>
      Message.full val (none_if_released loc ts pview released)
    | Message.half => Message.half
    end.

  Lemma none_if_bot loc ts msg:
    none_if loc ts bot msg = msg.
  Proof.
    destruct msg; ss.
  Qed.

  Ltac none_if_tac :=
    repeat
      (try match goal with
           | [ |- context[none_if _ _ _ ?msg]] =>
             unfold none_if; destruct msg; ss
           | [ |- context[none_if_released _ _ ?msg]] =>
             unfold none_if_released; condtac; ss
           end).

  Definition mem_le_transf (pview:t) (lhs rhs:Memory.t): Prop :=
    forall loc to from msg
      (LHS: Memory.get loc to lhs = Some (from, msg)),
      Memory.get loc to rhs = Some (from, none_if loc to pview msg).

  Definition kind_transf loc ts (pview:t) (kind:Memory.op_kind): Memory.op_kind :=
    match kind with
    | Memory.op_kind_add => Memory.op_kind_add
    | Memory.op_kind_split ts msg => Memory.op_kind_split ts (none_if loc ts pview msg)
    | Memory.op_kind_lower msg => Memory.op_kind_lower (none_if loc ts pview msg)
    end.

  Lemma kind_transf_bot loc ts kind:
    kind_transf loc ts bot kind = kind.
  Proof.
    destruct kind; ss; rewrite none_if_bot; ss.
  Qed.

  Inductive sem (pview:t) (inv:t) (promises_src promises_tgt:Memory.t): Prop :=
  | sem_intro
      (LE: mem_le_transf pview promises_tgt promises_src)
      (PVIEW: forall l t (MEM: mem l t pview), exists f val released, Memory.get l t promises_tgt = Some (f, Message.full val released))
      (SOUND: forall l t (INV: mem l t inv),
          Memory.get l t promises_tgt = None /\
          exists f m, Memory.get l t promises_src = Some (f, m))
      (COMPLETE: forall l t f m
                   (SRC: Memory.get l t promises_src = Some (f, m))
                   (TGT: Memory.get l t promises_tgt = None),
          mem l t inv)
  .

  Lemma promise
        pview inv
        loc from to msg
        promises1_src mem1_src
        promises1_tgt mem1_tgt promises2_tgt mem2_tgt
        kind_tgt
        (PROMISE_TGT: Memory.promise promises1_tgt mem1_tgt loc from to msg promises2_tgt mem2_tgt kind_tgt)
        (INV1: sem pview inv promises1_src promises1_tgt)
        (SIM1: sim_memory mem1_src mem1_tgt)
        (LE1_SRC: Memory.le promises1_src mem1_src)
        (LE1_TGT: Memory.le promises1_tgt mem1_tgt):
    exists promises2_src mem2_src,
      <<PROMISE_SRC: Memory.promise promises1_src mem1_src loc from to (none_if loc to pview msg) promises2_src mem2_src (kind_transf loc to pview kind_tgt)>> /\
      <<INV2: sem pview inv promises2_src promises2_tgt>> /\
      <<SIM2: sim_memory mem2_src mem2_tgt>>.
  Proof.
    inv PROMISE_TGT.
    - exploit (@Memory.add_exists mem1_src loc from to msg);
        try by inv MEM; inv ADD.
      { eapply covered_disjoint.
        - apply SIM1.
        - inv MEM. inv ADD. auto. }
      i. des.
      exploit Memory.add_exists_le; try apply LE1_SRC; eauto. i. des.
      exploit sim_memory_add; try apply SIM1; try refl; eauto. i.
      esplits; eauto.
      + none_if_tac.
        * inv INV1. exploit PVIEW; eauto. i. des.
          hexploit Memory.add_get0; try exact PROMISES; eauto. i. des. congr.
        * econs 1; eauto; congr.
        * econs 1; eauto.
          i. exploit HALF; eauto. i. des.
          inv SIM1. exploit MSG; eauto. i. des. inv MSG0. eauto.
      + econs.
        * ii. erewrite Memory.add_o; eauto.
          erewrite (@Memory.add_o promises2_tgt) in LHS; try exact PROMISES. revert LHS.
          condtac; ss.
          { i. des. inv LHS. none_if_tac.
            inv INV1. exploit PVIEW; eauto. i. des.
            exploit Memory.add_get0; try exact PROMISES; eauto. i. des. congr. }
          { apply INV1. }
        * i. inv INV1. exploit PVIEW; eauto. i. des.
          erewrite Memory.add_o; eauto. condtac; eauto.
          ss. des. subst. exploit LE; eauto. i.
          inv x1. inv ADD. exfalso.
          eapply DISJOINT; eauto; econs; eauto; try refl. ss.
          exploit Memory.get_ts; try eapply x. i. des; ss.
          subst. inv TO.
        * i. inv INV1. exploit SOUND; eauto. i.
          erewrite Memory.add_o; eauto. erewrite (@Memory.add_o promises2); eauto.
          condtac; ss. des. subst.
          exploit Memory.add_get0; eauto. i. des. congr.
        * i. revert SRC TGT.
          erewrite Memory.add_o; eauto. erewrite (@Memory.add_o promises2_tgt); eauto.
          condtac; ss. inv INV1. eapply COMPLETE; eauto.
    - exploit Memory.split_get0; try exact PROMISES; eauto. i. des.
      exploit (@Memory.split_exists promises1_src loc from to ts3 msg (none_if loc ts3 pview msg3));
        try by inv PROMISES; inv SPLIT.
      { apply INV1. eauto. }
      i. des.
      exploit Memory.split_exists_le; try apply LE1_SRC; eauto. i. des.
      exploit sim_memory_split; try apply SIM1; try refl; eauto. i.
      esplits; eauto.
      + unfold none_if. destruct msg; ss.
        * unfold none_if_released. condtac; ss.
          { inv INV1. exploit PVIEW; eauto. i. des.
            hexploit Memory.split_get0; try exact PROMISES; eauto. congr. }
          { econs 2; eauto; congr. }
        * econs 2; eauto.
          { i. exploit HALF1; eauto. i. des.
            inv SIM1. exploit MSG; eauto. i. des. inv MSG0. eauto. }
          { destruct msg3; ss. }
      + econs.
        * ii. revert LHS.
          erewrite Memory.split_o; eauto. erewrite (@Memory.split_o mem2); try exact x0.
          repeat condtac; ss.
          { i. des. inv LHS. none_if_tac.
            inv INV1. exploit PVIEW; eauto. i. des.
            exploit Memory.split_get0; try exact PROMISES; eauto. congr. }
          { guardH o. i. des. inv LHS. ss. }
          { apply INV1. }
        * i. inv INV1. exploit PVIEW; eauto. i. des.
          erewrite Memory.split_o; eauto. repeat condtac; eauto.
          { des. ss. subst. congr. }
          { des; ss. subst. rewrite GET0 in x. inv x. eauto. }
        * i. inv INV1. exploit SOUND; eauto. i.
          erewrite Memory.split_o; eauto. erewrite (@Memory.split_o mem2); eauto.
          exploit Memory.split_get0; try exact x0; eauto. i. des.
          repeat condtac; ss.
          { des. subst. congr. }
          { guardH o. des. subst. congr. }
          esplits; eauto.
        * i. revert SRC TGT.
          erewrite Memory.split_o; eauto. erewrite (@Memory.split_o promises2_tgt); eauto.
          repeat condtac; ss. inv INV1. eapply COMPLETE; eauto.
    - exploit Memory.lower_get0; try exact PROMISES; eauto. i. des.
      exploit (@Memory.lower_exists promises1_src loc from to (none_if loc to pview msg0) (none_if loc to pview msg));
        try by inv MEM; inv LOWER.
      { apply INV1. eauto. }
      { none_if_tac; econs; ss.
        inv MEM. inv LOWER. inv MSG_WF. ss. }
      { none_if_tac; destruct msg0; ss.
        - inv MEM. inv LOWER. inv MSG_LE. econs. refl.
        - inv PROMISES. inv MSG_LE. }
      i. des.
      exploit Memory.lower_exists_le; try apply LE1_SRC; eauto. i. des.
      exploit sim_memory_lower; try exact SIM1; try exact x1; try exact x2; eauto.
      { none_if_tac; try refl. econs. econs. }
      i. esplits; eauto.
      + econs 3; eauto.
        none_if_tac; viewtac. econs. viewtac.
      + econs.
        * ii. revert LHS.
          erewrite Memory.lower_o; eauto. erewrite (@Memory.lower_o mem2); try exact x0.
          condtac; ss.
          { i. des. inv LHS. ss. }
          { apply INV1. }
        * i. inv INV1. exploit PVIEW; eauto. i. des.
          erewrite Memory.lower_o; eauto. condtac; eauto.
          des. ss. subst. rewrite GET in x. inv x.
          inv MSG_LE. esplits; eauto.
        * i. inv INV1. exploit SOUND; eauto. i.
          erewrite Memory.lower_o; eauto. erewrite (@Memory.lower_o mem2); eauto.
          exploit Memory.lower_get0; try exact x1; eauto. i. des.
          condtac; ss.
          { des. subst. congr. }
          esplits; eauto.
        * i. revert SRC TGT.
          erewrite Memory.lower_o; eauto. erewrite (@Memory.lower_o promises2_tgt); eauto.
          repeat condtac; ss. inv INV1. eapply COMPLETE; eauto.
  Qed.

  Lemma promise_bot
        inv
        loc from to msg
        promises1_src mem1_src
        promises1_tgt mem1_tgt promises2_tgt mem2_tgt
        kind
        (PROMISE_TGT: Memory.promise promises1_tgt mem1_tgt loc from to msg promises2_tgt mem2_tgt kind)
        (INV1: sem bot inv promises1_src promises1_tgt)
        (SIM1: sim_memory mem1_src mem1_tgt)
        (LE1_SRC: Memory.le promises1_src mem1_src)
        (LE1_TGT: Memory.le promises1_tgt mem1_tgt):
    exists promises2_src mem2_src,
      <<PROMISE_SRC: Memory.promise promises1_src mem1_src loc from to msg promises2_src mem2_src kind>> /\
      <<INV2: sem bot inv promises2_src promises2_tgt>> /\
      <<SIM2: sim_memory mem2_src mem2_tgt>>.
  Proof.
    exploit promise; eauto. i. des.
    rewrite none_if_bot in *.
    rewrite kind_transf_bot in *.
    esplits; eauto.
  Qed.

  Lemma remove_tgt
        pview inv
        loc from to msg
        promises1_src mem1_src
        promises1_tgt mem1_tgt promises2_tgt
        (REMOVE_TGT: Memory.remove promises1_tgt loc from to msg promises2_tgt)
        (INV1: sem pview inv promises1_src promises1_tgt)
        (SIM1: sim_memory mem1_src mem1_tgt)
        (LE1_SRC: Memory.le promises1_src mem1_src)
        (LE1_TGT: Memory.le promises1_tgt mem1_tgt)
        (FINITE1_TGT: Memory.finite promises1_tgt):
      <<INV2: sem (unset loc to pview) (set loc to inv) promises1_src promises2_tgt>> /\
      <<INV2': mem loc to inv = false>>.
  Proof.
    exploit Memory.remove_future; eauto. i. des.
    exploit Memory.remove_get0; [eauto|]. i. des.
    inv INV1. exploit LE0; eauto. i.
    esplits.
    - econs.
      + ii. revert LHS.
        erewrite Memory.remove_o; eauto. condtac; ss. i.
        exploit LE0; eauto.
        unfold none_if, none_if_released. repeat condtac; ss.
        * revert COND1. rewrite unset_o. condtac; ss; [|congr].
          guardH o. des. subst. unguardH o. des; congr.
        * revert COND1. rewrite unset_o. condtac; ss. congr.
      + i. revert MEM. rewrite unset_o. condtac; ss. guardH o. i.
        exploit PVIEW; eauto. i. des.
        erewrite Memory.remove_o; eauto. condtac; ss; eauto.
        des. subst. unguardH o. des; congr.
      + i. erewrite Memory.remove_o; eauto.
        revert INV. rewrite set_o.
        unfold Time.t, DOSet.elt. condtac; ss; i.
        * des. subst. esplits; eauto.
        * exploit SOUND; eauto.
      + i. revert TGT.
        erewrite Memory.remove_o; eauto. rewrite set_o.
        unfold Time.t, DOSet.elt. condtac; ss; i.
        eapply COMPLETE; eauto.
    - destruct (mem loc to inv) eqn:X; auto.
      exploit SOUND; [eauto|]. i. des. congr.
  Qed.

  Lemma remove_src
        pview inv
        loc from to msg
        promises1_src mem1_src
        promises1_tgt mem1_tgt
        (INV1: sem pview inv promises1_src promises1_tgt)
        (INV1': mem loc to inv)
        (SIM1: sim_memory mem1_src mem1_tgt)
        (GET: Memory.get loc to promises1_src = Some (from, msg))
        (LE1_SRC: Memory.le promises1_src mem1_src)
        (LE1_TGT: Memory.le promises1_tgt mem1_tgt):
    exists promises2_src,
      <<REMOVE_SRC: Memory.remove promises1_src loc from to msg promises2_src>> /\
      <<INV2: sem pview (unset loc to inv) promises2_src promises1_tgt>>.
  Proof.
    inv INV1.
    exploit Memory.remove_exists; eauto. i. des.
    esplits; eauto.
    econs.
    - ii. revert LHS.
      erewrite (@Memory.remove_o mem2); eauto. condtac; ss; eauto.
      des. subst. exploit SOUND; eauto. i. des. congr.
    - i. exploit PVIEW; eauto.
    - i. rewrite unset_o in INV. revert INV. condtac; ss.
      guardH o.
      i. exploit SOUND; eauto. i. des. splits; eauto.
      erewrite Memory.remove_o; eauto. condtac; ss; eauto.
      des. subst. unguardH o. des; congr.
    - i. revert SRC.
      erewrite Memory.remove_o; eauto. rewrite unset_o.
      unfold Time.t, DOSet.elt. condtac; ss; i.
      eapply COMPLETE; eauto.
  Qed.

  Lemma remove
        pview inv
        loc from to msg
        promises1_src mem1_src
        promises1_tgt mem1_tgt promises2_tgt
        (MSG_WF: Message.wf msg)
        (TIME: Time.lt from to)
        (REMOVE_TGT: Memory.remove promises1_tgt loc from to msg promises2_tgt)
        (INV1: sem pview inv promises1_src promises1_tgt)
        (SIM1: sim_memory mem1_src mem1_tgt)
        (LE1_SRC: Memory.le promises1_src mem1_src)
        (LE1_TGT: Memory.le promises1_tgt mem1_tgt)
        (FINITE1_TGT: Memory.finite promises1_tgt):
    exists promises2_src,
      <<REMOVE_SRC: Memory.remove promises1_src loc from to (none_if loc to pview msg) promises2_src>> /\
      <<INV2: sem (unset loc to pview) inv promises2_src promises2_tgt>>.
  Proof.
    hexploit Memory.remove_future; try apply REMOVE_TGT; eauto. i. des.
    exploit remove_tgt; eauto. i. des.
    exploit Memory.remove_get0; eauto. i. des.
    inv INV1. exploit LE0; eauto. i.
    exploit remove_src; try apply set_eq; eauto. i. des.
    esplits; eauto.
    rewrite unset_set in INV0; auto.
  Qed.

  Lemma remove_bot
        inv
        loc from to msg
        promises1_src mem1_src
        promises1_tgt mem1_tgt promises2_tgt
        (MSG_WF: Message.wf msg)
        (TIME: Time.lt from to)
        (REMOVE_TGT: Memory.remove promises1_tgt loc from to msg promises2_tgt)
        (INV1: sem bot inv promises1_src promises1_tgt)
        (SIM1: sim_memory mem1_src mem1_tgt)
        (LE1_SRC: Memory.le promises1_src mem1_src)
        (LE1_TGT: Memory.le promises1_tgt mem1_tgt)
        (FINITE1_TGT: Memory.finite promises1_tgt):
    exists promises2_src,
      <<REMOVE_SRC: Memory.remove promises1_src loc from to msg promises2_src>> /\
      <<INV2: sem bot inv promises2_src promises2_tgt>>.
  Proof.
    exploit remove; eauto. i. des.
    rewrite none_if_bot in *.
    esplits; eauto.
    replace bot with (unset loc to bot); ss. apply ext. i.
    rewrite unset_o. condtac; ss.
  Qed.

  Lemma no_half
        pview
        lc_src mem_src
        lc_tgt mem_tgt
        (INV: sem pview bot lc_src.(Local.promises) lc_tgt.(Local.promises))
        (MEM: sim_memory mem_src mem_tgt)
        (WF_SRC: Local.wf lc_src mem_src)
        (WF_TGT: Local.wf lc_tgt mem_tgt)
        (MEM_SRC: Memory.closed mem_src)
        (MEM_TGT: Memory.closed mem_tgt)
        (NOHALF_SRC: Memory.no_half lc_src.(Local.promises) mem_src):
    Memory.no_half lc_tgt.(Local.promises) mem_tgt.
  Proof.
    ii. dup MEM. inv MEM0. inv INV.
    exploit MSG; eauto. i. des. inv MSG0.
    exploit NOHALF_SRC; eauto. i.
    destruct (Memory.get loc to lc_tgt.(Local.promises)) as [[from_tgt msg_tgt]|] eqn:GET_TGT; cycle 1.
    { exploit COMPLETE; eauto. i. rewrite bot_spec in x0. inv x0. }
    exploit LE; eauto. i. rewrite x in x0.
    destruct msg_tgt; ss; inv x0.
    inv WF_TGT. exploit PROMISES; eauto. i.
    rewrite GET in x0. inv x0. refl.
  Qed.

  Lemma concrete_aux
        pview
        promises_src mem1_src mem2_src
        promises_tgt mem1_tgt mem2_tgt
        (INV1: sem pview bot promises_src promises_tgt)
        (MEM1: sim_memory mem1_src mem1_tgt)
        (CONCRETE_SRC: Memory.concrete mem1_src mem2_src)
        (CONCRETE_TGT: Memory.concrete mem1_tgt mem2_tgt)
        (LE1_SRC: Memory.le promises_src mem1_src)
        (LE1_TGT: Memory.le promises_tgt mem1_tgt)
        (LE2_SRC: Memory.le promises_src mem2_src)
        (LE2_TGT: Memory.le promises_tgt mem2_tgt)
        (CLOSED1_SRC: Memory.closed mem1_src)
        (CLOSED1_TGT: Memory.closed mem1_tgt)
        (NOHALF_SRC: Memory.no_half promises_src mem2_src)
        (NOHALF_TGT: Memory.no_half promises_tgt mem2_tgt):
    sim_memory mem2_src mem2_tgt.
  Proof.
    inv MEM1. econs; i.
    - exploit concrete_covered; try exact CONCRETE_SRC. i.
      exploit concrete_covered; try exact CONCRETE_TGT. i.
      rewrite <- x0. rewrite <- x1. auto.
    - destruct msg_tgt; cycle 1.
      { inv INV1. exploit NOHALF_TGT; eauto. i.
        exploit LE; eauto. i. ss.
        exploit LE2_SRC; eauto. }
      inv CONCRETE_SRC. inv CONCRETE_TGT.
      exploit COMPLETE0; eauto. i. des.
      + exploit MSG; eauto. i. des. inv MSG0.
        exploit SOUND; eauto. i. des; ss. esplits; eauto.
      + dup x. rewrite <- HALF in x0.
        exploit SOUND; eauto. i. des.
        * exploit NOHALF_SRC; eauto. i. inv INV1.
          destruct (Memory.get loc to promises_tgt) eqn:GET_TGT; cycle 1.
          { exploit COMPLETE1; eauto. ss. }
          destruct p. exploit LE; eauto. i.
          rewrite x2 in x3. destruct t1; ss. inv x3.
          exploit LE2_TGT; eauto. i. congr.
        * exploit SOUND0; eauto. i. des; try congr.
          exploit MSG; eauto. i. des.
          rewrite x2 in GET0. inv GET0. rewrite GET in x6. inv x6.
          esplits; eauto.
    - inv INV1. split; i.
      + exploit NOHALF_SRC; eauto. i.
        destruct (Memory.get loc to promises_tgt) eqn:GET_TGT; cycle 1.
        { exploit COMPLETE; eauto. ss. }
        destruct p. exploit LE; eauto. i.
        rewrite x in x0. inv x0. destruct t1; ss. auto.
      + exploit NOHALF_TGT; eauto. i. exploit LE; eauto.
  Qed.

  Lemma concrete
        pview
        lc_src mem1_src mem2_src
        lc_tgt mem1_tgt
        (INV1: sem pview bot lc_src.(Local.promises) lc_tgt.(Local.promises))
        (MEM1: sim_memory mem1_src mem1_tgt)
        (CONCRETE_SRC: Memory.concrete mem1_src mem2_src)
        (WF1_SRC: Local.wf lc_src mem1_src)
        (WF1_TGT: Local.wf lc_tgt mem1_tgt)
        (WF2_SRC: Local.wf lc_src mem2_src)
        (MEM1_SRC: Memory.closed mem1_src)
        (MEM1_TGT: Memory.closed mem1_tgt)
        (HALF_WF1_SRC: Memory.half_wf mem1_src)
        (HALF_WF1_TGT: Memory.half_wf mem1_tgt)
        (NOHALF_SRC: Memory.no_half lc_src.(Local.promises) mem2_src):
    exists mem2_tgt,
      <<MEM2: sim_memory mem2_src mem2_tgt>> /\
      <<CONCRETE_TGT: Memory.concrete mem1_tgt mem2_tgt>> /\
      <<WF2_TGT: Local.wf lc_tgt mem2_tgt>> /\
      <<NOHALF_TGT: Memory.no_half lc_tgt.(Local.promises) mem2_tgt>>.
  Proof.
    exploit Memory.no_half_concrete_future_exists;
      try apply WF1_TGT; eauto. i. des.
    exploit concrete_aux; eauto;
      try apply WF1_SRC; try apply WF2_SRC; try apply WF1_TGT. i.
    esplits; try exact x0; eauto.
    inv WF1_TGT. econs; eauto.
    eapply TView.future_closed; eauto.
  Qed.

  Lemma concrete_cap
        pview
        lc_src mem1_src mem2_src mem3_src
        lc_tgt mem1_tgt
        (INV1: sem pview bot lc_src.(Local.promises) lc_tgt.(Local.promises))
        (MEM1: sim_memory mem1_src mem1_tgt)
        (CONCRETE_SRC: Memory.concrete mem1_src mem2_src)
        (WF1_SRC: Local.wf lc_src mem1_src)
        (WF1_TGT: Local.wf lc_tgt mem1_tgt)
        (WF2_SRC: Local.wf lc_src mem2_src)
        (MEM1_SRC: Memory.closed mem1_src)
        (MEM1_TGT: Memory.closed mem1_tgt)
        (HALF_WF1_SRC: Memory.half_wf mem1_src)
        (HALF_WF1_TGT: Memory.half_wf mem1_tgt)
        (NOHALF_SRC: Memory.no_half lc_src.(Local.promises) mem2_src)
        (CAP_SRC: Memory.cap mem2_src mem3_src):
    exists mem2_tgt mem3_tgt,
      <<MEM3: sim_memory mem3_src mem3_tgt>> /\
      <<CONCRETE_TGT: Memory.concrete mem1_tgt mem2_tgt>> /\
      <<WF2_TGT: Local.wf lc_tgt mem2_tgt>> /\
      <<NOHALF_TGT: Memory.no_half lc_tgt.(Local.promises) mem2_tgt>> /\
      <<CAP_TGT: Memory.cap mem2_tgt mem3_tgt>>.
  Proof.
    exploit concrete; eauto. i. des.
    exploit Memory.concrete_closed; try exact CONCRETE_SRC; eauto. i.
    exploit Memory.concrete_closed; try exact CONCRETE_TGT; eauto. i.
    exploit Memory.cap_future_exists; try exact x1; eauto. i. des.
    exploit sim_memory_cap; try exact MEM2; eauto. i.
    esplits; try exact x2; eauto.
  Qed.

  Lemma concrete_cap_future
        lc mem1 mem2 mem3
        (CONCRETE: Memory.concrete mem1 mem2)
        (WF1: Local.wf lc mem1)
        (WF2: Local.wf lc mem2)
        (MEM1: Memory.closed mem1)
        (HALF_WF1: Memory.half_wf mem1)
        (NOHALF: Memory.no_half lc.(Local.promises) mem2)
        (CAP: Memory.cap mem2 mem3):
      <<FUTURE: Memory.future mem1 mem3>> /\
      <<WF3: Local.wf lc mem3>> /\
      <<HALF_WF3: Memory.half_wf mem3>> /\
      <<NOHALF3: Memory.no_half lc.(Local.promises) mem3>>.
  Proof.
    exploit Memory.no_half_concrete_future; eauto;
      try apply WF1; try apply WF2; i.
    exploit Memory.future_closed; eauto. i.
    exploit Memory.cap_future; eauto. i.
    exploit Local.cap_wf; eauto. i.
    hexploit Memory.concrete_half_wf; eauto. i.
    hexploit Memory.cap_half_wf; eauto. i.
    hexploit Memory.cap_no_half; eauto. i.
    esplits; eauto. etrans; eauto.
  Qed.

  Lemma sem_bot promises:
    sem bot bot promises promises.
  Proof.
    econs.
    - ii. rewrite none_if_bot. ss.
    - i. revert MEM. rewrite bot_spec. congr.
    - i. inv INV.
    - i. congr.
  Qed.

  Lemma sem_bot_inv
        promises_src promises_tgt
        (SEM: sem bot bot promises_src promises_tgt):
    promises_src = promises_tgt.
  Proof.
    apply Memory.ext. i.
    destruct (Memory.get loc ts promises_tgt) as [[? []]|] eqn:X.
    - inv SEM. exploit LE; eauto.
    - destruct (Memory.get loc ts promises_src) as [[? []]|] eqn:Y.
      + inv SEM. exploit LE; eauto. s. i. congr.
      + inv SEM. exploit LE; eauto. s. i. congr.
      + inv SEM. exploit LE; eauto. s. i. congr.
    - destruct (Memory.get loc ts promises_src) as [[? []]|] eqn:Y.
      + inv SEM. exploit COMPLETE; eauto. i. inv x.
      + inv SEM. exploit COMPLETE; eauto. i. inv x.
      + ss.
  Qed.
End SimPromises.
