Require Import RelationClasses.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import Loc.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Language.

Require Import Event.
Require Import Time.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import MemoryFacts.
Require Import MemoryDomain.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.

Require Import Cover.

Require Import SimMemory.

Set Implicit Arguments.


Module SimPromises.
  Include MemoryDomain.

  Definition none_if_released loc ts (pview:t) (released:option View.t): option View.t :=
    if mem loc ts pview
    then None
    else released.

  Definition none_if loc ts (pview:t) (msg:Message.t): Message.t :=
    match msg with
    | Message.concrete val released =>
      Message.concrete val (none_if_released loc ts pview released)
    | Message.reserve => Message.reserve
    end.

  Lemma none_if_bot loc ts msg:
    none_if loc ts bot msg = msg.
  Proof.
    destruct msg; ss.
  Qed.

  Ltac none_if_tac :=
    repeat
      (try match goal with
           | [ |- context[none_if _ _ _ (Message.concrete ?val ?released)]] =>
             unfold none_if; ss
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
    | Memory.op_kind_cancel => Memory.op_kind_cancel
    end.

  Lemma kind_transf_bot loc ts kind:
    kind_transf loc ts bot kind = kind.
  Proof.
    destruct kind; ss; rewrite none_if_bot; ss.
  Qed.

  Inductive sem (pview:t) (inv:t) (promises_src promises_tgt:Memory.t): Prop :=
  | sem_intro
      (LE: mem_le_transf pview promises_tgt promises_src)
      (PVIEW: forall l t (MEM: mem l t pview), exists f val released, Memory.get l t promises_tgt = Some (f, Message.concrete val released))
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
        (LE1_TGT: Memory.le promises1_tgt mem1_tgt)
        (MEM1_SRC: Memory.closed mem1_src)
        (MEM1_TGT: Memory.closed mem1_tgt):
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
        * econs 1; eauto; try congr.
          i. exploit sim_memory_get_inv; try exact GET; eauto.
          { apply MEM1_SRC. }
          { apply MEM1_TGT. }
          i. des. inv FROM; cycle 1.
          { inv H. eauto. }
          exploit Memory.add_get0; try exact MEM. i. des.
          exploit Memory.add_get1; try exact GET_TGT; eauto. i.
          exploit Memory.get_ts; try exact GET1. i. des.
          { subst. inv H. }
          exploit Memory.get_ts; try exact x3. i. des.
          { subst. inv TO; inv H0.
            exploit Memory.get_ts; try exact GET. i. des; timetac. inv x5. }
          exploit Memory.get_disjoint; [exact GET1|exact x3|..]. i. des.
          { subst. congr. }
          apply (x6 to); econs; ss; try refl.
          exploit Memory.get_ts; try exact GET. i. des.
          { subst. eauto. }
          { etrans; eauto. econs. ss. }
        * econs 1; eauto; ss.
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
        unfold none_if_released. condtac; ss.
        * inv INV1. exploit PVIEW; eauto. i. des.
          hexploit Memory.split_get0; try exact PROMISES; eauto. congr.
        * subst. econs 2; eauto. ss. eauto.
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
        * none_if_tac; viewtac. econs. viewtac.
        * subst. ss. esplits; eauto.
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
    - exploit Memory.remove_get0; try exact PROMISES. i. des.
      exploit (@Memory.remove_exists promises1_src loc from to Message.reserve).
      { inv INV1. exploit LE; eauto. }
      i. des.
      exploit (@Memory.remove_exists mem1_src loc from to Message.reserve).
      { inv INV1. exploit LE; eauto. }
      i. des.
      exploit sim_memory_remove; try exact SIM1; eauto. i.
      esplits; try exact x2; eauto.
      inv INV1. econs; ii.
      + erewrite Memory.remove_o in LHS; eauto.
        erewrite Memory.remove_o; eauto.
        condtac; ss. eauto.
      + exploit PVIEW; eauto. i. des.
        erewrite Memory.remove_o; eauto. condtac; ss; eauto.
        des. subst. congr.
      + exploit SOUND; eauto. i. des. split.
        * erewrite Memory.remove_o; eauto. condtac; ss; eauto.
        * erewrite Memory.remove_o; eauto. condtac; ss; eauto.
          des. subst. congr.
      + erewrite Memory.remove_o in SRC; eauto.
        erewrite Memory.remove_o in TGT; eauto.
        des_ifs. eauto.
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
        (LE1_TGT: Memory.le promises1_tgt mem1_tgt)
        (MEM1_SRC: Memory.closed mem1_src)
        (MEM1_TGT: Memory.closed mem1_tgt):
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
    hexploit Memory.remove_future; eauto. i. des.
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
