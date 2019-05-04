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
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.

Require Import SimMemory.
Require Import MemorySplit.
Require Import MemoryMerge.

Set Implicit Arguments.


Module SimPromises.
  Definition t := Loc.t -> DOSet.t.

  Definition mem loc ts (promises:t) := DOSet.mem ts (promises loc).

  Lemma ext lhs rhs
        (EXT: forall loc ts, mem loc ts lhs = mem loc ts rhs):
    lhs = rhs.
  Proof.
    apply LocFun.ext. unfold LocFun.find. i.
    apply DOSet.eq_leibniz. ii.
    specialize (EXT i a). unfold mem in *. econs; i.
    - apply DOSet.mem_spec. erewrite <- EXT.
      apply DOSet.mem_spec. auto.
    - apply DOSet.mem_spec. erewrite EXT.
      apply DOSet.mem_spec. auto.
  Qed.

  Definition bot: t := fun _ => DOSet.empty.

  Lemma bot_spec loc ts: mem loc ts bot = false.
  Proof.
    unfold mem, bot. apply DOSet.Facts.empty_b.
  Qed.

  Definition le (lhs rhs:t): Prop :=
    forall loc ts, mem loc ts lhs -> mem loc ts rhs.

  Definition join (lhs rhs:t): t :=
    fun loc => DOSet.union (lhs loc) (rhs loc).

  Lemma join_comm lhs rhs: join lhs rhs = join rhs lhs.
  Proof.
    apply LocFun.ext. unfold LocFun.find, join. i.
    apply DOSet.eq_leibniz. ii.
    rewrite ? DOSet.union_spec. econs; i; des; auto.
  Qed.

  Lemma join_assoc a b c: join (join a b) c = join a (join b c).
  Proof.
    apply LocFun.ext. unfold LocFun.find, join. i.
    apply DOSet.eq_leibniz. ii.
    rewrite ? DOSet.union_spec. econs; i; des; auto.
  Qed.

  Lemma join_l lhs rhs: le lhs (join lhs rhs).
  Proof.
    unfold join. ii. unfold mem in *.
    rewrite DOSet.Facts.union_b, H. auto.
  Qed.

  Lemma join_r lhs rhs: le rhs (join lhs rhs).
  Proof. rewrite join_comm. apply join_l. Qed.

  Lemma join_spec lhs rhs o
        (LHS: le lhs o)
        (RHS: le rhs o):
    le (join lhs rhs) o.
  Proof.
    unfold join. ii.
    unfold mem in *. rewrite DOSet.Facts.union_b in *.
    apply Bool.orb_true_iff in H. des; eauto.
  Qed.

  Definition set (loc:Loc.t) (ts:Time.t) (promises:t) :=
    LocFun.add loc (DOSet.add ts (promises loc)) promises.

  Lemma set_o loc1 ts1 loc2 ts2 promises:
    mem loc1 ts1 (set loc2 ts2 promises) =
    if loc_ts_eq_dec (loc1, ts1) (loc2, ts2)
    then true
    else mem loc1 ts1 promises.
  Proof.
    unfold mem, set, LocFun.add, LocFun.find.
    repeat (try condtac; ss; des; subst; try congr).
    - rewrite DOSet.Facts.add_b.
      unfold DOSet.Facts.eqb. rewrite Time.eq_dec_eq. auto.
    - rewrite DOSet.Facts.add_b.
      unfold DOSet.Facts.eqb. rewrite Time.eq_dec_neq; auto.
  Qed.

  Lemma set_eq loc ts promises:
    mem loc ts (set loc ts promises) = true.
  Proof.
    rewrite set_o. condtac; ss. des; congr.
  Qed.

  Lemma set_inv loc1 ts1 loc2 ts2 promises
        (MEM: mem loc1 ts1 (set loc2 ts2 promises)):
    (loc1 = loc2 /\ ts1 = ts2) \/ mem loc1 ts1 promises.
  Proof.
    revert MEM. rewrite set_o. repeat condtac; ss; auto.
  Qed.

  Definition unset (loc:Loc.t) (ts:Time.t) (promises:t) :=
    LocFun.add loc (DOSet.remove ts (promises loc)) promises.

  Lemma unset_o loc1 ts1 loc2 ts2 promises:
    mem loc1 ts1 (unset loc2 ts2 promises) =
    if loc_ts_eq_dec (loc1, ts1) (loc2, ts2)
    then false
    else mem loc1 ts1 promises.
  Proof.
    unfold mem, unset, LocFun.add, LocFun.find.
    repeat (try condtac; ss; des; subst; try congr).
    - rewrite DOSet.Facts.remove_b.
      unfold DOSet.Facts.eqb. rewrite Time.eq_dec_eq.
      apply Bool.andb_false_iff. auto.
    - rewrite DOSet.Facts.remove_b.
      unfold DOSet.Facts.eqb. rewrite Time.eq_dec_neq; auto.
      apply Bool.andb_true_r.
  Qed.

  Lemma unset_eq loc ts promises:
    mem loc ts (unset loc ts promises) = false.
  Proof.
    rewrite unset_o. condtac; ss. des; congr.
  Qed.

  Lemma unset_inv loc1 ts1 loc2 ts2 promises
        (MEM: mem loc1 ts1 (unset loc2 ts2 promises)):
    ~ (loc1 = loc2 /\ ts1 = ts2) /\ mem loc1 ts1 promises.
  Proof.
    revert MEM. rewrite unset_o. condtac; ss. i.
    splits; auto. ii. des; auto.
  Qed.

  Lemma unset_set loc to inv
        (MEM: mem loc to inv = false):
    unset loc to (set loc to inv) = inv.
  Proof.
    apply ext. i.
    rewrite unset_o, set_o.  condtac; ss. des. subst. auto.
  Qed.

  Lemma unset_bot loc to:
    unset loc to bot = bot.
  Proof.
    apply ext. i. rewrite unset_o. condtac; ss.
  Qed.

  Inductive disjoint (lhs rhs:t): Prop :=
  | disjoint_intro
      (DISJOINT: forall loc ts
                   (LHS: mem loc ts lhs)
                   (RHS: mem loc ts rhs),
          False).

  Global Program Instance disjoint_Symmetric: Symmetric disjoint.
  Next Obligation.
    econs. ii. eapply H; eauto.
  Qed.

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
        * econs 1; eauto.
        * econs 1; eauto.
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
          { econs 2; eauto. }
        * econs 2; eauto.
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

  Lemma split_exists
        pview
        promises_src mem1_src
        promises_tgt mem1_tgt
        loc from to msg_src
        (INV1: sem pview bot promises_src promises_tgt)
        (SIM1: sim_memory mem1_src mem1_tgt)
        (GET1_SRC: Memory.get loc to mem1_src = Some (from, msg_src))
        (LE1_SRC: Memory.le promises_src mem1_src)
        (LE1_TGT: Memory.le promises_tgt mem1_tgt)
        (CLOSED1_SRC: Memory.closed mem1_src)
        (CLOSED1_TGT: Memory.closed mem1_tgt):
    exists mem2_tgt msg_tgt,
      <<FUTURE_TGT: Memory.future mem1_tgt mem2_tgt>> /\
      <<GET2_TGT: Memory.get loc to mem2_tgt = Some (from, msg_tgt)>> /\
      <<LE2_TGT: Memory.le promises_tgt mem2_tgt>> /\
      <<SIM2: sim_memory mem1_src mem2_tgt>>.
  Proof.
    exploit sim_memory_split_exists; try exact SIM1; eauto. i. des.
    - subst. esplits; eauto.
    - exploit Memory.split_get0; eauto. i. des.
      subst. esplits.
      + econs 2. econs; eauto. refl.
      + eauto.
      + ii. erewrite Memory.split_o; eauto. repeat condtac; ss.
        * des. subst. exploit LE1_TGT; eauto. i.
          rewrite GET in x. inv x.
        * guardH o. des. subst. exploit LE1_TGT; eauto. i.
          rewrite GET0 in x. inv x.
          inv INV1. exploit LE; eauto. i.
          exploit LE1_SRC; eauto. i.
          exploit Memory.get_disjoint; [exact GET1_SRC|exact x0|..]. i. des.
          { subst. timetac. }
          { exfalso.
            exploit Memory.get_ts; try exact GET1_SRC. i. des.
            { subst. inv CLOSED1_TGT. rewrite INHABITED in GET. inv GET. }
            apply (x2 to); econs; ss; try refl. econs; eauto. }
        * eapply LE1_TGT; eauto.
      + auto.
    - exploit Memory.split_get0; eauto. i. des.
      subst. esplits.
      + econs 2. econs; eauto. refl.
      + eauto.
      + ii. erewrite Memory.split_o; eauto. repeat condtac; ss.
        * des. subst. exploit LE1_TGT; eauto. i.
          rewrite GET in x. inv x.
        * guardH o. des. subst. exploit LE1_TGT; eauto. i.
          rewrite GET0 in x. inv x.
          inv INV1. exploit LE; eauto. i.
          exploit LE1_SRC; eauto. i.
          exploit Memory.get_disjoint; [exact GET1_SRC|exact x0|..]. i. des.
          { subst. timetac. }
          { exfalso.
            exploit Memory.get_ts; try exact GET1_SRC. i. des.
            { subst. inv CLOSED1_TGT. rewrite INHABITED in GET. inv GET. }
            exploit Memory.get_ts; try exact GET0. i. des.
            { subst. inv x3. }
            apply (x2 to_tgt); econs; ss; try refl. }
        * apply LE1_TGT; eauto.
      + auto.
    - exploit Memory.split_get0; try exact SPLIT. i. des.
      exploit Memory.split_get0; try exact SPLIT2. i. des.
      subst. esplits.
      + econs 2. econs; eauto.
        econs 2. econs; eauto. refl.
      + eauto.
      + ii. erewrite Memory.split_o; eauto. repeat condtac; ss.
        * des. subst. exploit LE1_TGT; eauto. i.
          revert GET3. erewrite Memory.split_o; eauto. repeat condtac; ss. i.
          rewrite GET3 in x. inv x.
        * guardH o. des. subst. exploit LE1_TGT; eauto. i.
          rewrite GET in x. inv x.
        * guardH o. guardH o0.
          erewrite Memory.split_o; eauto. repeat condtac; ss.
          { guardH o1. des. subst. exploit LE1_TGT; eauto. i.
            rewrite GET0 in x. inv x.
            inv INV1. exploit LE; eauto. i.
            exploit LE1_SRC; eauto. i.
            exploit Memory.get_disjoint; [exact GET1_SRC|exact x0|..]. i. des.
            - subst. timetac.
            - exfalso.
              exploit Memory.get_ts; try exact GET1_SRC. i. des.
              { subst. inv FROM. }
              exploit Memory.get_ts; try exact GET0. i. des.
              { subst. inv TO. }
              apply (x2 to); econs; ss; try refl.
              + eapply TimeFacts.lt_le_lt; try exact FROM. econs; eauto.
              + econs; eauto. }
          { apply LE1_TGT; eauto. }
      + auto.
  Qed.

  Lemma future_aux_imm
        pview
        promises_src mem1_src mem2_src
        promises_tgt mem1_tgt
        (FUTURE_SRC: Memory.future_imm mem1_src mem2_src)
        (INV1: sem pview bot promises_src promises_tgt)
        (SIM1: sim_memory mem1_src mem1_tgt)
        (LE1_SRC: Memory.le promises_src mem1_src)
        (LE1_TGT: Memory.le promises_tgt mem1_tgt)
        (LE2_SRC: Memory.le promises_src mem2_src)
        (CLOSED1_SRC: Memory.closed mem1_src)
        (CLOSED1_TGT: Memory.closed mem1_tgt):
    exists mem2_tgt,
      <<FUTURE_TGT: Memory.future mem1_tgt mem2_tgt>> /\
      <<LE2_TGT: Memory.le promises_tgt mem2_tgt>> /\
      <<SIM2: sim_memory mem2_src mem2_tgt>>.
  Proof.
    inv FUTURE_SRC. inv OP.
    - destruct msg; cycle 1.
      { exploit (@Memory.add_exists mem1_tgt loc from to Message.half).
        { eapply covered_disjoint; try apply SIM1; eauto. inv ADD. inv ADD0. auto. }
        { inv ADD. inv ADD0. auto. }
        { econs. }
        i. des. esplits.
        - econs 2; eauto.
        - ii. erewrite Memory.add_o; eauto. condtac; ss; eauto.
          des. subst. exploit LE1_TGT; eauto. exploit Memory.add_get0; eauto. i. des. congr.
        - eapply sim_memory_add; eauto. }
      exploit (@Memory.max_full_released_exists mem1_tgt loc to).
      { eapply CLOSED1_TGT. }
      i. des.
      exploit (@Memory.add_exists mem1_tgt loc from to (Message.full val (Some released0))).
      { eapply covered_disjoint; try apply SIM1; eauto. inv ADD. inv ADD0. auto. }
      { inv ADD. inv ADD0. auto. }
      { econs. econs. eapply Memory.max_full_released_wf; eauto. }
      i. des.
      exploit Memory.max_full_released_closed_add; eauto. i. des.
      esplits.
      + econs 2; eauto. econs; eauto.
      + ii. erewrite Memory.add_o; eauto. condtac; ss; eauto.
        des. subst. exploit LE1_TGT; eauto. exploit Memory.add_get0; eauto. i. des. congr.
      + eapply sim_memory_add; try exact ADD; try exact x1; eauto.
        econs. eapply Memory.max_full_released_spec_add; try exact ADD; eauto.
        * inv CLOSED. ss.
        * inv TS. ss.
        * exploit Memory.max_full_released_exists; try apply CLOSED1_SRC. i. des.
          exploit sim_memory_max_full_released; try exact SIM1; eauto. i. subst.
          auto.
    - exploit Memory.split_get0; eauto. i. des.
      exploit split_exists; eauto. i. des.
      exploit Memory.future_closed; eauto. intro CLOSED2_TGT.
      destruct msg; cycle 1.
      { exploit (@Memory.split_exists mem2_tgt loc from to to3 Message.half msg_tgt).
        { eauto. }
        { inv SPLIT. inv SPLIT0. ss. }
        { inv SPLIT. inv SPLIT0. ss. }
        { econs. }
        intro SPLIT_TGT. des. esplits.
        - etrans; try exact FUTURE_TGT. econs 2; eauto.
        - exploit Memory.split_get0; try exact SPLIT_TGT. i. des.
          ii. exploit LE2_TGT; eauto. i.
          erewrite Memory.split_o; eauto. repeat condtac; ss.
          + des. subst. rewrite GET3 in x. inv x.
          + guardH o. des. subst. rewrite GET4 in x. inv x.
            inv INV1. exploit LE; eauto. i.
            exploit LE2_SRC; eauto. i.
            exploit Memory.get_disjoint; [exact GET2|exact x0|..]. i. des.
            * subst. inv SPLIT. inv SPLIT0. timetac.
            * exfalso.
              exploit Memory.get_ts; try exact GET2. i. des.
              { subst. rewrite GET in GET0. inv GET0. }
              exploit Memory.get_ts; try exact x0. i. des.
              { subst. inv x3. }
              apply (x2 to3); econs; ss; try refl.
        - eapply sim_memory_split; eauto.
      }
      exploit (@Memory.max_full_released_exists mem2_tgt loc to).
      { apply CLOSED2_TGT. }
      i. des.
      exploit (@Memory.split_exists mem2_tgt loc from to to3 (Message.full val (Some released0)) msg_tgt).
      { eauto. }
      { inv SPLIT. inv SPLIT0. ss. }
      { inv SPLIT. inv SPLIT0. ss. }
      { econs. econs. eapply Memory.max_full_released_wf; eauto. }
      intro SPLIT_TGT. des. esplits.
      + etrans; try exact FUTURE_TGT. econs 2; try refl. econs; eauto.
        * econs. econs. eapply Memory.max_full_released_closed_split; eauto.
        * econs. eapply Memory.max_full_released_closed_split; eauto.
      + exploit Memory.split_get0; try exact SPLIT_TGT. i. des.
        ii. exploit LE2_TGT; eauto. i.
        erewrite Memory.split_o; eauto. repeat condtac; ss.
        * des. subst. rewrite GET3 in x. inv x.
        * guardH o. des. subst. rewrite GET4 in x. inv x.
          inv INV1. exploit LE; eauto. i.
          exploit LE2_SRC; eauto. i.
          exploit Memory.get_disjoint; [exact GET2|exact x1|..]. i. des.
          { subst. inv SPLIT. inv SPLIT0. timetac. }
          { exfalso.
            exploit Memory.get_ts; try exact GET2. i. des.
            { subst. rewrite GET in GET0. inv GET0. }
            exploit Memory.get_ts; try exact x1. i. des.
            { subst. inv x4. }
            apply (x3 to3); econs; ss; try refl. }
      + eapply sim_memory_split; try exact SIM2; try exact SPLIT; try exact SPLIT_TGT.
        econs.
        exploit Memory.max_full_released_exists; try apply CLOSED1_SRC. i. des.
        exploit sim_memory_max_full_released; try exact SIM2; eauto; i. subst.
        inv CLOSED. inv TS.
        eapply Memory.max_full_released_spec_split; try exact SPLIT; eauto.
    - exploit Memory.lower_get0; eauto. i. des.
      exploit split_exists; eauto. i. des.
      exploit Memory.future_closed; eauto. intro CLOSED2_TGT.
      exploit (@Memory.max_full_released_exists mem2_tgt loc to).
      { apply CLOSED2_TGT. }
      intro MAX. des.
      dup SIM2. inv SIM0. exploit MSG; eauto. i. des.
      rewrite GET in GET1. symmetry in GET1. inv GET1.
      clear COVER COVER_HALF MSG.
      exploit (@Memory.lower_exists mem2_tgt loc from to msg_tgt
                                    (match msg with
                                     | Message.half => Message.half
                                     | Message.full val _ =>
                                       (match msg_tgt with
                                        | Message.half => Message.full val (Some released)
                                        | _ => msg_tgt
                                        end)
                                     end)).
      { eauto. }
      { inv LOWER. inv LOWER0. ss. }
      { destruct msg; destruct msg_tgt; ss; econs.
        - inv CLOSED2_TGT. exploit CLOSED0; eauto. i. des.
          inv MSG_WF. ss.
        - econs. eapply Memory.max_full_released_wf; eauto. }
      { destruct msg; destruct msg_tgt; ss.
        - econs. refl.
        - inv LOWER. inv LOWER0. inv MSG_LE0. inv MSG0. }
      intro LOWER_TGT. des. esplits.
      + etrans; try exact FUTURE_TGT. econs 2; try refl. econs; eauto.
        * destruct msg; destruct msg_tgt; try by econs.
          { inv CLOSED2_TGT. exploit CLOSED0; eauto. i. des.
            eapply Memory.lower_closed_message; eauto. }
          { econs. econs. eapply Memory.max_full_released_closed_lower; eauto. }
        * destruct msg; destruct msg_tgt; try by econs.
          { inv CLOSED2_TGT. exploit CLOSED0; eauto. i. des.
            exploit Memory.lower_closed_message; eauto. }
          { econs. eapply Memory.max_full_released_closed_lower; eauto. }
      + exploit Memory.lower_get0; try exact LOWER_TGT. i. des.
        ii. exploit LE2_TGT; eauto. i.
        erewrite Memory.lower_o; eauto. repeat condtac; ss.
        * des. subst. rewrite GET1 in x. inv x.
          inv LOWER_TGT. inv MSG_LE0. ss.
        * des. subst. rewrite GET1 in x. inv x.
          inv LOWER_TGT. inv MSG_LE0.
        * des. subst. rewrite GET1 in x. inv x.
          destruct msg; ss.
          inv INV1. exploit LE; eauto. i.
          exploit LE2_SRC; eauto. i. ss.
          rewrite GET0 in x0. inv x0.
      + eapply sim_memory_lower; try exact SIM2; try exact LOWER; try exact LOWER_TGT.
        destruct msg; ss. destruct msg_tgt; ss.
        * inv LOWER. inv LOWER0. inv MSG0. inv MSG_LE0.
          econs. etrans; eauto.
        * econs.
          exploit Memory.max_full_released_exists; try apply CLOSED1_SRC. i. des.
          exploit sim_memory_max_full_released; try exact SIM2; eauto. i. subst.
          inv CLOSED. inv TS.
          eapply Memory.max_full_released_spec_lower; try exact LOWER; eauto.
  Qed.

  Lemma future_aux
        pview
        promises_src mem1_src mem2_src
        promises_tgt mem1_tgt
        (FUTURE_SRC: Memory.future mem1_src mem2_src)
        (INV1: sem pview bot promises_src promises_tgt)
        (SIM1: sim_memory mem1_src mem1_tgt)
        (LE1_SRC: Memory.le promises_src mem1_src)
        (LE1_TGT: Memory.le promises_tgt mem1_tgt)
        (LE2_SRC: Memory.le promises_src mem2_src)
        (CLOSED1_SRC: Memory.closed mem1_src)
        (CLOSED1_TGT: Memory.closed mem1_tgt):
    exists mem2_tgt,
      <<FUTURE_TGT: Memory.future mem1_tgt mem2_tgt>> /\
      <<LE2_TGT: Memory.le promises_tgt mem2_tgt>> /\
      <<SIM2: sim_memory mem2_src mem2_tgt>>.
  Proof.
    revert INV1 SIM1 LE1_SRC LE1_TGT LE2_SRC CLOSED1_SRC CLOSED1_TGT.
    revert promises_src promises_tgt mem1_tgt.
    induction FUTURE_SRC; i.
    { esplits; eauto. }
    assert (LE_SRC: Memory.le promises_src y).
    { ii. exploit LE1_SRC; eauto. i.
      exploit Memory.future_get1; try exact x0.
      { econs 2; [|refl]. eauto. }
      i. des.
      exploit Memory.future_get1; try exact GET; eauto. i. des.
      erewrite LE2_SRC in GET0; eauto. inv GET0.
      rewrite GET. f_equal. f_equal.
      - apply TimeFacts.antisym; eauto.
      - destruct msg', msg'0; inv MSG_LE; inv MSG_LE0; ss.
        f_equal. apply View.opt_antisym; eauto.
    }
    exploit future_aux_imm; eauto. i. des.
    exploit IHFUTURE_SRC; eauto.
    { eapply Memory.future_closed; try exact CLOSED1_SRC; eauto. }
    { eapply Memory.future_closed; try exact CLOSED1_TGT; eauto. }
    i. des.
    esplits.
    - etrans; eauto.
    - auto.
    - auto.
  Qed.

  Lemma future
        pview
        lc_src mem1_src mem2_src
        lc_tgt mem1_tgt
        (INV1: sem pview bot lc_src.(Local.promises) lc_tgt.(Local.promises))
        (MEM1: sim_memory mem1_src mem1_tgt)
        (FUTURE_SRC: Memory.future mem1_src mem2_src)
        (WF1_SRC: Local.wf lc_src mem1_src)
        (WF1_TGT: Local.wf lc_tgt mem1_tgt)
        (WF2_SRC: Local.wf lc_src mem2_src)
        (MEM1_SRC: Memory.closed mem1_src)
        (MEM1_TGT: Memory.closed mem1_tgt):
    exists mem2_tgt,
      <<MEM2: sim_memory mem2_src mem2_tgt>> /\
      <<FUTURE_TGT: Memory.future mem1_tgt mem2_tgt>> /\
      <<WF2_TGT: Local.wf lc_tgt mem2_tgt>> /\
      <<MEM2_TGT: Memory.closed mem2_tgt>>.
  Proof.
    exploit future_aux; eauto.
    { apply WF1_SRC. }
    { apply WF1_TGT. }
    { apply WF2_SRC. }
    i. des.
    esplits; eauto.
    - econs; eauto.
      + apply WF1_TGT.
      + eapply TView.future_closed; eauto. apply WF1_TGT.
      + apply WF1_TGT.
    - eapply Memory.future_closed; eauto.
  Qed.

  Lemma future_sc_mem
        pview
        lc_src mem1_src mem2_src sc1_src sc2_src
        lc_tgt mem1_tgt sc1_tgt
        (INV1: sem pview bot lc_src.(Local.promises) lc_tgt.(Local.promises))
        (MEM1: sim_memory mem1_src mem1_tgt)
        (MEM_FUTURE_SRC: Memory.future mem1_src mem2_src)
        (SC_FUTURE_SRC: TimeMap.le sc1_src sc2_src)
        (WF1_SRC: Local.wf lc_src mem1_src)
        (WF1_TGT: Local.wf lc_tgt mem1_tgt)
        (WF2_SRC: Local.wf lc_src mem2_src)
        (MEM1_SRC: Memory.closed mem1_src)
        (MEM1_TGT: Memory.closed mem1_tgt)
        (SC1_SRC: Memory.closed_timemap sc1_src mem1_src)
        (SC1_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
        (SC2_SRC: Memory.closed_timemap sc2_src mem2_src)
        (NOHALF_SRC: Memory.no_half lc_src.(Local.promises) mem2_src):
    exists sc2_tgt mem2_tgt,
      <<SC2: TimeMap.le sc2_src sc2_tgt>> /\
      <<MEM2: sim_memory mem2_src mem2_tgt>> /\
      <<SC_FUTURE_TGT: TimeMap.le sc1_tgt sc2_tgt>> /\
      <<MEM_FUTURE_TGT: Memory.future mem1_tgt mem2_tgt>> /\
      <<WF2_TGT: Local.wf lc_tgt mem2_tgt>> /\
      <<SC2_TGT: Memory.closed_timemap sc2_tgt mem2_tgt>> /\
      <<MEM2_TGT: Memory.closed mem2_tgt>> /\
      <<NOHALF_TGT: Memory.no_half lc_tgt.(Local.promises) mem2_tgt>>.
  Proof.
    exploit Memory.future_closed; eauto. intro MEM2_SRC.
    exploit future; eauto. i. des.
    exploit Memory.max_full_timemap_exists; try apply MEM2_SRC. i. des.
    exploit Memory.max_full_timemap_exists; try apply MEM2_TGT. i. des.
    exploit sim_memory_max_full_timemap; try exact MEM2; eauto. i. subst.
    esplits; eauto.
    - etrans; [|refl].
      eapply Memory.max_full_timemap_spec; try exact x0; eauto.
    - etrans; [|refl].
      eapply Memory.max_full_timemap_spec; try exact x1; eauto.
      eapply Memory.future_closed_timemap; eauto.
    - eapply Memory.max_full_timemap_closed; eauto.
    - ii. dup MEM2. inv MEM0. inv INV1.
      exploit MSG; eauto. i. des. inv MSG0.
      exploit NOHALF_SRC; eauto. i.
      destruct (Memory.get loc to lc_tgt.(Local.promises)) as [[from_tgt msg_tgt]|] eqn:GET_TGT; cycle 1.
      { exploit COMPLETE; eauto. i. rewrite bot_spec in x2. inv x2. }
      exploit LE; eauto. i. rewrite x in x2.
      destruct msg_tgt; ss; inv x2.
      inv WF2_TGT. exploit PROMISES; eauto. i.
      rewrite GET in x2. inv x2. refl.
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
