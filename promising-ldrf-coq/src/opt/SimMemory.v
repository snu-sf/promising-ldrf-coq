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
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.

Require Import Cover.
Require Import MemorySplit.
Require Import MemoryMerge.
Require Import FulfillStep.

Set Implicit Arguments.


Inductive sim_message: forall (msg_src msg_tgt: Message.t), Prop :=
| sim_message_concrete
    val released_src released_tgt
    (RELEASED: View.opt_le released_src released_tgt):
    sim_message (Message.concrete val released_src) (Message.concrete val released_tgt)
| sim_message_reserve:
    sim_message Message.reserve Message.reserve
.
Hint Constructors sim_message.

Program Instance sim_message_PreOrder: PreOrder sim_message.
Next Obligation.
  ii. destruct x; econs; refl.
Qed.
Next Obligation.
  ii. inv H; inv H0; econs. etrans; eauto.
Qed.

Inductive message_same_kind: forall (msg_src msg_tgt: Message.t), Prop :=
| message_same_kind_concrete
    val_src val_tgt released_src released_tgt:
    message_same_kind (Message.concrete val_src released_src) (Message.concrete val_tgt released_tgt)
| same_message_kine_reserve:
    message_same_kind Message.reserve Message.reserve
.
Hint Constructors sim_message.

Program Instance message_same_kind_Equivalence: Equivalence message_same_kind.
Next Obligation.
  ii. destruct x; econs.
Qed.
Next Obligation.
  ii. inv H; econs.
Qed.
Next Obligation.
  ii. inv H; inv H0; econs.
Qed.

Lemma sim_message_message_same_kind
      msg_src msg_tgt
      (SIM: sim_message msg_src msg_tgt):
  message_same_kind msg_src msg_tgt.
Proof.
  inv SIM; econs.
Qed.

Inductive sim_memory (mem_src mem_tgt:Memory.t): Prop :=
| sim_memory_intro
    (COVER: forall loc ts, covered loc ts mem_src <-> covered loc ts mem_tgt)
    (MSG: forall loc from_tgt to msg_tgt
            (GET: Memory.get loc to mem_tgt = Some (from_tgt, msg_tgt)),
        exists from_src msg_src,
          <<GET: Memory.get loc to mem_src = Some (from_src, msg_src)>> /\
          <<MSG: sim_message msg_src msg_tgt>>)
    (RESERVE: forall loc from to,
        Memory.get loc to mem_src = Some (from, Message.reserve) <->
        Memory.get loc to mem_tgt = Some (from, Message.reserve))
.

Program Instance sim_memory_PreOrder: PreOrder sim_memory.
Next Obligation.
  econs; try refl. i. esplits; eauto. refl.
Qed.
Next Obligation.
  ii. inv H. inv H0. econs; try etrans; eauto. i.
  exploit MSG0; eauto. i. des.
  exploit MSG; eauto. i. des.
  esplits; eauto. etrans; eauto.
Qed.


Lemma sim_memory_get
      loc from_tgt to msg_tgt mem_src mem_tgt
      (SIM: sim_memory mem_src mem_tgt)
      (GET: Memory.get loc to mem_tgt = Some (from_tgt, msg_tgt)):
  exists from_src msg_src,
    <<GET: Memory.get loc to mem_src = Some (from_src, msg_src)>> /\
    <<MSG: sim_message msg_src msg_tgt>>.
Proof.
  eapply SIM. eauto.
Qed.

Lemma sim_memory_get_message_same_kind
      loc
      from_src to_src msg_src mem_src
      from_tgt to_tgt msg_tgt mem_tgt
      ts
      (SIM: sim_memory mem_src mem_tgt)
      (GET_SRC: Memory.get loc to_src mem_src = Some (from_src, msg_src))
      (GET_TGT: Memory.get loc to_tgt mem_tgt = Some (from_tgt, msg_tgt))
      (ITV_SRC: Interval.mem (from_src, to_src) ts)
      (ITV_TGT: Interval.mem (from_tgt, to_tgt) ts):
  message_same_kind msg_src msg_tgt.
Proof.
  destruct msg_src, msg_tgt; try by econs.
  - inv SIM. rewrite <- RESERVE in GET_TGT.
    exploit Memory.get_disjoint; [exact GET_SRC|exact GET_TGT|..]. i. des; try congr.
    exfalso. apply (x0 ts); auto.
  - inv SIM. rewrite RESERVE in GET_SRC.
    exploit Memory.get_disjoint; [exact GET_SRC|exact GET_TGT|..]. i. des; try congr.
    exfalso. apply (x0 ts); auto.
Qed.

Lemma sim_memory_get_inv
      loc from_src to_src msg_src mem_src
      mem_tgt
      (INHABITED_SRC: Memory.inhabited mem_src)
      (INHABITED_TGT: Memory.inhabited mem_tgt)
      (SIM: sim_memory mem_src mem_tgt)
      (GET_SRC: Memory.get loc to_src mem_src = Some (from_src, msg_src)):
  exists from_tgt to_tgt msg_tgt,
    <<FROM: Time.le from_tgt from_src>> /\
    <<TO: Time.le to_src to_tgt>> /\
    <<GET_TGT: Memory.get loc to_tgt mem_tgt = Some (from_tgt, msg_tgt)>> /\
    <<MSG: message_same_kind msg_src msg_tgt>>.
Proof.
  destruct (Time.eq_dec to_src Time.bot).
  { subst. rewrite INHABITED_SRC in GET_SRC. inv GET_SRC.
    esplits; try refl. apply INHABITED_TGT. }
  dup SIM. inv SIM0. dup COVER. specialize (COVER0 loc to_src). des.
  exploit COVER0.
  { econs; eauto. econs; try refl.
    exploit Memory.get_ts; eauto. i. des; subst; timetac. }
  i. dup x. inv x0. esplits; eauto.
  - destruct (Time.le_lt_dec from from_src); ss.
    dup COVER. specialize (COVER2 loc from). des. exploit COVER2.
    { econs; eauto.
      exploit Memory.get_ts; try exact GET_SRC. i. des; ss.
      inv ITV. econs; eauto. econs. ss. }
    i. inv x0.
    destruct (Time.eq_dec to0 from).
    + subst. exploit MSG; try exact GET0. i. des.
      exploit Memory.get_disjoint; [exact GET_SRC|exact GET1|..]. i. des.
      * subst. inv ITV. timetac.
      * exfalso. apply (x1 from).
        { inv ITV. econs; eauto. s. econs; eauto. }
        { econs; try refl. s.
          exploit Memory.get_ts; try exact GET1. i. des; ss.
          subst. inv ITV0. inv FROM. }
    + exploit Memory.get_disjoint; [exact GET|exact GET0|..]. i. des.
      * subst. inv ITV0. timetac.
      * exfalso. destruct (Time.le_lt_dec to to0).
        { apply (x1 to).
          - econs; try refl.
            exploit Memory.get_ts; try exact GET. i. des; ss.
            subst. inv ITV0. inv FROM.
          - econs; eauto. inv ITV0. ss.
            exploit Memory.get_ts; try exact GET. i. des; ss.
            + subst. inv l.
            + eapply TimeFacts.lt_le_lt; eauto. econs; eauto. }
        { apply (x1 to0).
          - inv ITV0. econs; ss.
            + inv TO; ss. inv H. congr.
            + econs. ss.
          - econs; try refl.
            exploit Memory.get_ts; try exact GET0. i. des; ss.
            subst. inv ITV0. ss. inv TO; inv H. inv FROM. }
  - inv ITV. ss.
  - eapply sim_memory_get_message_same_kind; eauto.
    exploit Memory.get_ts; try exact GET_SRC. i. des; try congr.
    econs; eauto. refl.
Qed.

Lemma sim_memory_max_ts
      mem_src mem_tgt loc
      (SIM: sim_memory mem_src mem_tgt)
      (CLOSED_SRC: Memory.closed mem_src)
      (CLOSED_TGT: Memory.closed mem_tgt):
  Memory.max_ts loc mem_src = Memory.max_ts loc mem_tgt.
Proof.
  inv SIM. inv CLOSED_SRC. inv CLOSED_TGT.
  clear MSG RESERVE CLOSED CLOSED0.
  apply TimeFacts.antisym.
  - specialize (COVER loc (Memory.max_ts loc mem_src)). des.
    exploit Memory.max_ts_spec; try eapply (INHABITED loc). i. des.
    exploit Memory.get_ts; eauto. i. des.
    { rewrite x1. apply Time.bot_spec. }
    exploit COVER; i.
    { econs; eauto. econs; eauto. refl. }
    inv x. exploit Memory.max_ts_spec; try exact GET0. i. des.
    inv ITV. ss. etrans; eauto.
  - specialize (COVER loc (Memory.max_ts loc mem_tgt)). des.
    exploit Memory.max_ts_spec; try eapply (INHABITED0 loc). i. des.
    exploit Memory.get_ts; eauto. i. des.
    { rewrite x1. apply Time.bot_spec. }
    exploit COVER0; i.
    { econs; eauto. econs; eauto. refl. }
    inv x. exploit Memory.max_ts_spec; try exact GET0. i. des.
    inv ITV. ss. etrans; eauto.
Qed.

Lemma sim_memory_max_concrete_ts
      mem_src mem_tgt
      loc mts_src mts_tgt
      (SIM: sim_memory mem_src mem_tgt)
      (CLOSED_SRC: Memory.closed mem_src)
      (CLOSED_TGT: Memory.closed mem_tgt)
      (MAX_SRC: Memory.max_concrete_ts mem_src loc mts_src)
      (MAX_TGT: Memory.max_concrete_ts mem_tgt loc mts_tgt):
  mts_src = mts_tgt.
Proof.
  apply TimeFacts.antisym.
  - inv MAX_SRC. des.
    exploit sim_memory_get_inv; eauto.
    { apply CLOSED_SRC. }
    { apply CLOSED_TGT. }
    i. des. inv MSG.
    exploit Memory.max_concrete_ts_spec; eauto. i. des.
    etrans; eauto.
  - inv MAX_TGT. des.
    inv SIM. exploit MSG; eauto. i. des. inv MSG0.
    exploit Memory.max_concrete_ts_spec; eauto. i. des. ss.
Qed.

Lemma sim_memory_max_concrete_timemap
      mem_src mem_tgt mtm_src mtm_tgt
      (CLOSED_SRC: Memory.closed mem_src)
      (CLOSED_TGT: Memory.closed mem_tgt)
      (SIM: sim_memory mem_src mem_tgt)
      (MAX_SRC: Memory.max_concrete_timemap mem_src mtm_src)
      (MAX_TGT: Memory.max_concrete_timemap mem_tgt mtm_tgt):
  mtm_src = mtm_tgt.
Proof.
  extensionality loc.
  specialize (MAX_SRC loc).
  specialize (MAX_TGT loc).
  eapply sim_memory_max_concrete_ts; eauto.
Qed.

Lemma sim_memory_max_concrete_view
      mem_src mem_tgt mview_src mview_tgt
      (CLOSED_SRC: Memory.closed mem_src)
      (CLOSED_TGT: Memory.closed mem_tgt)
      (SIM: sim_memory mem_src mem_tgt)
      (MAX_SRC: Memory.max_concrete_view mem_src mview_src)
      (MAX_TGT: Memory.max_concrete_view mem_tgt mview_tgt):
  mview_src = mview_tgt.
Proof.
  inv MAX_SRC. inv MAX_TGT.
  exploit sim_memory_max_concrete_timemap; try exact SIM; eauto. i.
  subst. ss.
Qed.

Lemma split_sim_memory
      mem0 loc ts1 ts2 ts3 val2 released2 val3 released3 mem1
      (SPLIT: Memory.split mem0 loc ts1 ts2 ts3 (Message.concrete val2 released2) (Message.concrete val3 released3) mem1):
  sim_memory mem1 mem0.
Proof.
  econs; i.
  - eapply split_covered. eauto.
  - exploit Memory.split_get0; eauto. i. des.
    erewrite Memory.split_o; eauto. repeat condtac; ss.
    + des. subst. congr.
    + guardH o. des. subst. rewrite GET1 in GET. inv GET.
      esplits; eauto. refl.
    + esplits; eauto. refl.
  - exploit Memory.split_get0; eauto. i. des.
    erewrite Memory.split_o; eauto.
    repeat condtac; ss; split; i; try congr.
    + des. subst. rewrite GET in H. inv H.
    + guardH o. des. subst. rewrite GET0 in H. inv H.
Qed.

Lemma lower_sim_memory
      mem1 loc from to msg1 msg2 mem2
      (LOWER: Memory.lower mem1 loc from to msg1 msg2 mem2)
      (MSG: message_same_kind msg1 msg2):
  sim_memory mem2 mem1.
Proof.
  econs; i.
  - eapply lower_covered. eauto.
  - i. erewrite Memory.lower_o; eauto. condtac; ss.
    + des. subst.
      exploit Memory.lower_get0; eauto. i. des.
      rewrite GET0 in GET. inv GET.
      inv MSG_LE; inv MSG; esplits; eauto.
    + esplits; eauto. refl.
  - split; i.
    + revert H. erewrite Memory.lower_o; eauto. condtac; ss.
      i. des. subst. inv H. inv LOWER. inv LOWER0. inv MSG.
      unfold Memory.get, Cell.get. rewrite GET2. ss.
    + erewrite Memory.lower_o; eauto. condtac; ss.
      des. subst. inv LOWER. inv LOWER0.
      unfold Memory.get, Cell.get in H. rewrite H in GET2. inv GET2.
      inv MSG. ss.
Qed.

Lemma promise_lower_sim_memory
      promises1 mem1 loc from to msg1 msg2 promises2 mem2
      (PROMISE: Memory.promise promises1 mem1 loc from to msg2 promises2 mem2 (Memory.op_kind_lower msg1))
      (MSG: message_same_kind msg1 msg2):
  sim_memory mem2 mem1.
Proof.
  inv PROMISE. eapply lower_sim_memory; eauto.
Qed.

Lemma sim_memory_add
      mem1_src mem1_tgt msg_src
      mem2_src mem2_tgt msg_tgt
      loc from to
      (SIM_MSG: sim_message msg_src msg_tgt)
      (SRC: Memory.add mem1_src loc from to msg_src mem2_src)
      (TGT: Memory.add mem1_tgt loc from to msg_tgt mem2_tgt)
      (SIM: sim_memory mem1_src mem1_tgt):
  sim_memory mem2_src mem2_tgt.
Proof.
  inv SIM. econs; i.
  - rewrite add_covered; [|eauto]. rewrite (@add_covered mem2_tgt); [|eauto].
    econs; i; des; (try by right).
    + left. eapply COVER. eauto.
    + left. eapply COVER. eauto.
  - revert GET. erewrite Memory.add_o; eauto. condtac; ss.
    + des. subst. i. inv GET. esplits; eauto.
      erewrite Memory.add_o; eauto. condtac; ss.
    + erewrite (@Memory.add_o mem2_src); eauto. condtac; ss. eauto.
  - split; i.
    + erewrite Memory.add_o in H; try exact SRC.
      erewrite Memory.add_o; try exact TGT. condtac; ss.
      * des. subst. inv H. inv SIM_MSG. ss.
      * rewrite <- RESERVE. ss.
    + erewrite Memory.add_o in H; try exact TGT.
      erewrite Memory.add_o; try exact SRC. condtac; ss.
      * des. subst. inv H. inv SIM_MSG. ss.
      * rewrite RESERVE. ss.
Qed.

Lemma sim_memory_split
      mem1_src mem1_tgt
      mem2_src mem2_tgt
      loc ts1 ts2 ts3 msg2_src msg3_src msg2_tgt msg3_tgt
      (SIM_MSG: sim_message msg2_src msg2_tgt)
      (SRC: Memory.split mem1_src loc ts1 ts2 ts3 msg2_src msg3_src mem2_src)
      (TGT: Memory.split mem1_tgt loc ts1 ts2 ts3 msg2_tgt msg3_tgt mem2_tgt)
      (SIM: sim_memory mem1_src mem1_tgt):
  sim_memory mem2_src mem2_tgt.
Proof.
  inv SIM. econs; i.
  - rewrite split_covered; [|eauto]. rewrite (@split_covered mem2_tgt); [|eauto].
    apply COVER.
  - revert GET. erewrite Memory.split_o; eauto. repeat condtac; ss.
    + des. subst. i. inv GET. esplits; eauto.
      erewrite Memory.split_o; eauto. condtac; ss.
    + erewrite (@Memory.split_o mem2_src); eauto. repeat condtac; ss.
      i. inv GET. guardH o. guardH o0. des. subst.
      exploit Memory.split_get0; try exact SRC; eauto. i. des.
      exploit Memory.split_get0; try exact TGT; eauto. i. des.
      exploit MSG; eauto. i. des. rewrite GET0 in GET7. inv GET7.
      esplits; eauto.
    + erewrite (@Memory.split_o mem2_src); eauto. repeat condtac; ss. eauto.
  - split; i.
    + erewrite Memory.split_o in H; try exact SRC.
      erewrite Memory.split_o; try exact TGT. repeat condtac; ss.
      * des. subst. inv H. inv SIM_MSG. ss.
      * guardH o. des. subst. inv H.
        exploit Memory.split_get0; try exact SRC. i. des.
        exploit Memory.split_get0; try exact TGT. i. des.
        rewrite RESERVE in GET0. rewrite GET0 in GET4. inv GET4. ss.
      * rewrite <- RESERVE. ss.
    + erewrite Memory.split_o in H; try exact TGT.
      erewrite Memory.split_o; try exact SRC. repeat condtac; ss.
      * des. subst. inv H. inv SIM_MSG. ss.
      * guardH o. des. subst. inv H.
        exploit Memory.split_get0; try exact SRC. i. des.
        exploit Memory.split_get0; try exact TGT. i. des.
        rewrite <- RESERVE in GET4. rewrite GET0 in GET4. inv GET4. ss.
      * rewrite RESERVE. ss.
Qed.

Lemma sim_memory_lower
      mem1_src mem1_tgt
      mem2_src mem2_tgt
      loc from to msg1_src msg2_src msg1_tgt msg2_tgt
      (SIM_MSG: sim_message msg2_src msg2_tgt)
      (SRC: Memory.lower mem1_src loc from to msg1_src msg2_src mem2_src)
      (TGT: Memory.lower mem1_tgt loc from to msg1_tgt msg2_tgt mem2_tgt)
      (SIM: sim_memory mem1_src mem1_tgt):
  sim_memory mem2_src mem2_tgt.
Proof.
  dup SIM. inv SIM0. econs; i.
  - rewrite lower_covered; [|eauto]. rewrite (@lower_covered mem2_tgt); [|eauto].
    apply COVER.
  - revert GET. erewrite Memory.lower_o; eauto. condtac; ss.
    + des. subst. i. inv GET. esplits; eauto.
      erewrite Memory.lower_o; eauto. condtac; ss.
    + erewrite (@Memory.lower_o mem2_src); eauto. condtac; ss. eauto.
  - split; i.
    + erewrite Memory.lower_o in H; try exact SRC.
      erewrite Memory.lower_o; try exact TGT. condtac; ss.
      * des. subst. inv H. inv SIM_MSG. ss.
      * rewrite <- RESERVE. ss.
    + erewrite Memory.lower_o in H; try exact TGT.
      erewrite Memory.lower_o; try exact SRC. condtac; ss.
      * des. subst. inv H. inv SIM_MSG. ss.
      * rewrite RESERVE. ss.
Qed.

Lemma sim_memory_remove
      mem1_src mem1_tgt
      mem2_src mem2_tgt
      loc from to msg_src msg_tgt
      (SRC: Memory.remove mem1_src loc from to msg_src mem2_src)
      (TGT: Memory.remove mem1_tgt loc from to msg_tgt mem2_tgt)
      (SIM: sim_memory mem1_src mem1_tgt):
  sim_memory mem2_src mem2_tgt.
Proof.
  dup SIM. inv SIM0. econs; i.
  - rewrite remove_covered; [|eauto]. rewrite (@remove_covered mem2_tgt); [|eauto].
    rewrite COVER. refl.
  - revert GET. erewrite Memory.remove_o; eauto. condtac; ss.
    erewrite (@Memory.remove_o mem2_src); eauto. condtac; ss. eauto.
  - split; i.
    + erewrite Memory.remove_o in H; try exact SRC.
      erewrite Memory.remove_o; try exact TGT. condtac; ss.
      rewrite <- RESERVE. ss.
    + erewrite Memory.remove_o in H; try exact TGT.
      erewrite Memory.remove_o; try exact SRC. condtac; ss.
      rewrite RESERVE. ss.
Qed.

Lemma sim_memory_closed_timemap
      mem_src mem_tgt
      tm
      (SIM: sim_memory mem_src mem_tgt)
      (TGT: Memory.closed_timemap tm mem_tgt):
  Memory.closed_timemap tm mem_src.
Proof.
  ii. exploit TGT; eauto. i. des.
  exploit sim_memory_get; eauto. i. des.
  inv MSG. eauto.
Qed.

Lemma sim_memory_closed_view
      mem_src mem_tgt
      view
      (SIM: sim_memory mem_src mem_tgt)
      (TGT: Memory.closed_view view mem_tgt):
  Memory.closed_view view mem_src.
Proof.
  econs.
  - eapply sim_memory_closed_timemap; eauto. apply TGT.
  - eapply sim_memory_closed_timemap; eauto. apply TGT.
Qed.

Lemma sim_memory_closed_opt_view
      mem_src mem_tgt
      view
      (SIM: sim_memory mem_src mem_tgt)
      (TGT: Memory.closed_opt_view view mem_tgt):
  Memory.closed_opt_view view mem_src.
Proof.
  inv TGT; econs. eapply sim_memory_closed_view; eauto.
Qed.

Lemma sim_memory_closed_message
      mem_src mem_tgt
      msg
      (SIM: sim_memory mem_src mem_tgt)
      (TGT: Memory.closed_message msg mem_tgt):
  Memory.closed_message msg mem_src.
Proof.
  inv TGT; ss. econs. eapply sim_memory_closed_opt_view; eauto.
Qed.


(* cap *)

Lemma sim_memory_adjacent_src
      mem_src mem_tgt
      loc from1 to1 from2 to2
      (SIM: sim_memory mem_src mem_tgt)
      (CLOSED_SRC: Memory.closed mem_src)
      (CLOSED_TGT: Memory.closed mem_tgt)
      (ADJ: Memory.adjacent loc from1 to1 from2 to2 mem_src)
      (TS: Time.lt to1 from2):
  exists from1' to2',
    Memory.adjacent loc from1' to1 from2 to2' mem_tgt.
Proof.
  dup SIM. inv SIM0. inv ADJ. clear RESERVE TS0.
  assert (GET1_TGT: exists from1' m1', Memory.get loc to1 mem_tgt = Some (from1', m1')).
  { exploit Memory.get_ts; try exact GET1. i. des.
    { subst. esplits. eapply CLOSED_TGT. }
    destruct (COVER loc to1). exploit H; i.
    { econs; try exact GET1. econs; eauto. refl. }
    inv x. inv ITV. ss. inv TO; cycle 1.
    { inv H1. esplits; eauto. }
    exfalso.
    destruct (Time.le_lt_dec to from2).
    { exploit MSG; eauto. i. des.
      exploit (EMPTY to); eauto. i. congr. }
    destruct (COVER loc from2). exploit H3; i.
    { econs; eauto. econs; eauto. econs. ss. }
    inv x. inv ITV. ss. inv TO.
    - exploit Memory.get_ts; try exact GET2. i. des.
      { subst. inv FROM0. }
      exploit Memory.get_ts; try exact GET0. i. des.
      { subst. inv H4. }
      exploit Memory.get_disjoint; [exact GET2|exact GET0|..]. i. des.
      { timetac. }
      destruct (Time.le_lt_dec to2 to0).
      + apply (x3 to2); econs; ss; try refl.
        etrans; try exact FROM0. ss.
      + apply (x3 to0); econs; ss; try refl.
        econs. ss.
    - inv H4. exploit (EMPTY to0); eauto; try refl. i. congr.
  }
  assert (GET2_TGT: exists to2' m2', Memory.get loc to2' mem_tgt = Some (from2, m2')).
  { exploit Memory.get_ts; try exact GET2. i. des.
    { subst. inv TS. }
    exploit Memory.max_ts_spec; try exact GET2. i. des.
    clear from msg GET.
    erewrite sim_memory_max_ts in MAX; eauto.
    exploit TimeFacts.lt_le_lt; try exact x0; try exact MAX. i.
    exploit Memory.next_exists; try exact x1; try eapply CLOSED_TGT. i. des.
    destruct (TimeFacts.le_lt_dec from from2).
    - inv l; cycle 1.
      { inv H. esplits; eauto. }
      destruct (COVER loc from2). exploit H1; i.
      { econs; try exact x2. econs; ss. econs; ss. }
      inv x. inv ITV. ss. inv TO; cycle 1.
      { inv H2. exploit (EMPTY to0); eauto; try refl. i. congr. }
      exploit Memory.get_disjoint; [exact GET2|exact GET|..]. i. des.
      { subst. timetac. }
      exfalso.
      destruct (TimeFacts.le_lt_dec to2 to0).
      + apply (x5 to2); econs; ss; try refl.
        etrans; try exact FROM. ss.
      + apply (x5 to0); econs; ss; try refl.
        * econs. ss.
        * etrans; eauto.
    - destruct (TimeFacts.le_lt_dec to2 from).
      + destruct (COVER loc to2). exploit H; i.
        { econs; eauto. econs; ss. refl. }
        inv x. inv ITV. ss.
        exploit (x4 to0); eauto; try congr.
        { eapply TimeFacts.lt_le_lt; try exact TO; ss. }
        destruct (Time.le_lt_dec to to0); ss.
        exploit Memory.get_ts; try exact x2. i. des.
        { subst. inv x3. }
        exploit Memory.get_disjoint; [exact x2|exact GET|..]. i. des.
        { subst. timetac. }
        exfalso.
        apply (x6 to); econs; ss; try refl.
        etrans; try exact FROM.
        eapply TimeFacts.le_lt_lt; try exact x5. ss.
      + destruct (COVER loc from). exploit H; i.
        { econs; try exact GET2. econs; ss. econs. ss. }
        inv x. inv ITV. ss.
        destruct (TimeFacts.le_lt_dec to to0).
        * exploit Memory.get_ts; try exact x2. i. des.
          { subst. inv x3. }
          exploit Memory.get_ts; try exact GET. i. des.
          { subst. timetac. }
          exploit Memory.get_disjoint; [exact x2|exact GET|..]. i. des.
          { subst. timetac. }
          exfalso.
          apply (x7 to); econs; ss; try refl.
          eapply TimeFacts.lt_le_lt; try exact FROM. econs. ss.
        * exploit (x4 to0); ss; try congr.
          eapply TimeFacts.lt_le_lt; try exact TO; ss.
  }
  des. esplits. econs; eauto; i.
  { exploit Memory.get_ts; try exact GET2_TGT. i. des.
    - subst. inv TS.
    - etrans; eauto. }
  destruct (Memory.get loc ts mem_tgt) as [[]|] eqn:GET; ss.
  exfalso.
  exploit Memory.get_ts; try exact GET. i. des.
  { subst. inv TS1. }
  destruct (COVER loc ts). exploit H0; i.
  { econs; eauto. econs; ss. refl. }
  inv x. inv ITV. ss.
  destruct (TimeFacts.le_lt_dec to from2).
  { exploit (EMPTY to); try congr.
    eapply TimeFacts.lt_le_lt; try exact TS1. ss. }
  exploit Memory.get_ts; try exact GET2. i. des.
  { subst. inv TS. }
  exploit Memory.get_ts; try exact GET0. i. des.
  { subst. inv l. }
  exploit Memory.get_disjoint; [exact GET2|exact GET0|..]. i. des.
  { subst. timetac. }
  destruct (TimeFacts.le_lt_dec to2 to).
  - apply (x3 to2); econs; ss; try refl.
    etrans; try exact x1.
    eapply TimeFacts.lt_le_lt; try exact TS2. ss.
  - apply (x3 to); econs; ss; try refl. econs. ss.
Qed.

Lemma sim_memory_adjacent_tgt
      mem_src mem_tgt
      loc from1 to1 from2 to2
      (SIM: sim_memory mem_src mem_tgt)
      (CLOSED_SRC: Memory.closed mem_src)
      (CLOSED_TGT: Memory.closed mem_tgt)
      (ADJ: Memory.adjacent loc from1 to1 from2 to2 mem_tgt)
      (TS: Time.lt to1 from2):
  exists from1' to2',
    Memory.adjacent loc from1' to1 from2 to2' mem_src.
Proof.
  dup SIM. inv SIM0. inv ADJ. clear RESERVE TS0.
  assert (GET1_SRC: exists from1' m1', Memory.get loc to1 mem_src = Some (from1', m1')).
  { exploit MSG; try exact GET1. i. des. eauto. }
  assert (GET2_SRC: exists to2' m2', Memory.get loc to2' mem_src = Some (from2, m2')).
  { exploit Memory.get_ts; try exact GET2. i. des.
    { subst. inv TS. }
    exploit Memory.max_ts_spec; try exact GET2. i. des.
    clear from msg GET.
    erewrite <- sim_memory_max_ts in MAX; eauto.
    exploit TimeFacts.lt_le_lt; try exact x0; try exact MAX. i.
    exploit Memory.next_exists; try exact x1; try eapply CLOSED_SRC. i. des.
    destruct (TimeFacts.le_lt_dec from from2).
    - inv l; cycle 1.
      { inv H. esplits; eauto. }
      destruct (COVER loc from2). exploit H0; i.
      { econs; try exact x2. econs; ss. econs; ss. }
      inv x. inv ITV. ss. inv TO; cycle 1.
      { inv H2. exploit (EMPTY to0); eauto; try refl. i. congr. }
      exploit Memory.get_disjoint; [exact GET2|exact GET|..]. i. des.
      { subst. timetac. }
      exfalso.
      destruct (TimeFacts.le_lt_dec to2 to0).
      + apply (x5 to2); econs; ss; try refl.
        etrans; try exact FROM. ss.
      + apply (x5 to0); econs; ss; try refl.
        * econs. ss.
        * etrans; eauto.
    - destruct (TimeFacts.le_lt_dec to2 from).
      + destruct (COVER loc to2). exploit H0; i.
        { econs; eauto. econs; ss. refl. }
        inv x. inv ITV. ss.
        exploit (x4 to0); eauto; try congr.
        { eapply TimeFacts.lt_le_lt; try exact TO; ss. }
        destruct (Time.le_lt_dec to to0); ss.
        exploit Memory.get_ts; try exact x2. i. des.
        { subst. inv x3. }
        exploit Memory.get_disjoint; [exact x2|exact GET|..]. i. des.
        { subst. timetac. }
        exfalso.
        apply (x6 to); econs; ss; try refl.
        etrans; try exact FROM.
        eapply TimeFacts.le_lt_lt; try exact x5. ss.
      + destruct (COVER loc from). exploit H0; i.
        { econs; try exact GET2. econs; ss. econs. ss. }
        inv x. inv ITV. ss.
        destruct (TimeFacts.le_lt_dec to to0).
        * exploit Memory.get_ts; try exact x2. i. des.
          { subst. inv x3. }
          exploit Memory.get_ts; try exact GET. i. des.
          { subst. timetac. }
          exploit Memory.get_disjoint; [exact x2|exact GET|..]. i. des.
          { subst. timetac. }
          exfalso.
          apply (x7 to); econs; ss; try refl.
          eapply TimeFacts.lt_le_lt; try exact FROM. econs. ss.
        * exploit (x4 to0); ss; try congr.
          eapply TimeFacts.lt_le_lt; try exact TO; ss.
  }
  des. esplits. econs; eauto; i.
  { exploit Memory.get_ts; try exact GET2_SRC. i. des.
    - subst. inv TS.
    - etrans; eauto. }
  destruct (Memory.get loc ts mem_src) as [[]|] eqn:GET; ss.
  exfalso.
  exploit Memory.get_ts; try exact GET. i. des.
  { subst. inv TS1. }
  destruct (COVER loc ts). exploit H; i.
  { econs; eauto. econs; ss. refl. }
  inv x. inv ITV. ss.
  destruct (TimeFacts.le_lt_dec to from2).
  { exploit (EMPTY to); try congr.
    eapply TimeFacts.lt_le_lt; try exact TS1. ss. }
  exploit Memory.get_ts; try exact GET2. i. des.
  { subst. inv TS. }
  exploit Memory.get_ts; try exact GET0. i. des.
  { subst. inv l. }
  exploit Memory.get_disjoint; [exact GET2|exact GET0|..]. i. des.
  { subst. timetac. }
  destruct (TimeFacts.le_lt_dec to2 to).
  - apply (x3 to2); econs; ss; try refl.
    etrans; try exact x1.
    eapply TimeFacts.lt_le_lt; try exact TS2. ss.
  - apply (x3 to); econs; ss; try refl. econs. ss.
Qed.

Lemma sim_memory_cap_get_src
      mem1_src mem2_src
      mem1_tgt mem2_tgt
      loc from to msg
      (MEM1: sim_memory mem1_src mem1_tgt)
      (CAP_SRC: Memory.cap mem1_src mem2_src)
      (CAP_TGT: Memory.cap mem1_tgt mem2_tgt)
      (MEM1_SRC: Memory.closed mem1_src)
      (MEM1_TGT: Memory.closed mem1_tgt)
      (GET1_SRC: Memory.get loc to mem1_src = None)
      (GET2_SRC: Memory.get loc to mem2_src = Some (from, msg)):
  <<MSG: msg = Message.reserve>> /\
  <<GET1_TGT: Memory.get loc to mem1_tgt = None>> /\
  <<GET2_TGT: Memory.get loc to mem2_tgt = Some (from, msg)>>.
Proof.
  exploit Memory.cap_inv; try exact CAP_SRC; eauto. i. des; try congr.
  - subst.
    exploit sim_memory_adjacent_src; try exact x1; eauto. i. des.
    inv CAP_TGT. exploit MIDDLE; eauto. i. splits; auto.
    inv x3. apply EMPTY; eauto. refl.
  - subst.
    erewrite sim_memory_max_ts; eauto.
    inv CAP_TGT. splits; auto.
    destruct (Memory.get loc (Time.incr (Memory.max_ts loc mem1_tgt)) mem1_tgt) as [[]|] eqn:MAX; ss.
    exploit Memory.max_ts_spec; eauto. i. des.
    specialize (Time.incr_spec (Memory.max_ts loc mem1_tgt)). i. timetac.
Qed.

Lemma sim_memory_cap_get_tgt
      mem1_src mem2_src
      mem1_tgt mem2_tgt
      loc from to msg
      (MEM1: sim_memory mem1_src mem1_tgt)
      (CAP_SRC: Memory.cap mem1_src mem2_src)
      (CAP_TGT: Memory.cap mem1_tgt mem2_tgt)
      (MEM1_SRC: Memory.closed mem1_src)
      (MEM1_TGT: Memory.closed mem1_tgt)
      (GET1_TGT: Memory.get loc to mem1_tgt = None)
      (GET2_TGT: Memory.get loc to mem2_tgt = Some (from, msg)):
  <<MSG: msg = Message.reserve>> /\
  <<GET1_SRC: Memory.get loc to mem1_src = None>> /\
  <<GET2_SRC: Memory.get loc to mem2_src = Some (from, msg)>>.
Proof.
  exploit Memory.cap_inv; try exact CAP_TGT; eauto. i. des; try congr.
  - subst.
    exploit sim_memory_adjacent_tgt; try exact x1; eauto. i. des.
    inv CAP_SRC. exploit MIDDLE; eauto. i. splits; auto.
    inv x3. apply EMPTY; eauto. refl.
  - subst.
    erewrite <- sim_memory_max_ts; eauto.
    inv CAP_SRC. splits; auto.
    destruct (Memory.get loc (Time.incr (Memory.max_ts loc mem1_src)) mem1_src) as [[]|] eqn:MAX; ss.
    exploit Memory.max_ts_spec; eauto. i. des.
    specialize (Time.incr_spec (Memory.max_ts loc mem1_src)). i. timetac.
Qed.

Lemma sim_memory_cap
      mem1_src mem2_src
      mem1_tgt mem2_tgt
      (MEM1: sim_memory mem1_src mem1_tgt)
      (CAP_SRC: Memory.cap mem1_src mem2_src)
      (CAP_TGT: Memory.cap mem1_tgt mem2_tgt)
      (MEM1_SRC: Memory.closed mem1_src)
      (MEM1_TGT: Memory.closed mem1_tgt):
  <<MEM2: sim_memory mem2_src mem2_tgt>>.
Proof.
  econs; i; try split; i.
  - inv H.
    destruct (Memory.get loc to mem1_src) as [[]|] eqn:GET1.
    + inv CAP_SRC. exploit SOUND; eauto. i.
      rewrite x in GET. inv GET.
      eapply cap_covered; eauto.
      inv MEM1. rewrite <- COVER.
      econs; eauto.
    + exploit sim_memory_cap_get_src; eauto. i. des.
      econs; eauto.
  - inv H.
    destruct (Memory.get loc to mem1_tgt) as [[]|] eqn:GET1.
    + inv CAP_TGT. exploit SOUND; eauto. i.
      rewrite x in GET. inv GET.
      eapply cap_covered; eauto.
      inv MEM1. rewrite COVER.
      econs; eauto.
    + exploit sim_memory_cap_get_tgt; eauto. i. des.
      econs; eauto.
  - destruct (Memory.get loc to mem1_tgt) as [[]|] eqn:GET1.
    + inv CAP_TGT. exploit SOUND; eauto. i.
      rewrite x in GET. inv GET.
      inv MEM1. exploit MSG; eauto. i. des.
      inv CAP_SRC. exploit SOUND; eauto. i.
      esplits; eauto.
    + exploit sim_memory_cap_get_tgt; eauto. i. des.
      esplits; eauto. refl.
  - destruct (Memory.get loc to mem1_src) as [[]|] eqn:GET1.
    + inv CAP_SRC. exploit SOUND; eauto. i.
      rewrite x in H. inv H.
      inv MEM1. rewrite RESERVE in GET1.
      inv CAP_TGT. exploit SOUND0; eauto.
    + exploit sim_memory_cap_get_src; eauto. i. des. auto.
  - destruct (Memory.get loc to mem1_tgt) as [[]|] eqn:GET1.
    + inv CAP_TGT. exploit SOUND; eauto. i.
      rewrite x in H. inv H.
      inv MEM1. rewrite <- RESERVE in GET1.
      inv CAP_SRC. exploit SOUND0; eauto.
    + exploit sim_memory_cap_get_tgt; eauto. i. des. auto.
Qed.


(* fulfill_step *)

Lemma fulfill_write_sim_memory
      lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2
      (FULFILL: fulfill_step lc1 sc1 loc from to val releasedm released ord lc2 sc2)
      (REL_WF: View.opt_wf releasedm)
      (REL_CLOSED: Memory.closed_opt_view releasedm mem1)
      (ORD: Ordering.le ord Ordering.relaxed)
      (WF1: Local.wf lc1 mem1)
      (SC1: Memory.closed_timemap sc1 mem1)
      (MEM1: Memory.closed mem1):
  exists released' mem2',
    <<STEP: Local.write_step lc1 sc1 mem1 loc from to val releasedm released' ord lc2 sc2 mem2' (Memory.op_kind_lower (Message.concrete val released))>> /\
    <<REL_LE: View.opt_le released' released>> /\
    <<MEM: sim_memory mem2' mem1>>.
Proof.
  inv FULFILL.
  exploit TViewFacts.write_future_fulfill;
    try exact REL_CLOSED; try exact SC1; eauto; try by apply WF1.
  { apply WF1. eapply Memory.remove_get0. eauto. }
  i. des.
  exploit MemorySplit.remove_promise_remove;
    try exact REMOVE; eauto; try apply WF1; try by econs; eauto.
  { econs. inv REL_LE; try apply Time.bot_spec.
    cut (Time.le (View.rlx (View.unwrap (Some lhs)) loc)
                 (View.rlx (View.unwrap (Some rhs)) loc)).
    { i. etrans; eauto.
      cut (Memory.message_to (Message.concrete val (Some rhs)) loc to).
      { i. inv H1. auto. }
      eapply MEM1. apply WF1. eapply Memory.remove_get0. eauto. }
    destruct lhs; destruct rhs; inv LE; ss. }
  i. des.
  esplits; eauto.
  - econs; eauto.
    i. destruct ord; inv ORD; inv H.
  - eapply promise_lower_sim_memory; eauto. econs.
Qed.

Lemma promise_fulfill_write_sim_memory
      lc0 sc0 mem0 loc from to val releasedm released ord lc1 lc2 sc2 mem2 kind
      (PROMISE: Local.promise_step lc0 mem0 loc from to (Message.concrete val released) lc1 mem2 kind)
      (FULFILL: fulfill_step lc1 sc0 loc from to val releasedm released ord lc2 sc2)
      (REL_WF: View.opt_wf releasedm)
      (REL_CLOSED: Memory.closed_opt_view releasedm mem0)
      (ORD: Ordering.le Ordering.strong_relaxed ord -> Memory.nonsynch_loc loc (Local.promises lc0))
      (WF0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0):
  exists released' mem2',
    <<STEP: Local.write_step lc0 sc0 mem0 loc from to val releasedm released' ord lc2 sc2 mem2' kind>> /\
    <<REL_LE: View.opt_le released' released>> /\
    <<MEM: sim_memory mem2' mem2>> /\
    <<REL: released' = TView.write_released (Local.tview lc0) sc0 loc to releasedm ord>>.
Proof.
  exploit Local.promise_step_future; eauto. i. des.
  inv PROMISE. inv FULFILL. ss.
  exploit TViewFacts.write_future_fulfill; try exact REL_WF; eauto; try by apply WF2.
  { eapply Memory.future_closed_opt_view; eauto. }
  { eapply Memory.promise_get2; eauto. inv PROMISE0; ss. }
  s. i. des.
  exploit MemorySplit.remove_promise_remove;
    try exact REMOVE; eauto; try apply WF2; try by econs; eauto.
  { econs. inv REL_LE; try apply Time.bot_spec.
    cut (Time.le (View.rlx (View.unwrap (Some lhs)) loc)
                 (View.rlx (View.unwrap (Some rhs)) loc)).
    { i. etrans; eauto.
      cut (Memory.message_to (Message.concrete val (Some rhs)) loc to).
      { i. inv H1. auto. }
      eapply CLOSED2. apply WF2. eapply Memory.remove_get0. eauto. }
    destruct lhs; destruct rhs; inv LE; ss. }
  i. des.
  esplits; eauto.
  - econs; eauto. econs; eauto.
    eapply MemoryMerge.promise_promise_promise; eauto.
  - eapply promise_lower_sim_memory; eauto. econs.
Qed.
