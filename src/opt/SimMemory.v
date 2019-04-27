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

Set Implicit Arguments.


Inductive sim_message: forall (msg_src msg_tgt: Message.t), Prop :=
| sim_message_full
    val released_src released_tgt
    (RELEASED: View.opt_le released_src released_tgt):
    sim_message (Message.mk val released_src) (Message.mk val released_tgt)
| sim_message_half:
    sim_message Message.half Message.half
.
Hint Constructors sim_message.

Program Instance sim_message_PreOrder: PreOrder sim_message.
Next Obligation.
  ii. destruct x; econs; refl.
Qed.
Next Obligation.
  ii. inv H; inv H0; econs. etrans; eauto.
Qed.

Inductive same_message_kind: forall (msg_src msg_tgt: Message.t), Prop :=
| same_message_kind_full
    val_src val_tgt released_src released_tgt:
    same_message_kind (Message.mk val_src released_src) (Message.mk val_tgt released_tgt)
| same_message_kine_half:
    same_message_kind Message.half Message.half
.
Hint Constructors sim_message.

Program Instance same_message_kind_PreOrder: PreOrder same_message_kind.
Next Obligation.
  ii. destruct x; econs.
Qed.
Next Obligation.
  ii. inv H; inv H0; econs.
Qed.

Lemma sim_message_same_message_kind
      msg_src msg_tgt
      (SIM: sim_message msg_src msg_tgt):
  same_message_kind msg_src msg_tgt.
Proof.
  inv SIM; econs.
Qed.

Inductive covered (loc:Loc.t) (ts:Time.t) (mem:Memory.t): Prop :=
| covered_intro
    from to msg
    (GET: Memory.get loc to mem = Some (from, msg))
    (ITV: Interval.mem (from, to) ts)
.

Inductive covered_half (loc: Loc.t) (ts: Time.t) (mem: Memory.t): Prop :=
| covered_half_intro
    from to
    (GET: Memory.get loc to mem = Some (from, Message.half))
    (ITV: Interval.mem (from, to) ts)
.

Inductive sim_memory (mem_src mem_tgt:Memory.t): Prop :=
| sim_memory_intro
    (COVER: forall loc ts, covered loc ts mem_src <-> covered loc ts mem_tgt)
    (COVER_HALF: forall loc ts, covered_half loc ts mem_src <-> covered_half loc ts mem_tgt)
    (MSG: forall loc from_tgt to msg_tgt
            (GET: Memory.get loc to mem_tgt = Some (from_tgt, msg_tgt)),
        exists from_src msg_src,
          <<GET: Memory.get loc to mem_src = Some (from_src, msg_src)>> /\
          <<MSG: sim_message msg_src msg_tgt>>)
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

Lemma sim_memory_get_from
      loc from_src from_tgt to_src to_tgt msg_src msg_tgt mem_src mem_tgt
      (SIM: sim_memory mem_src mem_tgt)
      (GET_SRC: Memory.get loc to_src mem_src = Some (from_src, msg_src))
      (GET_TGT: Memory.get loc to_tgt mem_tgt = Some (from_tgt, msg_tgt))
      (FROM: Time.lt from_tgt from_src)
      (TO: Time.le to_src to_tgt):
  exists from_src' msg_src',
    Memory.get loc from_src mem_src = Some (from_src', msg_src').
Proof.
  exploit Memory.get_ts; try exact GET_SRC. i.
  exploit Memory.get_ts; try exact GET_TGT. i.
  des; subst; try by inv FROM.
  { subst. inv TO; inv H. inv x0. }
  inv SIM. specialize (COVER loc from_src). des.
  exploit COVER0.
  { econs; eauto. econs; timetac.
    econs. eapply TimeFacts.lt_le_lt; eauto. }
  i. inv x.
  destruct (Time.eq_dec to from_src).
  { subst. esplits; eauto. }
  inv ITV. ss. inv TO0; cycle 1.
  { inv H. congr. }
  exploit MemoryFacts.get_disjoint; [exact GET_SRC|exact GET|..]. i. des.
  { subst. timetac. }
  exfalso. destruct (Time.le_lt_dec to_src to).
  - apply (x2 to_src).
    + econs; eauto. refl.
    + econs; eauto.
  - apply (x2 to).
    + repeat econs; eauto.
    + econs; eauto. refl.
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
    <<MSG: same_message_kind msg_src msg_tgt>>.
Proof.
  destruct (Time.eq_dec to_src Time.bot).
  { subst. rewrite INHABITED_SRC in GET_SRC. inv GET_SRC.
    esplits; try refl. apply INHABITED_TGT. }
  inv SIM. dup COVER. specialize (COVER0 loc to_src). des.
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
      exploit MemoryFacts.get_disjoint; [exact GET_SRC|exact GET1|..]. i. des.
      * subst. inv ITV. timetac.
      * exfalso. apply (x1 from).
        { inv ITV. econs; eauto. s. econs; eauto. }
        { econs; try refl. s.
          exploit Memory.get_ts; try exact GET1. i. des; ss.
          subst. inv ITV0. inv FROM. }
    + exploit MemoryFacts.get_disjoint; [exact GET|exact GET0|..]. i. des.
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
  - destruct msg_src; destruct msg; try econs.
    + specialize (COVER_HALF loc to_src). des.
      exploit COVER_HALF0; try by econs; eauto. i. inv x0.
      destruct (Time.eq_dec to_src to0).
      * subst. rewrite GET_SRC in GET0. inv GET0.
      * exfalso.
        exploit MemoryFacts.get_disjoint; [exact GET_SRC|exact GET0|..]. i. des; ss.
        apply (x1 to_src); auto.
        exploit Memory.get_ts; try exact GET_SRC. i.
        exploit Memory.get_ts; try exact GET0. i. des; ss.
        { subst. rewrite INHABITED_SRC in GET0. inv GET0. }
        { econs; eauto. refl. }
    + specialize (COVER_HALF loc to_src). des.
      exploit COVER_HALF.
      { econs; eauto.
        exploit Memory.get_ts; try exact GET_SRC. i. des; ss.
        econs; eauto. refl. }
      i. inv x0.
      destruct (Time.eq_dec to to0).
      * subst. rewrite GET in GET0. inv GET0.
      * exfalso.
        exploit MemoryFacts.get_disjoint; [exact GET|exact GET0|..]. i. des; ss.
        apply (x1 to_src); auto.
Qed.

(* Lemma sim_memory_get_from *)
(*       loc from_src from_tgt to msg_src msg_tgt mem_src mem_tgt *)
(*       (SIM: sim_memory mem_src mem_tgt) *)
(*       (GET_SRC: Memory.get loc to mem_src = Some (from_src, msg_src)) *)
(*       (GET_TGT: Memory.get loc to mem_tgt = Some (from_tgt, msg_tgt)): *)
(*   <<FROM: Time.le from_tgt from_src>> /\ *)
(*   <<MSG: sim_message msg_src msg_tgt>>. *)
(* Proof. *)
(*   inv SIM. split; cycle 1. *)
(*   { exploit MSG; eauto. i. des. *)
(*     rewrite GET in GET_SRC. inv GET_SRC. ss. } *)
(*   destruct (Time.le_lt_dec from_tgt from_src); ss. *)
(*   generalize COVER. intro X. *)
(*   specialize (X loc from_tgt). des. *)
(*   exploit X. *)
(*   { econs; eauto. econs; ss. *)
(*     exploit Memory.get_ts; try exact GET_TGT. *)
(*     i. des; subst. *)
(*     - inv l. *)
(*     - econs. ss. } *)
(*   i. inv x. *)
(*   exploit MemoryFacts.get_disjoint; [exact GET_TGT|exact GET|..]. *)
(*   i. des. *)
(*   - subst. inv ITV. ss. timetac. *)
(*   - exploit Memory.get_ts; try exact GET_TGT. i. *)
(*     exploit Memory.get_ts; try exact GET. i. *)
(*     des; subst; try by apply Time.bot_spec. *)
(*     { inv ITV. ss. timetac. } *)
(*     destruct (Time.le_lt_dec to to0). *)
(*     + exploit (x0 to); ss; econs; timetac; try refl. *)
(*       inv ITV. etrans; eauto. *)
(*     + exploit MSG; try exact GET. i. des. *)
(*       exploit Memory.get_ts; try exact GET_SRC. i. *)
(*       exploit Memory.get_ts; try exact GET0. i. *)
(*       des; subst; timetac. *)
(*       { inv x2. } *)
(*       { inv l0. } *)
(*       exploit MemoryFacts.get_disjoint;  [exact GET_SRC|exact GET0|..]. *)
(*       i. des; timetac. *)
(*       inv ITV. ss. exfalso. apply (x5 to0); econs; ss; try refl. *)
(*       * eapply TimeFacts.lt_le_lt; try exact l. ss. *)
(*       * econs; eauto. *)
(* Qed. *)

Lemma sim_memory_max_full_timemap
      mem_src mem_tgt mtm_src mtm_tgt
      (CLOSED_SRC: Memory.closed mem_src)
      (CLOSED_TGT: Memory.closed mem_tgt)
      (SIM: sim_memory mem_src mem_tgt)
      (MAX_SRC: Memory.max_full_timemap mem_src mtm_src)
      (MAX_TGT: Memory.max_full_timemap mem_tgt mtm_tgt):
  mtm_src = mtm_tgt.
Proof.
  apply TimeMap.antisym.
  - eapply Memory.max_full_timemap_spec'; eauto. i.
    destruct (MAX_SRC loc). des.
    exploit sim_memory_get_inv; eauto.
    { apply CLOSED_SRC. }
    { apply CLOSED_TGT. }
    i. des. inv MSG. esplits; eauto.
  - eapply Memory.max_full_timemap_spec'; eauto. i.
    destruct (MAX_TGT loc). des.
    inv SIM. exploit MSG; eauto. i. des.
    inv MSG0. esplits; eauto.
Qed.

Lemma sim_memory_max_full_view
      mem_src mem_tgt mview_src mview_tgt
      (CLOSED_SRC: Memory.closed mem_src)
      (CLOSED_TGT: Memory.closed mem_tgt)
      (SIM: sim_memory mem_src mem_tgt)
      (MAX_SRC: Memory.max_full_view mem_src mview_src)
      (MAX_TGT: Memory.max_full_view mem_tgt mview_tgt):
  mview_src = mview_tgt.
Proof.
  inv MAX_SRC. inv MAX_TGT.
  exploit sim_memory_max_full_timemap; try exact SIM; eauto. i.
  subst. ss.
Qed.

Lemma sim_memory_max_full_released
      mem_src mem_tgt loc ts mr_src mr_tgt
      (CLOSED_SRC: Memory.closed mem_src)
      (CLOSED_TGT: Memory.closed mem_tgt)
      (SIM: sim_memory mem_src mem_tgt)
      (MAX_SRC: Memory.max_full_released mem_src loc ts mr_src)
      (MAX_TGT: Memory.max_full_released mem_tgt loc ts mr_tgt):
  mr_src = mr_tgt.
Proof.
  inv MAX_SRC. inv MAX_TGT.
  exploit sim_memory_max_full_timemap; try exact SIM; eauto. i.
  subst. ss.
Qed.

Lemma covered_disjoint
      mem1 mem2 loc from to
      (COVER: forall loc ts, covered loc ts mem1 -> covered loc ts mem2)
      (DISJOINT: forall to2 from2 msg2
                   (GET2: Memory.get loc to2 mem2 = Some (from2, msg2)),
          Interval.disjoint (from, to) (from2, to2)):
  forall to2 from2 msg2
    (GET2: Memory.get loc to2 mem1 = Some (from2, msg2)),
    Interval.disjoint (from, to) (from2, to2).
Proof.
  ii. exploit COVER; eauto.
  { econs; eauto. }
  i. inv x0. eapply DISJOINT; eauto.
Qed.

Lemma get_disjoint_covered_disjoint
      mem loc from to:
  (forall t f m, Memory.get loc t mem = Some (f, m) -> Interval.disjoint (from, to) (f, t)) ->
  (forall ts, covered loc ts mem -> ~ Interval.mem (from, to) ts).
Proof.
  ii. inv H0. eapply H; eauto.
Qed.

Lemma covered_disjoint_get_disjoint
      mem loc from to:
  (forall ts, covered loc ts mem -> ~ Interval.mem (from, to) ts) ->
  (forall t f m, Memory.get loc t mem = Some (f, m) -> Interval.disjoint (from, to) (f, t)).
Proof.
  ii. eapply H; eauto. econs; eauto.
Qed.

Lemma add_covered
      mem2 mem1 loc from to msg
      l t
      (ADD: Memory.add mem1 loc from to msg mem2):
  covered l t mem2 <->
  covered l t mem1 \/ (l = loc /\ Interval.mem (from, to) t).
Proof.
  econs; i.
  - inv H. revert GET. erewrite Memory.add_o; eauto. condtac; ss.
    + des. subst. i. inv GET. auto.
    + left. econs; eauto.
  - des.
    + inv H. econs; eauto.
      erewrite Memory.add_o; eauto. condtac; ss; eauto.
      des. subst. exploit Memory.add_get0; eauto. i. des. congr.
    + subst. econs; eauto. erewrite Memory.add_o; eauto. condtac; ss.
      des; congr.
Qed.

Lemma split_covered
      mem2 mem1 loc ts1 ts2 ts3 msg2 msg3
      l t
      (SPLIT: Memory.split mem1 loc ts1 ts2 ts3 msg2 msg3 mem2):
  covered l t mem2 <-> covered l t mem1.
Proof.
  econs; i.
  - exploit Memory.split_get0; eauto. i. des.
    inv H. revert GET3. erewrite Memory.split_o; eauto. repeat condtac; ss.
    + des. subst. i. inv GET3. econs; eauto.
      eapply Interval.le_mem; eauto. econs; [refl|].
      inv SPLIT. inv SPLIT0. left. auto.
    + guardH o. des. subst. i. inv GET3. econs; eauto.
      eapply Interval.le_mem; eauto. econs; [|refl].
      inv SPLIT. inv SPLIT0. left. auto.
    + i. econs; eauto.
  - exploit Memory.split_get0; eauto. i. des.
    inv H.
    destruct (loc_ts_eq_dec (l, to) (loc, ts3)); ss.
    + des. subst. rewrite GET0 in GET3. inv GET3.
      destruct (Time.le_lt_dec t ts2).
      * econs.
        { instantiate (2 := from). instantiate (2 := ts2).
          erewrite Memory.split_o; eauto. condtac; ss.
          des; congr.
        }
        { inv ITV. econs; ss. }
      * econs.
        { instantiate (2 := ts2). instantiate (2 := ts3).
          erewrite Memory.split_o; eauto. repeat condtac; ss.
          - des. subst. inv SPLIT. inv SPLIT0.
            exfalso. eapply Time.lt_strorder. eauto.
          - guardH o. des; congr.
        }
        { inv ITV. econs; ss. }
    + econs; eauto. erewrite Memory.split_o; eauto.
      repeat condtac; ss; eauto.
      * guardH o. des. subst. congr.
      * guardH o. guardH o0. des. subst.
        unguardH o. des; congr.
Qed.

Lemma lower_covered
      mem2 mem1 loc from to msg1 msg2
      l t
      (LOWER: Memory.lower mem1 loc from to msg1 msg2 mem2):
  covered l t mem2 <-> covered l t mem1.
Proof.
  econs; i.
  - inv H. revert GET. erewrite Memory.lower_o; eauto. condtac; ss.
    + des. subst. i. inv GET. econs; eauto.
      hexploit Memory.lower_get0; eauto. i. des. eauto.
    + i. econs; eauto.
  - exploit Memory.lower_get0; eauto. i. des.
    inv H.
    destruct (loc_ts_eq_dec (l, to0) (loc, to)); ss.
    + des. subst. econs; cycle 1; eauto.
      erewrite Memory.lower_o; eauto. condtac; [|by des].
      rewrite GET in GET1. inv GET1. eauto.
    + econs; eauto.
      erewrite Memory.lower_o; eauto. rewrite GET1. condtac; ss.
      des; congr.
Qed.

Lemma add_covered_half
      mem2 mem1 loc from to msg
      l t
      (ADD: Memory.add mem1 loc from to msg mem2):
  covered_half l t mem2 <->
  covered_half l t mem1 \/
  (l = loc /\ Interval.mem (from, to) t /\ msg = Message.half).
Proof.
  econs; i.
  - inv H. revert GET. erewrite Memory.add_o; eauto. condtac; ss.
    + des. subst. i. inv GET. auto.
    + left. econs; eauto.
  - des.
    + inv H. econs; eauto.
      erewrite Memory.add_o; eauto. condtac; ss; eauto.
      des. subst. exploit Memory.add_get0; eauto. i. des. congr.
    + subst. econs; eauto. erewrite Memory.add_o; eauto. condtac; ss.
      des; congr.
Qed.

Lemma split_covered_half
      mem2 mem1 loc ts1 ts2 ts3 msg2 msg3
      l t
      (SPLIT: Memory.split mem1 loc ts1 ts2 ts3 msg2 msg3 mem2):
  covered_half l t mem2 <->
  ((l <> loc \/ ~ Interval.mem (ts1, ts2) t) /\ covered_half l t mem1) \/
  (msg2 = Message.half /\ l = loc /\ Interval.mem (ts1, ts2) t).
Proof.
(*   econs; i. *)
(*   - exploit Memory.split_get0; eauto. i. des. *)
(*     inv H. revert GET3. erewrite Memory.split_o; eauto. repeat condtac; ss. *)
(*     + des. subst. i. inv GET3. eauto. *)
(*     + guardH o. des. subst. i. inv GET3. *)
(*       left. econs; eauto. *)
(*       eapply Interval.le_mem; eauto. econs; [|refl]. *)
(*       inv SPLIT. inv SPLIT0. left. auto. *)
(*     + i. left. econs; eauto. *)
(*   - exploit Memory.split_get0; eauto. i. des. *)
(*     + inv H. *)
(*       destruct (loc_ts_eq_dec (l, to) (loc, ts3)); ss. *)
(*       * des. subst. rewrite GET0 in GET3. inv GET3. *)
(*         destruct (Time.le_lt_dec t ts2). *)
(*         { econs. *)
(*           - instantiate (2 := from). instantiate (2 := ts2). *)
(*             erewrite Memory.split_o; eauto. condtac; ss. *)
(*             des; congr. *)
(*           - inv ITV. econs; ss. *)
(*         } *)
(*         { econs. *)
(*           - instantiate (2 := ts2). instantiate (2 := ts3). *)
(*           erewrite Memory.split_o; eauto. repeat condtac; ss. *)
(*             + des. subst. inv SPLIT. inv SPLIT0. *)
(*             exfalso. eapply Time.lt_strorder. eauto. *)
(*             + guardH o. des; congr. *)
(*           - inv ITV. econs; ss. *)
(*         } *)
(*     + econs; eauto. erewrite Memory.split_o; eauto. *)
(*       repeat condtac; ss; eauto. *)
(*       * guardH o. des. subst. congr. *)
(*       * guardH o. guardH o0. des. subst. *)
(*         unguardH o. des; congr. *)
Admitted.

Lemma split_covered_half_same
      mem2 mem1 loc ts1 ts2 ts3 msg3
      l t
      (SPLIT: Memory.split mem1 loc ts1 ts2 ts3 msg3 msg3 mem2):
  covered_half l t mem2 <-> covered_half l t mem1.
Proof.
  econs; i.
  - exploit Memory.split_get0; eauto. i. des.
    inv H. revert GET3. erewrite Memory.split_o; eauto. repeat condtac; ss.
    + des. subst. i. inv GET3. econs; eauto.
      eapply Interval.le_mem; eauto. econs; [refl|].
      inv SPLIT. inv SPLIT0. left. auto.
    + guardH o. des. subst. i. inv GET3. econs; eauto.
      eapply Interval.le_mem; eauto. econs; [|refl].
      inv SPLIT. inv SPLIT0. left. auto.
    + i. econs; eauto.
  - exploit Memory.split_get0; eauto. i. des.
    inv H.
    destruct (loc_ts_eq_dec (l, to) (loc, ts3)); ss.
    + des. subst. rewrite GET0 in GET3. inv GET3.
      destruct (Time.le_lt_dec t ts2).
      * econs.
        { instantiate (1 := from). instantiate (1 := ts2).
          erewrite Memory.split_o; eauto. condtac; ss.
          des; congr.
        }
        { inv ITV. econs; ss. }
      * econs.
        { instantiate (1 := ts2). instantiate (1 := ts3).
          erewrite Memory.split_o; eauto. repeat condtac; ss.
          - des. subst. inv SPLIT. inv SPLIT0.
            exfalso. eapply Time.lt_strorder. eauto.
          - guardH o. des; congr.
        }
        { inv ITV. econs; ss. }
    + econs; eauto. erewrite Memory.split_o; eauto.
      repeat condtac; ss; eauto.
      * guardH o. des. subst. congr.
      * guardH o. guardH o0. des. subst.
        unguardH o. des; congr.
Qed.

Lemma lower_covered_half
      mem2 mem1 loc from to msg1 msg2
      l t
      (LOWER: Memory.lower mem1 loc from to msg1 msg2 mem2):
  covered_half l t mem2 <->
  ((l <> loc \/ ~ Interval.mem (from, to) t) /\ covered_half l t mem1) \/
  (l = loc /\ Interval.mem (from, to) t /\ msg2 = Message.half).
Proof.
  (* econs; i. *)
  (* - exploit Memory.lower_get0; eauto. i. des. *)
  (*   inv H. *)
  (*   destruct (loc_ts_eq_dec (l, to0) (loc, to)); ss. *)
  (*   + des. subst. rewrite GET0 in GET1. inv GET1. eauto. *)
  (*   + left. split. *)
  (*     * des; eauto. destruct (Loc.eq_dec l loc); eauto. *)
  (*       subst. inv LOWER. unfold Memory.get in *. ss. *)
  (*       rewrite LocFun.add_spec in GET0, GET1. *)
  (*       exploit Cell.lower_wf; eauto. *)
  (*   inv H. revert GET. erewrite Memory.lower_o; eauto. condtac; ss. *)
  (*   + des. subst. i. inv GET. right. left. *)
  (*     hexploit Memory.lower_get0; eauto. i. des. inv MSG_LE. *)
  (*     esplits; eauto. econs; eauto. *)
  (*   + i. econs; eauto. *)
  (* - exploit Memory.lower_get0; eauto. i. des. *)
  (*   inv H. *)
  (*   destruct (loc_ts_eq_dec (l, to0) (loc, to)); ss. *)
  (*   + des. subst. econs; cycle 1; eauto. *)
  (*     erewrite Memory.lower_o; eauto. condtac; [|by des]. *)
  (*     rewrite GET in GET1. inv GET1. eauto. *)
  (*   + econs; eauto. *)
  (*     erewrite Memory.lower_o; eauto. rewrite GET1. condtac; ss. *)
  (*     des; congr. *)
Admitted.

Lemma sim_memory_split_exists_aux
      ts1 ts2 ts3
      loc from_src msg_src mem_src
      msg_tgt mem1_tgt
      (SIM: sim_memory mem_src mem1_tgt)
      (GET_SRC: Memory.get loc ts2 mem_src = Some (from_src, msg_src))
      (GET_TGT: Memory.get loc ts3 mem1_tgt = Some (ts1, msg_tgt))
      (CLOSED_SRC: Memory.closed mem_src)
      (CLOSED_TGT: Memory.closed mem1_tgt)
      (TS12: Time.lt ts1 ts2)
      (TS23: Time.lt ts2 ts3):
  exists msg_tgt' mem2_tgt,
    <<SPLIT: Memory.split mem1_tgt loc ts1 ts2 ts3 msg_tgt' msg_tgt mem2_tgt>> /\
    <<MSG_WF: Message.wf msg_tgt'>> /\
    <<MSG_TS: Memory.message_ts msg_tgt' loc ts2>> /\
    <<MSG_CLOSED: Memory.closed_message_view msg_tgt' mem2_tgt>> /\
    <<MSG_SIM: sim_message msg_src msg_tgt'>>.
Proof.
  destruct msg_src.
  - exploit (@Memory.max_full_released_exists mem1_tgt loc ts2); try apply CLOSED_TGT. i. des.
    exploit Memory.max_full_released_wf; eauto. i.
    exploit (@Memory.split_exists mem1_tgt loc ts1 ts2 ts3 (Message.mk val (Some released0)) msg_tgt); eauto.
    { econs. eauto. }
    i. des.
    exploit Memory.max_full_released_closed_split; eauto. i. des.
    esplits; eauto.
    + econs; eauto.
    + econs; eauto.
      exploit (@Memory.max_full_released_exists mem_src loc ts2); try apply CLOSED_SRC. i. des.
      exploit sim_memory_max_full_released; try exact SIM; eauto. i. subst.
      inv CLOSED_SRC. exploit CLOSED0; eauto. i. des.
      inv x3. ss. inv MSG_CLOSED. inv CLOSED1; ss.
      inv CLOSED2.
      hexploit Memory.max_full_timemap_spec; try exact PLN; eauto. i.
      hexploit Memory.max_full_timemap_spec; try exact RLX; eauto. i.
      econs. econs; ss.
      * ii. unfold TimeMap.add. condtac; eauto.
        subst. inv MSG_TS. etrans; [|exact TS].
        inv MSG_WF. inv WF. apply WF0.
      * ii. unfold TimeMap.add. condtac; eauto.
        subst. inv MSG_TS. etrans; [|exact TS]. ss. refl.
  - exploit (@Memory.split_exists mem1_tgt loc ts1 ts2 ts3 Message.half msg_tgt); eauto; try by econs.
    i. des. esplits; eauto; econs.
Qed.

Lemma sim_memory_split_exists
      loc from_src to_src msg_src mem_src
      mem1_tgt
      (CLOSED_SRC: Memory.closed mem_src)
      (CLOSED_TGT: Memory.closed mem1_tgt)
      (SIM: sim_memory mem_src mem1_tgt)
      (GET_SRC: Memory.get loc to_src mem_src = Some (from_src, msg_src)):
  exists msg_tgt from_tgt to_tgt,
    <<GET_TGT: Memory.get loc to_tgt mem1_tgt = Some (from_tgt, msg_tgt)>> /\
    (<<FROM: from_src = from_tgt>> /\
     <<TO: to_src = to_tgt>>) \/
    (<<FROM: from_src = from_tgt>> /\
     <<TO: Time.lt to_src to_tgt>> /\
     <<SPLIT1: exists msg_tgt' mem2_tgt,
         Memory.split mem1_tgt loc from_tgt to_src to_tgt msg_tgt' msg_tgt mem2_tgt /\
         Memory.message_ts msg_tgt' loc to_src /\
         Memory.closed_message_view msg_tgt' mem2_tgt /\
         sim_memory mem_src mem2_tgt>>)\/
    (<<FROM: Time.lt from_tgt from_src>> /\
     <<TO: to_src = to_tgt>> /\
     <<SPLIT: exists msg_tgt' mem2_tgt,
         Memory.split mem1_tgt loc from_tgt from_src to_tgt msg_tgt' msg_tgt mem2_tgt /\
         Memory.message_ts msg_tgt' loc from_src /\
         Memory.closed_message_view msg_tgt' mem2_tgt /\
         sim_memory mem_src mem2_tgt>>) \/
    (<<FROM: Time.lt from_tgt from_src>> /\
     <<TO: Time.lt to_src to_tgt>> /\
     <<SPLIT: exists msg_tgt' msg_tgt'' mem2_tgt mem3_tgt,
         Memory.split mem1_tgt loc from_tgt from_src to_tgt msg_tgt' msg_tgt mem2_tgt /\
         Memory.message_ts msg_tgt' loc from_src /\
         Memory.closed_message_view msg_tgt' mem2_tgt /\
         Memory.split mem2_tgt loc from_src to_src to_tgt msg_tgt'' msg_tgt mem3_tgt /\
         Memory.message_ts msg_tgt'' loc to_src /\
         Memory.closed_message_view msg_tgt'' mem3_tgt /\
         sim_memory mem_src mem3_tgt>>).
Proof.
  dup CLOSED_SRC. inv CLOSED_SRC0.
  dup CLOSED_TGT. inv CLOSED_TGT0.
  exploit Memory.get_ts; try exact GET_SRC. i. des.
  { subst. specialize (INHABITED0 loc).
    esplits. left. esplits; eauto. }
  exploit sim_memory_get_inv; try exact GET_SRC; eauto. i. des.
  exploit Memory.get_ts; try exact GET_TGT. i. des.
  { subst. inv TO; inv H. inv x0. }
  exists msg_tgt. inv FROM; inv TO.
  - esplits. repeat right. splits; eauto.
    admit.
  - inv H0. esplits. right. right. left. splits; eauto.
    admit.
  - inv H. esplits. right. left. splits; eauto.
    (* prove that proper split exists *)
    exploit Memory.split_exists; try exact GET_TGT.
    { apply x0. }
    { auto. }
    { eapply CLOSED0. eauto. }
    i. des. esplits; eauto. inv SIM. econs.
    + i. rewrite (@split_covered mem2); eauto.
    + i. rewrite (@split_covered_half_same mem2); eauto.
    + i. revert GET. erewrite Memory.split_o; eauto. condtac; ss.
      * des. subst. i. inv GET.
  - inv H. inv H0. esplits. left. splits; eauto.
Admitted.

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
  inv SIM. econs.
  - i. rewrite add_covered; [|eauto]. rewrite (@add_covered mem2_tgt); [|eauto].
    econs; i; des; (try by right).
    + left. eapply COVER. eauto.
    + left. eapply COVER. eauto.
  - i. rewrite add_covered_half; [|eauto]. rewrite (@add_covered_half mem2_tgt); [|eauto].
    econs; i; des; subst.
    + left. apply COVER_HALF. auto.
    + right. inv SIM_MSG. splits; eauto.
    + left. apply COVER_HALF. auto.
    + right. inv SIM_MSG. splits; eauto.
  - i. revert GET. erewrite Memory.add_o; eauto. condtac; ss.
    + des. subst. i. inv GET. esplits; eauto.
      erewrite Memory.add_o; eauto. condtac; ss.
    + erewrite (@Memory.add_o mem2_src); eauto. condtac; ss. eauto.
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
  inv SIM. econs.
  - i. rewrite split_covered; [|eauto]. rewrite (@split_covered mem2_tgt); [|eauto].
    apply COVER.
  - i. rewrite split_covered_half; [|eauto]. rewrite (@split_covered_half mem2_tgt); [|eauto].
    econs; i; des; subst;
      try by (left; split; auto; apply COVER_HALF; auto).
    + right. inv SIM_MSG. split; auto.
    + right. inv SIM_MSG. split; auto.
  - i. revert GET. erewrite Memory.split_o; eauto. repeat condtac; ss.
    + des. subst. i. inv GET. esplits; eauto.
      erewrite Memory.split_o; eauto. condtac; ss.
    + erewrite (@Memory.split_o mem2_src); eauto. repeat condtac; ss.
      i. inv GET. guardH o. guardH o0. des. subst.
      exploit Memory.split_get0; try exact SRC; eauto. i. des.
      exploit Memory.split_get0; try exact TGT; eauto. i. des.
      exploit MSG; eauto. i. des. rewrite GET0 in GET7. inv GET7.
      esplits; eauto.
    + erewrite (@Memory.split_o mem2_src); eauto. repeat condtac; ss. eauto.
Qed.

Lemma sim_memory_lower
      mem1_src mem1_tgt
      mem2_src mem2_tgt
      loc to from_src msg1_src msg2_src from_tgt msg1_tgt msg2_tgt
      (SIM_MSG: sim_message msg2_src msg2_tgt)
      (SRC: Memory.lower mem1_src loc from_src to msg1_src msg2_src mem2_src)
      (TGT: Memory.lower mem1_tgt loc from_tgt to msg1_tgt msg2_tgt mem2_tgt)
      (SIM: sim_memory mem1_src mem1_tgt):
  sim_memory mem2_src mem2_tgt.
Proof.
  dup SIM. inv SIM0. econs.
  - i. rewrite lower_covered; [|eauto]. rewrite (@lower_covered mem2_tgt); [|eauto].
    apply COVER.
  - i. rewrite lower_covered_half; [|eauto]. rewrite (@lower_covered_half mem2_tgt); [|eauto].
    exploit Memory.lower_get0; try exact SRC. i. des.
    exploit Memory.lower_get0; try exact TGT. i. des.
    exploit sim_memory_get_from; try exact SIM; eauto. i. des.
    econs; i; des; subst;
      try by (left; split; auto; apply COVER_HALF; auto).
    + admit.
    + admit.
    +
  - i. revert GET. erewrite Memory.lower_o; eauto. condtac; ss.
    + des. subst. i. inv GET. esplits; eauto.
      erewrite Memory.lower_o; eauto. condtac; ss.
    + erewrite (@Memory.lower_o mem2_src); eauto. condtac; ss. eauto.
Qed.

Lemma sim_memory_lower_none
      mem1_src mem2_src mem_tgt
      loc from to msg1 msg2
      (SRC: Memory.lower mem1_src loc from to msg1 msg2 mem2_src)
      (TGT: Memory.get loc to mem_tgt = None)
      (SIM: sim_memory mem1_src mem_tgt):
  sim_memory mem2_src mem_tgt.
Proof.
  inv SIM. econs.
  - i. rewrite lower_covered; [|eauto]. eauto.
  - i. erewrite Memory.lower_o; eauto.
    condtac; eauto; ss. des. subst. congr.
Qed.

Lemma sim_memory_promise
      loc from to kind
      promises1_src mem1_src msg_src promises2_src mem2_src
      promises1_tgt mem1_tgt msg_tgt promises2_tgt mem2_tgt
      (SIM_MSG: sim_message msg_src msg_tgt)
      (PROMISE_SRC: Memory.promise promises1_src mem1_src loc from to msg_src promises2_src mem2_src kind)
      (PROMISE_TGT: Memory.promise promises1_tgt mem1_tgt loc from to msg_tgt promises2_tgt mem2_tgt kind)
      (SIM: sim_memory mem1_src mem1_tgt):
  sim_memory mem2_src mem2_tgt.
Proof.
  inv PROMISE_SRC; inv PROMISE_TGT.
  - eapply sim_memory_add; eauto.
  - eapply sim_memory_split; eauto.
  - eapply sim_memory_lower; eauto.
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

Lemma sim_memory_closed_message_view
      mem_src mem_tgt
      msg
      (SIM: sim_memory mem_src mem_tgt)
      (TGT: Memory.closed_message_view msg mem_tgt):
  Memory.closed_message_view msg mem_src.
Proof.
  inv TGT; ss. econs. eapply sim_memory_closed_opt_view; eauto.
Qed.

Lemma lower_sim_memory
      mem1 loc from to val released1 msg2 mem2
      (LOWER: Memory.lower mem1 loc from to (Message.mk val released1) msg2 mem2):
  sim_memory mem2 mem1.
Proof.
  econs.
  - i. eapply lower_covered. eauto.
  - i. erewrite Memory.lower_o; eauto. condtac; ss.
    + des. subst.
      exploit Memory.lower_get0; eauto. i. des.
      rewrite GET0 in GET. inv GET. inv MSG_LE.
      esplits; eauto.
    + esplits; eauto. refl.
Qed.

Lemma promise_lower_sim_memory
      promises1 mem1 loc from to val released1 msg2 promises2 mem2
      (PROMISE: Memory.promise promises1 mem1 loc from to msg2 promises2 mem2 (Memory.op_kind_lower (Message.mk val released1))):
  sim_memory mem2 mem1.
Proof.
  inv PROMISE. eapply lower_sim_memory. eauto.
Qed.

Lemma split_sim_memory
      mem0 loc ts1 ts2 ts3 msg2 msg3 mem1
      (SPLIT: Memory.split mem0 loc ts1 ts2 ts3 msg2 msg3 mem1):
  sim_memory mem1 mem0.
Proof.
  econs.
  - i. eapply split_covered. eauto.
  - i. exploit Memory.split_get0; eauto. i. des.
    erewrite Memory.split_o; eauto. repeat condtac; ss.
    + des. subst. congr.
    + guardH o. des. subst. rewrite GET1 in GET. inv GET.
      esplits; eauto. refl.
    + esplits; eauto. refl.
Qed.
