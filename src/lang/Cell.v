Require Import Omega.
Require Import RelationClasses.

Require Import sflib.
From Paco Require Import paco.

Require Import Axioms.
Require Import Basic.
Require Import DataStructure.
Require Import DenseOrder.
Require Import Event.
Require Import Time.
Require Import View.

Set Implicit Arguments.


Module Message.
  Inductive t :=
  | full (val: Const.t) (released: option View.t)
  | half
  .
  Hint Constructors t.

  Definition elt: t := full 0 None.

  Inductive le : t -> t -> Prop :=
  | le_view
      val released released'
      (RELEASED: View.opt_le released released'):
      le (full val released) (full val released')
  | le_half
      msg:
      le msg half
  .
  Hint Constructors le.

  Program Instance le_PreOrder: PreOrder le.
  Next Obligation.
    ii. destruct x; econs. refl.
  Qed.
  Next Obligation.
    ii. inv H; inv H0; econs. etrans; eauto.
  Qed.

  Lemma le_antisym a b
        (AB: le a b)
        (BA: le b a):
    a = b.
  Proof.
    inv AB; inv BA; ss.
    f_equal. apply View.opt_antisym; auto.
  Qed.

  Inductive wf: t -> Prop :=
  | wf_view
      val released
      (WF: View.opt_wf released):
      wf (full val released)
  | wf_half:
      wf half
  .

  Definition elt_wf: wf elt.
  Proof. econs; ss. Qed.

  Definition is_released_none (msg: t): bool :=
    match msg with
    | full _ released => negb released
    | half => false
    end.
End Message.

Module Cell.
  Module Raw.
    Definition t := DOMap.t (DenseOrder.t * Message.t).

    Inductive wf (cell:t): Prop :=
    | wf_intro
        (VOLUME: forall from to msg
                   (GET: DOMap.find to cell = Some (from, msg)),
            (from, to) = (Time.bot, Time.bot) \/ Time.lt from to)
        (WF: forall from to msg
               (GET: DOMap.find to cell = Some (from, msg)),
            Message.wf msg)
        (DISJOINT: forall to1 to2 from1 from2 msg1 msg2
                     (GET1: DOMap.find to1 cell = Some (from1, msg1))
                     (GET2: DOMap.find to2 cell = Some (from2, msg2))
                     (NEQ: to1 <> to2),
            Interval.disjoint (from1, to1) (from2, to2))
    .
    Hint Constructors wf.

    Definition bot: t := DOMap.empty _.

    Lemma bot_wf: wf bot.
    Proof.
      econs; i.
      - rewrite DOMap.gempty in GET. inv GET.
      - rewrite DOMap.gempty in GET. inv GET.
      - rewrite DOMap.gempty in GET1. inv GET1.
    Qed.

    Definition singleton (from to:Time.t) (msg:Message.t): t :=
      DOMap.singleton to (from, msg).

    Lemma singleton_wf
          from to msg
          (LT: Time.lt from to)
          (WF: Message.wf msg):
      wf (singleton from to msg).
    Proof.
      unfold singleton. econs; s; i.
      - apply DOMap.singleton_find_inv in GET. des. inv GET0. auto.
      - apply DOMap.singleton_find_inv in GET. des. inv GET0. auto.
      - apply DOMap.singleton_find_inv in GET1. des. inv GET0.
        apply DOMap.singleton_find_inv in GET2. des. inv GET0.
        congr.
    Qed.

    Definition init: t :=
      DOMap.singleton Time.bot (Time.bot, Message.elt).

    Lemma init_wf: wf init.
    Proof.
      unfold init. econs; s; i.
      - apply DOMap.singleton_find_inv in GET. des. inv GET0. auto.
      - apply DOMap.singleton_find_inv in GET. des. inv GET0.
        apply Message.elt_wf.
      - apply DOMap.singleton_find_inv in GET1. des. inv GET0.
        apply DOMap.singleton_find_inv in GET2. des. inv GET0.
        congr.
    Qed.

    Lemma find_mem_ub
          from to msg cell
          (WF: wf cell)
          (FIND: DOMap.find to cell = Some (from, msg)):
      (from, to) = (Time.bot, Time.bot) \/
      Interval.mem (from, to) to.
    Proof.
      inv WF. exploit VOLUME; eauto. i. des; auto.
      right. econs; eauto. refl.
    Qed.

    Inductive add (cell1:t) (from to:Time.t) (msg:Message.t) (cell2:t): Prop :=
    | add_intro
        (DISJOINT: forall to2 from2 msg2
                          (GET2: DOMap.find to2 cell1 = Some (from2, msg2)),
            Interval.disjoint (from, to) (from2, to2))
        (TO: Time.lt from to)
        (MSG_WF: Message.wf msg)
        (CELL2: cell2 = DOMap.add to (from, msg) cell1):
        add cell1 from to msg cell2.
    Hint Constructors add.

    Lemma add_o
          cell2 cell1 from to msg
          t
          (ADD: add cell1 from to msg cell2):
      DOMap.find t cell2 =
      if Time.eq_dec t to
      then Some (from, msg)
      else DOMap.find t cell1.
    Proof.
      inv ADD. rewrite DOMap.gsspec.
      repeat condtac; auto; congr.
    Qed.

    Lemma add_wf
          cell1 from to msg cell2
          (ADD: add cell1 from to msg cell2)
          (CELL1: wf cell1):
      wf cell2.
    Proof.
      inv CELL1. econs; i.
      - revert GET. erewrite add_o; eauto. condtac; auto.
        + i. inv GET. inv ADD. auto.
        + i. eapply VOLUME; eauto.
      - revert GET. erewrite add_o; eauto. condtac; auto.
        + i. inv GET. inv ADD. auto.
        + i. eapply WF; eauto.
      - revert GET1 GET2.
        erewrite (add_o to1); eauto.
        erewrite (add_o to2); eauto.
        repeat condtac; s; i.
        + inv GET1. congr.
        + inv GET1. inv ADD. hexploit DISJOINT0; eauto.
        + inv GET2. inv ADD. symmetry. hexploit DISJOINT0; eauto.
        + eapply DISJOINT; eauto.
    Qed.

    Inductive split (cell1:t) (ts1 ts2 ts3:Time.t) (msg2 msg3:Message.t) (cell2:t): Prop :=
    | split_intro
        (GET2: DOMap.find ts3 cell1 = Some (ts1, msg3))
        (TS12: Time.lt ts1 ts2)
        (TS23: Time.lt ts2 ts3)
        (MSG_WF: Message.wf msg2)
        (CELL2: cell2 = DOMap.add ts2 (ts1, msg2)
                                  (DOMap.add ts3 (ts2, msg3) cell1))
    .
    Hint Constructors split.

    Lemma split_o
          cell2 cell1 ts1 ts2 ts3 msg2 msg3
          t
          (SPLIT: split cell1 ts1 ts2 ts3 msg2 msg3 cell2):
      DOMap.find t cell2 =
      if Time.eq_dec t ts2
      then Some (ts1, msg2)
      else if Time.eq_dec t ts3
           then Some (ts2, msg3)
           else DOMap.find t cell1.
    Proof.
      inv SPLIT. rewrite ? DOMap.gsspec.
      repeat condtac; repeat subst; try congr.
    Qed.

    Lemma split_wf
          cell2 cell1 ts1 ts2 ts3 msg2 msg3
          (SPLIT: split cell1 ts1 ts2 ts3 msg2 msg3 cell2)
          (CELL1: wf cell1):
      wf cell2.
    Proof.
      inv CELL1. econs; i.
      - revert GET. erewrite split_o; eauto. repeat condtac; auto.
        + i. inv GET. inv SPLIT. auto.
        + i. inv GET. inv SPLIT. auto.
        + i. eapply VOLUME; eauto.
      - revert GET. erewrite split_o; eauto. repeat condtac; auto.
        + i. inv GET. inv SPLIT. eauto.
        + i. inv GET. inv SPLIT. eauto.
        + i. eapply WF; eauto.
      - revert GET1 GET2.
        erewrite (split_o to1); eauto.
        erewrite (split_o to2); eauto.
        repeat condtac; repeat subst; try congr; i.
        + inv GET1. inv GET2.
          eapply Interval.disjoint_imm.
        + inv GET1.
          inv SPLIT. hexploit DISJOINT; try exact n0; eauto. i.
          symmetry in H. eapply Interval.le_disjoint; eauto.
          econs; [refl|by left].
        + inv GET1. inv GET2.
          symmetry. eapply Interval.disjoint_imm.
        + inv GET1.
          inv SPLIT. hexploit DISJOINT; try exact NEQ; eauto. i.
          eapply Interval.le_disjoint; eauto.
          econs; [by left|refl].
        + inv GET2.
          inv SPLIT. hexploit DISJOINT; try exact n0; eauto. i.
          symmetry in H. symmetry. eapply Interval.le_disjoint; eauto.
          econs; [refl|by left].
        + inv GET2.
          inv SPLIT. hexploit DISJOINT; try exact n0; eauto. i.
          symmetry in H. symmetry. eapply Interval.le_disjoint; eauto.
          econs; [by left|refl].
        + eapply DISJOINT; eauto.
    Qed.

    Inductive lower (cell1:t) (from to:Time.t) (msg1 msg2: Message.t) (cell2:t): Prop :=
    | update_intro
        (GET2: DOMap.find to cell1 = Some (from, msg1))
        (TS: Time.lt from to)
        (MSG_WF: Message.wf msg2)
        (MSG_LE: Message.le msg2 msg1)
        (CELL2: cell2 = DOMap.add to (from, msg2) cell1)
    .
    Hint Constructors lower.

    Lemma lower_o
          cell2 cell1 from to msg1 msg2
          t
          (LOWER: lower cell1 from to msg1 msg2 cell2):
      DOMap.find t cell2 =
      if Time.eq_dec t to
      then Some (from, msg2)
      else DOMap.find t cell1.
    Proof.
      inv LOWER. rewrite DOMap.gsspec.
      repeat condtac; auto; congr.
    Qed.

    Lemma lower_wf
          cell2 cell1 from to msg1 msg2
          (LOWER: lower cell1 from to msg1 msg2 cell2)
          (CELL1: wf cell1)
          (MSG2: Message.wf msg2):
      wf cell2.
    Proof.
      inv CELL1. econs; i.
      - revert GET. erewrite lower_o; eauto. condtac; auto.
        + i. inv GET. inv LOWER. eapply VOLUME. eauto.
        + i. eapply VOLUME; eauto.
      - revert GET. erewrite lower_o; eauto. condtac.
        + i. inv GET. inv LOWER. auto.
        + i. eapply WF. eauto.
      - revert GET1 GET2.
        erewrite (lower_o to1); eauto.
        erewrite (lower_o to2); eauto.
        repeat condtac; repeat subst; try congr; i.
        + inv GET1. inv LOWER. eapply DISJOINT; eauto.
        + inv GET2. inv LOWER. eapply DISJOINT; eauto.
        + eapply DISJOINT; eauto.
    Qed.

    Inductive remove (cell1:t) (from to:Time.t) (msg:Message.t) (cell2:t): Prop :=
    | remove_intro
        (GET: DOMap.find to cell1 = Some (from, msg))
        (CELL2: cell2 = DOMap.remove to cell1)
    .
    Hint Constructors remove.

    Lemma remove_o
          cell2 cell1 from to msg
          t
          (REMOVE: remove cell1 from to msg cell2):
      DOMap.find t cell2 =
      if Time.eq_dec t to
      then None
      else DOMap.find t cell1.
    Proof.
      inv REMOVE. rewrite DOMap.grspec.
      repeat condtac; auto; congr.
    Qed.

    Lemma remove_wf
          cell1 from to msg cell2
          (REMOVE: remove cell1 from to msg cell2)
          (CELL1: wf cell1):
      wf cell2.
    Proof.
      inv CELL1. econs; i.
      - revert GET. erewrite remove_o; eauto. condtac; try congr.
        i. eapply VOLUME; eauto.
      - revert GET. erewrite remove_o; eauto. condtac; ss. apply WF.
      - revert GET1 GET2.
        erewrite (remove_o to1); eauto.
        erewrite (remove_o to2); eauto.
        repeat condtac; repeat subst; try congr; i.
        eapply DISJOINT; eauto.
    Qed.
  End Raw.

  Structure t := mk {
    raw :> Raw.t;
    WF: Raw.wf raw;
  }.

  Definition get (ts:Time.t) (cell:t): option (Time.t * Message.t) := DOMap.find ts cell.(raw).

  Lemma ext
        (lhs rhs:t)
        (EXT: forall ts, get ts lhs = get ts rhs):
    lhs = rhs.
  Proof.
    destruct lhs, rhs.
    assert (raw0 = raw1).
    { apply DOMap.eq_leibniz. ii. apply EXT. }
    subst raw1. f_equal. apply proof_irrelevance.
  Qed.

  Lemma get_ts
        to cell from msg
        (GET: get to cell = Some (from, msg)):
    (from = Time.bot /\ to = Time.bot) \/ Time.lt from to.
  Proof.
    destruct cell. unfold get in *. ss.
    inv WF0. exploit VOLUME; eauto. i. des.
    - inv x. auto.
    - generalize (Time.le_lteq from to). i. des. auto.
  Qed.

  Definition le (lhs rhs:t): Prop :=
    forall to from msg
      (LHS: get to lhs = Some (from, msg)),
      get to rhs = Some (from, msg).

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation. ii. auto. Qed.
  Next Obligation. ii. eapply H0; eauto. Qed.

  Definition bot: t := mk Raw.bot_wf.

  Lemma bot_get ts: get ts bot = None.
  Proof. unfold get, bot, Raw.bot. s. apply DOMap.gempty. Qed.

  Lemma bot_le cell: le bot cell.
  Proof. ii. rewrite bot_get in LHS. congr. Qed.

  Definition singleton
             (from to:Time.t) (msg:Message.t)
             (LT: Time.lt from to)
             (WF: Message.wf msg): t :=
    mk (Raw.singleton_wf LT WF).

  Lemma singleton_get
        from to msg t
        (LT: Time.lt from to)
        (WF: Message.wf msg):
    get t (singleton LT WF) =
    if Loc.eq_dec t to
    then Some (from, msg)
    else None.
  Proof.
    unfold get, singleton, Raw.singleton. ss. condtac.
    - subst. rewrite DOMap.singleton_eq. auto.
    - rewrite DOMap.singleton_neq; auto.
  Qed.

  Definition init: t := mk Raw.init_wf.

  Lemma init_get t:
    get t init =
    if Loc.eq_dec t Time.bot
    then Some (Time.bot, Message.elt)
    else None.
  Proof.
    unfold get, init, Raw.init. ss. condtac.
    - subst. rewrite DOMap.singleton_eq. auto.
    - rewrite DOMap.singleton_neq; auto.
  Qed.

  Definition add (cell1:t) (from to:Time.t) (msg: Message.t) (cell2:t): Prop :=
    Raw.add cell1 from to msg cell2.

  Definition split (cell1:t) (ts1 ts2 ts3:Time.t) (msg2 msg3: Message.t) (cell2:t): Prop :=
    Raw.split cell1 ts1 ts2 ts3 msg2 msg3 cell2.

  Definition lower (cell1:t) (from to:Time.t) (msg1 msg2: Message.t) (cell2:t): Prop :=
    Raw.lower cell1 from to msg1 msg2 cell2.

  Definition remove (cell1:t) (from to:Time.t) (msg: Message.t) (cell2:t): Prop :=
    Raw.remove cell1 from to msg cell2.

  Lemma add_o
        cell2 cell1 from to msg
        t
        (ADD: add cell1 from to msg cell2):
    get t cell2 =
    if Time.eq_dec t to
    then Some (from, msg)
    else get t cell1.
  Proof. apply Raw.add_o. auto. Qed.

  Lemma split_o
        cell2 cell1 ts1 ts2 ts3 msg2 msg3
        t
        (SPLIT: split cell1 ts1 ts2 ts3 msg2 msg3 cell2):
    get t cell2 =
    if Time.eq_dec t ts2
    then Some (ts1, msg2)
    else if Time.eq_dec t ts3
         then Some (ts2, msg3)
         else get t cell1.
  Proof. apply Raw.split_o. auto. Qed.

  Lemma lower_o
        cell2 cell1 from to msg1 msg2
        t
        (LOWER: lower cell1 from to msg1 msg2 cell2):
    get t cell2 =
    if Time.eq_dec t to
    then Some (from, msg2)
    else get t cell1.
  Proof. eapply Raw.lower_o. eauto. Qed.

  Lemma remove_o
        cell2 cell1 from to msg
        t
        (REMOVE: remove cell1 from to msg cell2):
    get t cell2 =
    if Time.eq_dec t to
    then None
    else get t cell1.
  Proof. eapply Raw.remove_o. eauto. Qed.

  Definition max_ts (cell:t): Time.t :=
    DOMap.max_key cell.(raw).

  Lemma max_ts_spec
        ts from msg cell
        (GET: get ts cell = Some (from, msg)):
    <<GET: exists from msg, get (max_ts cell) cell = Some (from, msg)>> /\
    <<MAX: Time.le ts (max_ts cell)>>.
  Proof.
    unfold get in GET.
    generalize (DOMap.max_key_spec cell.(Cell.raw)). i. des. splits; eauto.
    - destruct (DOMap.find
                  (DOMap.max_key (Cell.raw cell))
                  (Cell.raw cell)) as [[]|]eqn:X.
      + esplits; eauto.
      + exfalso. eapply FIND; eauto. rewrite GET. congr.
    - apply MAX. rewrite GET. auto. congr.
  Qed.

  Lemma add_exists
        cell1 from to msg
        (DISJOINT: forall to2 from2 msg2
                     (GET2: get to2 cell1 = Some (from2, msg2)),
            Interval.disjoint (from, to) (from2, to2))
        (TO1: Time.lt from to)
        (WF: Message.wf msg):
    exists cell2, add cell1 from to msg cell2.
  Proof.
    destruct cell1. eexists (mk _). econs; s; eauto.
    Grab Existential Variables.
    eapply Raw.add_wf; eauto.
  Qed.

  Lemma add_exists_max_ts
        cell1 to msg
        (TO: Time.lt (max_ts cell1) to)
        (WF: Message.wf msg):
    exists cell2, add cell1 (max_ts cell1) to msg cell2.
  Proof.
    apply add_exists; auto. i.
    exploit max_ts_spec; eauto. i. des.
    ii. inv LHS. inv RHS. ss.
    rewrite MAX in TO1. eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt; eauto.
  Qed.

  Lemma add_exists_le
        promises1 cell1 from to msg cell2
        (LE: le promises1 cell1)
        (ADD: add cell1 from to msg cell2):
    exists promises2, add promises1 from to msg promises2.
  Proof.
    inv ADD. apply add_exists; auto. i.
    eapply DISJOINT. eauto.
  Qed.

  Lemma split_exists
        cell1 ts1 ts2 ts3 msg2 msg3
        (GET2: get ts3 cell1 = Some (ts1, msg3))
        (TS12: Time.lt ts1 ts2)
        (TS23: Time.lt ts2 ts3)
        (REL_WF: Message.wf msg2):
    exists cell2, split cell1 ts1 ts2 ts3 msg2 msg3 cell2.
  Proof.
    destruct cell1. eexists (mk _). econs; s; eauto.
  Grab Existential Variables.
    eapply Raw.split_wf; eauto.
  Qed.

  Lemma split_exists_le
        promises1 cell1 ts1 ts2 ts3 msg2 msg3 promises2
        (LE: le promises1 cell1)
        (SPLIT: split promises1 ts1 ts2 ts3 msg2 msg3 promises2):
    exists cell2, split cell1 ts1 ts2 ts3 msg2 msg3 cell2.
  Proof.
    inv SPLIT. eapply split_exists; eauto.
  Qed.

  Lemma lower_exists
        cell1 from to msg1 msg2
        (GET2: get to cell1 = Some (from, msg1))
        (TS: Time.lt from to)
        (REL_WF: Message.wf msg2)
        (REL_LE: Message.le msg2 msg1):
    exists cell2, lower cell1 from to msg1 msg2 cell2.
  Proof.
    destruct cell1. eexists (mk _). unfold lower. econs; eauto. ss.
  Grab Existential Variables.
    eapply Raw.lower_wf; eauto.
  Qed.

  Lemma lower_exists_le
        promises1 cell1 from to msg1 msg2 promises2
        (LE: le promises1 cell1)
        (LOWER: lower promises1 from to msg1 msg2 promises2):
    exists cell2, lower cell1 from to msg1 msg2 cell2.
  Proof.
    inv LOWER. apply lower_exists; auto.
  Qed.

  (* Lemmas on add, split, lower & remove *)

  Lemma add_get0
        cell1 from1 to1 msg1 cell2
        (ADD: add cell1 from1 to1 msg1 cell2):
    <<GET: get to1 cell1 = None>> /\
    <<GET: get to1 cell2 = Some (from1, msg1)>>.
  Proof.
    inv ADD. unfold get. splits.
    - destruct (DOMap.find to1 (raw cell1)) as [[]|] eqn:X; auto.
      exfalso. exploit DISJOINT; eauto.
      + apply Interval.mem_ub. auto.
      + apply Interval.mem_ub.
        destruct cell1.(Cell.WF). exploit VOLUME; eauto. i. des; ss.
        inv x. inv TO.
    - rewrite CELL2, DOMap.gsspec. condtac; ss.
  Qed.

  Lemma split_get0
        cell1 ts1 ts2 ts3 msg2 msg3 cell2
        (SPLIT: split cell1 ts1 ts2 ts3 msg2 msg3 cell2):
    <<GET: get ts2 cell1 = None>> /\
    <<GET: get ts3 cell1 = Some (ts1, msg3)>> /\
    <<GET: get ts2 cell2 = Some (ts1, msg2)>> /\
    <<GET: get ts3 cell2 = Some (ts2, msg3)>>.
  Proof.
    inv SPLIT. splits; auto.
    - destruct (get ts2 cell1) as [[]|] eqn:X; auto.
      destruct cell1.(WF). exfalso. eapply DISJOINT.
      + apply X.
      + apply GET2.
      + ii. subst. eapply Time.lt_strorder. eauto.
      + apply Interval.mem_ub. exploit VOLUME; eauto. i. des; auto.
        inv x. inv TS12.
      + econs; ss. left. auto.
    - unfold get. rewrite CELL2. rewrite ? DOMap.gsspec.
      repeat condtac; ss.
    - unfold get. rewrite CELL2. rewrite ? DOMap.gsspec.
      repeat condtac; ss.
      subst. timetac.
  Qed.

  Lemma lower_get0
        cell1 from to msg1 msg2 cell2
        (LOWER: lower cell1 from to msg1 msg2 cell2):
    <<GET: get to cell1 = Some (from, msg1)>> /\
    <<GET: get to cell2 = Some (from, msg2)>> /\
    <<MSG_LE: Message.le msg2 msg1>>.
  Proof.
    inv LOWER. splits; auto.
    unfold get. rewrite CELL2. rewrite DOMap.gsspec. condtac; ss.
  Qed.

  Lemma remove_get0
        cell1 from to msg cell2
        (REMOVE: remove cell1 from to msg cell2):
    <<GET: get to cell1 = Some (from, msg)>> /\
    <<GET: get to cell2 = None>>.
  Proof.
    inv REMOVE. splits; auto.
    unfold get. rewrite CELL2. rewrite DOMap.grspec. condtac; ss.
  Qed.

  Lemma add_inhabited
        cell1 cell2 from to msg
        (ADD: add cell1 from to msg cell2)
        (INHABITED: get Time.bot cell1 = Some (Time.bot, Message.elt)):
    <<INHABITED: get Time.bot cell2 = Some (Time.bot, Message.elt)>>.
  Proof.
    erewrite add_o; eauto. condtac; auto. subst.
    inv ADD. inv TO.
  Qed.

  Lemma split_inhabited
        cell1 ts1 ts2 ts3 msg2 msg3 cell2
        (SPLIT: split cell1 ts1 ts2 ts3 msg2 msg3 cell2)
        (INHABITED: get Time.bot cell1 = Some (Time.bot, Message.elt)):
    <<INHABITED: get Time.bot cell2 = Some (Time.bot, Message.elt)>>.
  Proof.
    erewrite split_o; eauto. repeat condtac; subst; ss.
    - inv SPLIT. inv TS12.
    - inv SPLIT. inv TS23.
  Qed.

  Lemma lower_inhabited
        cell1 from to msg1 msg2 cell2
        (LOWER: lower cell1 from to msg1 msg2 cell2)
        (INHABITED: get Time.bot cell1 = Some (Time.bot, Message.elt)):
    <<INHABITED: get Time.bot cell2 = Some (Time.bot, Message.elt)>>.
  Proof.
    erewrite lower_o; eauto. condtac; auto.
    subst. inv LOWER. inv TS.
  Qed.

  Lemma add_max_ts
        cell1 to msg cell2
        (ADD: add cell1 (max_ts cell1) to msg cell2)
        (INHABITED: get Time.bot cell1 = Some (Time.bot, Message.elt)):
    max_ts cell2 = to.
  Proof.
    hexploit add_inhabited; eauto. i. des.
    exploit max_ts_spec; eauto. i. des.
    revert GET. erewrite add_o; eauto. condtac; auto. i.
    apply TimeFacts.antisym.
    - left. eapply TimeFacts.le_lt_lt.
      + eapply max_ts_spec. eauto.
      + inv ADD. auto.
    - eapply max_ts_spec. erewrite add_o; eauto. condtac; ss.
  Qed.

  Lemma remove_singleton
        from to msg
        (LT:Time.lt from to)
        (WF: Message.wf msg):
    remove (singleton LT WF) from to msg bot.
  Proof.
    assert (Raw.bot = DOMap.remove to ((singleton LT WF).(raw))).
    { apply DOMap.eq_leibniz. ii.
      unfold Raw.bot. rewrite DOMap.gempty.
      rewrite DOMap.grspec. condtac; auto.
      unfold singleton, Raw.singleton, raw.
      rewrite DOMap.singleton_neq; auto.
    }
    unfold remove. s. rewrite H. econs; ss.
    unfold Raw.singleton. rewrite DOMap.singleton_eq. auto.
  Qed.

  Lemma remove_exists
        cell1 from to msg
        (GET: get to cell1 = Some (from, msg)):
    exists cell2, remove cell1 from to msg cell2.
  Proof.
    eexists (mk _). destruct cell1. ss.
    Grab Existential Variables.
    { eapply Raw.remove_wf.
      - econs; eauto.
      - apply WF.
    }
  Qed.

  Lemma get_opt_wf
        cell from to msg
        (GET: get to cell = Some (from, msg)):
    Message.wf msg.
  Proof.
    destruct cell. destruct WF0. eauto.
  Qed.

  Inductive max_full_ts (cell: t) (ts: Time.t): Prop :=
  | max_full_ts_intro
      (GET: exists from val released, get ts cell = Some (from, Message.full val released))
      (MAX: forall to from' val' released'
              (GET: get to cell = Some (from', Message.full val' released')),
          Time.le to ts)
  .

  Lemma max_full_ts_exists_aux
        A t a
        (l: list (Time.t * A))
        (f: A -> bool)
        (INHABITED1: f a = true)
        (INHABITED2: List.In (t, a) l):
    exists max_t max_a,
      f max_a = true /\
      List.In (max_t, max_a) l /\
      (forall t' a' (IN: List.In (t', a') l) (F: f a' = true), Time.le t' max_t).
  Proof.
    remember (length l) eqn:LEN.
    revert INHABITED1 INHABITED2 LEN. revert t a l.
    induction n; i.
    { destruct l; inv LEN. inv INHABITED2. }
    destruct l; inv LEN.
    destruct p as [t1 a1]. ss. des.
    - inv INHABITED2. destruct l.
      + esplits; eauto. i. des; inv IN. refl.
      + exploit (IHn t0 a ((t0, a)::l)); auto; try by econs.
        i. des. destruct p as [new_t new_a]. ss.
        destruct (f new_a) eqn:FNEW; cycle 1.
        { esplits; try exact x0.
          - des; eauto.
          - i. guardH x1. des.
            + inv IN. eapply x2; eauto.
            + inv IN. rewrite F in FNEW. inv FNEW.
            + eapply x2; eauto. }
        destruct (Time.le_lt_dec new_t max_t).
        { esplits; try exact x0.
          - des; eauto.
          - i. guardH x1. des.
            + inv IN. eapply x2; eauto.
            + inv IN. auto.
            + eapply x2; eauto. }
        exists new_t. exists new_a. splits; auto.
        i. guardH x1. des.
        * inv IN. exploit (x2 t' a'); eauto. i.
          etrans; eauto. econs. auto.
        * inv IN. refl.
        * etrans; [|econs; exact l0].
          eapply x2; eauto.
    - exploit (IHn t0 a l); eauto. i. des.
      destruct (f a1) eqn:FNEW; cycle 1.
      { esplits; try exact x0; eauto.
        i. des.
        - inv IN. rewrite FNEW in F. inv F.
        - eapply x2; eauto. }
      destruct (Time.le_lt_dec t1 max_t).
      { esplits; try exact x0; eauto.
        i. des.
        - inv IN. auto.
        - eapply x2; eauto. }
      exists t1. exists a1. esplits; eauto.
      i. des.
      + inv IN. refl.
      + etrans; [|econs; exact l0].
        eapply x2; eauto.
  Qed.

  Lemma max_full_ts_exists
        cell
        (INHABITED: get Time.bot cell = Some (Time.bot, Message.elt)):
    exists ts, max_full_ts cell ts.
  Proof.
    destruct cell. unfold get in *. ss.
    remember (DOMap.elements raw0) as l eqn:DOM.
    exploit (max_full_ts_exists_aux
               Time.bot (Time.bot, Message.elt) l
               (fun (a: Time.t * Message.t) => match a with
                                            | (_, Message.full _ _) => true
                                            | _ => false
                                            end)).
    { ss. }
    { subst. eapply DOMap.elements_correct. auto. }
    i. des. destruct max_a. destruct t1; ss.
    exists max_t. econs.
    - subst. esplits. unfold get. ss.
      eapply DOMap.elements_complete. eauto.
    - i. unfold get in GET. ss.
      apply DOMap.elements_correct in GET. subst.
      eapply x2; eauto.
  Qed.

  Lemma max_full_ts_inj
        cell ts1 ts2
        (MAX1: max_full_ts cell ts1)
        (MAX2: max_full_ts cell ts2):
    ts1 = ts2.
  Proof.
    inv MAX1. inv MAX2. des.
    apply MAX0 in GET. apply MAX in GET0.
    apply TimeFacts.antisym; auto.
  Qed.

  Lemma max_full_ts_spec
        ts from val released cell mts
        (MAX: max_full_ts cell mts)
        (GET: get ts cell = Some (from, Message.full val released)):
    <<GET: exists f v r, get mts cell = Some (f, Message.full v r)>> /\
    <<MAX: Time.le ts mts>>.
  Proof.
    inv MAX. des. esplits; eauto.
  Qed.
End Cell.
