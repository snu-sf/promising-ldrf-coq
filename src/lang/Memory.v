Require Import Omega.
Require Import RelationClasses.
Require Import Coq.Logic.ClassicalChoice.

Require Import sflib.

Require Import Axioms.
Require Import Basic.
Require Import DataStructure.
Require Import DenseOrder.
Require Import Event.
Require Import Time.
Require Import View.
Require Import Cell.

Set Implicit Arguments.


Module Memory.
  Definition t := Loc.t -> Cell.t.

  Definition get (loc:Loc.t) (ts:Time.t) (mem:t): option (Time.t * Message.t) :=
    Cell.get ts (mem loc).

  Lemma get_disjoint
        l f1 f2 t1 t2 msg1 msg2 m
        (GET1: get l t1 m = Some (f1, msg1))
        (GET2: get l t2 m = Some (f2, msg2)):
    (t1 = t2 /\ f1 = f2 /\ msg1 = msg2) \/
    Interval.disjoint (f1, t1) (f2, t2).
  Proof.
    destruct (Time.eq_dec t1 t2).
    { subst. rewrite GET1 in GET2. inv GET2. auto. }
    unfold get in *. unfold Cell.get in *.
    destruct (m l); ss. inv WF.
    hexploit DISJOINT; [exact GET1|exact GET2|..]; eauto.
  Qed.

  Lemma ext
        lhs rhs
        (EXT: forall loc ts, get loc ts lhs = get loc ts rhs):
    lhs = rhs.
  Proof.
    apply LocFun.ext. i.
    apply Cell.ext. i.
    apply EXT.
  Qed.

  Lemma get_ts
        loc to mem from msg
        (GET: get loc to mem = Some (from, msg)):
    (from = Time.bot /\ to = Time.bot) \/ Time.lt from to.
  Proof.
    unfold get in *.
    apply Cell.get_ts in GET. auto.
  Qed.

  Definition le (lhs rhs:t): Prop :=
    forall loc to from msg
      (LHS: get loc to lhs = Some (from, msg)),
      get loc to rhs = Some (from, msg).

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation. ii. auto. Qed.
  Next Obligation. ii. eapply H0; eauto. Qed.

  Inductive disjoint (lhs rhs:t): Prop :=
  | disjoint_intro
      (DISJOINT: forall loc to1 to2 from1 from2 msg1 msg2
                   (GET1: get loc to1 lhs = Some (from1, msg1))
                   (GET2: get loc to2 rhs = Some (from2, msg2)),
          Interval.disjoint (from1, to1) (from2, to2) /\
          (to1, to2) <> (Time.bot, Time.bot))
  .
  Hint Constructors disjoint.

  Global Program Instance disjoint_Symmetric: Symmetric disjoint.
  Next Obligation.
    inv H. econs. i. exploit DISJOINT; eauto. i. des. splits.
    - symmetry. auto.
    - ii. inv H. congr.
  Qed.

  Lemma disjoint_get
        lhs rhs
        loc froml fromr to msgl msgr
        (DISJOINT: disjoint lhs rhs)
        (LMSG: get loc to lhs = Some (froml, msgl))
        (RMSG: get loc to rhs = Some (fromr, msgr)):
    False.
  Proof.
    inv DISJOINT. exploit DISJOINT0; eauto. i. des.
    destruct (Time.eq_dec to Time.bot).
    - subst. congr.
    - eapply x.
      + apply Interval.mem_ub. destruct (lhs loc).(Cell.WF).
        exploit VOLUME; eauto. i. des; auto. inv x1. congr.
      + apply Interval.mem_ub. destruct (rhs loc).(Cell.WF).
        exploit VOLUME; eauto. i. des; auto. inv x1. congr.
  Qed.

  Lemma disjoint_get_general
        lhs rhs
        loc ts0 ts1 ts2 ts3 msgl msgr
        (TS12: Time.lt ts1 ts2)
        (TS23: Time.le ts2 ts3)
        (DISJOINT: disjoint lhs rhs)
        (LMSG: get loc ts2 lhs = Some (ts0, msgl))
        (RMSG: get loc ts3 rhs = Some (ts1, msgr)):
    False.
  Proof.
    inv DISJOINT. exploit DISJOINT0; eauto. i. des.
    destruct (Time.le_lt_dec ts2 ts0).
    - destruct (lhs loc).(Cell.WF). exploit VOLUME; eauto. i. des.
      + inv x1. inv TS12.
      + eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt; eauto.
    - eapply x.
      + eapply Interval.mem_ub. auto.
      + econs; auto.
  Qed.

  Definition bot: t := fun _ => Cell.bot.

  Lemma bot_get loc ts: get loc ts bot = None.
  Proof. unfold get. apply Cell.bot_get. Qed.

  Lemma bot_le mem: le bot mem.
  Proof. ii. rewrite bot_get in LHS. congr. Qed.

  Lemma bot_disjoint mem: disjoint bot mem.
  Proof.
    econs. i. rewrite bot_get in *. inv GET1.
  Qed.

  Definition singleton
             (loc:Loc.t) (from to:Time.t) (msg:Message.t)
             (LT: Time.lt from to)
             (WF: Message.wf msg): t :=
    (LocFun.add loc (Cell.singleton LT WF)
                (fun _ => Cell.bot)).

  Lemma singleton_get
        loc from to msg l t
        (LT:Time.lt from to)
        (WF: Message.wf msg):
    get l t (singleton loc LT WF) =
    if Loc.eq_dec l loc
    then if Time.eq_dec t to
         then Some (from, msg)
         else None
    else None.
  Proof.
    unfold get, singleton. unfold LocFun.add, LocFun.find.
    repeat condtac; subst.
    - rewrite Cell.singleton_get. condtac; [|congr]. auto.
    - rewrite Cell.singleton_get. condtac; [congr|]. auto.
    - apply Cell.bot_get.
  Qed.

  Definition init: t := fun _ => Cell.init.

  Definition finite (mem:t): Prop :=
    exists dom,
    forall loc from to msg (GET: get loc to mem = Some (from, msg)),
      List.In (loc, to) dom.

  Lemma bot_finite: finite bot.
  Proof.
    exists []. ii. rewrite bot_get in *. congr.
  Qed.

  Definition finite_half (mem:t): Prop :=
    exists dom,
    forall loc from to (GET: get loc to mem = Some (from, Message.half)),
      List.In (loc, to) dom.

  Lemma bot_finite_half: finite_half bot.
  Proof.
    exists []. ii. rewrite bot_get in *. congr.
  Qed.

  Lemma init_finite_half: finite_half init.
  Proof.
    exists []. i. revert GET. unfold get. unfold init. s.
    rewrite Cell.init_get. condtac; ss.
  Qed.

  Inductive message_to: forall (msg:Message.t) (loc:Loc.t) (to:Time.t), Prop :=
  | message_to_full
      val released loc to
      (TS: Time.le (released.(View.unwrap).(View.rlx) loc) to):
      message_to (Message.full val released) loc to
  | message_to_half
      loc to:
      message_to Message.half loc to
  .
  Hint Constructors message_to.

  Definition closed_timemap (times:TimeMap.t) (mem:t): Prop :=
    forall loc, exists from val released, get loc (times loc) mem = Some (from, Message.full val released).

  Inductive closed_view (view:View.t) (mem:t): Prop :=
  | closed_view_intro
      (PLN: closed_timemap view.(View.pln) mem)
      (RLX: closed_timemap view.(View.rlx) mem)
  .
  Hint Constructors closed_view.

  Inductive closed_opt_view: forall (view:option View.t) (mem:t), Prop :=
  | closed_opt_view_some
      view mem
      (CLOSED: closed_view view mem):
      closed_opt_view (Some view) mem
  | closed_opt_view_none
      mem:
      closed_opt_view None mem
  .
  Hint Constructors closed_opt_view.

  Inductive closed_message: forall (msg:Message.t) (mem:t), Prop :=
  | closed_message_full
      val released mem
      (CLOSED: closed_opt_view released mem):
      closed_message (Message.full val released) mem
  | closed_message_half
      mem:
      closed_message Message.half mem
  .
  Hint Constructors closed_message.


  Definition inhabited (mem:t): Prop :=
    forall loc, get loc Time.bot mem = Some (Time.bot, Message.elt).
  Hint Unfold inhabited.

  Inductive closed (mem:t): Prop :=
  | closed_intro
      (CLOSED: forall loc from to msg
                 (MSG: get loc to mem = Some (from, msg)),
          <<MSG_WF: Message.wf msg>> /\
          <<MSG_TS: message_to msg loc to>> /\
          <<MSG_CLOSED: closed_message msg mem>>)
      (INHABITED: inhabited mem)
      (FINITE_HALF: finite_half mem)
  .
  Hint Constructors closed.

  Lemma closed_timemap_bot
        mem
        (INHABITED: inhabited mem):
    closed_timemap TimeMap.bot mem.
  Proof. ii. esplits. eapply INHABITED. Qed.

  Lemma closed_view_bot
        mem
        (INHABITED: inhabited mem):
    closed_view View.bot mem.
  Proof. econs; apply closed_timemap_bot; auto. Qed.

  Lemma unwrap_closed_opt_view
        view mem
        (CLOSED: closed_opt_view view mem)
        (INHABITED: inhabited mem):
    closed_view view.(View.unwrap) mem.
  Proof.
    inv CLOSED; ss. apply closed_view_bot. ss.
  Qed.

  Lemma init_closed: closed init.
  Proof.
    econs; i; ss.
    - unfold get, init, Cell.get, Cell.init in MSG. ss.
      apply DOMap.singleton_find_inv in MSG. des. inv MSG0.
      splits; try econs; ss. refl.
    - apply init_finite_half.
  Qed.

  Definition half_wf (mem:t): Prop :=
    forall loc from to (MSG: get loc to mem = Some (from, Message.half)),
    exists from' val' released',
      get loc from mem = Some (from', Message.full val' released').

  Lemma init_half_wf: half_wf init.
  Proof.
    ii. unfold get, init, Cell.get, Cell.init in MSG. ss.
    apply DOMap.singleton_find_inv in MSG. des. inv MSG0.
  Qed.

  Inductive add (mem1:t) (loc:Loc.t) (from to:Time.t) (msg:Message.t) (mem2:t): Prop :=
  | add_intro
      r
      (ADD: Cell.add (mem1 loc) from to msg r)
      (MEM2: mem2 = LocFun.add loc r mem1)
  .
  Hint Constructors add.

  Inductive split (mem1:t) (loc:Loc.t) (ts1 ts2 ts3:Time.t) (msg2 msg3:Message.t) (mem2:t): Prop :=
  | split_intro
      r
      (SPLIT: Cell.split (mem1 loc) ts1 ts2 ts3 msg2 msg3 r)
      (MEM2: mem2 = LocFun.add loc r mem1)
  .
  Hint Constructors split.

  Inductive lower (mem1:t) (loc:Loc.t) (from to:Time.t) (msg1 msg2:Message.t) (mem2:t): Prop :=
  | lower_intro
      r
      (LOWER: Cell.lower (mem1 loc) from to msg1 msg2 r)
      (MEM2: mem2 = LocFun.add loc r mem1)
  .
  Hint Constructors lower.

  Inductive remove (mem1:t) (loc:Loc.t) (from1 to1:Time.t) (msg1:Message.t) (mem2:t): Prop :=
  | remove_intro
      r
      (REMOVE: Cell.remove (mem1 loc) from1 to1 msg1 r)
      (MEM2: mem2 = LocFun.add loc r mem1)
  .
  Hint Constructors remove.

  Inductive op_kind :=
  | op_kind_add
  | op_kind_split (ts3:Time.t) (msg3:Message.t)
  | op_kind_lower (msg1:Message.t)
  .
  Hint Constructors op_kind.

  Inductive op_kind_match: forall (k1 k2:op_kind), Prop :=
  | op_kind_match_add:
      op_kind_match
        op_kind_add
        op_kind_add
  | op_kind_match_split
      to m1 m2:
      op_kind_match
        (op_kind_split to m1)
        (op_kind_split to m2)
  | op_kind_match_lower
      m1 m2:
      op_kind_match
        (op_kind_lower m1)
        (op_kind_lower m2)
  .

  Definition op_kind_is_add kind :=
    match kind with op_kind_add => true | _ => false end.

  Definition op_kind_is_split kind :=
    match kind with op_kind_split _ _ => true | _ => false end.

  Definition op_kind_is_lower (kind:op_kind): bool :=
    match kind with op_kind_lower _ => true | _ => false end.

  Definition op_kind_is_lower_half (kind:op_kind): bool :=
    match kind with op_kind_lower Message.half => true | _ => false end.

  Definition op_kind_is_lower_full (kind:op_kind): bool :=
    match kind with op_kind_lower (Message.full _ _) => true | _ => false end.

  Inductive op mem1 loc from to msg mem2: forall (kind:op_kind), Prop :=
  | op_add
      (ADD: add mem1 loc from to msg mem2):
      op mem1 loc from to msg mem2 op_kind_add
  | op_split
      to3 msg3
      (SPLIT: split mem1 loc from to to3 msg msg3 mem2):
      op mem1 loc from to msg mem2 (op_kind_split to3 msg3)
  | op_lower
      msg0
      (LOWER: lower mem1 loc from to msg0 msg mem2):
      op mem1 loc from to msg mem2 (op_kind_lower msg0)
  .
  Hint Constructors op.

  Inductive future_imm (mem1 mem2:t): Prop :=
  | future_imm_intro
      loc from to msg kind
      (OP: op mem1 loc from to msg mem2 kind)
      (CLOSED: closed_message msg mem2)
      (TS: message_to msg loc to)
  .
  Hint Constructors future_imm.

  Definition future := rtc future_imm.
  Hint Unfold future.

  Inductive promise
            (promises1 mem1:t)
            (loc:Loc.t) (from to:Time.t) (msg:Message.t)
            (promises2 mem2:t): forall (kind:op_kind), Prop :=
  | promise_add
      (PROMISES: add promises1 loc from to msg promises2)
      (MEM: add mem1 loc from to msg mem2)
      (TS: message_to msg loc to)
      (HALF: msg = Message.half ->
             exists from' val' released',
               get loc from mem1 = Some (from', Message.full val' released')):
      promise promises1 mem1 loc from to msg promises2 mem2 op_kind_add
  | promise_split
      ts3 msg3
      (PROMISES: split promises1 loc from to ts3 msg msg3 promises2)
      (MEM: split mem1 loc from to ts3 msg msg3 mem2)
      (TS: message_to msg loc to)
      (HALF1: msg = Message.half ->
              exists from' val' released',
                get loc from mem1 = Some (from', Message.full val' released'))
      (HALF2: msg3 = Message.half ->
              exists val' released', msg = Message.full val' released'):
      promise promises1 mem1 loc from to msg promises2 mem2 (op_kind_split ts3 msg3)
  | promise_lower
      msg0
      (PROMISES: lower promises1 loc from to msg0 msg promises2)
      (MEM: lower mem1 loc from to msg0 msg mem2)
      (TS: message_to msg loc to):
      promise promises1 mem1 loc from to msg promises2 mem2 (op_kind_lower msg0)
  .
  Hint Constructors promise.

  Inductive write
            (promises1 mem1:t)
            (loc:Loc.t) (from1 to1:Time.t) (val:Const.t) (released: option View.t)
            (promises3 mem2:t) (kind:op_kind): Prop :=
  | write_intro
      promises2
      (PROMISE: promise promises1 mem1 loc from1 to1 (Message.full val released) promises2 mem2 kind)
      (REMOVE: remove promises2 loc from1 to1 (Message.full val released) promises3)
  .
  Hint Constructors write.


  (* Lemmas on add, split, lower & remove *)

  Lemma add_o
        mem2 mem1 loc from to msg
        l t
        (ADD: add mem1 loc from to msg mem2):
    get l t mem2 =
    if loc_ts_eq_dec (l, t) (loc, to)
    then Some (from, msg)
    else get l t mem1.
  Proof.
    inv ADD. unfold get, LocFun.add. condtac.
    - subst. erewrite Cell.add_o; eauto.
      repeat (condtac; subst; des; ss; try congr).
    - repeat (condtac; subst; des; ss; try congr).
  Qed.

  Lemma split_o
        mem2 mem1 loc ts1 ts2 ts3 msg2 msg3
        l t
        (SPLIT: split mem1 loc ts1 ts2 ts3 msg2 msg3 mem2):
    get l t mem2 =
    if loc_ts_eq_dec (l, t) (loc, ts2)
    then Some (ts1, msg2)
    else if loc_ts_eq_dec (l, t) (loc, ts3)
         then Some (ts2, msg3)
         else get l t mem1.
  Proof.
    inv SPLIT. unfold get, LocFun.add. condtac.
    - subst. erewrite Cell.split_o; eauto.
      repeat (condtac; subst; des; ss; try congr).
    - repeat (condtac; subst; des; ss; try congr).
  Qed.

  Lemma lower_o
        mem2 mem1 loc from to msg1 msg2
        l t
        (LOWER: lower mem1 loc from to msg1 msg2 mem2):
    get l t mem2 =
    if loc_ts_eq_dec (l, t) (loc, to)
    then Some (from, msg2)
    else get l t mem1.
  Proof.
    inv LOWER. unfold get, LocFun.add. condtac.
    - subst. erewrite Cell.lower_o; eauto.
      repeat (condtac; subst; des; ss; try congr).
    - repeat (condtac; subst; des; ss; try congr).
  Qed.

  Lemma remove_o
        mem2 mem1 loc from to msg
        l t
        (REMOVE: remove mem1 loc from to msg mem2):
    get l t mem2 =
    if loc_ts_eq_dec (l, t) (loc, to)
    then None
    else get l t mem1.
  Proof.
    inv REMOVE. unfold get, LocFun.add. condtac.
    - subst. erewrite Cell.remove_o; eauto.
      repeat (condtac; subst; des; ss; try congr).
    - repeat (condtac; subst; des; ss; try congr).
  Qed.

  Lemma add_get0
        mem1 loc from1 to1 msg1 mem2
        (ADD: add mem1 loc from1 to1 msg1 mem2):
    <<GET: get loc to1 mem1 = None>> /\
    <<GET: get loc to1 mem2 = Some (from1, msg1)>>.
  Proof.
    inv ADD. eapply Cell.add_get0; eauto.
    unfold get, Cell.get, LocFun.add. condtac; ss.
  Qed.

  Lemma split_get0
        mem1 loc ts1 ts2 ts3 msg2 msg3 mem2
        (SPLIT: split mem1 loc ts1 ts2 ts3 msg2 msg3 mem2):
    <<GET: get loc ts2 mem1 = None>> /\
    <<GET: get loc ts3 mem1 = Some (ts1, msg3)>> /\
    <<GET: get loc ts2 mem2 = Some (ts1, msg2)>> /\
    <<GET: get loc ts3 mem2 = Some (ts2, msg3)>>.
  Proof.
    inv SPLIT. eapply Cell.split_get0; eauto.
    unfold get, Cell.get, LocFun.add. condtac; ss.
  Qed.

  Lemma lower_get0
        mem1 loc from to msg1 msg2 mem2
        (LOWER: lower mem1 loc from to msg1 msg2 mem2):
    <<GET: get loc to mem1 = Some (from, msg1)>> /\
    <<GET: get loc to mem2 = Some (from, msg2)>> /\
    <<MSG_LE: Message.le msg2 msg1>>.
  Proof.
    inv LOWER. eapply Cell.lower_get0; eauto.
    unfold get, Cell.get, LocFun.add. condtac; ss.
  Qed.

  Lemma remove_get0
        mem1 loc from1 to1 msg1 mem2
        (REMOVE: remove mem1 loc from1 to1 msg1 mem2):
    <<GET: get loc to1 mem1 = Some (from1, msg1)>> /\
    <<GET: get loc to1 mem2 = None>>.
  Proof.
    inv REMOVE. eapply Cell.remove_get0; eauto.
    unfold get, Cell.get, LocFun.add. condtac; ss.
  Qed.

  Lemma add_get1
        m1 loc from to msg m2
        l f t m
        (ADD: add m1 loc from to msg m2)
        (GET1: get l t m1 = Some (f, m)):
    get l t m2 = Some (f, m).
  Proof.
    erewrite add_o; eauto. condtac; ss.
    des. subst. exploit add_get0; eauto. i. des. congr.
  Qed.

  Lemma split_get1
        m1 loc ts1 ts2 ts3 msg2 msg3 m2
        l f t m
        (SPLIT: split m1 loc ts1 ts2 ts3 msg2 msg3 m2)
        (GET1: get l t m1 = Some (f, m)):
    exists f',
      <<GET2: get l t m2 = Some (f', m)>> /\
      <<FROM: Time.le f f'>>.
  Proof.
    erewrite split_o; eauto. repeat condtac; ss.
    - des. subst. exploit split_get0; eauto. i. des. congr.
    - guardH o. des. subst. exploit split_get0; eauto. i. des.
      rewrite GET1 in GET0. inv GET0.
      esplits; eauto.
      inv SPLIT. inv SPLIT0. left. ss.
    - esplits; eauto.
      refl.
  Qed.

  Lemma lower_get1
        m1 loc from to msg1 msg2 m2
        l f t m
        (LOWER: lower m1 loc from to msg1 msg2 m2)
        (GET1: get l t m1 = Some (f, m)):
    exists m',
      <<GET2: get l t m2 = Some (f, m')>> /\
      <<MSG_LE: Message.le m' m>>.
  Proof.
    erewrite lower_o; eauto. condtac; ss.
    - des. subst. exploit lower_get0; eauto. i. des.
      rewrite GET1 in GET. inv GET.
      esplits; eauto.
    - esplits; eauto.
      refl.
  Qed.

  Lemma add_inhabited
        mem1 mem2 loc from to msg
        (ADD: add mem1 loc from to msg mem2)
        (INHABITED: inhabited mem1):
    <<INHABITED: inhabited mem2>>.
  Proof.
    ii. erewrite add_o; eauto. condtac; ss.
    des. subst. inv ADD. inv ADD0. inv TO.
  Qed.

  Lemma split_inhabited
        mem1 mem2 loc ts1 ts2 ts3 msg2 msg3
        (SPLIT: split mem1 loc ts1 ts2 ts3 msg2 msg3 mem2)
        (INHABITED: inhabited mem1):
    <<INHABITED: inhabited mem2>>.
  Proof.
    ii. erewrite split_o; eauto. repeat (condtac; ss).
    - des. subst. inv SPLIT. inv SPLIT0. inv TS12.
    - des; subst; try congr. inv SPLIT. inv SPLIT0. inv TS23.
  Qed.

  Lemma lower_inhabited
        mem1 mem2 loc from to msg1 msg2
        (LOWER: lower mem1 loc from to msg1 msg2 mem2)
        (INHABITED: inhabited mem1):
    <<INHABITED: inhabited mem2>>.
  Proof.
    ii. erewrite lower_o; eauto. condtac; ss.
    des. subst. inv LOWER. inv LOWER0. inv TS.
  Qed.

  Lemma add_le mem1 mem2 loc from to msg
        (ADD: add mem1 loc from to msg mem2):
    le mem1 mem2.
  Proof.
    ii. erewrite add_o; eauto. condtac; ss.
    des. subst. exploit add_get0; eauto. i. des. congr.
  Qed.


  (* Lemmas on op *)

  Lemma promise_op
        promises1 mem1 loc from to msg promises2 mem2 kind
        (PROMISE: promise promises1 mem1 loc from to msg promises2 mem2 kind):
    op mem1 loc from to msg mem2 kind.
  Proof.
    inv PROMISE.
    - econs 1. ss.
    - econs 2. ss.
    - econs 3. ss.
  Qed.

  Lemma op_get1
        m1 loc from to msg m2 kind
        l f t m
        (OP: op m1 loc from to msg m2 kind)
        (GET: get l t m1 = Some (f, m)):
    exists f' m',
      <<GET: get l t m2 = Some (f', m')>> /\
      <<FROM: Time.le f f'>> /\
      <<MSG_LE: Message.le m' m>>.
  Proof.
    inv OP.
    - exploit add_get1; eauto. i. des. esplits; eauto; refl.
    - exploit split_get1; eauto. i. des. esplits; eauto; refl.
    - exploit lower_get1; eauto. i. des. esplits; eauto; refl.
  Qed.

  Lemma op_get2
        m1 l f t msg m2 k
        (OP: op m1 l f t msg m2 k):
    get l t m2 = Some (f, msg).
  Proof.
    inv OP.
    - erewrite add_o; eauto. condtac; ss. des; congr.
    - erewrite split_o; eauto. condtac; ss. des; congr.
    - erewrite lower_o; eauto. condtac; ss. des; congr.
  Qed.

  Lemma op_get_inv
        mem1 loc from to msg mem2 kind
        l f t m
        (OP: op mem1 loc from to msg mem2 kind)
        (GET2: get l t mem2 = Some (f, m)):
    (l = loc /\ f = from /\ t = to /\ m = msg) \/
    (__guard__ (l <> loc \/ t <> to) /\
     exists f',
       <<GET1: get l t mem1 = Some (f', m)>> /\
       <<FROM: Time.le f' f>>).
  Proof.
    revert GET2. inv OP.
    - erewrite add_o; eauto. condtac; ss.
      + i. des. inv GET2. left. auto.
      + i. right. esplits; eauto. refl.
    - erewrite split_o; eauto. repeat condtac; ss.
      + i. des. inv GET2. left. auto.
      + guardH o. i. des. inv GET2. right. splits; auto.
        exploit split_get0; try exact MEM; eauto. i. des.
        rewrite GET0. esplits; eauto. inv SPLIT. inv SPLIT0. left. auto.
      + i. right. esplits; eauto. refl.
    - erewrite lower_o; eauto. condtac; ss.
      + i. des. inv GET2. left. auto.
      + i. right. esplits; eauto. refl.
  Qed.

  Lemma op_inhabited kind
        mem1 mem2 loc from to msg
        (OP: op mem1 loc from to msg mem2 kind)
        (INHABITED: inhabited mem1):
    inhabited mem2.
  Proof.
    inv OP.
    - eapply add_inhabited; eauto.
    - eapply split_inhabited; eauto.
    - eapply lower_inhabited; eauto.
  Qed.

  Lemma future_get1
        loc from to msg mem1 mem2
        (LE: future mem1 mem2)
        (GET: get loc to mem1 = Some (from, msg)):
    exists from' msg',
      <<GET: get loc to mem2 = Some (from', msg')>> /\
      <<FROM: Time.le from from'>> /\
      <<MSG_LE: Message.le msg' msg>>.
  Proof.
    revert from msg GET. induction LE.
    { i. esplits; eauto; refl. }
    i. inv H. exploit op_get1; eauto. i. des.
    exploit IHLE; eauto. i. des.
    esplits; eauto. etrans; eauto.
  Qed.


  (* lemmas on finite *)

  Lemma add_finite
        mem1 loc from to msg mem2
        (ADD: add mem1 loc from to msg mem2)
        (FINITE: finite mem1):
    finite mem2.
  Proof.
    unfold finite in *. des. exists ((loc, to) :: dom). i.
    revert GET. erewrite add_o; eauto. condtac; ss; eauto.
    i. des. inv GET. auto.
  Qed.

  Lemma split_finite
        mem1 loc ts1 ts2 ts3 msg2 msg3 mem2
        (SPLIT: split mem1 loc ts1 ts2 ts3 msg2 msg3 mem2)
        (FINITE: finite mem1):
    finite mem2.
  Proof.
    unfold finite in *. des. exists ((loc, ts2) :: dom). i.
    revert GET. erewrite split_o; eauto. repeat condtac; ss; eauto.
    - i. des. inv GET. auto.
    - guardH o. i. des. inv GET. right. eapply FINITE.
      hexploit split_get0; eauto. i. des. eauto.
  Qed.

  Lemma lower_finite
        mem1 loc from to msg1 msg2 mem2
        (LOWER: lower mem1 loc from to msg1 msg2 mem2)
        (FINITE: finite mem1):
    finite mem2.
  Proof.
    unfold finite in *. des. exists dom. i.
    revert GET. erewrite lower_o; eauto. condtac; ss; eauto.
    i. des. inv GET. eapply FINITE.
    hexploit lower_get0; eauto. i. des. eauto.
  Qed.

  Lemma remove_finite
        mem1 loc from to msg mem2
        (REMOVE: remove mem1 loc from to msg mem2)
        (FINITE: finite mem1):
    finite mem2.
  Proof.
    unfold finite in *. des. exists dom. i.
    revert GET. erewrite remove_o; eauto. condtac; ss; eauto.
  Qed.

  Lemma add_finite_half
        mem1 loc from to msg mem2
        (ADD: add mem1 loc from to msg mem2)
        (FINITE: finite_half mem1):
    finite_half mem2.
  Proof.
    unfold finite_half in *. des. destruct msg.
    - exists dom. i.
      revert GET. erewrite add_o; eauto. condtac; ss; eauto.
    - exists ((loc, to) :: dom). i.
      revert GET. erewrite add_o; eauto. condtac; ss; eauto.
      i. des. inv GET. auto.
  Qed.

  Lemma split_finite_half
        mem1 loc ts1 ts2 ts3 msg2 msg3 mem2
        (SPLIT: split mem1 loc ts1 ts2 ts3 msg2 msg3 mem2)
        (FINITE: finite_half mem1):
    finite_half mem2.
  Proof.
    unfold finite_half in *. des. destruct msg2.
    - exists dom. i.
      revert GET. erewrite split_o; eauto. repeat condtac; ss; eauto.
      guardH o. des. i. inv GET.
      exploit split_get0; eauto. i. des.
      eapply FINITE; eauto.
    - exists ((loc, ts2) :: dom). i.
      revert GET. erewrite split_o; eauto. repeat condtac; ss; eauto.
      + i. des. inv GET. auto.
      + guardH o. i. des. inv GET.
        exploit split_get0; eauto. i. des.
        right. eapply FINITE; eauto.
  Qed.

  Lemma lower_finite_half
        mem1 loc from to msg1 msg2 mem2
        (LOWER: lower mem1 loc from to msg1 msg2 mem2)
        (FINITE: finite_half mem1):
    finite_half mem2.
  Proof.
    unfold finite_half in *. des. destruct msg1, msg2.
    - exists dom. i.
      revert GET. erewrite lower_o; eauto. condtac; ss; eauto.
    - inv LOWER. inv LOWER0. inv MSG_LE.
    - exists ((loc, to) :: dom). i.
      revert GET. erewrite lower_o; eauto. repeat condtac; ss; eauto.
    - exists dom. i.
      revert GET. erewrite lower_o; eauto. condtac; ss; eauto.
      des. subst. i.
      exploit lower_get0; eauto. i. des.
      eapply FINITE; eauto.
  Qed.

  Lemma remove_finite_half
        mem1 loc from to msg mem2
        (REMOVE: remove mem1 loc from to msg mem2)
        (FINITE: finite_half mem1):
    finite_half mem2.
  Proof.
    unfold finite_half in *. des. exists dom. i.
    revert GET. erewrite remove_o; eauto. condtac; ss; eauto.
  Qed.


  (* Lemmas on closedness *)

  Lemma join_closed_timemap
        lhs rhs mem
        (LHS: closed_timemap lhs mem)
        (RHS: closed_timemap rhs mem):
    closed_timemap (TimeMap.join lhs rhs) mem.
  Proof.
    ii. unfold TimeMap.join.
    destruct (Time.join_cases (lhs loc) (rhs loc)) as [X|X]; rewrite X.
    - apply LHS.
    - apply RHS.
  Qed.

  Lemma join_closed_view
        lhs rhs mem
        (LHS: closed_view lhs mem)
        (RHS: closed_view rhs mem):
    closed_view (View.join lhs rhs) mem.
  Proof.
    econs.
    - apply join_closed_timemap.
      + apply LHS.
      + apply RHS.
    - apply join_closed_timemap.
      + apply LHS.
      + apply RHS.
  Qed.

  Lemma add_closed_timemap
        times
        mem1 loc from to msg mem2
        (ADD: add mem1 loc from to msg mem2)
        (CLOSED: closed_timemap times mem1):
    closed_timemap times mem2.
  Proof.
    ii. erewrite add_o; eauto. condtac; ss.
    des. subst. exfalso.
    specialize (CLOSED loc). des.
    inv ADD. inv ADD0. eapply DISJOINT; eauto.
    all: econs; eauto; ss; try refl.
    exploit get_ts; eauto. i. des; ss.
    rewrite x1 in TO. inv TO.
  Qed.

  Lemma add_closed_view
        view
        mem1 loc from to msg mem2
        (ADD: add mem1 loc from to msg mem2)
        (CLOSED: closed_view view mem1):
    closed_view view mem2.
  Proof.
    inv CLOSED. econs; eauto.
    - eapply add_closed_timemap; eauto.
    - eapply add_closed_timemap; eauto.
  Qed.

  Lemma add_closed_opt_view
        view
        mem1 loc from to msg mem2
        (ADD: add mem1 loc from to msg mem2)
        (CLOSED: closed_opt_view view mem1):
    closed_opt_view view mem2.
  Proof.
    inv CLOSED; econs. eapply add_closed_view; eauto.
  Qed.

  Lemma add_closed_message
        msg'
        mem1 loc from to msg mem2
        (ADD: add mem1 loc from to msg mem2)
        (CLOSED: closed_message msg' mem1):
    closed_message msg' mem2.
  Proof.
    destruct msg'; ss. inv CLOSED. econs.
    eapply add_closed_opt_view; eauto.
  Qed.

  Lemma add_closed
        mem1 loc from to msg mem2
        (ADD: add mem1 loc from to msg mem2)
        (CLOSED: closed mem1)
        (MSG_CLOSED: closed_message msg mem2)
        (MSG_TS: message_to msg loc to):
    closed mem2.
  Proof.
    inv CLOSED. econs.
    - i. revert MSG. erewrite add_o; eauto. condtac; ss.
      + des. subst. i. inv MSG. splits; auto.
        inv ADD. inv ADD0. auto.
      + guardH o. i. exploit CLOSED0; eauto. i. des. splits; auto.
        eapply add_closed_message; eauto.
    - eapply add_inhabited; eauto.
    - eapply add_finite_half; eauto.
  Qed.

  Lemma split_closed_timemap
        times
        mem1 loc ts1 ts2 ts3 msg2 msg3 mem2
        (SPLIT: split mem1 loc ts1 ts2 ts3 msg2 msg3 mem2)
        (CLOSED: closed_timemap times mem1):
    closed_timemap times mem2.
  Proof.
    ii. erewrite split_o; eauto. repeat condtac; ss.
    - des. subst. exfalso.
      specialize (CLOSED loc). des.
      inv SPLIT. inv SPLIT0. unfold get in CLOSED.
      destruct (mem1 loc). generalize WF. intro X. inv X. ss.
      eapply DISJOINT; [exact CLOSED|exact GET2|..].
      + ii. subst. timetac.
      + econs; ss; try refl.
        exploit Cell.get_ts; try eapply CLOSED. i. des; ss.
        rewrite x1 in *. inv TS12.
      + econs; ss; try refl.
        exploit (Cell.get_ts ts3 (Cell.mk WF)).
        { unfold Cell.get. ss. eauto. }
        i. des; subst.
        * inv TS23.
        * specialize (Time.le_lteq (times loc) ts3). i. des.
          apply H0. auto.
    - guardH o. des. subst. destruct msg3.
      { esplits; ss. }
      specialize (CLOSED loc). des.
      inv SPLIT. inv SPLIT0.
      unfold get in CLOSED. unfold Cell.get in CLOSED.
      rewrite CLOSED in GET2. inv GET2.
  Qed.

  Lemma split_closed_view
        view
        mem1 loc ts1 ts2 ts3 msg2 msg3 mem2
        (SPLIT: split mem1 loc ts1 ts2 ts3 msg2 msg3 mem2)
        (CLOSED: closed_view view mem1):
    closed_view view mem2.
  Proof.
    inv CLOSED. econs; eauto.
    - eapply split_closed_timemap; eauto.
    - eapply split_closed_timemap; eauto.
  Qed.

  Lemma split_closed_opt_view
        view
        mem1 loc ts1 ts2 ts3 msg2 msg3 mem2
        (SPLIT: split mem1 loc ts1 ts2 ts3 msg2 msg3 mem2)
        (CLOSED: closed_opt_view view mem1):
    closed_opt_view view mem2.
  Proof.
    inv CLOSED; econs. eapply split_closed_view; eauto.
  Qed.

  Lemma split_closed_message
        msg'
        mem1 loc ts1 ts2 ts3 msg2 msg3 mem2
        (SPLIT: split mem1 loc ts1 ts2 ts3 msg2 msg3 mem2)
        (CLOSED: closed_message msg' mem1):
    closed_message msg' mem2.
  Proof.
    destruct msg'; ss. inv CLOSED. econs.
    eapply split_closed_opt_view; eauto.
  Qed.

  Lemma split_closed
        mem1 loc ts1 ts2 ts3 msg2 msg3 mem2
        (SPLIT: split mem1 loc ts1 ts2 ts3 msg2 msg3 mem2)
        (CLOSED: closed mem1)
        (MSG_CLOSED: closed_message msg2 mem2)
        (MSG_TS: message_to msg2 loc ts2):
    closed mem2.
  Proof.
    inv CLOSED. econs.
    - i. revert MSG. erewrite split_o; eauto. repeat condtac; ss.
      + des. subst. i. inv MSG. splits; eauto.
        inv SPLIT. inv SPLIT0. auto.
      + guardH o. des. subst. i. inv MSG.
        exploit split_get0; eauto. i. des. exploit CLOSED0; eauto. i. des.
        splits; eauto.
        eapply split_closed_message; eauto.
      + guardH o. guardH o0. i. exploit CLOSED0; eauto. i. des. splits; auto.
        eapply split_closed_message; eauto.
    - eapply split_inhabited; eauto.
    - eapply split_finite_half; eauto.
  Qed.

  Lemma lower_closed_timemap
        times
        mem1 loc from to msg1 msg2 mem2
        (LOWER: lower mem1 loc from to msg1 msg2 mem2)
        (CLOSED: closed_timemap times mem1):
    closed_timemap times mem2.
  Proof.
    ii. erewrite lower_o; eauto. condtac; ss.
    des. subst. destruct msg2; eauto.
    inv LOWER. inv LOWER0. inv MSG_LE.
    specialize (CLOSED loc). des.
    unfold get in CLOSED. unfold Cell.get in CLOSED.
    rewrite CLOSED in GET2. inv GET2.
  Qed.

  Lemma lower_closed_view
        view
        mem1 loc from to msg1 msg2 mem2
        (LOWER: lower mem1 loc from to msg1 msg2 mem2)
        (CLOSED: closed_view view mem1):
    closed_view view mem2.
  Proof.
    inv CLOSED. econs; eauto.
    - eapply lower_closed_timemap; eauto.
    - eapply lower_closed_timemap; eauto.
  Qed.

  Lemma lower_closed_opt_view
        view
        mem1 loc from to msg1 msg2 mem2
        (LOWER: lower mem1 loc from to msg1 msg2 mem2)
        (CLOSED: closed_opt_view view mem1):
    closed_opt_view view mem2.
  Proof.
    inv CLOSED; econs. eapply lower_closed_view; eauto.
  Qed.

  Lemma lower_closed_message
        msg'
        mem1 loc from to msg1 msg2 mem2
        (LOWER: lower mem1 loc from to msg1 msg2 mem2)
        (CLOSED: closed_message msg' mem1):
    closed_message msg' mem2.
  Proof.
    destruct msg'; ss. inv CLOSED. econs.
    eapply lower_closed_opt_view; eauto.
  Qed.

  Lemma lower_closed
        mem1 loc from to msg1 msg2 mem2
        (LOWER: lower mem1 loc from to msg1 msg2 mem2)
        (CLOSED: closed mem1)
        (MSG_CLOSED: closed_message msg2 mem2)
        (MSG_TS: message_to msg2 loc to):
    closed mem2.
  Proof.
    inv CLOSED. econs.
    - i. revert MSG. erewrite lower_o; eauto. condtac; ss.
      + des. subst. i. inv MSG. splits; auto.
        inv LOWER. inv LOWER0. auto.
      + guardH o. i. exploit CLOSED0; eauto. i. des. splits; auto.
        eapply lower_closed_message; eauto.
    - eapply lower_inhabited; eauto.
    - eapply lower_finite_half; eauto.
  Qed.

  Lemma op_closed_timemap
        times
        mem1 loc from to msg mem2 kind
        (OP: op mem1 loc from to msg mem2 kind)
        (CLOSED: closed_timemap times mem1):
    closed_timemap times mem2.
  Proof.
    inv OP.
    - eapply add_closed_timemap; eauto.
    - eapply split_closed_timemap; eauto.
    - eapply lower_closed_timemap; eauto.
  Qed.

  Lemma op_closed_view
        view
        mem1 loc from to msg mem2 kind
        (OP: op mem1 loc from to msg mem2 kind)
        (CLOSED: closed_view view mem1):
    closed_view view mem2.
  Proof.
    inv OP.
    - eapply add_closed_view; eauto.
    - eapply split_closed_view; eauto.
    - eapply lower_closed_view; eauto.
  Qed.

  Lemma op_closed_opt_view
        kind view
        mem1 loc from to msg mem2
        (OP: Memory.op mem1 loc from to msg mem2 kind)
        (CLOSED: Memory.closed_opt_view view mem1):
    closed_opt_view view mem2.
  Proof.
    inv OP; eauto using Memory.add_closed_opt_view, Memory.split_closed_opt_view, Memory.lower_closed_opt_view.
  Qed.

  Lemma op_closed_message
        kind msg'
        mem1 loc from to msg mem2
        (OP: Memory.op mem1 loc from to msg mem2 kind)
        (CLOSED: Memory.closed_message msg' mem1):
    closed_message msg' mem2.
  Proof.
    inv OP; eauto using Memory.add_closed_message, Memory.split_closed_message, Memory.lower_closed_message.
  Qed.

  Lemma op_closed
        mem1 loc from to msg mem2 kind
        (OP: op mem1 loc from to msg mem2 kind)
        (CLOSED: closed mem1)
        (MSG_CLOSED: closed_message msg mem2)
        (MSG_TS: message_to msg loc to):
    closed mem2.
  Proof.
    inv OP; eauto using add_closed, split_closed, lower_closed.
  Qed.

  Lemma promise_closed_timemap
        times
        promises1 mem1 loc from to msg promises2 mem2 kind
        (PROMISE: promise promises1 mem1 loc from to msg promises2 mem2 kind)
        (CLOSED: closed_timemap times mem1):
    closed_timemap times mem2.
  Proof.
    eapply op_closed_timemap; eauto.
    eapply promise_op. eauto.
  Qed.

  Lemma promise_closed_view
        view
        promises1 mem1 loc from to msg promises2 mem2 kind
        (PROMISE: promise promises1 mem1 loc from to msg promises2 mem2 kind)
        (CLOSED: closed_view view mem1):
    closed_view view mem2.
  Proof.
    eapply op_closed_view; eauto.
    eapply promise_op. eauto.
  Qed.

  Lemma promise_closed_opt_view
        view
        promises1 mem1 loc from to msg promises2 mem2 kind
        (CLOSED: closed_opt_view view mem1)
        (PROMISE: promise promises1 mem1 loc from to msg promises2 mem2 kind):
    closed_opt_view view mem2.
  Proof.
    inv CLOSED; econs. eapply promise_closed_view; eauto.
  Qed.

  Lemma future_closed_timemap
        times mem1 mem2
        (CLOSED: closed_timemap times mem1)
        (FUTURE: future mem1 mem2):
    closed_timemap times mem2.
  Proof.
    revert CLOSED. induction FUTURE; auto. i.
    apply IHFUTURE. inv H. eapply op_closed_timemap; eauto.
  Qed.

  Lemma future_closed_view
        view mem1 mem2
        (FUTURE: future mem1 mem2)
        (CLOSED: closed_view view mem1):
    closed_view view mem2.
  Proof.
    revert CLOSED. induction FUTURE; auto. i.
    apply IHFUTURE. inv H. eapply op_closed_view; eauto.
  Qed.

  Lemma future_closed_opt_view
        view mem1 mem2
        (FUTURE: future mem1 mem2)
        (CLOSED: closed_opt_view view mem1):
    closed_opt_view view mem2.
  Proof.
    inv CLOSED; econs. eapply future_closed_view; eauto.
  Qed.

  Lemma future_closed_message
        msg mem1 mem2
        (FUTURE: future mem1 mem2)
        (CLOSED: closed_message msg mem1):
    closed_message msg mem2.
  Proof.
    inv CLOSED; econs. eapply future_closed_opt_view; eauto.
  Qed.

  Lemma future_closed
        mem1 mem2
        (FUTURE: future mem1 mem2)
        (CLOSED: closed mem1):
    closed mem2.
  Proof.
    revert CLOSED. induction FUTURE; auto. i. apply IHFUTURE.
    inv H. eapply op_closed; eauto.
  Qed.

  Lemma singleton_closed_timemap
        loc from to val released mem
        (GET: get loc to mem = Some (from, Message.full val released))
        (INHABITED: inhabited mem):
    closed_timemap (TimeMap.singleton loc to) mem.
  Proof.
    unfold TimeMap.singleton, LocFun.add, LocFun.find. ii. condtac.
    - subst. eauto.
    - apply closed_timemap_bot. auto.
  Qed.

  Lemma singleton_ur_closed_view
        loc from to val released mem
        (GET: get loc to mem = Some (from, Message.full val released))
        (INHABITED: inhabited mem):
    closed_view (View.singleton_ur loc to) mem.
  Proof.
    econs; s.
    - eapply singleton_closed_timemap; eauto.
    - eapply singleton_closed_timemap; eauto.
  Qed.

  Lemma singleton_rw_closed_view
        loc from to val released mem
        (GET: get loc to mem = Some (from, Message.full val released))
        (INHABITED: inhabited mem):
    closed_view (View.singleton_rw loc to) mem.
  Proof.
    econs; s.
    - apply closed_timemap_bot. auto.
    - eapply singleton_closed_timemap; eauto.
  Qed.

  Lemma singleton_ur_if_closed_view
        cond loc from to val released mem
        (GET: get loc to mem = Some (from, Message.full val released))
        (INHABITED: inhabited mem):
    closed_view (View.singleton_ur_if cond loc to) mem.
  Proof.
    destruct cond; ss.
    - eapply singleton_ur_closed_view; eauto.
    - eapply singleton_rw_closed_view; eauto.
  Qed.


  (* Lemmas on half_wf *)

  Lemma promise_half_wf
        promises1 mem1 loc from to msg promises2 mem2 kind
        (PROMISE: promise promises1 mem1 loc from to msg promises2 mem2 kind)
        (HALF_WF1: half_wf mem1):
    <<HALF_WF2: half_wf mem2>>.
  Proof.
    ii. inv PROMISE.
    - exploit add_get0; try exact MEM. i. des.
      revert MSG. erewrite add_o; eauto. condtac; ss.
      + des. subst. i. inv MSG.
        exploit HALF; eauto. i. des.
        erewrite add_o; eauto. condtac; ss; eauto.
        des. subst. inv MEM. inv ADD. timetac.
      + i. guardH o. erewrite add_o; eauto. condtac; ss; eauto.
        des. subst. exploit HALF_WF1; eauto. i. des.
        rewrite GET in x. inv x.
    - exploit split_get0; try exact MEM. i. des.
      revert MSG. erewrite split_o; eauto. repeat condtac; ss.
      + des. subst. i. inv MSG.
        exploit HALF1; eauto. i. des.
        erewrite split_o; eauto. repeat condtac; ss; eauto.
        * des. subst. inv MEM. inv SPLIT. timetac.
        * guardH o. des. subst. inv MEM. inv SPLIT.
          rewrite TS12 in TS23. timetac.
      + guardH o. des. subst. i. inv MSG.
        exploit HALF2; eauto. i. des. subst.
        erewrite split_o; eauto. repeat condtac; ss; eauto.
        * guardH o0. des. subst. inv MEM. inv SPLIT. timetac.
        * guardH o1. des; congr.
      + i. erewrite split_o; eauto. repeat condtac; ss; eauto.
        * guardH o. guardH o0. des. subst.
          exploit get_disjoint; [exact GET0|exact MSG|..]. i. des.
          { subst. inv MEM. inv SPLIT. timetac. }
          exploit get_ts; try exact MSG. i. des.
          { subst. inv MEM. inv SPLIT. inv TS12. }
          exfalso. inv MEM. inv SPLIT.
          destruct (Time.le_lt_dec ts3 to0).
          { inv l.
            - apply (x0 ts3); econs; eauto; try refl. econs. eauto.
            - inv H. unguardH o0. des; congr. }
          { apply (x0 to0); econs; eauto; try refl. econs. eauto. }
        * guardH o. guardH o0. guardH o1. des. subst.
          exploit HALF_WF1; eauto. i. des.
          rewrite GET0 in x. inv x. eauto.
    - exploit lower_get0; try exact MEM. i. des.
      revert MSG. erewrite lower_o; eauto. condtac; ss.
      + des. subst. i. inv MSG. inv MSG_LE.
        exploit HALF_WF1; eauto. i. des.
        erewrite lower_o; eauto. condtac; ss; eauto.
        des. subst. inv MEM. inv LOWER. timetac.
      + guardH o. i. exploit HALF_WF1; eauto. i. des.
        erewrite lower_o; eauto. condtac; ss; eauto.
        des. subst. rewrite GET in x. inv x. inv MSG_LE. eauto.
  Qed.

  Lemma write_half_wf
        promises1 mem1 loc from to val released promises3 mem2 kind
        (WRITE: write promises1 mem1 loc from to val released promises3 mem2 kind)
        (HALF_WF1: half_wf mem1):
    <<HALF_WF2: half_wf mem2>>.
  Proof.
    inv WRITE. eapply promise_half_wf; eauto.
  Qed.


  (* Lemmas on promise & remove *)

  Lemma promise_get0
        promises1 promises2 mem1 mem2
        loc from to msg kind
        (PROMISE: promise promises1 mem1 loc from to msg promises2 mem2 kind):
    <<GET_PROMISES: get loc to promises2 = Some (from, msg)>> /\
    <<GET_MEM: get loc to mem2 = Some (from, msg)>>.
  Proof.
    inv PROMISE.
    - erewrite (add_o _ _ PROMISES).
      erewrite (add_o _ _ MEM).
      condtac; ss. des; congr.
    - erewrite (split_o _ _ PROMISES).
      erewrite (split_o _ _ MEM).
      repeat condtac; ss; des; intuition.
    - erewrite (lower_o _ _ PROMISES).
      erewrite (lower_o _ _ MEM).
      condtac; ss. des; congr.
  Qed.

  Lemma promise_get1
        promises1 mem1 loc from to msg promises2 mem2 kind
        l t f m
        (PROMISE: promise promises1 mem1 loc from to msg promises2 mem2 kind)
        (GET: get l t mem1 = Some (f, m)):
    exists f' m',
      <<GET: get l t mem2 = Some (f', m')>> /\
      <<FROM: Time.le f f'>> /\
      <<MSG_LE: Message.le m' m>>.
  Proof.
    inv PROMISE.
    - eapply op_get1; eauto.
    - eapply op_get1; eauto.
    - eapply op_get1; eauto.
  Qed.

  Lemma promise_get1_promise
        promises1 mem1 loc from to msg promises2 mem2 kind
        l t f m
        (PROMISE: promise promises1 mem1 loc from to msg promises2 mem2 kind)
        (GET: get l t promises1 = Some (f, m)):
    exists f' m',
      <<GET: get l t promises2 = Some (f', m')>> /\
      <<FROM: Time.le f f'>> /\
      <<MSG_LE: Message.le m' m>>.
  Proof.
    inv PROMISE; eapply op_get1; eauto.
  Qed.

  Lemma promise_get2
        promises1 mem1 loc from to msg promises2 mem2 kind
        (PROMISE: promise promises1 mem1 loc from to msg promises2 mem2 kind):
    <<GET_PROMISE: get loc to promises2 = Some (from, msg)>> /\
    <<GET_MEM: get loc to mem2 = Some (from, msg)>>.
  Proof.
    inv PROMISE; splits; eauto using op_get2.
  Qed.

  Lemma op_future
        mem1 loc from to msg mem2 kind
        (OP: op mem1 loc from to msg mem2 kind)
        (CLOSED1: closed mem1)
        (MSG_CLOSED: closed_message msg mem2)
        (MSG_TS: message_to msg loc to):
    <<CLOSED2: closed mem2>> /\
    <<FUTURE: future mem1 mem2>> /\
    <<MSG_WF: Message.wf msg>>.
  Proof.
    hexploit op_inhabited; try apply CLOSED1; eauto. i. splits; auto.
    - eapply op_closed; eauto.
    - econs 2; eauto.
    - inv OP.
      + inv ADD. inv ADD0. ss.
      + inv SPLIT. inv SPLIT0. ss.
      + inv LOWER. inv LOWER0. ss.
  Qed.

  Lemma promise_future0
        promises1 mem1 loc from to msg promises2 mem2 kind
        (LE_PROMISES1: le promises1 mem1)
        (FINITE1: finite promises1)
        (INHABITED1: inhabited mem1)
        (PROMISE: promise promises1 mem1 loc from to msg promises2 mem2 kind):
    <<LE_PROMISES2: le promises2 mem2>> /\
    <<FINITE2: finite promises2>> /\
    <<INHABITED2: inhabited mem2>>.
  Proof.
    hexploit op_inhabited; eauto.
    { eapply promise_op. eauto. }
    i. splits; ss. inv PROMISE.
    - splits; eauto.
      ii. revert LHS.
      erewrite add_o; eauto. erewrite (@add_o mem2); try exact MEM; eauto.
      condtac; ss. auto.
    - splits; eauto.
      ii. revert LHS.
      erewrite split_o; eauto. erewrite (@split_o mem2); try exact MEM; eauto.
      repeat condtac; ss. auto.
    - splits; eauto.
      ii. revert LHS.
      erewrite lower_o; eauto. erewrite (@lower_o mem2); try exact MEM; eauto.
      condtac; ss. auto.
    - inv PROMISE.
      + eapply add_finite; eauto.
      + eapply split_finite; eauto.
      + eapply lower_finite; eauto.
  Qed.

  Lemma promise_future
        promises1 mem1 loc from to msg promises2 mem2 kind
        (LE_PROMISES1: le promises1 mem1)
        (FINITE1: finite promises1)
        (CLOSED1: closed mem1)
        (HALF_WF1: half_wf mem1)
        (MSG_CLOSED: closed_message msg mem2)
        (PROMISE: promise promises1 mem1 loc from to msg promises2 mem2 kind):
    <<LE_PROMISES2: le promises2 mem2>> /\
    <<FINITE2: finite promises2>> /\
    <<CLOSED2: closed mem2>> /\
    <<HALF_WF2: half_wf mem2>> /\
    <<FUTURE: future mem1 mem2>>.
  Proof.
    hexploit op_future; eauto.
    { eapply promise_op. eauto. }
    { by inv PROMISE. }
    i. des.
    exploit promise_future0; try apply CLOSED1; eauto. i. des. splits; auto.
    eapply promise_half_wf; eauto.
  Qed.

  Lemma promise_disjoint
        promises1 mem1 loc from to msg promises2 mem2 ctx kind
        (PROMISE: promise promises1 mem1 loc from to msg promises2 mem2 kind)
        (CLOSED: closed mem1)
        (FINITE: finite promises1)
        (LE: le promises1 mem1)
        (LE_CTX: le ctx mem1)
        (DISJOINT: disjoint promises1 ctx):
    <<DISJOINT: disjoint promises2 ctx>> /\
    <<LE_CTX: le ctx mem2>>.
  Proof.
    exploit promise_future0; try apply PROMISE; try apply CLOSED; eauto. i. des.
    inv PROMISE.
    - splits.
      + inv DISJOINT. econs. i. revert GET1. erewrite add_o; eauto. condtac; ss.
        * des. subst. i. inv GET1. splits.
          { inv MEM. inv ADD. eauto. }
          { ii. inv H. inv MEM. inv ADD. inv TO. }
        * i. eapply DISJOINT0; eauto.
      + ii. erewrite add_o; eauto. condtac; ss; eauto.
        des. subst. exfalso. inv MEM. inv ADD. eapply DISJOINT0; eauto.
        * apply Interval.mem_ub. auto.
        * apply Interval.mem_ub.
          destruct (mem1 loc).(Cell.WF). exploit VOLUME; eauto. i. des; auto.
          inv x. inv TO.
    - splits.
      + inv DISJOINT. econs. i. revert GET1. erewrite split_o; eauto. repeat condtac; ss.
        * des. subst. i. inv GET1.
          exploit split_get0; try exact PROMISES; eauto. i. des.
          exploit DISJOINT0; try exact GET0; eauto. i. des.
          splits.
          { eapply Interval.le_disjoint; eauto. econs; [refl|].
            left. inv MEM. inv SPLIT. auto.
          }
          { ii. inv H. inv MEM. inv SPLIT. inv TS12. }
        * guardH o. des. subst. i. inv GET1.
          exploit split_get0; try exact PROMISES; eauto. i. des.
          exploit DISJOINT0; try exact GET0; eauto. i. des.
          splits.
          { eapply Interval.le_disjoint; eauto. econs; [|refl].
            left. inv MEM. inv SPLIT. auto.
          }
          { ii. inv H. inv MEM. inv SPLIT. inv TS23. }
        * i. eapply DISJOINT0; eauto.
      + ii. erewrite split_o; eauto. repeat condtac; ss; eauto.
        * des. subst. exfalso. inv DISJOINT. exploit DISJOINT0; eauto.
          { hexploit split_get0; try exact PROMISES; eauto. i. des. eauto. }
          i. des. eapply x.
          { inv MEM. inv SPLIT. econs. eauto. left. auto. }
          { apply Interval.mem_ub.
            destruct (mem1 loc).(Cell.WF). exploit VOLUME; eauto. i. des; auto.
            inv x1. inv MEM. inv SPLIT. inv TS12.
          }
        * guardH o. des. subst. exfalso. inv DISJOINT. exploit DISJOINT0; eauto.
          { hexploit split_get0; try exact PROMISES; eauto. i. des. eauto. }
          i. des. eapply x.
          { apply Interval.mem_ub. inv MEM. inv SPLIT. etrans; eauto. }
          { apply Interval.mem_ub.
            destruct (ctx loc).(Cell.WF). exploit VOLUME; eauto. i. des; auto.
            inv x1. inv MEM. inv SPLIT. inv TS23.
          }
    - splits.
      + inv DISJOINT. econs. i. revert GET1. erewrite lower_o; eauto. condtac; ss.
        * des. subst. i. inv GET1. eapply DISJOINT0; eauto.
          hexploit lower_get0; try eapply PROMISES; eauto. i. des. eauto.
        * i. eapply DISJOINT0; eauto.
      + ii. erewrite lower_o; eauto. condtac; ss; eauto.
        des. subst. exfalso. eapply disjoint_get; eauto.
        hexploit lower_get0; try exact PROMISES; eauto. i. des. eauto.
  Qed.

  Lemma remove_future
        promises1 mem1 loc from to msg promises2
        (REMOVE: remove promises1 loc from to msg promises2)
        (LE: le promises1 mem1)
        (FINITE: finite promises1):
    <<LE: le promises2 mem1>> /\
    <<FINITE: finite promises2>>.
  Proof.
    splits.
    - ii. revert LHS. erewrite remove_o; eauto. condtac; ss. eauto.
    - eapply remove_finite; eauto.
  Qed.

  Lemma remove_disjoint
        promises1 mem1 loc from to msg promises2 ctx
        (REMOVE: remove promises1 loc from to msg promises2)
        (LE: le promises1 mem1)
        (LE_CTX: le ctx mem1)
        (DISJOINT: disjoint promises1 ctx):
    <<DISJOINT: disjoint promises2 ctx>>.
  Proof.
    econs. i. revert GET1. erewrite remove_o; eauto. condtac; ss.
    i. eapply DISJOINT; eauto.
  Qed.

  Lemma write_get2
        promises1 mem1 loc from to val released promises2 mem2 kind
        (WRITE: write promises1 mem1 loc from to val released promises2 mem2 kind)
        (MEM: inhabited mem1)
        (FINITE: finite promises1)
        (LE: le promises1 mem1):
    <<GET_PROMISE: get loc to promises2 = None>> /\
    <<GET_MEM: get loc to mem2 = Some (from, Message.full val released)>>.
  Proof.
    inv WRITE. splits.
    - erewrite remove_o; eauto. condtac; ss. des; ss.
    - exploit promise_future0; try apply PROMISE; eauto. i. des.
      eapply promise_get2; eauto.
  Qed.

  Lemma write_future0
        promises1 mem1 loc from to val released promises2 mem2 kind
        (LE_PROMISES1: le promises1 mem1)
        (FINITE1: finite promises1)
        (INHABITED1: inhabited mem1)
        (PROMISE: write promises1 mem1 loc from to val released promises2 mem2 kind):
    <<LE_PROMISES2: le promises2 mem2>> /\
    <<FINITE2: finite promises2>> /\
    <<INHABITED2: inhabited mem2>>.
  Proof.
    inv PROMISE.
    hexploit promise_future0; eauto. i. des.
    hexploit remove_future; eauto. i. des.
    splits; ss.
  Qed.

  Lemma write_future
        promises1 mem1 loc from to val released promises2 mem2 kind
        (WRITE: write promises1 mem1 loc from to val released promises2 mem2 kind)
        (CLOSED: closed mem1)
        (HALF_WF: half_wf mem1)
        (FINITE: finite promises1)
        (MSG_CLOSED: closed_message (Message.full val released) mem2)
        (LE: le promises1 mem1):
    <<CLOSED: closed mem2>> /\
    <<HALF_WF: half_wf mem2>> /\
    <<FINITE: finite promises2>> /\
    <<LE: le promises2 mem2>> /\
    <<FUTURE: future mem1 mem2>>.
  Proof.
    inv WRITE.
    hexploit promise_future; eauto. i. des.
    hexploit remove_future; eauto. i. des.
    splits; ss.
  Qed.

  Lemma write_disjoint
        promises1 mem1 loc from to val released promises2 mem2 ctx kind
        (WRITE: write promises1 mem1 loc from to val released promises2 mem2 kind)
        (CLOSED: closed mem1)
        (FINITE: finite promises1)
        (DISJOINT: disjoint promises1 ctx)
        (LE: le promises1 mem1)
        (LE_CTX: le ctx mem1):
    <<DISJOINT: disjoint promises2 ctx>> /\
    <<LE_CTX: le ctx mem2>>.
  Proof.
    inv WRITE.
    hexploit promise_future0; try apply PROMISE; try apply CLOSED; eauto. i. des.
    hexploit remove_future; try apply REMOVE; eauto. i. des.
    hexploit promise_disjoint; try apply PROMISE; eauto. i. des.
    hexploit remove_disjoint; try apply REMOVE; eauto.
  Qed.


  (* Lemmas on max_timemap *)

  Definition max_ts (loc:Loc.t) (mem:t): Time.t :=
    Cell.max_ts (mem loc).

  Lemma max_ts_spec
        loc ts from msg mem
        (GET: get loc ts mem = Some (from, msg)):
    <<GET: exists from msg, get loc (max_ts loc mem) mem = Some (from, msg)>> /\
    <<MAX: Time.le ts (max_ts loc mem)>>.
  Proof. eapply Cell.max_ts_spec; eauto. Qed.

  Lemma max_ts_spec2
        tm mem loc
        (CLOSED: closed_timemap tm mem):
    Time.le (tm loc) (max_ts loc mem).
  Proof.
    exploit CLOSED. i. des.
    eapply max_ts_spec. eauto.
  Qed.

  Definition max_timemap (mem:t): TimeMap.t :=
    fun loc => max_ts loc mem.

  Lemma max_timemap_spec tm mem
        (TIMEMAP: closed_timemap tm mem)
        (INHABITED: inhabited mem):
    TimeMap.le tm (max_timemap mem).
  Proof.
    ii. specialize (INHABITED loc). des.
    exploit TIMEMAP. i. des.
    eapply max_ts_spec; eauto.
  Qed.

  Lemma max_timemap_spec' tm mem
        (TIMEMAP: forall loc, exists from to val released, Time.le (tm loc) to /\ get loc to mem = Some (from, Message.full val released))
        (INHABITED: inhabited mem):
    TimeMap.le tm (max_timemap mem).
  Proof.
    ii. exploit TIMEMAP; eauto. i. des.
    etrans; eauto. eapply max_ts_spec; eauto.
  Qed.

  Definition max_view (mem:t): View.t :=
    View.mk (max_timemap mem) (max_timemap mem).

  Lemma max_view_wf mem: View.wf (max_view mem).
  Proof. econs. refl. Qed.

  Lemma max_view_spec tm mem
        (VIEW: closed_view tm mem)
        (INHABITED: inhabited mem):
    View.le tm (max_view mem).
  Proof.
    econs; apply max_timemap_spec; try apply VIEW; auto.
  Qed.

  Lemma closed_timemap_add
        loc from to val released mem tm
        (GET: get loc to mem = Some (from, Message.full val released))
        (CLOSED: closed_timemap tm mem):
    closed_timemap (TimeMap.add loc to tm) mem.
  Proof.
    ii. unfold TimeMap.add. condtac.
    - subst. esplits; eauto.
    - apply CLOSED.
  Qed.


  (* Lemmas on max_full_timemap *)

  Definition max_full_ts (mem: t) (loc: Loc.t) (ts: Time.t): Prop :=
    Cell.max_full_ts (mem loc) ts.

  Lemma max_full_ts_exists
        mem loc
        (INHABITED: inhabited mem):
    exists ts, max_full_ts mem loc ts.
  Proof.
    eapply Cell.max_full_ts_exists. apply INHABITED.
  Qed.

  Lemma max_full_ts_inj
        mem loc ts1 ts2
        (MAX1: max_full_ts mem loc ts1)
        (MAX2: max_full_ts mem loc ts2):
    ts1 = ts2.
  Proof.
    eapply Cell.max_full_ts_inj; eauto.
  Qed.

  Lemma max_full_ts_spec
        loc ts from val released mem mts
        (MAX: max_full_ts mem loc mts)
        (GET: get loc ts mem = Some (from, Message.full val released)):
    <<GET: exists from val' released', get loc mts mem = Some (from, Message.full val' released')>> /\
    <<MAX: Time.le ts mts>>.
  Proof.
    eapply Cell.max_full_ts_spec; eauto.
  Qed.

  Lemma max_full_ts_spec2
        tm mem loc mts
        (MAX: max_full_ts mem loc mts)
        (CLOSED: closed_timemap tm mem):
    Time.le (tm loc) mts.
  Proof.
    exploit CLOSED. i. des.
    eapply max_full_ts_spec; eauto.
  Qed.

  Definition max_full_timemap (mem: t) (tm: TimeMap.t): Prop :=
    forall loc, max_full_ts mem loc (tm loc).

  Lemma max_full_timemap_exists
        mem
        (INHABITED: inhabited mem):
    exists tm, max_full_timemap mem tm.
  Proof.
    apply choice. i. apply max_full_ts_exists. auto.
  Qed.

  Lemma max_full_timemap_inj
        mem tm1 tm2
        (MAX1: max_full_timemap mem tm1)
        (MAX2: max_full_timemap mem tm2):
    tm1 = tm2.
  Proof.
    extensionality l.
    specialize (MAX1 l). specialize (MAX2 l).
    eapply max_full_ts_inj; eauto.
  Qed.

  Lemma max_full_timemap_closed
        mem tm
        (MAX: max_full_timemap mem tm):
    closed_timemap tm mem.
  Proof.
    ii. specialize (MAX loc). inv MAX. des.
    esplits; eauto.
  Qed.

  Lemma max_full_timemap_spec
        tm mem mtm
        (MAX: max_full_timemap mem mtm)
        (TIMEMAP: closed_timemap tm mem):
    TimeMap.le tm mtm.
  Proof.
    ii. specialize (MAX loc). specialize (TIMEMAP loc).
    des. eapply max_full_ts_spec; eauto.
  Qed.

  Lemma max_full_timemap_spec'
        tm mem mtm
        (MAX: max_full_timemap mem mtm)
        (TIMEMAP: forall loc, exists from to val released, Time.le (tm loc) to /\ get loc to mem = Some (from, Message.full val released)):
    TimeMap.le tm mtm.
  Proof.
    ii. specialize (TIMEMAP loc). specialize (MAX loc). des.
    exploit max_full_ts_spec; eauto. i. des.
    etrans; eauto.
  Qed.

  Lemma future_max_full_timemap
        mem1 mem2 mtm1 mtm2
        (FUTURE: future mem1 mem2)
        (CLOSED1: closed mem1)
        (CLOSED2: closed mem2)
        (MAX1: max_full_timemap mem1 mtm1)
        (MAX2: max_full_timemap mem2 mtm2):
    TimeMap.le mtm1 mtm2.
  Proof.
    eapply max_full_timemap_spec'; eauto.
    i. exploit max_full_timemap_closed; try eapply MAX1. i. des.
    exploit future_get1; eauto. i. des.
    inv MSG_LE. esplits; try refl; eauto.
  Qed.

  Inductive max_full_view (mem: t): forall (view: View.t), Prop :=
  | max_full_view_intro
      tm
      (MAX: max_full_timemap mem tm):
      max_full_view mem (View.mk tm tm)
  .
  Hint Constructors max_full_view.

  Lemma max_full_view_exists
        mem
        (INHABITED: inhabited mem):
    exists view, max_full_view mem view.
  Proof.
    exploit max_full_timemap_exists; eauto. i. des.
    esplits. econs; eauto.
  Qed.

  Lemma max_full_view_inj
        mem view1 view2
        (MAX1: max_full_view mem view1)
        (MAX2: max_full_view mem view2):
    view1 = view2.
  Proof.
    inv MAX1. inv MAX2.
    exploit max_full_timemap_inj; [exact MAX|exact MAX0|..].
    i. subst. refl.
  Qed.

  Lemma max_full_view_wf
        mem view
        (MAX: max_full_view mem view):
    View.wf view.
  Proof.
    inv MAX. econs. refl.
  Qed.

  Lemma max_full_view_closed
        mem view
        (MAX: max_full_view mem view):
    closed_view view mem.
  Proof.
    inv MAX. econs; apply max_full_timemap_closed; auto.
  Qed.

  Lemma max_full_view_spec
        view mem mview
        (MAX: max_full_view mem mview)
        (VIEW: closed_view view mem):
    View.le view mview.
  Proof.
    inv MAX. inv VIEW.
    econs; eapply max_full_timemap_spec; eauto.
  Qed.

  Lemma add_max_full_timemap
        mem1 mem2 loc from to val released tm1 tm2
        (ADD: add mem1 loc from to (Message.full val released) mem2)
        (MAX1: max_full_timemap mem1 tm1)
        (MAX2: max_full_timemap mem2 tm2):
    tm2 = TimeMap.join tm1 (TimeMap.singleton loc to).
  Proof.
    extensionality l. apply TimeFacts.antisym; auto.
    - exploit max_full_timemap_closed; eauto. instantiate (1 := l). i. des.
      revert x0. erewrite add_o; eauto. condtac; ss.
      + des. subst. i. inv x0. etrans; [|apply TimeMap.join_r].
        apply TimeMap.singleton_inv. refl.
      + i. etrans; [|apply TimeMap.join_l].
        eapply max_full_ts_spec; eauto.
    - apply TimeMap.join_spec.
      + eapply max_full_timemap_spec; eauto.
        eapply add_closed_timemap; eauto.
        apply max_full_timemap_closed. auto.
      + apply TimeMap.singleton_spec.
        eapply max_full_ts_spec; eauto.
        erewrite add_o; eauto. condtac; ss. des; congr.
  Qed.

  Lemma split_max_full_timemap
        mem1 mem2 loc ts1 ts2 ts3 val released msg3 tm1 tm2
        (SPLIT: split mem1 loc ts1 ts2 ts3 (Message.full val released) msg3 mem2)
        (MAX1: max_full_timemap mem1 tm1)
        (MAX2: max_full_timemap mem2 tm2):
    tm2 = TimeMap.join tm1 (TimeMap.singleton loc ts2).
  Proof.
    extensionality l. apply TimeFacts.antisym; auto.
    - exploit max_full_timemap_closed; eauto. instantiate (1 := l). i. des.
      revert x0. erewrite split_o; eauto. repeat condtac; ss.
      + des. subst. i. inv x0. etrans; [|apply TimeMap.join_r].
        apply TimeMap.singleton_inv. refl.
      + guardH o. des. subst. i. inv x0. etrans; [|apply TimeMap.join_l].
        inv SPLIT. inv SPLIT0.
        eapply max_full_ts_spec; eauto.
      + i. etrans; [|apply TimeMap.join_l].
        eapply max_full_ts_spec; eauto.
    - apply TimeMap.join_spec.
      + eapply max_full_timemap_spec; eauto.
        eapply split_closed_timemap; eauto.
        apply max_full_timemap_closed. auto.
      + apply TimeMap.singleton_spec.
        eapply max_full_ts_spec; eauto.
        erewrite split_o; eauto. repeat condtac; ss.
        * guardH o. des. subst. congr.
        * des; congr.
  Qed.

  Lemma lower_max_full_timemap
        mem1 mem2 loc from to msg0 val released tm1 tm2
        (lower: lower mem1 loc from to msg0 (Message.full val released) mem2)
        (MAX1: max_full_timemap mem1 tm1)
        (MAX2: max_full_timemap mem2 tm2):
    tm2 = TimeMap.join tm1 (TimeMap.singleton loc to).
  Proof.
    extensionality l. apply TimeFacts.antisym; auto.
    - exploit max_full_timemap_closed; eauto. instantiate (1 := l). i. des.
      revert x0. erewrite lower_o; eauto. condtac; ss.
      + des. subst. i. inv x0. etrans; [|apply TimeMap.join_r].
        apply TimeMap.singleton_inv. refl.
      + i. etrans; [|apply TimeMap.join_l].
        eapply max_full_ts_spec; eauto.
    - apply TimeMap.join_spec.
      + eapply max_full_timemap_spec; eauto.
        eapply lower_closed_timemap; eauto.
        apply max_full_timemap_closed. auto.
      + apply TimeMap.singleton_spec.
        eapply max_full_ts_spec; eauto.
        erewrite lower_o; eauto. condtac; ss. des; congr.
  Qed.

  Lemma add_max_full_view
        mem1 mem2 loc from to val released mview1 mview2
        (ADD: add mem1 loc from to (Message.full val released) mem2)
        (MAX1: max_full_view mem1 mview1)
        (MAX2: max_full_view mem2 mview2):
    mview2 = View.join mview1 (View.singleton_ur loc to).
  Proof.
    inv MAX1. inv MAX2. apply View.ext; s.
    - eapply add_max_full_timemap; eauto.
    - eapply add_max_full_timemap; eauto.
  Qed.

  Lemma split_max_full_view
        mem1 mem2 loc ts1 ts2 ts3 val released msg3 mview1 mview2
        (SPLIT: split mem1 loc ts1 ts2 ts3 (Message.full val released) msg3 mem2)
        (MAX1: max_full_view mem1 mview1)
        (MAX2: max_full_view mem2 mview2):
    mview2 = View.join mview1 (View.singleton_ur loc ts2).
  Proof.
    inv MAX1. inv MAX2. apply View.ext; s.
    - eapply split_max_full_timemap; eauto.
    - eapply split_max_full_timemap; eauto.
  Qed.

  Lemma lower_max_full_view
        mem1 mem2 loc from to msg0 val released mview1 mview2
        (LOWER: lower mem1 loc from to msg0 (Message.full val released) mem2)
        (MAX1: max_full_view mem1 mview1)
        (MAX2: max_full_view mem2 mview2):
    mview2 = View.join mview1 (View.singleton_ur loc to).
  Proof.
    inv MAX1. inv MAX2. apply View.ext; s.
    - eapply lower_max_full_timemap; eauto.
    - eapply lower_max_full_timemap; eauto.
  Qed.

  Inductive max_full_released (mem: t) (loc: Loc.t) (ts: Time.t): forall (released: View.t), Prop :=
  | max_full_released_intro
      tm rlx
      (MAX: max_full_timemap mem tm)
      (RLX: rlx = TimeMap.add loc ts tm):
      max_full_released mem loc ts (View.mk rlx rlx)
  .
  Hint Constructors max_full_released.

  Lemma max_full_released_exists
        mem loc ts
        (INHABITED: inhabited mem):
    exists released, max_full_released mem loc ts released.
  Proof.
    exploit max_full_timemap_exists; eauto. i. des.
    esplits. econs; eauto.
  Qed.

  Lemma max_full_released_inj
        mem loc ts released1 released2
        (MAX1: max_full_released mem loc ts released1)
        (MAX2: max_full_released mem loc ts released2):
    released1 = released2.
  Proof.
    inv MAX1. inv MAX2.
    exploit max_full_timemap_inj; [exact MAX|exact MAX0|..].
    i. subst. refl.
  Qed.

  Lemma max_full_released_wf
        mem loc ts released
        (MAX: max_full_released mem loc ts released):
    View.wf released.
  Proof.
    inv MAX. econs. refl.
  Qed.

  Lemma max_full_released_closed_add
        mem1 loc from to val released mem2 mr
        (ADD: add mem1 loc from to (Message.full val released) mem2)
        (CLOSED: closed mem1)
        (MAX: max_full_released mem1 loc to mr):
    <<CLOSED: closed_view mr mem2>> /\
    <<REL_TS: Time.le (mr.(View.rlx) loc) to>>.
  Proof.
    splits.
    - inv MAX.
      hexploit add_inhabited; try apply CLOSED; eauto. i. des.
      cut (closed_timemap (TimeMap.add loc to tm) mem2).
      { i. econs; ss. }
      eapply closed_timemap_add.
      + erewrite add_o; eauto. condtac; ss. des; congr.
      + eapply add_closed_timemap; eauto.
        eapply max_full_timemap_closed. auto.
    - inv MAX. ss. unfold TimeMap.add. condtac; [|congr]. refl.
  Qed.

  Lemma max_full_released_spec_add
        mem1 loc from to val released mem2 mr
        (CLOSED: closed mem1)
        (ADD: add mem1 loc from to (Message.full val released) mem2)
        (REL_CLOSED: closed_opt_view released mem2)
        (REL_TS: Time.le (released.(View.unwrap).(View.rlx) loc) to)
        (MAX: max_full_released mem1 loc to mr):
    View.opt_le released (Some mr).
  Proof.
    inv REL_CLOSED; econs.
    hexploit add_inhabited; try apply CLOSED; eauto. i. des.
    exploit max_full_view_exists; eauto. i. des.
    exploit max_full_view_spec; eauto. i.
    inv MAX. erewrite add_max_full_view in x1; eauto. ss.
    inv x1. econs; ss.
    - ii. unfold TimeMap.add. condtac.
      + subst. etrans; [|exact REL_TS].
        inv ADD. inv ADD0. inv MSG_WF. inv WF. apply WF0.
      + etrans; [apply PLN|]. apply Time.join_spec; [refl|].
        unfold TimeMap.singleton, LocFun.add. condtac; ss. apply Time.bot_spec.
    - ii. unfold TimeMap.add. condtac.
      + subst. ss.
      + etrans; [apply RLX|]. apply Time.join_spec; [refl|].
        unfold TimeMap.singleton, LocFun.add. condtac; ss. apply Time.bot_spec.
  Qed.

  Lemma max_full_released_closed_split
        mem1 loc ts1 ts2 ts3 val released msg3 mem2 mr
        (SPLIT: split mem1 loc ts1 ts2 ts3 (Message.full val released) msg3 mem2)
        (CLOSED: closed mem1)
        (MAX: max_full_released mem1 loc ts2 mr):
    <<CLOSED: closed_view mr mem2>> /\
    <<REL_TS: Time.le (mr.(View.rlx) loc) ts2>>.
  Proof.
    splits.
    - inv MAX.
      hexploit split_inhabited; try apply CLOSED; eauto. i. des.
      cut (closed_timemap (TimeMap.add loc ts2 tm) mem2).
      { i. econs; ss. }
      eapply closed_timemap_add.
      + erewrite split_o; eauto. condtac; ss. des; congr.
      + eapply split_closed_timemap; eauto.
        eapply max_full_timemap_closed. auto.
    - inv MAX. ss. unfold TimeMap.add. condtac; [|congr]. refl.
  Qed.

  Lemma max_full_released_spec_split
        mem1 loc ts1 ts2 ts3 val released msg3 mem2 mr
        (CLOSED: closed mem1)
        (SPLIT: split mem1 loc ts1 ts2 ts3 (Message.full val released) msg3 mem2)
        (REL_CLOSED: closed_opt_view released mem2)
        (REL_TS: Time.le (released.(View.unwrap).(View.rlx) loc) ts2)
        (MAX: max_full_released mem1 loc ts2 mr):
    View.opt_le released (Some mr).
  Proof.
    inv REL_CLOSED; econs.
    hexploit split_inhabited; try apply CLOSED; eauto. i. des.
    exploit max_full_view_exists; eauto. i. des.
    exploit max_full_view_spec; eauto. i.
    inv MAX. erewrite split_max_full_view in x1; eauto. ss.
    inv x1. econs; ss.
    - ii. unfold TimeMap.add. condtac.
      + subst. etrans; [|exact REL_TS].
        inv SPLIT. inv SPLIT0. inv MSG_WF. inv WF. apply WF0.
      + etrans; [apply PLN|]. apply Time.join_spec; [refl|].
        unfold TimeMap.singleton, LocFun.add. condtac; ss. apply Time.bot_spec.
    - ii. unfold TimeMap.add. condtac.
      + subst. ss.
      + etrans; [apply RLX|]. apply Time.join_spec; [refl|].
        unfold TimeMap.singleton, LocFun.add. condtac; ss. apply Time.bot_spec.
  Qed.

  Lemma max_full_released_closed_lower
        mem1 loc from to msg0 val released mem2 mr
        (LOWER: lower mem1 loc from to msg0 (Message.full val released) mem2)
        (CLOSED: closed mem1)
        (MAX: max_full_released mem1 loc to mr):
    <<CLOSED: closed_view mr mem2>> /\
    <<REL_TS: Time.le (mr.(View.rlx) loc) to>>.
  Proof.
    splits.
    - inv MAX.
      hexploit lower_inhabited; try apply CLOSED; eauto. i. des.
      cut (closed_timemap (TimeMap.add loc to tm) mem2).
      { i. econs; ss. }
      eapply closed_timemap_add.
      + erewrite lower_o; eauto. condtac; ss. des; congr.
      + eapply lower_closed_timemap; eauto.
        eapply max_full_timemap_closed. auto.
    - inv MAX. ss. unfold TimeMap.add. condtac; [|congr]. refl.
  Qed.

  Lemma max_full_released_spec_lower
        mem1 loc from to msg0 val released mem2 mr
        (CLOSED: closed mem1)
        (LOWER: lower mem1 loc from to msg0 (Message.full val released) mem2)
        (REL_CLOSED: closed_opt_view released mem2)
        (REL_TS: Time.le (released.(View.unwrap).(View.rlx) loc) to)
        (MAX: max_full_released mem1 loc to mr):
    View.opt_le released (Some mr).
  Proof.
    inv REL_CLOSED; econs.
    hexploit lower_inhabited; try apply CLOSED; eauto. i. des.
    exploit max_full_view_exists; eauto. i. des.
    exploit max_full_view_spec; eauto. i.
    inv MAX. erewrite lower_max_full_view in x1; eauto. ss.
    inv x1. econs; ss.
    - ii. unfold TimeMap.add. condtac.
      + subst. etrans; [|exact REL_TS].
        inv LOWER. inv LOWER0. inv MSG_WF. inv WF. apply WF0.
      + etrans; [apply PLN|]. apply Time.join_spec; [refl|].
        unfold TimeMap.singleton, LocFun.add. condtac; ss. apply Time.bot_spec.
    - ii. unfold TimeMap.add. condtac.
      + subst. ss.
      + etrans; [apply RLX|]. apply Time.join_spec; [refl|].
        unfold TimeMap.singleton, LocFun.add. condtac; ss. apply Time.bot_spec.
  Qed.


  (* Lemmas on existence of memory op *)

  Lemma add_exists
        mem1 loc from to msg
        (DISJOINT: forall to2 from2 msg2
                     (GET2: get loc to2 mem1 = Some (from2, msg2)),
            Interval.disjoint (from, to) (from2, to2))
        (TO1: Time.lt from to)
        (MSG_WF: Message.wf msg):
    exists mem2, add mem1 loc from to msg mem2.
  Proof.
    exploit Cell.add_exists; eauto. i. des.
    eexists. econs; eauto.
  Qed.

  Lemma add_exists_max_ts
        mem1 loc to msg
        (TS: Time.lt (max_ts loc mem1) to)
        (MSG_WF: Message.wf msg):
    exists mem2,
      add mem1 loc (max_ts loc mem1) to msg mem2.
  Proof.
    eapply add_exists; eauto.
    i. exploit max_ts_spec; eauto. i. des.
    ii. inv LHS. inv RHS. ss.
    rewrite MAX in TO0. eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt; eauto.
  Qed.

  Lemma add_exists_le
        promises1 mem1 loc from to msg mem2
        (LE: le promises1 mem1)
        (ADD: add mem1 loc from to msg mem2):
    exists promises2, add promises1 loc from to msg promises2.
  Proof.
    inv ADD.
    exploit Cell.add_exists_le; eauto.
    { ii. eapply LE. eauto. }
    i. des.
    eexists. econs; eauto.
  Qed.

  (* unused *)
  (* Lemma promise_add_exists *)
  (*       promises1 mem1 loc from to msg mem2 *)
  (*       (LE_PROMISES1: le promises1 mem1) *)
  (*       (ADD: add mem1 loc from to msg mem2) *)
  (*       (MSG_CLOSED: closed_message msg mem2) *)
  (*       (MSG_TS: message_to msg loc to): *)
  (*   exists promises2, *)
  (*     promise promises1 mem1 loc from to msg promises2 mem2 op_kind_add. *)
  (* Proof. *)
  (*   exploit add_exists_le; eauto. i. des. *)
  (*   eexists. econs 1; s; eauto. *)
  (* Qed. *)

  Lemma split_exists
        mem1 loc ts1 ts2 ts3 msg2 msg3
        (GET2: get loc ts3 mem1 = Some (ts1, msg3))
        (TS12: Time.lt ts1 ts2)
        (TS23: Time.lt ts2 ts3)
        (MSG_WF: Message.wf msg2):
    exists mem2, split mem1 loc ts1 ts2 ts3 msg2 msg3 mem2.
  Proof.
    exploit Cell.split_exists; eauto. i. des.
    eexists. econs; eauto.
  Qed.

  Lemma split_exists_le
        promises1 mem1 loc ts1 ts2 ts3 msg2 msg3 promises2
        (LE: le promises1 mem1)
        (SPLIT: split promises1 loc ts1 ts2 ts3 msg2 msg3 promises2):
    exists mem2, split mem1 loc ts1 ts2 ts3 msg2 msg3 mem2.
  Proof.
    inv SPLIT.
    exploit Cell.split_exists_le; eauto.
    { ii. eapply LE. eauto. }
    i. des.
    eexists. econs; eauto.
  Qed.

  Lemma lower_exists
        mem1 loc from to msg1 msg2
        (GET: get loc to mem1 = Some (from, msg1))
        (TS: Time.lt from to)
        (MSG_WF: Message.wf msg2)
        (MSG_LE: Message.le msg2 msg1):
    exists mem2, lower mem1 loc from to msg1 msg2 mem2.
  Proof.
    exploit Cell.lower_exists; eauto. i. des.
    eexists. econs; eauto.
  Qed.

  Lemma lower_exists_le
        promises1 mem1 loc from to msg1 msg2 promises2
        (LE: le promises1 mem1)
        (LOWER: lower promises1 loc from to msg1 msg2 promises2):
    exists mem2, lower mem1 loc from to msg1 msg2 mem2.
  Proof.
    inv LOWER.
    exploit Cell.lower_exists_le; eauto.
    { ii. eapply LE. eauto. }
    i. des.
    eexists. econs; eauto.
  Qed.

  Lemma lower_exists_same
        mem1 loc from to msg
        (GET: get loc to mem1 = Some (from, msg))
        (TS: Time.lt from to)
        (MSG_WF: Message.wf msg):
    lower mem1 loc from to msg msg mem1.
  Proof.
    exploit lower_exists; eauto; try refl. i. des.
    cut (mem2 = mem1).
    { i. subst. auto. }
    apply ext. i.
    erewrite lower_o; eauto. condtac; ss. des. subst. auto.
  Qed.

  Lemma promise_exists_same
        promises1 mem1 loc from to msg
        (MSG_WF: Message.wf msg)
        (LE: le promises1 mem1)
        (MEM: closed mem1)
        (GET: get loc to promises1 = Some (from, msg))
        (LT: Time.lt from to):
    promise promises1 mem1 loc from to msg promises1 mem1 (op_kind_lower msg).
  Proof.
    exploit lower_exists_same; eauto. i.
    exploit lower_exists_same; try apply LE; eauto. i.
    econs; eauto.
    eapply MEM. eauto.
  Qed.

  Lemma remove_singleton
        loc from to msg
        (LT: Time.lt from to)
        (MSG_WF: Message.wf msg):
    remove (singleton loc LT MSG_WF) loc from to msg bot.
  Proof.
    assert (bot = LocFun.add loc Cell.bot (singleton loc LT MSG_WF)).
    { apply ext. i. rewrite bot_get.
      unfold get, LocFun.add, LocFun.find. condtac.
      - rewrite Cell.bot_get. auto.
      - unfold singleton, LocFun.add, LocFun.find. condtac; [congr|].
        rewrite Cell.bot_get. auto.
    }
    rewrite H. econs; ss.
    unfold singleton, LocFun.add, LocFun.find. condtac; [|congr].
    eapply Cell.remove_singleton.
  Qed.

  Lemma add_inj
        mem loc to from msg mem1 mem2
        (REMOVE1: Memory.add mem loc from to msg mem1)
        (REMOVE2: Memory.add mem loc from to msg mem2):
    mem1 = mem2.
  Proof.
    apply Memory.ext. i.
    setoid_rewrite Memory.add_o; eauto.
  Qed.

  Lemma split_inj
        mem loc to to' from msg1 msg2 mem1 mem2
        (REMOVE1: Memory.split mem loc from to to' msg1 msg2 mem1)
        (REMOVE2: Memory.split mem loc from to to' msg1 msg2 mem2):
    mem1 = mem2.
  Proof.
    apply Memory.ext. i.
    setoid_rewrite Memory.split_o; eauto.
  Qed.

  Lemma lower_inj
        mem loc to from msg1 msg2 mem1 mem2
        (LOWER1: Memory.lower mem loc from to msg1 msg2 mem1)
        (LOWER2: Memory.lower mem loc from to msg1 msg2 mem2):
    mem1 = mem2.
  Proof.
    apply Memory.ext. i.
    setoid_rewrite Memory.lower_o; eauto.
  Qed.

  Lemma remove_inj
        mem loc to from1 from2 msg1 msg2 mem1 mem2
        (REMOVE1: Memory.remove mem loc from1 to msg1 mem1)
        (REMOVE2: Memory.remove mem loc from2 to msg2 mem2):
    mem1 = mem2.
  Proof.
    apply Memory.ext. i.
    setoid_rewrite Memory.remove_o; eauto.
  Qed.

  Lemma split_remove_eq
        mem loc ts1 ts2 ts3
        mem2 mem3 msg1 msg2
        mem'2 mem'3 msg'1 msg'2
        (SPLIT : Memory.split mem loc ts1 ts2 ts3 msg1 msg2 mem2)
        (REMOVE: Memory.remove mem2 loc ts1 ts2 msg1 mem3)
        (SPLIT' : Memory.split mem loc ts1 ts2 ts3 msg'1 msg'2 mem'2)
        (REMOVE': Memory.remove mem'2 loc ts1 ts2 msg'1 mem'3):
    mem3 = mem'3.
  Proof.
    apply Memory.ext. i.
    setoid_rewrite Memory.remove_o; cycle 1; eauto.
    condtac; eauto. guardH o.
    setoid_rewrite Memory.split_o; cycle 1; eauto.
    repeat condtac; subst; ss; eauto. guardH o0.
    des. subst.

    exploit Memory.split_get0; try exact SPLIT; eauto. i. des.
    exploit Memory.split_get0; try exact SPLIT'; eauto. i. des.
    rewrite GET0 in GET4. inv GET4. ss.
  Qed.

  Lemma remove_exists
        mem1 loc from to msg
        (GET: get loc to mem1 = Some (from, msg)):
    exists mem2, remove mem1 loc from to msg mem2.
  Proof.
    exploit Cell.remove_exists; eauto. i. des.
    eexists. econs; ss. eauto.
  Qed.

  Definition nonsynch_loc (loc:Loc.t) (mem:t): Prop :=
    forall f t msg (GET: get loc t mem = Some (f, msg)),
      match msg with
      | Message.full _ rel => rel = None
      | Message.half => True
      end.

  Definition nonsynch (mem:t): Prop :=
    forall loc, nonsynch_loc loc mem.

  Lemma bot_nonsynch_loc loc: nonsynch_loc loc Memory.bot.
  Proof. ii. rewrite bot_get in *. congr. Qed.

  Lemma bot_nonsynch: nonsynch Memory.bot.
  Proof. ii. eapply bot_nonsynch_loc. eauto. Qed.


  (* no_half *)

  Definition no_half (promises mem: t): Prop :=
    forall loc to from
      (GET: get loc to mem = Some (from, Message.half)),
      get loc to promises = Some (from, Message.half).

  Lemma no_half_bot_max_ts
        mem loc mts
        (NOHALF: no_half bot mem)
        (MAX: max_full_ts mem loc mts):
    mts = max_ts loc mem.
  Proof.
    inv MAX. des.
    exploit max_ts_spec; eauto. i. des.
    apply TimeFacts.antisym; eauto.
    destruct msg.
    - eapply MAX0; eauto.
    - exploit NOHALF; eauto. i.
      rewrite bot_get in x. inv x.
  Qed.

  Lemma promise_no_half
        promises1 promises2 mem1 mem2
        loc from to msg kind
        (PROMISE: promise promises1 mem1 loc from to msg promises2 mem2 kind)
        (NOHALF1: no_half promises1 mem1):
    no_half promises2 mem2.
  Proof.
    ii. inv PROMISE.
    - erewrite add_o; try exact PROMISES.
      erewrite add_o in GET; try exact MEM.
      condtac; eauto.
    - erewrite split_o; try exact PROMISES.
      erewrite split_o in GET; try exact MEM.
      repeat condtac; eauto.
    - erewrite lower_o; try exact PROMISES.
      erewrite lower_o in GET; try exact MEM.
      condtac; eauto.
  Qed.


  (* concrete *)

  Inductive concrete (mem1 mem2: t): Prop :=
  | concrete_intro
      (SOUND: forall loc from to msg (GET: get loc to mem1 = Some (from, msg)),
          get loc to mem2 = Some (from, msg) \/
          msg = Message.half /\
          exists from' msg1 msg2,
            get loc from mem1 = Some (from', msg1) /\
            get loc to mem2 = Some (from, msg2) /\
            Message.le msg1 msg2)
      (COMPLETE: forall loc from to msg (GET: get loc to mem2 = Some (from, msg)),
          get loc to mem1 = Some (from, msg) \/
          get loc to mem1 = Some (from, Message.half))
  .

  Lemma concrete_closed_timemap
        mem1 mem2 tm
        (CONCRETE: concrete mem1 mem2)
        (CLOSED: closed_timemap tm mem1):
    closed_timemap tm mem2.
  Proof.
    ii. specialize (CLOSED loc). des.
    inv CONCRETE. exploit SOUND; eauto.
    i. des; eauto. inv x.
  Qed.

  Lemma concrete_closed_view
        mem1 mem2 view
        (CONCRETE: concrete mem1 mem2)
        (CLOSED: closed_view view mem1):
    closed_view view mem2.
  Proof.
    inv CLOSED; eauto using concrete_closed_timemap.
  Qed.

  Lemma concrete_closed_opt_view
        mem1 mem2 view
        (CONCRETE: concrete mem1 mem2)
        (CLOSED: closed_opt_view view mem1):
    closed_opt_view view mem2.
  Proof.
    inv CLOSED; eauto using concrete_closed_view.
  Qed.

  Lemma concrete_closed_message
        mem1 mem2 msg
        (CONCRETE: concrete mem1 mem2)
        (CLOSED: closed_message msg mem1):
    closed_message msg mem2.
  Proof.
    inv CLOSED; eauto using concrete_closed_opt_view.
  Qed.

  Lemma concrete_promise_exists
        promises1 mem1 loc from to msg promises2 mem2 kind
        mem1'
        (LE: le promises1 mem1)
        (CLOSED1: closed mem1)
        (PROMISE: promise promises1 mem1 loc from to msg promises2 mem2 kind)
        (CONCRETE1: concrete mem1 mem1')
        (LE': le promises1 mem1'):
    exists mem2',
      <<PROMISE': promise promises1 mem1' loc from to msg promises2 mem2' kind>> /\
      <<CONCRETE2: concrete mem2 mem2'>>.
  Proof.
    inv CONCRETE1. inv PROMISE.
    - exploit add_get0; try exact MEM. i. des.
      exploit get_ts; try exact GET0. i. des.
      { subst. inv CLOSED1. rewrite INHABITED in GET. inv GET. }
      exploit (@add_exists mem1' loc from to msg); eauto.
      { ii. assert (GET3: exists msg, get loc to2 mem1 = Some (from2, msg)).
        { exploit COMPLETE; eauto. i. des; eauto. }
        des. exploit add_o; eauto. erewrite GET3. condtac; ss.
        - des. subst. rewrite GET in GET3. inv GET3.
        - i. des; try congr.
          exploit get_disjoint; [exact GET0|exact x2|..]. i. des; try congr.
          eapply x3; eauto. }
      { inv MEM. inv ADD. ss. }
      i. des.
      exploit add_get0; try exact x1. i. des.
      esplits.
      + econs; eauto.
        i. subst. exploit HALF; eauto. i. des.
        exploit SOUND; eauto. i. des; eauto; congr.
      + econs; i.
        * erewrite add_o; eauto.
          revert GET3. erewrite add_o; try exact MEM.
          condtac; ss; eauto; i.
          guardH o. exploit SOUND; eauto. i. des; eauto.
          subst. right. split; auto.
          erewrite add_o; eauto. condtac; ss.
          { des. subst. exploit SOUND; try exact x2. i. des; congr. }
          { esplits; eauto. }
        * erewrite add_o; eauto.
          revert GET3. erewrite add_o; try exact x1.
          condtac; ss; eauto.
    - exploit split_get0; try exact MEM. i. des.
      exploit get_ts; try exact GET1. i. des.
      { subst. inv CLOSED1. rewrite INHABITED in GET. inv GET. }
      exploit get_ts; try exact GET2. i. des.
      { subst. inv CLOSED1. rewrite INHABITED in GET. inv GET. }
      exploit (@split_exists mem1' loc from to ts3 msg msg3); eauto.
      { exploit split_get0; try exact PROMISES. i. des.
        exploit LE'; try exact GET4. ss. }
      { inv MEM. inv SPLIT. ss. }
      i. des.
      exploit split_get0; try exact x2. i. des.
      esplits.
      + econs; eauto.
        i. subst. exploit HALF1; eauto. i. des.
        exploit SOUND; eauto. i. des; eauto; congr.
      + econs; i.
        * erewrite split_o; eauto.
          revert GET7. erewrite split_o; try exact MEM.
          repeat condtac; ss; eauto; i.
          { guardH o. guardH o0.
            exploit SOUND; eauto. i. des; eauto.
            subst. right. split; auto.
            erewrite split_o; eauto. repeat condtac; ss; eauto.
            - des. subst. exploit SOUND; try exact x3. i. des; congr.
            - guardH o1. des. subst. rewrite GET0 in x3. inv x3.
              esplits; eauto.
            - esplits; eauto. }
        * erewrite split_o; eauto.
          revert GET7. erewrite split_o; try exact x2.
          repeat condtac; ss; eauto.
    - exploit lower_get0; try exact MEM. i. des.
      exploit get_ts; try exact GET. i. des.
      { subst. inv MEM. inv LOWER. inv TS0. }
      exploit (@lower_exists mem1' loc from to msg0 msg); eauto.
      { exploit lower_get0; try exact PROMISES. i. des.
        exploit LE'; try exact GET1. ss. }
      { inv MEM. inv LOWER. ss. }
      i. des.
      exploit lower_get0; try exact x1. i. des.
      esplits.
      + econs; eauto.
      + econs; i.
        * erewrite lower_o; eauto.
          revert GET3. erewrite lower_o; try exact MEM.
          condtac; ss; eauto; i.
          guardH o. exploit SOUND; eauto. i. des; eauto.
          subst. right. split; auto.
          erewrite lower_o; eauto. condtac; ss; eauto.
          { des. subst. rewrite GET in x2. inv x2.
            exploit SOUND; try exact GET. i. des.
            - esplits; eauto. etrans; eauto.
            - subst. inv x4. esplits; eauto. }
          { esplits; eauto. }
        * erewrite lower_o; eauto.
          revert GET3. erewrite lower_o; try exact x1.
          condtac; ss; eauto.
  Qed.


  (* concrete_exact *)

  Inductive concrete_exact (mem1 mem2: t): Prop :=
  | concrete_exact_intro
      (SOUND: forall loc from to msg (GET: get loc to mem1 = Some (from, msg)),
          get loc to mem2 = Some (from, msg) \/
          msg = Message.half /\
          exists from' val' released',
            get loc from mem1 = Some (from', Message.full val' released') /\
            get loc to mem2 = Some (from, Message.full val' released'))
      (COMPLETE: forall loc from to msg (GET: get loc to mem2 = Some (from, msg)),
          get loc to mem1 = Some (from, msg) \/
          get loc to mem1 = Some (from, Message.half))
  .

  Lemma concrete_exact_concrete
        mem mem'
        (CONCRETE: concrete_exact mem mem'):
    concrete mem mem'.
  Proof.
    inv CONCRETE. econs; eauto.
    i. exploit SOUND; eauto. i. des; eauto.
    subst. right. split; auto.
    esplits; eauto. refl.
  Qed.

  Lemma concrete_exact_closed_timemap
        mem mem' tm
        (CONCRETE: concrete_exact mem mem')
        (CLOSED: closed_timemap tm mem):
    closed_timemap tm mem'.
  Proof.
    ii. specialize (CLOSED loc). des.
    inv CONCRETE. exploit SOUND; eauto. i. des; eauto.
  Qed.

  Lemma concrete_exact_closed_view
        mem mem' view
        (CONCRETE: concrete_exact mem mem')
        (CLOSED: closed_view view mem):
    closed_view view mem'.
  Proof.
    inv CLOSED.
    econs; eauto using concrete_exact_closed_timemap.
  Qed.

  Lemma concrete_exact_closed_opt_view
        mem mem' view
        (CONCRETE: concrete_exact mem mem')
        (CLOSED: closed_opt_view view mem):
    closed_opt_view view mem'.
  Proof.
    inv CLOSED; eauto using concrete_exact_closed_view.
  Qed.

  Lemma concrete_exact_closed_message
        mem mem' msg
        (CONCRETE: concrete_exact mem mem')
        (CLOSED: closed_message msg mem):
    closed_message msg mem'.
  Proof.
    inv CLOSED; eauto using concrete_exact_closed_opt_view.
  Qed.

  Lemma concrete_exact_closed
        mem mem'
        (CONCRETE: concrete_exact mem mem')
        (CLOSED: closed mem):
    closed mem'.
  Proof.
    dup CONCRETE. inv CONCRETE0. inv CLOSED.
    econs; i.
    - exploit COMPLETE; eauto. i. des.
      + exploit CLOSED0; eauto. i. des.
        esplits; eauto.
        eapply concrete_exact_closed_message; eauto.
      + exploit SOUND; eauto. i. des.
        * rewrite MSG in x0. inv x0.
          splits; econs; eauto.
        * rewrite MSG in x2. inv x2.
          exploit CLOSED0; try exact x1. i. des.
          splits; eauto.
          { exploit get_ts; try exact x. i. des.
            - subst. rewrite INHABITED in x. inv x.
            - inv MSG_TS. econs. etrans; eauto. econs; eauto. }
          { eapply concrete_exact_closed_message; eauto. }
    - ii. specialize (INHABITED loc).
      exploit SOUND; eauto. i. des; auto. inv x.
    - inv FINITE_HALF. exists x. i.
      exploit COMPLETE; eauto. i. des; eauto.
  Qed.

  Lemma lower_half_concrete_exact
        mem1 loc from to val released mem2
        (MSG: get loc from mem1 = Some (from, Message.full val released))
        (LOWER: lower mem1 loc from to Message.half (Message.full val released) mem2):
    concrete_exact mem1 mem2.
  Proof.
    exploit lower_get0; eauto. i. des.
    econs; i.
    - erewrite lower_o; eauto. condtac; ss.
      + des. subst. rewrite GET in GET1. inv GET1.
        right. esplits; eauto.
      + left. eauto.
    - revert GET1. erewrite lower_o; eauto. condtac; ss; i.
      + des. subst. inv GET1. eauto.
      + left. eauto.
  Qed.

  Lemma no_half_concret_exact_inj
        promises mem mem1 mem2
        (CONCRETE1: concrete_exact mem mem1)
        (CONCRETE2: concrete_exact mem mem2)
        (LE1: le promises mem1)
        (LE2: le promises mem2)
        (NOHALF1: no_half promises mem1)
        (NOHALF2: no_half promises mem2):
    mem1 = mem2.
  Proof.
    apply ext. i.
    inv CONCRETE1. inv CONCRETE2.
    destruct (get loc ts mem1) as [[from msg]|] eqn:GET1.
    - exploit COMPLETE; eauto. i. des.
      + exploit SOUND0; eauto. i. des; auto.
        subst. exploit LE2; eauto.
      + subst. exploit SOUND0; eauto. i. des.
        * exploit NOHALF2; eauto. i.
          exploit LE1; eauto. i.
          rewrite GET1 in x2. inv x2. eauto.
        * exploit SOUND; try exact x. i. des.
          { rewrite GET1 in x3. inv x3.
            exploit NOHALF1; eauto. i.
            exploit LE2; eauto. }
          { rewrite x1 in x4. inv x4.
            rewrite GET1 in x5. inv x5. ss. }
    - destruct (get loc ts mem2) as [[from msg]|] eqn:GET2; ss.
      exploit COMPLETE0; eauto. i. des.
      + exploit SOUND; eauto. i. des; congr.
      + exploit SOUND; eauto. i. des; congr.
  Qed.


  (* existence of concrete and concrete_elt *)

  Lemma le_finite_half_domain
        promises mem
        (LE: le promises mem)
        (CLOSED: closed mem):
    exists dom,
      <<NODUP: List.NoDup dom>> /\
      <<SOUND: forall loc from to
                 (GET: get loc to mem = Some (from, Message.half))
                 (GETP: get loc to promises = None),
        List.In (loc, to) dom>> /\
      <<COMPLETE: forall loc to (IN: List.In (loc, to) dom),
          exists from, get loc to mem = Some (from, Message.half) /\
                  get loc to promises = None>>.
  Proof.
    inv CLOSED. inv FINITE_HALF. clear CLOSED0.
    revert promises mem LE INHABITED H.
    induction x; i.
    { esplits; eauto; try by econs. }
    destruct a as [loc to]. ss.
    destruct (get loc to mem) as [[from [val released|]]|] eqn:GET.
    - eapply IHx; eauto. i. exploit H; eauto. i. des; ss.
      inv x0. rewrite GET in GET0. inv GET0.
    - destruct (get loc to promises) eqn:GETP.
      + destruct p. exploit LE; eauto. i.
        rewrite x0 in GET. inv GET.
        exploit Memory.get_ts; try exact x0. i. des.
        { subst. rewrite INHABITED in x0. inv x0. }
        exploit lower_exists; try exact GETP; eauto.
        { apply Message.elt_wf. }
        i. des.
        exploit lower_exists; try exact GET0; eauto.
        { apply Message.elt_wf. }
        i. des.
        assert (LE2: le mem2 mem0).
        { ii. erewrite lower_o; eauto.
          erewrite lower_o in LHS; try exact x3.
          revert LHS. condtac; ss; eauto. }
        hexploit lower_inhabited; eauto. i. des.
        exploit IHx; try exact LE2; eauto.
        { i. revert GET. erewrite lower_o; eauto. condtac; ss.
          i. exploit H; eauto. i. guardH o. des; eauto.
          inv x1. unguard. des; congr. }
        i. des. exists dom. splits; i.
        * ss.
        * eapply SOUND.
          { erewrite lower_o; eauto. condtac; ss.
            - des. subst. rewrite GETP in GETP0. inv GETP0.
            - rewrite GET. ss. }
          { erewrite lower_o; eauto. condtac; ss.
            des. subst. rewrite GETP in GETP0. inv GETP0. }
        * exploit COMPLETE; eauto. i. des.
          revert x1. erewrite lower_o; eauto. condtac; ss.
          i. esplits; try exact x1.
          erewrite lower_o in x5; eauto. revert x5. condtac; ss.
      + exploit get_ts; try exact GET. i. des.
        { subst. rewrite INHABITED in GET. inv GET. }
        exploit lower_exists; try exact GET; try apply Message.elt_wf; eauto.
        i. des.
        assert (LE2: le promises mem2).
        { ii. erewrite lower_o; eauto. condtac; ss.
          - des. subst. congr.
          - exploit LE; eauto. }
        exploit IHx; try exact LE2; eauto.
        { eapply lower_inhabited; eauto. }
        { i. revert GET0. erewrite lower_o; eauto. condtac; ss.
          i. exploit H; eauto. i. des; congr. }
        i. des.
        exists ((loc, to) :: dom). splits; i.
        * econs; eauto. ii.
          exploit COMPLETE; eauto. i. des.
          exploit lower_get0; eauto. i. des.
          rewrite x0 in GET1. inv GET1.
        * destruct (loc_ts_eq_dec (loc0, to0) (loc, to)); ss.
          { des. subst. auto. }
          right. eapply SOUND; eauto.
          { erewrite lower_o; eauto. condtac; ss.
            - des; subst; congr.
            - rewrite GET0; eauto. }
        * inv IN.
          { inv H0. esplits; eauto. }
          { exploit COMPLETE; eauto. i. des.
            esplits; eauto.
            revert x0. erewrite lower_o; eauto. condtac; ss.
            i. rewrite x0. ss. }
    - eapply IHx; eauto. i. exploit H; eauto. i. des; ss.
      inv x0. subst. congr.
  Grab Existential Variables.
  { inv IN. }
  Qed.

  Lemma no_half_concrete_exact_future_exists
        promises mem1
        (LE1: le promises mem1)
        (CLOSED1: closed mem1):
    exists mem2,
      <<FUTURE: future mem1 mem2>> /\
      <<CONCRETE: concrete_exact mem1 mem2>> /\
      <<NOHALF: no_half promises mem2>> /\
      <<LE2: le promises mem2>> /\
      <<CLOSED2: closed mem2>>.
  Proof.
    exploit le_finite_half_domain; eauto. i. des.
    revert mem1 LE1 CLOSED1 NODUP SOUND COMPLETE.
    induction dom; i.
    { esplits; eauto.
      ii. destruct (get loc to promises) eqn:GETP.
      - destruct p. exploit LE1; eauto. i.
        rewrite GET in x. inv x. ss.
      - exploit SOUND; eauto. i. inv x. }
    destruct a as [loc to]. ss.
    exploit (COMPLETE loc to); eauto. i. des.
    exploit get_ts; try exact x0. i. des.
    { subst. inv CLOSED1. rewrite INHABITED in x0. inv x0. }
    exploit lower_exists; eauto; try apply Message.elt_wf. i. des.
    exploit lower_half_elt_concrete_elt; eauto. i.
    exploit (IHdom mem2).
    { ii. exploit LE1; eauto. i.
      erewrite lower_o; eauto. condtac; ss.
      des. subst. rewrite x1 in LHS. inv LHS. }
    { eapply lower_closed; eauto; econs; ss.
      unfold TimeMap.bot. apply Time.bot_spec. }
    { inv NODUP. ss. }
    { i. exploit lower_get0; eauto. i. des.
      revert GET. erewrite lower_o; eauto. condtac; ss.
      i. exploit SOUND; eauto. i. des; ss; inv x; congr. }
    { i. exploit COMPLETE; eauto. i. des. esplits; eauto.
      erewrite lower_o; eauto. condtac; ss; eauto.
      des. subst. inv NODUP. congr. }
    i. des.
    exists mem0. splits; eauto; try by etrans; eauto.
    econs; eauto. econs; eauto; try by repeat econs.
    econs. ss. unfold TimeMap.bot. apply Time.bot_spec.
  Qed.

  Lemma no_half_concrete_elt_future
        promises mem1 mem2
        (CLOSED1: closed mem1)
        (LE1: le promises mem1)
        (LE2: le promises mem2)
        (CONCRETE_ELT: concrete_elt mem1 mem2)
        (NOHALF: no_half promises mem2):
    future mem1 mem2.
  Proof.
    exploit no_half_concrete_elt_future_exists; try exact CLOSED1; eauto. i. des.
    exploit no_half_concrete_elt_inj; [exact CONCRETE_ELT|exact CONCRETE_ELT0|..]; eauto. i. subst.
    ss.
  Qed.

  Lemma no_half_concrete_future_exists
        promises mem1
        (LE1: le promises mem1)
        (CLOSED1: closed mem1):
    exists mem2,
      <<FUTURE: future mem1 mem2>> /\
      <<CONCRETE: concrete mem1 mem2>> /\
      <<NOHALF: no_half promises mem2>> /\
      <<LE2: le promises mem2>> /\
      <<CLOSED2: closed mem2>>.
  Proof.
    exploit no_half_concrete_elt_future_exists; eauto. i. des.
    esplits; eauto. apply concrete_elt_concrete; auto.
  Qed.
End Memory.
