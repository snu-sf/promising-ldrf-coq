Require Import Omega.
Require Import RelationClasses.

From Paco Require Import paco.
From sflib Require Import sflib.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
Require Import Time.
Require Import Event.
From PromisingLib Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import Cover.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.
Require Import Progress.
Require Import PromiseConsistent.
From PromisingLib Require Import Loc.

Require Import PF.
Require Import Race.
Require Import Behavior.
Require Import SimMemory.
Require Import yjtac.
Require Import Program.
Require Import Cell.
Require Import Time.
Require Import PredStep.
Require Import ReorderPromises2.

Require Import DRF_PF.

Require Import PFConsistent.

Set Implicit Arguments.



Inductive added_memory_imm (tm: TimeMap.t): Memory.t -> Memory.t -> Prop :=
| added_memory_imm_intro
    m0 loc to from val m1
    (TLE: Time.le (tm loc) to)
    (ADD: Memory.add m0 loc to from (Message.full val None) m1)
  :
    added_memory_imm tm m0 m1
.

Definition added_memory (tm: TimeMap.t) := rtc (added_memory_imm tm).

Lemma added_memory_future tm m0 m1
      (ADDED: added_memory tm m0 m1)
  :
    Memory.future m0 m1.
Proof.
  ginduction ADDED; auto. etrans; [| apply IHADDED].
  inv H. econs; eauto. econs; eauto.
  econs. ss. eapply Time.bot_spec.
Qed.

Definition no_reserves (proms: Memory.t): Prop :=
  forall loc to from msg (GET: Memory.get loc to proms = Some (from, msg)),
    msg <> Message.reserve.

Inductive only_reserves (proms: Memory.t): Prop :=
| only_reserves_intro
    (RESERVES: forall loc to from msg (GET: Memory.get loc to proms = Some (from, msg)),
        msg = Message.reserve)
    (FINITE: Memory.finite proms)
.

Lemma reserves_cancelable lang st vw proms0 sc mem0
      (FINITE: Memory.finite proms0)
      (MLE: Memory.le proms0 mem0)
  :
    exists proms1 mem1,
      (<<STEPS: rtc (tau (@pred_step is_cancel lang))
                    (Thread.mk lang st (Local.mk vw proms0) sc mem0)
                    (Thread.mk lang st (Local.mk vw proms1) sc mem1)>>) /\
      (<<NORESERVES: no_reserves proms1>>).
Proof.
  assert (exists dom,
             (<<COMPLETE: forall loc to,
                 (exists from, (<<GET: Memory.get loc to proms0 = Some (from, Message.reserve)>>))
                 <-> (<<IN: List.In (loc, to) dom>>)>>)).
  { unfold Memory.finite in *. des.
    generalize (list_filter_exists (fun locto =>
                                      match locto with
                                      | (loc, to) =>
                                        exists from, Memory.get loc to proms0 = Some (from, Message.reserve)
                                      end) dom).
    i. des. exists l'. split; i.
    - eapply COMPLETE. des. esplits; eauto.
    - eapply COMPLETE in H. des. esplits; eauto. }
  des. ginduction dom; ss; i.
  - exists proms0, mem0. esplits; eauto.
    ii. clarify. eapply COMPLETE. eauto.
  - destruct a as [loc to].
    exploit (proj2 (COMPLETE loc to)); eauto. i. des.
    destruct (classic (List.In (loc, to) dom)).
    { exploit IHdom; eauto. i. split; i.
      - des. exploit (proj1 (COMPLETE loc0 to0)); eauto.
        i. des; clarify.
      - exploit (proj2 (COMPLETE loc0 to0)); eauto. }
    exploit Memory.remove_exists; eauto.
    intros [prom1 REMOVE0].
    exploit Memory.remove_exists.
    { eapply MLE. eapply GET. }
    intros [mem1 REMOVE1]. hexploit IHdom.
    * instantiate (1:=prom1).
      eapply Memory.remove_finite; eauto.
    * instantiate (1:=mem1).
      ii. erewrite Memory.remove_o in LHS; eauto. des_ifs.
      eapply MLE in LHS. erewrite Memory.remove_o; eauto. des_ifs.
      ss. des; clarify.
    * i. split; i.
      { des. erewrite Memory.remove_o in GET0; eauto. des_ifs.
        exploit (proj1 (COMPLETE loc0 to0)); eauto. i. des; clarify. }
      { exploit (proj2 (COMPLETE loc0 to0)); eauto. i. des; clarify.
        exists from0. erewrite Memory.remove_o; eauto. des_ifs.
        ss. des; clarify. }
    * i. des. exists proms1, mem2. split; eauto.
      econs 2.
      { econs.
        - instantiate (2:=ThreadEvent.promise loc from to Message.reserve Memory.op_kind_cancel).
          econs; ss. econs. econs 1. econs; ss.
          econs; ss. econs; eauto.
        - eauto. }
      { eauto. }
Qed.

(* Lemma reserves_cancelable lang st vw proms sc mem0 *)
(*       (RESERVES: only_reserves proms) *)
(*       (MLE: Memory.le proms mem0) *)
(*   : *)
(*     exists mem1, *)
(*       rtc (tau (@pred_step is_cancel lang)) *)
(*           (Thread.mk lang st (Local.mk vw proms) sc mem0) *)
(*           (Thread.mk lang st (Local.mk vw Memory.bot) sc mem1). *)
(* Proof. *)
(*   inv RESERVES. unfold Memory.finite in *. des. *)
(*   ginduction dom; ss; i. *)
(*   - exists mem0. replace proms with Memory.bot; auto. *)
(*     eapply Memory.ext. i. rewrite Memory.bot_get. *)
(*     destruct (Memory.get loc ts proms) as [[from msg]|] eqn:GET; auto. *)
(*     exfalso. eauto. *)
(*   - destruct a as [loc' to']. *)
(*     destruct (Memory.get loc' to' proms) as [[from' msg']|] eqn:GET. *)
(*     + exploit RESERVES0; eauto. i. clarify. *)
(*       exploit Memory.remove_exists. *)
(*       { eapply GET. } *)
(*       intros [prom1 REMOVE0]. *)
(*       exploit Memory.remove_exists. *)
(*       { eapply MLE. eapply GET. } *)
(*       intros [mem1 REMOVE1]. hexploit IHdom. *)
(*       * instantiate (1:=mem1). instantiate (1:=prom1). *)
(*         ii. erewrite Memory.remove_o in LHS; eauto. des_ifs. *)
(*         eapply MLE in LHS. erewrite Memory.remove_o; eauto. des_ifs. *)
(*         ss. des; clarify. *)
(*       * i. erewrite Memory.remove_o in GET0; eauto. des_ifs. *)
(*         eapply RESERVES0; eauto. *)
(*       * i. erewrite Memory.remove_o in GET0; eauto. des_ifs. *)
(*         exploit FINITE; eauto. i. ss. *)
(*         des; ss; clarify. *)
(*       * i. des. exists mem2. econs 2. *)
(*         { econs. *)
(*           - instantiate (2:=ThreadEvent.promise loc' from' to' Message.reserve Memory.op_kind_cancel). *)
(*             econs; ss. econs. econs 1. econs; ss. *)
(*             econs; ss. econs; eauto. *)
(*           - ss. } *)
(*         eapply H. *)
(*     + eapply IHdom; eauto. *)
(*       i. exploit FINITE; eauto. i. des; clarify. *)
(* Qed. *)

Lemma promise_free_no_promise P lang (th0 th1: Thread.t lang) e
      (NOPROMISE: th0.(Thread.local).(Local.promises) = Memory.bot)
      (STEP: pred_step (P /1\ promise_free) e th0 th1)
  :
    (<<STEP: pred_step (P /1\ no_promise) e th0 th1>>) /\
    (<<NOPROMISE: th1.(Thread.local).(Local.promises) = Memory.bot>>).
Proof.
  inv STEP. inv STEP0. inv STEP.
  - inv STEP0. inv LOCAL. inv PROMISE; ss; des; clarify.
    + rewrite NOPROMISE in *.
      eapply Memory.lower_get0 in PROMISES. des.
      erewrite Memory.bot_get in *. clarify.
    + rewrite NOPROMISE in *.
      eapply Memory.remove_get0 in PROMISES. des.
      erewrite Memory.bot_get in *. clarify.
  - inv STEP0. inv LOCAL.
    + ss. esplits; eauto. econs; eauto. econs; eauto.
    + ss. esplits; eauto.
      * econs; eauto. econs; eauto.
      * inv LOCAL0. ss.
    + ss. esplits; eauto.
      * econs; eauto. econs; eauto.
      * inv LOCAL0. rewrite NOPROMISE in *.
        exploit memory_write_bot_add; eauto. i. clarify.
        inv WRITE. inv PROMISE. ss.
        symmetry. eapply MemoryMerge.MemoryMerge.add_remove; eauto.
    + ss. esplits; eauto.
      * econs; eauto. econs; eauto.
      * inv LOCAL1. inv LOCAL2. rewrite NOPROMISE in *.
        exploit memory_write_bot_add; eauto. i. clarify.
        inv WRITE. inv PROMISE. ss.
        symmetry. eapply MemoryMerge.MemoryMerge.add_remove; eauto.
    + ss. esplits; eauto.
      * econs; eauto. econs; eauto.
      * inv LOCAL0. ss.
    + ss. esplits; eauto.
      * econs; eauto. econs; eauto.
      * inv LOCAL0. ss.
    + ss. esplits; eauto.
      * econs; eauto. econs; eauto.
Qed.

Definition caps (mem0 prom : Memory.t) (l : Loc.t) (t from : Time.t) (msg : Message.t) :=
  forall mem1 (CAP: Memory.cap prom mem0 mem1),
    (<<GET0: Memory.get l t mem0 = None>>) /\
    (<<GET1: Memory.get l t mem1 = Some (from, msg)>>).

(* Inductive my_caps (mem0 prom : Memory.t) (l : Loc.t) (t from : Time.t) (msg : Message.t) := *)
(*   (<<CAPS: caps mem0 prom l t from msg>>) /\ *)
(*   (<< *)



(*   forall mem1 (CAP: Memory.cap prom mem0 mem1), *)
(*     (<<GET0: Memory.get l t mem0 = None>>) /\ *)
(*     (<<GET1: Memory.get l t mem1 = Some (from, msg)>>). *)


Definition caps_loc (mem0 prom : Memory.t) (l : Loc.t) (t : Time.t): Prop :=
  exists from msg, (<<CAPS: caps mem0 prom l t from msg>>).

Lemma caps_unchangable mem0 prom mem1
      (MLE: Memory.le prom mem0)
      (CAP: Memory.cap prom mem0 mem1)
  :
    caps mem0 prom <4= unchangable mem1 prom.
Proof.
  i. exploit PR; eauto. i. des. inv CAP.
  econs; eauto. ii. inv H.
  destruct msg. eapply MLE in GET. clarify.
Qed.

Lemma finite_least P (l: list Time.t)
  :
    (exists to,
        (<<SAT: P to>>) /\
        (<<IN: List.In to l>>) /\
        (<<LEAST: forall to'
                         (IN: List.In to' l)
                         (SAT: P to'),
            Time.le to to'>>)) \/
    (<<EMPTY: forall to (IN: List.In to l), ~ P to>>).
Proof.
  induction l.
  - right. ii. inv IN.
  - destruct (classic (P a)).
    + des.
      * destruct (Time.le_lt_dec a to).
        { left. exists a. esplits; ss; eauto.
          i. des; clarify; eauto. refl. }
        { left. exists to. esplits; ss; eauto.
          i. des; clarify; eauto. left. eauto. }
      * left. exists a. esplits; ss; eauto.
        i. des; clarify.
        { refl. }
        { exfalso. eapply EMPTY; eauto. }
    + des.
      * left. esplits; ss; eauto.
        i. des; clarify. eapply LEAST; eauto.
      * right. ii. ss. des; clarify.
        eapply EMPTY; eauto.
Qed.

Lemma cell_elements_least cell P
  :
    (exists to from msg,
        (<<GET: Cell.get to cell = Some (from, msg)>>) /\
        (<<SAT: P to>>) /\
        (<<LEAST: forall to' from' msg'
                         (GET': Cell.get to' cell = Some (from', msg'))
                         (SAT: P to'),
            Time.le to to'>>)) \/
    (<<EMPTY: forall to from msg
                     (GET: Cell.get to cell = Some (from, msg)),
        ~ P to>>).
Proof.
  hexploit (Cell.finite cell). i. des.
  hexploit (finite_least (fun to => P to /\ exists from msg, Cell.get to cell = Some (from, msg)) dom).
  i. des.
  - left. esplits; eauto. i.
    dup GET'. eapply H in GET'. eauto.
  - right. ii. dup GET. eapply H in GET0.
    eapply EMPTY in GET0. eapply GET0.
    esplits; eauto.
Qed.

Lemma disjoint_equivalent2 from0 to0 from1 to1
  :
    (<<DISJOINT: Interval.disjoint (from0, to0) (from1, to1)>>) <->
    ((<<TS0: ~ Time.lt from0 to0>>) \/ (<<TS1: ~ Time.lt from1 to1>>) \/
     (<<TS0: Time.le (Time.meet to0 to1) (Time.join from0 from1)>>)).
Proof.
  set (disjoint_equivalent from0 to0 from1 to1).
  eapply not_iff_compat in i. split; i.
  - des. hexploit i.
    { ii. clarify. } i.
    apply not_and_or in H0. des; eauto.
    apply not_and_or in H0. des; eauto.
    right. right. red.
    destruct (Time.le_lt_dec (Time.meet to0 to1) (Time.join from0 from1)); eauto.
    exfalso. eauto.
  - destruct i. hexploit H1.
    { ii. des; eauto. eapply Time.lt_strorder.
      eapply TimeFacts.lt_le_lt; eauto. }
    ii. eauto.
Qed.

Lemma or_strengthen A B
      (OR: A \/ B)
  :
    (A \/ ((<<NOT: ~ A>>) /\ (<<SAT: B>>))).
Proof.
  destruct (classic A); eauto. des; eauto.
Qed.

Lemma memory_get_ts_strong loc to mem from msg
      (GET: Memory.get loc to mem = Some (from, msg))
  :
    (from = Time.bot /\ to = Time.bot) \/
    ((<<TS: Time.lt from to>>) /\ (<<TO: to <> Time.bot>>)).
Proof.
  apply Memory.get_ts in GET.
  destruct (classic (to = Time.bot)); clarify.
  - des; clarify; eauto.
    exfalso. eapply Time.lt_strorder.
    eapply TimeFacts.lt_le_lt; eauto. eapply Time.bot_spec.
  - des; clarify. right. eauto.
Qed.

Lemma memory_get_from_inj mem loc from to0 to1 msg0 msg1
      (GET0: Memory.get loc to0 mem = Some (from, msg0))
      (GET1: Memory.get loc to1 mem = Some (from, msg1))
  :
    (<<TO: to0 = to1>>) \/
    (((<<BOT: to0 = Time.bot>>) \/ (<<BOT: to1 = Time.bot>>)) /\ (<<BOT: from = Time.bot>>) /\
     (<<TO: to0 <> to1>>)).
Proof.
  exploit Memory.get_disjoint.
  - eapply GET0.
  - eapply GET1.
  - i. des; clarify; eauto.
    eapply memory_get_ts_strong in GET0.
    eapply memory_get_ts_strong in GET1.
    des; clarify; eauto.
    { right. esplits; eauto. }
    { right. esplits; eauto. }
    exfalso. eapply x0.
    + instantiate (1:=Time.meet to0 to1). econs; ss; eauto.
      * unfold Time.meet. des_ifs.
      * eapply Time.meet_l.
    + econs; ss; eauto.
      * unfold Time.meet. des_ifs.
      * eapply Time.meet_r.
Qed.


Lemma memory_get_to_mon mem loc from0 from1 to0 to1 msg0 msg1
      (GET0: Memory.get loc to0 mem = Some (from0, msg0))
      (GET1: Memory.get loc to1 mem = Some (from1, msg1))
      (TO: Time.lt from0 from1)
  :
    Time.lt to0 to1.
Proof.
  exploit Memory.get_disjoint.
  - eapply GET0.
  - eapply GET1.
  - i. des; clarify.
    + exfalso. eapply Time.lt_strorder. eauto.
    + dup GET0. dup GET1.
      eapply memory_get_ts_strong in GET0.
      eapply memory_get_ts_strong in GET1.
      des; clarify.
      * exfalso. eapply Time.lt_strorder.
        eapply TimeFacts.lt_le_lt; eauto. eapply Time.bot_spec.
      * hexploit (Time.bot_spec from1). i.
        destruct H; eauto.
      * eapply disjoint_equivalent2 in x0. des; clarify.
        unfold Time.meet, Time.join in *. des_ifs; eauto.
        { destruct l; eauto. destruct H; eauto. clarify.
          exfalso. eapply Time.lt_strorder; eauto. }
        { destruct l; eauto. destruct H; eauto. clarify.
          exfalso. eapply Time.lt_strorder; eauto. }
        { exfalso. eapply Time.lt_strorder.
          eapply TimeFacts.le_lt_lt; eauto. }
        { exfalso. eapply Time.lt_strorder.
          eapply TimeFacts.le_lt_lt; eauto. }
Qed.

Lemma memory_get_from_mon mem loc from0 from1 to0 to1 msg0 msg1
      (GET0: Memory.get loc to0 mem = Some (from0, msg0))
      (GET1: Memory.get loc to1 mem = Some (from1, msg1))
      (TO: Time.lt to0 to1)
  :
    (<<FROMTO: Time.le to0 from1>>) \/
    ((<<FROM0: from0 = Time.bot>>) /\ (<<FROM1: from1 = Time.bot>>) /\ (<<TO: to0 = Time.bot>>)).
Proof.
  exploit Memory.get_disjoint.
  - eapply GET0.
  - eapply GET1.
  - i. des; clarify.
    + exfalso. eapply Time.lt_strorder. eauto.
    + dup GET0. dup GET1.
      eapply memory_get_ts_strong in GET0.
      eapply memory_get_ts_strong in GET1.
      des; clarify.
      * exfalso. eapply Time.lt_strorder.
        eapply TimeFacts.lt_le_lt; eauto. eapply Time.bot_spec.
      * exfalso. eapply Time.lt_strorder.
        eapply TimeFacts.lt_le_lt; eauto. eapply Time.bot_spec.
      * left. apply Time.bot_spec.
      * left. destruct (Time.le_lt_dec to0 from1); auto. exfalso.
        eapply x0.
        { instantiate (1:=to0).
          econs; ss. refl. }
        { econs; ss. left. auto. }
Qed.

(* Lemma memory_get_from_mon2 mem loc from0 from1 to0 to1 msg0 msg1 *)
(*       (GET0: Memory.get loc to0 mem = Some (from0, msg0)) *)
(*       (GET1: Memory.get loc to1 mem = Some (from1, msg1)) *)
(*       (TO: Time.lt to0 to1) *)
(*   : *)
(*     (<<FROM: Time.lt from0 from1>>) \/ *)
(*     ((<<FROM0: from0 = Time.bot>>) /\ (<<FROM1: from1 = Time.bot>>) /\ (<<TO: to0 = Time.bot>>)). *)
(* Proof. *)
(* Admitted. *)

Lemma caps_concrete_last mem0 prom mem1 tm l t from val released
      (RESERVE: Memory.reserve_wf prom mem0)
      (INHABITED: Memory.inhabited mem0)
      (MAX: Memory.max_full_timemap mem0 tm)
      (CAP: Memory.cap prom mem0 mem1)
      (CAPS: caps mem0 prom l t from (Message.full val released))
  :
    from = Memory.max_ts l mem0.
Proof.
  exploit CAPS; eauto. i. des. inv CAP.
  exploit COMPLETE; eauto. i. des.
  destruct (classic (Memory.max_ts l mem0 = from)); eauto. exfalso.
  set (@cell_elements_least
         (mem0 l)
         (fun to => Time.lt from to)). des.
  + assert (TLE: Time.le from from0).
    { dup GET. eapply Memory.get_ts in GET. des; clarify.
      { exfalso. eapply Time.lt_strorder.
        eapply TimeFacts.lt_le_lt; eauto. eapply Time.bot_spec. }
      exploit memory_get_from_mon.
      - eapply x.
      - eapply GET2.
      - eauto.
      - i. des; clarify. refl. }
    destruct TLE.
    * exploit MIDDLE; eauto.
      econs.
      { eapply x. }
      { eapply GET. }
      { eauto. }
      { i. destruct (Memory.get l ts mem0) eqn: GET2; auto.
        destruct p. exfalso. dup GET2. eapply LEAST in GET2; eauto.
        eapply Memory.get_ts in GET. des; clarify.
        - eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
          eapply SAT. eapply Time.bot_spec.
        - eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
          eapply GET. etrans; eauto. }
      { i. exploit memory_get_from_inj.
        - eapply x1.
        - eapply GET1.
        - i. des; clarify. eapply Time.lt_strorder; eauto. }
    * destruct H0.
      exploit memory_get_from_inj.
      { eapply GET1. }
      { eapply SOUND. eapply GET. }
      { i. des; clarify.
        - unfold Memory.get in GET0. clarify.
        - eapply Time.lt_strorder; eauto. }
  + exploit Memory.max_ts_spec.
    { eapply x. } i. des.
    eapply EMPTY; eauto. destruct MAX0; clarify.
    exfalso. eauto.
Qed.

Lemma caps_max_view mem0 prom mem1 tm l t from val released
      (RESERVE: Memory.reserve_wf prom mem0)
      (INHABITED: Memory.inhabited mem0)
      (MAX: Memory.max_full_timemap mem0 tm)
      (CAP: Memory.cap prom mem0 mem1)
      (CAPS: caps mem0 prom l t from (Message.full val released))
  :
    (<<FROM: from = Memory.max_ts l mem0>>) /\
    (<<RESERVE: Memory.latest_reserve l prom mem0>>) /\
    (<<VAL: Memory.latest_val l mem0 val >>) /\
    (<<RELEASED: released = Some (View.mk tm tm)>>) /\
    (<<TO: t = Time.incr (Memory.max_ts l mem0)>>).
Proof.
  exploit caps_concrete_last; eauto. i. clarify.
  exploit CAPS; eauto. i. des. inv CAP.
  exploit COMPLETE; eauto. i. des.
  exploit Memory.latest_val_exists; eauto. i. des.
  exploit BACK; eauto. i.
  exploit memory_get_from_inj.
  { eapply x1. }
  { eapply GET1. } i. des; clarify.
  - esplits; eauto.
  - exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
    + eapply Time.incr_spec.
    + erewrite BOT0. eapply Time.bot_spec.
  - erewrite INHABITED in GET0. clarify.
Qed.

Definition pf_consistent_strong lang (e:Thread.t lang): Prop :=
  forall mem1 sc1
         (CAP: Memory.cap e.(Thread.local).(Local.promises) e.(Thread.memory) mem1),
  exists e2,
    (<<STEPS: rtc (tau (@pred_step ((promise_free /1\ no_acq_read_msgs (caps_loc e.(Thread.memory) e.(Thread.local).(Local.promises))) /1\ no_sc) lang)) (Thread.mk _ e.(Thread.state) e.(Thread.local) sc1 mem1) e2>>) /\
    ((<<FAILURE: Local.failure_step e2.(Thread.local)>>) \/
     (<<PROMISES: e2.(Thread.local).(Local.promises) = Memory.bot>>)).

Lemma write_promises_decrease prom0 mem0 loc from to val realeased prom1 mem1 kind
      (WRITE: Memory.write prom0 mem0 loc from to val realeased prom1 mem1 kind)
  :
    concrete_promised prom1 <2= concrete_promised prom0.
Proof.
  inv WRITE. inv PROMISE.
  - exploit MemoryMerge.MemoryMerge.add_remove.
    + eapply PROMISES.
    + eapply REMOVE.
    + i. clarify.
  - ii. inv PR.
    erewrite Memory.remove_o in GET; eauto. des_ifs.
    erewrite Memory.split_o in GET; eauto. des_ifs.
    + ss; des; clarify.
    + ss. des; clarify. eapply Memory.split_get0 in PROMISES.
      des. econs; eauto.
    + eapply Memory.split_get0 in PROMISES.
      guardH o. guardH o0. guardH o1. des. econs; eauto.
  - ii. inv PR.
    erewrite Memory.remove_o in GET; eauto. des_ifs.
    erewrite Memory.lower_o in GET; eauto. des_ifs.
    + ss; des; clarify.
    + econs; eauto.
  - clarify.
Qed.

Lemma pf_step_promises_decrease P lang e (th0 th1: Thread.t lang)
      (STEP: (@pred_step (promise_free /1\ P) lang) e th0 th1)
  :
    concrete_promised (th1.(Thread.local).(Local.promises)) <2=
    concrete_promised (th0.(Thread.local).(Local.promises)).
Proof.
  i. inv STEP. inv STEP0. des. inv STEP.
  - inv STEP0. ss. inv LOCAL. ss. inv PROMISE; clarify.
    + inv PR. erewrite Memory.lower_o in GET; eauto. des_ifs.
      * ss; des. clarify. eapply Memory.lower_get0 in PROMISES.
        des. econs; eauto.
      * econs; eauto.
    + inv PR. erewrite Memory.remove_o in GET; eauto. des_ifs.
      econs; eauto.
  - inv STEP0. ss. inv LOCAL; eauto.
    + inv LOCAL0. ss.
    + inv LOCAL0. ss. eapply write_promises_decrease; eauto.
    + inv LOCAL1. inv LOCAL2. ss. eapply write_promises_decrease; eauto.
    + inv LOCAL0. ss.
    + inv LOCAL0. ss.
Qed.

Lemma pf_step_rtc_promises_decrease P lang (th0 th1: Thread.t lang)
      (STEP: rtc (tau (@pred_step (promise_free /1\ P) lang)) th0 th1)
  :
    concrete_promised (th1.(Thread.local).(Local.promises)) <2=
    concrete_promised (th0.(Thread.local).(Local.promises)).
Proof.
  ginduction STEP; ss.
  i. eapply IHSTEP in PR; eauto. inv H.
  eapply pf_step_promises_decrease; eauto.
Qed.

Lemma le_inhabited mem0 mem1
      (INHABITED: Memory.inhabited mem0)
      (MLE: Memory.le mem0 mem1)
  :
    Memory.inhabited mem1.
Proof.
  ii. eapply MLE; eauto.
Qed.

Inductive configuration_step: forall (e:MachineEvent.t) (tid:Ident.t) (c1 c2:Configuration.t), Prop :=
| configuration_step_intro
    pf e tid c1 lang st1 lc1 e2 st3 lc3 sc3 memory3
    (TID: IdentMap.find tid c1.(Configuration.threads) = Some (existT _ lang st1, lc1))
    (STEPS: rtc (@Thread.tau_step _) (Thread.mk _ st1 lc1 c1.(Configuration.sc) c1.(Configuration.memory)) e2)
    (STEP: Thread.step pf e e2 (Thread.mk _ st3 lc3 sc3 memory3))
    (CONSISTENT: forall (EVENT: e <> ThreadEvent.failure),
        Thread.consistent (Thread.mk _ st3 lc3 sc3 memory3))
  :
    configuration_step (ThreadEvent.get_machine_event e) tid c1 (Configuration.mk (IdentMap.add tid (existT _ _ st3, lc3) c1.(Configuration.threads)) sc3 memory3)
.

Lemma configuration_step_equivalent e tid c1 c2
  :
    Configuration.step e tid c1 c2 <-> configuration_step e tid c1 c2.
Proof.
  split.
  - i. inv H.
    + replace MachineEvent.failure with (ThreadEvent.get_machine_event ThreadEvent.failure); auto.
      econs; eauto. i. clarify.
    + econs; eauto.
  - i. inv H. destruct (classic (e0 = ThreadEvent.failure)).
    + clarify. econs 1; eauto.
    + econs 2; eauto.
Qed.

Lemma no_sc_any_sc_rtc
      P lang th_src th_tgt th_tgt' st st' lc lc' sc sc_src sc'
      mem mem'
      (STEP: rtc (tau (@pred_step (P /1\ no_sc) lang)) th_tgt th_tgt')
      (TH_SRC: th_src = Thread.mk lang st lc sc_src mem)
      (TH_TGT0: th_tgt = Thread.mk lang st lc sc mem)
      (TH_TGT1: th_tgt' = Thread.mk lang st' lc' sc' mem')
  :
    exists sc_src',
      (<<STEP: rtc (tau (@pred_step (P /1\ no_sc) lang))
                   th_src
                   (Thread.mk lang st' lc' sc_src' mem')>>).
Proof.
  ginduction STEP.
  - i. clarify. esplits; eauto.
  - i. clarify. destruct y. destruct local, lc, lc'. ss.
    inv H. exploit no_sc_any_sc; eauto. i. des.
    exploit IHSTEP; eauto. i. des.
    exists sc_src'0. esplits. econs; eauto.
Qed.

Lemma max_full_timemap_get mem tm loc to from val released
      (MAX: Memory.max_full_timemap mem tm)
      (GET: Memory.get loc to mem = Some (from, Message.full val released) )
  :
    Time.le to (tm loc).
Proof.
  specialize (MAX loc). inv MAX. eapply MAX0; eauto.
Qed.

Lemma unchangable_rtc_increase P lang (th0 th1: Thread.t lang)
      (STEPS: rtc (tau (@pred_step P lang))th0 th1)
  :
    unchangable th0.(Thread.memory) th0.(Thread.local).(Local.promises) <4=
    unchangable th1.(Thread.memory) th1.(Thread.local).(Local.promises).
Proof.
  ginduction STEPS; ss. i.
  eapply IHSTEPS.
  inv H. inv TSTEP. inv STEP. eapply unchangable_increase; eauto.
Qed.

(* Lemma pf_consistent_pf_consistent_strong lang (th: Thread.t lang) *)
(*       (WF: Local.wf th.(Thread.local) th.(Thread.memory)) *)
(*       (MEM: Memory.closed th.(Thread.memory)) *)
(*       (INHABITED: Memory.inhabited th.(Thread.memory)) *)
(*       (CONSISTENT: pf_consistent th) *)
(*   : *)
(*     pf_consistent_strong th. *)
(* Proof. *)
(*   ii. exploit Memory.max_full_timemap_exists; eauto. intros MAX. des. *)
(*   ii. exploit Memory.max_full_timemap_exists. *)
(*   { eapply le_inhabited; eauto. eapply Memory.cap_le; eauto. refl. } *)
(*   i. des. exploit CONSISTENT; eauto. i. *)
(*   destruct x as [e2 [STEPS GOOD]]. guardH GOOD. des. *)
(*   eapply pf_step_promise_free_step_rtc in STEPS. *)
(*   eapply hold_or_not with (Q := no_acq_read_msgs (caps_loc (Thread.memory th) (Local.promises (Thread.local th))) /1\ no_sc) in STEPS. des. *)

(*   - destruct th. destruct e2. ss. *)
(*     eapply pred_step_rtc_mon with (Q:=(promise_free /1\ no_acq_read_msgs (caps_loc memory (Local.promises local))) /1\ no_sc) in HOLD; cycle 1. *)
(*     { i. des. esplits; eauto. } *)
(*     exploit no_sc_any_sc_rtc; try eapply HOLD; eauto. i. des. *)
(*     esplits; eauto. unguard. des. *)
(*     + left. ss. inv FAILURE; inv STEP0. inv LOCAL. eauto. *)
(*     + right. esplits; eauto. *)

(*   - exploit Thread.rtc_tau_step_future. *)
(*     { eapply thread_steps_pred_steps. eapply STEPS0. } *)
(*     { ss. eapply Local.cap_wf; eauto. } *)
(*     { ss. eapply Memory.max_full_timemap_closed; eauto. } *)
(*     { ss. eapply Memory.cap_closed; eauto. } *)
(*     i. des. ss. inv STEP. *)
(*     exploit Thread.step_future; eauto. *)
(*     i. des. *)

(*     hexploit (@rtc_tau_step_promise_consistent _ e3 e2); eauto. *)
(*     { eapply thread_steps_pred_steps; eauto. } *)
(*     { unguard. des. *)
(*       - inv FAILURE; inv STEP. inv LOCAL. inv LOCAL0. ss. *)
(*       - ii. rewrite PROMISES in *. *)
(*         erewrite Memory.bot_get in PROMISE. clarify. } intros PROMS. *)

(*     assert (RESERVES: only_reserves e2'.(Thread.local).(Local.promises)). *)
(*     { econs. *)
(*       - i. destruct msg; auto. exfalso. dup STEPS0. *)
(*         eapply pf_step_rtc_promises_decrease in STEPS0; cycle 1. *)
(*         { econs; eauto. } *)
(*         ss. inv STEPS0. *)
(*         unfold no_sc, no_acq_read_msgs in BREAKQ. des_ifs; try by (exfalso; eauto). *)
(*         + apply not_and_or in BREAKQ. des; clarify. *)
(*           apply imply_to_and in BREAKQ. des. apply NNPP in BREAKQ0. *)
(*           unfold caps_loc in *. des. dup CAPS. *)
(*           eapply caps_unchangable in CAPS; eauto; cycle 1. *)
(*           { inv WF. eauto. } *)
(*           eapply unchangable_rtc_increase in STEPS2; eauto. inv STEPS2. *)
(*           inv STEP0; inv STEP. ss. inv LOCAL. *)
(*           inv LOCAL0. clarify. eapply caps_max_view in CAPS0; eauto; cycle 1. *)
(*           { inv WF. eauto. } des. *)
(*           clarify. eapply PROMS in GET. ss. des_ifs. ss. *)
(*           exploit max_full_timemap_get. *)
(*           * apply MAX. *)
(*           * inv WF. eapply PROMISES. eauto. *)
(*           * i. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt; eauto. *)
(*             etrans; eauto. eapply TimeMap.join_r. *)
(*         + apply not_and_or in BREAKQ. des; clarify. *)
(*           apply imply_to_and in BREAKQ. des. apply NNPP in BREAKQ0. *)
(*           unfold caps_loc in *. des. dup CAPS. *)
(*           eapply caps_unchangable in CAPS; eauto; cycle 1. *)
(*           { inv WF. eauto. } *)
(*           eapply unchangable_rtc_increase in STEPS2; eauto. inv STEPS2. *)
(*           inv STEP0; inv STEP. ss. inv LOCAL. *)
(*           eapply write_step_promise_consistent in LOCAL2; eauto. *)
(*           inv LOCAL1. clarify. eapply caps_max_view in CAPS0; eauto; cycle 1. *)
(*           { inv WF. eauto. } des. *)
(*           clarify. eapply LOCAL2 in GET. ss. des_ifs. ss. *)
(*           exploit max_full_timemap_get. *)
(*           * apply MAX. *)
(*           * inv WF. eapply PROMISES. eauto. *)
(*           * i. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt; eauto. *)
(*             etrans; eauto. eapply TimeMap.join_r. *)
(*         + apply not_and_or in BREAKQ. des; clarify. apply NNPP in BREAKQ. *)
(*           inv STEP0; inv STEP. ss. inv LOCAL. inv LOCAL0. ss. *)
(*           eapply PROMS in GET. ss. des_ifs. ss. *)
(*           hexploit max_full_timemap_get; eauto. *)
(*           * inv WF. eapply Memory.cap_le; eauto. *)
(*           * i. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt; eauto. *)
(*         + inv STEP0; inv STEP. ss. inv LOCAL. inv LOCAL0. ss. *)
(*           eapply PROMS in GET. ss. des_ifs. ss. *)
(*           hexploit max_full_timemap_get; eauto. *)
(*           * inv WF. eapply Memory.cap_le; eauto. *)
(*           * i. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt; eauto. *)
(*       - inv WF2. eauto. } *)

(*     destruct e2'. destruct local. ss. *)
(*     eapply pred_step_rtc_mon with (Q:=(promise_free /1\ no_acq_read_msgs (caps_loc (Thread.memory th) (Local.promises (Thread.local th)))) /1\ no_sc) in STEPS0; cycle 1. *)
(*     { i. des. esplits; eauto. } *)
(*     eapply no_sc_any_sc_rtc in STEPS0; ss. des. *)
(*       exploit reserves_cancelable; eauto. *)
(*       { inv WF2. eauto. } *)
(*       i. des. esplits. *)
(*       * etrans. *)
(*         { eapply STEP. } *)
(*         { eapply pred_step_rtc_mon; eauto. *)
(*           unfold is_cancel. i. des_ifs. } *)
(*       * ss. eauto. *)
(* Qed. *)

Lemma promise_not_cacncel_reserves_same prom0 mem0 loc from to msg prom1 mem1 kind
      (PROM: Memory.promise prom0 mem0 loc from to msg prom1 mem1 kind)
      (NOTCANCEL: kind <> Memory.op_kind_cancel)
      loc0 to0 from0
      (GET: Memory.get loc0 to0 mem0 = Some (from0, Message.reserve))
  :
    exists from1,
      Memory.get loc0 to0 mem1 = Some (from1, Message.reserve).
Proof.
  inv PROM.
  - eapply Memory.add_get1 in GET; eauto.
  - des. clarify. erewrite Memory.split_o; eauto.
    dup MEM. eapply Memory.split_get0 in MEM0.
    eapply split_succeed_wf in MEM. des. des_ifs.
    + ss. des. clarify.
    + ss. guardH o. des. clarify.
      esplits; eauto.
    + esplits; eauto.
  - des. clarify. erewrite Memory.lower_o; eauto. des_ifs.
    + ss. des. clarify.
      eapply lower_succeed_wf in MEM. des. clarify.
    + esplits; eauto.
  - clarify.
Qed.

Lemma step_not_cancel_reserves_same lang e th0 th1
      (STEPS: (@pred_step (promise_free /1\ (fun e => ~ is_cancel e)) lang) e th0 th1)
      loc to from
      (GET: Memory.get loc to th0.(Thread.memory) = Some (from, Message.reserve))
  :
    exists from',
      Memory.get loc to th1.(Thread.memory) = Some (from', Message.reserve).
Proof.
  inv STEPS. inv STEP. inv STEP0.
  - inv STEP. des. ss. inv LOCAL.
    eapply promise_not_cacncel_reserves_same; eauto.
    ii. clarify.
  - inv STEP. inv LOCAL; ss.
    + esplits; eauto.
    + esplits; eauto.
    + inv LOCAL0. inv WRITE.
      eapply promise_not_cacncel_reserves_same; eauto.
      ii. clarify. inv PROMISE. clarify.
    + inv LOCAL2. inv WRITE.
      eapply promise_not_cacncel_reserves_same; eauto.
      ii. clarify. inv PROMISE. clarify.
    + esplits; eauto.
    + esplits; eauto.
    + esplits; eauto.
Qed.

Lemma steps_not_cancel_reserves_same lang th0 th1
      (STEPS: rtc (tau (@pred_step (promise_free /1\ (fun e => ~ is_cancel e)) lang)) th0 th1)
      loc to from
      (GET: Memory.get loc to th0.(Thread.memory) = Some (from, Message.reserve))
  :
    exists from',
      Memory.get loc to th1.(Thread.memory) = Some (from', Message.reserve).
Proof.
  ginduction STEPS; i.
  - esplits; eauto.
  - inv H. exploit step_not_cancel_reserves_same; eauto. i. des.
    exploit IHSTEPS; eauto.
Qed.

Definition pf_consistent_strong2 lang (e0:Thread.t lang): Prop :=
  forall mem1 sc1
         (CAP: Memory.cap e0.(Thread.local).(Local.promises) e0.(Thread.memory) mem1),
  exists e1 e2,
    (<<STEPS0: rtc (tau (@pred_step is_cancel lang)) e0 e1>>) /\
    (<<NORESERVE: no_reserves e1.(Thread.local).(Local.promises)>>) /\
    (<<STEPS1: rtc (tau (@pred_step ((promise_free /1\ (fun e => ~ is_cancel e) /1\ no_acq_read_msgs (caps_loc e0.(Thread.memory) e0.(Thread.local).(Local.promises))) /1\ no_sc) lang)) (Thread.mk _ e0.(Thread.state) e0.(Thread.local) sc1 mem1) e2>>) /\
    ((<<FAILURE: Local.failure_step e2.(Thread.local)>>) \/
     (<<PROMISES: e2.(Thread.local).(Local.promises) = Memory.bot>>)).

Lemma cancel_promises_decrease lang e th0 th1
      (STEP: (@pred_step is_cancel lang) e th0 th1)
  :
    Memory.le th1.(Thread.local).(Local.promises) th0.(Thread.local).(Local.promises).
Proof.
  inv STEP. unfold is_cancel in SAT. des_ifs.
  inv STEP0. inv STEP; inv STEP0; ss.
  - inv LOCAL. inv PROMISE; ss.
    ii. erewrite Memory.remove_o in LHS; eauto. des_ifs.
  - inv LOCAL.
Qed.

Lemma cancels_promises_decrease lang th0 th1
      (STEP: rtc (tau (@pred_step is_cancel lang)) th0 th1)
  :
    Memory.le th1.(Thread.local).(Local.promises) th0.(Thread.local).(Local.promises).
Proof.
  ginduction STEP.
  - refl.
  - etrans; eauto. inv H.
    eapply cancel_promises_decrease; eauto.
Qed.

Definition wf_time_evt (P: Loc.t -> Time.t -> Prop) (e: ThreadEvent.t) : Prop :=
  match e with
  | ThreadEvent.promise loc from to msg kind =>
    (<<FROM: P loc from>>) /\ (<<TO: P loc to>>)
  | ThreadEvent.write loc from to val released ordw =>
    (<<FROM: P loc from>>) /\ (<<TO: P loc to>>)
  | ThreadEvent.update loc from to valr valw releasedr releasedw ordr ordw =>
    (<<TO: P loc to>>)
  | _ => True
  end.

Lemma wf_time_evt_mon P0 P1
      (LE: P0 <2= P1)
  :
    wf_time_evt P0 <1= wf_time_evt P1.
Proof.
  ii. unfold wf_time_evt in *. des_ifs; des; splits; eauto.
Qed.

Lemma step_times_list_exists P lang th0 th1 e
      (STEPS: (@pred_step P lang) e th0 th1)
  :
    exists times,
      (@pred_step (P /1\ wf_time_evt (fun loc to => List.In (loc, to) times)) lang) e th0 th1.
Proof.
  inv STEPS. destruct e.
  - exists [(loc, from); (loc, to)]. econs; eauto.
    ss. splits; ss; eauto.
  - exists []. econs; eauto. ss.
  - exists []. econs; eauto. ss.
  - exists [(loc, from); (loc, to)]. econs; eauto.
    ss. splits; ss; eauto.
  - exists [(loc, tsw)]. econs; eauto.
    ss. splits; ss; eauto.
  - exists []. econs; eauto. ss.
  - exists []. econs; eauto. ss.
  - exists []. econs; eauto. ss.
Qed.

Lemma times_list_exists P lang th0 th1
      (STEPS: rtc (tau (@pred_step P lang)) th0 th1)
  :
    exists times,
      rtc (tau (@pred_step (P /1\ wf_time_evt (fun loc to => List.In (loc, to) times)) lang)) th0 th1.
Proof.
  ginduction STEPS.
  - exists []. refl.
  - dup H. inv H0.
    eapply step_times_list_exists in TSTEP. des.
    exists (times ++ times0). econs 2.
    + econs; eauto. eapply pred_step_mon; eauto.
      i. ss. des. split; auto.
      eapply wf_time_evt_mon; eauto.
      i. ss. eapply List.in_or_app; eauto.
    + eapply pred_step_rtc_mon; eauto.
      i. ss. des. split; auto.
      eapply wf_time_evt_mon; eauto.
      i. ss. eapply List.in_or_app; eauto.
Qed.

Lemma pf_consistent_pf_consistent_strong2 lang (th: Thread.t lang)
      (WF: Local.wf th.(Thread.local) th.(Thread.memory))
      (MEM: Memory.closed th.(Thread.memory))
      (INHABITED: Memory.inhabited th.(Thread.memory))
      (CONSISTENT: pf_consistent th)
  :
    pf_consistent_strong2 th.
Proof.
  ii. exploit Memory.max_full_timemap_exists; eauto. intros MAX. des.
  ii. exploit Memory.max_full_timemap_exists.
  { eapply le_inhabited; eauto. eapply Memory.cap_le; eauto. refl. }
  i. des. exploit CONSISTENT; eauto. i.
  assert (exists e2,
             (<<STEPS: rtc (tau (Thread.step true))
                           (Thread.mk _ (Thread.state th) (Thread.local th)
                                      tm0 mem1) e2 >>) /\
             ((exists e3, ((<< FAILURE: Thread.step true ThreadEvent.failure e2 e3 >>))
                          /\ (<<NORESERVES: no_reserves e2.(Thread.local).(Local.promises)>>)) \/
              (<<PROMISES: Local.promises (Thread.local e2) = Memory.bot >>))).
  { des.
    - exploit Thread.rtc_tau_step_future.
      + eapply rtc_implies; [|apply STEPS].
        i. inv PR. econs; eauto. econs; eauto.
      + ss. eapply Local.cap_wf; eauto.
      + ss. eapply Memory.max_full_timemap_closed; eauto.
      + ss. eapply Memory.cap_closed; eauto.
      + i. des.
        destruct e2. destruct local. inv WF2. ss.
        exploit reserves_cancelable; eauto. i. des.
        esplits.
        * etrans.
          { eapply STEPS. }
          { eapply rtc_implies; [|apply STEPS0].
            i. inv PR. inv TSTEP. inv STEP.
            unfold is_cancel in SAT. des_ifs.
            inv STEP0; inv STEP.
            - econs; eauto. econs; eauto. econs; eauto.
            - inv LOCAL. }
        * left. inv FAILURE; inv STEP. inv LOCAL. inv LOCAL0.
          exists (Thread.mk _ st2 (Local.mk tview proms1) sc2 mem0).
          ss. split; eauto.
          econs 2. econs; eauto. econs; eauto. econs; eauto.
          eapply cancels_promises_decrease in STEPS0. ss.
          ii. eapply CONSISTENT0; eauto.
    - esplits; eauto. }

  destruct th1. ss.
  eapply hold_or_not with (Q := no_acq_read_msgs (caps_loc (Thread.memory th) (Local.promises (Thread.local th))) /1\ no_sc) in STEPS2. des.

  - destruct e2. ss.
    eapply pred_step_rtc_mon with (Q:=(promise_free /1\ (fun e => ~ is_cancel e) /1\ no_acq_read_msgs (caps_loc memory (Local.promises local))) /1\ no_sc) in HOLD; cycle 1.
    { i. des. esplits; eauto. }
    exploit no_sc_any_sc_rtc; try eapply HOLD; eauto. i. des.
    esplits; eauto. unguard. des.
    + left. ss. inv FAILURE; inv STEP0. inv LOCAL. eauto.
    + right. esplits; eauto.

  - exploit Thread.rtc_tau_step_future.
    { eapply thread_steps_pred_steps. eapply STEPS0. }
    { ss. eapply Local.cap_wf; eauto. }
    { ss. eapply Memory.max_full_timemap_closed; eauto. }
    { ss. eapply Memory.cap_closed; eauto. }
    i. des. ss. inv STEP.
    exploit Thread.step_future; eauto.
    i. des.

    hexploit (@rtc_tau_step_promise_consistent _ e3 e2); eauto.
    { eapply thread_steps_pred_steps; eauto. }
    { unguard. des.
      - inv FAILURE; inv STEP. inv LOCAL. inv LOCAL0. ss.
      - ii. rewrite PROMISES in *.
        erewrite Memory.bot_get in PROMISE. clarify. } intros PROMS.

    assert (RESERVES: only_reserves e2'.(Thread.local).(Local.promises)).
    { econs.
      - i. destruct msg; auto. exfalso. dup STEPS0.
        eapply pf_step_rtc_promises_decrease in STEPS0; cycle 1.
        { econs; eauto. }
        ss. inv STEPS0.
        unfold no_sc, no_acq_read_msgs in BREAKQ. des_ifs; try by (exfalso; eauto).
        + apply not_and_or in BREAKQ. des; clarify.
          apply imply_to_and in BREAKQ. des. apply NNPP in BREAKQ0.
          unfold caps_loc in *. des. dup CAPS.
          eapply caps_unchangable in CAPS; eauto; cycle 1.
          { inv WF. eauto. }
          eapply unchangable_rtc_increase in STEPS2; eauto. inv STEPS2.
          inv STEP0; inv STEP. ss. inv LOCAL.
          inv LOCAL0. clarify. eapply caps_max_view in CAPS0; eauto; cycle 1.
          { inv WF. eauto. } des.
          clarify. eapply PROMS in GET. ss. des_ifs. ss.
          exploit max_full_timemap_get.
          * apply MAX.
          * inv WF. eapply PROMISES. eauto.
          * i. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt; eauto.
            etrans; eauto. eapply TimeMap.join_r.
        + apply not_and_or in BREAKQ. des; clarify.
          apply imply_to_and in BREAKQ. des. apply NNPP in BREAKQ0.
          unfold caps_loc in *. des. dup CAPS.
          eapply caps_unchangable in CAPS; eauto; cycle 1.
          { inv WF. eauto. }
          eapply unchangable_rtc_increase in STEPS2; eauto. inv STEPS2.
          inv STEP0; inv STEP. ss. inv LOCAL.
          eapply write_step_promise_consistent in LOCAL2; eauto.
          inv LOCAL1. clarify. eapply caps_max_view in CAPS0; eauto; cycle 1.
          { inv WF. eauto. } des.
          clarify. eapply LOCAL2 in GET. ss. des_ifs. ss.
          exploit max_full_timemap_get.
          * apply MAX.
          * inv WF. eapply PROMISES. eauto.
          * i. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt; eauto.
            etrans; eauto. eapply TimeMap.join_r.
        + apply not_and_or in BREAKQ. des; clarify. apply NNPP in BREAKQ.
          inv STEP0; inv STEP. ss. inv LOCAL. inv LOCAL0. ss.
          eapply PROMS in GET. ss. des_ifs. ss.
          hexploit max_full_timemap_get; eauto.
          * inv WF. eapply Memory.cap_le; eauto.
          * i. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt; eauto.
        + inv STEP0; inv STEP. ss. inv LOCAL. inv LOCAL0. ss.
          eapply PROMS in GET. ss. des_ifs. ss.
          hexploit max_full_timemap_get; eauto.
          * inv WF. eapply Memory.cap_le; eauto.
          * i. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt; eauto.
      - inv WF2. eauto. }

    destruct e2'. destruct local. ss.
    eapply pred_step_rtc_mon with (Q:=(promise_free /1\ no_acq_read_msgs (caps_loc (Thread.memory th) (Local.promises (Thread.local th)))) /1\ no_sc) in STEPS0; cycle 1.
    { i. des. esplits; eauto. }
    eapply no_sc_any_sc_rtc in STEPS0; ss. des.
      exploit reserves_cancelable; eauto.
      { inv WF2. eauto. }
      i. des. esplits.
      * etrans.
        { eapply STEP. }
        { eapply pred_step_rtc_mon; eauto.
          unfold is_cancel. i. des_ifs. }
      * ss. eauto.
Qed.


Lemma progressable_in_added_rtc
      lang st lc sc0 sc1 m0 m1 tm
      (CONSISTENT: Thread.consistent (Thread.mk lang st lc sc0 m0))
      (FUTURE: Memory.future m0 m1)
  :
    exists m2 e2,
      (<<ADDED: rtc (added_memory tm) m1 m2>>) /\
      (<<STEPS: rtc (Thread.tau_step (lang:=lang))
                    (Thread.mk _ st lc sc1 m1) e2>>) /\
      (<<PROMISES: Local.promises (Thread.local e2) = Memory.bot>>).
Proof.
Admitted.

Inductive diff_after_promises (prom mem0 mem1: Memory.t)
          (caps: Loc.t -> Time.t -> Time.t -> Message.t -> Prop): Prop :=
| diff_after_promises_intro
    (MLE: Memory.le mem0 mem1)
    (DIFF: forall loc to from msg
                  (GET: Memory.get loc to mem1 = Some (from, msg))
                  (NONE: Memory.get loc to mem0 = None),
        (<<CAP: caps loc to from msg>>) /\
        (exists from' to' val released,
            (<<PROM: Memory.get loc to' prom = Some (from', Message.full val released)>>)) /\
        (<<AFTER: forall from' to' val released
                         (PROM: Memory.get loc to' prom = Some (from', Message.full val released)),
            (<<TLE: Time.le to' from>>) >>))
.

(* Memory.future *)

(* Memory.future_get1 *)

(* Lemma diff_after_promises_step st lc mem0 mem1 caps sc sc' *)
(*       (CONSISTENT: Local.promise_consistent (Local.mk vw prom)) *)

(*       Thread.state *)




(* rtc_tau_step_promise_consistent *)
(*      : forall (lang : language) (th1 th2 : Thread.t lang), *)
(*        rtc (Thread.tau_step (lang:=lang)) th1 th2 -> *)
(*        Local.promise_consistent (Thread.local th2) -> *)
(*        Local.wf (Thread.local th1) (Thread.memory th1) -> *)
(*        Memory.closed_timemap (Thread.sc th1) (Thread.memory th1) -> *)
(*        Memory.closed (Thread.memory th1) -> Local.promise_consistent (Thread.local th1) *)





(* Definition caps (mem0 prom : Memory.t) (l : Loc.t) (t from : Time.t) (msg : Message.t) := *)
(*   forall mem1 (CAP: Memory.cap prom mem0 mem1), *)
(*     (<<GET0: Memory.get l t mem0 = None>>) /\ *)
(*     (<<GET1: Memory.get l t mem1 = Some (from, msg)>>). *)




(* pf_ *)

(* Definition pf_consistent_strong lang (e:Thread.t lang): Prop := *)
(*   forall mem1 sc1 *)
(*          (CAP: Memory.cap e.(Thread.local).(Local.promises) e.(Thread.memory) mem1), *)
(*   exists e2, *)
(*     (<<STEPS: rtc (tau (@pred_step ((promise_free /1\ no_acq_read_msgs (caps_loc e.(Thread.memory) e.(Thread.local).(Local.promises))) /1\ no_sc) lang)) (Thread.mk _ e.(Thread.state) e.(Thread.local) sc1 mem1) e2>>) /\ *)
(*     ((<<FAILURE: Local.failure_step e2.(Thread.local)>>) \/ *)
(*      (<<PROMISES: e2.(Thread.local).(Local.promises) = Memory.bot>>)). *)
