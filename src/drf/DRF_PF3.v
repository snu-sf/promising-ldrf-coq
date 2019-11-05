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

Require Import DRF_PF0.
Require Import DRF_PF1.
Require Import DRF_PF4.
Require Import Mapping.

Require Import PFConsistent.

Set Implicit Arguments.

Definition collapsing_latest_reserves (L: Loc.t -> Prop)
           (mem: Memory.t) (loc: Loc.t) (to: Time.t) (from: Time.t) :=
  (<<LATEST: to = Memory.max_ts loc mem>>) /\
  (<<RESERVE: Memory.get loc to mem = Some (from, Message.reserve)>>) /\
  (<<OTHER: L loc>>)
.

Definition collapsing_latest_reserves_times (L: Loc.t -> Prop)
           (mem: Memory.t) (loc: Loc.t) (to: Time.t): Prop :=
  exists from,
    (<<RESERVE: collapsing_latest_reserves L mem loc to from>>).

Definition collapsing_caps (L: Loc.t -> Prop)
           (mem0 mem1: Memory.t) (loc: Loc.t) (to: Time.t) (from: Time.t) :=
  (<<LATEST: exists val released,
      (<<CAP: caps mem0 mem1 loc to from (Message.full val released)>>)>>) /\
  (<<OTHER: L loc>>)
.

Definition collapsing_caps_times (L: Loc.t -> Prop)
           (mem0 mem1: Memory.t) (loc: Loc.t) (to: Time.t) :=
  exists from,
    (<<CAP: collapsing_caps L mem0 mem1 loc to from>>).

Inductive caps_collapsing (L: Loc.t -> Prop)
          (mem: Memory.t): Loc.t -> Time.t -> Time.t -> Prop :=
| caps_collapsing_not_in
    loc t
    (NSAT: ~ L loc)
  :
    caps_collapsing L mem loc t t
| caps_collapsing_in_memory
    loc t max
    (SAT: L loc)
    (FULL: Memory.max_full_ts mem loc max)
    (TLE: Time.le t max)
  :
    caps_collapsing L mem loc t t
| caps_collapsing_cap
    loc t max
    (SAT: L loc)
    (FULL: Memory.max_full_ts mem loc max)
    (TS0: Time.lt max t)
    (TS1: Time.le t (Time.incr (Memory.max_ts loc mem)))
  :
    caps_collapsing L mem loc t max
| caps_collapsing_outer_memory
    loc t
    (SAT: L loc)
    (TLE: Time.lt (Time.incr (Memory.max_ts loc mem)) t)
  :
    caps_collapsing L mem loc t t
.

Lemma caps_get_reserve mem0 prom mem1 loc to from
      (RESERVE: Memory.reserve_wf prom mem0)
      (CLOSED: Memory.closed mem0)
      (CAP: Memory.cap prom mem0 mem1)
      (CAPS: caps mem0 mem1 loc to from Message.reserve)
  :
    exists from0 to1 msg0 msg1,
      (<<GET0: Memory.get loc from mem0 = Some (from0, msg0)>>) /\
      (<<GET1: Memory.get loc to1 mem0 = Some (to, msg1)>>) /\
      (<<SPACE: forall t (ITV: Interval.mem (from, to) t), ~ covered loc t mem0>>)
.
Proof.
  unfold caps in CAPS. des. inv CAP.
  exploit COMPLETE; eauto. i. des.
  set (@cell_elements_least
         (mem0 loc)
         (fun t => Time.lt from t)). des.
  - hexploit (MIDDLE loc f from from0 to0).
    { econs; eauto. i.
      destruct (Memory.get loc ts mem0) eqn:GET2; auto. destruct p.
      exfalso. exploit LEAST.
      - eapply GET2.
      - eauto.
      - i. exploit Memory.get_ts; try apply GET.
        i. des; clarify.
        + eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
          * eapply SAT.
          * eapply Time.bot_spec.
        + eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt.
          * etrans.
            { eapply x1. }
            { eapply TS2. }
          * eauto. }
    { exploit memory_get_from_mon.
      - eapply x.
      - eapply GET.
      - eauto.
      - i. destruct x2; auto. destruct H. exfalso.
        exploit memory_get_from_inj.
        { eapply SOUND. eapply GET. }
        { eapply GET1. }
        i. des; clarify.
        + setoid_rewrite GET0 in GET. clarify.
        + eapply Time.lt_strorder; eauto. }
    i. exploit memory_get_from_inj.
    { eapply H. }
    { eapply GET1. }
    i. des; clarify.
    + esplits; eauto. ii. inv H0.
      exploit Memory.get_disjoint.
      * eapply SOUND. eapply GET2.
      * eapply H.
      * i. des; clarify. eapply x2; eauto.
    + inv CLOSED. specialize (INHABITED loc).
      eapply SOUND in INHABITED. clarify.
  - exploit Memory.max_ts_spec.
    { eapply x. }
    i. des. destruct MAX.
    + exfalso. eapply EMPTY; eauto.
    + unfold Time.eq in *. subst. exploit x0; auto. intros LATEST.
      exploit Memory.latest_val_exists; eauto.
      { inv CLOSED. eauto. }
      i. des.
      exploit Memory.max_full_view_exists; eauto.
      { inv CLOSED. eauto. } i. des.
      exploit BACK; eauto. i.
      exploit memory_get_from_inj.
      * eapply x1.
      * eapply GET1.
      * i. des; clarify.
        { exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
          - eapply Time.incr_spec.
          - rewrite BOT0. eapply Time.bot_spec. }
        { inv CLOSED. erewrite INHABITED in GET0. clarify. }
Qed.

Lemma max_full_ts_not_collapsed L prom mem0 mem1 loc max
      (INHABITED: Memory.inhabited mem0)
      (CAP: Memory.cap prom mem0 mem1)
      (MAX: Memory.max_full_ts mem0 loc max)
  :
    ~ (collapsing_latest_reserves_times L mem0 \2/ collapsing_caps_times L mem0 mem1) loc max.
Proof.
  ii. des.
  - inv H. inv H0. des. clarify.
    exploit Memory.max_full_ts_spec; eauto. i. des. clarify.
  - inv H. inv H0. des. inv CAP0.
    exploit Memory.max_full_ts_spec; eauto. i. des. clarify.
Qed.

Definition memory_concrete_le (lhs rhs: Memory.t): Prop :=
  forall loc to from val released
         (GET: Memory.get loc to lhs = Some (from, Message.full val released)),
    Memory.get loc to rhs = Some (from, Message.full val released).
Global Program Instance le_PreOrder: PreOrder memory_concrete_le.
Next Obligation. ii. ss. Qed.
Next Obligation. ii. eauto. Qed.

Lemma memory_concrete_le_le
  :
    Memory.le <2= memory_concrete_le.
Proof.
  ii. eauto.
Qed.
Hint Resolve memory_concrete_le_le.

Lemma memory_concrete_le_closed_timemap tm mem0 mem1
      (MLE: memory_concrete_le mem0 mem1)
      (TM: Memory.closed_timemap tm mem0)
  :
    Memory.closed_timemap tm mem1.
Proof.
  ii. hexploit (TM loc). i. des.
  esplits; eauto.
Qed.

Lemma memory_concrete_le_closed_view vw mem0 mem1
      (MLE: memory_concrete_le mem0 mem1)
      (VW: Memory.closed_view vw mem0)
  :
    Memory.closed_view vw mem1.
Proof.
  inv VW. econs.
  - eapply memory_concrete_le_closed_timemap; eauto.
  - eapply memory_concrete_le_closed_timemap; eauto.
Qed.

Lemma memory_concrete_le_closed_opt_view vw mem0 mem1
      (MLE: memory_concrete_le mem0 mem1)
      (VW: Memory.closed_opt_view vw mem0)
  :
    Memory.closed_opt_view vw mem1.
Proof.
  inv VW; econs.
  eapply memory_concrete_le_closed_view; eauto.
Qed.

Lemma memory_concrete_le_closed_msg msg mem0 mem1
      (MLE: memory_concrete_le mem0 mem1)
      (MSG: Memory.closed_message msg mem0)
  :
    Memory.closed_message msg mem1.
Proof.
  inv MSG; econs.
  eapply memory_concrete_le_closed_opt_view; eauto.
Qed.

Lemma memory_concrete_le_closed_tview vw mem0 mem1
      (MLE: memory_concrete_le mem0 mem1)
      (VW: TView.closed vw mem0)
  :
    TView.closed vw mem1.
Proof.
  inv VW. econs.
  - i. eapply memory_concrete_le_closed_view; eauto.
  - eapply memory_concrete_le_closed_view; eauto.
  - eapply memory_concrete_le_closed_view; eauto.
Qed.

Lemma memory_concrete_le_reserve_wf prom mem0 mem1
      (MLE: memory_concrete_le mem0 mem1)
      (RESERVE: Memory.reserve_wf prom mem0)
  :
    Memory.reserve_wf prom mem1.
Proof.
  ii. eapply RESERVE in GET. des.
  esplits; eauto.
Qed.

Lemma memory_concrete_le_local_wf lc mem0 mem1
      (MLE: memory_concrete_le mem0 mem1)
      (PROM: Memory.le (Local.promises lc) mem1)
      (LOCAL: Local.wf lc mem0)
  :
    Local.wf lc mem1.
Proof.
  inv LOCAL. econs; eauto.
  - eapply memory_concrete_le_closed_tview; eauto.
  - eapply memory_concrete_le_reserve_wf; eauto.
Qed.

Lemma partial_cap_closed prom mem0 mem1 mem2
      (MLE: Memory.le prom mem0)
      (CLOSED: Memory.closed mem0)
      (RESERVEWF: Memory.reserve_wf prom mem0)
      (CAP: Memory.cap prom mem0 mem2)
      (MLE0: Memory.le mem0 mem1)
      (MLE1: Memory.le mem1 mem2)
  :
    Memory.closed mem1.
Proof.
  exploit Memory.max_full_timemap_exists; eauto.
  { inv CLOSED. auto. }
  intros [tm MAX].
  inv CLOSED. econs; eauto.
  i. destruct (Memory.get loc to mem0) as [[from0 msg0]|] eqn:GET.
  - dup GET. eapply MLE0 in GET. clarify.
    eapply CLOSED0 in GET0. des. esplits; eauto.
    eapply memory_concrete_le_closed_msg; eauto.
  - destruct msg.
    + eapply MLE1 in MSG.
      exploit caps_max_view; eauto.
      * econs; eauto.
      * i. des; clarify. esplits; eauto.
        { econs; eauto. econs; eauto. econs. refl. }
        { econs; eauto. ss. transitivity (Memory.max_ts loc mem0).
          - specialize (MAX loc). inv MAX. des.
            eapply Memory.max_ts_spec in GET0. des. eauto.
          - left. eapply Time.incr_spec. }
        { eapply memory_concrete_le_closed_msg; eauto.
          econs. econs. econs.
          - eapply Memory.max_full_timemap_closed; eauto.
          - eapply Memory.max_full_timemap_closed; eauto. }
    + esplits; eauto. econs.
Qed.

Lemma collapsing_caps_forget_le
      mem0 mem1 mem2 prom (L: Loc.t -> Prop)
      (CAP: Memory.cap prom mem0 mem2)
      (FORGET: forget_memory (collapsing_latest_reserves_times L mem0 \2/ collapsing_caps_times L mem0 mem2) mem1 mem2)
  :
    memory_concrete_le mem0 mem1.
Proof.
  inv FORGET. ii.
  erewrite COMPLETE.
  - eapply Memory.cap_le in CAP; eauto. refl.
  - ii. des.
    + unfold collapsing_latest_reserves_times in *. des.
      inv RESERVE. des. clarify.
    + unfold collapsing_caps_times in *. des.
      inv CAP0. des. unfold caps in CAP0. des. clarify.
Qed.

Definition collapsable_cap (L: Loc.t -> Prop) (prom mem: Memory.t): Prop :=
  forall
    loc (SAT: L loc)
    from msg
    (GET: Memory.get loc (Memory.max_ts loc mem) prom = Some (from, msg)),
    msg <> Message.reserve.

Lemma collapsing_caps_forget_prom_le
      mem0 mem1 mem2 prom (L: Loc.t -> Prop)
      (COLLAPSABLE: collapsable_cap L prom mem0)
      (MLE: Memory.le prom mem0)
      (CLOSED: Memory.closed mem0)
      (RESERVEWF: Memory.reserve_wf prom mem0)
      (CAP: Memory.cap prom mem0 mem2)
      (FORGET: forget_memory (collapsing_latest_reserves_times L mem0 \2/ collapsing_caps_times L mem0 mem2) mem1 mem2)
  :
    Memory.le prom mem1.
Proof.
  inv FORGET. ii.
  erewrite COMPLETE.
  - eapply Memory.cap_le in CAP; eauto.
  - ii. des.
    + unfold collapsing_latest_reserves_times in *. des.
      inv RESERVE. des. clarify.
      dup LHS. eapply MLE in LHS0. clarify.
      eapply COLLAPSABLE in OTHER. eapply OTHER in LHS. clarify.
    + unfold collapsing_caps_times in *. des.
      inv CAP0. des. unfold caps in CAP0. des.
      eapply MLE in LHS; eauto. clarify.
Qed.

Lemma identity_mapped_view tm maxmap (f: Loc.t -> Time.t -> Time.t -> Prop)
      (TM: TimeMap.le tm maxmap)
      (IDENT: forall loc ts (TS: Time.le ts (maxmap loc)), f loc ts ts)
  :
    timemap_map f tm tm.
Proof.
  ii. eapply IDENT; eauto.
Qed.

Lemma caps_collapsing_ident L mem loc maxts ts
      (MAX: Memory.max_full_ts mem loc maxts)
      (TS: Time.le ts maxts)
  :
    (caps_collapsing L mem) loc ts ts.
Proof.
  i. destruct (classic (L loc)).
  - econs 2; eauto.
  - econs 1; eauto.
Qed.

Lemma not_latest_reserve_le_max_full_ts loc mem ts to from msg
      (RESERVEWF : memory_reserve_wf mem)
      (INHABITED : Memory.inhabited mem)
      (MAX : Memory.max_full_ts mem loc ts)
      (GET: Memory.get loc to mem = Some (from, msg))
  :
    (<<TLE: Time.le to ts>>) \/
    ((<<TO: to = Memory.max_ts loc mem>>) /\
     (<<FROM: from = ts>>) /\
     (<<MSG: msg = Message.reserve>>)).
Proof.
  inv MAX. des.
  destruct msg.
  - left. eapply MAX0; eauto.
  - exploit RESERVEWF; eauto. i. des.
    destruct (TimeFacts.le_lt_dec to ts); auto.
    dup x. eapply MAX0 in x; eauto. destruct x.
    + exfalso. exploit memory_get_from_mon.
      { eapply GET0. }
      { eapply GET. }
      { auto. }
      i. eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt.
      * eapply x1.
      * eapply H.
    + unfold Time.eq in *. subst. right. esplits; eauto.
      setoid_rewrite GET0 in x0. clarify.
      dup GET. eapply Memory.max_ts_spec in GET1. des.
      destruct MAX; auto. exfalso.
      destruct msg.
      * eapply MAX0 in GET2. eapply Time.lt_strorder.
        eapply TimeFacts.lt_le_lt.
        { etrans.
          - eapply l.
          - eapply H. }
        { eauto. }
      * dup GET2. eapply RESERVEWF in GET2. des.
        eapply MAX0 in GET2.
        exploit memory_get_from_mon.
        { eapply GET. }
        { eapply GET1. }
        { eapply H. }
        i. eapply Time.lt_strorder.
        eapply TimeFacts.lt_le_lt.
        { eapply l. }
        { etrans.
          - eapply x0.
          - eapply Memory.get_ts in GET1. des; clarify. }
Qed.

Lemma caps_collapsing_ident2 L mem maxts loc ts fts
      (MAX: Memory.max_full_ts mem loc maxts)
      (TS: Time.le ts maxts)
      (MAP: (caps_collapsing L mem) loc ts fts)
  :
    ts = fts.
Proof.
  inv MAP; eauto.
  exploit Memory.max_full_ts_inj.
  { eapply FULL. }
  { eapply MAX. } i. clarify.
  exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
  { eapply TS0. }
  { eapply TS. }
Qed.

Lemma caps_collapsing_ident3 L mem maxts loc ts fts
      (RESERVEWF : memory_reserve_wf mem)
      (INHABITED : Memory.inhabited mem)
      (MAX: Memory.max_full_ts mem loc maxts)
      (TS: Time.lt fts maxts)
      (MAP: (caps_collapsing L mem) loc ts fts)
  :
    ts = fts.
Proof.
  inv MAP; eauto.
  exploit Memory.max_full_ts_inj.
  { eapply FULL. }
  { eapply MAX. }
  i. clarify. exfalso. eapply Time.lt_strorder; eauto.
Qed.

Lemma caps_collapsing_timemap L mem tm
      (INHABITED: Memory.inhabited mem)
      (TM: Memory.closed_timemap tm mem)
  :
    timemap_map (caps_collapsing L mem) tm tm.
Proof.
  exploit Memory.max_full_timemap_exists; eauto. intros [maxmap MAX].
  eapply identity_mapped_view.
  - eapply Memory.max_full_timemap_spec; eauto.
  - i. eapply caps_collapsing_ident; eauto.
Qed.

Lemma caps_collapsing_view L mem vw
      (INHABITED: Memory.inhabited mem)
      (VW: Memory.closed_view vw mem)
  :
    view_map (caps_collapsing L mem) vw vw.
Proof.
  inv VW. econs.
  - eapply caps_collapsing_timemap; eauto.
  - eapply caps_collapsing_timemap; eauto.
Qed.

Lemma caps_collapsing_opt_view L mem vw
      (INHABITED: Memory.inhabited mem)
      (VW: Memory.closed_opt_view vw mem)
  :
    opt_view_map (caps_collapsing L mem) vw vw.
Proof.
  inv VW; econs.
  eapply caps_collapsing_view; eauto.
Qed.

Lemma caps_collapsing_message L mem msg
      (INHABITED: Memory.inhabited mem)
      (MSG: Memory.closed_message msg mem)
  :
    msg_map (caps_collapsing L mem) msg msg.
Proof.
  inv MSG; econs.
  eapply caps_collapsing_opt_view; eauto.
Qed.

Lemma caps_collapsing_tview L mem vw
      (INHABITED: Memory.inhabited mem)
      (VW: TView.closed vw mem)
  :
    tview_map (caps_collapsing L mem) vw vw.
Proof.
  inv VW. econs.
  - i. eapply caps_collapsing_view; eauto.
  - eapply caps_collapsing_view; eauto.
  - eapply caps_collapsing_view; eauto.
Qed.

Lemma memory_cap_message_closed prom mem0 mem1
      (CLOSED: Memory.closed mem0)
      (CAP: Memory.cap prom mem0 mem1)
      loc to from msg
      (GET: Memory.get loc to mem1 = Some (from, msg))
  :
    Memory.closed_message msg mem0.
Proof.
  eapply Memory.cap_inv in GET; eauto. des.
  - eapply CLOSED in GET. des; auto.
  - clarify.
  - clarify. econs. econs.
    eapply Memory.max_full_view_closed; eauto.
Qed.

Lemma caps_collapsing_promises (L: Loc.t -> Prop) mem prom
      (MLE: Memory.le prom mem)
      (CLOSED: Memory.closed mem)
      (RESERVEWF: memory_reserve_wf mem)
      (COLLAPSABLE: collapsable_cap L prom mem)
  :
    promises_map (caps_collapsing L mem) prom prom.
Proof.
  exploit Memory.max_full_timemap_exists; eauto.
  { inv CLOSED. eauto. }
  intros [tm MAX].
  dup CLOSED. inv CLOSED0. econs.
  - i. dup GET. eapply MLE in GET0. eapply CLOSED1 in GET0. des.
    exists to, from, msg.
    destruct (classic (L loc)).
    + dup GET. eapply MLE in GET0.
      eapply not_latest_reserve_le_max_full_ts in GET0; eauto.
      eapply or_strengthen in GET0. des; clarify.
      * esplits; eauto.
        { ii. unfold collapsed in *. des.
          eapply caps_collapsing_ident2 in MAP1; eauto; cycle 1.
          eapply caps_collapsing_ident2 in MAP0; eauto; cycle 1.
          { etrans; eauto. left. auto. } clarify.
          eapply Time.lt_strorder; eauto. }
        { econs 2; eauto. }
        { eapply caps_collapsing_message; eauto. }
      * exfalso. exploit COLLAPSABLE; eauto.
    + splits; auto.
      * ii. unfold collapsed in *. des.
        inv MAP0; clarify. inv MAP1; clarify.
        eapply Time.lt_strorder. eauto.
      * econs 1; eauto.
      * eapply caps_collapsing_message; eauto.
  - i. exists fto, ffrom, fmsg.
    destruct (classic (L loc)).
    + dup GET. eapply MLE in GET.
      eapply not_latest_reserve_le_max_full_ts in GET; eauto.
      des; clarify.
      * splits; auto.
        { eapply caps_collapsing_ident; eauto. }
        { eapply caps_collapsing_ident; eauto.
          etrans; eauto.
          eapply memory_get_ts_strong in GET0. des; clarify.
          { refl. }
          { left. auto. } }
      * exfalso. exploit COLLAPSABLE; eauto.
    + splits; auto.
      * econs 1; eauto.
      * econs 1; eauto.
Qed.

Lemma caps_collapsing_memory' (L0 L1: Loc.t -> Prop)
      mem0 mem1 mem2 mem3 prom
      (MLE: Memory.le prom mem0)
      (CLOSED: Memory.closed mem0)
      (RESERVEWF0: memory_reserve_wf mem0)
      (RESERVEWF1: Memory.reserve_wf prom mem0)
      (COLLAPSABLE0: collapsable_cap L0 prom mem0)
      (COLLAPSABLE1: collapsable_cap L1 prom mem0)
      (CAP: Memory.cap prom mem0 mem1)
      (FORGET0: forget_memory (collapsing_latest_reserves_times L0 mem0 \2/ collapsing_caps_times L0 mem0 mem1) mem2 mem1)
      (FORGET1: forget_memory (collapsing_latest_reserves_times L1 mem0 \2/ collapsing_caps_times L1 mem0 mem1) mem3 mem2)
  :
    memory_map (caps_collapsing L1 mem0) mem2 mem3.
Proof.
  exploit Memory.max_full_timemap_exists; eauto.
  { inv CLOSED. eauto. }
  intros [tm MAX].
  dup FORGET0. inv FORGET0. dup FORGET1. inv FORGET1.
  dup CLOSED. inv CLOSED0. econs.
  - i. dup GET. eapply forget_memory_get in GET0; eauto. des.
    destruct (classic (L1 loc)).
    + destruct (classic ((collapsing_latest_reserves_times L1 mem0 \2/ collapsing_caps_times L1 mem0 mem1) loc to)).
      * des.
        { inv H0. inv H1. des. clarify.
          dup RESERVE. eapply Memory.cap_le in RESERVE0; eauto; [|refl]. clarify.
          replace from with (tm loc) in *; cycle 1.
          { eapply Memory.max_full_ts_inj; eauto.
            eapply max_ts_reserve_from_full_ts; eauto. }
          dup RESERVE0. eapply RESERVEWF0 in RESERVE. des.
          eapply Memory.cap_le in RESERVE; eauto. refl.
        }
        { inv H0. inv H1. des.
          dup CAP0. eapply caps_max_view in CAP0; eauto. des. clarify.
          unfold caps in CAP1. des. clarify.
          inv VAL.
          exploit Memory.max_full_ts_inj.
          { eapply MAX0. }
          { eapply MAX. } i. clarify.
          exploit Memory.max_full_ts_spec; eauto. i. des. clarify. right.
          exists (tm loc), from, (Message.full val (Some (View.mk tm tm))), (Message.full val released).
          splits.
          - econs 3; eauto.
            { eapply TimeFacts.le_lt_lt.
              - eapply max_full_ts_le_max_ts; eauto.
              - eapply DenseOrder.DenseOrder.incr_spec. }
            { refl. }
          - eapply caps_collapsing_message; eauto. econs. econs.
            eapply Memory.max_full_view_closed. econs; eauto.
          - econs. eapply CLOSED1 in GET3. des. inv MSG_CLOSED.
            inv CLOSED0; eauto. inv CLOSED2. econs. econs; ss.
            + eapply Memory.max_full_timemap_spec; eauto.
            + eapply Memory.max_full_timemap_spec; eauto.
          - erewrite COMPLETE0; eauto.
            + erewrite COMPLETE; eauto.
              * eapply Memory.cap_le in GET3; eauto. refl.
              * eapply max_full_ts_not_collapsed; eauto.
            + eapply max_full_ts_not_collapsed; eauto. }
      * apply not_or_and in H0. des.
        assert (TS: Time.le to (tm loc)).
        { dup GET1. eapply Memory.cap_inv in GET1; eauto. des; clarify.
          - dup GET1. eapply not_latest_reserve_le_max_full_ts in GET1; eauto.
            des; clarify. exfalso. eapply H0. econs; eauto. econs; eauto.
          - inv GET2. dup GET5. eapply not_latest_reserve_le_max_full_ts in GET5; eauto.
            des; clarify.
            + eapply memory_get_ts_le in GET2. etrans; eauto.
            + refl.
          - exfalso. eapply H1. econs; eauto. econs; eauto.
            esplits; eauto. econs; eauto. }
        right. exists to, from, msg, msg. splits; auto.
        { econs 2; eauto. }
        { eapply caps_collapsing_message; eauto.
          eapply memory_cap_message_closed; eauto. }
        { refl. }
        { erewrite COMPLETE0; eauto. ii. des; clarify. }
    + right. exists to, from, msg, msg. esplits; eauto.
      * econs 1; eauto.
      * eapply caps_collapsing_message; eauto.
        eapply memory_cap_message_closed in GET1; eauto.
      * refl.
      * erewrite COMPLETE0; eauto. ii. des.
        { inv H0. inv H1. des. clarify. }
        { inv H0. inv H1. des. clarify. }
  - i. dup GET. eapply forget_memory_get in GET0; eauto. des.
    apply not_or_and in NOT. des.
    exists fto, ffrom, fmsg. destruct (classic (L1 loc)).
    + assert (TS: Time.le fto (tm loc)).
      { dup GET1. eapply forget_memory_get in GET1; eauto. des.
        dup GET2. eapply Memory.cap_inv in GET2; eauto. des; clarify.
        - dup GET2. eapply not_latest_reserve_le_max_full_ts in GET2; eauto.
          des; clarify. exfalso. eapply NOT. econs; eauto. econs; eauto.
        - inv GET3. dup GET6. eapply not_latest_reserve_le_max_full_ts in GET6; eauto.
          des; clarify.
          + eapply memory_get_ts_le in GET3. etrans; eauto.
          + refl.
        - exfalso. eapply NOT0. econs; eauto. econs; eauto.
          esplits; eauto. econs; eauto. }
      splits; auto.
      * econs 2; eauto.
      * econs 2; eauto. etrans; eauto.
        eapply memory_get_ts_le; eauto.
    + splits; auto.
      * econs 1; eauto.
      * econs 1; eauto.
Qed.

(* TODO: move it to DRF_PF0 *)
Lemma bot_forget P mem0
      (BOT: P <2= bot2)
  :
    forget_memory P mem0 mem0.
Proof.
  econs; eauto. i. eapply BOT in PROMS. clarify.
Qed.

Lemma caps_collapsing_memory
      mem0 mem1 mem2 prom (L: Loc.t -> Prop)
      (MLE: Memory.le prom mem0)
      (CLOSED: Memory.closed mem0)
      (RESERVEWF0: memory_reserve_wf mem0)
      (RESERVEWF1: Memory.reserve_wf prom mem0)
      (COLLAPSABLE: collapsable_cap L prom mem0)
      (CAP: Memory.cap prom mem0 mem1)
      (FORGET: forget_memory (collapsing_latest_reserves_times L mem0 \2/ collapsing_caps_times L mem0 mem1) mem2 mem1)
  :
    memory_map (caps_collapsing L mem0) mem1 mem2.
Proof.
  eapply (@caps_collapsing_memory' bot1); eauto.
  - ii. clarify.
  - eapply bot_forget. i.
    unfold collapsing_latest_reserves_times, collapsing_caps_times,
    collapsing_latest_reserves, collapsing_caps in PR. des; clarify.
Qed.

(* Definition memory_last_reserves (prom mem: Memory.t) := (fun loc => Memory.latest_reserve loc prom mem). *)

Definition pf_consistent_drf' lang (e0:Thread.t lang): Prop :=
  let L := (fun loc => Memory.latest_reserve loc e0.(Thread.local).(Local.promises) e0.(Thread.memory)) in
  forall mem1 mem2
         (CAP: Memory.cap e0.(Thread.local).(Local.promises) e0.(Thread.memory) mem1)
         (FORGET: forget_memory (collapsing_latest_reserves_times L e0.(Thread.memory) \2/ collapsing_caps_times L e0.(Thread.memory) mem1) mem2 mem1),
  exists e1,
    (<<STEPS0: rtc (tau (@pred_step is_cancel lang)) (Thread.mk _ e0.(Thread.state) e0.(Thread.local) TimeMap.bot mem2) e1>>) /\
    (<<NORESERVE: no_reserves e1.(Thread.local).(Local.promises)>>) /\
    exists e2,
      (<<STEPS1: rtc (tau (@pred_step ((promise_free /1\ (fun e => ~ is_cancel e) /1\ no_acq_update_msgs ((fun loc to => L loc) /2\ Memory.max_full_ts e0.(Thread.memory))) /1\ no_sc) lang)) e1 e2>>) /\
      (__guard__((<<FAILURE: Local.failure_step e2.(Thread.local)>>) \/
                 (<<PROMISES: e2.(Thread.local).(Local.promises) = Memory.bot>>))).

Lemma caps_collapsing_collapsable_unwritable L prom mem0 mem1
      (MLE: Memory.le prom mem0)
      (RESERVEWF : memory_reserve_wf mem0)
      (INHABITED : Memory.inhabited mem0)
      (COLLAPSABLE: collapsable_cap L prom mem0)
      (CAP: Memory.cap prom mem0 mem1)
  :
    collapsable_unwritable (caps_collapsing L mem0) prom mem1.
Proof.
  ii. des. unfold collapsed in *. des. inv ITV. ss.
  inv MAP0; inv MAP1; clarify.
  - exfalso; eapply Time.lt_strorder; eapply TimeFacts.lt_le_lt; eauto.
  - exfalso; eapply Time.lt_strorder; eapply TimeFacts.lt_le_lt; eauto.
  - exploit Memory.max_full_ts_inj; [apply FULL|apply FULL0|i; clarify].
    inv CAP. destruct (Time.le_lt_dec t (Memory.max_ts loc mem0)).
    + exploit max_full_ts_max_ts; eauto. i. des; clarify.
      * clear - FROM l.
        exfalso; eapply Time.lt_strorder; eapply TimeFacts.lt_le_lt; eauto.
      * econs; eauto.
        { econs; eauto.
          destruct (Memory.get loc (Memory.max_ts loc mem0) prom) eqn:GETPROM; eauto.
          exfalso. destruct p as [from []].
          - eapply MLE in GETPROM. clarify.
          - eapply COLLAPSABLE in GETPROM; eauto. }
        { econs; ss. }
    + exploit Memory.latest_val_exists; eauto. i. des.
      exploit Memory.max_full_view_exists; eauto. i. des.
      exploit BACK; eauto.
      { instantiate (1:=loc). unfold Memory.latest_reserve. des_ifs.
        eapply COLLAPSABLE in Heq; eauto. }
      i. econs; eauto.
      * econs; eauto.
        destruct (Memory.get loc (Time.incr (Memory.max_ts loc mem0)) prom) eqn:GETPROM; eauto.
        exfalso. destruct p as [from msg].
        eapply MLE in GETPROM.
        eapply Memory.max_ts_spec in GETPROM; eauto. des.
        exfalso; eapply Time.lt_strorder; eapply TimeFacts.lt_le_lt; eauto.
      * econs; eauto.
  - clear - FROM TO. exfalso; eapply Time.lt_strorder; eapply TimeFacts.lt_le_lt; eauto.
  - exploit Memory.max_full_ts_inj; [apply FULL|apply FULL0|i; clarify].
    exfalso; eapply Time.lt_strorder; eapply TimeFacts.le_lt_lt.
    { eapply TO. }
    etrans; eauto.
  - exploit Memory.max_full_ts_inj; [apply FULL|apply FULL0|i; clarify].
    inv CAP. destruct (Time.le_lt_dec t (Memory.max_ts loc mem0)).
    + exploit max_full_ts_max_ts; eauto. i. des; clarify.
      * clear - FROM TS0 l.
        exfalso; eapply Time.lt_strorder; eapply TimeFacts.lt_le_lt; eauto.
        etrans; eauto. left. auto.
      * econs; eauto.
        { econs; eauto.
          destruct (Memory.get loc (Memory.max_ts loc mem0) prom) eqn:GETPROM; eauto.
          exfalso. destruct p as [from []].
          - eapply MLE in GETPROM. clarify.
          - eapply COLLAPSABLE in GETPROM; eauto. }
        { econs; ss. clear - FROM TS0. etrans; eauto. }
    + exploit Memory.latest_val_exists; eauto. i. des.
      exploit Memory.max_full_view_exists; eauto. i. des.
      exploit BACK; eauto.
      { instantiate (1:=loc). unfold Memory.latest_reserve. des_ifs.
        eapply COLLAPSABLE in Heq; eauto. }
      i. econs; eauto.
      * econs; eauto.
        destruct (Memory.get loc (Time.incr (Memory.max_ts loc mem0)) prom) eqn:GETPROM; eauto.
        exfalso. destruct p as [from msg].
        eapply MLE in GETPROM.
        eapply Memory.max_ts_spec in GETPROM; eauto. des.
        exfalso; eapply Time.lt_strorder; eapply TimeFacts.lt_le_lt; eauto.
      * econs; eauto.
  - exfalso; eapply Time.lt_strorder; eapply TimeFacts.le_lt_lt; eauto.
  - clear - FROM TO. exfalso; eapply Time.lt_strorder; eapply TimeFacts.lt_le_lt; eauto.
  - exfalso; eapply Time.lt_strorder; eapply TimeFacts.le_lt_lt.
    { eapply TS1. }
    etrans; eauto.
  - clear - FROM TO. exfalso; eapply Time.lt_strorder; eapply TimeFacts.lt_le_lt; eauto.
Qed.

Lemma caps_collapsing_mapping_map_le L prom mem0 mem1
      (COLLAPSABLE: collapsable_cap L prom mem0)
      (CAP: Memory.cap prom mem0 mem1)
  :
    mapping_map_le (caps_collapsing L mem0).
Proof.
  ii. inv MAP0; inv MAP1; clarify.
  - exploit Memory.max_full_ts_inj; [apply FULL|apply FULL0|i; clarify].
  - etrans; eauto. left. auto.
  - exploit Memory.max_full_ts_inj; [apply FULL|apply FULL0|i; clarify]. refl.
  - etrans; eauto. left. auto.
  - exfalso; eapply Time.lt_strorder; eapply TimeFacts.lt_le_lt.
    { eapply TLE. }
    etrans; eauto.
Qed.

Lemma caps_collapsing_mapping_map_bot L prom mem0 mem1
      (COLLAPSABLE: collapsable_cap L prom mem0)
      (INHABITED: Memory.inhabited mem0)
      (CAP: Memory.cap prom mem0 mem1)
  :
    mapping_map_bot (caps_collapsing L mem0).
Proof.
  ii. destruct (classic (L loc)).
  - exploit Memory.max_full_ts_exists; eauto. i. des.
    econs 2; eauto. eapply Time.bot_spec.
  - econs 1; eauto.
Qed.

Lemma caps_collapsing_mapping_map_eq L prom mem0 mem1
      (COLLAPSABLE: collapsable_cap L prom mem0)
      (CAP: Memory.cap prom mem0 mem1)
  :
    mapping_map_eq (caps_collapsing L mem0).
Proof.
  ii. inv MAP0; inv MAP1; clarify.
  - exploit Memory.max_full_ts_inj; [apply FULL|apply FULL0|i; clarify].
    exfalso; eapply Time.lt_strorder; eapply TimeFacts.lt_le_lt; eauto.
  - exploit Memory.max_full_ts_inj; [apply FULL|apply FULL0|i; clarify].
    exfalso; eapply Time.lt_strorder; eapply TimeFacts.le_lt_lt; eauto.
  - exploit Memory.max_full_ts_inj; [apply FULL|apply FULL0|i; clarify].
  - exfalso; eapply Time.lt_strorder; eapply TimeFacts.lt_le_lt; eauto.
  - clear - TLE TS1. exfalso; eapply Time.lt_strorder; eapply TimeFacts.lt_le_lt; eauto.
Qed.

Lemma caps_collapsing_total L mem0 loc to
      (INHABITED: Memory.inhabited mem0)
  :
    exists fto,
      <<MAP: caps_collapsing L mem0 loc to fto >>.
Proof.
  destruct (classic (L loc)).
  - exploit Memory.max_full_ts_exists; eauto. i. des.
    destruct (Time.le_lt_dec to ts).
    { eexists. econs 2; eauto. }
    destruct (Time.le_lt_dec to (Time.incr (Memory.max_ts loc mem0))).
    { eexists. econs 3; eauto. }
    { eexists. econs 4; eauto. }
  - eexists. econs 1; eauto.
Qed.

Lemma caps_collapsing_mappable_time_always L mem0
      (INHABITED: Memory.inhabited mem0)
      loc to
  :
    mappable_time (caps_collapsing L mem0) loc to.
Proof.
  eapply caps_collapsing_total; eauto.
Qed.

Lemma caps_collapsing_mappable_event_always L mem0
      (INHABITED: Memory.inhabited mem0)
      e
  :
    mappable_evt (caps_collapsing L mem0) e.
Proof.
  destruct e; ss; split; (apply caps_collapsing_mappable_time_always; auto).
Qed.

Lemma collapsing_caps_forget_closed
      mem0 mem1 mem2 prom (L: Loc.t -> Prop)
      (CLOSED: Memory.closed mem0)
      (CAP: Memory.cap prom mem0 mem2)
      (FORGET: forget_memory (collapsing_latest_reserves_times L mem0 \2/ collapsing_caps_times L mem0 mem2) mem1 mem2)
  :
    Memory.closed mem1.
Proof.
  hexploit collapsing_caps_forget_le; eauto. intros MLE.
  inv CLOSED.
  econs.
  - ii. eapply forget_memory_get in MSG; eauto. des.
    eapply Memory.cap_inv in GET; try apply CAP; eauto. des; clarify.
    + eapply CLOSED0 in GET; eauto. des. splits; auto.
      eapply memory_concrete_le_closed_msg; eauto.
    + split; auto. econs.
    + splits; auto.
      * econs; eauto. econs. eapply Memory.max_full_view_wf; eauto.
      * econs; eauto. ss. inv GET4. ss. etrans.
        { eapply max_full_ts_le_max_ts; eauto. }
        { left. eapply Time.incr_spec. }
      * eapply memory_concrete_le_closed_msg; eauto.
        econs; eauto. econs.
        eapply Memory.max_full_view_closed; eauto.
  - ii. eauto.
Qed.

Lemma pf_consistent_pf_consistent_drf' lang (th: Thread.t lang)
      (WF: Local.wf th.(Thread.local) th.(Thread.memory))
      (MEM: Memory.closed th.(Thread.memory))
      (CONSISTENT: pf_consistent_strong th)
      (RESERVEWF: memory_reserve_wf (Thread.memory th))
  :
    pf_consistent_drf' th.
Proof.
  assert (INHABITED: Memory.inhabited th.(Thread.memory)).
  { inv MEM. auto. }
  ii.
  set (L:=fun loc : Loc.t =>
                      Memory.latest_reserve loc (Local.promises (Thread.local th)) (Thread.memory th)).
  assert (COLLAPSABLE: collapsable_cap L (Local.promises (Thread.local th)) (Thread.memory th)).
  { ii. clarify. unfold L, Memory.latest_reserve in SAT.
    rewrite GET in SAT. clarify. }
  assert (MAPLE: mapping_map_le (caps_collapsing L th.(Thread.memory))).
  { eapply caps_collapsing_mapping_map_le; eauto. }
  assert (MAPBOT: mapping_map_bot (caps_collapsing L th.(Thread.memory))).
  { eapply caps_collapsing_mapping_map_bot; eauto. }
  assert (MAPEQ: mapping_map_eq (caps_collapsing L th.(Thread.memory))).
  { eapply caps_collapsing_mapping_map_eq; eauto. }
  assert (CONCRETELE: memory_concrete_le th.(Thread.memory) mem2).
  { eapply collapsing_caps_forget_le; eauto. }

  exploit CONSISTENT; eauto. i. des.

  assert (WFTGT: Local.wf (Thread.local th) mem1).
  { eapply Local.cap_wf; eauto. }
  assert (CLOSEDTGT: Memory.closed mem1).
  { eapply Memory.cap_closed; eauto. }
  assert (CLOSEDSRC: Memory.closed mem2).
  { eapply collapsing_caps_forget_closed; cycle 1; eauto. }
  assert (LCWFSRC: Local.wf th.(Thread.local) mem2).
  { eapply memory_concrete_le_local_wf; eauto. inv WF.
    eapply collapsing_caps_forget_prom_le; eauto. }

  assert (SCSRC: Memory.closed_timemap TimeMap.bot mem2).
  { eapply Memory.closed_timemap_bot; eauto. }
  assert (SCTGT: Memory.closed_timemap TimeMap.bot mem1).
  { eapply Memory.closed_timemap_bot; eauto.
    ii. eapply Memory.cap_le; eauto. refl. }
  assert (UNWRITABLE: collapsable_unwritable
                        (caps_collapsing L (Thread.memory th))
                        (Local.promises (Thread.local th)) mem1).
  { inv WF. eapply caps_collapsing_collapsable_unwritable; eauto. }

  destruct e1.
  hexploit (@steps_map (caps_collapsing L (Thread.memory th))); try apply STEPS0; auto; eauto.
  { i. eapply caps_collapsing_mappable_event_always; eauto. }
  { econs.
    - refl.
    - eapply caps_collapsing_tview; eauto. inv WF. eauto.
    - eapply caps_collapsing_promises; eauto. inv WF. eauto. }
  { inv WF. eapply caps_collapsing_memory; try apply FORGET; eauto. }
  { eapply timemap_bot_map; eauto. }
  { refl. }
  { instantiate (1:=is_cancel). ii. inv REL; ss. inv KIND; ss. }
  i. des.

  exploit Thread.rtc_tau_step_future.
  { eapply thread_steps_pred_steps. eapply STEPS0. } all: eauto. i. des. ss.
  exploit Thread.rtc_tau_step_future.
  { eapply thread_steps_pred_steps. eapply STEP. } all: eauto. i. des. ss.

  destruct e2.
  eapply steps_write_not_in in STEPS1; cycle 1.
  { inv WF2. ss. }
  eapply steps_wf_event in STEPS1; cycle 1.
  { inv CLOSED2. ss. }

  hexploit (@steps_map (caps_collapsing L (Thread.memory th))); try apply STEPS1; auto; eauto.
  { i. eapply caps_collapsing_mappable_event_always; eauto. }
  { eapply collapsable_unwritable_steps in STEPS0; eauto. }
  { instantiate (1:=(promise_free /1\ (fun e => ~ is_cancel e) /1\ no_acq_update_msgs ((fun loc to => L loc) /2\ Memory.max_full_ts th.(Thread.memory))) /1\ no_sc).
    ss. ii. des. inv REL; splits; ss; eauto.
    - inv KIND; ss. inv MSG0; ss. inv MSG; ss. inv MAP0; ss.
    - inv KIND; ss.
    - ii. des.
      specialize (SAT1 (Time.meet to (Time.incr (Memory.max_ts loc (Thread.memory th))))).
      inv FROM.
      + clarify.
      + exploit Memory.max_full_ts_inj; [apply SAT6|apply FULL|i; clarify].
        assert (TS: Time.lt max (Time.incr (Memory.max_ts loc (Thread.memory th)))).
        { eapply TimeFacts.le_lt_lt.
          { eapply max_full_ts_le_max_ts; eauto. }
          { eapply Time.incr_spec. } }
        assert (UNWRITABLE0: unwritable memory (Local.promises local) loc (Time.meet to (Time.incr (Memory.max_ts loc (Thread.memory th))))).
        { exploit rtc_unwritable_increase; [| |].
          - eapply thread_steps_pred_steps. eapply STEPS0.
          - ss. eapply UNWRITABLE.
            eexists max, (Time.incr (Memory.max_ts loc (Thread.memory th))). splits; eauto.
            + eexists. splits.
              * econs 2; eauto.
              * econs 3; eauto. refl.
            + instantiate (1:=Time.meet to (Time.incr (Memory.max_ts loc (Thread.memory th)))).
              unfold Time.meet. des_ifs; econs; ss. refl.
          - ss. }
        eapply SAT1; eauto. unfold Time.meet. des_ifs; econs; ss.
        * refl.
        * left. auto.
      + destruct TS1.
        { assert (TS: Time.lt ffrom (Time.incr (Memory.max_ts loc (Thread.memory th)))).
          { eapply TimeFacts.le_lt_lt.
            { eapply max_full_ts_le_max_ts; eauto. }
            { eapply Time.incr_spec. } }
          assert (UNWRITABLE0: unwritable memory (Local.promises local) loc (Time.meet to (Time.incr (Memory.max_ts loc (Thread.memory th))))).
          { exploit rtc_unwritable_increase; [| |].
            - eapply thread_steps_pred_steps. eapply STEPS0.
            - ss. eapply UNWRITABLE.
              eexists ffrom, (Time.incr (Memory.max_ts loc (Thread.memory th))). splits; eauto.
              + eexists. splits.
                * econs 2; eauto. refl.
                * econs 3; eauto. refl.
              + instantiate (1:=Time.meet to (Time.incr (Memory.max_ts loc (Thread.memory th)))).
                unfold Time.meet. des_ifs; econs; ss.
                * transitivity from; auto.
                * refl.
            - ss. }
          eapply SAT1; eauto. unfold Time.meet. des_ifs; econs; ss.
          * refl.
          * left. auto. }
        { unfold Time.eq in *. subst.
          eapply SAT3; eauto. econs; eauto. inv CAP.
          hexploit (@Memory.latest_val_exists loc (Thread.memory th)); eauto. i. des.
          hexploit (@Memory.max_full_view_exists (Thread.memory th)); eauto. i. des.
          exploit BACK; eauto. i.
          esplits; eauto. econs; eauto.
          destruct (Memory.get loc (Time.incr (Memory.max_ts loc (Thread.memory th))) (Thread.memory th)) eqn: GET; auto.
          exfalso. destruct p.
          eapply Memory.max_ts_spec in GET. des.
          eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt.
          - eapply MAX.
          - eapply Time.incr_spec. }
      + exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
        { eapply TLE. }
        etrans.
        { eapply max_full_ts_le_max_ts; eauto. }
        { left. eapply Time.incr_spec. }
  }
  i. des.
  esplits; eauto.
  - ss. inv LOCAL. eapply no_reserves_map; eauto.
  - ss. unguard. des.
    + left. econs. inv FAILURE. inv LOCAL0.
      eapply promise_consistent_mon.
      { eapply promise_consistent_map; eauto. }
      { ss. }
      { ss. }
    + right. inv LOCAL0. rewrite PROMISES in *.
      eapply bot_promises_map; eauto.
Qed.


Definition pf_consistent_drf'' lang (e0:Thread.t lang): Prop :=
  let L := (fun loc => Memory.latest_reserve loc e0.(Thread.local).(Local.promises) e0.(Thread.memory)) in
  forall mem1 mem2
         (CAP: Memory.cap e0.(Thread.local).(Local.promises) e0.(Thread.memory) mem1)
         (FORGET: forget_memory (collapsing_latest_reserves_times L e0.(Thread.memory) \2/ collapsing_caps_times L e0.(Thread.memory) mem1) mem2 mem1),
  exists e1,
    (<<STEPS0: rtc (tau (@pred_step ((promise_free /1\ no_acq_update_msgs ((fun loc to => L loc) /2\ Memory.max_full_ts e0.(Thread.memory))) /1\ no_sc) lang)) (Thread.mk _ e0.(Thread.state) e0.(Thread.local) TimeMap.bot mem2) e1>>) /\
    (__guard__((<<FAILURE: Local.failure_step e1.(Thread.local)>>) \/
               (<<PROMISES: e1.(Thread.local).(Local.promises) = Memory.bot>>))).


Lemma pf_consistent_pf_consistent_drf'' lang (th: Thread.t lang)
      (WF: Local.wf th.(Thread.local) th.(Thread.memory))
      (MEM: Memory.closed th.(Thread.memory))
      (CONSISTENT: pf_consistent_drf' th)
      (RESERVEWF: memory_reserve_wf (Thread.memory th))
  :
    pf_consistent_drf'' th.
Proof.
  ii. exploit CONSISTENT; eauto. i. des.
  eexists. esplits.
  - etrans.
    + eapply pred_step_rtc_mon; try apply STEPS0.
      i. destruct x1; ss. destruct kind; ss.
    + eapply pred_step_rtc_mon; try apply STEPS1.
      i. ss. des. split; auto.
  - eauto.
Qed.

Inductive latest_other_reserves (prom mem: Memory.t) (loc: Loc.t) (to: Time.t): Prop :=
| latest_other_reserves_intro
    from
    (MAX: to = Memory.max_ts loc mem)
    (GET: Memory.get loc to mem = Some (from, Message.reserve))
    (NONE: Memory.get loc to prom = None)
.

Definition mapping_map_lt (f: Loc.t -> Time.t -> Time.t -> Prop): Prop :=
  forall loc t0 t1 ft0 ft1
         (MAP0: f loc t0 ft0)
         (MAP1: f loc t1 ft1),
    Time.lt t0 t1 -> Time.lt ft0 ft1.

Definition ident_map (loc: Loc.t) := @eq Time.t.

Lemma ident_map_lt
  :
    mapping_map_lt ident_map.
Proof.
  unfold ident_map in *. ii. clarify.
Qed.

Lemma ident_map_le
  :
    mapping_map_le ident_map.
Proof.
  unfold ident_map in *. ii. clarify.
Qed.

Lemma ident_map_bot
  :
    mapping_map_bot ident_map.
Proof.
  unfold ident_map in *. ii. clarify.
Qed.

Lemma ident_map_eq
  :
    mapping_map_eq ident_map.
Proof.
  unfold ident_map in *. ii. clarify.
Qed.

Lemma ident_map_total
      loc to
  :
    exists fto,
      <<MAP: ident_map loc to fto >>.
Proof.
  esplits; eauto. refl.
Qed.

Lemma mapping_map_lt_non_collapsable f
      (MAPLT: mapping_map_lt f)
      loc to
  :
    non_collapsable f loc to.
Proof.
  ii. unfold collapsed in *. des.
  eapply MAPLT in TLE; eauto. eapply Time.lt_strorder; eauto.
Qed.

Lemma ident_map_timemap
      tm
  :
    timemap_map ident_map tm tm.
Proof.
  ii. refl.
Qed.

Lemma ident_map_view
      vw
  :
    view_map ident_map vw vw.
Proof.
  econs; eapply ident_map_timemap.
Qed.

Lemma ident_map_message
      msg
  :
    msg_map ident_map msg msg.
Proof.
  destruct msg; econs. destruct released; econs.
  apply ident_map_view.
Qed.

Lemma ident_map_promises
      prom
  :
    promises_map ident_map prom prom.
Proof.
  econs; i.
  - esplits; eauto.
    + eapply mapping_map_lt_non_collapsable.
      eapply ident_map_lt.
    + refl.
    + eapply ident_map_message.
  - esplits; eauto; refl.
Qed.

Lemma ident_map_local
      lc
  :
    local_map ident_map lc lc.
Proof.
  econs; i.
  - refl.
  - econs; i; eapply ident_map_view.
  - eapply ident_map_promises.
Qed.

Lemma mapping_map_lt_collapsable_unwritable f prom mem
      (MAPLT: mapping_map_lt f)
  :
    collapsable_unwritable f prom mem.
Proof.
  ii. exfalso. des.
  eapply mapping_map_lt_non_collapsable; try eassumption.
  inv ITV. eapply TimeFacts.lt_le_lt; eauto.
Qed.

Lemma ident_map_collapsing_latest_memory L prom mem0 mem1 mem2 mem3
      (MLE: Memory.le prom mem0)
      (CLOSED: Memory.closed mem0)
      (LOCS: L = (fun loc => Memory.latest_reserve loc prom mem0))
      (CAP: Memory.cap prom mem0 mem1)
      (FORGET0: forget_memory (collapsing_latest_reserves_times L mem0 \2/ collapsing_caps_times L mem0 mem1) mem2 mem1)
      (FORGET1: forget_memory (latest_other_reserves prom mem0) mem3 mem0)
  :
    memory_map ident_map mem2 mem3.
Proof.
  econs.
  - i. dup GET. eapply forget_memory_get in GET0; eauto. des.
    apply not_or_and in NOT. des.
    dup GET1. eapply Memory.cap_inv in GET0; eauto. des.
    + inv FORGET1.
      erewrite <- COMPLETE in GET0.
      * right. esplits.
        { refl. }
        { eapply ident_map_message. }
        { refl. }
        { eauto. }
      * intros LATEST. inv LATEST.
        eapply NOT. eexists. econs; eauto. splits; eauto.
        unfold Memory.latest_reserve. des_ifs.
    + clarify. left. auto.
    + clarify. exfalso. eapply NOT0.
      eexists. econs; eauto. esplits. econs; eauto.
  - i. dup GET. eapply forget_memory_get in GET0; eauto. des.
    dup GET1. eapply Memory.cap_le in GET0; eauto; [|refl].
    inv FORGET0.
    dup GET0. erewrite <- COMPLETE in GET2.
    + esplits.
      * refl.
      * eauto.
      * refl.
    + ii. des.
      * unfold collapsing_latest_reserves_times, collapsing_latest_reserves, Memory.latest_reserve in H.
        des. clarify. apply NOT. econs; eauto. des_ifs.
        eapply MLE in Heq. clarify.
      * unfold collapsing_caps_times, collapsing_caps, Memory.latest_reserve in H.
        des. inv CAP0. des. clarify.
Qed.

Lemma collapsing_latest_memory_concrete_le L prom mem0 mem1 mem2 mem3
      (MLE: Memory.le prom mem0)
      (CLOSED: Memory.closed mem0)
      (LOCS: L = (fun loc => Memory.latest_reserve loc prom mem0))
      (CAP: Memory.cap prom mem0 mem1)
      (FORGET0: forget_memory (collapsing_latest_reserves_times L mem0 \2/ collapsing_caps_times L mem0 mem1) mem2 mem1)
      (FORGET1: forget_memory (latest_other_reserves prom mem0) mem3 mem0)
  :
    memory_concrete_le mem2 mem3.
Proof.
  ii. dup GET. eapply forget_memory_get in GET0; eauto. des.
  apply not_or_and in NOT. des.
  dup GET1. eapply Memory.cap_inv in GET0; eauto. des; clarify.
  - inv FORGET1.
    erewrite <- COMPLETE in GET0; eauto.
    ii. inv H. clarify.
  - exfalso. eapply NOT0.
    eexists. econs; eauto. esplits. econs; eauto.
Qed.

Lemma forget_latest_other_reserves_promises_le prom mem0 mem1
      (MLE: Memory.le prom mem0)
      (FORGET: forget_memory (latest_other_reserves prom mem0) mem1 mem0)
  :
    Memory.le prom mem1.
Proof.
  ii. inv FORGET. erewrite COMPLETE; eauto.
  ii. inv H. clarify.
Qed.

Lemma forget_latest_other_reserves_concrete_le prom mem0 mem1
      (FORGET: forget_memory (latest_other_reserves prom mem0) mem1 mem0)
  :
    memory_concrete_le mem0 mem1.
Proof.
  ii. inv FORGET. erewrite COMPLETE; eauto.
  ii. inv H. clarify.
Qed.

Lemma concrete_le_inhabited mem0 mem1
      (INHABITED: Memory.inhabited mem0)
      (MLE: memory_concrete_le mem0 mem1)
  :
    Memory.inhabited mem1.
Proof.
  ii. eapply MLE; eauto.
Qed.

Lemma forget_latest_other_reserves_closed prom mem0 mem1
      (CLOSED: Memory.closed mem0)
      (MLE: Memory.le prom mem0)
      (FORGET: forget_memory (latest_other_reserves prom mem0) mem1 mem0)
  :
    Memory.closed mem1.
Proof.
  inv CLOSED. econs; eauto.
  - i. dup MSG. eapply forget_memory_get in MSG; eauto. des.
    dup GET. eapply CLOSED0 in GET0. des. splits; auto.
    eapply memory_concrete_le_closed_msg; eauto.
    eapply forget_latest_other_reserves_concrete_le; eauto.
  - eapply concrete_le_inhabited; eauto.
    eapply forget_latest_other_reserves_concrete_le; eauto.
Qed.

Definition my_max_timemap (prom mem: Memory.t) (tm: TimeMap.t): Prop :=
  forall loc,
    ((<<MAX: Memory.max_full_ts mem loc (tm loc)>>) /\
     (<<LATEST: Memory.latest_reserve loc prom mem>>)) \/
    ((<<MAX: Memory.max_ts loc mem = (tm loc)>>) /\
     (<<LATEST: ~ Memory.latest_reserve loc prom mem>>)).

Lemma my_max_timemap_exists prom mem
      (INHABITED: Memory.inhabited mem)
  :
    exists tm, <<MYMAX: my_max_timemap prom mem tm>>.
Proof.
  exploit (choice
             (fun loc to =>
                ((<<MAX: Memory.max_full_ts mem loc to>>) /\
                 (<<LATEST: Memory.latest_reserve loc prom mem>>)) \/
                ((<<MAX: Memory.max_ts loc mem = to>>) /\
                 (<<LATEST: ~ Memory.latest_reserve loc prom mem>>)))).
  - i. destruct (classic (Memory.latest_reserve x prom mem)).
    + exploit Memory.max_full_ts_exists; eauto.
      i. des. esplits. left. split; eauto.
    + esplits. right. split; eauto.
  - i. des. exists f. esplits; eauto.
Qed.

Lemma my_max_timemap_inj prom mem tm0 tm1
      (MYMAX0: my_max_timemap prom mem tm0)
      (MYMAX1: my_max_timemap prom mem tm1)
  :
    tm0 = tm1.
Proof.
  extensionality loc.
  specialize (MYMAX0 loc). specialize (MYMAX1 loc). des; clarify.
  - eapply Memory.max_full_ts_inj; eauto.
  - rewrite <- MAX0. auto.
Qed.

Lemma memory_cap_covered prom mem0 mem1
      (CAP: Memory.cap prom mem0 mem1)
      (INHABITED: Memory.inhabited mem0)
      loc to
      (TS0: Time.lt Time.bot to)
      (TS1: Time.le to (Memory.max_ts loc mem0))
  :
    covered loc to mem1.
Proof.
  inv CAP.
  set (@cell_elements_least
         (mem0 loc)
         (fun to' => Time.le to to')). des; cycle 1.
  { exfalso. exploit Memory.max_ts_spec.
    - eapply INHABITED.
    - i. des. exploit EMPTY; eauto. }
  set (@cell_elements_greatest
         (mem0 loc)
         (fun to' => Time.lt to' to)). des; cycle 1.
  { exfalso. exploit EMPTY.
    - eapply INHABITED.
    - eauto.
    - ss. }
  destruct (Time.le_lt_dec to from).
  - exploit MIDDLE.
    + econs.
      * eapply GET0.
      * eapply GET.
      * eapply TimeFacts.lt_le_lt; eauto.
      * i. destruct (Memory.get loc ts mem0) eqn:GET1; auto.
        exfalso. destruct p.
        destruct (Time.le_lt_dec to ts).
        { exploit LEAST; eauto. i.
          eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt.
          { eapply x. }
          eapply TimeFacts.le_lt_lt.
          { eapply TS3. }
          { eapply memory_get_ts_strong in GET. des; clarify; ss.
            exfalso. eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt.
            - eapply l.
            - eauto. } }
        { exploit GREATEST; eauto. i.
          eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt.
          { eapply x. }
          { eauto. } }
    + eapply TimeFacts.lt_le_lt; eauto.
    + i. econs; eauto. econs; eauto.
  - econs.
    + eapply Memory.cap_le; try apply GET; eauto. refl.
    + econs; eauto.
Qed.

Definition later_times (tm: TimeMap.t) (loc: Loc.t) (to: Time.t): Prop :=
  Time.lt (tm loc) to.

Lemma forget_covered L mem0 mem1
      (FORGET: forget_memory L mem1 mem0)
      loc ts
      (COVERED: covered loc ts mem0)
      (KEEP: forall to from msg (SAT: L loc to)
                    (GET: Memory.get loc to mem0 = Some (from, msg)),
          ~ Interval.mem (from, to) ts)
  :
    covered loc ts mem1.
Proof.
  inv COVERED. inv FORGET.
  erewrite <- COMPLETE in GET.
  - econs; eauto.
  - ii. eapply KEEP in H; eauto.
Qed.

Lemma memory_reserve_wf_mon prom0 prom1 mem
      (RESERVEWF: Memory.reserve_wf prom1 mem)
      (MLE: Memory.le prom0 prom1)
  :
    Memory.reserve_wf prom0 mem.
Proof.
  ii. eauto.
Qed.

Lemma ident_map_mappable_any_event e
  :
    mappable_evt ident_map e.
Proof.
  destruct e; ss; split; eapply ident_map_total.
Qed.
  
Lemma collapsing_last_reserves_promise_or_later
      L prom mem0 mem1 mem2 max
      (LOC: L = (fun loc => Memory.latest_reserve loc prom mem0))
      (MLE: Memory.le prom mem0)
      (RESERVEWF: memory_reserve_wf mem0)
      (CLOSED: Memory.closed mem0)
      (CAP: Memory.cap prom mem0 mem1)
      (MAX: my_max_timemap prom mem0 max)
      (FORGET: forget_memory (collapsing_latest_reserves_times L mem0 \2/ collapsing_caps_times L mem0 mem1) mem2 mem1)
      loc to
      (UNWRITABLE: ~ unwritable mem2 prom loc to)
  :
    <<COVERED: covered loc to prom>> \/ <<LATER: later_times max loc to>> \/ <<BOT: to = Time.bot>>.
Proof.
  clarify.
  assert (RESERVEWF0: Memory.reserve_wf prom mem0).
  { eapply memory_reserve_wf_mon; eauto. }
  assert (INHABITED: Memory.inhabited mem0).
  { inv CLOSED. eauto. }
  assert (MLE0: Memory.le prom mem2).
  { eapply collapsing_caps_forget_prom_le; eauto.
    ii. clarify. unfold Memory.latest_reserve in SAT. des_ifs. }
  erewrite unwritable_eq in UNWRITABLE; eauto.
  eapply not_and_or in UNWRITABLE. des.
  - destruct (Time.le_lt_dec to Time.bot).
    { right. right. destruct l; auto. exfalso.
      eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt; eauto.
      eapply Time.bot_spec. }
    right. left.
    destruct (Time.le_lt_dec to (max loc)); auto. exfalso.
    eapply UNWRITABLE. red.
    eapply forget_covered; eauto.
    + eapply memory_cap_covered; eauto.
      etrans; eauto. specialize (MAX loc). des; clarify.
      { eapply max_full_ts_le_max_ts; eauto. }
      { rewrite <- MAX0. refl. }
    + ii. inv H. ss. des.
      * unfold collapsing_latest_reserves_times, collapsing_latest_reserves in SAT.
        des. clarify. specialize (MAX loc). des; clarify.
        dup RESERVE. eapply Memory.cap_le in RESERVE0; eauto; [|refl]. clarify.
        eapply max_ts_reserve_from_full_ts in RESERVE; eauto.
        exploit Memory.max_full_ts_inj.
        { eapply RESERVE. }
        { eapply MAX0. }
        i. clarify. eapply Time.lt_strorder.
        eapply TimeFacts.lt_le_lt; eauto.
      * unfold collapsing_caps_times, collapsing_caps, caps in SAT. des. clarify.
        exploit Memory.cap_inv; eauto. i. des; clarify.
        eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
        { eapply FROM. }
        etrans.
        { eapply l0. }
        { specialize (MAX loc). des; clarify.
          eapply max_full_ts_le_max_ts; eauto. }
  - apply NNPP in UNWRITABLE. auto.
Qed.

Lemma write_not_in_write_in L0 L1
      (LOCS: forall loc to (NSAT: ~ L0 loc to),
          <<SAT: L1 loc to>> \/ <<BOT: to = Time.bot>>)
  :
    write_not_in L0 <1= write_in L1.
Proof.
  i. destruct x0; ss.
  - i. dup IN. eapply PR in IN. eapply LOCS in IN. des; auto.
    clarify. inv IN0. ss. exfalso.
    eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
    + eapply FROM.
    + eapply Time.bot_spec.
  - i. dup IN. eapply PR in IN. eapply LOCS in IN. des; auto.
    clarify. inv IN0. ss. exfalso.
    eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
    + eapply FROM.
    + eapply Time.bot_spec.
Qed.

Definition pf_consistent_drf lang (e0:Thread.t lang): Prop :=
  let L := (fun loc => Memory.latest_reserve loc e0.(Thread.local).(Local.promises) e0.(Thread.memory)) in
  forall mem1 max sc
         (FORGET: forget_memory (latest_other_reserves e0.(Thread.local).(Local.promises) e0.(Thread.memory)) mem1 e0.(Thread.memory))
         (MAX: my_max_timemap e0.(Thread.local).(Local.promises) e0.(Thread.memory) max),
  exists e1,
    (<<STEPS0: rtc (tau (@pred_step ((promise_free /1\ no_acq_update_msgs ((fun loc to => L loc) /2\ Memory.max_full_ts e0.(Thread.memory))) /1\ no_sc /1\ write_in (later_times max \2/ fun loc to => covered loc to e0.(Thread.local).(Local.promises))) lang)) (Thread.mk _ e0.(Thread.state) e0.(Thread.local) sc mem1) e1>>) /\
    (__guard__((<<FAILURE: Local.failure_step e1.(Thread.local)>>) \/
               (<<PROMISES: e1.(Thread.local).(Local.promises) = Memory.bot>>))).

Lemma pf_consistent_pf_consistent_drf lang (th: Thread.t lang)
      (WF: Local.wf th.(Thread.local) th.(Thread.memory))
      (MEM: Memory.closed th.(Thread.memory))
      (CONSISTENT: pf_consistent th)
      (RESERVEWF: memory_reserve_wf (Thread.memory th))
  :
    pf_consistent_drf th.
Proof.
  eapply pf_consistent_pf_consistent_strong in CONSISTENT; eauto.
  eapply pf_consistent_pf_consistent_drf' in CONSISTENT; eauto.
  eapply pf_consistent_pf_consistent_drf'' in CONSISTENT; eauto.
  
  set (L:=fun loc : Loc.t =>
            Memory.latest_reserve loc (Local.promises (Thread.local th)) (Thread.memory th)).
  exploit Memory.cap_exists; eauto. i. des.
  exploit forget_exists; eauto. i. des.
  ii. exploit CONSISTENT; eauto. i. des.
  assert (MLE0: Memory.le (Local.promises (Thread.local th)) (Thread.memory th)).
  { inv WF. auto. }
  assert (COLLAPSABLE: collapsable_cap L (Local.promises (Thread.local th)) (Thread.memory th)).
  { ii. clarify. unfold L, Memory.latest_reserve in SAT.
    rewrite GET in SAT. clarify. }
  assert (MEMORY: memory_map ident_map mem_src mem1).
  { eapply ident_map_collapsing_latest_memory; cycle 3; eauto. }
  assert (MLE1: memory_concrete_le mem_src mem1).
  { eapply collapsing_latest_memory_concrete_le; cycle 3; eauto. }
  assert (CONCRETELE: memory_concrete_le th.(Thread.memory) mem_src).
  { eapply collapsing_caps_forget_le; eauto. }
  assert (LCWFTGT: Local.wf th.(Thread.local) mem_src).
  { eapply memory_concrete_le_local_wf; eauto. inv WF.
    eapply collapsing_caps_forget_prom_le; eauto. } 
  assert (LCWFSRC: Local.wf th.(Thread.local) mem1).
  { eapply memory_concrete_le_local_wf; eauto. inv WF.
    eapply forget_latest_other_reserves_promises_le; eauto. }
  assert (CLOSEDSRC: Memory.closed mem1).
  { eapply forget_latest_other_reserves_closed; cycle 1; eauto. }
  assert (CLOSEDTGT: Memory.closed mem_src).
  { eapply collapsing_caps_forget_closed; cycle 1; eauto. }
  eapply steps_write_not_in in STEPS0; ss; cycle 1.
  { eauto. inv LCWFTGT. auto. }
  eapply steps_wf_event in STEPS0; ss; cycle 1.
  { inv CLOSEDTGT. auto. }
  
  destruct e1.
  hexploit (@steps_map ident_map); try apply STEPS0; try apply MEMORY; eauto.
  { eapply ident_map_le. }
  { eapply ident_map_bot. }
  { eapply ident_map_eq. }
  { ss. i. eapply ident_map_mappable_any_event. }
  { eapply Memory.closed_timemap_bot; eauto. inv CLOSEDSRC. auto. }
  { eapply Memory.closed_timemap_bot; eauto. inv CLOSEDTGT. auto. }
  { eapply ident_map_local; eauto. }
  { eapply mapping_map_lt_collapsable_unwritable. eapply ident_map_lt. }
  { eapply ident_map_timemap. }
  { refl. }
  { instantiate (1:=(promise_free /1\ no_acq_update_msgs ((fun loc to => L loc) /2\ Memory.max_full_ts th.(Thread.memory))) /1\ no_sc /1\ write_in (later_times max \2/ fun loc to => covered loc to th.(Thread.local).(Local.promises))).
    ii. ss. des. splits.
    - inv REL; ss. inv KIND; ss. inv MSG0; ss. inv MSG; ss. inv MAP0; ss.
    - inv REL; ss. inv FROM. ss.
    - inv REL; ss.
    - eapply write_not_in_write_in in SAT1.
      + instantiate (1:=later_times max \2/ fun loc to => covered loc to th.(Thread.local).(Local.promises)) in SAT1.
        inv REL; ss.
        * inv FROM. inv TO. eauto.
        * inv FROM. inv TO. eauto.
      + i. eapply collapsing_last_reserves_promise_or_later in NSAT; ss; eauto.
        des; auto. }
  i. des.
  eapply no_sc_any_sc_rtc in STEP; ss; cycle 1.
  { i. destruct x1; ss; des; auto. } des.
  esplits; eauto.
  unguard. des; ss.
  - left. econs. inv FAILURE. inv LOCAL.
    eapply promise_consistent_mon.
    { eapply promise_consistent_map; eauto.
      - eapply ident_map_le.
      - eapply ident_map_eq. }
    { ss. }
    { ss. }
  - right. inv LOCAL. rewrite PROMISES in *.
    eapply bot_promises_map; eauto.
Qed.


Definition times_in_memory (mem: Memory.t) (L: Loc.t -> list Time.t): Prop :=
  forall loc t,
    (<<SAT: List.In t (L loc)>>) <->
    (<<INMEMORY:
       (exists from msg, (<<GET: Memory.get loc t mem = Some (from, msg)>>)) \/
       (exists to msg, (<<GET: Memory.get loc to mem = Some (t, msg)>>))>>).

Lemma times_in_memory_exists mem
  :
    exists l, times_in_memory mem l.
Proof.
  hexploit (choice
              (fun loc tl =>
                 forall t,
                   (<<SAT: List.In t tl>>) <->
                   (<<INMEMORY:
                      (exists from msg, (<<GET: Memory.get loc t mem = Some (from, msg)>>)) \/
                      (exists to msg, (<<GET: Memory.get loc to mem = Some (t, msg)>>))>>))); auto.
  intros loc.
  hexploit (wf_cell_msgs_exists (mem loc)). i. des.
  exists ((List.map (fun ftm =>
                       match ftm with
                       | (from, _, _) => from
                       end) l)
            ++
            (List.map (fun ftm =>
                         match ftm with
                         | (_, to, _) => to
                         end) l)).
  i. split; i.
  - red in H. eapply List.in_app_or in H. des.
    + eapply List.in_map_iff in H. des.
      destruct x as [[from to] msg]. clarify.
      eapply COMPLETE in H0. right. eauto.
    + eapply List.in_map_iff in H. des.
      destruct x as [[from to] msg]. clarify.
      eapply COMPLETE in H0. left. eauto.
  - eapply List.in_or_app.  des.
    + right. eapply COMPLETE in GET.
      eapply List.in_map_iff. esplits; eauto. ss.
    + left. eapply COMPLETE in GET.
      eapply List.in_map_iff. esplits; eauto. ss.
Qed.



(* Inductive shifted_map mlast mcert *)
(*           (updates: Loc.t -> Prop) *)
(*           (sky gap: TimeMap.t) *)
(*           (f: Loc.t -> Time.t -> Time.t): Prop := *)
(* | shifted_map_intro *)
(*     (PRSV: map_preserving (times_in_memory mcert) f) *)
(*     (SAME: forall l t (TLE: Time.le t (Memory.max_ts l mlast)), *)
(*         f l t = t) *)
(*     (INGAP: forall l t (TLT: Time.lt (Memory.max_ts l mcert) t), *)
(*         Time.lt (f l t) (gap l)) *)
(*     (AFTERSKY: forall l t (TLT: Time.lt (Memory.max_ts l mcert) t), *)
(*         Time.lt (sky l) (f l t)) *)
(* . *)

(* Lemma shifted_map_exists mlast mcert updates *)
(*       (MLE: Memory.le mlast mcert) *)
(*       (sky gap: TimeMap.t) *)
(*       (SKY: forall l, Time.lt (Memory.max_ts l mlast) (sky l)) *)
(*       (GAP: forall l, Time.lt (Memory.max_ts l mlast) (gap l)) *)
(*   : *)
(*     exists f, (<<SHIFTED: shifted_map mlast mcert updates sky gap f>>). *)
(* Proof. *)
(*   (* may be very hard... *) *)
(* Admitted. *)

(* Lemma shifted_map_preserving_last_mem  mlast mcert updates sky gap f *)
(*       (CLOSED: Memory.closed mlast) *)
(*       (SHIFTED: shifted_map mlast mcert updates sky gap f) *)
(*   : *)
(*     memory_map f mlast mlast. *)
(* Proof. *)
(*   inv SHIFTED. inv PRSV. econs; i. *)
(*   - exploit Memory.max_ts_spec; eauto. i. des. *)
(*     repeat erewrite SAME; eauto. *)
(*     + rewrite GET. unfold msg_map. des_ifs. repeat f_equal. *)
(*       inv CLOSED. exploit CLOSED0; try apply GET; eauto. i. des. *)
(*       inv MSG_CLOSED. inv CLOSED; ss. f_equal. *)
(*       destruct view. inv CLOSED1. unfold view_map, timemap_map. ss. f_equal. *)
(*       * extensionality l. erewrite SAME; auto. *)
(*         specialize (PLN l). des. *)
(*         exploit Memory.max_ts_spec; eauto. i. des. auto. *)
(*       * extensionality l. erewrite SAME; auto. *)
(*         specialize (RLX l). des. *)
(*         exploit Memory.max_ts_spec; eauto. i. des. auto. *)
(*     + exploit Memory.get_ts; try apply GET; eauto. i. des. *)
(*       * clarify. *)
(*       * left. eapply TimeFacts.lt_le_lt; eauto. *)
(*   - destruct msg_src as [from msg]. exploit Memory.max_ts_spec; eauto. i. des. *)
(*     esplits. *)
(*     + erewrite SAME; eauto. *)
(*     + eauto. *)
(* Qed. *)






(* Inductive add_cap (caps: Loc.t -> option (Time.t * Time.t * Message.t)): Memory.t -> Memory.t -> Prop := *)
(* | add_cap_refl mem0 *)
(*   : *)
(*     add_cap caps mem0 mem0 *)
(* | add_cap_add *)
(*     loc from to msg mem0 mem1 *)
(*     (CAP: caps loc = Some (from, to, msg)) *)
(*     (ADD: Memory.add mem0 loc from to msg mem1) *)
(*   : *)
(*     add_cap caps mem0 mem1 *)
(* . *)
(* Hint Constructors add_cap. *)


(* Lemma diff_after_promise_write caps prom0 mem_src0 mem_tgt0 *)
(*       loc from to val released kind prom1 mem_tgt1 *)
(*       (DIFF: diff_after_promises caps prom0 mem_src0 mem_tgt0) *)
(*       (CAPSWF: forall loc from to msg (CAP: caps loc = Some (from, to, msg)), *)
(*           Time.lt from to) *)
(*       (MLE: Memory.le prom0 mem_src0) *)
(*       (WRITE: Memory.write prom0 mem_tgt0 loc from to val released prom1 mem_tgt1 kind) *)
(*   : *)
(*     exists mem_src1' mem_src1, *)
(*       (<<WRITE: Memory.write prom0 mem_src0 loc from to val released prom1 mem_src1' kind>>) /\ *)
(*       (<<ADD: add_cap caps mem_src1' mem_src1>>) /\ *)
(*       (<<DIFF: diff_after_promises caps prom1 mem_src1 mem_tgt1>>). *)
(* Proof. *)
(*   dup DIFF. inv DIFF. inv WRITE; ss. *)
(*   generalize (unchangable_promise PROMISE). intros UNCH. *)
(*   inv PROMISE; ss. *)
(*   - exploit Memory.add_exists_le. *)
(*     { eapply MLE0. } *)
(*     { eapply MEM. } *)
(*     intros [mem_src' ADD]. exists mem_src', mem_src'. splits; auto. *)
(*     + econs; eauto. econs; eauto. i. clarify. *)
(*     + assert (PROM: prom1 = prom0). *)
(*       { eapply MemoryFacts.MemoryFacts.add_remove_eq; eauto. } clarify. *)
(*       econs. *)
(*       * eapply memory_op_le; eauto. *)
(*       * i. erewrite Memory.add_o in GET; eauto. *)
(*         erewrite Memory.add_o in NONE; eauto. des_ifs. guardH o. *)
(*         exploit DIFF1; eauto. *)
(*       * i. exploit UNCH. *)
(*         { eapply diff_after_promise_unchangable; eauto. } i. inv x. *)
(*         eapply CAPS in CAP. des. splits; eauto. *)
(*         { i. erewrite Memory.add_o in NONE; eauto. des_ifs. guardH o. *)
(*           eapply SRCGET in NONE. eauto. } *)
(*         { i. eapply PROM in PROM0. des. split; auto. *)
(*           erewrite Memory.add_o; eauto. des_ifs. ss. des; clarify. *)
(*           eapply Memory.add_get0 in MEM. des. clarify. } *)

(*   - exploit Memory.split_exists_le. *)
(*     { eapply MLE. } *)
(*     { eapply PROMISES. } *)
(*     intros [mem_src' SPLIT]. exists mem_src', mem_src'. splits; auto. *)
(*     + econs; eauto. *)
(*     + econs. *)
(*       * eapply memory_op_le; eauto. *)
(*       * i. erewrite Memory.split_o in GET; eauto. *)
(*         erewrite Memory.split_o in NONE; eauto. des_ifs. guardH o. guardH o0. *)
(*         exploit DIFF1; eauto. *)
(*       * i. exploit UNCH. *)
(*         { eapply diff_after_promise_unchangable; eauto. } i. inv x. *)
(*         eapply CAPS in CAP. des. splits; eauto. *)
(*         { erewrite Memory.remove_o; eauto. des_ifs. } *)
(*         { i. erewrite Memory.split_o in NONE; eauto. des_ifs. *)
(*           guardH o. guardH o0. eapply SRCGET in NONE. des. *)
(*           dup PROM0. eapply Memory.split_get1 in PROM0; eauto. des. *)
(*           eapply Memory.remove_get1 in GET2; eauto. ss. des; clarify. *)
(*           - eapply Memory.split_get0 in PROMISES. des. clarify. *)
(*           - esplits; eauto. } *)
(*         { dup PROMISES. eapply Memory.split_get0 in PROMISES; eauto. des. *)
(*           i. erewrite Memory.remove_o in PROM0; eauto. des_ifs. guardH o. *)
(*           erewrite Memory.split_o in PROM0; eauto. des_ifs; ss; clarify. *)
(*           - unguard. des; clarify. *)
(*           - guardH o0. des; clarify. *)
(*             eapply PROM in GET1. des. split; auto. *)
(*             erewrite Memory.split_o; eauto. des_ifs. *)
(*             + ss. des; clarify. *)
(*             + guardH o1. ss. des; clarify. *)
(*           - guardH o0. guardH o1. dup PROM0. eapply PROM in PROM0. *)
(*             des. split; auto. *)
(*             erewrite Memory.split_o; eauto. des_ifs. *)
(*             + ss. unguard. des; clarify. *)
(*             + ss. unguard. des; clarify. } *)

(*   - exploit Memory.lower_exists_le. *)
(*     { eapply MLE. } *)
(*     { eapply PROMISES. } *)
(*     intros [mem_src' LOWER]. *)

(*     destruct (classic ((forall to' from' msg *)
(*                                (GET: Memory.get loc to' prom1 = Some (from', msg)), *)
(*                            msg = Message.reserve) /\ *)
(*                        exists p, (<<CAP: caps loc = Some p>>))). *)
(*     { des. destruct p as [[from1 to1] msg1]. *)
(*       dup CAP. eapply CAPS in CAP. des. *)
(*       exploit UNCH. *)
(*       { eapply diff_after_promise_unchangable; eauto. } i. inv x. *)
(*       hexploit (@Memory.add_exists mem_src' loc from1 to1 msg1); eauto. *)
(*       { i. dup GET2. eapply memory_op_le in GET2; eauto. *)
(*         exploit Memory.get_disjoint. *)
(*         - eapply GET. *)
(*         - eapply GET2. *)
(*         - i. des; clarify. exfalso. *)
(*           eapply Memory.lower_get0 in PROMISES. des. *)
(*           eapply PROM in GET1. des. *)
(*           erewrite Memory.lower_o in GET0; eauto. des_ifs; ss; des; clarify. } *)
(*       { eapply Cell.get_opt_wf; eauto. } *)
(*       intros [mem_src'' ADD]. exists mem_src', mem_src''. *)
(*       splits; eauto. econs. *)
(*       - hexploit memory_op_le; eauto. intros MLE1. *)
(*         ii. erewrite Memory.add_o in LHS; eauto. des_ifs; eauto. *)
(*         ss. des; clarify. *)
(*       - i. erewrite Memory.add_o in NONE; eauto. des_ifs. guardH o. *)
(*         erewrite Memory.lower_o in GET0; eauto. *)
(*         erewrite Memory.lower_o in NONE; eauto. des_ifs. eapply DIFF1; eauto. *)
(*       - i. exploit UNCH. *)
(*         { eapply diff_after_promise_unchangable; eauto. } i. inv x. *)
(*         dup CAP. eapply CAPS in CAP. des. splits; eauto. *)
(*         + erewrite Memory.remove_o; eauto. des_ifs. *)
(*         + i. erewrite Memory.add_o in NONE; eauto. des_ifs. guardH o. *)
(*           erewrite Memory.lower_o in NONE; eauto. des_ifs. guardH o0. *)
(*           eapply SRCGET0 in NONE. des. *)
(*           eapply Memory.lower_get1 in PROM1; eauto. des. inv MSG_LE. *)
(*           eapply Memory.remove_get1 in GET2; eauto. des; clarify; eauto. *)
(*           ss. unguard. des; clarify. *)
(*         + i. dup PROM1. erewrite Memory.remove_o in PROM2; eauto. des_ifs. *)
(*           guardH o. erewrite Memory.lower_o in PROM2; eauto. des_ifs. *)
(*           * ss. unguard. des; clarify. *)
(*           * guardH o0. ss. eapply PROM0 in PROM2. des. split; auto. *)
(*             erewrite Memory.add_o; eauto. des_ifs. *)
(*             { ss. des; clarify. eapply H in PROM1. clarify. } *)
(*             { erewrite Memory.lower_o; eauto. des_ifs. *)
(*               unguard. ss. des;clarify. } *)
(*     } *)
(*     { exists mem_src', mem_src'. splits; auto. *)
(*       + econs; eauto. *)
(*       + econs. *)
(*         * eapply memory_op_le; eauto. *)
(*         * i. erewrite Memory.lower_o in GET; eauto. *)
(*           erewrite Memory.lower_o in NONE; eauto. des_ifs. guardH o. *)
(*           exploit DIFF1; eauto. *)
(*         * i. exploit UNCH. *)
(*           { eapply diff_after_promise_unchangable; eauto. } i. inv x. *)
(*           dup CAP. eapply CAPS in CAP. des. splits; eauto. *)
(*           { erewrite Memory.remove_o; eauto. des_ifs. } *)
(*           { i. erewrite Memory.lower_o in NONE; eauto. des_ifs. *)
(*             guardH o. eapply SRCGET in NONE. des. *)
(*             dup PROM0. eapply Memory.lower_get1 in PROM0; eauto. des. *)
(*             eapply Memory.remove_get1 in GET2; eauto. ss. des; clarify. *)
(*             - apply not_and_or in H. des. *)
(*               + eapply not_all_ex_not in H. destruct H as [from1 H]. *)
(*                 eapply not_all_ex_not in H. destruct H as [to1 H]. *)
(*                 eapply not_all_ex_not in H. destruct H as [msg1 H]. *)
(*                 eapply imply_to_and in H. destruct H as [GET0 CONCRETE]. *)
(*                 destruct msg1; clarify. esplits; eauto. *)
(*               + exfalso. eapply H. esplits; eauto. *)
(*             - inv MSG_LE. esplits; eauto. } *)
(*           { dup PROMISES. eapply Memory.lower_get0 in PROMISES; eauto. des. *)
(*             i. erewrite Memory.remove_o in PROM0; eauto. des_ifs. guardH o. *)
(*             erewrite Memory.lower_o in PROM0; eauto. des_ifs; ss; clarify. *)
(*             - unguard. des; clarify. *)
(*             - guardH o0. eapply PROM in PROM0. des. split; auto. *)
(*               erewrite Memory.lower_o; eauto. des_ifs. *)
(*               ss. des; clarify. } *)
(*     } *)
(* Qed. *)

(* Lemma diff_after_promises_step caps P lang *)
(*       th_src th_tgt th_tgt' st st' v v' prom prom' sc sc' *)
(*       mem_src mem_tgt mem_tgt' e *)
(*       (CAPSWF: forall loc from to msg (CAP: caps loc = Some (from, to, msg)), *)
(*           Time.lt from to) *)
(*       (MLE: Memory.le prom mem_src) *)
(*       (STEP: (@pred_step P lang) e th_tgt th_tgt') *)
(*       (PROMISEFREE: P <1= promise_free) *)
(*       (TH_SRC: th_src = Thread.mk lang st (Local.mk v prom) sc mem_src) *)
(*       (TH_TGT0: th_tgt = Thread.mk lang st (Local.mk v prom) sc mem_tgt) *)
(*       (TH_TGT1: th_tgt' = Thread.mk lang st' (Local.mk v' prom') sc' mem_tgt') *)
(*       (DIFF: diff_after_promises caps prom mem_src mem_tgt) *)
(*       (CONSISTENT: Local.promise_consistent (Local.mk v' prom')) *)
(*   : *)
(*     exists mem_src' mem_src'', *)
(*       (<<STEP: (@pred_step P lang) *)
(*                  e th_src *)
(*                  (Thread.mk lang st' (Local.mk v' prom') sc' mem_src')>>) /\ *)
(*       (<<ADD: add_cap caps mem_src' mem_src''>>) /\ *)
(*       (<<DIFF: diff_after_promises caps prom' mem_src'' mem_tgt'>>) *)
(* . *)
(* Proof. *)
(*   inv STEP. dup SAT. eapply PROMISEFREE in SAT. inv STEP0. inv STEP. *)
(*   - inv STEP0. inv LOCAL. ss. clarify. *)
(*     exploit diff_after_promise_promise; eauto. *)
(*     i. des. exists mem_src1, mem_src1. splits; eauto. *)
(*     econs; eauto. econs; eauto. econs 1; eauto. *)
(*     econs; eauto. econs; eauto. *)
(*     unfold Message.is_released_none, Memory.op_kind_is_cancel, andb, orb in *. *)
(*     des_ifs. *)
(*     + econs. econs. *)
(*     + inv PROMISE. econs. *)
(*   - inv STEP0. inv LOCAL; ss. *)
(*     + exists mem_src, mem_src. splits; eauto. *)
(*       econs; eauto. econs; eauto. *)
(*     + dup LOCAL0. inv LOCAL0. ss. clarify. *)
(*       assert (GETSRC: Memory.get loc ts mem_src = Some (from, Message.full val released)). *)
(*       { inv DIFF. destruct (Memory.get loc ts mem_src) eqn: GET0. *)
(*         - destruct p. eapply MLE0 in GET0. clarify. *)
(*         - exploit DIFF0; eauto. intros CAP. *)
(*           eapply CAPS in CAP. des. eapply SRCGET in GET0. des. *)
(*           dup PROM0. eapply PROM in PROM0. des. *)
(*           exploit promise_consistent_promise_read; eauto. *)
(*           i. exfalso. eapply Time.lt_strorder. etrans; eauto. } *)
(*       exists mem_src, mem_src. splits; eauto. *)
(*       econs; eauto. econs; eauto. *)
(*     + inv LOCAL0. ss. clarify. *)
(*       exploit diff_after_promise_write; eauto. i. des. *)
(*       exists mem_src1', mem_src1. splits; eauto. *)
(*       econs; eauto. econs; eauto. *)
(*     + eapply write_step_promise_consistent in CONSISTENT; eauto. *)
(*       dup LOCAL1. inv LOCAL1. inv LOCAL2. ss. clarify. *)
(*       assert (GETSRC: Memory.get loc tsr mem_src = Some (from, Message.full valr releasedr)). *)
(*       { inv DIFF. destruct (Memory.get loc tsr mem_src) eqn: GET0. *)
(*         - destruct p. eapply MLE0 in GET0. clarify. *)
(*         - exploit DIFF0; eauto. intros CAP. *)
(*           eapply CAPS in CAP. des. eapply SRCGET in GET0. des. *)
(*           dup PROM0. eapply PROM in PROM0. des. *)
(*           exploit promise_consistent_promise_read; eauto. *)
(*           i. exfalso. eapply Time.lt_strorder. etrans; eauto. } *)
(*       exploit diff_after_promise_write; eauto. i. des. *)
(*       exists mem_src1', mem_src1. splits; eauto. *)
(*       econs; eauto. econs; eauto. econs 2; eauto. *)
(*     + inv LOCAL0. ss. clarify. *)
(*       exists mem_src, mem_src. splits; eauto. *)
(*       econs; eauto. econs; eauto. *)
(*     + inv LOCAL0. ss. clarify. *)
(*       exists mem_src, mem_src. splits; eauto. *)
(*       econs; eauto. econs; eauto. *)
(*     + inv LOCAL0. ss. clarify. *)
(*       exists mem_src, mem_src. splits; eauto. *)
(*       econs; eauto. econs; eauto. *)
(* Qed. *)
