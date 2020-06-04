Require Import RelationClasses.

From Paco Require Import paco.
From sflib Require Import sflib.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import Language.
From PromisingLib Require Import Loc.
Require Import Time.
Require Import Event.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import MemoryFacts.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.
Require Import Progress.
Require Import Behavior.
Require Import Cover.
Require Import Pred.
Require Import Trace.

Require Import MemoryProps.
Require Import Mapping.

Require Import LocalDRFDef.
Require Import LocalDRF_PF.

Set Implicit Arguments.

Section CONCRETEIDENT.

  Definition map_ident_concrete (f: Loc.t -> Time.t -> Time.t -> Prop)
             (mem: Memory.t): Prop :=
    forall loc to
           (CONCRETE: concrete_promised mem loc to),
      f loc to to.

  Definition map_ident_concrete_bot
             f mem
             (MAP: map_ident_concrete f mem)
             (CLOSED: Memory.closed mem)
    :
      mapping_map_bot f.
  Proof.
    ii. eapply MAP. inv CLOSED. econs; eauto.
  Qed.

  Lemma map_ident_concrete_closed_timemap
        f mem tm
        (MAP: map_ident_concrete f mem)
        (CLOSED: Memory.closed_timemap tm mem)
    :
      timemap_map f tm tm.
  Proof.
    ii. eapply MAP; eauto.
    exploit CLOSED; eauto. i. des. econs; eauto.
  Qed.

  Lemma map_ident_concrete_closed_view
        f mem vw
        (MAP: map_ident_concrete f mem)
        (CLOSED: Memory.closed_view vw mem)
    :
      view_map f vw vw.
  Proof.
    inv CLOSED. econs.
    - eapply map_ident_concrete_closed_timemap; eauto.
    - eapply map_ident_concrete_closed_timemap; eauto.
  Qed.

  Lemma map_ident_concrete_closed_tview
        f mem tvw
        (MAP: map_ident_concrete f mem)
        (CLOSED: TView.closed tvw mem)
    :
      tview_map f tvw tvw.
  Proof.
    inv CLOSED. econs.
    - i. eapply map_ident_concrete_closed_view; eauto.
    - eapply map_ident_concrete_closed_view; eauto.
    - eapply map_ident_concrete_closed_view; eauto.
  Qed.

  Lemma map_ident_concrete_closed_opt_view
        f mem vw
        (MAP: map_ident_concrete f mem)
        (CLOSED: Memory.closed_opt_view vw mem)
    :
      opt_view_map f vw vw.
  Proof.
    inv CLOSED; econs.
    eapply map_ident_concrete_closed_view; eauto.
  Qed.

  Lemma map_ident_concrete_closed_message
        f mem msg
        (MAP: map_ident_concrete f mem)
        (CLOSED: Memory.closed_message msg mem)
    :
      msg_map f msg msg.
  Proof.
    inv CLOSED; econs.
    eapply map_ident_concrete_closed_opt_view; eauto.
  Qed.

  Inductive compose_map (f0 f1: Loc.t -> Time.t -> Time.t -> Prop)
    : Loc.t -> Time.t -> Time.t -> Prop :=
  | compose_map_intro
      loc ts0 ts1 ts2
      (MAP0: f0 loc ts0 ts1)
      (MAP1: f1 loc ts1 ts2)
    :
      compose_map f0 f1 loc ts0 ts2
  .
  Hint Constructors compose_map.

  Lemma compose_map_eq f0 f1
        (MAPEQ0: mapping_map_eq f0)
        (MAPEQ1: mapping_map_eq f1)
    :
      mapping_map_eq (compose_map f0 f1).
  Proof.
    unfold mapping_map_eq in *. i. inv MAP0. inv MAP1.
    hexploit (@MAPEQ0 _ _ _ _ MAP2 MAP0); eauto. i. clarify.
    eauto.
  Qed.

  Lemma compose_map_le f0 f1
        (MAPLE0: mapping_map_le f0)
        (MAPLE1: mapping_map_le f1)
    :
      mapping_map_le (compose_map f0 f1).
  Proof.
    unfold mapping_map_le in *. i. inv MAP0. inv MAP1.
    hexploit (@MAPLE0 _ _ _ _ _ MAP2 MAP0); eauto.
  Qed.

  Lemma compose_map_bot f0 f1
        (MAPBOT0: mapping_map_bot f0)
        (MAPBOT1: mapping_map_bot f1)
    :
      mapping_map_bot (compose_map f0 f1).
  Proof.
    ii. econs; eauto.
  Qed.

  Lemma compose_map_lt f0 f1
        (MAPLT0: mapping_map_lt f0)
        (MAPLT1: mapping_map_lt f1)
    :
      mapping_map_lt (compose_map f0 f1).
  Proof.
    unfold mapping_map_lt in *. i. inv MAP0. inv MAP1.
    transitivity (Time.lt ts1 ts2); eauto.
  Qed.

  Lemma compose_map_timemap f0 f1 tm0 tm1 tm2
        (MAP0: timemap_map f0 tm0 tm1)
        (MAP1: timemap_map f1 tm1 tm2)
    :
      timemap_map (compose_map f0 f1) tm0 tm2.
  Proof.
    ii. eauto.
  Qed.

  Lemma compose_map_view f0 f1 vw0 vw1 vw2
        (MAP0: view_map f0 vw0 vw1)
        (MAP1: view_map f1 vw1 vw2)
    :
      view_map (compose_map f0 f1) vw0 vw2.
  Proof.
    inv MAP0. inv MAP1. econs.
    - eapply compose_map_timemap; eauto.
    - eapply compose_map_timemap; eauto.
  Qed.

  Lemma compose_map_opt_view f0 f1 vw0 vw1 vw2
        (MAP0: opt_view_map f0 vw0 vw1)
        (MAP1: opt_view_map f1 vw1 vw2)
    :
      opt_view_map (compose_map f0 f1) vw0 vw2.
  Proof.
    inv MAP0; inv MAP1; econs.
    eapply compose_map_view; eauto.
  Qed.

  Lemma compose_map_tview f0 f1 tvw0 tvw1 tvw2
        (MAP0: tview_map f0 tvw0 tvw1)
        (MAP1: tview_map f1 tvw1 tvw2)
    :
      tview_map (compose_map f0 f1) tvw0 tvw2.
  Proof.
    inv MAP0. inv MAP1. econs.
    - i. eapply compose_map_view; eauto.
    - eapply compose_map_view; eauto.
    - eapply compose_map_view; eauto.
  Qed.

  Lemma compose_map_msg f0 f1 msg0 msg1 msg2
        (MAP0: msg_map f0 msg0 msg1)
        (MAP1: msg_map f1 msg1 msg2)
    :
      msg_map (compose_map f0 f1) msg0 msg2.
  Proof.
    inv MAP0; inv MAP1; econs.
    eapply compose_map_opt_view; eauto.
  Qed.

  Lemma compose_map_mappable f0 f1 mem0 mem1
        (MAP: memory_map f0 mem0 mem1)
        (MAPPABLE: mappable_memory f1 mem1)
    :
      mappable_memory (compose_map f0 f1) mem0.
  Proof.
    ii. inv MAP. exploit MAPPED; eauto. i. des; clarify.
    inv MSG. inv MSGLE. exploit MAPPABLE; eauto. i. inv x.
    eexists. eauto.
  Qed.

  Lemma compose_map_memory2 f0 f1 m0 m1 m2
        (MAPEQ0: mapping_map_eq f0)
        (MAPLE: mapping_map_le f1)
        (MEM0: memory_map2 f0 m0 m1)
        (CLOSED0: Memory.closed m0)
        (MEM1: memory_map2 f1 m1 m2)
    :
      memory_map2 (compose_map f0 f1) m0 m2.
  Proof.
    dup MEM0. dup MEM1.
    inv MEM0. inv MEM1. econs.
    - ii. exploit MAPPED; eauto. i. des; auto.
      exploit MAPPED0; eauto. i. des; auto.
      + subst. inv MSGLE. inv MSG. auto.
      + right. inv CLOSED0. exploit CLOSED; eauto. i. des.
        exploit closed_message_map; try apply MSG; eauto.
        { eapply memory_map2_memory_map; eauto. } intros MSG_CLOSED1.
        exploit msg_map_exists; try apply MSG_CLSOED1; eauto.
        { eapply memory_map2_memory_map; eauto. } i. des.
        esplits; [..|eauto].
        * eauto.
        * eapply compose_map_msg; eauto.
        * etrans; eauto. eapply msg_le_map; eauto.
    - i. exploit ONLY0; eauto. i. des.
      exploit ONLY; eauto. i. des. esplits; eauto.
  Qed.

  Lemma compose_map_promise f0 f1 m0 m1 m2
        (MAPLT0: mapping_map_lt f0)
        (MAPLT1: mapping_map_lt f1)
        (MEM0: promises_map f0 m0 m1)
        (CLOSED0: Memory.closed m0)
        (MEM1: promises_map f1 m1 m2)
    :
      promises_map (compose_map f0 f1) m0 m2.
  Proof.
    dup MEM0. dup MEM1.
    inv MEM0. inv MEM1. econs.
    - ii. exploit MAPPED; eauto. i. des; auto.
      exploit MAPPED0; eauto. i. des; auto. esplits; eauto.
      + eapply mapping_map_lt_non_collapsable.
        eapply compose_map_lt; eauto.
      + eapply compose_map_msg; eauto.
    - ii. exploit ONLY0; eauto. i. des.
      exploit ONLY; eauto. i. des. esplits; eauto.
  Qed.

End CONCRETEIDENT.


Section CAPFLEX.

  Inductive cap_flex (mem1 mem2: Memory.t) (tm: TimeMap.t): Prop :=
  | cap_flex_intro
      (SOUND: Memory.le mem1 mem2)
      (MIDDLE: forall loc from1 to1 from2 to2
                      (ADJ: Memory.adjacent loc from1 to1 from2 to2 mem1)
                      (TO: Time.lt to1 from2),
          Memory.get loc from2 mem2 = Some (to1, Message.reserve))
      (BACK: forall loc, Memory.get loc (tm loc) mem2 =
                         Some (Memory.max_ts loc mem1, Message.reserve))
      (COMPLETE: forall loc from to msg
                        (GET1: Memory.get loc to mem1 = None)
                        (GET2: Memory.get loc to mem2 = Some (from, msg)),
          (exists f m, Memory.get loc from mem1 = Some (f, m)))
  .
  Hint Constructors cap_flex.

  Lemma cap_flex_inv
        mem1 mem2 tm
        loc from to msg
        (CLOSED: Memory.closed mem1)
        (CAP: cap_flex mem1 mem2 tm)
        (GET: Memory.get loc to mem2 = Some (from, msg))
        (TM: forall loc, Time.lt (Memory.max_ts loc mem1) (tm loc))
    :
    Memory.get loc to mem1 = Some (from, msg) \/
    (Memory.get loc to mem1 = None /\
     exists from1 to2,
        Memory.adjacent loc from1 from to to2 mem1 /\
        Time.lt from to /\
        msg = Message.reserve) \/
    (Memory.get loc to mem1 = None /\
     from = Memory.max_ts loc mem1 /\
     to = tm loc /\
     msg = Message.reserve).
  Proof.
    inv CAP. move GET at bottom.
    destruct (Memory.get loc to mem1) as [[]|] eqn:GET1.
    { exploit SOUND; eauto. i.
      rewrite GET in x. inv x. auto. }
    right. exploit COMPLETE; eauto. i. des.
    exploit Memory.max_ts_spec; eauto. i. des. inv MAX.
    - left.
      exploit Memory.adjacent_exists; try eapply H; eauto. i. des.
      assert (LT: Time.lt from from2).
      { clear MIDDLE BACK COMPLETE GET0 H.
        inv x1. rewrite GET0 in x. inv x.
        exploit Memory.get_ts; try exact GET2. i. des.
        { subst. inv TS. }
        destruct (Time.le_lt_dec from2 from); auto.
        inv l.
        - exfalso.
          exploit Memory.get_ts; try exact GET0. i. des.
          { subst. inv H. }
          exploit Memory.get_disjoint; [exact GET0|exact GET2|..]. i. des.
          { subst. timetac. }
          apply (x2 from); econs; ss.
          + refl.
          + econs. auto.
        - exfalso. inv H.
          exploit SOUND; try exact GET2. i.
          exploit Memory.get_ts; try exact GET. i. des.
          { subst. rewrite GET1 in GET0. inv GET0. }
          exploit Memory.get_disjoint; [exact GET|exact x|..]. i. des.
          { subst. rewrite GET1 in GET2. inv GET2. }
          destruct (Time.le_lt_dec to to2).
          + apply (x3 to); econs; ss. refl.
          + apply (x3 to2); econs; ss.
            * econs. auto.
            * refl.
      }
      exploit MIDDLE; try eapply x1; eauto. i.
      destruct (Time.eq_dec to from2).
      + subst. rewrite GET in x0. inv x0. esplits; eauto.
      + exfalso. inv x1.
        exploit Memory.get_ts; try exact GET. i. des.
        { subst. rewrite GET1 in x. inv x. }
        exploit Memory.get_ts; try exact x0. i. des.
        { subst. exploit SOUND; try exact GET3. i.
          exploit Memory.get_disjoint; [exact GET|exact x1|..]. i. des.
          { subst. rewrite GET1 in GET3. inv GET3. }
          destruct (Time.le_lt_dec to to2).
          - apply (x4 to); econs; ss. refl.
          - apply (x4 to2); econs; ss.
            + econs. auto.
            + refl.
        }
        exploit Memory.get_disjoint; [exact GET|exact x0|..]. i. des; try congr.
        destruct (Time.le_lt_dec to from2).
        * apply (x4 to); econs; ss. refl.
        * apply (x4 from2); econs; ss.
          { econs. auto. }
          { refl. }
    - right. inv H. do 2 (split; auto).
      rewrite GET0 in x. inv x.
      specialize (BACK loc).
      exploit Memory.get_ts; try exact GET. i. des; try congr.
      exploit Memory.get_disjoint; [exact GET|exact BACK|..]. i. des.
      { subst. esplits; eauto. }
      exfalso.
      destruct (Time.le_lt_dec to (tm loc)).
      + apply (x1 to); econs; ss. refl.
      + apply (x1 (tm loc)); econs; s;
          eauto using TM; try refl.
        econs. ss.
  Qed.

  Lemma cap_flex_exists
        mem1 tm
        (CLOSED1: Memory.closed mem1)
        (TM: forall loc, Time.lt (Memory.max_ts loc mem1) (tm loc))
    :
      exists mem2, (<<CAP: cap_flex mem1 mem2 tm>>).
  Proof.
    hexploit Memory.cap_exists; eauto. i. des.
    hexploit (@choice
                Loc.t Cell.t
                (fun loc cell =>
                   forall ts,
                     Cell.get ts cell =
                     if (Time.eq_dec ts (tm loc))
                     then Some (Memory.max_ts loc mem1, Message.reserve)
                     else if (Time.eq_dec ts (Time.incr (Memory.max_ts loc mem1)))
                          then None
                          else Memory.get loc ts mem2)).
    { intros loc.
      hexploit (@Cell.remove_exists (mem2 loc)).
      { inv CAP. eapply BACK. } i. des.
      hexploit (@Cell.add_exists cell2 (Memory.max_ts loc mem1) (tm loc) Message.reserve).
      { i. erewrite Cell.remove_o in GET2; eauto. des_ifs.
        eapply Memory.cap_inv in GET2; eauto. des; clarify.
        { symmetry. eapply interval_le_disjoint.
          eapply Memory.max_ts_spec in GET2. des. auto. }
        { inv GET0. symmetry. eapply interval_le_disjoint.
          transitivity to0.
          { eapply memory_get_ts_le; eauto. }
          { eapply Memory.max_ts_spec in GET4. des. auto. }
        }
      }
      { eauto. }
      { econs. } i. des.
      exists cell0. i.
      erewrite Cell.add_o; eauto. erewrite Cell.remove_o; eauto. des_ifs. }
    intros [mem3 SPEC].

    exists mem3. dup CAP. inv CAP. econs.
    { ii. unfold Memory.get. rewrite SPEC. des_ifs.
      { eapply Memory.max_ts_spec in LHS. des.
        exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
        { eapply TM. }
        { eapply MAX. }
      }
      { eapply Memory.max_ts_spec in LHS. des.
        exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
        { eapply Time.incr_spec. }
        { eapply MAX. }
      }
      { eapply SOUND; auto. }
    }
    { i. unfold Memory.get. erewrite SPEC. dup ADJ. inv ADJ. des_ifs.
      { dup GET2. apply Memory.max_ts_spec in GET2. des.
        apply Memory.get_ts in GET0. des; subst.
        { exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
          { eapply TS. }
          { eapply Time.bot_spec. }
        }
        { exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
          { eapply GET0. } etrans.
          { eapply MAX. }
          { left. eauto. }
        }
      }
      { dup GET2. apply Memory.max_ts_spec in GET2. des.
        apply Memory.get_ts in GET0. des; subst.
        { exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
          { eapply TS. }
          { eapply Time.bot_spec. }
        }
        { exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
          { eapply GET0. } etrans.
          { eapply MAX. }
          { left. eapply Time.incr_spec. }
        }
      }
      { eapply MIDDLE; eauto. }
    }
    { i. unfold Memory.get. erewrite SPEC. des_ifs. }
    { i. unfold Memory.get in GET2. rewrite SPEC in GET2. des_ifs.
      { hexploit (@Memory.max_ts_spec loc).
        { inv CLOSED1. eapply INHABITED. }
        i. des. eauto. }
      { eapply COMPLETE; eauto. }
    }
  Qed.

  Lemma cap_cap_flex mem1 mem2
        (CAP: Memory.cap mem1 mem2)
    :
      cap_flex mem1 mem2 (fun loc => Time.incr (Memory.max_ts loc mem1)).
  Proof.
    inv CAP. econs; eauto.
  Qed.

  Lemma cap_flex_max_ts mem1 mem2 tm
        (CLOSED: Memory.closed mem1)
        (CAP: cap_flex mem1 mem2 tm)
        (TM: forall loc, Time.lt (Memory.max_ts loc mem1) (tm loc))
    :
      forall loc,
        Memory.max_ts loc mem2 = tm loc.
  Proof.
    i. dup CAP. inv CAP0. specialize (BACK loc).
    exploit Memory.max_ts_spec; try exact BACK. i. des.
    apply TimeFacts.antisym; ss.
    destruct (Time.le_lt_dec (Memory.max_ts loc mem2) (tm loc)); ss.
    exploit cap_flex_inv; try exact GET; eauto. i. des.
    - exploit Memory.max_ts_spec; try exact x0. i. des.
      exploit TimeFacts.lt_le_lt; try exact l; try exact MAX0. i.
      specialize (TM loc). rewrite x1 in TM. timetac.
    - inv x1. exploit Memory.get_ts; try exact GET2. i. des.
      { rewrite x1 in *. inv l. }
      exploit Memory.max_ts_spec; try exact GET2. i. des.
      exploit TimeFacts.lt_le_lt; try exact x1; try exact MAX0. i.
      rewrite x3 in l. specialize (TM loc). rewrite l in TM. timetac.
    - subst. rewrite x2 in *. timetac.
  Qed.

  Lemma cap_flex_covered
        mem0 mem1 tm
        (CAP: cap_flex mem0 mem1 tm)
        (CLOSED: Memory.closed mem0)
        (TM: forall loc, Time.lt (Memory.max_ts loc mem0) (tm loc))
        loc to
    :
      Interval.mem (Time.bot, (tm loc)) to
      <->
      covered loc to mem1.
  Proof.
    split; i.
    {
      inv H. inv CAP. set (@cell_elements_least
                             (mem0 loc)
                             (fun to' => Time.le to to')). des; cycle 1.
      { destruct (Time.le_lt_dec to (Memory.max_ts loc mem0)).
        - exfalso. exploit Memory.max_ts_spec.
          + eapply CLOSED.
          + i. des. exploit EMPTY; eauto.
        - econs.
          + eapply BACK.
          + econs; eauto. }
      set (@cell_elements_greatest
             (mem0 loc)
             (fun to' => Time.lt to' to)). des; cycle 1.
      { exfalso. exploit EMPTY.
        - eapply CLOSED.
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
              { eapply TS2. }
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
        + eapply SOUND. eapply GET.
        + econs; eauto.
    }
    {
      inv H. apply Memory.max_ts_spec in GET. des.
      inv ITV. ss. econs; ss.
      - eapply TimeFacts.le_lt_lt; eauto. apply Time.bot_spec.
      - etrans; eauto. erewrite <- cap_flex_max_ts; eauto.
    }
  Qed.

End CAPFLEX.


Section MIDDLE.

  Variable L: Loc.t -> bool.
  Variable times: Loc.t -> list Time.t.

  Lemma sim_memory_max_ts_le F extra mem_src mem_tgt
        (MEM: sim_memory L times F extra mem_src mem_tgt)
        (MEMTGT: Memory.closed mem_tgt)
        loc
    :
      Time.le (Memory.max_ts loc mem_tgt) (Memory.max_ts loc mem_src).
  Proof.
    hexploit (@Memory.max_ts_spec loc).
    { inv MEMTGT. eapply INHABITED. } i. des.
    destruct (Memory.get loc (Memory.max_ts loc mem_tgt) mem_src) as [[from_src msg_src]|] eqn:GETSRC; cycle 1.
    { exfalso. eapply sim_memory_src_none in GETSRC; eauto. des; clarify. }
    apply Memory.max_ts_spec in GETSRC. des. auto.
  Qed.

  Lemma sim_memory_max_ts_extra F extra mem_src mem_tgt
        (MEM: sim_memory L times F extra mem_src mem_tgt)
        (MEMTGT: Memory.closed mem_tgt)
        loc
    :
      Memory.max_ts loc mem_src = Memory.max_ts loc mem_tgt \/
      extra loc (Memory.max_ts loc mem_src) (Memory.max_ts loc mem_tgt).
  Proof.
    hexploit sim_memory_max_ts_le; eauto. intros [TS|[]]; auto.
    assert (exists from_bot msg_bot, <<GETBOTSRC: Memory.get loc Time.bot mem_src = Some (from_bot, msg_bot)>>).
    { set (MEM0:=MEM.(sim_memory_contents) loc Time.bot).
      inv MEMTGT. erewrite INHABITED in MEM0. inv MEM0; eauto. }
    des. eapply Memory.max_ts_spec in GETBOTSRC. des.
    dup GET. eapply sim_memory_get_larger in GET; eauto. des.
    { apply Memory.max_ts_spec in GETTGT. des.
      left. apply Memory.max_ts_spec in GET. des.
      apply TimeFacts.antisym; auto.
      destruct (Memory.get loc (Memory.max_ts loc mem_tgt) mem_src) as [[from_src msg_src]|] eqn:GETSRC; cycle 1.
      { exfalso. eapply sim_memory_src_none in GETSRC; eauto. des; clarify. }
      eapply Memory.max_ts_spec in GETSRC; eauto. des. auto.
    }
    { hexploit (MEM.(sim_memory_wf) loc from (Memory.max_ts loc mem_src)); eauto. i. des.
      set (MEM0 := MEM.(sim_memory_contents) loc from). inv MEM0; ss. symmetry in H.
      right. replace (Memory.max_ts loc mem_tgt) with from; auto.
      apply Memory.max_ts_spec in H; eauto. des. apply TimeFacts.antisym; auto.
      destruct (Memory.get loc (Memory.max_ts loc mem_tgt) mem_src) as [[ts msg_src]|] eqn:GETSRC; cycle 1.
      { exfalso. eapply sim_memory_src_none in GETSRC; eauto. des; clarify. }
      hexploit memory_get_disjoint_strong.
      { eapply GETSRC. }
      { eapply GET0. }
      i. des; auto.
      { subst. rewrite H in *. timetac. }
      { exfalso. eapply Time.lt_strorder. etrans; [apply TS|eauto]. }
    }
  Qed.

  (* sim memory strong *)
  Inductive sim_memory_content_strong
            (F: Prop)
            (extra: Time.t -> Prop)
            (extra_all: Time.t -> Time.t -> Prop)
            (loc: Loc.t) (ts: Time.t)
    : option (Time.t * Message.t) -> option (Time.t * Message.t) -> Prop :=
  | sim_memory_content_strong_none
      (NPROM: ~ F)
      (NEXTRA: forall t, ~ extra t)
    :
      sim_memory_content_strong F extra extra_all loc ts None None
  | sim_memory_content_strong_normal
      from_src from_tgt msg
      (NPROM: ~ F)
      (NEXTRA: forall t, ~ extra t)
      (FROM: Time.le from_tgt from_src)
      (LB: forall (LOC: L loc), lb_time (times loc) from_tgt from_src)
      (EXTRA: from_tgt = from_src \/ extra_all from_src from_tgt)
      (NLOC: ~ L loc -> from_src = from_tgt)
    :
      sim_memory_content_strong F extra extra_all loc ts (Some (from_src, msg)) (Some (from_tgt, msg))
  | sim_memory_content_strong_forget
      from_src from_tgt val released
      (PROM: F)
      (NEXTRA: forall t, ~ extra t)
      (NLOC: L loc)
      (FROM: Time.le from_tgt from_src)
      (LB: lb_time (times loc) from_tgt from_src)
      (EXTRA: from_tgt = from_src \/ extra_all from_src from_tgt)
    :
      sim_memory_content_strong F extra extra_all loc ts (Some (from_src, Message.reserve)) (Some (from_tgt, Message.concrete val released))
  | sim_memory_content_strong_extra
      from
      (NPROM: ~ F)
      (EXTRA: extra from)
      (NLOC: L loc)
    :
      sim_memory_content_strong F extra extra_all loc ts (Some (from, Message.reserve)) None
  .
  Hint Constructors sim_memory_content_strong.
  Hint Constructors sim_memory_content.

  Lemma sim_memory_content_strong_sim_memory_content
        loc ts F extra get0 get1 extra_all
        (SIM: sim_memory_content_strong F extra extra_all loc ts get0 get1)
    :
      sim_memory_content L times F extra loc ts get0 get1.
  Proof.
    inv SIM; econs; eauto.
  Qed.

  Record sim_memory_strong
         (F: Loc.t -> Time.t -> Prop)
         (extra: Loc.t -> Time.t -> Time.t -> Prop)
         (mem_src mem_tgt: Memory.t): Prop :=
    {
      sim_memory_strong_contents:
        forall loc ts,
          sim_memory_content_strong (F loc ts) (extra loc ts) (extra loc)
                                    loc ts (Memory.get loc ts mem_src) (Memory.get loc ts mem_tgt);
      sim_memory_strong_wf:
        forall loc from ts (EXTRA: extra loc ts from),
          (<<FORGET: F loc from>>) /\
          (<<LB: lb_time (times loc) from ts>>) /\
          (<<TS: Time.lt from ts>>) /\
          (<<UNIQUE: forall from' (EXTRA: extra loc ts from'),
              from' = from>>);
    }.

  Lemma sim_memory_strong_sim_memory
        self extra prom_src prom_tgt
        (SIM: sim_memory_strong self extra prom_src prom_tgt)
    :
      sim_memory L times self extra prom_src prom_tgt.
  Proof.
    econs.
    - ii. eapply sim_memory_content_strong_sim_memory_content; eauto.
      eapply SIM; eauto.
    - apply SIM.
  Qed.

  Lemma sim_memory_strong_left_end F extra mem_src mem_tgt
        (MEM: sim_memory_strong F extra mem_src mem_tgt)
        loc from to_tgt msg_tgt
        (GETTGT: Memory.get loc to_tgt mem_tgt = Some (from, msg_tgt))
    :
      exists to_src msg_src,
        (<<GETSRC: Memory.get loc to_src mem_src = Some (from, msg_src)>>).
  Proof.
    set (MEM0:=MEM.(sim_memory_strong_contents) loc to_tgt).
    rewrite GETTGT in *. inv MEM0.
    { des; clarify; eauto.
      set (MEM0:=MEM.(sim_memory_strong_contents) loc from_src).
      inv MEM0; try by (exfalso; eapply NEXTRA0; eauto).
      eapply MEM.(sim_memory_strong_wf) in EXTRA. des.
      apply UNIQUE in EXTRA0. subst. eauto. }
    { des; clarify; eauto.
      set (MEM0:=MEM.(sim_memory_strong_contents) loc from_src).
      inv MEM0; try by (exfalso; eapply NEXTRA0; eauto).
      eapply MEM.(sim_memory_strong_wf) in EXTRA. des.
      apply UNIQUE in EXTRA0. subst. eauto. }
  Qed.

  Lemma sim_memory_strong_left_end_inv F extra mem_src mem_tgt
        (MEM: sim_memory_strong F extra mem_src mem_tgt)
        loc from to_src msg_src
        (GETSRC: Memory.get loc to_src mem_src = Some (from, msg_src))
        (NONE: Memory.get loc from mem_src = None)
    :
      exists to_tgt msg_tgt,
        (<<GETTGT: Memory.get loc to_tgt mem_tgt = Some (from, msg_tgt)>>).
  Proof.
    set (MEM0:=MEM.(sim_memory_strong_contents) loc to_src).
    rewrite GETSRC in *. inv MEM0.
    { des; clarify; eauto.
      set (MEM0:=MEM.(sim_memory_strong_contents) loc from).
      inv MEM0; try by (exfalso; eapply NEXTRA0; eauto).
      rewrite NONE in *. clarify. }
    { des; clarify; eauto.
      set (MEM0:=MEM.(sim_memory_strong_contents) loc from).
      inv MEM0; try by (exfalso; eapply NEXTRA0; eauto).
      rewrite NONE in *. clarify. }
    { exploit (MEM.(sim_memory_strong_wf) loc from to_src); eauto. i. des.
      set (MEM0:=MEM.(sim_memory_strong_contents) loc from). inv MEM0; ss.
      rewrite NONE in *. clarify. }
  Qed.

  Lemma sim_memory_right_end F extra mem_src mem_tgt
        (MEM: sim_memory L times F extra mem_src mem_tgt)
        loc from_tgt to_tgt msg_tgt ts
        (GETTGT: Memory.get loc to_tgt mem_tgt = Some (from_tgt, msg_tgt))
        (TS: Time.lt to_tgt ts)
        (TIMES: List.In ts (times loc))
        (EMPTY: forall t (TS0: Time.lt to_tgt t) (TS1: Time.le t ts),
            Memory.get loc t mem_tgt = None)
    :
      exists from_src to_src msg_src,
        (<<GETSRC: Memory.get loc to_src mem_src = Some (from_src, msg_src)>>) /\
        (<<TS: Time.lt to_src ts>>) /\
        (<<EMPTY: forall t (TS0: Time.lt to_src t) (TS1: Time.le t ts),
            Memory.get loc t mem_src = None>>) /\
        (<<EXTRA: __guard__(to_tgt = to_src \/ extra loc to_src to_tgt)>>)
  .
  Proof.
    destruct (classic (exists to_src, <<EXTRA: extra loc to_src to_tgt>>)) as [EXTRA|NEXTRA].
    { des. set (MEM0:=MEM.(sim_memory_contents) loc to_src).
      inv MEM0; try by (exfalso; eapply NEXTRA; eauto).
      assert (TS1: Time.lt to_src ts).
      { eapply MEM.(sim_memory_wf) in EXTRA0. des.
        eapply UNIQUE in EXTRA. subst. eapply LB; auto. }

      exploit (MEM.(sim_memory_wf) loc to_tgt to_src); auto. i. des.
      eapply UNIQUE in EXTRA. subst.
      esplits; eauto; cycle 1.
      { right. auto. } i.

      destruct (Memory.get loc t mem_src) as [[from_src0 msg_src0]|] eqn:GETSRC0; auto.
      eapply sim_memory_get_larger in GETSRC0; eauto. des.
      { erewrite EMPTY in GETTGT0; clarify. etrans; eauto. }
      { exploit (MEM.(sim_memory_wf) loc from_src0 t); auto. i. des.
        set (MEM0:=MEM.(sim_memory_contents) loc from_src0). inv MEM0; ss.
        hexploit memory_get_disjoint_strong.
        { symmetry. eapply H3. }
        { eapply GETTGT. }
        i. des; subst.
        { exfalso. hexploit sim_memory_extra_inj; try apply MEM.
          { eapply EXTRA0. }
          { eapply EXTRA. }
          i. subst. timetac.
        }
        { set (MEM0:=MEM.(sim_memory_contents) loc t).
          inv MEM0; try by (exfalso; eapply NEXTRA0; eauto).
          eapply UNIQUE0 in EXTRA1. subst.
          hexploit Memory.get_disjoint.
          { symmetry. apply H4. }
          { symmetry. apply H0. }
          i. des; subst.
          { clarify. exfalso. timetac. }
          { exfalso. eapply H1.
            { instantiate (1:=to_src). econs; ss.
              { transitivity to_tgt; auto. }
              { left. auto. }
            }
            { econs; ss. refl. }
          }
        }
        { set (MEM0:=MEM.(sim_memory_contents) loc from_src0). inv MEM0; ss.
          erewrite EMPTY in H3; clarify. transitivity t; auto. left. auto. }
      }
    }
    { destruct (Memory.get loc to_tgt mem_src) as [[from_src msg_src]|] eqn:GETSRC.
      { esplits; eauto; cycle 1.
        { left. auto. } i.
        destruct (Memory.get loc t mem_src) as [[from_src0 msg_src0]|] eqn:GETSRC0; auto.
        eapply sim_memory_get_larger in GETSRC0; eauto. des.
        { erewrite EMPTY in GETTGT0; clarify. }
        { exploit (MEM.(sim_memory_wf) loc from_src0 t); auto. i. des.
          set (MEM0:=MEM.(sim_memory_contents) loc from_src0). inv MEM0; ss.
          hexploit memory_get_disjoint_strong.
          { symmetry. eapply H. }
          { eapply GETTGT. }
          i. des; subst.
          { exfalso. eapply NEXTRA. eauto. }
          { set (MEM0:=MEM.(sim_memory_contents) loc t).
            inv MEM0; try by (exfalso; eapply NEXTRA1; eauto).
            eapply UNIQUE in EXTRA0. subst.
            hexploit Memory.get_disjoint.
            { symmetry. apply H2. }
            { eapply GETSRC. }
            i. des; subst.
            { clarify. exfalso. timetac. }
            { exfalso. eapply H1.
              { instantiate (1:=to_tgt). econs; ss. left. auto. }
              { econs; ss; [|refl].
                apply memory_get_ts_strong in GETSRC. des; auto.
                subst. exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
                { eapply TS4. }
                { eapply Time.bot_spec. }
              }
            }
          }
          { set (MEM0:=MEM.(sim_memory_contents) loc from_src0). inv MEM0; ss.
            erewrite EMPTY in H3; clarify. transitivity t; auto. left. auto. }
        }
      }
      { eapply sim_memory_src_none in GETSRC; eauto. des. clarify. }
    }
  Qed.


  Lemma sim_memory_strong_adjancent F extra mem_src mem_tgt
        (MEM: sim_memory_strong F extra mem_src mem_tgt)
        (MEMWF: memory_times_wf times mem_tgt)
        loc from1_tgt to1_tgt from2 to2_tgt
        (ADJ: Memory.adjacent loc from1_tgt to1_tgt from2 to2_tgt mem_tgt)
        (TS: Time.lt to1_tgt from2)
    :
      exists from1_src to1_src to2_src,
        (<<ADJ: Memory.adjacent loc from1_src to1_src from2 to2_src mem_src>>) /\
        (<<TS: Time.lt to1_src from2>>) /\
        (<<FROM: Time.le to1_tgt to1_src>>) /\
        (<<LB: forall (LOC: L loc), lb_time (times loc) to1_tgt to1_src>>) /\
        (<<EXTRA: __guard__(to1_tgt = to1_src \/ extra loc to1_src to1_tgt)>>) /\
        (<<NLOC: ~ L loc -> to1_src = to1_tgt>>).
  Proof.
    inv ADJ. hexploit sim_memory_strong_left_end; eauto. i. des.
    hexploit sim_memory_right_end.
    { eapply sim_memory_strong_sim_memory. eauto. }
    { eapply GET1. }
    { eapply TS. }
    { apply MEMWF in GET2. des. auto. }
    { eauto. }
    i. des. exists from_src, to_src0, to_src.
    destruct EXTRA.
    { subst. splits; ss.
      { econs; eauto. eapply TimeFacts.lt_le_lt; eauto. eapply memory_get_ts_le; eauto. }
      { refl. }
      { i. eapply eq_lb_time. }
      { left. auto. }
    }
    { dup H. apply MEM.(sim_memory_strong_wf) in H. des. splits; ss.
      { econs; eauto. eapply TimeFacts.lt_le_lt; eauto. eapply memory_get_ts_le; eauto. }
      { left. auto. }
      { right. auto. }
      { i. set (MEM0:=MEM.(sim_memory_strong_contents) loc to_src0).
        inv MEM0; ss; try by (exfalso; eapply NEXTRA; eauto). }
    }
  Qed.

  Lemma cap_left_end mem1 mem2 tm loc ts1 ts2 msg1
        (MEM: Memory.closed mem1)
        (CAP: cap_flex mem1 mem2 tm)
        (GET: Memory.get loc ts2 mem1 = Some (ts1, msg1))
    :
      exists ts0 msg0,
        (<<GET: Memory.get loc ts1 mem2 = Some (ts0, msg0)>>).
  Proof.
    destruct (Memory.get loc ts1 mem1) as [[ts0 msg0]|] eqn:GETORG.
    { inv CAP. eapply SOUND in GETORG; eauto. }
    { hexploit (@cell_elements_greatest
                  (mem1 loc)
                  (fun ts => Time.lt ts ts1)). i. des; cycle 1.
      { inv MEM. specialize (INHABITED loc).
        hexploit EMPTY; eauto. intros TS.
        destruct (Time.le_lt_dec ts1 Time.bot); ss. destruct l.
        { exfalso. eapply Time.lt_strorder.
          eapply TimeFacts.lt_le_lt; eauto. eapply Time.bot_spec. }
        { inv H. clarify. }
      }
      inv CAP. hexploit MIDDLE.
      { econs.
        { eapply GET0. }
        { eapply GET. }
        { eapply TimeFacts.lt_le_lt; eauto. eapply memory_get_ts_le; eauto. }
        { i. destruct TS2.
          { destruct (Memory.get loc ts mem1) eqn:GETTS; auto. destruct p.
            eapply GREATEST in GETTS; eauto. timetac. }
          { inv H. eauto. }
        }
      }
      { auto. }
      eauto.
    }
  Qed.

  Lemma sim_memory_strong_cap F extra mem_src mem_tgt tm cap_src cap_tgt
        (MEM: sim_memory_strong F extra mem_src mem_tgt)
        (MEMSRC: Memory.closed mem_src)
        (MEMTGT: Memory.closed mem_tgt)
        (MEMWF: memory_times_wf times mem_tgt)
        (CAPSRC: cap_flex mem_src cap_src tm)
        (CAPTGT: cap_flex mem_tgt cap_tgt tm)
        (TM: forall loc, Time.lt (Memory.max_ts loc mem_src) (tm loc))
    :
      sim_memory L times F extra cap_src cap_tgt.
  Proof.
    assert (TMTGT: forall loc, Time.lt (Memory.max_ts loc mem_tgt) (tm loc)).
    { i. eapply TimeFacts.le_lt_lt; eauto.
      eapply sim_memory_max_ts_le; try apply MEMSRC; eauto.
      eapply sim_memory_strong_sim_memory; eauto. }

    dup CAPTGT. inv CAPTGT0. dup CAPSRC. inv CAPSRC0. econs.
    { i. set (MEM0:=MEM.(sim_memory_strong_contents) loc ts).
      inv MEM0; symmetry in H; symmetry in H0; rename H into GETMEMTGT; rename H0 into GETMEMSRC.
      { destruct (Memory.get loc ts cap_tgt) as [[from_tgt msg_tgt]|] eqn:GETTGT; eauto.
        { eapply cap_flex_inv in GETTGT; try apply CAPTGT; eauto. des; clarify.
          { hexploit sim_memory_strong_adjancent; eauto. i. des.
            erewrite MIDDLE0; eauto. }
          { erewrite BACK0. i. econs 2; auto.
            { eapply sim_memory_max_ts_le; eauto. eapply sim_memory_strong_sim_memory; eauto. }
            { i. hexploit sim_memory_max_ts_extra.
              { eapply sim_memory_strong_sim_memory; eauto. }
              { eauto. }
              i. des.
              { rewrite H. apply eq_lb_time. }
              { apply MEM.(sim_memory_strong_wf) in H. des. auto. }
            }
            { i. hexploit (@Memory.max_ts_spec loc).
              { inv MEMSRC. eapply INHABITED. } i. des.
              i. hexploit (@Memory.max_ts_spec loc).
              { inv MEMTGT. eapply INHABITED. } i. des.
              apply TimeFacts.antisym.
              { set (MEM0:=MEM.(sim_memory_strong_contents) loc (Memory.max_ts loc mem_src)).
                erewrite GET in MEM0. inv MEM0; ss.
                symmetry in H3. eapply Memory.max_ts_spec in H3. des; auto. }
              { set (MEM0:=MEM.(sim_memory_strong_contents) loc (Memory.max_ts loc mem_tgt)).
                erewrite GET0 in MEM0. inv MEM0; ss.
                symmetry in H1. eapply Memory.max_ts_spec in H1. des; auto. }
            }
          }
        }
        { destruct (Memory.get loc ts cap_src) as [[from_src msg_src]|] eqn:GETSRC; eauto.
          eapply cap_flex_inv in GETSRC; try apply CAPSRC; eauto. des; clarify.
          { inv GETSRC0. exploit sim_memory_strong_left_end_inv; eauto. i. des.
            eapply cap_left_end in GETTGT0; eauto. des. clarify. }
          { erewrite BACK in GETTGT. clarify. }
        }
      }
      { eapply SOUND0 in GETMEMSRC. eapply SOUND in GETMEMTGT.
        rewrite GETMEMSRC. rewrite GETMEMTGT. eauto. }
      { eapply SOUND0 in GETMEMSRC. eapply SOUND in GETMEMTGT.
        rewrite GETMEMSRC. rewrite GETMEMTGT. eauto. }
      { dup GETMEMSRC. eapply SOUND0 in GETMEMSRC. rewrite GETMEMSRC.
        destruct (Memory.get loc ts cap_tgt) as [[from_tgt msg_tgt]|] eqn:GETTGT; eauto.
        eapply cap_flex_inv in GETTGT; eauto. des; clarify.
        { inv GETTGT0. eapply MEM.(sim_memory_strong_wf) in EXTRA. des.
          exploit LB.
          { eapply MEMWF in GET2. des. eapply FROM. }
          { auto. }
          i. timetac.
        }
        { eapply Memory.max_ts_spec in GETMEMSRC0. des.
          exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
          { eapply TM. }
          { eapply MAX. }
        }
      }
    }
    { eapply MEM.(sim_memory_strong_wf); eauto. }
  Qed.

  Definition sim_cell_list
             loc
             (F: Loc.t -> Time.t -> Prop)
             (extra: Loc.t -> Time.t -> Time.t -> Prop)
             (cell_src cell_tgt: Cell.t)
             (l: list Time.t)
    :=
      forall ts,
        (<<CONTENT: sim_memory_content
                      L times
                      (F loc ts) (extra loc ts)
                      loc ts (Cell.get ts cell_src) (Cell.get ts cell_tgt)>>) /\
        ((<<STRONG: sim_memory_content_strong
                      (F loc ts) (extra loc ts) (extra loc)
                      loc ts (Cell.get ts cell_src) (Cell.get ts cell_tgt)>>) \/
         (<<LIN: List.In ts l>>)).

  Lemma sim_cell_list_exists loc F extra cell_src cell_tgt
        (CELL: forall ts,
            sim_memory_content L times (F loc ts) (extra loc ts)
                               loc ts (Cell.get ts cell_src) (Cell.get ts cell_tgt))
    :
      exists l,
        (<<CELL: sim_cell_list loc F extra cell_src cell_tgt l>>).
  Proof.
    hexploit (Cell.finite cell_src). i. des. exists dom. ii. splits; auto.
    destruct (Cell.get ts cell_src) as [[from_src msg_src]|] eqn:GETSRC.
    { right. eauto. }
    { specialize (CELL ts). rewrite GETSRC in *. inv CELL; eauto. }
  Qed.

  Lemma sim_cell_strong_exists loc F extra cell_src cell_tgt
        (CELL: forall ts,
            sim_memory_content L times (F loc ts) (extra loc ts)
                               loc ts (Cell.get ts cell_src) (Cell.get ts cell_tgt))
        (WF: forall loc from ts (EXTRA: extra loc ts from),
            (<<FORGET: F loc from>>) /\
            (<<LB: lb_time (times loc) from ts>>) /\
            (<<TS: Time.lt from ts>>) /\
            (<<UNIQUE: forall from' (EXTRA: extra loc ts from'),
                from' = from>>))
    :
      exists cell_src',
        (<<CELL: forall ts,
            sim_memory_content_strong
              (F loc ts) (extra loc ts) (extra loc)
              loc ts (Cell.get ts cell_src') (Cell.get ts cell_tgt)>>).
  Proof.
    destruct (classic (L loc)) as [LOC|NLOC]; cycle 1.
    { exists cell_src. ii. specialize (CELL ts). inv CELL; ss; eauto.
      hexploit NLOC0; eauto. }

    hexploit sim_cell_list_exists; eauto. clear CELL. i. des. ginduction l.
    { i. exists cell_src. ii. specialize (CELL ts). des; ss. }
    i. assert (exists cell_src', sim_cell_list loc F extra cell_src' cell_tgt l).
    { set (CELL a). des.
      { exists cell_src. ii. splits.
        { apply CELL. }
        { destruct (Time.eq_dec a ts).
          { subst. left. auto. }
          { specialize (CELL ts). des; auto. ss. des; auto; ss. }
        }
      } clear LIN.

      destruct (Time.le_lt_dec a Time.bot).
      { assert (a = Time.bot).
        { apply TimeFacts.antisym; auto. apply Time.bot_spec. } subst.
        exists cell_src. ii. splits.
        { apply CELL. }
        { destruct (Time.eq_dec Time.bot ts).
          { subst. left. inv CONTENT; eauto.
            { econs; eauto. left.
              symmetry in H. symmetry in H0. eapply TimeFacts.antisym.
              { eapply Cell.get_ts in H. des; subst.
                { eapply Time.bot_spec. }
                { exfalso. eapply Time.lt_strorder.
                  eapply (@TimeFacts.lt_le_lt from_tgt Time.bot); eauto.
                  eapply Time.bot_spec.
                }
              }
              { eapply Cell.get_ts in H0. des; subst.
                { eapply Time.bot_spec. }
                { exfalso. eapply Time.lt_strorder.
                  eapply (@TimeFacts.lt_le_lt from_src Time.bot); eauto.
                  eapply Time.bot_spec.
                }
              }
            }
            { econs; eauto. left.
              symmetry in H. symmetry in H0. eapply TimeFacts.antisym.
              { eapply Cell.get_ts in H. des; subst.
                { eapply Time.bot_spec. }
                { exfalso. eapply Time.lt_strorder.
                  eapply (@TimeFacts.lt_le_lt from_tgt Time.bot); eauto.
                  eapply Time.bot_spec.
                }
              }
              { eapply Cell.get_ts in H0. des; subst.
                { eapply Time.bot_spec. }
                { exfalso. eapply Time.lt_strorder.
                  eapply (@TimeFacts.lt_le_lt from_src Time.bot); eauto.
                  eapply Time.bot_spec.
                }
              }
            }
          }
          { specialize (CELL ts). des; auto. ss. des; auto; ss. }
        }
      }

      inv CONTENT.
      { exists cell_src. ii. splits.
        { apply CELL. }
        { destruct (Time.eq_dec a ts).
          { subst. rewrite <- H. rewrite <- H0. left. eauto. }
          { specialize (CELL ts). des; auto. ss. des; auto; ss. }
        }
      }

      { symmetry in H. symmetry in H0.
        hexploit (@Cell.remove_exists cell_src from_src a msg); auto.
        intros [cell_src0 REMOVE].
        destruct (classic (exists from_src', extra loc from_src' from_tgt))
          as [[from_src' EXTRA]|].
        { hexploit WF; eauto. i. des.
          set (MEM0:=proj1 (CELL from_src')).
          inv MEM0; try by (exfalso; eapply NEXTRA0; eauto).
          eapply UNIQUE in EXTRA0. subst.
          hexploit (@Cell.add_exists cell_src0 from_src' a msg); auto.
          { i. erewrite Cell.remove_o in GET2; eauto. des_ifs.
            set (MEM0:=proj1 (CELL to2)). rewrite GET2 in MEM0. inv MEM0.
            { hexploit Cell.get_disjoint.
              { eapply H. }
              { symmetry. eapply H6. }
              i. des; subst; ss.
              eapply Interval.le_disjoint.
              { symmetry. symmetry in H1.
                eapply Interval.le_disjoint; try apply H1; eauto.
                econs; ss. refl. }
              { econs; ss; [|refl]. left. auto. }
            }
            { hexploit Cell.get_disjoint.
              { eapply H. }
              { symmetry. eapply H6. }
              i. des; subst; ss.
              eapply Interval.le_disjoint.
              { symmetry. symmetry in H1.
                eapply Interval.le_disjoint; try apply H1; eauto.
                econs; ss. refl. }
              { econs; ss; [|refl]. left. auto. }
            }
            hexploit WF; try apply EXTRA0. i. des.
            set (MEM0:=proj1 (CELL from2)). inv MEM0; ss.
            hexploit Cell.get_disjoint.
            { eapply H. }
            { symmetry. eapply H5. }
            i. des; subst; ss.
            ii. inv LHS. inv RHS. ss.
            destruct (Time.le_lt_dec to2 from_src); cycle 1.
            { exploit Cell.get_disjoint.
              { eapply GET2. }
              { eapply H0. }
              i. des; subst; ss. eapply x1.
              { instantiate (1:=Time.meet to2 a). econs; ss.
                { unfold Time.meet. des_ifs.
                  { eapply TimeFacts.lt_le_lt with (b:=x); auto. }
                }
                { eapply Time.meet_l. }
              }
              { econs; ss.
                { unfold Time.meet. des_ifs.
                  apply Cell.get_ts in H0. des; auto.
                  subst. timetac.
                }
                { eapply Time.meet_r. }
              }
            }
            destruct (Time.le_lt_dec from_src' from2); cycle 1.
            { exploit Cell.get_disjoint.
              { eapply GET2. }
              { symmetry. eapply H2. }
              i. des; subst; ss.
              { timetac. }
              eapply x1.
              { instantiate (1:=Time.meet to2 from_src'). econs; ss.
                { unfold Time.meet. des_ifs. }
                { eapply Time.meet_l. }
              }
              { econs; ss.
                { unfold Time.meet. des_ifs. eapply TimeFacts.lt_le_lt.
                  { eapply TS. } etrans.
                  { left. eapply FROM1. }
                  eauto.
                }
                { eapply Time.meet_r. }
              }
            }
            eapply H1.
            { instantiate (1:=from2). econs; ss.
              { eapply TimeFacts.lt_le_lt with (b:=from_src'); auto. }
              { transitivity x; auto. left. auto. }
            }
            { econs; ss; [|refl]. symmetry in H4.
              apply Cell.get_ts in H4. des.
              { subst. assert (from_src' = Time.bot).
                { apply TimeFacts.antisym; auto. apply Time.bot_spec. }
                subst. timetac.
              }
              { eapply TimeFacts.le_lt_lt with (b:=from_src0); auto. }
            }
          }
          { destruct (Time.le_lt_dec a from_src'); auto. exfalso.
            hexploit Cell.get_disjoint.
            { symmetry. eapply H2. }
            { eapply H0. }
            i. des; subst.
            { rewrite H in *. clarify. }
            { eapply H1.
              { instantiate (1:=a). econs; ss.
                eapply Cell.get_ts in H. des; auto. subst. timetac. }
              { econs; ss; [|refl].
                eapply Cell.get_ts in H0. des; auto. subst. timetac. }
            }
          }
          { eapply Cell.get_opt_wf in H0. auto. }
          intros [cell_src1 ADD]. exists cell_src1. ii.
          erewrite (@Cell.add_o cell_src1); eauto.
          erewrite (@Cell.remove_o cell_src0); eauto. des_ifs.
          { rewrite H. splits.
            { econs 2; eauto; ss. left. auto. }
            { left. econs 2; eauto; ss. left. auto. }
          }
          { specialize (CELL ts). des; auto. ss. des; clarify. splits; auto. }
        }
        {

        { admit. }
      }
      { admit. }
      { exists cell_src. ii. splits.
        { apply CELL. }
        { destruct (Time.eq_dec a ts).
          { subst. rewrite <- H. rewrite <- H0. left. eauto. }
          { specialize (CELL ts). des; auto. ss. des; auto; ss. }
        }
      }
    }
    des. eauto.
  Admitted.

          {


          {
            { admit. }
            { exists cell_src. ii. splits.
              { apply CELL. }
              { destruct (Time.eq_dec a ts).
                { subst. rewrite <- H. rewrite <- H0. left. eauto. }
                { specialize (CELL ts). des; auto. ss. des; auto; ss. }
              }
            }
          }
          des. eauto.
  Admitted.

        }



      { symmetry in H. symmetry in H0.
        hexploit (@Cell.remove_exists cell_src from_src a msg); auto.
        intros [cell_src0 REMOVE].
        destruct (classic (exists from_src', extra loc from_src' from_tgt))
          as [[from_src' EXTRA]|].
        { hexploit WF; eauto. i. des.
          set (MEM0:=proj1 (CELL from_src')).
          inv MEM0; try by (exfalso; eapply NEXTRA0; eauto).
          eapply UNIQUE in EXTRA0. subst.
          hexploit (@Cell.add_exists cell_src0 from_src' a msg); auto.
          { i. erewrite Cell.remove_o in GET2; eauto. des_ifs.
            ii. inv LHS. inv RHS. ss.

            destruct (Time.le_lt_dec to2 from_src); cycle 1.
            { exploit Cell.get_disjoint.
              { eapply GET2. }
              { eapply H0. }
              i. des; subst; ss. eapply x1.
              { instantiate (1:=Time.meet to2 a). econs; ss.
                { unfold Time.meet. des_ifs.
                  { eapply TimeFacts.lt_le_lt with (b:=x); auto. }
                  { eapply TimeFacts.lt_le_lt with (b:=x); auto. }
                }
                { eapply Time.meet_l. }
              }
              { econs; ss.
                { unfold Time.meet. des_ifs.
                  admit.
                }
                { eapply Time.meet_r. }
              }
            }

            destruct (Time.le_lt_dec from_src' from2); cycle 1.
            { exploit Cell.get_disjoint.
              { eapply GET2. }
              { symmetry. eapply H2. }
              i. des; subst; ss.
              { timetac. }
              eapply x1.
              { instantiate (1:=Time.meet to2 from_src'). econs; ss.
                { unfold Time.meet. des_ifs.
                  eapply TimeFacts.lt_le_lt with (b:=x); auto. }
                { eapply Time.meet_l. }
              }
              { econs; ss.
                { unfold Time.meet. des_ifs. eapply TimeFacts.lt_le_lt.
                  { eapply TS. } etrans.
                  { left. eapply FROM0. }
                  eauto.
                }
                { eapply Time.meet_r. }
              }
            }






                { eapply TimeFacts.lt_le_lt with (b:=x); auto. }
                }
                { eapply Time.meet_l. }
              }
              { econs; ss.
                { unfold Time.meet. des_ifs.
                  admit.
                }
                { eapply Time.meet_r. }
              }
            }

            {


                  { admit. }
                  {

                  eapply TimeFacts.lt_le_lt with (b:=x); auto. }
                  { eapply TimeFacts.lt_le_lt with (b:=x); auto. }
                }

                    d


                                   Time.meet

                instantiate (1:=to2). econs; ss; [|refl].
                admit.
              }
              { econs; ss.

                eapply TimeFacts.lt_le_lt; eauto. }
              { econs; ss; [|refl].
                admit.
              }
            }


            destruct (Time.le_lt_dec a to2).
            { exploit Cell.get_disjoint.
              { eapply GET2. }
              { eapply H0. }
              i. des; subst; ss. eapply x1.
              { instantiate (1:=a). econs; ss. eapply TimeFacts.lt_le_lt; eauto. }
              { econs; ss; [|refl].
                admit.
              }
            }






              {

              destruct l0.
              {


                admit. }
              { inv H1. ss. }
            }








            admit. }

          {
            admit. }
          { eapply Cell.get_opt_wf in H0. auto. }
          intros [cell_src1 ADD]. exists cell_src1. ii.
          erewrite (@Cell.add_o cell_src1); eauto.
          erewrite (@Cell.remove_o cell_src0); eauto. des_ifs.
          { rewrite H. splits.
            { econs 2; eauto; ss. left. auto. }
            { left. econs 2; eauto; ss. left. auto. }
          }
          { specialize (CELL ts). des; auto. ss. des; clarify. splits; auto. }
        }
        { admit. }
      }
      { admit. }
      { exists cell_src. ii. splits.
        { apply CELL. }
        { destruct (Time.eq_dec a ts).
          { subst. rewrite <- H. rewrite <- H0. left. eauto. }
          { specialize (CELL ts). des; auto. ss. des; auto; ss. }
        }
      }
    }
    des. eauto.
  Admitted.


    exploit IHl; eauto.


    hexploit
    {


    { eapply CONTENT.


      des; eauto.



  :



           sim_memory_content L times (F loc ts) (extra loc ts)
                               loc ts (Cell.get ts cell_src) (Cell.get ts cell_tgt))
    :
      exists l,
        (<<CELL: sim_cell_list_contents loc F extra cell_src cell_tgt l>>).
  Proof.
    hexploit (Cell.finite cell_src). i. des. exists dom. ii.
    destruct (Cell.get ts cell_src) as [[from_src msg_src]|] eqn:GETSRC.
    { right. rewrite <- GETSRC. splits; eauto. }
    { specialize (CELL loc ts). rewrite GETSRC in *. inv CELL; auto.
      left. econs; eauto. }
  Qed.


  Lemma sim_memory_strong_exists F extra mem_src mem_tgt
        (MEM: sim_memory L times F extra mem_src mem_tgt)
    :
      exists mem_src',
        (<<MEM: sim_memory_strong F extra mem_src' mem_tgt>>).
  Proof.



  Record sim_memory_strong
         (F: Loc.t -> Time.t -> Prop)
         (extra: Loc.t -> Time.t -> Time.t -> Prop)
         (mem_src mem_tgt: Memory.t): Prop :=
    {
      sim_memory_strong_contents:
        forall loc ts,
          sim_memory_content_strong (F loc ts) (extra loc ts) (extra loc)
                                    loc ts (Memory.get loc ts mem_src) (Memory.get loc ts mem_tgt);
      sim_memory_strong_wf:
        forall loc from ts (EXTRA: extra loc ts from),
          (<<FORGET: F loc from>>) /\
          (<<LB: lb_time (times loc) from ts>>) /\
          (<<TS: Time.lt from ts>>) /\
          (<<UNIQUE: forall from' (EXTRA: extra loc ts from'),
              from' = from>>);
    }.




End MIDDLE.
