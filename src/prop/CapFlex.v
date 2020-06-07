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

Set Implicit Arguments.

Section CAPFLEX.

  Record cap_flex (mem1 mem2: Memory.t) (tm: TimeMap.t): Prop :=
    {
      cap_flex_le: Memory.le mem1 mem2;
      cap_flex_middle: forall loc from1 to1 from2 to2
                              (ADJ: Memory.adjacent loc from1 to1 from2 to2 mem1)
                              (TO: Time.lt to1 from2),
          Memory.get loc from2 mem2 = Some (to1, Message.reserve);
      cap_flex_back: forall loc, Memory.get loc (tm loc) mem2 =
                                 Some (Memory.max_ts loc mem1, Message.reserve);
      cap_flex_complete: forall loc from to msg
                               (GET1: Memory.get loc to mem1 = None)
                               (GET2: Memory.get loc to mem2 = Some (from, msg)),
          (exists f m, Memory.get loc from mem1 = Some (f, m));
    }
  .

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
    { exploit cap_flex_le0; eauto. i.
      rewrite GET in x. inv x. auto. }
    right. exploit cap_flex_complete0; eauto. i. des.
    exploit Memory.max_ts_spec; eauto. i. des. inv MAX.
    - left.
      exploit Memory.adjacent_exists; try eapply H; eauto. i. des.
      assert (LT: Time.lt from from2).
      { clear cap_flex_middle0 cap_flex_back0 cap_flex_complete0 GET0 H.
        (* clear MIDDLE BACK COMPLETE GET0 H. *)
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
          exploit cap_flex_le0; try exact GET2. i.
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
      exploit cap_flex_middle0; try eapply x1; eauto. i.
      destruct (Time.eq_dec to from2).
      + subst. rewrite GET in x0. inv x0. esplits; eauto.
      + exfalso. inv x1.
        exploit Memory.get_ts; try exact GET. i. des.
        { subst. rewrite GET1 in x. inv x. }
        exploit Memory.get_ts; try exact x0. i. des.
        { subst. exploit cap_flex_le0; try exact GET3. i.
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
      specialize (cap_flex_back0 loc).
      exploit Memory.get_ts; try exact GET. i. des; try congr.
      exploit Memory.get_disjoint; [exact GET|exact cap_flex_back0|..]. i. des.
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
    i. set (BACK:=CAP.(cap_flex_back) loc).
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
      inv H. set (@cell_elements_least
                             (mem0 loc)
                             (fun to' => Time.le to to')). des; cycle 1.
      { destruct (Time.le_lt_dec to (Memory.max_ts loc mem0)).
        - exfalso. exploit Memory.max_ts_spec.
          + eapply CLOSED.
          + i. des. exploit EMPTY; eauto.
        - econs.
          + eapply cap_flex_back; eauto.
          + econs; eauto. }
      set (@cell_elements_greatest
             (mem0 loc)
             (fun to' => Time.lt to' to)). des; cycle 1.
      { exfalso. exploit EMPTY.
        - eapply CLOSED.
        - eauto.
        - ss. }
      destruct (Time.le_lt_dec to from).
      - exploit CAP.(cap_flex_middle).
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
        + eapply CAP.(cap_flex_le). eapply GET.
        + econs; eauto.
    }
    {
      inv H. apply Memory.max_ts_spec in GET. des.
      inv ITV. ss. econs; ss.
      - eapply TimeFacts.le_lt_lt; eauto. apply Time.bot_spec.
      - etrans; eauto. erewrite <- cap_flex_max_ts; eauto.
    }
  Qed.

  Record cap_flex_map (max tm0 tm1: TimeMap.t)
         (times: Loc.t -> list Time.t)
         (f: Loc.t -> Time.t -> Time.t -> Prop): Prop :=
    {
      cap_flex_map_map_lt:
        mapping_map_lt f;
      cap_flex_map_map_bot:
        mapping_map_bot f;
      cap_flex_map_ident:
        forall loc ts (TS: Time.le ts (max loc)),
          f loc ts ts;
      cap_flex_map_max:
        forall loc,
        exists fts,
          (<<MAP: f loc (tm0 loc) fts>>) /\
          (<<TS: Time.le (tm1 loc) fts>>);
      cap_flex_map_complete:
        forall loc ts (IN: List.In ts (times loc)),
          mappable_time f loc ts;
    }.

  Lemma cap_flex_map_exists max tm0 tm1 times
        (TM0: forall loc, Time.lt (max loc) (tm0 loc))
        (TM1: forall loc, Time.lt (max loc) (tm1 loc))
    :
      exists f,
        (<<MAP: cap_flex_map max tm0 tm1 times f>>).
  Proof.
    hexploit (@choice
                Loc.t (Time.t -> Time.t -> Prop)
                (fun loc f =>
                   (<<MAPLT: mapping_map_lt_loc f>>) /\
                   (<<IDENT: forall ts (TS: Time.le ts (max loc)),
                       f ts ts>>) /\
                   (<<MAX: exists fts,
                       (<<MAP: f (tm0 loc) fts>>) /\
                       (<<TS: Time.le (tm1 loc) fts>>)>>)/\
                   (<<COMPLETE: forall ts (IN: List.In ts (times loc)),
                       exists fts, (<<MAP: f ts fts>>)>>))).
    { intros loc.
      hexploit (@shift_map_exists
                  (max loc) (tm1 loc) (Time.incr (tm1 loc))
                  ((tm0 loc)::times loc)); ss.
      { left. auto. }
      { apply Time.incr_spec. }
      intros [f SPEC]. exists f. des. splits; auto.
      { hexploit (COMPLETE (tm0 loc)); eauto. i. des. esplits; eauto.
        eapply BOUND in MAPPED; eauto. left. des. auto. }
      { i. hexploit (COMPLETE ts); eauto. }
    }
    intros [f SPEC]. exists f. econs.
    { eapply mapping_map_lt_locwise.
      i. specialize (SPEC loc). des. auto. }
    { ii. specialize (SPEC loc). des.
      eapply IDENT. eapply Time.bot_spec. }
    { i. specialize (SPEC loc). des. auto. }
    { i. specialize (SPEC loc). des. eauto. }
    { i. specialize (SPEC loc). des.
      exploit COMPLETE; eauto. }
  Qed.

  Lemma concrete_messages_le_cap_flex_memory_map
        mem0 mem1 tm0 tm1 cap0 cap1 times f
        (CONCRETE: concrete_messages_le mem0 mem1)
        (TM0: forall loc, Time.lt (Memory.max_ts loc mem0) (tm0 loc))
        (TM1: forall loc, Time.lt (Memory.max_ts loc mem1) (tm1 loc))
        (CAP0: cap_flex mem0 cap0 tm0)
        (CAP1: cap_flex mem1 cap1 tm1)
        (MEM0: Memory.closed mem0)
        (MEM1: Memory.closed mem1)
        (MAP: cap_flex_map (Memory.max_timemap mem0) tm0 tm1 times f)
    :
      memory_map f cap0 cap1.
  Proof.
    assert (IDENT: map_ident_in_memory f mem0).
    { ii. eapply cap_flex_map_ident; eauto. }
    econs.
    { i. eapply (@cap_flex_inv mem0 cap0 tm0) in GET; eauto. des; eauto.
      destruct msg as [val released|]; auto. right.
      exploit CONCRETE; eauto. i. des. esplits.
      { eapply cap_flex_map_ident; eauto.
        eapply Memory.max_ts_spec in GET. des. auto. }
      { eapply map_ident_in_memory_closed_message; eauto.
        eapply MEM0 in GET. des; auto. }
      { refl. }
      { eapply CAP1.(cap_flex_le) in GET1. eauto. }
    }
    { i. hexploit (MAP.(cap_flex_map_max) loc). i. des.
      left. exists (tm0 loc), Time.bot, fts, Time.bot. splits; auto.
      { eapply Time.bot_spec. }
      { hexploit (@cap_flex_max_ts mem1 cap1 tm1); eauto.
        i. eapply Memory.max_ts_spec in GET. des.
        erewrite H in MAX. etrans; eauto. }
      { eapply MAP.(cap_flex_map_map_bot). }
      { i. eapply cap_flex_covered; eauto. }
    }
  Qed.

  Lemma cap_flex_closed mem cap tm
        (CAP: cap_flex mem cap tm)
        (TM: forall loc, Time.lt (Memory.max_ts loc mem) (tm loc))
        (CLOSED: Memory.closed mem)
    :
      Memory.closed cap.
  Proof.
    dup CLOSED. inv CLOSED. econs.
    { i. eapply cap_flex_inv in MSG; eauto. des; subst.
      { exploit CLOSED1; eauto. i. des. splits; auto.
        eapply concrete_promised_le_closed_message; eauto.
        eapply concrete_messages_le_concrete_promised_le; eauto.
        eapply memory_le_concrete_messages_le; eauto.
        eapply cap_flex_le; eauto. }
      { esplits; eauto. econs. }
      { esplits; eauto. econs. }
    }
    { ii. specialize (INHABITED loc).
      eapply cap_flex_le in INHABITED; eauto.
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
    { eapply cap_flex_le in GETORG; eauto. }
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
      hexploit CAP.(cap_flex_middle).
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

End CAPFLEX.
