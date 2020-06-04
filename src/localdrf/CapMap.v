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

  Inductive cap_flex (mem1 mem2: Memory.t) (newmax: TimeMap.t): Prop :=
  | cap_flex_intro
      (SOUND: Memory.le mem1 mem2)
      (MIDDLE: forall loc from1 to1 from2 to2
                      (ADJ: Memory.adjacent loc from1 to1 from2 to2 mem1)
                      (TO: Time.lt to1 from2),
          Memory.get loc from2 mem2 = Some (to1, Message.reserve))
      (BACK: forall loc, Memory.get loc (newmax loc) mem2 =
                         Some (Memory.max_ts loc mem1, Message.reserve))
      (COMPLETE: forall loc from to msg
                        (GET1: Memory.get loc to mem1 = None)
                        (GET2: Memory.get loc to mem2 = Some (from, msg)),
          (exists f m, Memory.get loc from mem1 = Some (f, m)))
  .
  Hint Constructors cap_flex.

  Lemma cap_flex_inv
        mem1 mem2 newmax
        loc from to msg
        (CLOSED: Memory.closed mem1)
        (CAP: cap_flex mem1 mem2 newmax)
        (GET: Memory.get loc to mem2 = Some (from, msg))
        (NEWMAX: forall loc, Time.lt (Memory.max_ts loc mem1) (newmax loc))
    :
    Memory.get loc to mem1 = Some (from, msg) \/
    (Memory.get loc to mem1 = None /\
     exists from1 to2,
        Memory.adjacent loc from1 from to to2 mem1 /\
        Time.lt from to /\
        msg = Message.reserve) \/
    (Memory.get loc to mem1 = None /\
     from = Memory.max_ts loc mem1 /\
     to = newmax loc /\
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
      destruct (Time.le_lt_dec to (newmax loc)).
      + apply (x1 to); econs; ss. refl.
      + apply (x1 (newmax loc)); econs; s;
          eauto using NEWMAX; try refl.
        econs. ss.
  Qed.

  Lemma cap_flex_exists
        mem1 newmax
        (CLOSED1: Memory.closed mem1)
        (NEWMAX: forall loc, Time.lt (Memory.max_ts loc mem1) (newmax loc))
    :
      exists mem2, (<<CAP: cap_flex mem1 mem2 newmax>>).
  Proof.
    hexploit Memory.cap_exists; eauto. i. des.
    hexploit (@choice
                Loc.t Cell.t
                (fun loc cell =>
                   forall ts,
                     Cell.get ts cell =
                     if (Time.eq_dec ts (newmax loc))
                     then Some (Memory.max_ts loc mem1, Message.reserve)
                     else if (Time.eq_dec ts (Time.incr (Memory.max_ts loc mem1)))
                          then None
                          else Memory.get loc ts mem2)).
    { intros loc.
      hexploit (@Cell.remove_exists (mem2 loc)).
      { inv CAP. eapply BACK. } i. des.
      hexploit (@Cell.add_exists cell2 (Memory.max_ts loc mem1) (newmax loc) Message.reserve).
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
        { eapply NEWMAX. }
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

End CAPFLEX.


Section MIDDLE.

  Variable L: Loc.t -> bool.
  Variable times: Loc.t -> list Time.t.


  Lemma sim_memory_max_ts_extra F extra mem_src mem_tgt
        (MEM: sim_memory L times F extra mem_src mem_tgt)
        (MEMSRC: Memory.closed mem_src)
        (MEMTGT: Memory.closed mem_tgt)
        loc
    :
      Memory.max_ts loc mem_src = Memory.max_ts loc mem_tgt \/
      extra loc (Memory.max_ts loc mem_src) (Memory.max_ts loc mem_tgt).
  Proof.
    hexploit (@Memory.max_ts_spec loc).
    { inv MEMTGT. eapply INHABITED. } i. des.
    destruct (Memory.get loc (Memory.max_ts loc mem_tgt) mem_src) as [[from_src msg_src]|] eqn:GETSRC; cycle 1.
    { exfalso. eapply sim_memory_src_none in GETSRC; eauto. des; clarify. }

    i. hexploit (@Memory.max_ts_spec loc).
    { inv MEMTGT. eapply INHABITED. } i. des.
    destruct (Memory.get loc (Memory.max_ts loc mem_tgt) mem_src) eqn:GETSRC0.
    { destruct p. dup GETSRC0. dup GET. eapply Memory.max_ts_spec in GETSRC0. des.
      eapply Memory.max_ts_spec in GET0. des.
      dup GET1. eapply sim_memory_get_larger in GET2; eauto. des.
      { clarify. left. apply TimeFacts.antisym.
        { apply Memory.max_ts_spec in GETTGT. des. auto. }
        { apply Memory.max_ts_spec in GETSRC1. des. auto. }
      }
      { right.
  Admitted.

  Lemma sim_memory_max_ts_le F extra mem_src mem_tgt
        (MEM: sim_memory L times F extra mem_src mem_tgt)
        (MEMSRC: Memory.closed mem_src)
        (MEMTGT: Memory.closed mem_tgt)
        loc
    :
      Time.le (Memory.max_ts loc mem_tgt) (Memory.max_ts loc mem_src).
  Proof.
    hexploit sim_memory_max_ts_extra; eauto. i. des.
    { rewrite H. refl. }
    { eapply MEM.(sim_memory_wf) in H. des. left. auto. }
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
        (CAP: cap mem1 mem2)
        (GET: Memory.get loc ts2 mem1 = Some (ts1, msg1))
    :
      exists ts0 msg0,
        (<<GET: Memory.get loc ts1 mem2 = Some (ts0, msg0)>>).
  Proof.
    destruct (Memory.get loc ts1 mem1) as [[ts0 msg0]|] eqn:GETORG.
    { eapply Memory.cap_le in GETORG; eauto. refl. }
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

  Lemma sim_memory_strong_cap F extra mem_src mem_tgt cap_src cap_tgt
        (MEM: sim_memory_strong F extra mem_src mem_tgt)
        (MEMSRC: Memory.closed mem_src)
        (MEMTGT: Memory.closed mem_tgt)
        (MEMWF: memory_times_wf times mem_tgt)
        (CAPSRC: Memory.cap mem_src cap_src)
        (CAPTGT: cap_flex mem_tgt cap_tgt (Memory.max_timemap cap_src))
    :
      sim_memory L times F extra cap_src cap_tgt.
  Proof.
    assert (NEXMAX: forall loc, Time.lt (Memory.max_ts loc mem_tgt) (Memory.max_timemap cap_src loc)).
    { i. unfold Memory.max_timemap. erewrite (@Memory.cap_max_ts mem_src cap_src); eauto.
      eapply TimeFacts.le_lt_lt.
      { eapply sim_memory_max_ts_le; try apply MEMSRC; eauto.
        eapply sim_memory_strong_sim_memory; eauto. }
      { eapply Time.incr_spec. }
    }
    dup CAPTGT. inv CAPTGT0. dup CAPSRC. inv CAPSRC0. econs.
    { i. set (MEM0:=MEM.(sim_memory_strong_contents) loc ts).
      inv MEM0; symmetry in H; symmetry in H0; rename H into GETMEMTGT; rename H0 into GETMEMSRC.
      { destruct (Memory.get loc ts cap_tgt) as [[from_tgt msg_tgt]|] eqn:GETTGT; eauto.
        { eapply cap_flex_inv in GETTGT; try apply CAPTGT; eauto. des; clarify.
          { hexploit sim_memory_strong_adjancent; eauto. i. des.
            erewrite MIDDLE0; eauto. }
          { revert NEXTRA NPROM. unfold Memory.max_timemap.
            erewrite Memory.cap_max_ts; try apply CAPSRC; eauto.
            erewrite BACK0. i. econs 2; auto.
            { eapply sim_memory_max_ts_le; eauto. eapply sim_memory_strong_sim_memory; eauto. }
            { i. hexploit sim_memory_max_ts_extra.
              { eapply sim_memory_strong_sim_memory; eauto. }
              { eauto. }
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
          eapply Memory.cap_inv in GETSRC; try apply CAPSRC; eauto. des; clarify.
          { inv GETSRC0. eapply

            eapply cap_left_end in GET2; eauto. des.

            cap_left_end

            Memory.adjacent


            admit. }
          { erewrite <- (@Memory.cap_max_ts mem_src cap_src) in GETTGT; eauto.
            unfold Memory.max_timemap in BACK. erewrite BACK in *. clarify. }
      }
      { eapply Memory.cap_le in GETMEMSRC; [|try apply CAPSRC|refl].
        eapply SOUND in GETMEMTGT.
        rewrite GETMEMSRC. rewrite GETMEMTGT. eauto. }
      { eapply Memory.cap_le in GETMEMSRC; [|try apply CAPSRC|refl].
        eapply SOUND in GETMEMTGT.
        rewrite GETMEMSRC. rewrite GETMEMTGT. eauto. }
      { dup GETMEMSRC. eapply Memory.cap_le in GETMEMSRC; [|try apply CAPSRC|refl].
        rewrite GETMEMSRC.
        destruct (Memory.get loc ts cap_tgt) as [[from_tgt msg_tgt]|] eqn:GETTGT; eauto.
        eapply cap_flex_inv in GETTGT; eauto. des; clarify.
        { inv GETTGT0. eapply MEM.(sim_memory_strong_wf) in EXTRA. des.
          exploit LB.
          { eapply MEMWF in GET2. des. eapply FROM. }
          { auto. }
          i. timetac.
        }
        { exfalso. unfold Memory.max_timemap in GETMEMSRC0.
          erewrite Memory.cap_max_ts in GETMEMSRC0; try apply CAPSRC; eauto.
          apply Memory.max_ts_spec in GETMEMSRC0. des.
          eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
          { eapply Time.incr_spec. }
          { eapply MAX. }
        }
      }
    }
    { eapply MEM.(sim_memory_strong_wf); eauto. }
  Qed.


  Lemma sim_memory_strong_cap F extra mem_src mem_tgt cap_src cap_tgt
        (MEM: sim_memory_strong F extra mem_src mem_tgt)
        (MEMSRC: Memory.closed mem_src)
        (MEMTGT: Memory.closed mem_tgt)
        (CAPSRC: Memory.cap mem_src cap_src)
        (CAPTGT: cap_flex mem_tgt cap_tgt (Memory.max_timemap cap_src))
    :
      sim_memory L times F extra cap_src cap_tgt.
  Proof.
    assert (NEXMAX: forall loc, Time.lt (Memory.max_ts loc mem_tgt) (Memory.max_timemap cap_src loc)).
    { i. unfold Memory.max_timemap. erewrite (@Memory.cap_max_ts mem_src cap_src); eauto.
      eapply TimeFacts.le_lt_lt.
      { eapply sim_memory_max_ts; eauto. eapply sim_memory_strong_sim_memory; eauto. }
      { eapply Time.incr_spec. }
    }
    dup CAPTGT. inv CAPTGT0. econs.
    { i. set (MEM0:=MEM.(sim_memory_strong_contents) loc ts).
      inv MEM0; symmetry in H; symmetry in H0; rename H into GETMEMTGT; rename H0 into GETMEMSRC.
      {


        admit. }
      { eapply Memory.cap_le in GETMEMSRC; [|try apply CAPSRC|refl].
        eapply SOUND in GETMEMTGT.
        rewrite GETMEMSRC. rewrite GETMEMTGT. eauto. }
      { eapply Memory.cap_le in GETMEMSRC; [|try apply CAPSRC|refl].
        eapply SOUND in GETMEMTGT.
        rewrite GETMEMSRC. rewrite GETMEMTGT. eauto. }
       memor{
        dup GETMEMSRC. eapply Memory.cap_le in GETMEMSRC; [|try apply CAPSRC|refl].
        rewrite GETMEMSRC.
        destruct (Memory.get loc ts cap_tgt) as [[from_tgt msg_tgt]|] eqn:GETTGT; eauto.
        eapply cap_flex_inv in GETTGT; eauto. des; clarify.
        { inv GETTGT0.


          admit. }
        {

          admit. }
      }
    }
    { eapply MEM.(sim_memory_strong_wf); eauto. }
  Qed.

      i. eapp

      Memory.cap_inv



        others self extra_others extra_self
        prom_src prom_tgt mem_src mem_tgt
        (MEM: sim_memory_strong (others \\2// self) (extra_others \\3// extra_self) mem_src mem_tgt)
        (MLETGT: Memory.le prom_tgt mem_tgt)
        (MLESRC: Memory.le prom_src mem_src)
        (FIN: Memory.finite prom_src)
        (BOTNONESRC: Memory.bot_none prom_src)
        (PROM: sim_promise self extra_self prom_src prom_tgt)
        (MEMWF: memory_times_wf times mem_tgt)
    :
      exists prom_src' mem_src',
        (<<FUTURE: reserve_future_memory prom_src mem_src prom_src' mem_src'>>) /\
        (<<MEM: sim_memory (others \\2// self) (extra_others \\3// extra_self) mem_src' mem_tgt>>) /\
        (<<PROM: sim_promise_strong
                   self extra_self (extra_others \\3// extra_self)
                   prom_src' prom_tgt>>).
  Proof.
    exploit sim_promise_weak_list_exists; eauto. i. des.
    clear PROM. ginduction l.
    { i. exists prom_src, mem_src. splits; auto.
      eapply sim_promise_list_nil; eauto. }
    i. destruct a as [loc ts].


  Lemma sim_promise_weak_stengthen others self extra_others extra_self
        prom_src prom_tgt mem_src mem_tgt
        (MEM: sim_memory (others \\2// self) (extra_others \\3// extra_self) mem_src mem_tgt)
        (MLETGT: Memory.le prom_tgt mem_tgt)
        (MLESRC: Memory.le prom_src mem_src)
        (FIN: Memory.finite prom_src)
        (BOTNONESRC: Memory.bot_none prom_src)
        (PROM: sim_promise self extra_self prom_src prom_tgt)
        (MEMWF: memory_times_wf times mem_tgt)
    :
      exists prom_src' mem_src',
        (<<FUTURE: reserve_future_memory prom_src mem_src prom_src' mem_src'>>) /\
        (<<MEM: sim_memory (others \\2// self) (extra_others \\3// extra_self) mem_src' mem_tgt>>) /\
        (<<PROM: sim_promise_strong
                   self extra_self (extra_others \\3// extra_self)
                   prom_src' prom_tgt>>).
  Proof.
    exploit sim_promise_weak_list_exists; eauto. i. des.
    clear PROM. ginduction l.
    { i. exists prom_src, mem_src. splits; auto.
      eapply sim_promise_list_nil; eauto. }
    i. destruct a as [loc ts].


  Lemma sim_memory_content_strong



  Lemma sim_promise_content_strong_sim_promise_content
        loc ts F extra get0 get1 extra_all
        (SIM: sim_promise_content_strong F extra extra_all loc ts  get0 get1)
    :
      sim_promise_content F extra loc ts get0 get1.
  Proof.
    inv SIM; econs; eauto.
  Qed.

  Record sim_promise_strong
         (self: Loc.t -> Time.t -> Prop)
         (extra: Loc.t -> Time.t -> Time.t -> Prop)
         (extra_all: Loc.t -> Time.t -> Time.t -> Prop)
         (prom_src prom_tgt: Memory.t): Prop :=
    {
      sim_promise_strong_contents:
        forall loc ts,
          sim_promise_content_strong (self loc ts) (extra loc ts) (extra_all loc)
                                     loc ts
                                     (Memory.get loc ts prom_src)
                                     (Memory.get loc ts prom_tgt);
      sim_promise_strong_wf:
        forall loc from ts (EXTRA: extra loc ts from),
          (<<FORGET: self loc from>>) /\
          (<<LB: lb_time (times loc) from ts>>) /\
          (<<TS: Time.lt from ts>>);
      sim_promise_strong_extra:
        forall loc ts (SELF: self loc ts),
        exists to,
          (<<GET: Memory.get loc to prom_src = Some (ts, Message.reserve)>>) /\
          (<<TS: Time.lt ts to>>);
    }.

  Lemma sim_promise_strong_sim_promise
        self extra extra_all prom_src prom_tgt
        (SIM: sim_promise_strong self extra extra_all prom_src prom_tgt)
    :
      sim_promise self extra prom_src prom_tgt.
  Proof.
    econs.
    - ii. eapply sim_promise_content_strong_sim_promise_content; eauto.
      eapply SIM; eauto.
    - apply SIM.
    - apply SIM.
  Qed.

  Record sim_promise_list
         (self: Loc.t -> Time.t -> Prop)
         (extra: Loc.t -> Time.t -> Time.t -> Prop)
         (extra_all: Loc.t -> Time.t -> Time.t -> Prop)
         (prom_src prom_tgt: Memory.t)
         (l: list (Loc.t * Time.t)): Prop :=
    {
      sim_promise_list_contents:
        forall loc ts,
          (<<NORMAL: sim_promise_content_strong (self loc ts) (extra loc ts) (extra_all loc) loc ts
                                                (Memory.get loc ts prom_src)
                                                (Memory.get loc ts prom_tgt)>>) \/
          ((<<LIN: List.In (loc, ts) l>>) /\
           (<<WEAK: sim_promise_content (self loc ts) (extra loc ts) loc ts
                                        (Memory.get loc ts prom_src)
                                        (Memory.get loc ts prom_tgt)>>));
      sim_promise_list_wf:
        forall loc from ts (EXTRA: extra loc ts from),
          (<<FORGET: self loc from>>) /\
          (<<LB: lb_time (times loc) from ts>>) /\
          (<<TS: Time.lt from ts>>);
      sim_promise_list_extra:
        forall loc ts (SELF: self loc ts),
        exists to,
          (<<GET: Memory.get loc to prom_src = Some (ts, Message.reserve)>>) /\
          (<<TS: Time.lt ts to>>);
    }.

  Lemma sim_promise_list_nil self extra extra_all prom_src prom_tgt
        (SIM: sim_promise_list self extra extra_all prom_src prom_tgt [])
    :
      sim_promise_strong self extra extra_all prom_src prom_tgt.
  Proof.
    econs.
    - ii. hexploit SIM.(sim_promise_list_contents); eauto. i. des; eauto. ss.
    - apply SIM.
    - apply SIM.
  Qed.

  Lemma sim_promise_weak_list_exists self extra extra_all prom_src prom_tgt
        (SIM: sim_promise self extra prom_src prom_tgt)
        (FIN: Memory.finite prom_src)
    :
      exists l,
        (<<SIM: sim_promise_list self extra extra_all prom_src prom_tgt l>>).
  Proof.
    unfold Memory.finite in *. des.
    hexploit (@list_filter_exists
                (Loc.t * Time.t)
                (fun locts =>
                   let (loc, ts) := locts in
                   ~ sim_promise_content_strong (self loc ts) (extra loc ts) (extra_all loc) loc ts
                     (Memory.get loc ts prom_src)
                     (Memory.get loc ts prom_tgt))
                dom).
    i. des. exists l'. econs; [|apply SIM|apply SIM].
    ii. set (PROM:= SIM.(sim_promise_contents) loc ts).
    destruct (classic (List.In (loc,ts) l')).
    - right. splits; auto.
    - left. red. inv PROM; try by (econs; eauto).
      + apply NNPP. ii. exploit FIN; eauto. i.
        hexploit (proj1 (@COMPLETE (loc, ts))); auto.
        splits; auto. ii. rewrite H1 in *. rewrite H2 in *. auto.
      + apply NNPP. ii. exploit FIN; eauto. i.
        hexploit (proj1 (@COMPLETE (loc, ts))); auto.
        splits; auto. ii. rewrite H1 in *. rewrite H2 in *. auto.
  Qed.

  Lemma sim_promise_weak_stengthen others self extra_others extra_self
        prom_src prom_tgt mem_src mem_tgt
        (MEM: sim_memory (others \\2// self) (extra_others \\3// extra_self) mem_src mem_tgt)
        (MLETGT: Memory.le prom_tgt mem_tgt)
        (MLESRC: Memory.le prom_src mem_src)
        (FIN: Memory.finite prom_src)
        (BOTNONESRC: Memory.bot_none prom_src)
        (PROM: sim_promise self extra_self prom_src prom_tgt)
        (MEMWF: memory_times_wf times mem_tgt)
    :
      exists prom_src' mem_src',
        (<<FUTURE: reserve_future_memory prom_src mem_src prom_src' mem_src'>>) /\
        (<<MEM: sim_memory (others \\2// self) (extra_others \\3// extra_self) mem_src' mem_tgt>>) /\
        (<<PROM: sim_promise_strong
                   self extra_self (extra_others \\3// extra_self)
                   prom_src' prom_tgt>>).
  Proof.
    exploit sim_promise_weak_list_exists; eauto. i. des.
    clear PROM. ginduction l.
    { i. exists prom_src, mem_src. splits; auto.
      eapply sim_promise_list_nil; eauto. }
    i. destruct a as [loc ts].

    cut (sim_promise_content_strong (self loc ts) (extra_self loc ts)
                                    ((extra_others \\3// extra_self) loc)
                                    loc ts
                                    (Memory.get loc ts prom_src)
                                    (Memory.get loc ts prom_tgt) \/
         exists prom_src' mem_src',
           (<<FUTURE: reserve_future_memory prom_src mem_src prom_src' mem_src'>>) /\
           (<<MEM: sim_memory (others \\2// self) (extra_others \\3// extra_self) mem_src' mem_tgt>>) /\
           (<<PROM: sim_promise_list
                      self extra_self (extra_others \\3// extra_self)
                      prom_src' prom_tgt l>>)).
    { intros H. match goal with
                | [H:?A \/ ?B |- _ ] => cut B
                end.
      { clear H. i. des. exploit IHl.
        { eapply MEM0. }
        { eauto. }
        { eapply reserve_future_memory_le; eauto. }
        { eapply reserve_future_memory_finite; eauto. }
        { eapply reserve_future_memory_bot_none; try apply BOTNONESRC; eauto. }
        { eauto. }
        { eauto. }
        i. des. exists prom_src'0, mem_src'0. splits; eauto.
        eapply reserve_future_memory_trans; eauto. }
      { des; eauto. exists prom_src, mem_src. splits; auto.
        econs; [|apply SIM|apply SIM]. ii.
        set (PROM:=SIM.(sim_promise_list_contents) loc0 ts0).
        ss. des; clarify; auto. }
    }

    set (SIM0:= SIM.(sim_promise_list_contents) loc ts). des; auto.
    inv WEAK.
    { left. econs 1; eauto. }
    { left. econs 2; eauto. }
    { clear LIN. symmetry in H. symmetry in H0.
      rename H into PROMTGT. rename H0 into PROMSRC.
      dup PROMSRC. dup PROMTGT. apply MLESRC in PROMSRC0. apply MLETGT in PROMTGT0.
      rename PROMSRC0 into MEMSRC. rename PROMTGT0 into MEMTGT.
      set (MEM0:=MEM.(sim_memory_contents) loc ts).
      rewrite MEMSRC in MEM0. rewrite MEMTGT in MEM0. inv MEM0; ss.
      destruct (classic (self loc from_src)) as [SELF|NSELF].
      { left. exploit sim_memory_from_forget; eauto. ss. right. auto. }

      hexploit (@Memory.remove_exists prom_src); eauto.
      intros [prom_src' REMOVEPROM].
      hexploit (@Memory.remove_exists_le prom_src mem_src); eauto.
      intros [mem_src' REMOVEMEM].
      assert (REMOVE: Memory.promise prom_src mem_src loc from_src ts Message.reserve prom_src' mem_src' Memory.op_kind_cancel).
      { econs; eauto. }
      destruct (classic (exists from_src', (extra_others \\3// extra_self) loc from_src' from_tgt))
        as [[from_src' EXTRA]|].
      { guardH EXTRA.
        hexploit (@Memory.add_exists mem_src' loc from_src' ts Message.reserve).
        { ii. erewrite Memory.remove_o in GET2; eauto. des_ifs. guardH o.
          hexploit sim_memory_disjoint.
          { eauto. }
          { eauto. }
          { apply MEMTGT. }
          { eapply GET2. }
          { instantiate (1:=x). inv LHS. econs; ss.
            transitivity from_src'; auto.
            eapply MEM.(sim_memory_wf) in EXTRA. des; auto. }
          { eauto. }
          i. destruct H as [EQ|[EQ [FORGET [EXTRA0 TS]]]].
          { des; subst. destruct o; ss. }
          { guardH FORGET. guardH EXTRA0.
            hexploit sim_memory_extra_inj.
            { eapply MEM. }
            { eapply EXTRA0. }
            { eapply EXTRA. }
            i. subst. inv LHS. inv RHS. ss. timetac. }
        }
        { eapply MEM.(sim_memory_wf) in EXTRA. destruct EXTRA as [_ EXTRA]. des.
          eapply LB0.
          { eapply MEMWF in MEMTGT. des; auto. }
          { apply memory_get_ts_strong in MEMTGT. des; auto.
            subst. erewrite BOTNONESRC in PROMSRC. clarify. }
        }
        { econs; eauto. }
        intros [mem_src'' ADDMEM].
        hexploit (@Memory.add_exists_le prom_src' mem_src'); eauto.
        { eapply promise_memory_le; eauto. }
        intros [prom_src'' ADDPROM].
        assert (ADD: Memory.promise prom_src' mem_src' loc from_src' ts Message.reserve prom_src'' mem_src'' Memory.op_kind_add).
        { econs; eauto. i. clarify. }
        right. exists prom_src'', mem_src''. splits; eauto.
        { econs; [|apply MEM]. i.
          erewrite (@Memory.add_o mem_src''); eauto.
          erewrite (@Memory.remove_o mem_src'); eauto. des_ifs.
          { ss. des; subst. rewrite MEMTGT. econs; eauto.
            { left. eapply sim_memory_wf; eauto. ss. eauto. }
            { i. apply MEM.(sim_memory_wf). ss. }
            { i. ss. }
          }
          { apply MEM. }
        }
        { econs; [|apply SIM|].
          { i. erewrite (@Memory.add_o prom_src''); eauto.
            erewrite (@Memory.remove_o prom_src'); eauto. des_ifs.
            { ss. des; subst. left. rewrite PROMTGT. econs; eauto. }
            { guardH o. set (PROM:=SIM.(sim_promise_list_contents) loc0 ts0).
              des; auto. right. splits; eauto. ss. des; auto.
              clarify. unguard. des; ss. }
          }
          { i. set (PROM:=SIM.(sim_promise_list_extra) loc0 ts0 SELF).
            des. exists to.
            erewrite Memory.add_o; eauto. erewrite Memory.remove_o; eauto. des_ifs.
            ss. des; subst. clarify. }
        }
      }

      { hexploit (@Memory.add_exists mem_src' loc from_tgt ts Message.reserve).
        { ii. erewrite Memory.remove_o in GET2; eauto. des_ifs. guardH o.
          hexploit sim_memory_disjoint.
          { eauto. }
          { eauto. }
          { eapply MEMTGT. }
          { eapply GET2. }
          { instantiate (1:=x). eauto. }
          { eauto. }
          i. destruct H0 as [EQ|[EQ [FORGET [EXTRA TS]]]].
          { des; subst. destruct o; ss. }
          { guardH FORGET. guardH EXTRA.
            eapply H. esplits; eauto. }
        }
        { apply memory_get_ts_strong in MEMTGT. des; auto. subst.
          erewrite BOTNONESRC in PROMSRC. clarify. }
        { econs. }
        intros [mem_src'' ADDMEM].
        hexploit (@Memory.add_exists_le prom_src' mem_src'); eauto.
        { eapply promise_memory_le; eauto. }
        intros [prom_src'' ADDPROM].
        assert (ADD: Memory.promise prom_src' mem_src' loc from_tgt ts Message.reserve prom_src'' mem_src'' Memory.op_kind_add).
        { econs; eauto. i. clarify. }
        right. exists prom_src'', mem_src''. splits; eauto.
        { econs; [|apply MEM]. i.
          erewrite (@Memory.add_o mem_src''); eauto.
          erewrite (@Memory.remove_o mem_src'); eauto. des_ifs.
          { ss. des; subst. rewrite MEMTGT. econs; eauto.
            { refl. }
            { i. apply eq_lb_time. }
          }
          { apply MEM. }
        }
        { econs; [|apply SIM|].
          { i. erewrite (@Memory.add_o prom_src''); eauto.
            erewrite (@Memory.remove_o prom_src'); eauto. des_ifs.
            { ss. des; subst. left. rewrite PROMTGT. eauto. }
            { guardH o. set (PROM:=SIM.(sim_promise_list_contents) loc0 ts0).
              des; auto. right. splits; eauto. ss. des; auto.
              clarify. unguard. des; ss. }
          }
          { i. set (PROM:=SIM.(sim_promise_list_extra) loc0 ts0 SELF).
            des. exists to.
            erewrite Memory.add_o; eauto. erewrite Memory.remove_o; eauto. des_ifs.
            ss. des; subst. clarify. }
        }
      }
    }

    { clear LIN. symmetry in H. symmetry in H0.
      rename H into PROMTGT. rename H0 into PROMSRC.
      dup PROMSRC. dup PROMTGT. apply MLESRC in PROMSRC0. apply MLETGT in PROMTGT0.
      rename PROMSRC0 into MEMSRC. rename PROMTGT0 into MEMTGT.
      set (MEM0:=MEM.(sim_memory_contents) loc ts).
      rewrite MEMSRC in MEM0. rewrite MEMTGT in MEM0. inv MEM0; ss. guardH PROM0.
      destruct (classic (self loc from_src)) as [SELF|NSELF].
      { left. exploit sim_memory_from_forget; eauto. ss. right. auto. }

      hexploit (@Memory.remove_exists prom_src); eauto.
      intros [prom_src' REMOVEPROM].
      hexploit (@Memory.remove_exists_le prom_src mem_src); eauto.
      intros [mem_src' REMOVEMEM].
      assert (REMOVE: Memory.promise prom_src mem_src loc from_src ts Message.reserve prom_src' mem_src' Memory.op_kind_cancel).
      { econs; eauto. }
      destruct (classic (exists from_src', (extra_others \\3// extra_self) loc from_src' from_tgt))
        as [[from_src' EXTRA]|].
      { guardH EXTRA.
        hexploit (@Memory.add_exists mem_src' loc from_src' ts Message.reserve).
        { ii. erewrite Memory.remove_o in GET2; eauto. des_ifs. guardH o.
          hexploit sim_memory_disjoint.
          { eauto. }
          { eauto. }
          { eapply MEMTGT. }
          { eapply GET2. }
          { instantiate (1:=x). inv LHS. econs; ss.
            transitivity from_src'; auto.
            eapply MEM.(sim_memory_wf) in EXTRA. des; auto. }
          { eauto. }
          i. destruct H as [EQ|[EQ [FORGET [EXTRA0 TS]]]].
          { des; subst. destruct o; ss. }
          { guardH FORGET. guardH EXTRA0.
            hexploit sim_memory_extra_inj.
            { eapply MEM. }
            { eapply EXTRA0. }
            { eapply EXTRA. }
            i. subst. inv LHS. inv RHS. ss. timetac. }
        }
        { eapply MEM.(sim_memory_wf) in EXTRA. destruct EXTRA as [_ EXTRA]. des.
          eapply LB0.
          { eapply MEMWF in MEMTGT. des; auto. }
          { apply memory_get_ts_strong in MEMTGT. des; auto.
            subst. erewrite BOTNONESRC in PROMSRC. clarify. }
        }
        { econs; eauto. }
        intros [mem_src'' ADDMEM].
        hexploit (@Memory.add_exists_le prom_src' mem_src'); eauto.
        { eapply promise_memory_le; eauto. }
        intros [prom_src'' ADDPROM].
        assert (ADD: Memory.promise prom_src' mem_src' loc from_src' ts Message.reserve prom_src'' mem_src'' Memory.op_kind_add).
        { econs; eauto. i. clarify. }
        right. exists prom_src'', mem_src''. splits; eauto.
        { econs; [|apply MEM]. i.
          erewrite (@Memory.add_o mem_src''); eauto.
          erewrite (@Memory.remove_o mem_src'); eauto. des_ifs.
          { ss. des; subst. rewrite MEMTGT.
            econs; eauto.
            { left. eapply sim_memory_wf; eauto. ss. eauto. }
            { i. apply MEM.(sim_memory_wf). ss. }
          }
          { apply MEM. }
        }
        { econs; [|apply SIM|].
          { i. erewrite (@Memory.add_o prom_src''); eauto.
            erewrite (@Memory.remove_o prom_src'); eauto. des_ifs.
            { ss. des; subst. left. rewrite PROMTGT. econs; eauto. }
            { guardH o. set (PROM1:=SIM.(sim_promise_list_contents) loc0 ts0).
              des; auto. right. splits; eauto. ss. des; auto.
              clarify. unguard. des; ss. }
          }
          { i. set (PROM1:=SIM.(sim_promise_list_extra) loc0 ts0 SELF).
            des. exists to.
            erewrite Memory.add_o; eauto. erewrite Memory.remove_o; eauto. des_ifs.
            ss. des; subst. clarify. }
        }
      }

      { hexploit (@Memory.add_exists mem_src' loc from_tgt ts Message.reserve).
        { ii. erewrite Memory.remove_o in GET2; eauto. des_ifs. guardH o.
          hexploit sim_memory_disjoint.
          { eauto. }
          { eauto. }
          { eapply MEMTGT. }
          { eapply GET2. }
          { instantiate (1:=x). eauto. }
          { eauto. }
          i. destruct H0 as [EQ|[EQ [FORGET [EXTRA TS]]]].
          { des; subst. destruct o; ss. }
          { guardH FORGET. guardH EXTRA.
            eapply H. esplits; eauto. }
        }
        { apply memory_get_ts_strong in MEMTGT. des; auto. subst.
          erewrite BOTNONESRC in PROMSRC. clarify. }
        { econs. }
        intros [mem_src'' ADDMEM].
        hexploit (@Memory.add_exists_le prom_src' mem_src'); eauto.
        { eapply promise_memory_le; eauto. }
        intros [prom_src'' ADDPROM].
        assert (ADD: Memory.promise prom_src' mem_src' loc from_tgt ts Message.reserve prom_src'' mem_src'' Memory.op_kind_add).
        { econs; eauto. i. clarify. }
        right. exists prom_src'', mem_src''. splits; eauto.
        { econs; [|apply MEM]. i.
          erewrite (@Memory.add_o mem_src''); eauto.
          erewrite (@Memory.remove_o mem_src'); eauto. des_ifs.
          { ss. des; subst. rewrite MEMTGT.
            econs; eauto.
            { refl. }
            { apply eq_lb_time. }
          }
          { apply MEM. }
        }
        { econs; [|apply SIM|].
          { i. erewrite (@Memory.add_o prom_src''); eauto.
            erewrite (@Memory.remove_o prom_src'); eauto. des_ifs.
            { ss. des; subst. left. rewrite PROMTGT. eauto. }
            { guardH o. set (PROM1:=SIM.(sim_promise_list_contents) loc0 ts0).
              des; auto. right. splits; eauto. ss. des; auto.
              clarify. unguard. des; ss. }
          }
          { i. set (PROM1:=SIM.(sim_promise_list_extra) loc0 ts0 SELF).
            des. exists to.
            erewrite Memory.add_o; eauto. erewrite Memory.remove_o; eauto. des_ifs.
            ss. des; subst. clarify. }
        }
      }
    }
    { left. econs 5; eauto. }
  Qed.


  Definition promises_list
             (prom_src prom_tgt: Memory.t)
             (others: Loc.t -> Time.t -> Prop)
             (self: Loc.t -> Time.t -> Prop)
             (extra_self: Loc.t -> Time.t -> Prop)

             (l: list (Loc

  Inductive

  sim_promise_strong

  Induct

  Inductive mid_memory (mem_src mem_tgt: Memory.t)


  Lemma mid

  Lemma middle_state_exists
        others self lc_src lc_tgt sc mem_src mem_tgt
        (views: Loc.t -> Time.t -> list View.t)
        times
        (MEM: sim_memory L (others \2/ self) mem_src mem_tgt)
        (SCSRC: Memory.closed_timemap sc mem_src)
        (SCTGT: Memory.closed_timemap sc mem_tgt)
        (MEMSRC: Memory.closed mem_src)
        (MEMTGT: Memory.closed mem_tgt)
        (LOCALSRC: Local.wf lc_src mem_src)
        (LOCALTGT: Local.wf lc_tgt mem_tgt)
        (SIM: sim_local L self lc_src lc_tgt)
        (EXCLUSIVE: forall loc' ts' (OTHER: others loc' ts'),
            exists from msg, <<UNCH: unchangable mem_src lc_src.(Local.promises) loc' ts' from msg>>)
        (JOINED: forall loc ts (NLOC: ~ L loc), List.Forall (fun vw => Memory.closed_view vw mem_src) (views loc ts))

        cap_src cap_tgt max_src max_tgt
        (CAPSRC: Memory.cap mem_src cap_src)
        (CAPTGT: Memory.cap mem_src cap_src)
        (MAXSRC: Memory.max_concrete_timemap cap_src max_src)
        (MAXTGT: Memory.max_concrete_timemap cap_tgt max_tgt)
    :
      exists f prom_src' cap_src' max_mid
             lc_mid cap_mid self'
      ,
        (<<FUTURE: reserve_future_memory lc_src.(Local.promises) cap_src prom_src' cap_src'>>) /\

        (<<SCMID: Memory.closed_timemap max_src cap_mid>>) /\
        (<<MEMMID: Memory.closed cap_mid>>) /\
        (<<LOCALMID: Local.wf lc_mid cap_mid>>) /\

        (<<COMPLETE: forall loc to (IN: List.In (loc, to) times), mappable_time f loc to>>) /\

        (<<MEMORYMAP: memory_map f cap_tgt cap_mid>>) /\
        (<<LOCALMAP: local_map f lc_tgt lc_mid>>) /\
        (<<SCMAP: timemap_map f max_tgt max_mid>>) /\
        (<<SCLE: TimeMap.le max_src max_mid>>) /\

        (<<MEM: sim_memory L (others \2/ self') cap_src' cap_mid>>) /\
        (<<SIM: sim_local L self' (Local.mk lc_src.(Local.tview) cap_src) lc_mid>>) /\

        (<<PROMATTACH: promises_not_attached self' (promised prom_src') cap_src'>>) /\
        (<<EXCLUSIVE: forall loc' ts' (OTHER: others loc' ts'),
            exists from msg, (<<UNCH: unchangable cap_src prom_src' loc' ts' from msg>>)>>) /\
        (<<JOINED: forall loc ts (NLOC: ~ L loc), List.Forall (fun vw => Memory.closed_view vw cap_src') (views loc ts)>>).
  Proof.
  Admitted.

  Record deattached_memory
         (f: Loc.t -> Time.t -> Time.t -> Prop)
         (mem mem_d: Memory.t): Prop :=
    {
      deattached_memory_get_normal:
        forall loc to
               (NMAP0: forall fto, ~ f loc to fto)
               (NMAP1: forall f_1to, ~ f loc f_1to to),
          Memory.get loc to mem = Memory.get loc to mem_d;
      deattached_memory_get_new:
        forall loc to fto
               (MAP: f loc to fto),
        exists from,
          (<<GETORIG: Memory.get loc to mem = Some (from, Message.reserve)>>) /\
          (<<GETDNEW: Memory.get loc fto mem_d = Some (from, Message.reserve)>>) /\
          (<<GETDORIG: Memory.get loc to mem_d = None>>) /\
          (<<TS0: Time.lt from fto>>) /\
          (<<TS1: Time.lt fto to>>);
    }.

  Lemma deattached_memory_map_eq
        f mem mem_d
        (DEATTACH: deattached_memory f mem mem_d)
        loc to fto0 fto1
        (MAP0: f loc to fto0)
        (MAP1: f loc to fto1)
    :
      fto0 = fto1.
  Proof.
    hexploit deattached_memory_get_new; try apply MAP0; eauto. i. des.
    hexploit deattached_memory_get_new; try apply MAP1; eauto. i. des. clarify.
    exploit Memory.get_disjoint.
    { eapply GETDNEW. }
    { eapply GETDNEW0. } i. des; subst; auto.
    exfalso. eapply x0.
    { instantiate (1:=Time.meet fto0 fto1). unfold Time.meet. des_ifs.
      - econs; ss. refl.
      - econs; ss. left. auto. }
    { unfold Time.meet. des_ifs. econs; ss. refl. }
  Qed.

  Lemma deattached_memory_map_inj
        f mem mem_d
        (DEATTACH: deattached_memory f mem mem_d)
        loc to0 to1 fto
        (MAP0: f loc to0 fto)
        (MAP1: f loc to1 fto)
    :
      to0 = to1.
  Proof.
    hexploit deattached_memory_get_new; try apply MAP0; eauto. i. des.
    hexploit deattached_memory_get_new; try apply MAP1; eauto. i. des. clarify.
    exploit Memory.get_disjoint.
    { eapply GETORIG. }
    { eapply GETORIG0. } i. des; subst; auto.
    exfalso. eapply x0.
    { instantiate (1:=fto). econs; ss. left. auto. }
    { econs; ss. left. auto. }
  Qed.

  Lemma deattached_memory_get_orig_unmap
        f mem mem_d
        (DEATTACH: deattached_memory f mem mem_d)
        loc to fto
        (MAP: f loc to fto)
    :
      Memory.get loc fto mem = None.
  Proof.
    hexploit deattached_memory_get_new; eauto. i. des.
    destruct (Memory.get loc fto mem) as [[from' msg]|] eqn:GET; auto. exfalso.
    exploit Memory.get_disjoint.
    { eapply GETORIG. }
    { eapply GET. } i. des; subst.
    - eapply Time.lt_strorder; eauto.
    - eapply x0.
      + instantiate (1:=fto). econs; ss. left. auto.
      + econs; ss.
        * eapply memory_get_ts_strong in GET. des; subst; auto.
          exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
          { eapply TS0. }
          { eapply Time.bot_spec. }
        * refl.
  Qed.

  Lemma deattaching_promises
        (self: Loc.t -> Time.t -> Prop) mem prom
        (SELF: forall loc to (SELF: self loc to),
            exists from,
              (<<GET: Memory.get loc to prom = Some (from, Message.reserve)>>))
        (MLE: Memory.le prom mem)
        (FIN: Memory.finite prom)
        (CLOSED: Memory.closed mem)
    :
      exists f mem' prom',
        (<<FUTURE: reserve_future_memory prom mem prom' mem'>>) /\
        (<<DEATTACHMEM: deattached_memory f mem mem'>>) /\
        (<<DEATTACHPROM: deattached_memory f prom prom'>>) /\
        (<<COMPLETE: forall loc to (SELF: self loc to),
            exists fto, (<<MAP: f loc to fto>>)>>) /\
        (<<SOUND: forall loc to fto (MAP: f loc to fto), self loc to>>).
  Proof.
    assert (exists (l: list (Loc.t * Time.t)),
               (<<COMPLETE: forall loc to,
                   self loc to <-> List.In (loc, to) l>>)).
    { unfold Memory.finite in *. des.
      hexploit list_filter_exists.
      instantiate (2:=fun locto => self (fst locto) (snd locto)).
      instantiate (1:=dom). i. des. exists l'.
      i. split.
      - i. eapply COMPLETE. splits; auto.
        exploit SELF; eauto. i. des. eapply FIN; eauto.
      - i. eapply COMPLETE in H. des. auto.
    }
    des. ginduction l.
    { i. exists (fun _ _ _ => False), mem, prom. splits.
      - econs 1.
      - econs; i; ss.
      - econs; i; ss.
      - i. eapply COMPLETE in SELF0. ss.
      - i. ss. }
    { i. destruct a as [loc to].
      destruct (classic (List.In (loc, to) l)) as [IN|NIN].
      { eapply IHl; eauto. i. rewrite COMPLETE. ss.
        split; i; auto. des; auto. clarify. }
      hexploit (IHl L (fun loc' to' => (<<SELF: self loc' to'>>)
                                       /\ (<<REMOVE: (loc, to) <> (loc', to')>>))); eauto.
      { i. des. eauto. }
      { i. split; i.
        - des. eapply COMPLETE in SELF0. ss. des; auto. clarify.
        - split.
          + eapply COMPLETE. ss. auto.
          + ii. clarify. }
      i. des.

      assert (SELFTS: self loc to).
      { eapply COMPLETE. ss. auto. }
      assert (NMAP0: forall fto, ~ f loc to fto).
      { ii. eapply SOUND in H. des. clarify. }
      assert (NMAP1: forall f_1to, ~ f loc f_1to to).
      { ii. dup H. eapply SOUND in H. des.
        hexploit (DEATTACHPROM.(deattached_memory_get_new)); eauto. i. des.
        exploit SELF; try apply SELFTS. i. des.
        exploit Memory.get_disjoint.
        { eapply GET. }
        { eapply GETORIG. }
        i. des; subst; clarify. eapply x0.
        { instantiate (1:=to). econs; ss.
          - apply memory_get_ts_strong in GET. des; subst; auto.
            exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
            { eapply TS0. }
            { eapply Time.bot_spec. }
          - refl. }
        { econs; ss. left. auto. }
      }

      hexploit SELF.
      { eauto. } i. des.
      rewrite DEATTACHPROM.(deattached_memory_get_normal) in GET; eauto.
      assert (GETMEM: Memory.get loc to mem' = Some (from, Message.reserve)).
      { eapply reserve_future_memory_le; eauto. }

      assert (FROMTO: Time.lt from to).
      { apply memory_get_ts_strong in GET. des; auto. subst.
        exploit Memory.future_closed.
        { eapply reserve_future_future; eauto. }
        { eauto. }
        intros []. erewrite INHABITED in GETMEM. clarify. }
      set (fto := Time.middle from to).

      hexploit (@Memory.remove_exists prom' loc from to Message.reserve); eauto.
      intros [prom0 REMOVEPROM].
      hexploit (@Memory.remove_exists_le prom' mem' loc from to Message.reserve); eauto.
      { eapply reserve_future_memory_le; eauto. }
      intros [mem0 REMOVEMEM].

      assert (PROMISE0: Memory.promise prom' mem' loc from to Message.reserve prom0 mem0 Memory.op_kind_cancel).
      { econs; eauto. }

      hexploit (@Memory.add_exists mem0 loc from fto Message.reserve).
      { ii. exploit Memory.get_disjoint.
        { instantiate (4:=to2).
          erewrite Memory.remove_o in GET2; eauto. des_ifs. eauto. }
        { eapply GETMEM. }
        i. des; subst.
        { eapply Memory.remove_get0 in REMOVEMEM. des. clarify. }
        { eapply x1; eauto. inv LHS. econs; ss.
          transitivity fto; auto. left. eapply Time.middle_spec; auto. }
      }
      { eapply Time.middle_spec; eauto. }
      { econs. }
      intros [mem1 ADDMEM].
      hexploit (@Memory.add_exists_le prom0 mem0 loc from fto Message.reserve); eauto.
      { eapply promise_memory_le; cycle 1; eauto.
        eapply reserve_future_memory_le; eauto. }
      intros [prom1 ADDPROM].
      assert (PROMISE1: Memory.promise prom0 mem0 loc from fto Message.reserve prom1 mem1 Memory.op_kind_add).
      { econs; eauto. i. clarify. }

      assert (NMAP2: forall fto', ~ f loc fto fto').
      { i. intros MAP.
        exploit deattached_memory_get_new; try apply DEATTACHPROM; eauto. i. des.
        exploit Memory.get_disjoint.
        { eapply GETORIG. }
        { instantiate (3:=to).
          erewrite deattached_memory_get_normal; try apply DEATTACHPROM; eauto. }
        i. des.
        { exfalso. eapply Time.lt_strorder.
          instantiate (1:=to). rewrite <- x0 at 1.
          eapply Time.middle_spec; auto. }
        { eapply x0.
          { instantiate (1:=fto). econs; ss.
            - etrans; eauto.
            - refl. }
          { econs; ss.
            - eapply Time.middle_spec; auto.
            - left. eapply Time.middle_spec; auto. }
        }
      }

      assert (NMAP3: forall to', ~ f loc to' fto).
      { i. intros MAP.
        exploit deattached_memory_get_new; try apply DEATTACHPROM; eauto. i. des.
        exploit Memory.get_disjoint.
        { eapply GETORIG. }
        { instantiate (3:=to).
          erewrite deattached_memory_get_normal; try apply DEATTACHPROM; eauto. }
        i. des; subst.
        { eapply NMAP0; eauto. }
        { eapply x0.
          { instantiate (1:=fto). econs; ss. left. auto. }
          { econs; ss.
            - eapply Time.middle_spec; auto.
            - left. eapply Time.middle_spec; auto. }
        }
      }

      exists (fun l t ft => (<<ORIG: f l t ft>>) \/ (<<NEW: l = loc /\ t = to /\ ft = fto>>)),
      mem1, prom1. splits.
      { eapply reserve_future_memory_trans; eauto. }
      { econs.
        { i. erewrite (@Memory.add_o mem1); eauto.
          erewrite (@Memory.remove_o mem0); eauto. des_ifs.
          - ss. des; clarify. exfalso.
            eapply NMAP5; eauto.
          - ss. des; clarify. exfalso.
            eapply NMAP4; eauto.
          - eapply deattached_memory_get_normal; eauto.
            { ii. eapply NMAP4; eauto. }
            { ii. eapply NMAP5; eauto. }
        }
        { i. des.
          { exploit deattached_memory_get_new; try apply DEATTACHMEM; eauto. i. des. esplits; eauto.
            - erewrite (@Memory.add_o mem1); eauto.
              erewrite (@Memory.remove_o mem0); eauto. des_ifs.
              + ss. des; clarify. exfalso. eapply NMAP3; eauto.
              + ss. des; clarify. exfalso. eapply NMAP1; eauto.
            - erewrite (@Memory.add_o mem1); eauto.
              erewrite (@Memory.remove_o mem0); eauto. des_ifs.
              ss. des; clarify. exfalso. eapply NMAP2; eauto.
          }
          { subst. exists from. splits; auto.
            { erewrite deattached_memory_get_normal; try apply DEATTACHMEM; eauto. }
            { eapply Memory.add_get0; eauto. }
            { erewrite (@Memory.add_o mem1); eauto.
              erewrite (@Memory.remove_o mem0); eauto. des_ifs.
              - ss. des; clarify.
                exfalso. eapply Time.lt_strorder.
                instantiate (1:=to). rewrite a0 at 1. eapply Time.middle_spec; auto.
              - ss. des; clarify. }
            { eapply Time.middle_spec; eauto. }
            { eapply Time.middle_spec; eauto. }
          }
        }
      }
      { econs.
        { i. erewrite (@Memory.add_o prom1); eauto.
          erewrite (@Memory.remove_o prom0); eauto. des_ifs.
          - ss. des; clarify. exfalso.
            eapply NMAP5; eauto.
          - ss. des; clarify. exfalso.
            eapply NMAP4; eauto.
          - eapply deattached_memory_get_normal; eauto.
            { ii. eapply NMAP4; eauto. }
            { ii. eapply NMAP5; eauto. }
        }
        { i. des.
          { exploit deattached_memory_get_new; try apply DEATTACHPROM; eauto. i. des. esplits; eauto.
            - erewrite (@Memory.add_o prom1); eauto.
              erewrite (@Memory.remove_o prom0); eauto. des_ifs.
              + ss. des; clarify. exfalso. eapply NMAP3; eauto.
              + ss. des; clarify. exfalso. eapply NMAP1; eauto.
            - erewrite (@Memory.add_o prom1); eauto.
              erewrite (@Memory.remove_o prom0); eauto. des_ifs.
              ss. des; clarify. exfalso. eapply NMAP2; eauto.
          }
          { subst. exists from. splits; auto.
            { erewrite deattached_memory_get_normal; try apply DEATTACHPROM; eauto. }
            { eapply Memory.add_get0; eauto. }
            { erewrite (@Memory.add_o prom1); eauto.
              erewrite (@Memory.remove_o prom0); eauto. des_ifs.
              - ss. des; clarify.
                exfalso. eapply Time.lt_strorder.
                instantiate (1:=to). rewrite a0 at 1. eapply Time.middle_spec; auto.
              - ss. des; clarify. }
            { eapply Time.middle_spec; eauto. }
            { eapply Time.middle_spec; eauto. }
          }
        }
      }
      { i. destruct (classic ((loc0, to0) = (loc, to))).
        - clarify. eauto.
        - exploit COMPLETE0; eauto. i. des. eauto. }
      { i. des.
        - eapply SOUND in MAP. des. auto.
        - subst. auto. }
    }
  Qed.

  Definition attached_promises (self prom: Loc.t -> Time.t -> Prop) (mem: Memory.t)
             (loc: Loc.t) (ts0: Time.t): Prop :=
    (<<SELF: self loc ts0>>) /\
    (<<ATTACH: exists ts1 msg,
        (<<GET: Memory.get loc ts1 mem = Some (ts0, msg)>>) /\
        (<<OTHERS: ~ prom loc ts1>>)>>).

  Inductive mapped_self_promises (self: Loc.t -> Time.t -> Prop)
            (f: Loc.t -> Time.t -> Time.t -> Prop)
    :
      forall (loc: Loc.t) (ts: Time.t), Prop:=
  | mapped_self_promises_unmap
      loc ts
      (SELF: self loc ts)
      (UNMAP: forall fts, ~ f loc ts fts)
    :
      mapped_self_promises self f loc ts
  | mapped_self_promises_map
      loc ts fts
      (MAP: f loc ts fts)
      (SELF: self loc ts)
    :
      mapped_self_promises self f loc fts
  .

  Inductive mid_map (mem: Memory.t) (prom: Memory.t)
            (f: Loc.t -> Time.t -> Time.t -> Prop)
    :
      Loc.t -> Time.t -> Time.t -> Prop :=
  | mid_map_normal
      loc ts
      (NMAP: forall fts, ~ f loc ts fts)
      (PROMISED: promised mem loc ts)
    :
      mid_map mem prom f loc ts ts
  | mid_map_promise
      loc from to msg
      (NMAP: forall fts, ~ f loc to fts)
      (PROMISED: Memory.get loc to prom = Some (from, msg))
    :
      mid_map mem prom f loc from from
  | mid_map_map
      loc ts fts
      (MAP: f loc ts fts)
    :
      mid_map mem prom f loc ts fts
  .
  Hint Constructors mid_map.

  Lemma mid_map_map_bot f mem mem' prom
        (DEATTACHMEM: deattached_memory f mem mem')
        (CLOSED: Memory.closed mem)
    :
      mapping_map_bot (mid_map mem prom f).
  Proof.
    ii. econs 1.
    - ii. exploit deattached_memory_get_new; eauto. i. des.
      exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
      { eapply TS1. }
      { eapply Time.bot_spec. }
    - inv CLOSED. econs; eauto.
  Qed.

  Lemma mid_map_map_lt f mem mem' prom
        (DEATTACHMEM: deattached_memory f mem mem')
    :
      mapping_map_lt (mid_map mem prom f).
  Proof.
    ii. inv MAP0; inv MAP1.
    - auto.
    - auto.
    - exploit deattached_memory_get_new; eauto. i. des. split.
      + i. inv PROMISED. destruct msg.
        exploit memory_get_from_mon.
        { eapply GET. }
        { eapply GETORIG. }
        { eauto. }
        i. eapply TimeFacts.le_lt_lt; eauto.
      + i. etrans; eauto.
    - auto.
    - auto.
    -

      admit.
    - exploit deattached_memory_get_new; eauto. i. des. split.
      + i. etrans; eauto.
      + i. inv PROMISED. destruct msg.
        destruct (Time.le_lt_dec ft1 t0); auto. destruct l.
        { exfalso. exploit memory_get_from_mon.
          { eapply GET. }
          { eapply GETORIG. }
          { eauto. }
          i. eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt.
          { eapply x0. }
          { transitivity ft0; auto. }
        }
        { inv H0. exfalso. eapply NMAP; eauto. }
    - admit.
    - exploit deattached_memory_get_new; try apply MAP; eauto.
      exploit deattached_memory_get_new; try apply MAP0; eauto. i. des.
      destruct (Time.le_lt_dec t0 t1); cycle 1.
      { split; i.
        - exfalso. eapply Time.lt_strorder. transitivity t0; eauto.
        - exploit memory_get_from_mon.
          { eapply GETORIG0. }
          { eapply GETORIG. }
          { eauto. }
          i. exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
          { eapply TS3. } etrans.
          { eapply x0. } etrans.
          { left. eapply TS0. }
          { left. auto. }
      }
      destruct l.
      { split; i; auto.
        exploit memory_get_from_mon.
        { eapply GETORIG. }
        { eapply GETORIG0. }
        { eauto. }
        i. etrans.
        { eapply TS1. } eapply TimeFacts.le_lt_lt.
        { eapply x0. }
        { eauto. }
      }
      { inv H. clarify. hexploit deattached_memory_map_eq.
        { eauto. }
        { eapply MAP. }
        { eapply MAP0. }
        i. subst. split; i; exfalso; eapply Time.lt_strorder; eauto.
      }
  Admitted.

  Lemma deattached_promises_not_attached (self: Loc.t -> Time.t -> Prop)
        f prom mem prom' mem'
        (MLE: Memory.le prom' mem')
        (DEATTACHMEM: deattached_memory f mem mem')
        (DEATTACHPROM: deattached_memory f prom prom')
        (COMPLETE: forall loc to (SELF: attached_promises self (promised prom) mem loc to),
            exists fto, (<<MAP: f loc to fto>>))
    :
      promises_not_attached (mapped_self_promises self f) (promised prom') mem'.
  Proof.
    ii. inv PROMISED.
    - admit.
    - hexploit deattached_memory_get_new; try apply DEATTACHMEM; eauto. i. des.
  Admitted.

End MIDDLE.
