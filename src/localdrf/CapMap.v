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
Require Import CapFlex.

Require Import LocalDRFDef.
Require Import LocalDRF_PF.

Set Implicit Arguments.



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

    econs.
    { i. set (MEM0:=MEM.(sim_memory_strong_contents) loc ts).
      inv MEM0; symmetry in H; symmetry in H0; rename H into GETMEMTGT; rename H0 into GETMEMSRC.
      { destruct (Memory.get loc ts cap_tgt) as [[from_tgt msg_tgt]|] eqn:GETTGT; eauto.
        { eapply cap_flex_inv in GETTGT; try apply CAPTGT; eauto. des; clarify.
          { hexploit sim_memory_strong_adjancent; eauto. i. des.
            erewrite CAPSRC.(cap_flex_middle); eauto. }
          { erewrite CAPSRC.(cap_flex_back). i. econs 2; auto.
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
          { erewrite CAPTGT.(cap_flex_back) in GETTGT. clarify. }
        }
      }
      { eapply CAPSRC.(cap_flex_le) in GETMEMSRC. eapply CAPTGT.(cap_flex_le) in GETMEMTGT.
        rewrite GETMEMSRC. rewrite GETMEMTGT. eauto. }
      { eapply CAPSRC.(cap_flex_le) in GETMEMSRC. eapply CAPTGT.(cap_flex_le) in GETMEMTGT.
        rewrite GETMEMSRC. rewrite GETMEMTGT. eauto. }
      { dup GETMEMSRC. eapply CAPSRC.(cap_flex_le) in GETMEMSRC. rewrite GETMEMSRC.
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
        (MEMWF: forall to from msg
                       (GET: Cell.get to cell_tgt = Some (from, msg)),
            (<<FROM: List.In from (times loc)>>) /\ (<<TO: List.In to (times loc)>>))
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

      assert (MSG: forall from_src from_tgt msg_src msg_tgt
                          (FROM: Time.le from_tgt from_src)
                          (CELLSRC: Cell.get a cell_src = Some (from_src, msg_src))
                          (CELLTGT: Cell.get a cell_tgt = Some (from_tgt, msg_tgt)),
                 exists cell_src' : Cell.t, sim_cell_list loc F extra cell_src' cell_tgt l
             ).
      { i. hexploit (@Cell.remove_exists cell_src from_src a msg_src); auto.
        intros [cell_src0 REMOVE].
        destruct (classic (exists from_src', extra loc from_src' from_tgt))
          as [[from_src' EXTRA]|].
        { hexploit WF; eauto. i. des.
          set (MEM0:=proj1 (CELL from_src')).
          inv MEM0; try by (exfalso; eapply NEXTRA; eauto).
          eapply UNIQUE in EXTRA0. subst.
          hexploit (@Cell.add_exists cell_src0 from_src' a msg_src); auto.
          { i. erewrite Cell.remove_o in GET2; eauto. des_ifs.
            set (MEM0:=proj1 (CELL to2)). rewrite GET2 in MEM0. inv MEM0.
            { hexploit Cell.get_disjoint.
              { eapply CELLTGT. }
              { symmetry. eapply H4. }
              i. des; subst; ss.
              eapply Interval.le_disjoint.
              { symmetry. symmetry in H1.
                eapply Interval.le_disjoint; try apply H1; eauto.
                econs; ss. refl. }
              { econs; ss; [|refl]. left. auto. }
            }
            { hexploit Cell.get_disjoint.
              { eapply CELLTGT. }
              { symmetry. eapply H4. }
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
            { eapply CELLTGT. }
            { symmetry. eapply H3. }
            i. des; subst; ss.
            { eapply Interval.disjoint_imm. }
            ii. inv LHS. inv RHS. ss.
            destruct (Time.le_lt_dec to2 from_src); cycle 1.
            { exploit Cell.get_disjoint.
              { eapply GET2. }
              { eapply CELLSRC. }
              i. des; subst; ss. eapply x1.
              { instantiate (1:=Time.meet to2 a). econs; ss.
                { unfold Time.meet. des_ifs.
                  { eapply TimeFacts.lt_le_lt with (b:=x); auto. }
                }
                { eapply Time.meet_l. }
              }
              { econs; ss.
                { unfold Time.meet. des_ifs.
                  apply Cell.get_ts in CELLSRC. des; auto.
                  subst. timetac.
                }
                { eapply Time.meet_r. }
              }
            }
            destruct (Time.le_lt_dec from_src' from2); cycle 1.
            { exploit Cell.get_disjoint.
              { eapply GET2. }
              { symmetry. eapply H0. }
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
            { econs; ss; [|refl]. symmetry in H2.
              apply Cell.get_ts in H2. des.
              { subst. assert (from_src' = Time.bot).
                { apply TimeFacts.antisym; auto. apply Time.bot_spec. }
                subst. timetac.
              }
              { eapply TimeFacts.le_lt_lt with (b:=from_src0); auto. }
            }
          }
          { destruct (Time.le_lt_dec a from_src'); auto. exfalso.
            hexploit Cell.get_disjoint.
            { symmetry. eapply H0. }
            { eapply CELLSRC. }
            i. des; subst.
            { rewrite CELLTGT in *. clarify. }
            { eapply H1.
              { instantiate (1:=a). econs; ss.
                eapply Cell.get_ts in CELLTGT. des; auto. subst. timetac. }
              { econs; ss; [|refl].
                eapply Cell.get_ts in CELLSRC. des; auto. subst. timetac. }
            }
          }
          { eapply Cell.get_opt_wf in CELLSRC. auto. }
          intros [cell_src1 ADD]. exists cell_src1. ii.
          erewrite (@Cell.add_o cell_src1); eauto.
          erewrite (@Cell.remove_o cell_src0); eauto. des_ifs.
          { cut (sim_memory_content_strong (F loc a) (extra loc a) (extra loc) loc a
                                           (Some (from_src', msg_src)) (Cell.get a cell_tgt)).
            { i. splits; auto.
              eapply sim_memory_content_strong_sim_memory_content; eauto. }
            rewrite CELLTGT in *. rewrite CELLSRC in *. inv CONTENT.
            { econs 2; eauto; ss. left. auto. }
            { econs 3; eauto. left. auto. }
          }
          { specialize (CELL ts). des; auto. ss. des; clarify. splits; auto. }
        }

        { hexploit (@Cell.add_exists cell_src0 from_tgt a msg_src); auto.
          { i. erewrite Cell.remove_o in GET2; eauto. des_ifs.
            set (MEM0:=proj1 (CELL to2)). rewrite GET2 in MEM0. inv MEM0.
            { hexploit Cell.get_disjoint.
              { eapply CELLTGT. }
              { symmetry. eapply H3. }
              i. des; subst; ss.
              eapply Interval.le_disjoint.
              { symmetry. symmetry in H0.
                eapply Interval.le_disjoint; try apply H0; eauto.
                econs; ss. refl. }
              { econs; ss; [|refl]. refl. }
            }
            { hexploit Cell.get_disjoint.
              { eapply CELLTGT. }
              { symmetry. eapply H3. }
              i. des; subst; ss.
              eapply Interval.le_disjoint.
              { symmetry. symmetry in H0.
                eapply Interval.le_disjoint; try apply H0; eauto.
                econs; ss. refl. }
              { econs; ss; [|refl]. refl. }
            }
            hexploit WF; try apply EXTRA. i. des.
            set (MEM0:=proj1 (CELL from2)). inv MEM0; ss.
            hexploit Cell.get_disjoint.
            { eapply CELLTGT. }
            { symmetry. eapply H2. }
            i. des; subst; ss.
            { eapply Interval.disjoint_imm. }
            ii. inv LHS. inv RHS. ss.
            destruct (Time.le_lt_dec to2 from_src); cycle 1.
            { exploit Cell.get_disjoint.
              { eapply GET2. }
              { eapply CELLSRC. }
              i. des; subst; ss. eapply x1.
              { instantiate (1:=Time.meet to2 a). econs; ss.
                { unfold Time.meet. des_ifs.
                  { eapply TimeFacts.lt_le_lt with (b:=x); auto. }
                }
                { eapply Time.meet_l. }
              }
              { econs; ss.
                { unfold Time.meet. des_ifs.
                  apply Cell.get_ts in CELLSRC. des; auto.
                  subst. timetac.
                }
                { eapply Time.meet_r. }
              }
            }
            destruct (Time.le_lt_dec from_tgt from2); cycle 1.
            { hexploit (LB from_tgt); auto.
              { apply MEMWF in CELLTGT. des. auto. }
              i. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
              { eapply H4. } etrans.
              { left. eapply FROM1. }
              eauto.
            }
            destruct l2; cycle 1.
            { inv H4. eapply H; eauto. }
            eapply H0.
            { instantiate (1:=from2). econs; ss. transitivity x; auto. left. auto. }
            { econs; ss; [|refl]. symmetry in H2.
              apply Cell.get_ts in H2. des; auto. subst.
              eapply TimeFacts.le_lt_lt with (b:=from_tgt); auto. eapply Time.bot_spec.
            }
          }
          { apply Cell.get_ts in CELLTGT. des; auto. subst. auto. }
          { eapply Cell.get_opt_wf in CELLSRC. auto. }
          intros [cell_src1 ADD]. exists cell_src1. ii.
          erewrite (@Cell.add_o cell_src1); eauto.
          erewrite (@Cell.remove_o cell_src0); eauto. des_ifs.

          { cut (sim_memory_content_strong (F loc a) (extra loc a) (extra loc) loc a
                                           (Some (from_tgt, msg_src)) (Cell.get a cell_tgt)).
            { i. splits; auto.
              eapply sim_memory_content_strong_sim_memory_content; eauto. }
            rewrite CELLTGT in *. rewrite CELLSRC in *. inv CONTENT.
            { econs 2; eauto; ss.
              { refl. }
              { i. apply eq_lb_time. }
            }
            { econs 3; eauto; ss.
              { refl. }
            }
          }
          { specialize (CELL ts). des; auto. ss. des; clarify. splits; auto. }
        }
      }

      inv CONTENT; eauto.
      { exists cell_src. ii. splits.
        { apply CELL. }
        { destruct (Time.eq_dec a ts).
          { subst. rewrite <- H. rewrite <- H0. left. eauto. }
          { specialize (CELL ts). des; auto. ss. des; auto; ss. }
        }
      }
      { exists cell_src. ii. splits.
        { apply CELL. }
        { destruct (Time.eq_dec a ts).
          { subst. rewrite <- H. rewrite <- H0. left. eauto. }
          { specialize (CELL ts). des; auto. ss. des; auto; ss. }
        }
      }
    }
    des. eauto.
  Qed.

  Lemma sim_memory_strong_exists F extra mem_src mem_tgt
        (MEM: sim_memory L times F extra mem_src mem_tgt)
        (MEMWF: memory_times_wf times mem_tgt)
    :
      exists mem_src',
        (<<MEM: sim_memory_strong F extra mem_src' mem_tgt>>).
  Proof.
    hexploit (@choice
                Loc.t
                Cell.t
                (fun loc cell =>
                   forall ts,
                     sim_memory_content_strong
                       (F loc ts) (extra loc ts) (extra loc)
                       loc ts (Cell.get ts cell) (Memory.get loc ts mem_tgt))).
    { unfold Memory.get. i. eapply sim_cell_strong_exists.
      { i. eapply MEM. }
      { i. eapply MEMWF; eauto. }
      { i. eapply MEM; eauto. }
    }
    intros [mem_src' SPEC]. exists mem_src'. econs; eauto.
    eapply MEM.
  Qed.


  Lemma sim_promise_memory_strong_le others self extra_others extra_self
        mem_src mem_tgt prom_src prom_tgt mem_src'
        (MEM: sim_memory L times (others \\2// self) (extra_others \\3// extra_self) mem_src mem_tgt)
        (PROM: sim_promise_strong L times self extra_self (extra_others \\3// extra_self) prom_src prom_tgt)
        (MLESRC: Memory.le prom_src mem_src)
        (MLETGT: Memory.le prom_tgt mem_tgt)
        (MEMSTRONG: sim_memory_strong (others \\2// self) (extra_others \\3// extra_self) mem_src' mem_tgt)
    :
      Memory.le prom_src mem_src'.
  Proof.
    ii. exploit MLESRC; eauto. intros GETSRC.
    set (MEM0:=MEM.(sim_memory_contents) loc to).
    set (MEM1:=MEMSTRONG.(sim_memory_strong_contents) loc to).
    set (PROM0:=PROM.(sim_promise_strong_contents) loc to).
    rewrite LHS in PROM0. rewrite GETSRC in *.

    inv PROM0.
    { inv MEM0; ss. rewrite <- H in *. inv MEM1; ss. f_equal. f_equal.
      transitivity from_tgt; auto. symmetry. auto. }
    { symmetry in H. rename H into RHS.
      exploit MLETGT; eauto. intros GETTGT. rewrite GETTGT in *.
      inv MEM1. f_equal. f_equal. des; subst; auto.
      { exploit MEM.(sim_memory_wf); eauto. i. des.
        exfalso. set (MEM2:=MEMSTRONG.(sim_memory_strong_contents) loc from).
        inv MEM2; try by (eapply NEXTRA1; eauto).
        eapply UNIQUE in EXTRA0. subst.
        hexploit memory_get_from_inj.
        { symmetry. eapply H1. }
        { symmetry. eapply H0. }
        i. des; clarify.
        inv MEM0; ss. eapply NEXTRA1; eauto.
      }
      { exploit MEM.(sim_memory_wf); eauto. i. des.
        exfalso. set (MEM2:=MEM.(sim_memory_contents) loc from_src).
        inv MEM2; try by (eapply NEXTRA1; eauto).
        eapply UNIQUE in EXTRA. subst.
        hexploit memory_get_from_inj.
        { symmetry. eapply H1. }
        { eapply GETSRC. }
        i. des; clarify.
        inv MEM0; ss. eapply NEXTRA1; eauto.
      }
      { eapply sim_memory_extra_inj; eauto; ss; eauto.  }
    }
    { symmetry in H. rename H into RHS.
      exploit MLETGT; eauto. intros GETTGT. rewrite GETTGT in *.
      inv MEM0; ss. inv MEM1; ss. f_equal. f_equal. des; subst; auto.
      { exploit MEM.(sim_memory_wf); eauto. i. des.
        exfalso. set (MEM2:=MEMSTRONG.(sim_memory_strong_contents) loc from).
        inv MEM2; try by (eapply NEXTRA2; eauto).
        eapply UNIQUE in EXTRA0. subst.
        hexploit memory_get_from_inj.
        { symmetry. eapply H1. }
        { symmetry. eapply H0. }
        i. des; clarify. apply TO. apply TimeFacts.antisym.
        { eapply memory_get_ts_le; eauto. }
        { apply Time.bot_spec. }
      }
      { exploit MEM.(sim_memory_wf); eauto. i. des.
        exfalso. set (MEM2:=MEM.(sim_memory_contents) loc from_src).
        inv MEM2; try by (eapply NEXTRA2; eauto).
        eapply UNIQUE in EXTRA. subst.
        hexploit memory_get_from_inj.
        { symmetry. eapply H1. }
        { eapply GETSRC. }
        i. des; clarify. apply TO. apply TimeFacts.antisym.
        { eapply memory_get_ts_le; eauto. }
        { apply Time.bot_spec. }
      }
      { eapply sim_memory_extra_inj; eauto; ss; eauto.  }
    }
    { inv MEM0; ss; try by (exfalso; eapply NEXTRA; right; eauto).
      inv MEM1; ss; try by (exfalso; eapply NEXTRA; right; eauto).
      exploit (MEM.(sim_memory_wf) loc from to).
      { right. auto. } i. des.
      eapply UNIQUE in EXTRA0. eapply UNIQUE in EXTRA1. subst. auto.
    }
  Qed.

  Lemma sim_memory_same_concrete_messages_le
        F extra mem_src mem_tgt mem_src'
        (MEM0: sim_memory L times F extra mem_src mem_tgt)
        (MEM1: sim_memory L times F extra mem_src' mem_tgt)
    :
      concrete_messages_le mem_src mem_src'.
  Proof.
    ii.
    set (CNT0:=MEM0.(sim_memory_contents) loc to).
    set (CNT1:=MEM1.(sim_memory_contents) loc to).
    rewrite GET0 in CNT0. inv CNT0.
    rewrite <- H in *. inv CNT1; clarify. eauto.
  Qed.

  Lemma sim_memory_concrete_messages_le
        F extra mem_src mem_tgt
        (MEM: sim_memory L times F extra mem_src mem_tgt)
    :
      concrete_messages_le mem_src mem_tgt.
  Proof.
    ii. set (CNT:=MEM.(sim_memory_contents) loc to).
    rewrite GET0 in *. inv CNT. eauto.
  Qed.

  Lemma sim_memory_strong_sim_local others self extra_others extra_self
        mem_src mem_tgt lc_src lc_tgt mem_src'
        (MEM: sim_memory L times (others \\2// self) (extra_others \\3// extra_self) mem_src mem_tgt)
        (LOCAL: sim_local L times self extra_self lc_src lc_tgt)
        (LOCALSRC: Local.wf lc_src mem_src)
        (LOCALTGT: Local.wf lc_tgt mem_tgt)
        (PROM: sim_promise_strong L times self extra_self (extra_others \\3// extra_self)
                                  lc_src.(Local.promises) lc_tgt.(Local.promises))
        (MEMSTRONG: sim_memory_strong (others \\2// self) (extra_others \\3// extra_self) mem_src' mem_tgt)
    :
      Local.wf (Local.mk lc_src.(Local.tview) lc_src.(Local.promises)) mem_src'.
  Proof.
    econs; ss.
    { eapply LOCALSRC. }
    { eapply concrete_promised_le_closed_tview.
      { eapply concrete_messages_le_concrete_promised_le.
        eapply sim_memory_same_concrete_messages_le.
        { eapply MEM. }
        { eapply sim_memory_strong_sim_memory; eauto. }
      }
      { eapply LOCALSRC. }
    }
    { eapply sim_promise_memory_strong_le; eauto.
      { eapply LOCALSRC. }
      { eapply LOCALTGT. }
    }
    { eapply LOCALSRC. }
    { eapply LOCALSRC. }
  Qed.

  Lemma sim_memory_same_closed
        F extra mem_src mem_tgt mem_src'
        (MEM0: sim_memory L times F extra mem_src mem_tgt)
        (MEM1: sim_memory L times F extra mem_src' mem_tgt)
        (CLOSED: Memory.closed mem_src)
    :
      Memory.closed mem_src'.
  Proof.
    econs.
    { i. destruct msg as [val released|].
      { exploit sim_memory_same_concrete_messages_le.
        { eapply MEM1. }
        { eapply MEM0. }
        { eauto. }
        i. des. eapply CLOSED in GET1.
        des. esplits; eauto.
        eapply concrete_promised_le_closed_message; eauto.
        eapply concrete_messages_le_concrete_promised_le.
        eapply sim_memory_same_concrete_messages_le.
        { eapply MEM0. }
        { eapply MEM1. }
      }
      { esplits; eauto. econs. }
    }
    { ii. exploit sim_memory_same_concrete_messages_le.
      { eapply MEM0. }
      { eapply MEM1. }
      { eapply CLOSED. }
      i. des. replace from1 with Time.bot in GET1; eauto.
      apply TimeFacts.antisym.
      { eapply Time.bot_spec. }
      { eapply memory_get_ts_le; eauto. }
    }
  Qed.

End MIDDLE.
