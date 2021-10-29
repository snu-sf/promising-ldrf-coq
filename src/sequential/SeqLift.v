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
Require Import MemoryProps.

Require Import gSimAux.
Require Import LowerMemory.
Require Import JoinedView.

Require Import MaxView.
Require Import Delayed.

Set Implicit Arguments.


Definition version := nat.
Definition version_le := le.

Module Mapping.
  Record t: Type :=
    mk
      { map:> version -> Loc.t -> Time.t -> option Time.t;
        ver: version;
      }.

  Record wf (f: t): Prop :=
    { map_finite: forall v loc, exists l, forall ts fts (MAP: f v loc ts = Some fts), List.In (ts, fts) l;
      mapping_map_lt: forall v loc ts0 ts1 fts0 fts1
                             (MAP0: f.(map) v loc ts0 = Some fts0) (MAP0: f.(map) v loc ts1 = Some fts1),
          Time.lt ts0 ts1 <-> Time.lt fts0 fts1;
      mapping_incr: forall v0 v1 loc ts fts0
                           (VER0: v0 <= v1)
                           (VER1: v1 <= f.(ver))
                           (MAP0: f.(map) v0 loc ts = Some fts0),
          exists fts1,
            (<<MAP: f.(map) v1 loc ts = Some fts1>>) /\
            (<<TS: Time.le fts0 fts1>>);
      mapping_empty: forall v (VER: f.(ver) < v) loc ts, f v loc ts = None;
      mapping_bot: forall loc, f.(map) 0 loc Time.bot = Some Time.bot;
    }.

  Lemma mapping_map_le (f: t) (WF: wf f):
    forall v loc ts0 ts1 fts0 fts1
           (MAP0: f.(map) v loc ts0 = Some fts0) (MAP0: f.(map) v loc ts1 = Some fts1),
      Time.le ts0 ts1 <-> Time.le fts0 fts1.
  Proof.
    i. split.
    { i. destruct (Time.le_lt_dec fts0 fts1); auto.
      erewrite <- mapping_map_lt in l; eauto. timetac. }
    { i. destruct (Time.le_lt_dec ts0 ts1); auto.
      erewrite mapping_map_lt in l; eauto. timetac. }
  Qed.

  Lemma mapping_map_eq (f: t) (WF: wf f):
    forall v loc ts0 ts1 fts0 fts1
           (MAP0: f.(map) v loc ts0 = Some fts0) (MAP0: f.(map) v loc ts1 = Some fts1),
      ts0 = ts1 <-> fts0 = fts1.
  Proof.
    i. split.
    { i. subst. apply TimeFacts.antisym.
      { erewrite <- mapping_map_le; eauto. refl. }
      { erewrite <- mapping_map_le; eauto. refl. }
    }
    { i. subst. apply TimeFacts.antisym.
      { erewrite mapping_map_le; eauto. refl. }
      { erewrite mapping_map_le; eauto. refl. }
    }
  Qed.
End Mapping.

Definition versions := Loc.t -> Time.t -> option version.

Definition versions_wf (f: Mapping.t) (vers: versions): Prop :=
  forall loc to ver (VER: vers loc to = Some ver),
    ver <= f.(Mapping.ver).

Definition version_wf (f: Mapping.t) (v: version): Prop :=
  v <= f.(Mapping.ver).

Definition mapping_messages_le (msgs: Messages.t) (f0 f1: Mapping.t): Prop :=
  (<<VER: f0.(Mapping.ver) <= f1.(Mapping.ver)>>) /\
  (<<TIME: forall v (VER: v <= f0.(Mapping.ver)),
      f1.(Mapping.map) v = f0.(Mapping.map) v>>) /\
  (<<MAPPING: forall loc from ffrom to msg
                     (MSG: msgs loc from to msg)
                     (RESERVE: msg <> Message.reserve)
                     (MAP: f0.(Mapping.map) f0.(Mapping.ver) loc from = Some ffrom),
      f1.(Mapping.map) f1.(Mapping.ver) loc from = Some ffrom>>)
.

Definition versions_messages_le (msgs: Messages.t) (vers0 vers1: versions): Prop :=
  forall loc from to msg ts v
         (MSG: msgs loc from to msg)
         (RESERVE: msg <> Message.reserve)
         (VER: vers0 loc ts = Some v)
         (TS: Time.lt ts to),
    vers1 loc ts = Some v.

Program Instance mapping_messages_le_PreOrder: forall msgs, PreOrder (mapping_messages_le msgs).
Next Obligation.
Proof.
  ii. red. splits; ss.
Qed.
Next Obligation.
Proof.
  ii. unfold mapping_messages_le in *. des. splits; eauto.
  { etrans; eauto. }
  { i. transitivity (y.(Mapping.map) v); eauto.
    eapply TIME; eauto. etrans; eauto. }
Qed.

Program Instance versions_messages_le_PreOrder: forall msgs, PreOrder (versions_messages_le msgs).
Next Obligation.
Proof.
  ii. eauto.
Qed.
Next Obligation.
Proof.
  ii. eauto.
Qed.

Lemma mapping_messages_le_mon:
  forall msgs0 msgs1 f0 f1
         (LE: mapping_messages_le msgs1 f0 f1)
         (MSGS: msgs0 <4= msgs1),
    mapping_messages_le msgs0 f0 f1.
Proof.
  unfold mapping_messages_le in *. i. des. splits; eauto.
Qed.

Lemma versions_messages_le_mon:
  forall msgs0 msgs1 f0 f1
         (LE: versions_messages_le msgs1 f0 f1)
         (MSGS: msgs0 <4= msgs1),
    versions_messages_le msgs0 f0 f1.
Proof.
  ii. eauto.
Qed.

Lemma mapping_latest_wf f
  :
    version_wf f f.(Mapping.ver).
Proof.
  red. refl.
Qed.

Lemma version_wf_mon v0 v1 f0 f1 msgs
      (MAPPING: mapping_messages_le msgs f0 f1)
      (VER: v0 <= v1)
      (WF: version_wf f0 v1)
  :
    version_wf f1 v0.
Proof.
  unfold version_wf in *. etrans; eauto. etrans; eauto. eapply MAPPING.
Qed.

Definition sim_timestamp_exact (l: Loc.t) (f: Mapping.t) (v: version) (ts_src ts_tgt: Time.t) :=
  f.(Mapping.map) v l ts_tgt = Some ts_src.

Definition sim_timestamp (l: Loc.t) (f: Mapping.t) (v: version) (ts_src ts_tgt: Time.t) :=
  exists ts_src' ts_tgt',
    (<<TSSRC: Time.le ts_src ts_src'>>) /\
    (<<TSTGT: Time.le ts_tgt' ts_tgt>>) /\
    (<<SIM: sim_timestamp_exact l f v ts_src' ts_tgt'>>).

Record sim_timestamp_max (l: Loc.t) (f: Mapping.t) (v: version) (ts_src ts_tgt: Time.t): Prop :=
  sim_timestamp_max_intro {
      sim_timestamp_max_sim: sim_timestamp l f v ts_src ts_tgt;
      sim_timestamp_max_max: forall ts (SIM: sim_timestamp l f v ts ts_tgt),
          Time.le ts ts_src;
    }.

Lemma sim_timestamp_exact_sim l f v ts_src ts_tgt
      (EXACT: sim_timestamp_exact l f v ts_src ts_tgt)
  :
    sim_timestamp l f v ts_src ts_tgt.
Proof.
  exists ts_src, ts_tgt. splits; auto; try refl.
Qed.

Lemma sim_timestamp_exact_max l f v ts_src ts_tgt
      (EXACT: sim_timestamp_exact l f v ts_src ts_tgt)
      (WF: Mapping.wf f)
  :
    sim_timestamp_max l f v ts_src ts_tgt.
Proof.
  econs.
  { eapply sim_timestamp_exact_sim. eauto. }
  { i. unfold sim_timestamp, sim_timestamp_exact in *. des.
    etrans; eauto. erewrite <- Mapping.mapping_map_le; eauto. }
Qed.

Lemma sim_timestamp_mon_src l f v ts_src0 ts_src1 ts_tgt
      (SIM: sim_timestamp l f v ts_src1 ts_tgt)
      (TS: Time.le ts_src0 ts_src1)
  :
    sim_timestamp l f v ts_src0 ts_tgt.
Proof.
  unfold sim_timestamp in *. des.
  esplits; [..|eauto]; auto. etrans; eauto.
Qed.

Lemma sim_timestamp_mon_tgt l f v ts_src ts_tgt0 ts_tgt1
      (SIM: sim_timestamp l f v ts_src ts_tgt0)
      (TS: Time.le ts_tgt0 ts_tgt1)
  :
    sim_timestamp l f v ts_src ts_tgt1.
Proof.
  unfold sim_timestamp in *. des.
  esplits; [..|eauto]; auto. etrans; eauto.
Qed.

Lemma sim_timestamp_exact_mon_ver l f v0 v1 ts_src0 ts_tgt
      (SIM: sim_timestamp_exact l f v0 ts_src0 ts_tgt)
      (VER: v0 <= v1)
      (WF: Mapping.wf f)
      (VERWF: version_wf f v1)
  :
    exists ts_src1, (<<TS: Time.le ts_src0 ts_src1>>) /\ (<<SIM: sim_timestamp_exact l f v1 ts_src1 ts_tgt>>).
Proof.
  unfold sim_timestamp_exact in *.
  eapply Mapping.mapping_incr in SIM; eauto. des. esplits; eauto.
Qed.

Lemma sim_timestamp_mon_ver l f v0 v1 ts_src ts_tgt
      (SIM: sim_timestamp l f v0 ts_src ts_tgt)
      (VER: v0 <= v1)
      (WF: Mapping.wf f)
      (VERWF: version_wf f v1)
  :
    sim_timestamp l f v1 ts_src ts_tgt.
Proof.
  unfold sim_timestamp in *. des.
  eapply sim_timestamp_exact_mon_ver in SIM; eauto. des.
  esplits; [..|eauto]; eauto.
Qed.

Lemma sim_timestamp_exact_mon_mapping l msgs f0 f1 v ts_src ts_tgt
      (WF: Mapping.wf f0)
      (VERWF: version_wf f0 v)
      (MAP: mapping_messages_le msgs f0 f1)
  :
    sim_timestamp_exact l f0 v ts_src ts_tgt <-> sim_timestamp_exact l f1 v ts_src ts_tgt.
Proof.
  unfold sim_timestamp_exact, mapping_messages_le in *. des.
  rewrite TIME; eauto.
Qed.

Lemma sim_timestamp_mon_mapping l msgs f0 f1 v ts_src ts_tgt
      (WF: Mapping.wf f0)
      (VERWF: version_wf f0 v)
      (MAP: mapping_messages_le msgs f0 f1)
  :
    sim_timestamp l f0 v ts_src ts_tgt <-> sim_timestamp l f1 v ts_src ts_tgt.
Proof.
  unfold sim_timestamp in *. split.
  { i. des. esplits; eauto.
    erewrite <- sim_timestamp_exact_mon_mapping; eauto. }
  { i. des. esplits; eauto.
    erewrite sim_timestamp_exact_mon_mapping; eauto. }
Qed.

Lemma sim_timestamp_max_mon_mapping l msgs f0 f1 v ts_src ts_tgt
      (WF: Mapping.wf f0)
      (VERWF: version_wf f0 v)
      (MAP: mapping_messages_le msgs f0 f1)
  :
    sim_timestamp_max l f0 v ts_src ts_tgt <-> sim_timestamp_max l f1 v ts_src ts_tgt.
Proof.
  split.
  { i. econs.
    { erewrite <- sim_timestamp_mon_mapping; eauto. eapply sim_timestamp_max_sim; eauto. }
    { i. erewrite <- sim_timestamp_mon_mapping in SIM; eauto.
      eapply sim_timestamp_max_max; eauto. }
  }
  { i. econs.
    { erewrite sim_timestamp_mon_mapping; eauto. eapply sim_timestamp_max_sim; eauto. }
    { i. erewrite sim_timestamp_mon_mapping in SIM; eauto.
      eapply sim_timestamp_max_max; eauto. }
  }
Qed.

Lemma sim_timestamp_max_exists l f v ts_tgt
      (WF: Mapping.wf f)
      (VER: version_wf f v)
  :
    exists ts_src, <<MAX: sim_timestamp_max l f v ts_src ts_tgt>>.
Proof.
  hexploit Mapping.map_finite; eauto. i. des.
  hexploit (@finite_greatest (fun ts => Time.le ts ts_tgt /\ exists fts, Mapping.map f v l ts = Some fts) (List.map fst l0)).
  i. des.
  { exists fts. econs.
    { eapply sim_timestamp_mon_tgt; eauto.
      eapply sim_timestamp_exact_sim. red. eauto. }
    { i. unfold sim_timestamp in *. des.
      assert (LE: Time.le ts_tgt' to).
      { eapply GREATEST; eauto.
        eapply H in SIM. eapply List.in_map with (f:=fst) in SIM; ss; eauto. }
      transitivity ts_src'; eauto.
      erewrite Mapping.mapping_map_le in LE; eauto.
    }
  }
  { exfalso. hexploit (Mapping.mapping_bot); eauto. i.
    eapply sim_timestamp_exact_mon_ver with (v1:=v) in H0; eauto.
    { des. eapply EMPTY.
      { hexploit H; eauto. i.
        eapply List.in_map with (f:=fst) in H0; ss; eauto. }
      { split.
        { eapply Time.bot_spec. }
        { esplits; eauto. }
      }
    }
    { eapply le_0_n. }
  }
Qed.

Lemma sim_timestamp_le l f v
      ts_src0 ts_src1 ts_tgt0 ts_tgt1
      (SIM0: sim_timestamp l f v ts_src0 ts_tgt0)
      (SIM1: sim_timestamp_exact l f v ts_src1 ts_tgt1)
      (TS: Time.le ts_tgt0 ts_tgt1)
      (WF: Mapping.wf f)
      (VERWF: version_wf f v)
  :
    Time.le ts_src0 ts_src1.
Proof.
  unfold sim_timestamp in *. des.
  transitivity ts_src'; eauto.
  erewrite <- Mapping.mapping_map_le; cycle 1; eauto.
Qed.

Lemma sim_timestamp_lt l f v
      ts_src0 ts_src1 ts_tgt0 ts_tgt1
      (SIM0: sim_timestamp l f v ts_src0 ts_tgt0)
      (SIM1: sim_timestamp_exact l f v ts_src1 ts_tgt1)
      (TS: Time.lt ts_tgt0 ts_tgt1)
      (WF: Mapping.wf f)
      (VERWF: version_wf f v)
  :
    Time.lt ts_src0 ts_src1.
Proof.
  unfold sim_timestamp in *. des.
  eapply TimeFacts.le_lt_lt; eauto.
  erewrite <- Mapping.mapping_map_lt; cycle 1; eauto.
  eapply TimeFacts.le_lt_lt; eauto.
Qed.

Lemma sim_timestamp_bot l f v ts
      (WF: Mapping.wf f)
      (VERWF: version_wf f v)
  :
    sim_timestamp l f v Time.bot ts.
Proof.
  hexploit Mapping.mapping_bot; eauto. i.
  eapply Mapping.mapping_incr with (v1:=v) in H; eauto.
  { des. exists fts1, Time.bot. splits; ss; eauto. eapply Time.bot_spec. }
  { eapply le_0_n. }
Qed.

Lemma sim_timestamp_exact_join l f v
      ts_src0 ts_src1 ts_tgt0 ts_tgt1
      (SIM0: sim_timestamp_exact l f v ts_src0 ts_tgt0)
      (SIM1: sim_timestamp_exact l f v ts_src1 ts_tgt1)
      (WF: Mapping.wf f)
      (VERWF: version_wf f v)
  :
    sim_timestamp_exact l f v (Time.join ts_src0 ts_src1) (Time.join ts_tgt0 ts_tgt1).
Proof.
  unfold Time.join in *. des_ifs.
  { erewrite <- Mapping.mapping_map_le in l0; eauto. timetac. }
  { erewrite Mapping.mapping_map_le in l1; eauto. timetac. }
Qed.

Lemma sim_timestamp_join l f v
      ts_src0 ts_src1 ts_tgt0 ts_tgt1
      (SIM0: sim_timestamp l f v ts_src0 ts_tgt0)
      (SIM1: sim_timestamp l f v ts_src1 ts_tgt1)
      (WF: Mapping.wf f)
      (VERWF: version_wf f v)
  :
    sim_timestamp l f v (Time.join ts_src0 ts_src1) (Time.join ts_tgt0 ts_tgt1).
Proof.
  unfold sim_timestamp in *. des.
  exists (Time.join ts_src'0 ts_src'), (Time.join ts_tgt'0 ts_tgt'). splits.
  { eapply time_join_mon; eauto. }
  { eapply time_join_mon; eauto. }
  { eapply sim_timestamp_exact_join; eauto. }
Qed.


Definition sim_timemap (L: Loc.t -> Prop)
           (f: Mapping.t) (v: version) (tm_src tm_tgt: TimeMap.t) :=
  forall l (LOC: L l), sim_timestamp l f v (tm_src l) (tm_tgt l).

Lemma sim_timemap_mon_src L f v tm_src0 tm_src1 tm_tgt
      (SIM: sim_timemap L f v tm_src1 tm_tgt)
      (TM: TimeMap.le tm_src0 tm_src1)
  :
    sim_timemap L f v tm_src0 tm_tgt.
Proof.
  ii. eapply sim_timestamp_mon_src; eauto.
Qed.

Lemma sim_timemap_mon_tgt L f v tm_src tm_tgt0 tm_tgt1
      (SIM: sim_timemap L f v tm_src tm_tgt0)
      (TM: TimeMap.le tm_tgt0 tm_tgt1)
  :
    sim_timemap L f v tm_src tm_tgt1.
Proof.
  ii. eapply sim_timestamp_mon_tgt; eauto.
Qed.

Lemma sim_timemap_mon_ver L f v0 v1 tm_src tm_tgt
      (SIM: sim_timemap L f v0 tm_src tm_tgt)
      (VER: v0 <= v1)
      (WF: Mapping.wf f)
      (VERWF: version_wf f v1)
  :
    sim_timemap L f v1 tm_src tm_tgt.
Proof.
  ii. eapply sim_timestamp_mon_ver; eauto.
Qed.

Lemma sim_timemap_mon_mapping L msgs f0 f1 v tm_src tm_tgt
      (WF: Mapping.wf f0)
      (VERWF: version_wf f0 v)
      (MAP: mapping_messages_le msgs f0 f1)
  :
    sim_timemap L f0 v tm_src tm_tgt <-> sim_timemap L f1 v tm_src tm_tgt.
Proof.
  split; ii.
  { erewrite <- sim_timestamp_mon_mapping; eauto. }
  { erewrite sim_timestamp_mon_mapping; eauto. }
Qed.

Lemma sim_timemap_mon_locs L0 L1 f v tm_src tm_tgt
      (SIM: sim_timemap L1 f v tm_src tm_tgt)
      (LOCS: L0 <1= L1)
  :
    sim_timemap L0 f v tm_src tm_tgt.
Proof.
  ii. eauto.
Qed.

Lemma sim_timemap_join L f v
      tm_src0 tm_src1 tm_tgt0 tm_tgt1
      (SIM0: sim_timemap L f v tm_src0 tm_tgt0)
      (SIM1: sim_timemap L f v tm_src1 tm_tgt1)
      (WF: Mapping.wf f)
      (VERWF: version_wf f v)
  :
    sim_timemap L f v (TimeMap.join tm_src0 tm_src1) (TimeMap.join tm_tgt0 tm_tgt1).
Proof.
  ii. eapply sim_timestamp_join; eauto.
Qed.

Lemma sim_timemap_bot l f v tm
      (WF: Mapping.wf f)
      (VERWF: version_wf f v)
  :
    sim_timemap l f v TimeMap.bot tm.
Proof.
  ii. eapply sim_timestamp_bot; eauto.
Qed.

Lemma sim_timemap_singleton l (L: Loc.t -> Prop) f v
      ts_src ts_tgt
      (SIM: L l -> sim_timestamp l f v ts_src ts_tgt)
      (WF: Mapping.wf f)
      (VERWF: version_wf f v)
  :
    sim_timemap L f v (TimeMap.singleton l ts_src) (TimeMap.singleton l ts_tgt).
Proof.
  ii. unfold TimeMap.singleton.
  setoid_rewrite LocFun.add_spec. des_ifs; eauto.
  rewrite LocFun.init_spec.
  eapply sim_timestamp_bot; eauto.
Qed.

Definition sim_timemap_max (L: Loc.t -> Prop) (f: Mapping.t) (v: version) (tm_src tm_tgt: TimeMap.t): Prop :=
  forall l (LOC: L l), sim_timestamp_max l f v (tm_src l) (tm_tgt l).

Lemma sim_timemap_max_sim (L: Loc.t -> Prop) f v tm_src tm_tgt
      (SIM: sim_timemap_max L f v tm_src tm_tgt)
  :
    sim_timemap L f v tm_src tm_tgt.
Proof.
  ii. eapply sim_timestamp_max_sim; eauto.
Qed.

Lemma sim_timemap_max_max f v tm_src tm_tgt
      tm
      (MAX: sim_timemap_max (fun _ => True) f v tm_src tm_tgt)
      (SIM: sim_timemap (fun _ => True) f v tm tm_tgt)
  :
    TimeMap.le tm tm_src.
Proof.
  ii. eapply sim_timestamp_max_max; eauto.
Qed.

Lemma sim_timemap_max_mon_mapping L msgs f0 f1 v tm_src tm_tgt
      (WF: Mapping.wf f0)
      (VERWF: version_wf f0 v)
      (MAP: mapping_messages_le msgs f0 f1)
  :
    sim_timemap_max L f0 v tm_src tm_tgt <-> sim_timemap_max L f1 v tm_src tm_tgt.
Proof.
  split; ii.
  { erewrite <- sim_timestamp_max_mon_mapping; eauto. }
  { erewrite sim_timestamp_max_mon_mapping; eauto. }
Qed.

Lemma sim_timemap_max_exists L f v tm_tgt
      (WF: Mapping.wf f)
      (VER: version_wf f v)
  :
    exists tm_src, <<MAX: sim_timemap_max L f v tm_src tm_tgt>>.
Proof.
  hexploit (choice (fun loc ts => sim_timestamp_max loc f v ts (tm_tgt loc))).
  { i. eapply sim_timestamp_max_exists; eauto. }
  i. des. exists f0. ii. eauto.
Qed.


Record sim_view (L: Loc.t -> Prop)
       (f: Mapping.t) (v: version) (vw_src vw_tgt: View.t) :=
  sim_timemap_intro {
      sim_view_pln: sim_timemap L f v vw_src.(View.pln) vw_tgt.(View.pln);
      sim_view_rlx: sim_timemap L f v vw_src.(View.rlx) vw_tgt.(View.rlx);
    }.

Lemma sim_view_mon_src L f v vw_src0 vw_src1 vw_tgt
      (SIM: sim_view L f v vw_src1 vw_tgt)
      (VW: View.le vw_src0 vw_src1)
  :
    sim_view L f v vw_src0 vw_tgt.
Proof.
  econs.
  { eapply sim_timemap_mon_src; eauto.
    { eapply SIM. }
    { eapply VW. }
  }
  { eapply sim_timemap_mon_src; eauto.
    { eapply SIM. }
    { eapply VW. }
  }
Qed.

Lemma sim_view_mon_tgt L f v vw_src vw_tgt0 vw_tgt1
      (SIM: sim_view L f v vw_src vw_tgt0)
      (VW: View.le vw_tgt0 vw_tgt1)
  :
    sim_view L f v vw_src vw_tgt1.
Proof.
  econs.
  { eapply sim_timemap_mon_tgt; eauto.
    { eapply SIM. }
    { eapply VW. }
  }
  { eapply sim_timemap_mon_tgt; eauto.
    { eapply SIM. }
    { eapply VW. }
  }
Qed.

Lemma sim_view_mon_ver L f v0 v1 vw_src vw_tgt
      (SIM: sim_view L f v0 vw_src vw_tgt)
      (VER: v0 <= v1)
      (WF: Mapping.wf f)
      (VERWF: version_wf f v1)
  :
    sim_view L f v1 vw_src vw_tgt.
Proof.
  econs.
  { eapply sim_timemap_mon_ver; eauto.
    eapply SIM.
  }
  { eapply sim_timemap_mon_ver; eauto.
    eapply SIM.
  }
Qed.

Lemma sim_view_mon_mapping L msgs f0 f1 v vw_src vw_tgt
      (WF: Mapping.wf f0)
      (VERWF: version_wf f0 v)
      (MAP: mapping_messages_le msgs f0 f1)
  :
    sim_view L f0 v vw_src vw_tgt <-> sim_view L f1 v vw_src vw_tgt.
Proof.
  split; ii; econs.
  { erewrite <- sim_timemap_mon_mapping; eauto. eapply H. }
  { erewrite <- sim_timemap_mon_mapping; eauto. eapply H. }
  { erewrite sim_timemap_mon_mapping; eauto. eapply H. }
  { erewrite sim_timemap_mon_mapping; eauto. eapply H. }
Qed.

Lemma sim_view_mon_locs L0 L1 f v vw_src vw_tgt
      (SIM: sim_view L1 f v vw_src vw_tgt)
      (LOCS: L0 <1= L1)
  :
    sim_view L0 f v vw_src vw_tgt.
Proof.
  econs.
  { eapply sim_timemap_mon_locs; eauto. eapply SIM. }
  { eapply sim_timemap_mon_locs; eauto. eapply SIM. }
Qed.

Lemma sim_view_join l f v
      vw_src0 vw_src1 vw_tgt0 vw_tgt1
      (SIM0: sim_view l f v vw_src0 vw_tgt0)
      (SIM1: sim_view l f v vw_src1 vw_tgt1)
      (WF: Mapping.wf f)
      (VERWF: version_wf f v)
  :
    sim_view l f v (View.join vw_src0 vw_src1) (View.join vw_tgt0 vw_tgt1).
Proof.
  econs.
  { eapply sim_timemap_join; eauto.
    { eapply SIM0. }
    { eapply SIM1. }
  }
  { eapply sim_timemap_join; eauto.
    { eapply SIM0. }
    { eapply SIM1. }
  }
Qed.

Lemma sim_view_bot l f v vw
      (WF: Mapping.wf f)
      (VERWF: version_wf f v)
  :
    sim_view l f v View.bot vw.
Proof.
  econs.
  { eapply sim_timemap_bot; eauto. }
  { eapply sim_timemap_bot; eauto. }
Qed.

Lemma sim_view_singleton_ur l (L: Loc.t -> Prop) f v
      ts_src ts_tgt
      (SIM: L l -> sim_timestamp l f v ts_src ts_tgt)
      (WF: Mapping.wf f)
      (VERWF: version_wf f v)
  :
    sim_view L f v (View.singleton_ur l ts_src) (View.singleton_ur l ts_tgt).
Proof.
  econs; ss.
  { eapply sim_timemap_singleton; eauto. }
  { eapply sim_timemap_singleton; eauto. }
Qed.

Lemma sim_view_singleton_rw l (L: Loc.t -> Prop) f v
      ts_src ts_tgt
      (SIM: L l -> sim_timestamp l f v ts_src ts_tgt)
      (WF: Mapping.wf f)
      (VERWF: version_wf f v)
  :
    sim_view L f v (View.singleton_rw l ts_src) (View.singleton_rw l ts_tgt).
Proof.
  econs; ss.
  { eapply sim_timemap_bot; eauto. }
  { eapply sim_timemap_singleton; eauto. }
Qed.

Record sim_view_max (L: Loc.t -> Prop)
       (f: Mapping.t) (v: version) (vw_src vw_tgt: View.t) :=
  sim_view_max_intro {
      sim_view_max_pln: sim_timemap_max L f v vw_src.(View.pln) vw_tgt.(View.pln);
      sim_view_max_rlx: sim_timemap_max L f v vw_src.(View.rlx) vw_tgt.(View.rlx);
    }.

Lemma sim_view_max_sim (L: Loc.t -> Prop) f v vw_src vw_tgt
      (SIM: sim_view_max L f v vw_src vw_tgt)
  :
    sim_view L f v vw_src vw_tgt.
Proof.
  econs.
  { eapply sim_timemap_max_sim; eauto. eapply SIM. }
  { eapply sim_timemap_max_sim; eauto. eapply SIM. }
Qed.

Lemma sim_view_max_max f v vw_src vw_tgt
      vw
      (MAX: sim_view_max (fun _ => True) f v vw_src vw_tgt)
      (SIM: sim_view (fun _ => True) f v vw vw_tgt)
  :
    View.le vw vw_src.
Proof.
  econs.
  { eapply sim_timemap_max_max; eauto.
    { eapply MAX. }
    { eapply SIM. }
  }
  { eapply sim_timemap_max_max; eauto.
    { eapply MAX. }
    { eapply SIM. }
  }
Qed.

Lemma sim_view_max_mon_mapping L msgs f0 f1 v vw_src vw_tgt
      (WF: Mapping.wf f0)
      (VERWF: version_wf f0 v)
      (MAP: mapping_messages_le msgs f0 f1)
  :
    sim_view_max L f0 v vw_src vw_tgt <-> sim_view_max L f1 v vw_src vw_tgt.
Proof.
  split; i.
  { econs.
    { erewrite <- sim_timemap_max_mon_mapping; eauto. eapply H. }
    { erewrite <- sim_timemap_max_mon_mapping; eauto. eapply H. }
  }
  { econs.
    { erewrite sim_timemap_max_mon_mapping; eauto. eapply H. }
    { erewrite sim_timemap_max_mon_mapping; eauto. eapply H. }
  }
Qed.

Lemma sim_view_max_exists L f v vw_tgt
      (WF: Mapping.wf f)
      (VER: version_wf f v)
  :
    exists vw_src, <<MAX: sim_view_max L f v vw_src vw_tgt>>.
Proof.
  hexploit sim_timemap_max_exists; eauto. i. des.
  hexploit sim_timemap_max_exists; eauto. i. des.
  exists (View.mk tm_src tm_src0). econs; eauto.
Qed.



Variant sim_opt_view (L: Loc.t -> Prop)
        (f: Mapping.t) (v: version):
  forall (vw_src vw_tgt: option View.t), Prop :=
| sim_opt_view_some
    vw_src vw_tgt
    (SIM: sim_view L f v vw_src vw_tgt)
  :
    sim_opt_view L f v (Some vw_src) (Some vw_tgt)
| sim_opt_view_none
    vw
  :
    sim_opt_view L f v None vw
.

Lemma sim_opt_view_mon_src L f v vw_src0 vw_src1 vw_tgt
      (SIM: sim_opt_view L f v vw_src1 vw_tgt)
      (VW: View.opt_le vw_src0 vw_src1)
  :
    sim_opt_view L f v vw_src0 vw_tgt.
Proof.
  inv SIM; inv VW; econs.
  eapply sim_view_mon_src; eauto.
Qed.

Lemma sim_opt_view_mon_tgt L f v vw_src vw_tgt0 vw_tgt1
      (SIM: sim_opt_view L f v vw_src vw_tgt0)
      (VW: View.opt_le vw_tgt0 vw_tgt1)
  :
    sim_opt_view L f v vw_src vw_tgt1.
Proof.
  inv SIM; inv VW; econs.
  eapply sim_view_mon_tgt; eauto.
Qed.

Lemma sim_opt_view_mon_ver L f v0 v1 vw_src vw_tgt
      (SIM: sim_opt_view L f v0 vw_src vw_tgt)
      (VER: v0 <= v1)
      (WF: Mapping.wf f)
      (VERWF: version_wf f v1)
  :
    sim_opt_view L f v1 vw_src vw_tgt.
Proof.
  inv SIM; econs.
  eapply sim_view_mon_ver; eauto.
Qed.

Lemma sim_opt_view_mon_mapping L msgs f0 f1 v vw_src vw_tgt
      (WF: Mapping.wf f0)
      (VERWF: version_wf f0 v)
      (MAP: mapping_messages_le msgs f0 f1)
  :
    sim_opt_view L f0 v vw_src vw_tgt <-> sim_opt_view L f1 v vw_src vw_tgt.
Proof.
  split; i.
  { inv H; econs. erewrite <- sim_view_mon_mapping; eauto. }
  { inv H; econs. erewrite sim_view_mon_mapping; eauto. }
Qed.

Lemma sim_opt_view_mon_locs L0 L1 f v vw_src vw_tgt
      (SIM: sim_opt_view L1 f v vw_src vw_tgt)
      (LOCS: L0 <1= L1)
  :
    sim_opt_view L0 f v vw_src vw_tgt.
Proof.
  inv SIM; econs; eauto.
  eapply sim_view_mon_locs; eauto.
Qed.

Lemma sim_opt_view_unwrap l f v
      vw_src vw_tgt
      (SIM: sim_opt_view l f v vw_src vw_tgt)
      (WF: Mapping.wf f)
      (VERWF: version_wf f v)
  :
    sim_view l f v (View.unwrap vw_src) (View.unwrap vw_tgt).
Proof.
  inv SIM; ss. eapply sim_view_bot; eauto.
Qed.

Variant sim_opt_view_max (L: Loc.t -> Prop)
        (f: Mapping.t) (v: version):
  forall (vw_src vw_tgt: option View.t), Prop :=
| sim_opt_view_max_some
    vw_src vw_tgt
    (SIM: sim_view_max L f v vw_src vw_tgt)
  :
    sim_opt_view_max L f v (Some vw_src) (Some vw_tgt)
| sim_opt_view_max_none
  :
    sim_opt_view_max L f v None None
.

Lemma sim_opt_view_max_sim (L: Loc.t -> Prop) f v vw_src vw_tgt
      (SIM: sim_opt_view_max L f v vw_src vw_tgt)
  :
    sim_opt_view L f v vw_src vw_tgt.
Proof.
  inv SIM; econs.
  eapply sim_view_max_sim; eauto.
Qed.

Lemma sim_opt_view_max_max f v vw_src vw_tgt
      vw
      (MAX: sim_opt_view_max (fun _ => True) f v vw_src vw_tgt)
      (SIM: sim_opt_view (fun _ => True) f v vw vw_tgt)
  :
    View.opt_le vw vw_src.
Proof.
  inv MAX; inv SIM.
  { econs. eapply sim_view_max_max; eauto. }
  { econs. }
  { econs. }
Qed.

Lemma sim_opt_view_max_mon_mapping L msgs f0 f1 v vw_src vw_tgt
      (WF: Mapping.wf f0)
      (VERWF: version_wf f0 v)
      (MAP: mapping_messages_le msgs f0 f1)
  :
    sim_opt_view_max L f0 v vw_src vw_tgt <-> sim_opt_view_max L f1 v vw_src vw_tgt.
Proof.
  split; i.
  { inv H; econs.
    erewrite <- sim_view_max_mon_mapping; eauto.
  }
  { inv H; econs.
    erewrite sim_view_max_mon_mapping; eauto.
  }
Qed.

Lemma sim_opt_view_max_exists L f v vw_tgt
      (WF: Mapping.wf f)
      (VER: version_wf f v)
  :
    exists vw_src, <<MAX: sim_opt_view_max L f v vw_src vw_tgt>>.
Proof.
  destruct vw_tgt as [vw_tgt|].
  { hexploit sim_view_max_exists; eauto. i. des.
    eexists (Some _). econs; eauto. }
  { exists None. econs. }
Qed.


Variant sim_message_max
        (f: Mapping.t) (v: version):
  forall (msg_src msg_tgt: Message.t), Prop :=
| sim_message_max_concrete
    val vw_src vw_tgt
    (SIM: sim_opt_view_max (fun _ => True) f v vw_src vw_tgt)
  :
    sim_message_max f v (Message.concrete val vw_src) (Message.concrete val vw_tgt)
| sim_message_max_undef
  :
    sim_message_max f v Message.undef Message.undef
| sim_message_max_reserve
  :
    sim_message_max f v Message.reserve Message.reserve
.


















    sim_opt_view_max L f v (Some vw_src) (Some vw_tgt)
| sim_message_max_undef
  :
    sim_opt_view_max L f v None None
.

Lemma sim_opt_view_max_sim (L: Loc.t -> Prop) f v vw_src vw_tgt
      (SIM: sim_opt_view_max L f v vw_src vw_tgt)
  :
    sim_opt_view L f v vw_src vw_tgt.
Proof.
  inv SIM; econs.
  eapply sim_view_max_sim; eauto.
Qed.

Lemma sim_opt_view_max_max f v vw_src vw_tgt
      vw
      (MAX: sim_opt_view_max (fun _ => True) f v vw_src vw_tgt)
      (SIM: sim_opt_view (fun _ => True) f v vw vw_tgt)
  :
    View.opt_le vw vw_src.
Proof.
  inv MAX; inv SIM.
  { econs. eapply sim_view_max_max; eauto. }
  { econs. }
  { econs. }
Qed.

Lemma sim_opt_view_max_mon_mapping L msgs f0 f1 v vw_src vw_tgt
      (WF: Mapping.wf f0)
      (VERWF: version_wf f0 v)
      (MAP: mapping_messages_le msgs f0 f1)
  :
    sim_opt_view_max L f0 v vw_src vw_tgt <-> sim_opt_view_max L f1 v vw_src vw_tgt.
Proof.
  split; i.
  { inv H; econs.
    erewrite <- sim_view_max_mon_mapping; eauto.
  }
  { inv H; econs.
    erewrite sim_view_max_mon_mapping; eauto.
  }
Qed.

Lemma sim_opt_view_max_exists L f v vw_tgt
      (WF: Mapping.wf f)
      (VER: version_wf f v)
  :
    exists vw_src, <<MAX: sim_opt_view_max L f v vw_src vw_tgt>>.
Proof.
  destruct vw_tgt as [vw_tgt|].
  { hexploit sim_view_max_exists; eauto. i. des.
    eexists (Some _). econs; eauto. }
  { exists None. econs. }
Qed.


Message.le



  exists ts_src' ts_tgt',
    (<<TSSRC: Time.le ts_src ts_src'>>) /\
    (<<TSTGT: Time.le ts_tgt' ts_tgt>>) /\
    (<<SIM: sim_timestamp_exact l f v ts_src' ts_tgt'>>).



Record world :=
  mk_world {
      mapping:> Mapping.t;
      vers: versions;
    }.

Definition world_wf (w: world): Prop :=
  (<<MAPPING: Mapping.wf w.(mapping)>>) /\
  (<<VERS: forall loc to ver (VER: w.(vers) loc to = Some ver),
      ver <= w.(mapping).(Mapping.ver)>>)
.

Definition version_wf (w: world) (v: version): Prop :=
  (<<VER: v <= w.(mapping).(Mapping.ver)>>).

Definition world_messages_le (msgs: Messages.t) (w0 w1: world): Prop :=
  (<<VER: w0.(mapping).(Mapping.ver) <= w1.(mapping).(Mapping.ver)>>) /\
  (<<TIME: forall v (VER: v <= w0.(mapping).(Mapping.ver)),
      w1.(mapping).(Mapping.map) v = w0.(mapping).(Mapping.map) v>>) /\
  (<<VERSIONS: forall loc from to msg ts v
                      (MSG: msgs loc from to msg)
                      (RESERVE: msg <> Message.reserve)
                      (VER: w0.(vers) loc ts = Some v)
                      (TS: Time.lt ts to),
      w1.(vers) loc ts = Some v>>) /\
  (<<MAPPING: forall loc from ffrom to msg
                     (MSG: msgs loc from to msg)
                     (RESERVE: msg <> Message.reserve)
                     (MAP: w0.(mapping).(Mapping.map) w0.(mapping).(Mapping.ver) loc from = Some ffrom),
      w1.(mapping).(Mapping.map) w1.(mapping).(Mapping.ver) loc from = Some ffrom>>)
.

Program Instance world_messages_le_PreOrder: forall msgs, PreOrder (world_messages_le msgs).
Next Obligation.
Proof.
  ii. red. splits; ss.
Qed.
Next Obligation.
Proof.
  ii. unfold world_messages_le in *. des. splits; eauto.
  { etrans; eauto. }
  { i. transitivity (y.(mapping).(Mapping.map) v); eauto.
    eapply TIME; eauto. etrans; eauto. }
Qed.

Lemma world_messages_le_mon:
  forall msgs0 msgs1 w0 w1
         (LE: world_messages_le msgs1 w0 w1)
         (MSGS: msgs0 <4= msgs1),
    world_messages_le msgs0 w0 w1.
Proof.
  unfold world_messages_le in *. i. des. splits; eauto.
Qed.

Definition sim_timestamp_exact (l: Loc.t) (w: world) (v: version) (ts_src ts_tgt: Time.t) :=
  w.(mapping).(Mapping.map) v l ts_tgt = Some ts_src.

Definition sim_timestamp (l: Loc.t) (w: world) (v: version) (ts_src ts_tgt: Time.t) :=
  exists ts_src' ts_tgt',
    (<<TSSRC: Time.le ts_src ts_src'>>) /\
    (<<TSTGT: Time.le ts_tgt' ts_tgt>>) /\
    (<<SIM: sim_timestamp_exact l w v ts_src' ts_tgt'>>).

Lemma sim_timestamp_exact_sim l w v ts_src ts_tgt
      (EXACT: sim_timestamp_exact l w v ts_src ts_tgt)
  :
    sim_timestamp l w v ts_src ts_tgt.
Proof.
  exists ts_src, ts_tgt. splits; auto; try refl.
Qed.

Lemma sim_timestamp_mon l msgs w0 v0 w1 v1 ts_src0 ts_tgt0 ts_src1 ts_tgt1
      (SIM: sim_timestamp l w0 v0 ts_src1 ts_tgt0)
      (WF0: version_wf w0 v0)
      (WF1: version_wf w1 v1)
      (VER: version_le v0 v1)
      (MAP: world_messages_le msgs w0 w1)
      (TSSRC: Time.le ts_src0 ts_src1)
      (TSTGT: Time.le ts_tgt0 ts_tgt1)
  :
    sim_timestamp l w1 v1 ts_src0 ts_tgt1.
Proof.


Admitted.

Definition sim_timemap (w: world) (v: version) (tm_src tm_tgt: TimeMap.t): Prop :=
  forall l, sim_timestamp l w v (tm_src l) (tm_tgt l).

Lemma sim_timemap_mon msgs w0 v0 w1 v1 tm_src0 tm_tgt0 tm_src1 tm_tgt1
      (SIM: sim_timemap w0 v0 tm_src1 tm_tgt0)
      (WF0: version_wf w0 v0)
      (WF1: version_wf w1 v1)
      (VER: version_le v0 v1)
      (MAP: world_messages_le msgs w0 w1)
      (TMSRC: TimeMap.le tm_src0 tm_src1)
      (TMTGT: TimeMap.le tm_tgt0 tm_tgt1)
  :
    sim_timemap w1 v1 tm_src0 tm_tgt1.
Proof.
  ii. eapply sim_timestamp_mon; eauto.
Qed.

Record sim_view (w: world) (v: version) (vw_src vw_tgt: View.t): Prop :=
  mk_sim_view {
      sim_view_pln: sim_timemap w v vw_src.(View.pln) vw_tgt.(View.pln);
      sim_view_rlx: sim_timemap w v vw_src.(View.rlx) vw_tgt.(View.rlx);
    }.

Lemma sim_view_mon msgs w0 v0 w1 v1 vw_src0 vw_tgt0 vw_src1 vw_tgt1
      (SIM: sim_view w0 v0 vw_src1 vw_tgt0)
      (WF0: version_wf w0 v0)
      (WF1: version_wf w1 v1)
      (VER: version_le v0 v1)
      (MAP: world_messages_le msgs w0 w1)
      (VWSRC: View.le vw_src0 vw_src1)
      (VWTGT: View.le vw_tgt0 vw_tgt1)
  :
    sim_view w1 v1 vw_src0 vw_tgt1.
Proof.
  econs.
  { eapply sim_timemap_mon.
    { eapply sim_view_pln; eauto. }
    all: eauto.
    { eapply VWSRC. }
    { eapply VWTGT. }
  }
  { eapply sim_timemap_mon.
    { eapply sim_view_rlx; eauto. }
    all: eauto.
    { eapply VWSRC. }
    { eapply VWTGT. }
  }
Qed.

Variant sim_opt_view (w: world) (v: version): forall (vw_src vw_tgt: option View.t), Prop :=
| sim_opt_view_some
    vw_src vw_tgt
    (SIM: sim_view w v vw_src vw_tgt)
  :
    sim_opt_view w v (Some vw_src) (Some vw_tgt)
| sim_opt_view_none
    vw_tgt
  :
    sim_opt_view w v None vw_tgt
.

Lemma sim_opt_view_mon msgs w0 v0 w1 v1 vw_src0 vw_tgt0 vw_src1 vw_tgt1
      (SIM: sim_opt_view w0 v0 vw_src1 vw_tgt0)
      (WF0: version_wf w0 v0)
      (WF1: version_wf w1 v1)
      (VER: version_le v0 v1)
      (MAP: world_messages_le msgs w0 w1)
      (VWSRC: View.opt_le vw_src0 vw_src1)
      (VWTGT: View.opt_le vw_tgt0 vw_tgt1)
  :
    sim_opt_view w1 v1 vw_src0 vw_tgt1.
Proof.
  inv SIM.
  { inv VWSRC; inv VWTGT; econs.
    eapply sim_view_mon; eauto. }
  { inv VWSRC; inv VWTGT; econs. }
Qed.

Variant sim_timemap_loc: forall
    (l: Loc.t)
    (w: world) (v: version)
    (ts_src: Time.t) (tm_src tm_tgt: TimeMap.t), Prop :=
| sim_timemap_loc_intro
    l w v tm_src tm_tgt
    (SIM: forall l' (LOC: l' <> l), sim_timestamp l' w v (tm_src l') (tm_tgt l'))
  :
    sim_timemap_loc l w v (tm_src l) tm_src tm_tgt
.

Lemma sim_timemap_loc_sim l w v ts_src tm_src tm_tgt
      (SIM: sim_timemap_loc l w v ts_src tm_src tm_tgt)
      (TS: sim_timestamp l w v ts_src (tm_tgt l))
  :
    sim_timemap w v tm_src tm_tgt.
Proof.
  inv SIM. ii. destruct (Loc.eq_dec l l0); clarify; auto.
Qed.

Record sim_view_loc (l: Loc.t) (w: world) (v: version)
       (ts_src: Time.t) (vw_src vw_tgt: View.t): Prop :=
  mk_sim_view_loc {
      sim_view_loc_pln: sim_timemap_loc l w v ts_src vw_src.(View.pln) vw_tgt.(View.pln);
      sim_view_loc_rlx: sim_timemap_loc l w v ts_src vw_src.(View.rlx) vw_tgt.(View.rlx);
    }.

Lemma sim_view_loc_sim l w v ts_src vw_src vw_tgt
      (SIM: sim_view_loc l w v ts_src vw_src vw_tgt)
      (PLN: sim_timestamp l w v ts_src (vw_tgt.(View.pln) l))
      (RLX: sim_timestamp l w v ts_src (vw_tgt.(View.rlx) l))
  :
    sim_view w v vw_src vw_tgt.
Proof.
  econs.
  { eapply sim_timemap_loc_sim; eauto. eapply sim_view_loc_pln; eauto. }
  { eapply sim_timemap_loc_sim; eauto. eapply sim_view_loc_rlx; eauto. }
Qed.

Variant sim_opt_view_loc (l: Loc.t) (w: world) (v: version) (ts_src: Time.t)
  : forall (vw_src vw_tgt: option View.t), Prop :=
| sim_opt_view_loc_some
    vw_src vw_tgt
    (SIM: sim_view_loc l w v ts_src vw_src vw_tgt)
  :
    sim_opt_view_loc l w v ts_src (Some vw_src) (Some vw_tgt)
| sim_opt_view_loc_none
    vw_tgt
  :
    sim_opt_view_loc l w v ts_src None vw_tgt
.

Lemma sim_opt_view_loc_sim l w v ts_src vw_src vw_tgt
      (SIM: sim_opt_view_loc l w v ts_src vw_src vw_tgt)
      (SOME: forall vw_tgt' (EQ: vw_tgt = Some vw_tgt'),
          (<<PLN: sim_timestamp l w v ts_src (vw_tgt'.(View.pln) l)>>) /\
          (<<RLX: sim_timestamp l w v ts_src (vw_tgt'.(View.rlx) l)>>))
  :
    sim_opt_view w v vw_src vw_tgt.
Proof.
  inv SIM; econs. eapply sim_view_loc_sim; eauto.
  { eapply SOME; eauto. }
  { eapply SOME; eauto. }
Qed.

Record sim_timestamp_max (l: Loc.t) (w: world) (v: version) (ts_src ts_tgt: Time.t): Prop :=
  sim_timestamp_max_intro {
      sim_timestamp_max_sim: sim_timestamp l w v ts_src ts_tgt;
      sim_timestamp_max_max: forall ts (SIM: sim_timestamp l w v ts ts_tgt),
          Time.le ts ts_src;
    }.

Lemma sim_timestamp_max_exists l w v ts_tgt
  :
    exists ts_src, <<MAX: sim_timestamp_max l w v ts_src ts_tgt>>.
Admitted.

Variant sim_timemap_loc_max: forall
    (l: Loc.t)
    (w: world) (v: version)
    (ts_src: Time.t) (tm_src tm_tgt: TimeMap.t), Prop :=
| sim_timemap_loc_max_intro
    l w v tm_src tm_tgt
    (SIM: forall l' (LOC: l' <> l), sim_timestamp_max l' w v (tm_src l') (tm_tgt l'))
  :
    sim_timemap_loc_max l w v (tm_src l) tm_src tm_tgt
.

Lemma sim_timemap_loc_max_sim l w v ts_src tm_src tm_tgt
      (SIM: sim_timemap_loc_max l w v ts_src tm_src tm_tgt)
  :
    sim_timemap_loc l w v ts_src tm_src tm_tgt.
Proof.
  inv SIM. econs. i. eapply sim_timestamp_max_sim; eauto.
Qed.

Lemma sim_timemap_loc_max_max l w v ts_src tm_src tm_tgt tm
      (MAX: sim_timemap_loc_max l w v ts_src tm_src tm_tgt)
      (SIM: sim_timemap_loc l w v ts_src tm tm_tgt)
  :
    TimeMap.le tm tm_src.
Proof.
  ii. inv SIM. inv MAX. destruct (Loc.eq_dec l loc); clarify.
  { rewrite H3. auto. refl. }
  { eapply sim_timestamp_max_max; eauto. }
Qed.

Lemma sim_timemap_loc_max_exists l w v ts_src tm_tgt
  :
    exists tm_src, <<MAX: sim_timemap_loc_max l w v ts_src tm_src tm_tgt>>.
Proof.
  hexploit (choice (fun l' ts => (l <> l' -> sim_timestamp_max l' w v ts (tm_tgt l')) /\ (l = l' -> ts = ts_src))).
  { i. destruct (Loc.eq_dec l x).
    { exists ts_src. splits; ss. }
    { hexploit sim_timestamp_max_exists. i. des.
      exists ts_src0. splits; ss. i. eapply MAX. }
  }
  i. des. exists f. subst. replace ts_src with (f l).
  { econs; eauto. i. specialize (H l'). des. auto. }
  { specialize (H l). des. auto. }
Qed.

Record sim_view_loc_max (l: Loc.t) (w: world) (v: version)
       (ts_src: Time.t) (vw_src vw_tgt: View.t): Prop :=
  mk_sim_view_loc_max {
      sim_view_loc_max_pln: sim_timemap_loc_max l w v ts_src vw_src.(View.pln) vw_tgt.(View.pln);
      sim_view_loc_max_rlx: sim_timemap_loc_max l w v ts_src vw_src.(View.rlx) vw_tgt.(View.rlx);
    }.

Lemma sim_view_loc_max_sim l w v ts_src vw_src vw_tgt
      (SIM: sim_view_loc_max l w v ts_src vw_src vw_tgt)
  :
    sim_view_loc l w v ts_src vw_src vw_tgt.
Proof.
  inv SIM. econs.
  { eapply sim_timemap_loc_max_sim; eauto. }
  { eapply sim_timemap_loc_max_sim; eauto. }
Qed.

Lemma sim_view_loc_max_max l w v ts_src vw_src vw_tgt vw
      (MAX: sim_view_loc_max l w v ts_src vw_src vw_tgt)
      (SIM: sim_view_loc l w v ts_src vw vw_tgt)
  :
    View.le vw vw_src.
Proof.
  inv MAX. inv SIM. econs.
  { eapply sim_timemap_loc_max_max; eauto. }
  { eapply sim_timemap_loc_max_max; eauto. }
Qed.

Lemma sim_view_loc_max_exists l w v ts_src vw_tgt
  :
    exists vw_src, <<MAX: sim_view_loc_max l w v ts_src vw_src vw_tgt>>.
Proof.
  hexploit (@sim_timemap_loc_max_exists l w v ts_src vw_tgt.(View.pln)); auto.
  i. des.
  hexploit (@sim_timemap_loc_max_exists l w v ts_src vw_tgt.(View.rlx)); auto.
  i. des.
  exists (View.mk tm_src tm_src0). econs; eauto.
Qed.

Variant sim_opt_view_loc_max (l: Loc.t) (w: world) (v: version) (ts_src: Time.t)
  : forall (vw_src vw_tgt: option View.t), Prop :=
| sim_opt_view_loc_max_some
    vw_src vw_tgt
    (SIM: sim_view_loc_max l w v ts_src vw_src vw_tgt)
  :
    sim_opt_view_loc_max l w v ts_src (Some vw_src) (Some vw_tgt)
| sim_opt_view_loc_max_none
  :
    sim_opt_view_loc_max l w v ts_src None None
.

Lemma sim_opt_view_loc_max_sim l w v ts_src vw_src vw_tgt
      (SIM: sim_opt_view_loc_max l w v ts_src vw_src vw_tgt)
  :
    sim_opt_view_loc l w v ts_src vw_src vw_tgt.
Proof.
  inv SIM; econs. eapply sim_view_loc_max_sim; eauto.
Qed.

Lemma sim_opt_view_loc_max_max l w v ts_src vw_src vw_tgt vw
      (MAX: sim_opt_view_loc_max l w v ts_src vw_src vw_tgt)
      (SIM: sim_opt_view_loc l w v ts_src vw vw_tgt)
  :
    View.opt_le vw vw_src.
Proof.
  inv MAX; inv SIM; econs.
  eapply sim_view_loc_max_max; eauto.
Qed.

Lemma sim_opt_view_loc_max_exists l w v ts_src vw_tgt
  :
    exists vw_src, <<MAX: sim_opt_view_loc_max l w v ts_src vw_src vw_tgt>>.
Proof.
  destruct vw_tgt as [vw|].
  { hexploit sim_view_loc_max_exists. i. des.
    eexists (Some _). econs; eauto. }
  { exists None. econs. }
Qed.

Local.write_step

Definition flags := Loc.t -> bool.
Definition flags_bot: flags := fun _ => false.

Definition flags_le (f_tgt f_src: flags): Prop :=
  forall loc, (f_tgt loc) -> (f_src loc).

Definition update_flags (f: flags) (l: Loc.t) (b: bool): flags :=
  fun l' => if (Loc.eq_dec l' l) then b else f l'.


Definition sim_timemap (f_src: flags) (b: bool) (w: world) (sc_src sc_tgt: TimeMap.t): Prop. Admitted.

Definition sim_memory (f_src: flags) (b: bool) (w: world) (mem_src: Memory.t) (mem_tgt: Memory.t): Prop. Admitted.


Definition value_map := Loc.t -> option (Const.t * Const.t).

Definition value_map_le (vm0 vm1: value_map): Prop :=
  forall loc,
    match (vm0 loc), (vm1 loc) with
    | _, None => True
    | Some vs0, Some vs1 => vs0 = vs1
    | _, _ => False
    end.

Definition update_value_map (vm: value_map) (l: Loc.t) (vs: option (Const.t * Const.t)) :=
  fun l' => if (Loc.eq_dec l' l) then vs else vm l'.


Definition sim_local (vm: value_map) (f_src: flags) (f_tgt: flags)
           (b: bool) (w: world)
           (lc_src: Local.t) (lc_tgt: Local.t)
           (mem_src: Memory.t) (mem_tgt: Memory.t)
           (sc_src: TimeMap.t) (sc_tgt: TimeMap.t): Prop. Admitted.


Lemma sim_local_lower vm flags_bot f_tgt w lc_src lc_tgt0 lc_tgt1 mem_src
      mem_tgt0 mem_tgt1 sc_src sc_tgt0 sc_tgt1
      (SIM: sim_local vm flags_bot f_tgt false w lc_src lc_tgt0 mem_src mem_tgt0 sc_src sc_tgt0)
      (LOCAL: lower_local lc_tgt0 lc_tgt1)
      (MEM: lower_memory mem_tgt0 mem_tgt1)
      (SC: TimeMap.le sc_tgt0 sc_tgt1)
  :
    sim_local vm flags_bot f_tgt false w lc_src lc_tgt1 mem_src mem_tgt1 sc_src sc_tgt1.
Admitted.

Lemma sim_update_latest lang_src
      (st_src: lang_src.(Language.state))
      vm f_tgt w0 lc_src lc_tgt mem_src mem_tgt sc_src sc_tgt
      (LOCAL: sim_local vm flags_bot f_tgt true w0 lc_src lc_tgt mem_src mem_tgt sc_src sc_tgt)
      (MEM: sim_memory flags_bot false w0 mem_src mem_tgt)
      (SC: sim_timemap flags_bot false w0 sc_src sc_tgt)
  :
    exists mem_src' lc_src' w1,
      (<<STEPS: rtc (@Thread.tau_step _)
                    (Thread.mk _ st_src lc_src sc_src mem_src)
                    (Thread.mk _ st_src lc_src' sc_src mem_src')>>) /\
      (<<LOCAL: sim_local vm flags_bot f_tgt false w1 lc_src' lc_tgt mem_src' mem_tgt sc_src sc_tgt>>) /\
      (<<MEM: sim_memory flags_bot false w1 mem_src' mem_tgt>>) /\
      (<<SC: sim_timemap flags_bot false w1 sc_src sc_tgt>>) /\
      (<<WORLD: world_messages_le (unchangable mem_src lc_src.(Local.promises)) w0 w1>>).
Admitted.

Lemma sim_memory_lower f_src w mem_src mem_tgt0 mem_tgt1
      (SIM: sim_memory f_src false w mem_src mem_tgt0)
      (MEM: lower_memory mem_tgt0 mem_tgt1)
  :
    sim_memory f_src false w mem_src mem_tgt1.
Admitted.

Lemma sim_timemap_lower f_src w sc_src sc_tgt0 sc_tgt1
      (SIM: sim_timemap f_src false w sc_src sc_tgt0)
      (SC: TimeMap.le sc_tgt0 sc_tgt1)
  :
    sim_timemap f_src false w sc_src sc_tgt1.
Admitted.







Lemma sim_promise_consistent
      vm f_src f_tgt b w lc_src lc_tgt mem_src mem_tgt sc_src sc_tgt
      (LOCAL: sim_local vm f_src f_tgt false w lc_src lc_tgt mem_src mem_tgt sc_src sc_tgt)
      (MEM: sim_memory flags_bot b w mem_src mem_tgt)
      (SC: sim_timemap flags_bot b w sc_src sc_tgt)
      (CONSISTENT: Local.promise_consistent lc_tgt)
  :
    Local.promise_consistent lc_src.
Admitted.

Lemma sim_cap vm f_tgt w0 lc_src lc_tgt mem_src0 mem_tgt0 mem_tgt1 sc_src sc_tgt
      (LOCAL: sim_local vm flags_bot f_tgt false w0 lc_src lc_tgt mem_src0 mem_tgt0 sc_src sc_tgt)
      (MEM: sim_memory flags_bot false w0 mem_src0 mem_tgt0)
      (SC: sim_timemap flags_bot false w0 sc_src sc_tgt)
      (CAP: Memory.cap mem_tgt0 mem_tgt1)
  :
    exists tm_src mem_src1 w1,
      (<<TM: forall loc, Time.lt (Memory.max_ts loc mem_src0) (tm_src loc)>>) /\
      (<<CAP: CapFlex.cap_flex mem_src0 mem_src1 tm_src>>) /\
      (<<MEM: sim_memory flags_bot true w1 mem_src1 mem_tgt1>>) /\
      (<<SC: sim_timemap flags_bot true w1 sc_src sc_tgt>>) /\
      (<<LOCAL: sim_local vm flags_bot f_tgt true w1 lc_src lc_tgt mem_src1 mem_tgt1 sc_src sc_tgt>>) /\
      (<<WORLD: world_messages_le (unchangable mem_src0 lc_src.(Local.promises)) w0 w1>>).
Admitted.

Lemma sim_future vm0 f_tgt w0 lc_src lc_tgt mem_src0 mem_tgt0 sc_src0 sc_tgt0
      (SIM: sim_local vm0 flags_bot f_tgt false w0 lc_src lc_tgt mem_src0 mem_tgt0 sc_src0 sc_tgt0)
      (MEM0: sim_memory flags_bot false w0 mem_src0 mem_tgt0)
      (SC0: sim_timemap flags_bot false w0 sc_src0 sc_tgt0)

      w1 mem_src1 mem_tgt1 sc_src1 sc_tgt1
      (WORLD: world_messages_le (Messages.of_memory lc_src.(Local.promises)) w0 w1)
      (MEMSRC: Memory.future mem_src0 mem_src1)
      (MEMTGT: Memory.future mem_tgt0 mem_tgt1)
      (SCSRC: TimeMap.le sc_src0 sc_src1)
      (SCTGT: TimeMap.le sc_tgt0 sc_tgt1)
      (MEM1: sim_memory flags_bot false w1 mem_src1 mem_tgt1)
      (SC1: sim_timemap flags_bot false w1 sc_src1 sc_tgt1)
  :
    exists vm1,
      (<<SIM: sim_local vm1 flags_bot f_tgt true w1 lc_src lc_tgt mem_src1 mem_tgt1 sc_src1 sc_tgt1>>) /\
      (<<VALUES: value_map_le vm0 vm1>>)
.
Admitted.

Lemma sim_make_promise_match lang_src
      (st_src: lang_src.(Language.state))
      vm f_src f_tgt b w0 lc_src lc_tgt mem_src mem_tgt sc_src sc_tgt
      loc v
      (FLAG: f_src loc = true)
      (LOCAL: sim_local vm f_src f_tgt false w0 lc_src lc_tgt mem_src mem_tgt sc_src sc_tgt)
      (MEM: sim_memory f_src b w0 mem_src mem_tgt)
      (SC: sim_timemap f_src b w0 sc_src sc_tgt)
      (VAL: vm loc = Some (v, v))
  :
    exists mem_src' lc_src' w1,
      (<<STEPS: rtc (@Thread.tau_step _)
                    (Thread.mk _ st_src lc_src sc_src mem_src)
                    (Thread.mk _ st_src lc_src' sc_src mem_src')>>) /\
      (<<LOCAL: sim_local vm (update_flags f_src loc false) (update_flags f_tgt loc false) false w1 lc_src' lc_tgt mem_src' mem_tgt sc_src sc_tgt>>) /\
      (<<MEM: sim_memory (update_flags f_src loc false) b w1 mem_src' mem_tgt>>) /\
      (<<WORLD: world_messages_le (unchangable mem_src lc_src.(Local.promises)) w0 w1>>).
Admitted.

Lemma sim_make_promise_not_match lang_src
      (st_src: lang_src.(Language.state))
      vm f_src f_tgt b w0 lc_src lc_tgt mem_src mem_tgt sc_src sc_tgt
      loc v_src v_tgt
      (FLAG: f_src loc = true)
      (LOCAL: sim_local vm f_src f_tgt false w0 lc_src lc_tgt mem_src mem_tgt sc_src sc_tgt)
      (MEM: sim_memory f_src b w0 mem_src mem_tgt)
      (SC: sim_timemap f_src b w0 sc_src sc_tgt)
      (VAL: vm loc = Some (v_src, v_tgt))
  :
    exists mem_src' lc_src' w1,
      (<<STEPS: rtc (@Thread.tau_step _)
                    (Thread.mk _ st_src lc_src sc_src mem_src)
                    (Thread.mk _ st_src lc_src' sc_src mem_src')>>) /\
      (<<LOCAL: sim_local vm (update_flags f_src loc false) (update_flags f_tgt loc true) false w1 lc_src' lc_tgt mem_src' mem_tgt sc_src sc_tgt>>) /\
      (<<MEM: sim_memory (update_flags f_src loc false) b w1 mem_src' mem_tgt>>) /\
      (<<WORLD: world_messages_le (unchangable mem_src lc_src.(Local.promises)) w0 w1>>).
Admitted.

Lemma sim_make_lower lang_src
      (st_src: lang_src.(Language.state))
      vm f_src f_tgt b w0 lc_src lc_tgt mem_src mem_tgt sc_src sc_tgt
      loc
      (LOCAL: sim_local vm f_src f_tgt false w0 lc_src lc_tgt mem_src mem_tgt sc_src sc_tgt)
      (MEM: sim_memory f_src b w0 mem_src mem_tgt)
      (SC: sim_timemap f_src b w0 sc_src sc_tgt)
  :
    exists mem_src' lc_src' w1,
      (<<STEPS: rtc (@Thread.tau_step _)
                    (Thread.mk _ st_src lc_src sc_src mem_src)
                    (Thread.mk _ st_src lc_src' sc_src mem_src')>>) /\
      (<<LOCAL: sim_local vm f_src (update_flags f_tgt loc true) false w1 lc_src' lc_tgt mem_src' mem_tgt sc_src sc_tgt>>) /\
      (<<MEM: sim_memory f_src b w1 mem_src' mem_tgt>>) /\
      (<<WORLD: world_messages_le (unchangable mem_src lc_src.(Local.promises)) w0 w1>>).
Admitted.

Lemma sim_na_racy_read_tgt
      vm f_src f_tgt b w lc_src lc_tgt mem_src mem_tgt sc_src sc_tgt
      loc val ord
      (LOCAL: sim_local vm f_src f_tgt false w lc_src lc_tgt mem_src mem_tgt sc_src sc_tgt)
      (MEM: sim_memory f_src b w mem_src mem_tgt)
      (SC: sim_timemap f_src b w sc_src sc_tgt)
      (READ: Local.racy_read_step lc_tgt mem_tgt loc val ord)
  :
    (<<VALUE: vm loc = None>>) /\
    (<<ORD: ord = Ordering.na>>).
Admitted.

Lemma sim_na_read_tgt
      vm f_src f_tgt b w lc_src lc_tgt0 mem_src mem_tgt sc_src sc_tgt
      lc_tgt1 loc ts val released
      (LOCAL: sim_local vm f_src f_tgt false w lc_src lc_tgt0 mem_src mem_tgt sc_src sc_tgt)
      (MEM: sim_memory f_src b w mem_src mem_tgt)
      (SC: sim_timemap f_src b w sc_src sc_tgt)
      (READ: Local.read_step lc_tgt0 mem_tgt loc ts val released Ordering.na lc_tgt1)
  :
    forall v_src v_tgt (VALUE: vm loc = Some (v_src, v_tgt)), v_tgt = val.
Admitted.

Lemma sim_na_racy_write_tgt
      vm f_src f_tgt b w lc_src lc_tgt mem_src mem_tgt sc_src sc_tgt
      loc ord
      (LOCAL: sim_local vm f_src f_tgt false w lc_src lc_tgt mem_src mem_tgt sc_src sc_tgt)
      (MEM: sim_memory f_src b w mem_src mem_tgt)
      (SC: sim_timemap f_src b w sc_src sc_tgt)
      (WRITE: Local.racy_write_step lc_tgt mem_tgt loc ord)
  :
    (<<VALUE: vm loc = None>>) /\
    (<<ORD: ord = Ordering.na>>).
Admitted.

Lemma sim_na_write_tgt
      vm f_src f_tgt b w lc_src lc_tgt0 mem_src mem_tgt0 sc_src sc_tgt0
      loc mem_tgt1 lc_tgt1 sc_tgt1 from to val ord msgs kinds kind v_src v_tgt
      (LOCAL: sim_local vm f_src f_tgt false w lc_src lc_tgt0 mem_src mem_tgt0 sc_src sc_tgt0)
      (MEM: sim_memory f_src b w mem_src mem_tgt0)
      (SC: sim_timemap f_src b w sc_src sc_tgt0)
      (WRITE: Local.write_na_step lc_tgt0 sc_tgt0 mem_tgt0 loc from to val ord lc_tgt1 sc_tgt1 mem_tgt1 msgs kinds kind)
      (LOWER: lower_memory mem_tgt1 mem_tgt0)
      (FLAG: f_tgt loc = true)
      (VALUES: vm loc = Some (v_src, v_tgt))
  :
    (<<LOCAL: sim_local (update_value_map vm loc (Some (v_src, val))) f_src f_tgt false w lc_src lc_tgt1 mem_src mem_tgt1 sc_src sc_tgt1>>) /\
    (<<MEM: sim_memory f_src b w mem_src mem_tgt1>>) /\
    (<<SC: sim_timemap f_src b w sc_src sc_tgt1>>) /\
    (<<ORD: ord = Ordering.na>>) /\
    (<<SC: sc_tgt1 = sc_tgt0>>).
Admitted.

Lemma sim_na_read_src
      vm f_src f_tgt b w lc_src lc_tgt mem_src mem_tgt sc_src sc_tgt
      loc v_src v_tgt
      (LOCAL: sim_local vm f_src f_tgt false w lc_src lc_tgt mem_src mem_tgt sc_src sc_tgt)
      (MEM: sim_memory f_src b w mem_src mem_tgt)
      (SC: sim_timemap f_src b w sc_src sc_tgt)
      (VALUE: vm loc = Some (v_src, v_tgt))
  :
    exists ts released,
      (<<READ: Local.read_step lc_src mem_src loc ts v_src released Ordering.na lc_src>>).
Admitted.

Lemma sim_na_racy_read_src
      vm f_src f_tgt b w lc_src lc_tgt mem_src mem_tgt sc_src sc_tgt
      loc val
      (LOCAL: sim_local vm f_src f_tgt false w lc_src lc_tgt mem_src mem_tgt sc_src sc_tgt)
      (MEM: sim_memory f_src b w mem_src mem_tgt)
      (SC: sim_timemap f_src b w sc_src sc_tgt)
      (VALUE: vm loc = None)
  :
    Local.racy_read_step lc_src mem_src loc val Ordering.na.
Admitted.

Lemma sim_na_racy_write_src
      vm f_src f_tgt b w lc_src lc_tgt mem_src mem_tgt sc_src sc_tgt
      loc
      (LOCAL: sim_local vm f_src f_tgt false w lc_src lc_tgt mem_src mem_tgt sc_src sc_tgt)
      (MEM: sim_memory f_src b w mem_src mem_tgt)
      (SC: sim_timemap f_src b w sc_src sc_tgt)
      (VALUE: vm loc = None)
  :
    Local.racy_write_step lc_src mem_src loc Ordering.na.
Admitted.

Lemma sim_na_write_src
      vm f_src f_tgt b w lc_src0 lc_tgt mem_src0 mem_tgt sc_src sc_tgt
      loc v_src v_tgt val
      (LOCAL: sim_local vm f_src f_tgt false w lc_src0 lc_tgt mem_src0 mem_tgt sc_src sc_tgt)
      (MEM: sim_memory f_src b w mem_src0 mem_tgt)
      (SC: sim_timemap f_src b w sc_src sc_tgt)
      (VALUE: vm loc = Some (v_src, v_tgt))
  :
    let f_src := update_flags f_src loc true in
    let vm := (update_value_map vm loc (Some (val, v_tgt))) in
    exists from to msgs kinds kind lc_src1 mem_src1,
      (<<WRITE: Local.write_na_step lc_src0 sc_src mem_src0 loc from to val Ordering.na lc_src1 sc_src mem_src1 msgs kinds kind>>) /\
      (<<LOCAL: sim_local vm f_src f_tgt false w lc_src1 lc_tgt mem_src1 mem_tgt sc_src sc_tgt>>) /\
      (<<MEM: sim_memory f_src b w mem_src1 mem_tgt>>) /\
      (<<SC: sim_timemap f_src b w sc_src sc_tgt>>).
Admitted.
