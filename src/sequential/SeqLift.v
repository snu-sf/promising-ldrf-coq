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

Require Import Lia.

Set Implicit Arguments.


Definition flag := bool.
Definition flags := Loc.t -> flag.

Definition version := Loc.t -> nat.
Definition version_le (v0 v1: version): Prop := forall loc, le (v0 loc) (v1 loc).

Program Instance version_le_PreOrder: PreOrder version_le.
Next Obligation.
Proof.
  ii. refl.
Qed.
Next Obligation.
Proof.
  ii. etrans; eauto.
Qed.

Definition versions := Loc.t -> Time.t -> option version.
Definition reserve_versions := Loc.t -> Time.t -> option nat.

Module Mapping.
  Record t: Type :=
    mk
      { map:> nat -> Time.t -> option Time.t;
        ver: nat;
        times: nat -> Time.t -> Prop;
      }.

  Record wf (f: t): Prop :=
    { map_finite: forall v, exists l, forall ts fts (MAP: f v ts = Some fts),
            List.In (ts, fts) l;
      mapping_map_lt: forall v ts0 ts1 fts0 fts1
                             (MAP0: f.(map) v ts0 = Some fts0) (MAP0: f.(map) v ts1 = Some fts1),
          Time.lt ts0 ts1 <-> Time.lt fts0 fts1;
      mapping_incr: forall v0 v1 ts fts0
                           (VER0: v0 <= v1)
                           (VER1: v1 <= f.(ver))
                           (MAP0: f.(map) v0 ts = Some fts0),
          exists fts1,
            (<<MAP: f.(map) v1 ts = Some fts1>>) /\
            (<<TS: Time.le fts0 fts1>>);
      mapping_empty: forall v (VER: f.(ver) < v) ts, f v ts = None;
      mapping_bot: f.(map) 0 Time.bot = Some Time.bot;
      times_finite: forall v, exists l, forall ts (CLOSED: f.(times) v ts),
              List.In ts l;
      times_incr: forall v0 v1 ts
                         (VER0: v0 <= v1)
                         (VER1: v1 <= f.(ver))
                         (TIME: f.(times) v0 ts),
          f.(times) v1 ts;
      times_empty: forall v (VER: f.(ver) < v) ts, ~ f.(times) v ts;
      times_bot: f.(times) 0 Time.bot;
    }.

  Definition le (f0 f1: t): Prop :=
    (<<VER: f0.(ver) <= f1.(ver)>>) /\
    (<<MAP: forall v (VER: v <= f0.(ver)),
        f1.(map) v = f0.(map) v>>) /\
    (<<TIME: forall v (VER: v <= f0.(ver)),
        f1.(times) v =f0.(times) v>>)
  .

  Program Instance le_PreOrder: PreOrder le.
  Next Obligation.
  Proof.
    ii. unfold le. splits; i; refl.
  Qed.
  Next Obligation.
  Proof.
    ii. unfold le in *. des. splits; i.
    { etrans; eauto. }
    { transitivity (y.(map) v); eauto. eapply MAP; eauto. lia. }
    { transitivity (y.(times) v); eauto. eapply TIME; eauto. lia. }
  Qed.

  Definition le_strong (f0 f1: t): Prop :=
    (<<VER: f0.(ver) <= f1.(ver)>>) /\
    (<<MAP: forall v (VER: v <= f0.(ver)),
        f1.(map) v = f0.(map) v>>) /\
    (<<TIME: forall v (VER: v <= f0.(ver)),
        f1.(times) v =f0.(times) v>>) /\
    (<<PRESERVE: forall v ts fts
                        (VER0: f0.(ver) < v) (VER1: v <= f1.(ver))
                        (MAP: f0.(map) f0.(ver) ts = Some fts),
        f1.(map) v ts = Some fts>>)
  .

  Program Instance le_strong_PreOrder: PreOrder le_strong.
  Next Obligation.
  Proof.
    ii. unfold le_strong. splits; i; auto. exfalso. lia.
  Qed.
  Next Obligation.
  Proof.
    ii. unfold le_strong in *. des. splits; i.
    { etrans; eauto. }
    { transitivity (y.(map) v); eauto. eapply MAP; eauto. lia. }
    { transitivity (y.(times) v); eauto. eapply TIME; eauto. lia. }
    { assert (v <= y.(ver) \/ y.(ver) < v) by lia. des.
      { rewrite MAP; eauto. }
      { eapply PRESERVE; eauto.
        assert (x.(ver) < y.(ver) \/ x.(ver) = y.(ver)) by lia. des.
        { eapply PRESERVE0; eauto. }
        { rewrite H0 in *. rewrite MAP0; eauto. }
      }
    }
  Qed.

  Lemma le_strong_le f0 f1
        (LE: le_strong f0 f1)
    :
      le f0 f1.
  Proof.
    unfold le_strong, le in*. des. splits; auto.
  Qed.

  Lemma mapping_map_le (f: t) (WF: wf f):
    forall v ts0 ts1 fts0 fts1
           (MAP0: f.(map) v ts0 = Some fts0) (MAP0: f.(map) v ts1 = Some fts1),
      Time.le ts0 ts1 <-> Time.le fts0 fts1.
  Proof.
    i. split.
    { i. destruct (Time.le_lt_dec fts0 fts1); auto.
      erewrite <- mapping_map_lt in l; eauto. timetac. }
    { i. destruct (Time.le_lt_dec ts0 ts1); auto.
      erewrite mapping_map_lt in l; eauto. timetac. }
  Qed.

  Lemma mapping_map_eq (f: t) (WF: wf f):
    forall v ts0 ts1 fts0 fts1
           (MAP0: f.(map) v ts0 = Some fts0) (MAP0: f.(map) v ts1 = Some fts1),
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

  Definition ts := Loc.t -> Mapping.t.

  Definition vers (f: ts): version :=
    fun loc => (f loc).(ver).

  Definition wfs (f: ts): Prop := forall loc, wf (f loc).

  Definition les (f0 f1: ts): Prop :=
    forall loc, le (f0 loc) (f1 loc).

  Program Instance les_PreOrder: PreOrder les.
  Next Obligation.
  Proof.
    ii. refl.
  Qed.
  Next Obligation.
  Proof.
    ii. etrans; eauto.
  Qed.

  Definition les_strong (f0 f1: ts): Prop :=
    forall loc, le_strong (f0 loc) (f1 loc).

  Program Instance les_strong_PreOrder: PreOrder les_strong.
  Next Obligation.
  Proof.
    ii. refl.
  Qed.
  Next Obligation.
  Proof.
    ii. etrans; eauto.
  Qed.

  Lemma les_strong_les f0 f1
        (LE: les_strong f0 f1)
    :
      les f0 f1.
  Proof.
    ii. eapply le_strong_le; eauto.
  Qed.

  Definition closed (f: t) (v: nat) (ts: Time.t): Prop :=
    f.(times) v ts.
End Mapping.


Definition reserve_versions_wf (f: Mapping.ts) (rvers: reserve_versions): Prop :=
  forall loc to ver (VER: rvers loc to = Some ver),
    le ver (Mapping.vers f loc).

Definition loc_version_wf (f: Mapping.t) (v: nat): Prop :=
  le v f.(Mapping.ver).

Definition version_wf (f: Mapping.ts) (v: version): Prop :=
  forall loc, loc_version_wf (f loc) (v loc).

Definition opt_version_wf (f: Mapping.ts) (v: option version): Prop :=
  match v with
  | Some v => version_wf f v
  | None => True
  end.

Definition versions_wf (f: Mapping.ts) (vers: versions): Prop :=
  forall loc to, opt_version_wf f (vers loc to).

Lemma version_le_version_wf f v
  :
    version_le v (Mapping.vers f) <-> version_wf f v.
Proof.
  split.
  { ii. eapply H. }
  { ii. eapply H. }
Qed.

Definition versions_messages_le (msgs: Messages.t) (vers0 vers1: versions): Prop :=
  forall loc from to msg ts v
         (MSG: msgs loc from to msg)
         (RESERVE: msg <> Message.reserve)
         (VER: vers0 loc ts = Some v)
         (TS: Time.lt ts to),
    vers1 loc ts = Some v.

Program Instance versions_messages_le_PreOrder: forall msgs, PreOrder (versions_messages_le msgs).
Next Obligation.
Proof.
  ii. eauto.
Qed.
Next Obligation.
Proof.
  ii. eauto.
Qed.

Lemma versions_messages_le_mon:
  forall msgs0 msgs1 f0 f1
         (LE: versions_messages_le msgs1 f0 f1)
         (MSGS: msgs0 <4= msgs1),
    versions_messages_le msgs0 f0 f1.
Proof.
  ii. eauto.
Qed.

Lemma mapping_latest_wf_loc f
  :
    loc_version_wf f (Mapping.ver f).
Proof.
  ii. red. refl.
Qed.

Lemma mapping_latest_wf f
  :
    version_wf f (Mapping.vers f).
Proof.
  ii. red. refl.
Qed.

Definition sim_timestamp_exact (f: Mapping.t) (v: nat) (ts_src ts_tgt: Time.t) :=
  f.(Mapping.map) v ts_tgt = Some ts_src.

Lemma mapping_map_finite_exact (f: Mapping.t) (WF: Mapping.wf f) v:
  exists l, forall ts fts,
      sim_timestamp_exact f v fts ts <-> List.In (ts, fts) l.
Proof.
  hexploit Mapping.map_finite; eauto. i. des.
  hexploit (@list_filter_exists _ (fun '(ts, fts) => f.(Mapping.map) v ts = Some fts) l).
  i. des. exists l'. i. split; i.
  { eapply COMPLETE. splits; eauto. }
  { eapply COMPLETE in H0. des; auto. }
Qed.

Lemma mapping_times_finite_exact (f: Mapping.t) (WF: Mapping.wf f) v:
  exists l, forall ts,
      Mapping.closed f v ts <-> List.In ts l.
Proof.
  hexploit Mapping.times_finite; eauto. i. des.
  hexploit (@list_filter_exists _ (fun ts => Mapping.closed f v ts) l).
  i. des. exists l'. i. split; i.
  { eapply COMPLETE. splits; eauto. }
  { eapply COMPLETE in H0. des; auto. }
Qed.

Lemma sim_timestamp_exact_inject f v ts_src0 ts_src1 ts_tgt
      (SIM0: sim_timestamp_exact f v ts_src0 ts_tgt)
      (SIM1: sim_timestamp_exact f v ts_src1 ts_tgt)
  :
    ts_src0 = ts_src1.
Proof.
  unfold sim_timestamp_exact in *. clarify.
Qed.

Lemma sim_timestamp_exact_mon_ver f v0 v1 ts_src0 ts_tgt
      (SIM: sim_timestamp_exact f v0 ts_src0 ts_tgt)
      (VER: v0 <= v1)
      (WF: Mapping.wf f)
      (VERWF: loc_version_wf f v1)
  :
    exists ts_src1, (<<TS: Time.le ts_src0 ts_src1>>) /\ (<<SIM: sim_timestamp_exact f v1 ts_src1 ts_tgt>>).
Proof.
  unfold sim_timestamp_exact in *.
  eapply Mapping.mapping_incr in SIM; eauto. des. esplits; eauto.
Qed.

Lemma sim_timestamp_exact_mon_mapping f0 f1 v ts_src ts_tgt
      (WF: Mapping.wf f0)
      (VERWF: loc_version_wf f0 v)
      (MAP: Mapping.le f0 f1)
  :
    sim_timestamp_exact f0 v ts_src ts_tgt <-> sim_timestamp_exact f1 v ts_src ts_tgt.
Proof.
  unfold sim_timestamp_exact, Mapping.le in *. des.
  rewrite MAP; eauto.
Qed.

Lemma sim_timestamp_exact_mon_strong f0 f1 ts_src ts_tgt
      (WF: Mapping.wf f0)
      (MAP: Mapping.le_strong f0 f1)
      (SIM: sim_timestamp_exact f0 f0.(Mapping.ver) ts_src ts_tgt)
  :
    sim_timestamp_exact f1 f1.(Mapping.ver) ts_src ts_tgt.
Proof.
  unfold sim_timestamp_exact, Mapping.le_strong in *. des.
  assert (f0.(Mapping.ver) < f1.(Mapping.ver) \/ f0.(Mapping.ver) = f1.(Mapping.ver)) by lia.
  des.
  { eapply PRESERVE; eauto. }
  { rewrite H in *. rewrite MAP; eauto. }
Qed.


Lemma sim_closed_mon_ver f v0 v1 ts
      (CLOSED: Mapping.closed f v0 ts)
      (VER: v0 <= v1)
      (WF: Mapping.wf f)
      (VERWF: loc_version_wf f v1)
  :
    Mapping.closed f v1 ts.
Proof.
  unfold Mapping.closed in *.
  eapply Mapping.times_incr; eauto.
Qed.

Lemma sim_closed_mon_mapping f0 f1 v ts
      (WF: Mapping.wf f0)
      (VERWF: loc_version_wf f0 v)
      (MAP: Mapping.le f0 f1)
  :
    Mapping.closed f0 v ts <-> Mapping.closed f1 v ts.
Proof.
  unfold Mapping.closed, Mapping.le in *. des. split.
  { i. rewrite TIME; eauto. }
  { i. rewrite <- TIME; eauto. }
Qed.

Lemma sim_closed_bot f v
      (WF: Mapping.wf f)
      (VERWF: loc_version_wf f v)
  :
    Mapping.closed f v Time.bot.
Proof.
  hexploit Mapping.times_bot; eauto. i.
  eapply Mapping.times_incr with (v1:=v) in H; eauto. lia.
Qed.

Lemma sim_closed_join f v ts0 ts1
      (CLOSED0: Mapping.closed f v ts0)
      (CLOSED1: Mapping.closed f v ts1)
  :
    Mapping.closed f v (Time.join ts0 ts1).
Proof.
  unfold Time.join. des_ifs.
Qed.

Lemma sim_closed_meet f v ts0 ts1
      (CLOSED0: Mapping.closed f v ts0)
      (CLOSED1: Mapping.closed f v ts1)
  :
    Mapping.closed f v (Time.meet ts0 ts1).
Proof.
  unfold Time.meet. des_ifs.
Qed.


Definition sim_timestamp (f: Mapping.t) (v: nat) (ts_src ts_tgt: Time.t) :=
  exists ts_src' ts_tgt',
    (<<TSSRC: Time.le ts_src ts_src'>>) /\
    (<<TSTGT: Time.le ts_tgt' ts_tgt>>) /\
    (<<SIM: sim_timestamp_exact f v ts_src' ts_tgt'>>) /\
    (<<CLOSED: Mapping.closed f v ts_src>>)
.

Record sim_timestamp_max (f: Mapping.t) (v: nat) (ts_src ts_tgt: Time.t): Prop :=
  sim_timestamp_max_intro {
      sim_timestamp_max_sim: sim_timestamp f v ts_src ts_tgt;
      sim_timestamp_max_max: forall ts (SIM: sim_timestamp f v ts ts_tgt),
          Time.le ts ts_src;
    }.

Lemma sim_timestamp_exact_sim f v ts_src ts_tgt
      (EXACT: sim_timestamp_exact f v ts_src ts_tgt)
      (CLOSED: Mapping.closed f v ts_src)
  :
    sim_timestamp f v ts_src ts_tgt.
Proof.
  exists ts_src, ts_tgt. splits; auto; try refl.
Qed.

Lemma sim_timestamp_exact_max f v ts_src ts_tgt
      (EXACT: sim_timestamp_exact f v ts_src ts_tgt)
      (CLOSED: Mapping.closed f v ts_src)
      (WF: Mapping.wf f)
  :
    sim_timestamp_max f v ts_src ts_tgt.
Proof.
  econs.
  { eapply sim_timestamp_exact_sim; eauto. }
  { i. unfold sim_timestamp, sim_timestamp_exact in *. des.
    etrans; eauto. erewrite <- Mapping.mapping_map_le; eauto. }
Qed.

Lemma sim_timestamp_mon_tgt f v ts_src ts_tgt0 ts_tgt1
      (SIM: sim_timestamp f v ts_src ts_tgt0)
      (TS: Time.le ts_tgt0 ts_tgt1)
  :
    sim_timestamp f v ts_src ts_tgt1.
Proof.
  unfold sim_timestamp in *. des.
  esplits; [..|eauto|]; auto. etrans; eauto.
Qed.

Lemma sim_timestamp_mon_ver f v0 v1 ts_src ts_tgt
      (SIM: sim_timestamp f v0 ts_src ts_tgt)
      (VER: v0 <= v1)
      (WF: Mapping.wf f)
      (VERWF: loc_version_wf f v1)
  :
    sim_timestamp f v1 ts_src ts_tgt.
Proof.
  unfold sim_timestamp in *. des.
  eapply sim_timestamp_exact_mon_ver in SIM; eauto. des.
  esplits; [..|eauto|]; eauto.
  eapply sim_closed_mon_ver; eauto.
Qed.

Lemma sim_timestamp_mon_mapping f0 f1 v ts_src ts_tgt
      (WF: Mapping.wf f0)
      (VERWF: loc_version_wf f0 v)
      (MAP: Mapping.le f0 f1)
  :
    sim_timestamp f0 v ts_src ts_tgt <-> sim_timestamp f1 v ts_src ts_tgt.
Proof.
  unfold sim_timestamp in *. split.
  { i. des. esplits; eauto.
    { erewrite <- sim_timestamp_exact_mon_mapping; eauto. }
    { erewrite <- sim_closed_mon_mapping; eauto. }
  }
  { i. des. esplits; eauto.
    { erewrite sim_timestamp_exact_mon_mapping; eauto. }
    { erewrite sim_closed_mon_mapping; eauto. }
  }
Qed.

Lemma sim_timestamp_max_mon_mapping f0 f1 v ts_src ts_tgt
      (WF: Mapping.wf f0)
      (VERWF: loc_version_wf f0 v)
      (MAP: Mapping.le f0 f1)
  :
    sim_timestamp_max f0 v ts_src ts_tgt <-> sim_timestamp_max f1 v ts_src ts_tgt.
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

Lemma sim_timestamp_bot f v ts
      (WF: Mapping.wf f)
      (VERWF: loc_version_wf f v)
  :
    sim_timestamp f v Time.bot ts.
Proof.
  hexploit Mapping.mapping_bot; eauto. i.
  eapply Mapping.mapping_incr with (v1:=v) in H; eauto.
  { des. exists fts1, Time.bot. esplits; ss; eauto.
    { eapply Time.bot_spec. }
    { eapply sim_closed_bot; eauto. }
  }
  { eapply le_0_n. }
Qed.

Lemma sim_timestamp_max_exists f v ts_tgt
      (WF: Mapping.wf f)
      (VER: loc_version_wf f v)
  :
    exists ts_src, <<MAX: sim_timestamp_max f v ts_src ts_tgt>>.
Proof.
  hexploit mapping_times_finite_exact; eauto. i. des.
  hexploit (@finite_greatest (fun ts => sim_timestamp f v ts ts_tgt) l). i. des.
  { exists to. red. econs; auto. i.
    eapply GREATEST; eauto. eapply H. red in SIM. des. eauto.
  }
  { exfalso. eapply EMPTY.
    { eapply H. eapply sim_closed_bot; eauto. }
    { eapply sim_timestamp_bot; eauto. }
  }
Qed.


Lemma sim_timestamp_exact_le f v
      ts_src0 ts_src1 ts_tgt0 ts_tgt1
      (SIM0: sim_timestamp_exact f v ts_src0 ts_tgt0)
      (SIM1: sim_timestamp_exact f v ts_src1 ts_tgt1)
      (TS: Time.le ts_tgt0 ts_tgt1)
      (WF: Mapping.wf f)
      (VERWF: loc_version_wf f v)
  :
    Time.le ts_src0 ts_src1.
Proof.
  unfold sim_timestamp_exact in *.
  erewrite <- Mapping.mapping_map_le; cycle 1; eauto.
Qed.

Lemma sim_timestamp_exact_lt f v
      ts_src0 ts_src1 ts_tgt0 ts_tgt1
      (SIM0: sim_timestamp_exact f v ts_src0 ts_tgt0)
      (SIM1: sim_timestamp_exact f v ts_src1 ts_tgt1)
      (TS: Time.lt ts_tgt0 ts_tgt1)
      (WF: Mapping.wf f)
      (VERWF: loc_version_wf f v)
  :
    Time.lt ts_src0 ts_src1.
Proof.
  unfold sim_timestamp in *. des.
  erewrite <- Mapping.mapping_map_lt; cycle 1; eauto.
Qed.

Lemma sim_timestamp_le f v
      ts_src0 ts_src1 ts_tgt0 ts_tgt1
      (SIM0: sim_timestamp f v ts_src0 ts_tgt0)
      (SIM1: sim_timestamp_exact f v ts_src1 ts_tgt1)
      (TS: Time.le ts_tgt0 ts_tgt1)
      (WF: Mapping.wf f)
      (VERWF: loc_version_wf f v)
  :
    Time.le ts_src0 ts_src1.
Proof.
  unfold sim_timestamp in *. des.
  transitivity ts_src'; eauto.
  erewrite <- Mapping.mapping_map_le; cycle 1; eauto.
Qed.

Lemma sim_timestamp_lt f v
      ts_src0 ts_src1 ts_tgt0 ts_tgt1
      (SIM0: sim_timestamp f v ts_src0 ts_tgt0)
      (SIM1: sim_timestamp_exact f v ts_src1 ts_tgt1)
      (TS: Time.lt ts_tgt0 ts_tgt1)
      (WF: Mapping.wf f)
      (VERWF: loc_version_wf f v)
  :
    Time.lt ts_src0 ts_src1.
Proof.
  unfold sim_timestamp in *. des.
  eapply TimeFacts.le_lt_lt; eauto.
  erewrite <- Mapping.mapping_map_lt; cycle 1; eauto.
  eapply TimeFacts.le_lt_lt; eauto.
Qed.

Lemma sim_timestamp_exact_join f v
      ts_src0 ts_src1 ts_tgt0 ts_tgt1
      (SIM0: sim_timestamp_exact f v ts_src0 ts_tgt0)
      (SIM1: sim_timestamp_exact f v ts_src1 ts_tgt1)
      (WF: Mapping.wf f)
      (VERWF: loc_version_wf f v)
  :
    sim_timestamp_exact f v (Time.join ts_src0 ts_src1) (Time.join ts_tgt0 ts_tgt1).
Proof.
  unfold Time.join in *. des_ifs.
  { erewrite <- Mapping.mapping_map_le in l; eauto. timetac. }
  { erewrite Mapping.mapping_map_le in l0; eauto. timetac. }
Qed.

Lemma sim_timestamp_join f v
      ts_src0 ts_src1 ts_tgt0 ts_tgt1
      (SIM0: sim_timestamp f v ts_src0 ts_tgt0)
      (SIM1: sim_timestamp f v ts_src1 ts_tgt1)
      (WF: Mapping.wf f)
      (VERWF: loc_version_wf f v)
  :
    sim_timestamp f v (Time.join ts_src0 ts_src1) (Time.join ts_tgt0 ts_tgt1).
Proof.
  unfold sim_timestamp in *. des.
  exists (Time.join ts_src'0 ts_src'), (Time.join ts_tgt'0 ts_tgt'). splits.
  { eapply time_join_mon; eauto. }
  { eapply time_join_mon; eauto. }
  { eapply sim_timestamp_exact_join; eauto. }
  { eapply sim_closed_join; eauto. }
Qed.

Lemma sim_timestamp_exact_meet f v
      ts_src0 ts_src1 ts_tgt0 ts_tgt1
      (SIM0: sim_timestamp_exact f v ts_src0 ts_tgt0)
      (SIM1: sim_timestamp_exact f v ts_src1 ts_tgt1)
      (WF: Mapping.wf f)
      (VERWF: loc_version_wf f v)
  :
    sim_timestamp_exact f v (Time.meet ts_src0 ts_src1) (Time.meet ts_tgt0 ts_tgt1).
Proof.
  unfold Time.meet in *. des_ifs.
  { erewrite <- Mapping.mapping_map_le in l; eauto. timetac. }
  { erewrite Mapping.mapping_map_le in l0; eauto. timetac. }
Qed.

Lemma sim_timestamp_exact_le_if f v
      ts_src0 ts_src1 ts_tgt0 ts_tgt1
      (SIM0: sim_timestamp_exact f v ts_src0 ts_tgt0)
      (SIM1: sim_timestamp_exact f v ts_src1 ts_tgt1)
      (TS: Time.le ts_src0 ts_src1)
      (WF: Mapping.wf f)
      (VERWF: loc_version_wf f v)
  :
    Time.le ts_tgt0 ts_tgt1.
Proof.
  unfold sim_timestamp_exact in *.
  erewrite Mapping.mapping_map_le; eauto.
Qed.

Lemma sim_timestamp_exact_lt_if f v
      ts_src0 ts_src1 ts_tgt0 ts_tgt1
      (SIM0: sim_timestamp_exact f v ts_src0 ts_tgt0)
      (SIM1: sim_timestamp_exact f v ts_src1 ts_tgt1)
      (TS: Time.lt ts_src0 ts_src1)
      (WF: Mapping.wf f)
      (VERWF: loc_version_wf f v)
  :
    Time.lt ts_tgt0 ts_tgt1.
Proof.
  unfold sim_timestamp_exact in *.
  erewrite Mapping.mapping_map_lt; eauto.
Qed.

Lemma sim_timestamp_exact_unique f v ts_src ts_tgt0 ts_tgt1
      (SIM0: sim_timestamp_exact f v ts_src ts_tgt0)
      (SIM1: sim_timestamp_exact f v ts_src ts_tgt1)
      (WF: Mapping.wf f)
      (VERWF: loc_version_wf f v)
  :
    ts_tgt0 = ts_tgt1.
Proof.
  eapply TimeFacts.antisym.
  { eapply sim_timestamp_exact_le_if; eauto. refl. }
  { eapply sim_timestamp_exact_le_if; eauto. refl. }
Qed.

Lemma sim_disjoint f v
      from_tgt0 from_src0 to_tgt0 to_src0
      from_tgt1 from_src1 to_tgt1 to_src1
      (WF: Mapping.wf f)
      (VER: loc_version_wf f v)
      (FROM0: sim_timestamp_exact f v from_src0 from_tgt0)
      (TO0: sim_timestamp_exact f v to_src0 to_tgt0)
      (FROM1: sim_timestamp_exact f v from_src1 from_tgt1)
      (TO1: sim_timestamp_exact f v to_src1 to_tgt1)
      (DISJOINT: Interval.disjoint (from_tgt0, to_tgt0) (from_tgt1, to_tgt1))
  :
    Interval.disjoint (from_src0, to_src0) (from_src1, to_src1).
Proof.
  apply NNPP. ii. revert DISJOINT.
  apply disjoint_equivalent. apply disjoint_equivalent in H. des.
  splits.
  - eapply sim_timestamp_exact_lt_if; eauto.
  - eapply sim_timestamp_exact_lt_if; eauto.
  - eapply sim_timestamp_exact_lt_if; eauto.
    + eapply sim_timestamp_exact_join; eauto.
    + eapply sim_timestamp_exact_meet; eauto.
Qed.


Definition sim_timemap (L: Loc.t -> Prop)
           (f: Mapping.ts) (v: version) (tm_src tm_tgt: TimeMap.t) :=
  forall l (LOC: L l), sim_timestamp (f l) (v l) (tm_src l) (tm_tgt l).

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
      (VER: version_le v0 v1)
      (WF: Mapping.wfs f)
      (VERWF: version_wf f v1)
  :
    sim_timemap L f v1 tm_src tm_tgt.
Proof.
  ii. eapply sim_timestamp_mon_ver; eauto.
Qed.

Lemma sim_timemap_mon_mapping L f0 f1 v tm_src tm_tgt
      (WF: Mapping.wfs f0)
      (VERWF: version_wf f0 v)
      (MAP: Mapping.les f0 f1)
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
      (WF: Mapping.wfs f)
      (VERWF: version_wf f v)
  :
    sim_timemap L f v (TimeMap.join tm_src0 tm_src1) (TimeMap.join tm_tgt0 tm_tgt1).
Proof.
  ii. eapply sim_timestamp_join; eauto.
Qed.

Lemma sim_timemap_bot l f v tm
      (WF: Mapping.wfs f)
      (VERWF: version_wf f v)
  :
    sim_timemap l f v TimeMap.bot tm.
Proof.
  ii. eapply sim_timestamp_bot; eauto.
Qed.

Lemma sim_timemap_singleton l (L: Loc.t -> Prop) f v
      ts_src ts_tgt
      (SIM: L l -> sim_timestamp (f l) (v l) ts_src ts_tgt)
      (WF: Mapping.wfs f)
      (VERWF: version_wf f v)
  :
    sim_timemap L f v (TimeMap.singleton l ts_src) (TimeMap.singleton l ts_tgt).
Proof.
  ii. unfold TimeMap.singleton.
  setoid_rewrite LocFun.add_spec. des_ifs; eauto.
  rewrite LocFun.init_spec.
  eapply sim_timestamp_bot; eauto.
Qed.

Definition sim_timemap_max (L: Loc.t -> Prop) (f: Mapping.ts) (v: version) (tm_src tm_tgt: TimeMap.t): Prop :=
  forall l (LOC: L l), sim_timestamp_max (f l) (v l) (tm_src l) (tm_tgt l).

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

Lemma sim_timemap_max_mon_mapping L f0 f1 v tm_src tm_tgt
      (WF: Mapping.wfs f0)
      (VERWF: version_wf f0 v)
      (MAP: Mapping.les f0 f1)
  :
    sim_timemap_max L f0 v tm_src tm_tgt <-> sim_timemap_max L f1 v tm_src tm_tgt.
Proof.
  split; ii.
  { erewrite <- sim_timestamp_max_mon_mapping; eauto. }
  { erewrite sim_timestamp_max_mon_mapping; eauto. }
Qed.

Lemma sim_timemap_max_exists L f v tm_tgt
      (WF: Mapping.wfs f)
      (VER: version_wf f v)
  :
    exists tm_src, <<MAX: sim_timemap_max L f v tm_src tm_tgt>>.
Proof.
  hexploit (choice (fun loc ts => sim_timestamp_max (f loc) (v loc) ts (tm_tgt loc))).
  { i. eapply sim_timestamp_max_exists; eauto. }
  i. des. exists f0. ii. eauto.
Qed.


Record sim_view (L: Loc.t -> Prop)
       (f: Mapping.ts) (v: version) (vw_src vw_tgt: View.t) :=
  sim_timemap_intro {
      sim_view_pln: sim_timemap L f v vw_src.(View.pln) vw_tgt.(View.pln);
      sim_view_rlx: sim_timemap L f v vw_src.(View.rlx) vw_tgt.(View.rlx);
    }.

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
      (VER: version_le v0 v1)
      (WF: Mapping.wfs f)
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

Lemma sim_view_mon_mapping L f0 f1 v vw_src vw_tgt
      (WF: Mapping.wfs f0)
      (VERWF: version_wf f0 v)
      (MAP: Mapping.les f0 f1)
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
      (WF: Mapping.wfs f)
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
      (WF: Mapping.wfs f)
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
      (SIM: L l -> sim_timestamp (f l) (v l) ts_src ts_tgt)
      (WF: Mapping.wfs f)
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
      (SIM: L l -> sim_timestamp (f l) (v l) ts_src ts_tgt)
      (WF: Mapping.wfs f)
      (VERWF: version_wf f v)
  :
    sim_view L f v (View.singleton_rw l ts_src) (View.singleton_rw l ts_tgt).
Proof.
  econs; ss.
  { eapply sim_timemap_bot; eauto. }
  { eapply sim_timemap_singleton; eauto. }
Qed.

Record sim_view_max (L: Loc.t -> Prop)
       (f: Mapping.ts) (v: version) (vw_src vw_tgt: View.t) :=
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

Lemma sim_view_max_mon_mapping L f0 f1 v vw_src vw_tgt
      (WF: Mapping.wfs f0)
      (VERWF: version_wf f0 v)
      (MAP: Mapping.les f0 f1)
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
      (WF: Mapping.wfs f)
      (VER: version_wf f v)
  :
    exists vw_src, <<MAX: sim_view_max L f v vw_src vw_tgt>>.
Proof.
  hexploit sim_timemap_max_exists; eauto. i. des.
  hexploit sim_timemap_max_exists; eauto. i. des.
  exists (View.mk tm_src tm_src0). econs; eauto.
Qed.



Variant sim_opt_view (L: Loc.t -> Prop)
        (f: Mapping.ts) (v: version):
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
      (VER: version_le v0 v1)
      (WF: Mapping.wfs f)
      (VERWF: version_wf f v1)
  :
    sim_opt_view L f v1 vw_src vw_tgt.
Proof.
  inv SIM; econs.
  eapply sim_view_mon_ver; eauto.
Qed.

Lemma sim_opt_view_mon_mapping L f0 f1 v vw_src vw_tgt
      (WF: Mapping.wfs f0)
      (VERWF: version_wf f0 v)
      (MAP: Mapping.les f0 f1)
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
      (WF: Mapping.wfs f)
      (VERWF: version_wf f v)
  :
    sim_view l f v (View.unwrap vw_src) (View.unwrap vw_tgt).
Proof.
  inv SIM; ss. eapply sim_view_bot; eauto.
Qed.

Variant sim_opt_view_max (L: Loc.t -> Prop)
        (f: Mapping.ts) (v: version):
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

Lemma sim_opt_view_max_mon_mapping L f0 f1 v vw_src vw_tgt
      (WF: Mapping.wfs f0)
      (VERWF: version_wf f0 v)
      (MAP: Mapping.les f0 f1)
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
      (WF: Mapping.wfs f)
      (VER: version_wf f v)
  :
    exists vw_src, <<MAX: sim_opt_view_max L f v vw_src vw_tgt>>.
Proof.
  destruct vw_tgt as [vw_tgt|].
  { hexploit sim_view_max_exists; eauto. i. des.
    eexists (Some _). econs; eauto. }
  { exists None. econs. }
Qed.



Definition top_time (top: Time.t) (f: Mapping.t): Prop :=
  forall ts fts
         (MAP: f.(Mapping.map) f.(Mapping.ver) ts = Some fts),
    Time.lt fts top.

Definition top_times (f: Mapping.ts) (tops: Loc.t -> option Time.t): Prop :=
  (<<MAX: forall loc ts fts top
                 (TOP: tops loc = Some top)
                 (MAP: (f loc).(Mapping.map) (f loc).(Mapping.ver) ts = Some fts),
      Time.lt fts top>>) /\
  (<<FIN: exists l, forall loc top (TOP: tops loc = Some top), List.In loc l>>)
.

Lemma top_time_exists f ts
      (WF: Mapping.wf f)
  :
    exists top, (<<TOP: top_time top f>>) /\ (<<TS: Time.lt ts top>>).
Proof.
  hexploit Mapping.map_finite; eauto. i. des.
  hexploit (@finite_greatest (fun _ => True) (List.map snd l)).
  i. des.
  { exists (Time.incr (Time.join ts to)). split.
    { ii. eapply TimeFacts.le_lt_lt; [|eapply Time.incr_spec].
      etrans; [|eapply Time.join_r]. eapply GREATEST; ss.
      eapply H in MAP. eapply List.in_map with (f:=snd) in MAP; auto. }
    { eapply TimeFacts.le_lt_lt; [|eapply Time.incr_spec]. eapply Time.join_l. }
  }
  { exists (Time.incr ts). split.
    { ii. eapply H in MAP. eapply List.in_map with (f:=snd) in MAP.
      exfalso. eapply EMPTY; eauto. }
    { eapply Time.incr_spec. }
  }
Qed.


Variant sim_message
        (f: Mapping.ts):
  forall (v: option version) (msg_src msg_tgt: Message.t), Prop :=
| sim_message_concrete
    v val_src val_tgt vw_src vw_tgt
    (VAL: Const.le val_tgt val_src)
    (SIM: sim_opt_view (fun _ => True) f v vw_src vw_tgt)
  :
    sim_message f (Some v) (Message.concrete val_src vw_src) (Message.concrete val_tgt vw_tgt)
| sim_message_undef
    v
  :
    sim_message f (Some v) Message.undef Message.undef
| sim_message_reserve
    v
  :
    sim_message f v Message.reserve Message.reserve
.

Lemma sim_message_mon_tgt f v msg_src msg_tgt0 msg_tgt1
      (SIM: sim_message f v msg_src msg_tgt0)
      (MSG: Message.le msg_tgt0 msg_tgt1)
  :
    sim_message f v msg_src msg_tgt1.
Proof.
  inv SIM; inv MSG; econs; eauto.
  { etrans; eauto. }
  { eapply sim_opt_view_mon_tgt; eauto. }
Qed.

Lemma sim_message_mon_ver f v0 v1 msg_src msg_tgt
      (SIM: sim_message f v0 msg_src msg_tgt)
      (VER: option_rel version_le v0 v1)
      (WF: Mapping.wfs f)
      (VERWF: opt_version_wf f v1)
  :
    sim_message f v1 msg_src msg_tgt.
Proof.
  inv SIM.
  { ss. des_ifs. econs; eauto. eapply sim_opt_view_mon_ver; eauto. }
  { ss. des_ifs. econs; eauto. }
  { econs. }
Qed.

Lemma sim_message_mon_mapping f0 f1 v msg_src msg_tgt
      (WF: Mapping.wfs f0)
      (VERWF: opt_version_wf f0 v)
      (MAP: Mapping.les f0 f1)
  :
    sim_message f0 v msg_src msg_tgt <-> sim_message f1 v msg_src msg_tgt.
Proof.
  split; i.
  { inv H; econs; auto. erewrite <- sim_opt_view_mon_mapping; eauto. }
  { inv H; econs; auto. erewrite sim_opt_view_mon_mapping; eauto. }
Qed.

Variant sim_message_max
        (f: Mapping.ts):
  forall (v: option version) (msg_src msg_tgt: Message.t), Prop :=
| sim_message_max_concrete
    v val vw_src vw_tgt
    (SIM: sim_opt_view_max (fun _ => True) f v vw_src vw_tgt)
  :
    sim_message_max f (Some v) (Message.concrete val vw_src) (Message.concrete val vw_tgt)
| sim_message_max_undef
    v
  :
    sim_message_max f (Some v) Message.undef Message.undef
| sim_message_max_reserve
    v
  :
    sim_message_max f v Message.reserve Message.reserve
.

Lemma sim_message_max_sim f v msg_src msg_tgt
      (SIM: sim_message_max f v msg_src msg_tgt)
  :
    sim_message f v msg_src msg_tgt.
Proof.
  inv SIM; econs; eauto; [refl|].
  eapply sim_opt_view_max_sim; eauto.
Qed.

Lemma sim_message_max_max f v msg_src msg_tgt
      msg
      (MAX: sim_message_max f v msg_src msg_tgt)
      (SIM: sim_message f v msg msg_tgt)
  :
    Message.le msg msg_src.
Proof.
  inv MAX; inv SIM.
  { econs; eauto. eapply sim_opt_view_max_max; eauto. }
  { econs. }
  { econs. }
Qed.

Lemma sim_message_max_mon_mapping f0 f1 v msg_src msg_tgt
      (WF: Mapping.wfs f0)
      (VERWF: opt_version_wf f0 v)
      (MAP: Mapping.les f0 f1)
  :
    sim_message_max f0 v msg_src msg_tgt <-> sim_message_max f1 v msg_src msg_tgt.
Proof.
  split; i.
  { inv H; econs.
    erewrite <- sim_opt_view_max_mon_mapping; eauto.
  }
  { inv H; econs.
    erewrite sim_opt_view_max_mon_mapping; eauto.
  }
Qed.

Lemma sim_message_max_exists f v msg_tgt
      (WF: Mapping.wfs f)
      (VER: forall (RESERVE: msg_tgt <> Message.reserve),
          exists v0, (<<EQ: v = Some v0>>) /\ (<<WF: version_wf f v0>>))
  :
    exists msg_src, <<MAX: sim_message_max f v msg_src msg_tgt>>.
Proof.
  destruct msg_tgt.
  { hexploit VER; ss. i. des; clarify.
    hexploit sim_opt_view_max_exists; eauto. i. des.
    esplits; eauto. econs; eauto.
  }
  { hexploit VER; ss. i. des; clarify.
    esplits. econs. }
  { esplits. econs. }
Qed.


Definition mapping_update (f: Mapping.t) ts fts: Mapping.t :=
  Mapping.mk
    (fun v => if PeanoNat.Nat.eq_dec v (S f.(Mapping.ver))
              then
                fun ts' =>
                  if (Time.eq_dec ts ts')
                  then Some fts
                  else f.(Mapping.map) f.(Mapping.ver) ts'
              else
                f.(Mapping.map) v)
    (S f.(Mapping.ver))
    (fun v => if PeanoNat.Nat.eq_dec v (S f.(Mapping.ver))
              then
                f.(Mapping.times) f.(Mapping.ver)
              else
                f.(Mapping.times) v)
.

Lemma mapping_update_old f ts fts ts0 fts0
      (MAP: sim_timestamp_exact f f.(Mapping.ver) fts0 ts0)
  :
    (sim_timestamp_exact (mapping_update f ts fts) (mapping_update f ts fts).(Mapping.ver) fts0 ts0) \/
    (ts = ts0).
Proof.
  unfold sim_timestamp_exact in *. ss. des_ifs; auto.
Qed.

Lemma mapping_update_new f ts fts
  :
    sim_timestamp_exact (mapping_update f ts fts) (mapping_update f ts fts).(Mapping.ver) fts ts.
Proof.
  unfold sim_timestamp_exact in *. ss. des_ifs; auto.
Qed.

Lemma mapping_update_closed_old f ts fts to
  :
    Mapping.closed f f.(Mapping.ver) to
    <->
    Mapping.closed (mapping_update f ts fts) (mapping_update f ts fts).(Mapping.ver) to.
Proof.
  ss. des_ifs.
Qed.

Lemma mapping_update_wf f ts fts
      (WF: Mapping.wf f)
      (INCR: forall fts' (MAP: sim_timestamp_exact f f.(Mapping.ver) fts' ts),
          Time.le fts' fts)
      (LEFT: forall ts' fts'
                    (LT: Time.lt ts' ts)
                    (MAP: sim_timestamp_exact f f.(Mapping.ver) fts' ts'),
          Time.lt fts' fts)
      (RIGHT: forall ts' fts'
                     (LT: Time.lt ts ts')
                     (MAP: sim_timestamp_exact f f.(Mapping.ver) fts' ts'),
          Time.lt fts fts')
  :
    Mapping.wf (mapping_update f ts fts).
Proof.
  econs.
  { i. destruct (PeanoNat.Nat.eq_dec v (S f.(Mapping.ver))).
    { clarify.
      hexploit (Mapping.map_finite WF f.(Mapping.ver)); eauto. i. des.
      exists ((ts, fts)::l). i.
      unfold mapping_update in *. ss. des_ifs.
      { auto. }
      { right. eapply H; eauto. }
    }
    { hexploit (Mapping.map_finite WF v); eauto. i. des.
      exists l. i.
      unfold mapping_update in *. ss. des_ifs.
      eapply H; eauto.
    }
  }
  { i. unfold mapping_update in *. ss. des_ifs.
    { ss. des; clarify. split; i; timetac. }
    { ss. des; clarify. split.
      { i. hexploit LEFT; eauto. }
      { i. destruct (Time.le_lt_dec ts1 ts0); auto. inv l; ss.
        eapply RIGHT in H0; eauto.
        exfalso. eapply Time.lt_strorder. etrans; eauto. }
    }
    { ss. des; clarify. split.
      { i. hexploit RIGHT; eauto. }
      { i. destruct (Time.le_lt_dec ts1 ts0); auto. inv l; ss.
        2:{ exfalso. eapply n; ss. }
        eapply LEFT in H0; eauto.
        exfalso. eapply Time.lt_strorder. etrans; eauto. }
    }
    { eapply Mapping.mapping_map_lt; eauto. }
    { eapply Mapping.mapping_map_lt; eauto. }
  }
  { i. ss. des_ifs.
    { ss. des; clarify. esplits; eauto. refl. }
    { ss. des; clarify. esplits; eauto.
      hexploit (@Mapping.mapping_incr _ WF v0 f.(Mapping.ver)); eauto.
      { lia. }
      i. des. transitivity fts1; eauto.
    }
    { ss. esplits; eauto. refl. }
    { hexploit (@Mapping.mapping_incr _ WF v0 f.(Mapping.ver)); eauto.
      lia.
    }
    { ss. des; clarify. exfalso. lia. }
    { exfalso. lia. }
    { eapply Mapping.mapping_incr; eauto. lia. }
  }
  { i. ss. des_ifs; try by lia.
    eapply Mapping.mapping_empty; eauto. lia. }
  { i. ss. eapply Mapping.mapping_bot; eauto. }
  { i. destruct (PeanoNat.Nat.eq_dec v (S f.(Mapping.ver))).
    { clarify.
      hexploit (Mapping.times_finite WF f.(Mapping.ver)); eauto. i. des.
      exists (ts::l). i.
      unfold mapping_update in *. ss. des_ifs. auto.
    }
    { hexploit (Mapping.times_finite WF v); eauto. i. des.
      exists l. i. ss. des_ifs. eapply H; eauto.
    }
  }
  { i. ss. des_ifs; eauto.
    { eapply Mapping.times_incr; [..|eauto]; eauto. lia. }
    { lia. }
    { eapply Mapping.times_incr; [..|eauto]; eauto. lia. }
  }
  { ii. ss. des_ifs.
    { lia. }
    eapply Mapping.times_empty; [..|eauto]; eauto. lia.
  }
  { i. ss. eapply Mapping.times_bot; eauto. }
Qed.

Lemma mapping_update_le f ts fts
  :
    Mapping.le f (mapping_update f ts fts).
Proof.
  red. splits.
  { ss. lia. }
  { i. ss. des_ifs. exfalso. lia. }
  { i. ss. des_ifs. exfalso. lia. }
Qed.

Lemma mapping_add f0 ts
      (WF: Mapping.wf f0)
  :
    exists f1 fts,
      (<<WF: Mapping.wf f1>>) /\
      (<<MAPLE: Mapping.le_strong f0 f1>>) /\
      (<<MAP: sim_timestamp_exact f1 f1.(Mapping.ver) fts ts>>) /\
      (<<MAPEQ: forall ts0 fts0 (MAP: sim_timestamp_exact f0 f0.(Mapping.ver) fts0 ts0),
          sim_timestamp_exact f1 f1.(Mapping.ver) fts0 ts0>>) /\
      (<<TIMES: forall to, Mapping.closed f0 f0.(Mapping.ver) to
                           <->
                           Mapping.closed f1 f1.(Mapping.ver) to>>)
.
Proof.
  destruct (classic (exists fts1, sim_timestamp_exact f0 f0.(Mapping.ver) fts1 ts)).
  { des. exists f0, fts1. splits; auto. refl. }
  hexploit Mapping.map_finite; eauto. i. des.
  hexploit (@finite_greatest (fun ts' => Time.le ts' ts /\ exists fts, Mapping.map f0 f0.(Mapping.ver) ts' = Some fts) (List.map fst l)). i. des.
  2:{
    exfalso. hexploit (Mapping.mapping_bot); eauto. i.
    eapply sim_timestamp_exact_mon_ver with (v1:=f0.(Mapping.ver)) in H1; eauto.
    { des. eapply EMPTY.
      { hexploit H; eauto. i.
        eapply List.in_map with (f:=fst) in H0; ss; eauto. }
      { split.
        { eapply Time.bot_spec. }
        { esplits; eauto. }
      }
    }
    { eapply le_0_n. }
    { eapply mapping_latest_wf_loc. }
  }
  inv SAT.
  2:{ inv H1. exfalso. eapply H; eauto. }
  hexploit (@finite_least (fun ts' => Time.le ts ts' /\ exists fts, Mapping.map f0 f0.(Mapping.ver) ts' = Some fts) (List.map fst l)). i. des.
  { inv SAT.
    2:{ inv H2. exfalso. eapply H; eauto. }
    assert (LT: Time.lt fts fts0).
    { erewrite <- Mapping.mapping_map_lt; cycle 2; try eassumption.
      transitivity ts; eauto. }
    exists (mapping_update f0 ts (Time.middle fts fts0)), (Time.middle fts fts0).
    splits.
    { eapply mapping_update_wf; eauto.
      { i. exfalso. eapply H; eauto. }
      { i. hexploit (GREATEST (fst (ts', fts'))).
        { eapply List.in_map; eauto. }
        { splits; eauto. ss. left. auto. }
        i. ss. eapply (@TimeFacts.le_lt_lt _ fts).
        { erewrite <- Mapping.mapping_map_le; cycle 2; eauto. }
        { eapply Time.middle_spec; eauto. }
      }
      { i. hexploit (LEAST (fst (ts', fts'))).
        { eapply List.in_map; eauto. }
        { splits; eauto. ss. left. auto. }
        i. ss. eapply (@TimeFacts.lt_le_lt _ fts0).
        { eapply Time.middle_spec; eauto. }
        { erewrite <- Mapping.mapping_map_le; cycle 2; eauto. }
      }
    }
    { red. splits.
      { ss. lia. }
      { i. ss. des_ifs. exfalso. lia. }
      { i. ss. des_ifs. lia. }
      { i. ss. des_ifs.
        { exfalso. eapply H; eauto. }
        { replace v with f0.(Mapping.ver) by lia. auto. }
      }
    }
    { unfold sim_timestamp_exact. ss. des_ifs. }
    { unfold sim_timestamp_exact. i. ss. des_ifs. ss. des; clarify.
      exfalso. eapply H; eauto. }
    { i. ss. des_ifs. }
  }
  { exists (mapping_update f0 ts (Time.incr fts)), (Time.incr fts).
    splits.
    { eapply mapping_update_wf; eauto.
      { i. exfalso. eapply H; eauto. }
      { i. hexploit (GREATEST (fst (ts', fts'))).
        { eapply List.in_map; eauto. }
        { splits; eauto. ss. left. auto. }
        i. ss. eapply (@TimeFacts.le_lt_lt _ fts).
        { erewrite <- Mapping.mapping_map_le; cycle 2; eauto. }
        { eapply Time.incr_spec; eauto. }
      }
      { i. exfalso. eapply EMPTY.
        { eapply List.in_map. eapply H0. eapply MAP. }
        { ss. splits; eauto. left. auto. }
      }
    }
    { red. splits.
      { ss. lia. }
      { i. ss. des_ifs. exfalso. lia. }
      { i. ss. des_ifs. lia. }
      { i. ss. des_ifs.
        { exfalso. eapply H; eauto. }
        { replace v with f0.(Mapping.ver) by lia. auto. }
      }
    }
    { unfold sim_timestamp_exact. ss. des_ifs. }
    { unfold sim_timestamp_exact. i. ss. des_ifs. ss. des; clarify.
      exfalso. eapply H; eauto. }
    { i. ss. des_ifs. }
  }
Qed.


Variant sim_promises
        (f: Mapping.ts)
        (vers: versions)
        (* (rmap: ReserveMap.t) *)
        (prom_src prom_tgt: Memory.t): Prop :=
| sim_promises_intro
    (MESSAGE: forall loc to from msg_tgt
                     (GET: Memory.get loc to prom_tgt = Some (from, msg_tgt)),
        exists fto ffrom msg_src,
          (<<FROM: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) ffrom from>>) /\
          (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) fto to>>) /\
          (<<GET: Memory.get loc fto prom_src = Some (ffrom, msg_src)>>) /\
          (<<MSG: sim_message_max f (vers loc to) msg_src msg_tgt>>))
    (SOUND: forall loc fto ffrom msg_src
                   (GET: Memory.get loc fto prom_src = Some (ffrom, msg_src)),
        exists to from msg_tgt,
          (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) fto to>>) /\
          (<<GET: Memory.get loc to prom_tgt = Some (from, msg_tgt)>>))
.

Lemma sim_promises_get f vers prom_src prom_tgt loc from_tgt to_tgt msg_tgt
      (SIM: sim_promises f vers prom_src prom_tgt)
      (GET: Memory.get loc to_tgt prom_tgt = Some (from_tgt, msg_tgt))
  :
    exists from_src to_src msg_src,
      (<<FROM: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) from_src from_tgt>>) /\
      (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src to_tgt>>) /\
      (<<GET: Memory.get loc to_src prom_src = Some (from_src, msg_src)>>) /\
      (<<MSG: sim_message_max f (vers loc to_tgt) msg_src msg_tgt>>).
Proof.
  inv SIM. hexploit MESSAGE; eauto. i. des. esplits; eauto.
Qed.

Lemma sim_promises_get_if f vers prom_src prom_tgt loc from_src to_src msg_src
      (SIM: sim_promises f vers prom_src prom_tgt)
      (GET: Memory.get loc to_src prom_src = Some (from_src, msg_src))
  :
    exists from_tgt to_tgt msg_tgt,
      (<<FROM: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) from_src from_tgt>>) /\
      (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src to_tgt>>) /\
      (<<GET: Memory.get loc to_tgt prom_tgt = Some (from_tgt, msg_tgt)>>) /\
      (<<MSG: sim_message_max f (vers loc to_tgt) msg_src msg_tgt>>).
Proof.
  inv SIM. hexploit SOUND; eauto. i. des.
  hexploit MESSAGE; eauto. i. des.
  hexploit sim_timestamp_exact_inject.
  { eapply TO. }
  { eapply TO0. }
  i. clarify. esplits; eauto.
Qed.

Lemma add_sim_promises f vers mem_tgt0 mem_tgt1 mem_src0 mem_src1
      loc from_tgt to_tgt from_src to_src msg_tgt msg_src
      (ADDTGT: Memory.add mem_tgt0 loc from_tgt to_tgt msg_tgt mem_tgt1)
      (PROMS: sim_promises f vers mem_src0 mem_tgt0)
      (ADDSRC: Memory.add mem_src0 loc from_src to_src msg_src mem_src1)
      (FROM: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) from_src from_tgt)
      (TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src to_tgt)
      (MSG: sim_message_max f (vers loc to_tgt) msg_src msg_tgt)
      (WF: Mapping.wfs f)
  :
    sim_promises f vers mem_src1 mem_tgt1.
Proof.
  econs.
  { i. erewrite Memory.add_o in GET; eauto. des_ifs.
    { ss. des; clarify. esplits; eauto.
      eapply Memory.add_get0; eauto. }
    { guardH o. hexploit sim_promises_get; eauto. i. des.
      esplits; eauto. erewrite Memory.add_o; eauto. des_ifs; eauto.
      exfalso. ss. des; clarify. unguard. des; ss.
      eapply o. eapply sim_timestamp_exact_unique; eauto.
      eapply mapping_latest_wf_loc.
    }
  }
  { i. erewrite Memory.add_o in GET; eauto. des_ifs.
    { ss. des; clarify. esplits; eauto.
      eapply Memory.add_get0; eauto. }
    { guardH o. hexploit sim_promises_get_if; eauto. i. des.
      esplits; eauto. eapply Memory.add_get1; eauto. }
  }
Qed.

Lemma remove_sim_promises f vers mem_tgt0 mem_tgt1 mem_src0 mem_src1
      loc from_tgt to_tgt from_src to_src msg_tgt msg_src
      (REMOVETGT: Memory.remove mem_tgt0 loc from_tgt to_tgt msg_tgt mem_tgt1)
      (PROMS: sim_promises f vers mem_src0 mem_tgt0)
      (REMOVESRC: Memory.remove mem_src0 loc from_src to_src msg_src mem_src1)
      (TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src to_tgt)
      (WF: Mapping.wfs f)
  :
    sim_promises f vers mem_src1 mem_tgt1.
Proof.
  econs.
  { i. erewrite Memory.remove_o in GET; eauto. des_ifs.
    guardH o. hexploit sim_promises_get; eauto. i. des.
    esplits; eauto. erewrite Memory.remove_o; eauto. des_ifs; eauto.
    exfalso. ss. des; clarify. unguard. des; ss.
    eapply o. eapply sim_timestamp_exact_unique; eauto.
    eapply mapping_latest_wf_loc.
  }
  { i. erewrite Memory.remove_o in GET; eauto. des_ifs.
    guardH o. hexploit sim_promises_get_if; eauto. i. des.
    esplits; eauto. erewrite <- GET0.
    erewrite Memory.remove_o; eauto. des_ifs. exfalso.
    unguard. ss. des; clarify.
    eapply o. eapply sim_timestamp_exact_inject; eauto.
  }
Qed.

Lemma lower_sim_promises f vers mem_tgt0 mem_tgt1 mem_src0 mem_src1
      loc from_tgt to_tgt from_src to_src
      msg_tgt0 msg_tgt1 msg_src0 msg_src1
      (LOWERTGT: Memory.lower mem_tgt0 loc from_tgt to_tgt msg_tgt0 msg_tgt1 mem_tgt1)
      (PROMS: sim_promises f vers mem_src0 mem_tgt0)
      (LOWERSRC: Memory.lower mem_src0 loc from_src to_src msg_src0 msg_src1 mem_src1)
      (TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src to_tgt)
      (MSG: sim_message_max f (vers loc to_tgt) msg_src1 msg_tgt1)
      (WF: Mapping.wfs f)
  :
    sim_promises f vers mem_src1 mem_tgt1.
Proof.
  pose proof (mapping_latest_wf_loc (f loc)) as VERWF.
  hexploit lower_succeed_wf; [eapply LOWERSRC|]. i. des.
  hexploit lower_succeed_wf; [eapply LOWERTGT|]. i. des.
  hexploit sim_promises_get_if; eauto. i. des.
  eapply sim_timestamp_exact_unique in TO; eauto. clarify.
  econs.
  { i. erewrite Memory.lower_o in GET0; eauto. des_ifs.
    { ss. des; clarify. esplits; eauto.
      eapply Memory.lower_get0; eauto. }
    { guardH o. hexploit sim_promises_get; eauto. i. des.
      esplits; eauto. erewrite Memory.lower_o; eauto.
      rewrite <- GET2. des_ifs. exfalso.
      unguard. ss. des; clarify.
      eapply o. eapply sim_timestamp_exact_unique; eauto.
    }
  }
  { i. erewrite Memory.lower_o in GET0; eauto. des_ifs.
    { ss. des; clarify. esplits; eauto.
      eapply Memory.lower_get0; eauto. }
    { guardH o. hexploit sim_promises_get_if; eauto. i. des.
      esplits; eauto. erewrite Memory.lower_o; eauto.
      rewrite <- GET2. des_ifs. exfalso.
      unguard. ss. des; clarify.
      eapply o. eapply sim_timestamp_exact_inject; eauto.
    }
  }
Qed.

Lemma split_sim_promises f vers mem_tgt0 mem_tgt1 mem_src0 mem_src1
      loc ts_tgt0 ts_tgt1 ts_tgt2 ts_src0 ts_src1 ts_src2
      msg_tgt0 msg_tgt1 msg_src0 msg_src1
      (SPLITTGT: Memory.split mem_tgt0 loc ts_tgt0 ts_tgt1 ts_tgt2 msg_tgt0 msg_tgt1 mem_tgt1)
      (MEM: sim_promises f vers mem_src0 mem_tgt0)
      (SPLITSRC: Memory.split mem_src0 loc ts_src0 ts_src1 ts_src2 msg_src0 msg_src1 mem_src1)
      (TS1: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) ts_src1 ts_tgt1)
      (TS2: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) ts_src2 ts_tgt2)
      (MSG: sim_message_max f (vers loc ts_tgt1) msg_src0 msg_tgt0)
      (RESERVETGT0: msg_tgt0 <> Message.reserve)
      (RESERVETGT1: msg_tgt1 <> Message.reserve)
      (RESERVESRC1: msg_src1 <> Message.reserve)
      (WF: Mapping.wfs f)
  :
    sim_promises f vers mem_src1 mem_tgt1.
Proof.
  pose proof (mapping_latest_wf_loc (f loc)) as VERWF.
  hexploit Memory.split_get0; [eapply SPLITTGT|]. i. des.
  hexploit Memory.split_get0; [eapply SPLITSRC|]. i. des. clarify.
  hexploit sim_promises_get_if; eauto. i. des.
  eapply sim_timestamp_exact_unique in TS2; eauto. clarify.
  econs.
  { i. erewrite Memory.split_o in GET0; eauto. des_ifs.
    { ss. des; clarify. esplits; eauto. }
    { ss. des; clarify. esplits; eauto. }
    { guardH o. guardH o0.
      hexploit sim_promises_get; [|eapply GET0|..]; eauto.
      i. des. esplits; eauto.
      erewrite Memory.split_o; eauto. rewrite <- GET8. des_ifs.
      { exfalso. unguard. ss. des; clarify. }
      { exfalso. unguard. ss. des; clarify.
        eapply o0. eapply sim_timestamp_exact_unique; eauto.   }
    }
  }
  { i. erewrite Memory.split_o in GET0; eauto. des_ifs.
    { ss. des; clarify. esplits; eauto. }
    { ss. des; clarify. esplits; eauto. }
    { guardH o. guardH o0.
      hexploit sim_promises_get_if; eauto. i. des.
      esplits; eauto. erewrite Memory.split_o; eauto.
      rewrite <- GET8. des_ifs.
      { exfalso. unguard. ss. des; clarify. }
      { exfalso. unguard. ss. des; clarify.
        eapply o0. eapply sim_timestamp_exact_inject; eauto. }
    }
  }
Qed.


Lemma sim_promises_cancel f vers mem_tgt0 mem_tgt1 mem_src0
      loc from_tgt to_tgt
      (REMOVETGT: Memory.remove mem_tgt0 loc from_tgt to_tgt Message.reserve mem_tgt1)
      (PROMS: sim_promises f vers mem_src0 mem_tgt0)
  :
    exists from_src to_src mem_src1,
      (<<FROM: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) from_src from_tgt>>) /\
      (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src to_tgt>>) /\
      (<<GET: Memory.get loc to_src mem_src0 = Some (from_src, Message.reserve)>>) /\
      (<<GET: Memory.remove mem_src0 loc from_src to_src Message.reserve mem_src1>>).
Proof.
  hexploit sim_promises_get; eauto.
  { eapply Memory.remove_get0; eauto. }
  i. des. inv MSG. hexploit Memory.remove_exists; eauto. i. des. esplits; eauto.
Qed.

Lemma sim_promises_split f vers mem_tgt0 mem_tgt1 mem_src0
      loc ts_tgt0 ts_tgt1 ts_tgt2 msg_tgt0 msg_tgt1 msg_src0 ts_src1
      (SPLITTGT: Memory.split mem_tgt0 loc ts_tgt0 ts_tgt1 ts_tgt2 msg_tgt0 msg_tgt1 mem_tgt1)
      (TS: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) ts_src1 ts_tgt1)
      (MSGWF: Message.wf msg_src0)
      (PROMS: sim_promises f vers mem_src0 mem_tgt0)
      (WF: Mapping.wfs f)
  :
    exists ts_src0 ts_src2 msg_src1 mem_src1,
      (<<TS0: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) ts_src0 ts_tgt0>>) /\
      (<<TS2: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) ts_src2 ts_tgt2>>) /\
      (<<MSG: sim_message_max f (vers loc ts_tgt2) msg_src1 msg_tgt1>>)/\
      (<<GET: Memory.get loc ts_src2 mem_src0 = Some (ts_src0, msg_src1)>>) /\
      (<<SPLIT: Memory.split mem_src0 loc ts_src0 ts_src1 ts_src2 msg_src0 msg_src1 mem_src1>>).
Proof.
  pose proof (mapping_latest_wf_loc (f loc)) as VERWF.
  hexploit split_succeed_wf; eauto. i. des.
  hexploit sim_promises_get; eauto. i. des.
  hexploit (@Memory.split_exists mem_src0 loc from_src ts_src1 to_src msg_src0 msg_src); eauto.
  { eapply sim_timestamp_exact_lt; [| |eapply TS12|..]; eauto. }
  { eapply sim_timestamp_exact_lt; [| |eapply TS23|..]; eauto. }
  i. des. esplits; eauto.
Qed.

Lemma sim_promises_lower f vers mem_tgt0 mem_tgt1 mem_src0
      loc from_tgt to_tgt to_src msg_tgt0 msg_tgt1 msg_src1
      (LOWERTGT: Memory.lower mem_tgt0 loc from_tgt to_tgt msg_tgt0 msg_tgt1 mem_tgt1)
      (TS: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src to_tgt)
      (MSGWF: Message.wf msg_src1)
      (MSG: sim_message f (vers loc to_tgt) msg_src1 msg_tgt1)
      (PROMS: sim_promises f vers mem_src0 mem_tgt0)
      (WF: Mapping.wfs f)
  :
    exists from_src msg_src0 mem_src1,
      (<<FROM: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) from_src from_tgt>>) /\
      (<<MSG: sim_message_max f (vers loc to_tgt) msg_src0 msg_tgt0>>)/\
      (<<GET: Memory.get loc to_src mem_src0 = Some (from_src, msg_src0)>>) /\
      (<<MSGLE: Message.le msg_src1 msg_src0>>) /\
      (<<LOWER: Memory.lower mem_src0 loc from_src to_src msg_src0 msg_src1 mem_src1>>).
Proof.
  pose proof (mapping_latest_wf_loc (f loc)) as VERWF.
  hexploit lower_succeed_wf; eauto. i. des.
  hexploit sim_promises_get; eauto. i. des.
  eapply sim_timestamp_exact_inject in TS; eauto. clarify.
  assert (MSGLE: Message.le msg_src1 msg_src).
  { eapply sim_message_max_max; eauto.
    eapply sim_message_mon_tgt; eauto. }
  hexploit (@Memory.lower_exists mem_src0 loc from_src to_src msg_src msg_src1); eauto.
  { eapply sim_timestamp_exact_lt; [| |eapply TS0|..]; eauto. }
  i. des. esplits; eauto.
Qed.


Variant no_reserve_covered loc ts mem: Prop :=
| no_reserve_covered_intro
    from to msg
    (GET: Memory.get loc to mem = Some (from, msg))
    (ITV: Interval.mem (from, to) ts)
    (RESERVE: msg <> Message.reserve)
.

Lemma no_reserve_coverd_covered loc ts mem
      (COVER: no_reserve_covered loc ts mem)
  :
    covered loc ts mem.
Proof.
  inv COVER. econs; eauto.
Qed.

Lemma add_no_reserve_covered mem0 mem1 loc from to msg loc' ts'
      (RESERVE: no_reserve_covered loc' ts' mem0)
      (ADD: Memory.add mem0 loc from to msg mem1)
  :
    no_reserve_covered loc' ts' mem1.
Proof.
  inv RESERVE. econs; eauto.
  eapply Memory.add_get1; eauto.
Qed.

Lemma split_no_reserve_covered mem0 mem1 loc ts0 ts1 ts2 msg0 msg1 loc' ts'
      (RESERVE: no_reserve_covered loc' ts' mem0)
      (SPLIT: Memory.split mem0 loc ts0 ts1 ts2 msg0 msg1 mem1)
      (MSG0: msg0 <> Message.reserve)
      (MSG1: msg1 <> Message.reserve)
  :
    no_reserve_covered loc' ts' mem1.
Proof.
  hexploit split_succeed_wf; eauto. i. des.
  hexploit Memory.split_get0; eauto. i. des.
  inv RESERVE.
  hexploit (Memory.split_o loc' to SPLIT); eauto. intros GETMEM1. des_ifs.
  { ss. des; clarify. }
  { inv ITV. ss. des; clarify. destruct (Time.le_lt_dec ts' ts1).
    { econs.
      { eapply GET1. }
      { econs; ss. }
      { ss. }
    }
    { econs.
      { eapply GETMEM1. }
      { econs; ss. }
      { ss. }
    }
  }
  { econs; eauto. rewrite GETMEM1. auto. }
Qed.

Lemma lower_no_reserve_covered mem0 mem1 loc from to msg0 msg1 loc' ts'
      (RESERVE: no_reserve_covered loc' ts' mem0)
      (LOWER: Memory.lower mem0 loc from to msg0 msg1 mem1)
      (MSG1: msg1 <> Message.reserve)
  :
    no_reserve_covered loc' ts' mem1.
Proof.
  hexploit lower_succeed_wf; eauto. i. des.
  hexploit Memory.lower_get0; eauto. i. des.
  inv RESERVE.
  hexploit (Memory.lower_o loc' to0 LOWER); eauto. intros GETMEM1. des_ifs.
  { ss. des; clarify. econs; eauto. }
  { econs; eauto. rewrite GETMEM1. auto. }
Qed.

Lemma remove_no_reserve_covered mem0 mem1 loc from to loc' ts'
      (RESERVE: no_reserve_covered loc' ts' mem0)
      (REMOVE: Memory.remove mem0 loc from to Message.reserve mem1)
  :
    no_reserve_covered loc' ts' mem1.
Proof.
  hexploit Memory.remove_get0; eauto. i. des.
  inv RESERVE. econs; eauto.
  erewrite Memory.remove_o; eauto. des_ifs.
  ss. des; clarify.
Qed.

Variant sim_memory
        (f: Mapping.ts)
        (vers: versions)
        (* (rmap: Loc.t -> Time.t -> option Time.t) *)
        (mem_src mem_tgt: Memory.t)
  (* (flag_tgt: Loc.t -> flag) *)
  : Prop :=
| sim_memory_intro
    (MESSAGE: forall loc to from msg_tgt
                     (GET: Memory.get loc to mem_tgt = Some (from, msg_tgt))
                     (RESERVE: msg_tgt <> Message.reserve),
        exists fto ffrom msg_src,
          (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) fto to>>) /\
          (<<GET: Memory.get loc fto mem_src = Some (ffrom, msg_src)>>) /\
          (<<MSG: sim_message f (vers loc to) msg_src msg_tgt>>))
    (SOUND: forall loc fto0 ffrom1 msg_src
                   (GET: Memory.get loc fto0 mem_src = Some (ffrom1, msg_src)),
        (exists fto1 ffrom0 to from,
            (<<TS0: Time.le ffrom0 ffrom1>>) /\
            (<<TS1: Time.le fto0 fto1>>) /\
            (<<FROM: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) ffrom0 from>>) /\
            (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) fto1 to>>) /\
            (<<COVERED: forall ts (ITV: Interval.mem (from, to) ts),
                no_reserve_covered loc ts mem_tgt>>)) \/
        (exists to from,
            (<<RESERVE: msg_src = Message.reserve>>) /\
            (<<FROM: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) ffrom1 from>>) /\
            (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) fto0 to>>) /\
            (<<GET: Memory.get loc to mem_tgt = Some (from, Message.reserve)>>)))
.

Lemma sim_memory_get f vers mem_src mem_tgt loc from_tgt to_tgt msg_tgt
      (SIM: sim_memory f vers mem_src mem_tgt)
      (GET: Memory.get loc to_tgt mem_tgt = Some (from_tgt, msg_tgt))
      (RESERVE: msg_tgt <> Message.reserve)
  :
    exists from_src to_src msg_src,
      (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src to_tgt>>) /\
      (<<GET: Memory.get loc to_src mem_src = Some (from_src, msg_src)>>) /\
      (<<MSG: sim_message f (vers loc to_tgt) msg_src msg_tgt>>).
Proof.
  inv SIM. hexploit MESSAGE; eauto. i. des. esplits; eauto.
Qed.

Lemma sim_memory_sound f vers mem_src mem_tgt loc fto0 ffrom1 msg_src
      (SIM: sim_memory f vers mem_src mem_tgt)
      (GET: Memory.get loc fto0 mem_src = Some (ffrom1, msg_src))
  :
    (exists fto1 ffrom0 to from,
        (<<TS0: Time.le ffrom0 ffrom1>>) /\
        (<<TS1: Time.le fto0 fto1>>) /\
        (<<FROM: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) ffrom0 from>>) /\
        (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) fto1 to>>) /\
        (<<COVERED: forall ts (ITV: Interval.mem (from, to) ts),
            no_reserve_covered loc ts mem_tgt>>)) \/
    (exists to from,
        (<<RESERVE: msg_src = Message.reserve>>) /\
        (<<FROM: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) ffrom1 from>>) /\
        (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) fto0 to>>) /\
        (<<GET: Memory.get loc to mem_tgt = Some (from, Message.reserve)>>)).
Proof.
  inv SIM. eauto.
Qed.

Lemma sim_memory_attach f vers mem_src mem_tgt loc ts_tgt ts_src
      (SIM: sim_memory f vers mem_src mem_tgt)
      (TS: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) ts_src ts_tgt)
      (ATTACH: forall to' msg'
                      (GET: Memory.get loc to' mem_tgt = Some (ts_tgt, msg')), False)
      (COVER: ~ covered loc ts_tgt mem_tgt)
      (NBOT: Time.lt Time.bot ts_tgt)
      (WF: Mapping.wfs f)
  :
    forall to' msg'
           (GET: Memory.get loc to' mem_src = Some (ts_src, msg')), False.
Proof.
  pose proof (mapping_latest_wf_loc (f loc)) as VERWF.
  ii. hexploit sim_memory_sound; eauto. i. des.
  { assert (FROMTO: Time.lt ts_src to').
    { hexploit memory_get_ts_strong; eauto. i. des; clarify.
      eapply sim_timestamp_lt in NBOT; eauto.
      eapply sim_timestamp_bot; eauto.
    }
    hexploit (@closed_point mem_tgt loc ts_tgt to); auto.
    { eapply sim_timestamp_exact_lt_if; eauto.
      eapply TimeFacts.lt_le_lt; eauto.
    }
    { i. eapply no_reserve_coverd_covered.
      eapply COVERED. inv ITV. econs; ss.
      eapply TimeFacts.le_lt_lt; eauto.
      eapply sim_timestamp_exact_le_if; eauto.
    }
    i. des. inv TS2.
    { eapply COVER. econs; eauto. econs; ss.
      left. auto. }
    { inv H. eapply ATTACH; eauto. }
  }
  { subst. eapply sim_timestamp_exact_unique in TS; eauto.
    i. subst. eapply ATTACH; eauto.
  }
Qed.

Lemma sim_memory_space f vers mem_src mem_tgt loc from_tgt to_tgt from_src to_src
      (SIM: sim_memory f vers mem_src mem_tgt)
      (FROM: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) from_src from_tgt)
      (TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src to_tgt)
      (TS: Time.lt from_tgt to_tgt)
      (DISJOINT: forall to2 from2 msg2
                        (GET: Memory.get loc to2 mem_tgt = Some (from2, msg2)),
          Interval.disjoint (from_tgt, to_tgt) (from2, to2))
      (WF: Mapping.wfs f)
  :
    forall to2 from2 msg2
           (GET: Memory.get loc to2 mem_src = Some (from2, msg2)),
      Interval.disjoint (from_src, to_src) (from2, to2).
Proof.
  pose proof (mapping_latest_wf_loc (f loc)) as VERWF.
  eapply covered_disjoint_get_disjoint. ii. inv H.
  hexploit sim_memory_sound; eauto. i. des.
  { assert (Interval.disjoint (from0, to0) (from_tgt, to_tgt)).
    { ii. eapply (get_disjoint_covered_disjoint DISJOINT); eauto.
      eapply no_reserve_coverd_covered; eauto. }
    eapply sim_disjoint in H; cycle 2; eauto. eapply (H ts); auto.
    inv ITV. econs; ss.
    { eapply TimeFacts.le_lt_lt; eauto. }
    { etrans; eauto. }
  }
  { subst. hexploit DISJOINT; eauto. i.
    eapply sim_disjoint in H; cycle 2; eauto.
  }
Qed.

Lemma add_sim_memory f vers mem_tgt0 mem_tgt1 mem_src0 mem_src1
      loc from_tgt to_tgt from_src to_src msg_tgt msg_src
      (ADDTGT: Memory.add mem_tgt0 loc from_tgt to_tgt msg_tgt mem_tgt1)
      (MEM: sim_memory f vers mem_src0 mem_tgt0)
      (ADDSRC: Memory.add mem_src0 loc from_src to_src msg_src mem_src1)
      (FROM: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) from_src from_tgt)
      (TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src to_tgt)
      (MSG: sim_message f (vers loc to_tgt) msg_src msg_tgt)
      (WF: Mapping.wfs f)
  :
    sim_memory f vers mem_src1 mem_tgt1.
Proof.
  econs.
  { i. erewrite Memory.add_o in GET; eauto. des_ifs.
    { ss. des; clarify. esplits; eauto.
      eapply Memory.add_get0; eauto. }
    { guardH o. hexploit sim_memory_get; eauto. i. des.
      esplits; eauto. erewrite Memory.add_o; eauto. des_ifs; eauto.
      exfalso. ss. des; clarify. unguard. des; ss.
      eapply o. eapply sim_timestamp_exact_unique; eauto.
      eapply mapping_latest_wf_loc.
    }
  }
  { i. erewrite Memory.add_o in GET; eauto. des_ifs.
    { ss. des; clarify. destruct (classic (msg_src0 = Message.reserve)).
      { right. subst. inv MSG. esplits; eauto.
        eapply Memory.add_get0; eauto. }
      { left. esplits.
        { refl. }
        { refl. }
        { eauto. }
        { eauto. }
        i. econs.
        { eapply Memory.add_get0; eauto. }
        { eauto. }
        { ii. subst. inv MSG; ss. }
      }
    }
    { guardH o. hexploit sim_memory_sound; eauto. i. des.
      { left. esplits; eauto. i. eapply COVERED in ITV.
        eapply add_no_reserve_covered; eauto.
      }
      { right. esplits; eauto.
        eapply Memory.add_get1; eauto.
      }
    }
  }
Qed.

Lemma remove_sim_memory f vers mem_tgt0 mem_tgt1 mem_src0 mem_src1
      loc from_tgt to_tgt from_src to_src
      (REMOVETGT: Memory.remove mem_tgt0 loc from_tgt to_tgt Message.reserve mem_tgt1)
      (MEM: sim_memory f vers mem_src0 mem_tgt0)
      (REMOVESRC: Memory.remove mem_src0 loc from_src to_src Message.reserve mem_src1)
      (TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src to_tgt)
      (WF: Mapping.wfs f)
  :
    sim_memory f vers mem_src1 mem_tgt1.
Proof.
  econs.
  { i. erewrite Memory.remove_o in GET; eauto. des_ifs.
    guardH o. hexploit sim_memory_get; eauto. i. des.
    esplits; eauto. erewrite Memory.remove_o; eauto. des_ifs; eauto.
    exfalso. ss. des; clarify. unguard. des; ss.
    eapply o. eapply sim_timestamp_exact_unique; eauto.
    eapply mapping_latest_wf_loc.
  }
  { i. erewrite Memory.remove_o in GET; eauto. des_ifs.
    guardH o. hexploit sim_memory_sound; eauto. i. des.
    { left. esplits; eauto. i.
      eapply remove_no_reserve_covered; eauto.
    }
    { right. esplits; eauto. clarify. ss.
      erewrite Memory.remove_o; eauto. des_ifs.
      ss. unguard. des; clarify. exfalso.
      eapply o. eapply sim_timestamp_exact_inject; eauto.
    }
  }
Qed.

Lemma split_sim_memory f vers mem_tgt0 mem_tgt1 mem_src0 mem_src1
      loc ts_tgt0 ts_tgt1 ts_tgt2 ts_src0 ts_src1 ts_src2
      msg_tgt0 msg_tgt1 msg_src0 msg_src1
      (SPLITTGT: Memory.split mem_tgt0 loc ts_tgt0 ts_tgt1 ts_tgt2 msg_tgt0 msg_tgt1 mem_tgt1)
      (MEM: sim_memory f vers mem_src0 mem_tgt0)
      (SPLITSRC: Memory.split mem_src0 loc ts_src0 ts_src1 ts_src2 msg_src0 msg_src1 mem_src1)
      (TS: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) ts_src1 ts_tgt1)
      (MSG: sim_message f (vers loc ts_tgt1) msg_src0 msg_tgt0)
      (RESERVETGT0: msg_tgt0 <> Message.reserve)
      (RESERVETGT1: msg_tgt1 <> Message.reserve)
      (RESERVESRC1: msg_src1 <> Message.reserve)
      (WF: Mapping.wfs f)
  :
    sim_memory f vers mem_src1 mem_tgt1.
Proof.
  hexploit Memory.split_get0; [eapply SPLITTGT|]. i. des.
  hexploit Memory.split_get0; [eapply SPLITSRC|]. i. des. clarify.
  econs.
  { i. erewrite Memory.split_o in GET7; eauto. des_ifs.
    { ss. des; clarify. esplits; eauto. }
    { ss. des; clarify.
      hexploit sim_memory_get; [|eapply GET0|..]; eauto. i. des.
      eapply Memory.split_get1 in GET7; eauto. des. esplits; eauto.
    }
    { guardH o. guardH o0.
      hexploit sim_memory_get; [|eapply GET7|..]; eauto. i. des.
      eapply Memory.split_get1 in GET8; eauto. des. esplits; eauto.
    }
  }
  { hexploit sim_memory_sound; [|eapply GET4|..]; eauto. i. des; clarify.
    i. erewrite Memory.split_o in GET7; eauto. des_ifs.
    { ss. des; clarify. left. esplits; eauto.
      { hexploit split_succeed_wf; [eapply SPLITSRC|]. i. des.
        etrans; eauto. left. auto. }
      { i. eapply split_no_reserve_covered; eauto. }
    }
    { ss. des; clarify. left. esplits; [| |eapply FROM|eapply TO|..].
      { hexploit split_succeed_wf; [eapply SPLITSRC|]. i. des.
        etrans; eauto. left. auto. }
      { hexploit split_succeed_wf; [eapply SPLITSRC|]. i. des. auto. }
      { i. eapply split_no_reserve_covered; eauto. }
    }
    { guardH o. guardH o0.
      hexploit sim_memory_sound; [|eapply GET7|..]; eauto. i. des.
      { left. esplits; eauto. i.
        eapply split_no_reserve_covered; eauto. }
      { right. esplits; eauto.
        erewrite Memory.split_o; eauto. des_ifs.
        { ss. des; clarify. }
        { ss. des; clarify. }
      }
    }
  }
Qed.

Lemma lower_sim_memory f vers mem_tgt0 mem_tgt1 mem_src0 mem_src1
      loc from_tgt to_tgt from_src to_src
      msg_tgt0 msg_tgt1 msg_src0 msg_src1
      (LOWERTGT: Memory.lower mem_tgt0 loc from_tgt to_tgt msg_tgt0 msg_tgt1 mem_tgt1)
      (MEM: sim_memory f vers mem_src0 mem_tgt0)
      (LOWERSRC: Memory.lower mem_src0 loc from_src to_src msg_src0 msg_src1 mem_src1)
      (TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src to_tgt)
      (MSG: sim_message f (vers loc to_tgt) msg_src1 msg_tgt1)
      (RESERVE: msg_tgt1 <> Message.reserve)
      (WF: Mapping.wfs f)
  :
    sim_memory f vers mem_src1 mem_tgt1.
Proof.
  econs.
  { i. erewrite Memory.lower_o in GET; eauto. des_ifs.
    { ss. des; clarify. esplits; eauto.
      eapply Memory.lower_get0; eauto.
    }
    { guardH o. hexploit sim_memory_get; eauto. i. des.
      esplits; eauto. erewrite Memory.lower_o; eauto. des_ifs; eauto.
      exfalso. ss. des; clarify.
      eapply sim_timestamp_exact_unique in TO; eauto.
      { subst. unguard. des; ss. }
      { eapply mapping_latest_wf_loc. }
    }
  }
  { i. erewrite Memory.lower_o in GET; eauto. des_ifs.
    { ss. des; clarify. hexploit sim_memory_sound.
      { eauto. }
      { eapply Memory.lower_get0 in LOWERSRC. des; eauto. }
      i. des.
      { left. esplits; eauto. i. eapply lower_no_reserve_covered; eauto. }
      { exfalso. apply lower_succeed_wf in LOWERSRC. des. subst.
        inv MSG_LE. inv MSG. ss.
      }
    }
    { guardH o. hexploit sim_memory_sound; eauto. i. des.
      { left. esplits; eauto. i. eapply lower_no_reserve_covered; eauto. }
      { right. esplits; eauto. erewrite Memory.lower_o; eauto. des_ifs.
        exfalso. ss. unguard. des; clarify.
        eapply o. eapply sim_timestamp_exact_inject; eauto.
      }
    }
  }
Qed.

Variant increased_undef_mem (f: Mapping.ts) (fin: Messages.t): Prop :=
| increased_undef_mem_intro
    (UNDEF: forall loc ts v0 v1 fts0 fts1
                   (SIM0: sim_timestamp_exact (f loc) v0 ts fts0)
                   (SIM1: sim_timestamp_exact (f loc) v1 ts fts1)
                   (TS: Time.lt fts0 fts1),
        exists from to,
          (<<MSG: fin loc from to Message.undef>>) /\
          (<<TS: Time.lt fts0 to>>))
.

Variant sim_closed_mem (f: Mapping.ts) (mem: Memory.t): Prop :=
| sim_closed_mem_intro
    (CLOSED: forall loc to (MAP: Mapping.closed (f loc) (f loc).(Mapping.ver) to),
        exists from val released, Memory.get loc to mem = Some (from, Message.concrete val released))
.

Lemma sim_timestamp_closed f v mem loc ts_src ts_tgt
      (CLOSED: sim_closed_mem f mem)
      (SIM: sim_timestamp (f loc) v ts_src ts_tgt)
      (WF: Mapping.wfs f)
      (VERWF: loc_version_wf (f loc) v)
  :
    exists from val released, Memory.get loc ts_src mem = Some (from, Message.concrete val released).
Proof.
  inv SIM. inv CLOSED. des. eapply CLOSED0; eauto.
  eapply sim_closed_mon_ver; eauto. eapply mapping_latest_wf_loc.
Qed.

Lemma sim_timemap_closed f v mem tm_src tm_tgt
      (CLOSED: sim_closed_mem f mem)
      (SIM: sim_timemap (fun _ => True) f v tm_src tm_tgt)
      (WF: Mapping.wfs f)
      (VERWF: version_wf f v)
  :
    Memory.closed_timemap tm_src mem.
Proof.
  ii. hexploit sim_timestamp_closed; eauto.
Qed.

Lemma sim_view_closed f v mem vw_src vw_tgt
      (CLOSED: sim_closed_mem f mem)
      (SIM: sim_view (fun _ => True) f v vw_src vw_tgt)
      (WF: Mapping.wfs f)
      (VERWF: version_wf f v)
  :
    Memory.closed_view vw_src mem.
Proof.
  econs.
  { eapply sim_timemap_closed; eauto. eapply SIM. }
  { eapply sim_timemap_closed; eauto. eapply SIM. }
Qed.

Lemma sim_opt_view_closed f v mem vw_src vw_tgt
      (CLOSED: sim_closed_mem f mem)
      (SIM: sim_opt_view (fun _ => True) f v vw_src vw_tgt)
      (WF: Mapping.wfs f)
      (VERWF: version_wf f v)
  :
    Memory.closed_opt_view vw_src mem.
Proof.
  inv SIM; econs. eapply sim_view_closed; eauto.
Qed.

Lemma sim_message_closed f v mem msg_src msg_tgt
      (CLOSED: sim_closed_mem f mem)
      (SIM: sim_message f v msg_src msg_tgt)
      (WF: Mapping.wfs f)
      (VERWF: opt_version_wf f v)
  :
    Memory.closed_message msg_src mem.
Proof.
  inv SIM; econs. eapply sim_opt_view_closed; eauto.
Qed.

Lemma sim_message_to f v msg_src msg_tgt loc ts_src ts_tgt
      (SIM: sim_message f v msg_src msg_tgt)
      (WF: Mapping.wfs f)
      (VERWF: opt_version_wf f v)
      (MSGTO: Memory.message_to msg_tgt loc ts_tgt)
      (TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) ts_src ts_tgt)
  :
    Memory.message_to msg_src loc ts_src.
Proof.
  inv SIM; econs. inv MSGTO.
  eapply sim_opt_view_unwrap in SIM0; eauto.
  hexploit (SIM0.(sim_view_rlx) loc); auto. i.
  eapply sim_timestamp_mon_ver in H.
  { eapply sim_timestamp_le; eauto. eapply mapping_latest_wf_loc; eauto. }
  { ss. eapply VERWF. }
  { eauto. }
  { eapply mapping_latest_wf_loc; eauto. }
Qed.

Lemma sim_message_wf f v msg_src msg_tgt
      (SIM: sim_message_max f v msg_src msg_tgt)
      (WF: Mapping.wfs f)
      (VERWF: opt_version_wf f v)
      (MSGWF: Message.wf msg_tgt)
  :
    Message.wf msg_src.
Proof.
  inv SIM; econs. inv MSGWF. inv SIM0; econs. inv WF0. ss.
  inv WF1. econs. eapply sim_timemap_max_max.
  { eapply SIM. }
  eapply sim_view_max_pln in SIM.
  eapply sim_timemap_mon_tgt.
  { eapply sim_timemap_max_sim. eauto. }
  { eauto. }
Qed.

Lemma sim_closed_mem_future f mem0 mem1
      (CLOSED: sim_closed_mem f mem0)
      (FUTURE: Memory.future_weak mem0 mem1)
  :
    sim_closed_mem f mem1.
Proof.
  inv CLOSED. econs. i. eapply CLOSED0 in MAP. des.
  eapply Memory.future_weak_get1 in MAP; eauto; ss.
  des. inv MSG_LE. eauto.
Qed.

Lemma sim_memory_add f vers mem_tgt0 mem_tgt1 mem_src0
      loc from_tgt to_tgt from_src to_src msg_tgt msg_src
      (ADDTGT: Memory.add mem_tgt0 loc from_tgt to_tgt msg_tgt mem_tgt1)
      (MEM: sim_memory f vers mem_src0 mem_tgt0)
      (MSG: sim_message f (vers loc to_tgt) msg_src msg_tgt)
      (FROM: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) from_src from_tgt)
      (TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src to_tgt)
      (WF: Mapping.wfs f)
      (MSGWF: Message.wf msg_src)
  :
    exists mem_src1,
      (<<ADD: Memory.add mem_src0 loc from_src to_src msg_src mem_src1>>) /\
      (<<ATTACH: forall (NOATTACH: forall to' msg (GET: Memory.get loc to' mem_tgt0 = Some (to_tgt, msg)), False)
                        to' msg
                        (GET: Memory.get loc to' mem_src0 = Some (to_src, msg)), False>>).
Proof.
  pose proof (mapping_latest_wf_loc (f loc)) as VERWF.
  hexploit add_succeed_wf; eauto. i. des.
  hexploit (@Memory.add_exists mem_src0 loc from_src to_src msg_src).
  { eapply sim_memory_space; eauto. }
  { eapply sim_timestamp_exact_lt; eauto. }
  { eauto. }
  i. des. esplits; eauto.
  i. eapply sim_memory_attach; eauto.
  { ii. inv H0. eapply DISJOINT; eauto. econs; ss. refl. }
  { eapply TimeFacts.le_lt_lt; eauto. eapply Time.bot_spec. }
Qed.


(* Variant sim_promises *)
(*         (f: Mapping.ts) *)
(*         (vers: versions) *)
(*         (* (rvers: Loc.t -> Time.t -> option Time.t) *) *)
(*         (prom_src prom_tgt: Memory.t): Prop := *)
(* | sim_promises_intro *)
(*     (MESSAGE: forall loc to from msg_tgt *)
(*                      (GET: Memory.get loc to prom_tgt = Some (from, msg_tgt)), *)
(*         exists fto ffrom msg_src, *)
(*           (<<FROM: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) ffrom from>>) /\ *)
(*           (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) fto to>>) /\ *)
(*           (<<GET: Memory.get loc fto prom_src = Some (ffrom, msg_src)>>) /\ *)
(*           (<<MSG: sim_message_max f (vers loc to) msg_src msg_tgt>>)) *)
(*     (SOUND: forall loc fto ffrom msg_src *)
(*                    (GET: Memory.get loc fto prom_src = Some (ffrom, msg_src)), *)
(*         exists to from msg_tgt, *)
(*           (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) fto to>>) /\ *)
(*           (<<GET: Memory.get loc to prom_tgt = Some (from, msg_tgt)>>)) *)
(* . *)

(* Variant sim_promises *)
(*         (f: Mapping.ts) *)
(*         (vers: versions) *)
(*         (rvers: Loc.t -> Time.t -> option Time.t) *)
(*         (prom_src prom_tgt: Memory.t): Prop := *)
(* | sim_promises_intro *)
(*     (MESSAGE: forall loc to from msg_tgt *)
(*                      (GET: Memory.get loc to prom_tgt = Some (from, msg_tgt)), *)
(*         exists fto ffrom msg_src, *)
(*           (<<FROM: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) ffrom from>>) /\ *)
(*           (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) fto to>>) /\ *)
(*           (<<GET: Memory.get loc fto prom_src = Some (ffrom, msg_src)>>) /\ *)
(*           (<<MSG: sim_message_max f (vers loc to) msg_src msg_tgt>>) /\ *)
(*           (<<RESERVE: msg_tgt = Message.reserve -> rvers loc to = Some (f loc).(Mapping.ver)>>)) *)
(*     (SOUND: forall loc fto ffrom msg_src *)
(*                    (GET: Memory.get loc fto prom_src = Some (ffrom, msg_src)), *)
(*         exists to from msg_tgt, *)
(*           (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) fto to>>) /\ *)
(*           (<<GET: Memory.get loc to prom_tgt = Some (from, msg_tgt)>>)) *)
(* . *)

(* Variant sim_memory *)
(*         (f: Mapping.ts) *)
(*         (vers: versions) *)
(*         (reserve_vers: Loc.t -> Time.t -> option Time.t) *)
(*         (mem_src mem_tgt: Memory.t) *)
(*         (flag_tgt: Loc.t -> flag) *)
(*   : Prop := *)
(* | sim_memory_intro *)
(*     (MESSAGE: forall loc to from msg_tgt *)
(*                      (GET: Memory.get loc to mem_tgt = Some (from, msg_tgt)) *)
(*                      (RESERVE: msg_tgt <> Message.reserve), *)
(*         exists fto ffrom msg_src, *)
(*           (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) fto to>>) /\ *)
(*           (<<GET: Memory.get loc fto mem_src = Some (ffrom, msg_src)>>) /\ *)
(*           (<<MSG: sim_message f (vers loc to) msg_src msg_tgt>>)) *)
(*     (SOUND: forall loc fto0 ffrom1 msg_src *)
(*                    (GET: Memory.get loc fto0 mem_src = Some (ffrom1, msg_src)) *)
(*                    (RESERVE: msg_src <> Message.reserve), *)
(*         exists fto1 ffrom0 to from msg_tgt, *)
(*           (<<TS0: Time.le ffrom0 ffrom1>>) /\ *)
(*           (<<TS1: Time.le fto0 fto1>>) /\ *)
(*           (<<FROM: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) ffrom0 from>>) /\ *)
(*           (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) fto1 to>>) /\ *)
(*           (<<GET: Memory.get loc to mem_tgt = Some (from, msg_tgt)>>) /\ *)
(*           (<<RESERVE: msg_tgt <> Message.reserve>>)) *)
(* . *)

(*     (SOUNDRESERVE: forall loc fto ffrom *)
(*                           (GET: Memory.get loc fto mem_src = Some (ffrom, Message.reserve)), *)
(*         exists v to from, *)
(*           (<<VER: reserve_vers loc to = Some v>>) /\ *)
(*           (<<TO: sim_timestamp_exact (f loc) v fto to>>) /\ *)
(*           (<<FROM: sim_timestamp_exact (f loc) v ffrom from>>) /\ *)
(*           (<<GET: Memory.get loc to mem_tgt = Some (from, Message.reserve)>>)) *)
(* . *)



(* Variant sim_promises_extern *)
(*         (f: Mapping.ts) *)
(*         (vers: versions) *)
(*         (reserve_vers: versions) *)
(*         (prom_src prom_tgt: Memory.t): Prop := *)
(* | sim_promises_extern_intro *)
(*     (MESSAGE: forall loc to from msg_tgt *)
(*                      (GET: Memory.get loc to prom_tgt = Some (from, msg_tgt)) *)
(*                      (RESERVE: msg_tgt <> Message.reserve), *)
(*         exists fto ffrom msg_src, *)
(*           (<<FROM: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) ffrom from>>) /\ *)
(*           (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) fto to>>) /\ *)
(*           (<<GET: Memory.get loc fto prom_src = Some (ffrom, msg_src)>>) /\ *)
(*           (<<MSG: sim_message_max f (vers loc to) msg_src msg_tgt>>)) *)
(*     (RESERVE: forall loc to from *)
(*                      (GET: Memory.get loc to prom_tgt = Some (from, Message.reserve)), *)
(*         exists v fto ffrom, *)
(*           (<<VER: reserve_vers loc to = Some v>>) /\ *)
(*           (<<FROM: sim_timestamp_exact (f loc) (v loc) ffrom from>>) /\ *)
(*           (<<TO: sim_timestamp_exact (f loc) (v loc) fto to>>) /\ *)
(*           (<<GET: Memory.get loc fto prom_src = Some (ffrom, Message.reserve)>>)) *)
(*     (SOUND: forall loc fto ffrom msg_src *)
(*                    (GET: Memory.get loc fto prom_src = Some (ffrom, msg_src)) *)
(*                    (RESERVE: msg_src <> Message.reserve), *)
(*         exists to from msg_tgt, *)
(*           (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) fto to>>) /\ *)
(*           (<<GET: Memory.get loc to prom_tgt = Some (from, msg_tgt)>>)) *)
(*     (SOUNDRESERVE: forall loc fto ffrom *)
(*                           (GET: Memory.get loc fto prom_src = Some (ffrom, Message.reserve)), *)
(*         exists v to from, *)
(*           (<<VER: reserve_vers loc to = Some v>>) /\ *)
(*           (<<TO: sim_timestamp_exact (f loc) (v loc) fto to>>) /\ *)
(*           (<<GET: Memory.get loc to prom_tgt = Some (from, Message.reserve)>>)) *)
(* . *)

(* Variant sim_memory *)
(*         (f: Mapping.ts) *)
(*         (vers: versions) *)
(*         (reserve_vers: reserve_versions) *)
(*         (mem_src mem_tgt: Memory.t) *)
(*         (flag_tgt: Loc.t -> flag) *)
(*   : Prop := *)
(* | sim_memory_intro *)
(*     (MESSAGE: forall loc to from msg_tgt *)
(*                      (GET: Memory.get loc to mem_tgt = Some (from, msg_tgt)) *)
(*                      (RESERVE: msg_tgt <> Message.reserve), *)
(*         exists fto ffrom msg_src, *)
(*           (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) fto to>>) /\ *)
(*           (<<GET: Memory.get loc fto mem_src = Some (ffrom, msg_src)>>) /\ *)
(*           (<<MSG: sim_message f (vers loc to) msg_src msg_tgt>>)) *)
(*     (SOUND: forall loc fto0 ffrom1 msg_src *)
(*                    (GET: Memory.get loc fto0 mem_src = Some (ffrom1, msg_src)) *)
(*                    (RESERVE: msg_src <> Message.reserve), *)
(*         exists fto1 ffrom0 to from msg_tgt, *)
(*           (<<TS0: Time.le ffrom0 ffrom1>>) /\ *)
(*           (<<TS1: Time.le fto0 fto1>>) /\ *)
(*           (<<FROM: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) ffrom0 from>>) /\ *)
(*           (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) fto1 to>>) /\ *)
(*           (<<GET: Memory.get loc to mem_tgt = Some (from, msg_tgt)>>) /\ *)
(*           (<<RESERVE: msg_tgt <> Message.reserve>>)) *)
(*     (SOUNDRESERVE: forall loc fto ffrom *)
(*                           (GET: Memory.get loc fto mem_src = Some (ffrom, Message.reserve)), *)
(*         exists v to from, *)
(*           (<<VER: reserve_vers loc to = Some v>>) /\ *)
(*           (<<TO: sim_timestamp_exact (f loc) v fto to>>) /\ *)
(*           (<<FROM: sim_timestamp_exact (f loc) v ffrom from>>) /\ *)
(*           (<<GET: Memory.get loc to mem_tgt = Some (from, Message.reserve)>>)) *)
(* . *)

(* Variant sim_memory *)
(*         (f: Mapping.ts) *)
(*         (vers: versions) *)
(*         (reserve_vers: reserve_versions) *)
(*         (mem_src mem_tgt: Memory.t) *)
(*         (flag_tgt: Loc.t -> flag) *)
(* : Prop := *)
(* | sim_memory_intro *)
(*     (MESSAGE: forall loc to from msg_tgt *)
(*                      (GET: Memory.get loc to mem_tgt = Some (from, msg_tgt)) *)
(*                      (RESERVE: msg_tgt <> Message.reserve), *)
(*         exists fto ffrom msg_src, *)
(*           (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) fto to>>) /\ *)
(*           (<<GET: Memory.get loc fto mem_src = Some (ffrom, msg_src)>>) /\ *)
(*           (<<MSG: sim_message f (vers loc to) msg_src msg_tgt>>)) *)
(*     (SOUND: forall loc fto0 ffrom1 msg_src *)
(*                    (GET: Memory.get loc fto0 mem_src = Some (ffrom1, msg_src)) *)
(*                    (RESERVE: msg_src <> Message.reserve), *)
(*         exists fto1 ffrom0 to from msg_tgt, *)
(*           (<<TS0: Time.le ffrom0 ffrom1>>) /\ *)
(*           (<<TS1: Time.le fto0 fto1>>) /\ *)
(*           (<<FROM: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) ffrom0 from>>) /\ *)
(*           (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) fto1 to>>) /\ *)
(*           (<<GET: Memory.get loc to mem_tgt = Some (from, msg_tgt)>>) /\ *)
(*           (<<RESERVE: msg_tgt <> Message.reserve>>)) *)
(*     (SOUNDRESERVE: forall loc fto ffrom *)
(*                           (GET: Memory.get loc fto mem_src = Some (ffrom, Message.reserve)), *)
(*         exists v to from, *)
(*           (<<VER: reserve_vers loc to = Some v>>) /\ *)
(*           (<<TO: sim_timestamp_exact (f loc) v fto to>>) /\ *)
(*           (<<FROM: sim_timestamp_exact (f loc) v ffrom from>>) /\ *)
(*           (<<GET: Memory.get loc to mem_tgt = Some (from, Message.reserve)>>)) *)
(* . *)

(* Variant sim_memory_cap *)
(*         (f: Mapping.ts) *)
(*         (vers: versions) *)
(*         (mem_src mem_tgt: Memory.t) *)
(*         (* (flag_tgt: Loc.t -> flag) *) *)
(*   : Prop := *)
(* | sim_memory_cap_intro *)
(*     (MESSAGE: forall loc to from msg_tgt *)
(*                      (GET: Memory.get loc to mem_tgt = Some (from, msg_tgt)) *)
(*                      (RESERVE: msg_tgt <> Message.reserve), *)
(*         exists fto ffrom msg_src, *)
(*           (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) fto to>>) /\ *)
(*           (<<GET: Memory.get loc fto mem_src = Some (ffrom, msg_src)>>) /\ *)
(*           (<<MSG: sim_message f (vers loc to) msg_src msg_tgt>>)) *)
(*     (SOUND: forall loc fto0 ffrom1 msg_src *)
(*                    (GET: Memory.get loc fto0 mem_src = Some (ffrom1, msg_src)), *)
(*         exists fto1 ffrom0 to from, *)
(*           (<<TS0: Time.le ffrom0 ffrom1>>) /\ *)
(*           (<<TS1: Time.le fto0 fto1>>) /\ *)
(*           (<<FROM: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) ffrom0 from>>) /\ *)
(*           (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) fto1 to>>) /\ *)
(*           (<<GET: forall ts (ITV: Interval.mem (from, to) ts), *)
(*               covered loc ts mem_tgt>>)) *)
(* . *)



(* Definition reserve_vers_wf (f: Mapping.ts) (vers: reserve_versions): Prop := *)
(*   forall loc to v (VER: vers loc to = Some v), *)
(*     (<<WF: loc_version_wf (f loc) v>>) /\ *)
(*     (<<UNIQUE: forall fto to' v' *)
(*                       (VER: vers loc to' = Some v') *)
(*                       (SIM0: sim_timestamp_exact (f loc) v' fto to') *)
(*                       (SIM0: sim_timestamp_exact (f loc) v' fto to'), *)
(*         v = v' /\ to' = to>>). *)


(* Module ReserveMap. *)
(*   Record t := *)
(*     mk { *)
(*         to_tgt: Loc.t -> Time.t -> option Time.t; *)
(*         to_src: Loc.t -> Time.t -> option Time.t; *)
(*       }. *)

(*   Definition wf (rmap: t): Prop := *)
(*     forall loc ts_src ts_tgt, *)
(*       (rmap.(to_tgt) loc ts_src = Some ts_tgt) *)
(*       <-> *)
(*       (rmap.(to_src) loc ts_tgt = Some ts_src). *)
(* End ReserveMap. *)


(* Lemma sim_attach f vers mem_tgt mem_src *)
(*       loc to_tgt to_src *)
(*       (WF: Mapping.wfs f) *)
(*       (MEM: sim_memory_cap f vers mem_src mem_tgt) *)
(*       (TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src to_tgt) *)
(*       (ATTACH: forall to' msg' *)
(*                       (GET: Memory.get loc to' mem_tgt = Some (to_tgt, msg')), False) *)
(*   : *)
(*     forall to' msg' *)
(*            (GET: Memory.get loc to' mem_src = Some (to_src, msg')), False. *)
(* Admitted. *)

(* Lemma sim_add_space f vers mem_tgt mem_src *)
(*       loc to_tgt to_src *)
(*       (WF: Mapping.wfs f) *)
(*       (MEM: sim_memory_cap f vers mem_src mem_tgt) *)
(*       (TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src to_tgt) *)
(*       (ATTACH: forall to' msg' *)
(*                       (GET: Memory.get loc to' mem_tgt = Some (to_tgt, msg')), False) *)
(*   : *)
(*     forall to' msg' *)
(*            (GET: Memory.get loc to' mem_src = Some (to_src, msg')), False. *)
(* Admitted. *)

(* Lemma sim_memory_map f vers mem_tgt0 mem_tgt1 mem_src0 *)
(*       loc from_tgt to_tgt from_src to_src msg_tgt msg_src *)
(*       (ADD: Memory.add mem_tgt0 loc from_tgt to_tgt msg_tgt mem_tgt1) *)
(*       (PROMS: sim_memory_cap f vers mem_src0 mem_tgt0) *)
(*       (FROM: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) from_src from_tgt) *)
(*       (TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src to_tgt) *)
(*       (MSG: sim_message f (vers loc to_tgt) msg_src msg_tgt) *)
(*   : *)
(*     exists mem_src1, *)
(*       (<<PROMS: sim_memory_cap f vers mem_src1 mem_tgt1>>) /\ *)
(*       (<<ADD: Memory.add mem_src0 loc from_src to_src msg_src mem_src1>>) *)
(* . *)
(* Proof. *)
(*   hexploit add_succeed_wf; eauto. i. des. *)
(*   hexploit (@Memory.add_exists mem_src0 loc from_src to_src msg_src). *)
(*   { admit. } *)

(* i. dup GET2. dup PROMS. inv PROMS. eapply ONLY in GET2; eauto. des. *)
(*     eapply disjoint_map; eauto. } *)
(*   { erewrite <- map_lt_non_collapsable; eauto. } *)
(*   { eapply msg_wf_map; eauto. } *)
(*   i. des. esplits; eauto. *)
(*   eapply add_promises_map0; eauto. *)
(* Qed. *)

(* Lemma sim_promises_map f vers mem_tgt0 mem_tgt1 mem_src0 *)
(*       loc from_tgt to_tgt from_src to_src msg_tgt msg_src *)
(*       (ADD: Memory.add mem_tgt0 loc from_tgt to_tgt msg_tgt mem_tgt1) *)
(*       (PROMS: sim_promises f vers mem_src0 mem_tgt0) *)
(*       (FROM: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) from_src from_tgt) *)
(*       (TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src to_tgt) *)
(*       (MSG: sim_message f (vers loc to_tgt) msg_src msg_tgt) *)
(*   : *)
(*     exists mem_src1, *)
(*       (<<PROMS: sim_promises f vers mem_src1 mem_tgt1>>) /\ *)
(*       (<<ADD: Memory.add mem_src0 loc from_src to_src msg_src mem_src1>>) *)
(* . *)
(* Proof. *)
(*   hexploit add_succeed_wf; eauto. i. des. *)
(*   hexploit (@Memory.add_exists mem_src0 loc from_src to_src msg_src). *)
(*   { i. dup GET2. dup PROMS. inv PROMS. eapply ONLY in GET2; eauto. des. *)
(*     eapply disjoint_map; eauto. } *)
(*   { erewrite <- map_lt_non_collapsable; eauto. } *)
(*   { eapply msg_wf_map; eauto. } *)
(*   i. des. esplits; eauto. *)
(*   eapply add_promises_map0; eauto. *)
(* Qed. *)

(* Lemma add_promises_map mem0 fmem0 loc from ffrom to fto msg fmsg mem1 *)
(*       (ADD: Memory.add mem0 loc from to msg mem1) *)
(*       (PROMS: sim_promises mem_src0 mem_tgt0) *)
(*       (FROM: sim_timestamp_exact (f loc) v from_src from_tgt) *)
(*       (TO: sim_timestamp_exact (f loc) v to_src to_tgt) *)
(*       (MSG: sim_message msg_map msg fmsg) *)
(*   : *)
(*     exists fmem1, *)
(*       (<<PROMS: sim_promises f mem1 fmem1>>) /\ *)
(*       (<<ADD: Memory.add fmem0 loc ffrom fto fmsg fmem1>>). *)
(* Proof. *)
(*   hexploit add_succeed_wf; eauto. i. des. *)
(*   hexploit (@Memory.add_exists fmem0 loc ffrom fto fmsg). *)
(*   { i. dup GET2. dup PROMS. inv PROMS. eapply ONLY in GET2; eauto. des. *)
(*     eapply disjoint_map; eauto. } *)
(*   { erewrite <- map_lt_non_collapsable; eauto. } *)
(*   { eapply msg_wf_map; eauto. } *)
(*   i. des. esplits; eauto. *)
(*   eapply add_promises_map0; eauto. *)
(* Qed. *)

(* Memory.promise *)
(* Lemma add_promises_map0 mem0 fmem0 loc from ffrom to fto msg fmsg mem1 fmem1 *)
(*       (ADD0: Memory.add mem0 loc from to msg mem1) *)
(*       (PROMS: promises_map mem0 fmem0) *)
(*       (FROM: f loc from ffrom) *)
(*       (TO: f loc to fto) *)
(*       (NCLPS: non_collapsable loc to) *)
(*       (MSG: msg_map msg fmsg) *)
(*       (ADD1: Memory.add fmem0 loc ffrom fto fmsg fmem1) *)
(*   : *)
(*     promises_map mem1 fmem1. *)
(* Proof. *)
(*   econs. *)
(*   - i. erewrite Memory.add_o in GET; eauto. des_ifs. *)
(*     + ss. des; clarify. *)
(*       esplits; eauto. *)
(*       eapply Memory.add_get0; eauto. *)
(*     + eapply msg_get_promises_map in GET; eauto. *)
(*       guardH o. des. unguard. *)
(*       esplits; eauto. *)
(*       eapply Memory.add_get1; eauto. *)
(*   - i. erewrite Memory.add_o in GET; eauto. des_ifs. *)
(*     + ss. des; clarify. exists to. esplits; eauto. *)
(*       eapply Memory.add_get0; eauto. *)
(*     + inv PROMS. eapply ONLY in GET; eauto. *)
(*       guardH o. des. esplits; eauto. *)
(*       eapply Memory.add_get1; eauto. *)
(* Qed. *)

(* Lemma add_promises_map0 mem0 fmem0 loc from ffrom to fto msg fmsg mem1 fmem1 *)
(*       (ADD0: Memory.add mem0 loc from to msg mem1) *)
(*       (PROMS: promises_map mem0 fmem0) *)
(*       (FROM: f loc from ffrom) *)
(*       (TO: f loc to fto) *)
(*       (NCLPS: non_collapsable loc to) *)
(*       (MSG: msg_map msg fmsg) *)
(*       (ADD1: Memory.add fmem0 loc ffrom fto fmsg fmem1) *)
(*   : *)
(*     promises_map mem1 fmem1. *)
(* Proof. *)
(*   econs. *)
(*   - i. erewrite Memory.add_o in GET; eauto. des_ifs. *)
(*     + ss. des; clarify. *)
(*       esplits; eauto. *)
(*       eapply Memory.add_get0; eauto. *)
(*     + eapply msg_get_promises_map in GET; eauto. *)
(*       guardH o. des. unguard. *)
(*       esplits; eauto. *)
(*       eapply Memory.add_get1; eauto. *)
(*   - i. erewrite Memory.add_o in GET; eauto. des_ifs. *)
(*     + ss. des; clarify. exists to. esplits; eauto. *)
(*       eapply Memory.add_get0; eauto. *)
(*     + inv PROMS. eapply ONLY in GET; eauto. *)
(*       guardH o. des. esplits; eauto. *)
(*       eapply Memory.add_get1; eauto. *)
(* Qed. *)


(* Lemma sim_memory_add *)
(*       mem_sr *)

(*       L *)

(* Lemma mapping_update_latest msgs f0 loc ts *)
(*       (WF: Mapping.wf f0) *)
(*   : *)
(*     exists f1 fts, *)
(*       (<<WF: Mapping.wf f1>>) /\ *)
(*       (<<MAPLE: mapping_messages_le msgs f0 f1>>) /\ *)
(*       (<<MAP: sim_timestamp_exact loc f1 f1.(Mapping.ver) fts ts>>) /\ *)
(*       (<<MAPEQ: forall loc0 ts0 fts0 (MAP: sim_timestamp_exact loc0 f0 f0.(Mapping.ver) fts0 ts0), *)
(*           sim_timestamp_exact loc0 f1 f1.(Mapping.ver) fts0 ts0>>). *)
(* Proof. *)


(* Variant sim_memory *)
(*         (f: Mapping.t) *)
(*         (vers: versions) *)
(*         (reserve_vers: versions) *)
(*         (mem_src mem_tgt: Memory.t) *)
(*         (flag_tgt: Loc.t -> flag): Prop := *)
(* | sim_memory_intro *)
(*     (MESSAGE: forall loc to from msg_tgt *)
(*                      (GET: Memory.get loc to prom_tgt = Some (from, msg_tgt)) *)
(*                      (RESERVE: msg_tgt <> Message.reserve), *)
(*         exists fto ffrom msg_src, *)
(*           (<<FROM: sim_timestamp_exact loc f f.(Mapping.ver) ffrom from>>) /\ *)
(*           (<<TO: sim_timestamp_exact loc f f.(Mapping.ver) fto to>>) /\ *)
(*           (<<GET: Memory.get loc fto prom_src = Some (ffrom, msg_src)>>) /\ *)
(*           (<<MSG: sim_message_max f (vers loc to) msg_src msg_tgt>>)) *)
(*     (RESERVE: forall loc to from *)
(*                      (GET: Memory.get loc to prom_tgt = Some (from, Message.reserve)), *)
(*         exists v fto ffrom, *)
(*           (<<VER: reserve_vers loc to = Some v>>) /\ *)
(*           (<<FROM: sim_timestamp_exact loc f v ffrom from>>) /\ *)
(*           (<<TO: sim_timestamp_exact loc f v fto to>>) /\ *)
(*           (<<GET: Memory.get loc fto prom_src = Some (ffrom, Message.reserve)>>)) *)
(*     (SOUND: forall loc fto ffrom msg_src *)
(*                    (GET: Memory.get loc fto prom_src = Some (ffrom, msg_src)) *)
(*                    (RESERVE: msg_src <> Message.reserve), *)
(*         exists to from msg_tgt, *)
(*           (<<TO: sim_timestamp_exact loc f f.(Mapping.ver) fto to>>) /\ *)
(*           (<<GET: Memory.get loc to prom_tgt = Some (from, msg_tgt)>>)) *)
(*     (SOUNDRESERVE: forall loc fto ffrom *)
(*                           (GET: Memory.get loc fto prom_src = Some (ffrom, Message.reserve)), *)
(*         exists v to from, *)
(*           (<<VER: reserve_vers loc to = Some v>>) /\ *)
(*           (<<TO: sim_timestamp_exact loc f v fto to>>) /\ *)
(*           (<<GET: Memory.get loc to prom_tgt = Some (from, Message.reserve)>>)) *)
(* . *)



(* Variant sim_promises_latest *)
(*         (f: Mapping.t) *)
(*         (vers: versions) *)
(*         (reserve_vers: versions) *)
(*         (prom_src prom_tgt: Memory.t) *)
(*         (flag_tgt: Loc.t -> flag): Prop := *)
(* | promises_map_latest_intro *)
(*     (MESSAGE: forall loc to from msg_tgt *)
(*                      (GET: Memory.get loc to prom_tgt = Some (from, msg_tgt)) *)
(*                      (RESERVE: msg_tgt <> Message.reserve), *)
(*         exists fto ffrom msg_src, *)
(*           (<<FROM: sim_timestamp_exact loc f f.(Mapping.ver) ffrom from>>) /\ *)
(*           (<<TO: sim_timestamp_exact loc f f.(Mapping.ver) fto to>>) /\ *)
(*           (<<GET: Memory.get loc fto prom_src = Some (ffrom, msg_src)>>) /\ *)
(*           (<<MSG: sim_message_max f (vers loc to) msg_src msg_tgt>>)) *)
(*     (RESERVE: forall loc to from *)
(*                      (GET: Memory.get loc to prom_tgt = Some (from, Message.reserve)), *)
(*         exists v fto ffrom, *)
(*           (<<VER: reserve_vers loc to = Some v>>) /\ *)
(*           (<<FROM: sim_timestamp_exact loc f v ffrom from>>) /\ *)
(*           (<<TO: sim_timestamp_exact loc f v fto to>>) /\ *)
(*           (<<GET: Memory.get loc fto prom_src = Some (ffrom, Message.reserve)>>)) *)
(*     (SOUND: forall loc fto ffrom msg_src *)
(*                    (GET: Memory.get loc fto prom_src = Some (ffrom, msg_src)), *)
(*         exists to from msg_tgt, *)
(*           (<<TO: sim_timestamp_exact loc f f.(Mapping.ver) fto to>>) /\ *)
(*           (<<GET: Memory.get loc to prom_tgt = Some (from, msg_tgt)>>)) *)
(*     (SOUNDRESERVE: forall loc fto ffrom *)
(*                           (GET: Memory.get loc fto prom_src = Some (ffrom, Message.reserve)), *)
(*         exists v to from, *)
(*           (<<VER: reserve_vers loc to = Some v>>) /\ *)
(*           (<<TO: sim_timestamp_exact loc f v fto to>>) /\ *)
(*           (<<UNIQUE: forall to' v' *)
(*                             (VER: reserve_vers loc to' = Some v') *)
(*                             (TO: sim_timestamp_exact loc f v' fto to'), *)
(*               v = v' /\ to' = to>>) /\ *)
(*           (<<GET: Memory.get loc to prom_tgt = Some (from, Message.reserve)>>)) *)
(* . *)


(* Variant sim_promises_map *)
(*         (f: Mapping.t) *)
(*         (vers: versions) *)
(*         (reserve_vers: versions) *)
(*         (prom_src prom_tgt: Memory.t) *)
(*         (flag_tgt: Loc.t -> flag): Prop := *)
(* | promises_map_latest_intro *)
(*     (MESSAGE: forall loc to from msg_tgt *)
(*                      (GET: Memory.get loc to prom_tgt = Some (from, msg_tgt)) *)
(*                      (RESERVE: msg_tgt <> Message.reserve), *)
(*         exists fto ffrom msg_src, *)
(*           (<<FROM: sim_timestamp_exact loc f f.(Mapping.ver) ffrom from>>) /\ *)
(*           (<<TO: sim_timestamp_exact loc f f.(Mapping.ver) fto to>>) /\ *)
(*           (<<GET: Memory.get loc fto prom_src = Some (ffrom, msg_src)>>) /\ *)
(*           (<<MSG: sim_message_max f (vers loc to) msg_src msg_tgt>>)) *)
(*     (RESERVE: forall loc to from *)
(*                      (GET: Memory.get loc to prom_tgt = Some (from, Message.reserve)), *)
(*         exists v fto ffrom, *)
(*           (<<VER: reserve_vers loc to = Some v>>) /\ *)
(*           (<<FROM: sim_timestamp_exact loc f v ffrom from>>) /\ *)
(*           (<<TO: sim_timestamp_exact loc f v fto to>>) /\ *)
(*           (<<GET: Memory.get loc fto prom_src = Some (ffrom, Message.reserve)>>)) *)
(*     (SOUND: forall loc fto ffrom msg_src *)
(*                    (GET: Memory.get loc fto prom_src = Some (ffrom, msg_src)), *)
(*         exists to from msg_tgt, *)
(*           (<<TO: sim_timestamp_exact loc f f.(Mapping.ver) fto to>>) /\ *)
(*           (<<GET: Memory.get loc to prom_tgt = Some (from, msg_tgt)>>)) *)
(*     (SOUNDRESERVE: forall loc fto ffrom *)
(*                           (GET: Memory.get loc fto prom_src = Some (ffrom, Message.reserve)), *)
(*         exists v to from, *)
(*           (<<VER: reserve_vers loc to = Some v>>) /\ *)
(*           (<<TO: sim_timestamp_exact loc f v fto to>>) /\ *)
(*           (<<UNIQUE: forall to' v' *)
(*                             (VER: reserve_vers loc to' = Some v') *)
(*                             (TO: sim_timestamp_exact loc f v' fto to'), *)
(*               v = v' /\ to' = to>>) /\ *)
(*           (<<GET: Memory.get loc to prom_tgt = Some (from, Message.reserve)>>)) *)
(* . *)

(* v fto ffrom, *)
(*           (<<VER: reserve_vers loc to = Some v>>) /\ *)
(*           (<<FROM: sim_timestamp_exact loc f v ffrom from>>) /\ *)
(*           (<<TO: sim_timestamp_exact loc f v fto to>>) /\ *)
(*           (<<GET: Memory.get loc fto prom_src = Some (ffrom, Message.reserve)>>)) *)
(* . *)

(*     (RESERVE: forall loc to from *)
(*                      (GET: Memory.get loc to prom_tgt = Some (from, Message.reserve)), *)
(*         exists v fto ffrom, *)
(*           (<<VER: vers loc to = Some v>>) /\ *)
(*           (<<FROM: sim_timestamp_exact loc f v ffrom from>>) /\ *)
(*           (<<TO: sim_timestamp_exact loc f v fto to>>) /\ *)
(*           (<<GET: Memory.get loc fto prom_src = Some (ffrom, Message.reserve)>>)) *)
(* . *)

(*     (SOUND: forall loc fto ffrom fmsg *)
(*                    (FLAGTRUE: flag_tgt loc = false) *)
(*                    (GET: Memory.get loc fto prom_src = Some (ffrom, fmsg)), *)
(*         exists to from msg, *)
(*           (<<FROM: sim_timemap_exact loc f v fto to>>) /\ *)
(*           (<<GET: Memory.get loc fto prom_src = Some (from, msg)>>)) *)
(* . *)



(*     (UNDEF: forall loc to from *)
(*                    (GET: Memory.get loc to prom_src = Some (from, Message.undef)), *)
(*         exists fto ffrom, *)
(*           (<<FROM: sim_timestamp_exact loc f f.(Mapping.ver) ffrom from>>) /\ *)
(*           (<<TO: sim_timestamp loc f f.(Mapping.ver) fto to>>) /\ *)
(*           (<<GET: Memory.get loc fto prom_src = Some (ffrom, Message.undef)>>)) *)
(* . *)

(*     (CONCRETE: forall loc to from val released *)
(*                       (FLAGFALSE: flag_src loc = false) *)
(*                       (GET: Memory.get loc to prom_tgt = Some (from, Message.concrete val released)), *)
(*         exists v fto ffrom freleased, *)
(*           (<<VER: vers loc to = Some v>>) /\ *)
(*           (<<FROM: time_map_latest loc ffrom from>>) /\ *)
(*           (<<TO: time_map_latest loc fto to>>) /\ *)
(*           (<<RELEASED: opt_view_map_ver v freleased released>>) /\ *)
(*           (<<GET: Memory.get loc fto prom_src = Some (ffrom, Message.concrete val freleased)>>)) *)
(*     (RESERVE: forall loc to from *)
(*                      (FLAGFALSE: flag_src loc = false) *)
(*                      (GET: Memory.get loc to prom_tgt = Some (from, Message.reserve)), *)
(*         exists fto ffrom, *)
(*           (<<FROM: time_map_latest loc ffrom from>>) /\ *)
(*           (<<TO: time_map_latest loc fto to>>) /\ *)
(*           (<<GET: Memory.get loc fto prom_src = Some (ffrom, Message.reserve)>>)) *)
(*     (SOUND: forall loc fto ffrom fmsg *)
(*                    (FLAGTRUE: flag_tgt loc = false) *)
(*                    (GET: Memory.get loc fto prom_src = Some (ffrom, fmsg)), *)
(*         exists to from msg, *)
(*           (<<TO: time_map_latest loc fto to>>) /\ *)
(*           (<<GET: Memory.get loc fto prom_src = Some (from, msg)>>)) *)




(*     (FLAGFALSE: forall loc (SRC: flag_src loc = false) (TGT: flag_tgt loc = true), *)
(*         exists to from, (<<GET: Memory.get loc to prom_tgt = Some (from, Message.undef)>>)) *)
(*     (FLAGTRUE: forall loc (SRC: flag_src loc = true), *)
(*         forall to, Memory.get loc to prom_src = None) *)
(*     (UNDEF: forall loc to from *)
(*                    (FLAGFALSE: flag_src loc = false) *)
(*                    (GET: Memory.get loc to prom_tgt = Some (from, Message.undef)), *)
(*         exists fto ffrom, *)
(*           (<<FROM: time_map_latest loc ffrom from>>) /\ *)
(*           (<<TO: time_map_latest loc fto to>>) /\ *)
(*           (<<GET: Memory.get loc fto prom_src = Some (ffrom, Message.undef)>>)) *)
(*     (CONCRETE: forall loc to from val released *)
(*                       (FLAGFALSE: flag_src loc = false) *)
(*                       (GET: Memory.get loc to prom_tgt = Some (from, Message.concrete val released)), *)
(*         exists v fto ffrom freleased, *)
(*           (<<VER: vers loc to = Some v>>) /\ *)
(*           (<<FROM: time_map_latest loc ffrom from>>) /\ *)
(*           (<<TO: time_map_latest loc fto to>>) /\ *)
(*           (<<RELEASED: opt_view_map_ver v freleased released>>) /\ *)
(*           (<<GET: Memory.get loc fto prom_src = Some (ffrom, Message.concrete val freleased)>>)) *)
(*     (RESERVE: forall loc to from *)
(*                      (FLAGFALSE: flag_src loc = false) *)
(*                      (GET: Memory.get loc to prom_tgt = Some (from, Message.reserve)), *)
(*         exists fto ffrom, *)
(*           (<<FROM: time_map_latest loc ffrom from>>) /\ *)
(*           (<<TO: time_map_latest loc fto to>>) /\ *)
(*           (<<GET: Memory.get loc fto prom_src = Some (ffrom, Message.reserve)>>)) *)
(*     (SOUND: forall loc fto ffrom fmsg *)
(*                    (FLAGTRUE: flag_tgt loc = false) *)
(*                    (GET: Memory.get loc fto prom_src = Some (ffrom, fmsg)), *)
(*         exists to from msg, *)
(*           (<<TO: time_map_latest loc fto to>>) /\ *)
(*           (<<GET: Memory.get loc fto prom_src = Some (from, msg)>>)) *)
(* . *)

(* Cell.t *)


(* Variant sim_promises_cell (latest: bool) (flag_src: bool) (flag_tgt: bool) *)
(*         (ts: Time.t) *)
(*         (vers: Time.t -> option version) (c_src c_tgt: Cell.t): Prop := *)
(* | sim_promises_cell_latest_true *)
(*     (BOT: forall (FLAG: flag_src) to, Cell.get to c_src = None) *)
(* | sim_promises_cell_latest_false *)
(*     (CONSISTENT: forall (FLAG: flag_tgt) to from msg *)
(*                         (MSG: msg <> Message.reserve) *)
(*                         (GET: Cell.get to c_src = Some (from, msg)), *)
(*         Time.lt ts to) *)
(*     (COMPLETE: *)
(*        sim_timemap *)

(* . *)

(* add *)
(* split *)
(* lower *)



(* Variant promises_map_latest (vers: versions) (prom_src prom_tgt: Memory.t) *)
(*         (flag_src: flags) (flag_tgt: flags): Prop := *)
(*   | promises_map_latest_intro *)
(*       (FLAGFALSE: forall loc (SRC: flag_src loc = false) (TGT: flag_tgt loc = true), *)
(*           exists to from, (<<GET: Memory.get loc to prom_tgt = Some (from, Message.undef)>>)) *)
(*       (FLAGTRUE: forall loc (SRC: flag_src loc = true), *)
(*           forall to, Memory.get loc to prom_src = None) *)
(*       (UNDEF: forall loc to from *)
(*                      (FLAGFALSE: flag_src loc = false) *)
(*                      (GET: Memory.get loc to prom_tgt = Some (from, Message.undef)), *)
(*           exists fto ffrom, *)
(*             (<<FROM: time_map_latest loc ffrom from>>) /\ *)
(*             (<<TO: time_map_latest loc fto to>>) /\ *)
(*             (<<GET: Memory.get loc fto prom_src = Some (ffrom, Message.undef)>>)) *)
(*       (CONCRETE: forall loc to from val released *)
(*                         (FLAGFALSE: flag_src loc = false) *)
(*                         (GET: Memory.get loc to prom_tgt = Some (from, Message.concrete val released)), *)
(*           exists v fto ffrom freleased, *)
(*             (<<VER: vers loc to = Some v>>) /\ *)
(*             (<<FROM: time_map_latest loc ffrom from>>) /\ *)
(*             (<<TO: time_map_latest loc fto to>>) /\ *)
(*             (<<RELEASED: opt_view_map_ver v freleased released>>) /\ *)
(*             (<<GET: Memory.get loc fto prom_src = Some (ffrom, Message.concrete val freleased)>>)) *)
(*       (RESERVE: forall loc to from *)
(*                        (FLAGFALSE: flag_src loc = false) *)
(*                        (GET: Memory.get loc to prom_tgt = Some (from, Message.reserve)), *)
(*           exists fto ffrom, *)
(*             (<<FROM: time_map_latest loc ffrom from>>) /\ *)
(*             (<<TO: time_map_latest loc fto to>>) /\ *)
(*             (<<GET: Memory.get loc fto prom_src = Some (ffrom, Message.reserve)>>)) *)
(*       (SOUND: forall loc fto ffrom fmsg *)
(*                      (FLAGTRUE: flag_tgt loc = false) *)
(*                      (GET: Memory.get loc fto prom_src = Some (ffrom, fmsg)), *)
(*           exists to from msg, *)
(*             (<<TO: time_map_latest loc fto to>>) /\ *)
(*             (<<GET: Memory.get loc fto prom_src = Some (from, msg)>>)) *)
(* . *)
(* Cell.t *)

(* Variant promises_map (vers: versions) (prom_src prom_tgt: Memory.t) *)
(*         (flag_src: flags) (flag_tgt: flags): Prop := *)
(*   | promises_map_intro *)
(*       (FLAGFALSE: forall loc (SRC: flag_src loc = false) (TGT: flag_tgt loc = true), *)
(*           exists to from, (<<GET: Memory.get loc to prom_tgt = Some (from, Message.undef)>>)) *)
(*       (FLAGTRUE: forall loc (SRC: flag_src loc = true), *)
(*           forall to, Memory.get loc to prom_src = None) *)
(*       (UNDEF: forall loc to from *)
(*                      (FLAGFALSE: flag_src loc = false) *)
(*                      (GET: Memory.get loc to prom_tgt = Some (from, Message.undef)), *)
(*           exists fto ffrom, *)
(*             (<<FROM: time_map_latest loc ffrom from>>) /\ *)
(*             (<<TO: time_map_latest loc fto to>>) /\ *)
(*             (<<GET: Memory.get loc fto prom_src = Some (ffrom, Message.undef)>>)) *)
(*       (CONCRETE: forall loc to from val released *)
(*                         (FLAGFALSE: flag_src loc = false) *)
(*                         (GET: Memory.get loc to prom_tgt = Some (from, Message.concrete val released)), *)
(*           exists v fto ffrom freleased, *)
(*             (<<VER: vers loc to = Some v>>) /\ *)
(*             (<<FROM: time_map_latest loc ffrom from>>) /\ *)
(*             (<<TO: time_map_latest loc fto to>>) /\ *)
(*             (<<RELEASED: opt_view_map_ver v freleased released>>) /\ *)
(*             (<<GET: Memory.get loc fto prom_src = Some (ffrom, Message.concrete val freleased)>>)) *)
(*       (RESERVE: forall loc to from *)
(*                        (FLAGFALSE: flag_src loc = false) *)
(*                        (GET: Memory.get loc to prom_tgt = Some (from, Message.reserve)), *)
(*           exists v fto ffrom, *)
(*             (<<FROM: time_map_ver v loc ffrom from>>) /\ *)
(*             (<<TO: time_map_ver v loc fto to>>) /\ *)
(*             (<<GET: Memory.get loc fto prom_src = Some (ffrom, Message.reserve)>>)) *)
(*       (SOUND: forall loc fto ffrom fmsg *)
(*                      (FLAGTRUE: flag_tgt loc = false) *)
(*                      (GET: Memory.get loc fto prom_src = Some (ffrom, fmsg)) *)
(*                      (NRESERVE: fmsg <> Message.reserve), *)
(*           exists to from msg, *)
(*             (<<TO: time_map_latest loc fto to>>) /\ *)
(*             (<<GET: Memory.get loc fto prom_src = Some (from, msg)>>)) *)
(*       (SOUNDRESERVE: forall loc fto ffrom *)
(*                             (FLAGTRUE: flag_tgt loc = false) *)
(*                             (GET: Memory.get loc fto prom_src = Some (ffrom, Message.reserve)), *)
(*           exists v to from, *)
(*             (<<FROM: time_map_ver v loc ffrom from>>) /\ *)
(*             (<<TO: time_map_ver v loc fto to>>) /\ *)
(*             (<<GET: Memory.get loc to prom_tgt = Some (from, Message.reserve)>>) /\ *)
(*             (<<UNIQUE: forall v' ffrom' fto' msg' *)
(*                               (MAP: time_map_ver v' loc fto' to) *)
(*                               (GET: Memory.get loc fto' prom_src = Some (ffrom', msg')), *)
(*                 fto' = fto>>)) *)
(* . *)

(* Variant sim_memory_latest *)
(*         (vers: versions) (mem_src mem_tgt: Memory.t): Prop := *)
(*   | sim_memory_latest_intro *)
(*       (CONCRETE: forall loc to from val released *)
(*                         (GET: Memory.get loc to mem_tgt = Some (from, Message.concrete val released)), *)
(*           exists fto ffrom rel, *)
(*             (<<TO: time_map_latest loc fto to>>) /\ *)
(*             (<<GET: Memory.get loc fto mem_src = Some (ffrom, Message.concrete val rel)>>) /\ *)
(*             (<<RELEASED: forall freleased (EQ: rel = Some freleased), *)
(*                 exists v vw, *)
(*                   (<<VER: vers loc to = Some v>>) /\ *)
(*                   (<<MAP: opt_view_map_ver v vw released>>) /\ *)
(*                   (<<VIEW: View.opt_le rel vw>>)>>)) *)
(*       (UNDEF: forall loc to from *)
(*                      (GET: Memory.get loc to mem_tgt = Some (from, Message.undef)), *)
(*           exists fto ffrom, *)
(*             (<<TO: time_map_latest loc fto to>>) /\ *)
(*             (<<GET: Memory.get loc fto mem_src = Some (ffrom, Message.undef)>>)) *)
(*       (COVER: forall loc fto ffrom msg *)
(*                      (GET: Memory.get loc fto mem_src = Some (ffrom, msg)), *)
(*           exists to from fto' ffrom', *)
(*             (<<TS: Time.le fto fto'>>) /\ *)
(*             (<<TS: Time.le ffrom' ffrom>>) /\ *)
(*             (<<FROM: time_map_latest loc ffrom' from>>) /\ *)
(*             (<<TO: time_map_latest loc fto' to>>) /\ *)
(*             (<<COVERED: forall ts (ITV: Interval.mem (from, to) ts), covered loc ts mem_tgt>>)) *)
(* . *)


(* Lemma mapping_add_exists f0 msgs loc ts *)
(*       (WF: Mapping.wf f) *)
(*       (MSG: forall msg (RESERVE: msg <> Message.reserve), ~ msgs loc ts msg) *)
(*   : *)
(*     exists f1 fts, *)
(*       (<<MAP: sim_timestamp_exact loc f1 f1.(Mapping.ver) ts fts>>) /\ *)
(*       (<<LE: mapping_messages_le msgs f0 f1>>) /\ *)
(*       (<<WF: Mapping.wf f>>). *)



(*       (WF: Mapping.wf f) *)
(*   : *)
(*     exists top, (<< *)




(* Lemma mapping_add_time f loc ts *)
(*       (TOP: top_time *)
(*       (WF: Mapping.wf f) *)


(* Definition max_times := Loc.t -> option Time.t. *)

(* Definition max_times_wf (f: Mapping.t) (top: max_times): Prop := *)
(*   (<<MAX: forall loc ts fts max *)
(*                  (TOP: top loc = Some max) *)
(*                  (MAP: f.(Mapping.map) f.(Mapping.ver) loc ts = Some fts), *)
(*       Time.lt fts max>>) /\ *)
(*   (<<FIN: exists l, forall loc max (TOP: top loc = Some max), List.In loc l>>) *)
(* . *)



(* Lemma max_times_mon (f0 f1: Mapping.t) *)
(*       (LE: *)



(*  (f: *)

















(*     sim_opt_view_max L f v (Some vw_src) (Some vw_tgt) *)
(* | sim_message_max_undef *)
(*   : *)
(*     sim_opt_view_max L f v None None *)
(* . *)

(* Lemma sim_opt_view_max_sim (L: Loc.t -> Prop) f v vw_src vw_tgt *)
(*       (SIM: sim_opt_view_max L f v vw_src vw_tgt) *)
(*   : *)
(*     sim_opt_view L f v vw_src vw_tgt. *)
(* Proof. *)
(*   inv SIM; econs. *)
(*   eapply sim_view_max_sim; eauto. *)
(* Qed. *)

(* Lemma sim_opt_view_max_max f v vw_src vw_tgt *)
(*       vw *)
(*       (MAX: sim_opt_view_max (fun _ => True) f v vw_src vw_tgt) *)
(*       (SIM: sim_opt_view (fun _ => True) f v vw vw_tgt) *)
(*   : *)
(*     View.opt_le vw vw_src. *)
(* Proof. *)
(*   inv MAX; inv SIM. *)
(*   { econs. eapply sim_view_max_max; eauto. } *)
(*   { econs. } *)
(*   { econs. } *)
(* Qed. *)

(* Lemma sim_opt_view_max_mon_mapping L msgs f0 f1 v vw_src vw_tgt *)
(*       (WF: Mapping.wf f0) *)
(*       (VERWF: version_wf f0 v) *)
(*       (MAP: mapping_messages_le msgs f0 f1) *)
(*   : *)
(*     sim_opt_view_max L f0 v vw_src vw_tgt <-> sim_opt_view_max L f1 v vw_src vw_tgt. *)
(* Proof. *)
(*   split; i. *)
(*   { inv H; econs. *)
(*     erewrite <- sim_view_max_mon_mapping; eauto. *)
(*   } *)
(*   { inv H; econs. *)
(*     erewrite sim_view_max_mon_mapping; eauto. *)
(*   } *)
(* Qed. *)

(* Lemma sim_opt_view_max_exists L f v vw_tgt *)
(*       (WF: Mapping.wf f) *)
(*       (VER: version_wf f v) *)
(*   : *)
(*     exists vw_src, <<MAX: sim_opt_view_max L f v vw_src vw_tgt>>. *)
(* Proof. *)
(*   destruct vw_tgt as [vw_tgt|]. *)
(*   { hexploit sim_view_max_exists; eauto. i. des. *)
(*     eexists (Some _). econs; eauto. } *)
(*   { exists None. econs. } *)
(* Qed. *)


(* Message.le *)



(*   exists ts_src' ts_tgt', *)
(*     (<<TSSRC: Time.le ts_src ts_src'>>) /\ *)
(*     (<<TSTGT: Time.le ts_tgt' ts_tgt>>) /\ *)
(*     (<<SIM: sim_timestamp_exact l f v ts_src' ts_tgt'>>). *)



(* Record world := *)
(*   mk_world { *)
(*       mapping:> Mapping.t; *)
(*       vers: versions; *)
(*     }. *)

(* Definition world_wf (w: world): Prop := *)
(*   (<<MAPPING: Mapping.wf w.(mapping)>>) /\ *)
(*   (<<VERS: forall loc to ver (VER: w.(vers) loc to = Some ver), *)
(*       ver <= w.(mapping).(Mapping.ver)>>) *)
(* . *)

(* Definition version_wf (w: world) (v: version): Prop := *)
(*   (<<VER: v <= w.(mapping).(Mapping.ver)>>). *)

(* Definition world_messages_le (msgs: Messages.t) (w0 w1: world): Prop := *)
(*   (<<VER: w0.(mapping).(Mapping.ver) <= w1.(mapping).(Mapping.ver)>>) /\ *)
(*   (<<TIME: forall v (VER: v <= w0.(mapping).(Mapping.ver)), *)
(*       w1.(mapping).(Mapping.map) v = w0.(mapping).(Mapping.map) v>>) /\ *)
(*   (<<VERSIONS: forall loc from to msg ts v *)
(*                       (MSG: msgs loc from to msg) *)
(*                       (RESERVE: msg <> Message.reserve) *)
(*                       (VER: w0.(vers) loc ts = Some v) *)
(*                       (TS: Time.lt ts to), *)
(*       w1.(vers) loc ts = Some v>>) /\ *)
(*   (<<MAPPING: forall loc from ffrom to msg *)
(*                      (MSG: msgs loc from to msg) *)
(*                      (RESERVE: msg <> Message.reserve) *)
(*                      (MAP: w0.(mapping).(Mapping.map) w0.(mapping).(Mapping.ver) loc from = Some ffrom), *)
(*       w1.(mapping).(Mapping.map) w1.(mapping).(Mapping.ver) loc from = Some ffrom>>) *)
(* . *)

(* Program Instance world_messages_le_PreOrder: forall msgs, PreOrder (world_messages_le msgs). *)
(* Next Obligation. *)
(* Proof. *)
(*   ii. red. splits; ss. *)
(* Qed. *)
(* Next Obligation. *)
(* Proof. *)
(*   ii. unfold world_messages_le in *. des. splits; eauto. *)
(*   { etrans; eauto. } *)
(*   { i. transitivity (y.(mapping).(Mapping.map) v); eauto. *)
(*     eapply TIME; eauto. etrans; eauto. } *)
(* Qed. *)

(* Lemma world_messages_le_mon: *)
(*   forall msgs0 msgs1 w0 w1 *)
(*          (LE: world_messages_le msgs1 w0 w1) *)
(*          (MSGS: msgs0 <4= msgs1), *)
(*     world_messages_le msgs0 w0 w1. *)
(* Proof. *)
(*   unfold world_messages_le in *. i. des. splits; eauto. *)
(* Qed. *)

(* Definition sim_timestamp_exact (l: Loc.t) (w: world) (v: version) (ts_src ts_tgt: Time.t) := *)
(*   w.(mapping).(Mapping.map) v l ts_tgt = Some ts_src. *)

(* Definition sim_timestamp (l: Loc.t) (w: world) (v: version) (ts_src ts_tgt: Time.t) := *)
(*   exists ts_src' ts_tgt', *)
(*     (<<TSSRC: Time.le ts_src ts_src'>>) /\ *)
(*     (<<TSTGT: Time.le ts_tgt' ts_tgt>>) /\ *)
(*     (<<SIM: sim_timestamp_exact l w v ts_src' ts_tgt'>>). *)

(* Lemma sim_timestamp_exact_sim l w v ts_src ts_tgt *)
(*       (EXACT: sim_timestamp_exact l w v ts_src ts_tgt) *)
(*   : *)
(*     sim_timestamp l w v ts_src ts_tgt. *)
(* Proof. *)
(*   exists ts_src, ts_tgt. splits; auto; try refl. *)
(* Qed. *)

(* Lemma sim_timestamp_mon l msgs w0 v0 w1 v1 ts_src0 ts_tgt0 ts_src1 ts_tgt1 *)
(*       (SIM: sim_timestamp l w0 v0 ts_src1 ts_tgt0) *)
(*       (WF0: version_wf w0 v0) *)
(*       (WF1: version_wf w1 v1) *)
(*       (VER: version_le v0 v1) *)
(*       (MAP: world_messages_le msgs w0 w1) *)
(*       (TSSRC: Time.le ts_src0 ts_src1) *)
(*       (TSTGT: Time.le ts_tgt0 ts_tgt1) *)
(*   : *)
(*     sim_timestamp l w1 v1 ts_src0 ts_tgt1. *)
(* Proof. *)


(* Admitted. *)

(* Definition sim_timemap (w: world) (v: version) (tm_src tm_tgt: TimeMap.t): Prop := *)
(*   forall l, sim_timestamp l w v (tm_src l) (tm_tgt l). *)

(* Lemma sim_timemap_mon msgs w0 v0 w1 v1 tm_src0 tm_tgt0 tm_src1 tm_tgt1 *)
(*       (SIM: sim_timemap w0 v0 tm_src1 tm_tgt0) *)
(*       (WF0: version_wf w0 v0) *)
(*       (WF1: version_wf w1 v1) *)
(*       (VER: version_le v0 v1) *)
(*       (MAP: world_messages_le msgs w0 w1) *)
(*       (TMSRC: TimeMap.le tm_src0 tm_src1) *)
(*       (TMTGT: TimeMap.le tm_tgt0 tm_tgt1) *)
(*   : *)
(*     sim_timemap w1 v1 tm_src0 tm_tgt1. *)
(* Proof. *)
(*   ii. eapply sim_timestamp_mon; eauto. *)
(* Qed. *)

(* Record sim_view (w: world) (v: version) (vw_src vw_tgt: View.t): Prop := *)
(*   mk_sim_view { *)
(*       sim_view_pln: sim_timemap w v vw_src.(View.pln) vw_tgt.(View.pln); *)
(*       sim_view_rlx: sim_timemap w v vw_src.(View.rlx) vw_tgt.(View.rlx); *)
(*     }. *)

(* Lemma sim_view_mon msgs w0 v0 w1 v1 vw_src0 vw_tgt0 vw_src1 vw_tgt1 *)
(*       (SIM: sim_view w0 v0 vw_src1 vw_tgt0) *)
(*       (WF0: version_wf w0 v0) *)
(*       (WF1: version_wf w1 v1) *)
(*       (VER: version_le v0 v1) *)
(*       (MAP: world_messages_le msgs w0 w1) *)
(*       (VWSRC: View.le vw_src0 vw_src1) *)
(*       (VWTGT: View.le vw_tgt0 vw_tgt1) *)
(*   : *)
(*     sim_view w1 v1 vw_src0 vw_tgt1. *)
(* Proof. *)
(*   econs. *)
(*   { eapply sim_timemap_mon. *)
(*     { eapply sim_view_pln; eauto. } *)
(*     all: eauto. *)
(*     { eapply VWSRC. } *)
(*     { eapply VWTGT. } *)
(*   } *)
(*   { eapply sim_timemap_mon. *)
(*     { eapply sim_view_rlx; eauto. } *)
(*     all: eauto. *)
(*     { eapply VWSRC. } *)
(*     { eapply VWTGT. } *)
(*   } *)
(* Qed. *)

(* Variant sim_opt_view (w: world) (v: version): forall (vw_src vw_tgt: option View.t), Prop := *)
(* | sim_opt_view_some *)
(*     vw_src vw_tgt *)
(*     (SIM: sim_view w v vw_src vw_tgt) *)
(*   : *)
(*     sim_opt_view w v (Some vw_src) (Some vw_tgt) *)
(* | sim_opt_view_none *)
(*     vw_tgt *)
(*   : *)
(*     sim_opt_view w v None vw_tgt *)
(* . *)

(* Lemma sim_opt_view_mon msgs w0 v0 w1 v1 vw_src0 vw_tgt0 vw_src1 vw_tgt1 *)
(*       (SIM: sim_opt_view w0 v0 vw_src1 vw_tgt0) *)
(*       (WF0: version_wf w0 v0) *)
(*       (WF1: version_wf w1 v1) *)
(*       (VER: version_le v0 v1) *)
(*       (MAP: world_messages_le msgs w0 w1) *)
(*       (VWSRC: View.opt_le vw_src0 vw_src1) *)
(*       (VWTGT: View.opt_le vw_tgt0 vw_tgt1) *)
(*   : *)
(*     sim_opt_view w1 v1 vw_src0 vw_tgt1. *)
(* Proof. *)
(*   inv SIM. *)
(*   { inv VWSRC; inv VWTGT; econs. *)
(*     eapply sim_view_mon; eauto. } *)
(*   { inv VWSRC; inv VWTGT; econs. } *)
(* Qed. *)

(* Variant sim_timemap_loc: forall *)
(*     (l: Loc.t) *)
(*     (w: world) (v: version) *)
(*     (ts_src: Time.t) (tm_src tm_tgt: TimeMap.t), Prop := *)
(* | sim_timemap_loc_intro *)
(*     l w v tm_src tm_tgt *)
(*     (SIM: forall l' (LOC: l' <> l), sim_timestamp l' w v (tm_src l') (tm_tgt l')) *)
(*   : *)
(*     sim_timemap_loc l w v (tm_src l) tm_src tm_tgt *)
(* . *)

(* Lemma sim_timemap_loc_sim l w v ts_src tm_src tm_tgt *)
(*       (SIM: sim_timemap_loc l w v ts_src tm_src tm_tgt) *)
(*       (TS: sim_timestamp l w v ts_src (tm_tgt l)) *)
(*   : *)
(*     sim_timemap w v tm_src tm_tgt. *)
(* Proof. *)
(*   inv SIM. ii. destruct (Loc.eq_dec l l0); clarify; auto. *)
(* Qed. *)

(* Record sim_view_loc (l: Loc.t) (w: world) (v: version) *)
(*        (ts_src: Time.t) (vw_src vw_tgt: View.t): Prop := *)
(*   mk_sim_view_loc { *)
(*       sim_view_loc_pln: sim_timemap_loc l w v ts_src vw_src.(View.pln) vw_tgt.(View.pln); *)
(*       sim_view_loc_rlx: sim_timemap_loc l w v ts_src vw_src.(View.rlx) vw_tgt.(View.rlx); *)
(*     }. *)

(* Lemma sim_view_loc_sim l w v ts_src vw_src vw_tgt *)
(*       (SIM: sim_view_loc l w v ts_src vw_src vw_tgt) *)
(*       (PLN: sim_timestamp l w v ts_src (vw_tgt.(View.pln) l)) *)
(*       (RLX: sim_timestamp l w v ts_src (vw_tgt.(View.rlx) l)) *)
(*   : *)
(*     sim_view w v vw_src vw_tgt. *)
(* Proof. *)
(*   econs. *)
(*   { eapply sim_timemap_loc_sim; eauto. eapply sim_view_loc_pln; eauto. } *)
(*   { eapply sim_timemap_loc_sim; eauto. eapply sim_view_loc_rlx; eauto. } *)
(* Qed. *)

(* Variant sim_opt_view_loc (l: Loc.t) (w: world) (v: version) (ts_src: Time.t) *)
(*   : forall (vw_src vw_tgt: option View.t), Prop := *)
(* | sim_opt_view_loc_some *)
(*     vw_src vw_tgt *)
(*     (SIM: sim_view_loc l w v ts_src vw_src vw_tgt) *)
(*   : *)
(*     sim_opt_view_loc l w v ts_src (Some vw_src) (Some vw_tgt) *)
(* | sim_opt_view_loc_none *)
(*     vw_tgt *)
(*   : *)
(*     sim_opt_view_loc l w v ts_src None vw_tgt *)
(* . *)

(* Lemma sim_opt_view_loc_sim l w v ts_src vw_src vw_tgt *)
(*       (SIM: sim_opt_view_loc l w v ts_src vw_src vw_tgt) *)
(*       (SOME: forall vw_tgt' (EQ: vw_tgt = Some vw_tgt'), *)
(*           (<<PLN: sim_timestamp l w v ts_src (vw_tgt'.(View.pln) l)>>) /\ *)
(*           (<<RLX: sim_timestamp l w v ts_src (vw_tgt'.(View.rlx) l)>>)) *)
(*   : *)
(*     sim_opt_view w v vw_src vw_tgt. *)
(* Proof. *)
(*   inv SIM; econs. eapply sim_view_loc_sim; eauto. *)
(*   { eapply SOME; eauto. } *)
(*   { eapply SOME; eauto. } *)
(* Qed. *)

(* Record sim_timestamp_max (l: Loc.t) (w: world) (v: version) (ts_src ts_tgt: Time.t): Prop := *)
(*   sim_timestamp_max_intro { *)
(*       sim_timestamp_max_sim: sim_timestamp l w v ts_src ts_tgt; *)
(*       sim_timestamp_max_max: forall ts (SIM: sim_timestamp l w v ts ts_tgt), *)
(*           Time.le ts ts_src; *)
(*     }. *)

(* Lemma sim_timestamp_max_exists l w v ts_tgt *)
(*   : *)
(*     exists ts_src, <<MAX: sim_timestamp_max l w v ts_src ts_tgt>>. *)
(* Admitted. *)

(* Variant sim_timemap_loc_max: forall *)
(*     (l: Loc.t) *)
(*     (w: world) (v: version) *)
(*     (ts_src: Time.t) (tm_src tm_tgt: TimeMap.t), Prop := *)
(* | sim_timemap_loc_max_intro *)
(*     l w v tm_src tm_tgt *)
(*     (SIM: forall l' (LOC: l' <> l), sim_timestamp_max l' w v (tm_src l') (tm_tgt l')) *)
(*   : *)
(*     sim_timemap_loc_max l w v (tm_src l) tm_src tm_tgt *)
(* . *)

(* Lemma sim_timemap_loc_max_sim l w v ts_src tm_src tm_tgt *)
(*       (SIM: sim_timemap_loc_max l w v ts_src tm_src tm_tgt) *)
(*   : *)
(*     sim_timemap_loc l w v ts_src tm_src tm_tgt. *)
(* Proof. *)
(*   inv SIM. econs. i. eapply sim_timestamp_max_sim; eauto. *)
(* Qed. *)

(* Lemma sim_timemap_loc_max_max l w v ts_src tm_src tm_tgt tm *)
(*       (MAX: sim_timemap_loc_max l w v ts_src tm_src tm_tgt) *)
(*       (SIM: sim_timemap_loc l w v ts_src tm tm_tgt) *)
(*   : *)
(*     TimeMap.le tm tm_src. *)
(* Proof. *)
(*   ii. inv SIM. inv MAX. destruct (Loc.eq_dec l loc); clarify. *)
(*   { rewrite H3. auto. refl. } *)
(*   { eapply sim_timestamp_max_max; eauto. } *)
(* Qed. *)

(* Lemma sim_timemap_loc_max_exists l w v ts_src tm_tgt *)
(*   : *)
(*     exists tm_src, <<MAX: sim_timemap_loc_max l w v ts_src tm_src tm_tgt>>. *)
(* Proof. *)
(*   hexploit (choice (fun l' ts => (l <> l' -> sim_timestamp_max l' w v ts (tm_tgt l')) /\ (l = l' -> ts = ts_src))). *)
(*   { i. destruct (Loc.eq_dec l x). *)
(*     { exists ts_src. splits; ss. } *)
(*     { hexploit sim_timestamp_max_exists. i. des. *)
(*       exists ts_src0. splits; ss. i. eapply MAX. } *)
(*   } *)
(*   i. des. exists f. subst. replace ts_src with (f l). *)
(*   { econs; eauto. i. specialize (H l'). des. auto. } *)
(*   { specialize (H l). des. auto. } *)
(* Qed. *)

(* Record sim_view_loc_max (l: Loc.t) (w: world) (v: version) *)
(*        (ts_src: Time.t) (vw_src vw_tgt: View.t): Prop := *)
(*   mk_sim_view_loc_max { *)
(*       sim_view_loc_max_pln: sim_timemap_loc_max l w v ts_src vw_src.(View.pln) vw_tgt.(View.pln); *)
(*       sim_view_loc_max_rlx: sim_timemap_loc_max l w v ts_src vw_src.(View.rlx) vw_tgt.(View.rlx); *)
(*     }. *)

(* Lemma sim_view_loc_max_sim l w v ts_src vw_src vw_tgt *)
(*       (SIM: sim_view_loc_max l w v ts_src vw_src vw_tgt) *)
(*   : *)
(*     sim_view_loc l w v ts_src vw_src vw_tgt. *)
(* Proof. *)
(*   inv SIM. econs. *)
(*   { eapply sim_timemap_loc_max_sim; eauto. } *)
(*   { eapply sim_timemap_loc_max_sim; eauto. } *)
(* Qed. *)

(* Lemma sim_view_loc_max_max l w v ts_src vw_src vw_tgt vw *)
(*       (MAX: sim_view_loc_max l w v ts_src vw_src vw_tgt) *)
(*       (SIM: sim_view_loc l w v ts_src vw vw_tgt) *)
(*   : *)
(*     View.le vw vw_src. *)
(* Proof. *)
(*   inv MAX. inv SIM. econs. *)
(*   { eapply sim_timemap_loc_max_max; eauto. } *)
(*   { eapply sim_timemap_loc_max_max; eauto. } *)
(* Qed. *)

(* Lemma sim_view_loc_max_exists l w v ts_src vw_tgt *)
(*   : *)
(*     exists vw_src, <<MAX: sim_view_loc_max l w v ts_src vw_src vw_tgt>>. *)
(* Proof. *)
(*   hexploit (@sim_timemap_loc_max_exists l w v ts_src vw_tgt.(View.pln)); auto. *)
(*   i. des. *)
(*   hexploit (@sim_timemap_loc_max_exists l w v ts_src vw_tgt.(View.rlx)); auto. *)
(*   i. des. *)
(*   exists (View.mk tm_src tm_src0). econs; eauto. *)
(* Qed. *)

(* Variant sim_opt_view_loc_max (l: Loc.t) (w: world) (v: version) (ts_src: Time.t) *)
(*   : forall (vw_src vw_tgt: option View.t), Prop := *)
(* | sim_opt_view_loc_max_some *)
(*     vw_src vw_tgt *)
(*     (SIM: sim_view_loc_max l w v ts_src vw_src vw_tgt) *)
(*   : *)
(*     sim_opt_view_loc_max l w v ts_src (Some vw_src) (Some vw_tgt) *)
(* | sim_opt_view_loc_max_none *)
(*   : *)
(*     sim_opt_view_loc_max l w v ts_src None None *)
(* . *)

(* Lemma sim_opt_view_loc_max_sim l w v ts_src vw_src vw_tgt *)
(*       (SIM: sim_opt_view_loc_max l w v ts_src vw_src vw_tgt) *)
(*   : *)
(*     sim_opt_view_loc l w v ts_src vw_src vw_tgt. *)
(* Proof. *)
(*   inv SIM; econs. eapply sim_view_loc_max_sim; eauto. *)
(* Qed. *)

(* Lemma sim_opt_view_loc_max_max l w v ts_src vw_src vw_tgt vw *)
(*       (MAX: sim_opt_view_loc_max l w v ts_src vw_src vw_tgt) *)
(*       (SIM: sim_opt_view_loc l w v ts_src vw vw_tgt) *)
(*   : *)
(*     View.opt_le vw vw_src. *)
(* Proof. *)
(*   inv MAX; inv SIM; econs. *)
(*   eapply sim_view_loc_max_max; eauto. *)
(* Qed. *)

(* Lemma sim_opt_view_loc_max_exists l w v ts_src vw_tgt *)
(*   : *)
(*     exists vw_src, <<MAX: sim_opt_view_loc_max l w v ts_src vw_src vw_tgt>>. *)
(* Proof. *)
(*   destruct vw_tgt as [vw|]. *)
(*   { hexploit sim_view_loc_max_exists. i. des. *)
(*     eexists (Some _). econs; eauto. } *)
(*   { exists None. econs. } *)
(* Qed. *)

(* Local.write_step *)

(* Definition flags := Loc.t -> bool. *)
(* Definition flags_bot: flags := fun _ => false. *)

(* Definition flags_le (f_tgt f_src: flags): Prop := *)
(*   forall loc, (f_tgt loc) -> (f_src loc). *)

(* Definition update_flags (f: flags) (l: Loc.t) (b: bool): flags := *)
(*   fun l' => if (Loc.eq_dec l' l) then b else f l'. *)


(* Definition sim_timemap (f_src: flags) (b: bool) (w: world) (sc_src sc_tgt: TimeMap.t): Prop. Admitted. *)

(* Definition sim_memory (f_src: flags) (b: bool) (w: world) (mem_src: Memory.t) (mem_tgt: Memory.t): Prop. Admitted. *)


(* Definition value_map := Loc.t -> option (Const.t * Const.t). *)

(* Definition value_map_le (vm0 vm1: value_map): Prop := *)
(*   forall loc, *)
(*     match (vm0 loc), (vm1 loc) with *)
(*     | _, None => True *)
(*     | Some vs0, Some vs1 => vs0 = vs1 *)
(*     | _, _ => False *)
(*     end. *)

(* Definition update_value_map (vm: value_map) (l: Loc.t) (vs: option (Const.t * Const.t)) := *)
(*   fun l' => if (Loc.eq_dec l' l) then vs else vm l'. *)


(* Definition sim_local (vm: value_map) (f_src: flags) (f_tgt: flags) *)
(*            (b: bool) (w: world) *)
(*            (lc_src: Local.t) (lc_tgt: Local.t) *)
(*            (mem_src: Memory.t) (mem_tgt: Memory.t) *)
(*            (sc_src: TimeMap.t) (sc_tgt: TimeMap.t): Prop. Admitted. *)


(* Lemma sim_local_lower vm flags_bot f_tgt w lc_src lc_tgt0 lc_tgt1 mem_src *)
(*       mem_tgt0 mem_tgt1 sc_src sc_tgt0 sc_tgt1 *)
(*       (SIM: sim_local vm flags_bot f_tgt false w lc_src lc_tgt0 mem_src mem_tgt0 sc_src sc_tgt0) *)
(*       (LOCAL: lower_local lc_tgt0 lc_tgt1) *)
(*       (MEM: lower_memory mem_tgt0 mem_tgt1) *)
(*       (SC: TimeMap.le sc_tgt0 sc_tgt1) *)
(*   : *)
(*     sim_local vm flags_bot f_tgt false w lc_src lc_tgt1 mem_src mem_tgt1 sc_src sc_tgt1. *)
(* Admitted. *)

(* Lemma sim_update_latest lang_src *)
(*       (st_src: lang_src.(Language.state)) *)
(*       vm f_tgt w0 lc_src lc_tgt mem_src mem_tgt sc_src sc_tgt *)
(*       (LOCAL: sim_local vm flags_bot f_tgt true w0 lc_src lc_tgt mem_src mem_tgt sc_src sc_tgt) *)
(*       (MEM: sim_memory flags_bot false w0 mem_src mem_tgt) *)
(*       (SC: sim_timemap flags_bot false w0 sc_src sc_tgt) *)
(*   : *)
(*     exists mem_src' lc_src' w1, *)
(*       (<<STEPS: rtc (@Thread.tau_step _) *)
(*                     (Thread.mk _ st_src lc_src sc_src mem_src) *)
(*                     (Thread.mk _ st_src lc_src' sc_src mem_src')>>) /\ *)
(*       (<<LOCAL: sim_local vm flags_bot f_tgt false w1 lc_src' lc_tgt mem_src' mem_tgt sc_src sc_tgt>>) /\ *)
(*       (<<MEM: sim_memory flags_bot false w1 mem_src' mem_tgt>>) /\ *)
(*       (<<SC: sim_timemap flags_bot false w1 sc_src sc_tgt>>) /\ *)
(*       (<<WORLD: world_messages_le (unchangable mem_src lc_src.(Local.promises)) w0 w1>>). *)
(* Admitted. *)

(* Lemma sim_memory_lower f_src w mem_src mem_tgt0 mem_tgt1 *)
(*       (SIM: sim_memory f_src false w mem_src mem_tgt0) *)
(*       (MEM: lower_memory mem_tgt0 mem_tgt1) *)
(*   : *)
(*     sim_memory f_src false w mem_src mem_tgt1. *)
(* Admitted. *)

(* Lemma sim_timemap_lower f_src w sc_src sc_tgt0 sc_tgt1 *)
(*       (SIM: sim_timemap f_src false w sc_src sc_tgt0) *)
(*       (SC: TimeMap.le sc_tgt0 sc_tgt1) *)
(*   : *)
(*     sim_timemap f_src false w sc_src sc_tgt1. *)
(* Admitted. *)







(* Lemma sim_promise_consistent *)
(*       vm f_src f_tgt b w lc_src lc_tgt mem_src mem_tgt sc_src sc_tgt *)
(*       (LOCAL: sim_local vm f_src f_tgt false w lc_src lc_tgt mem_src mem_tgt sc_src sc_tgt) *)
(*       (MEM: sim_memory flags_bot b w mem_src mem_tgt) *)
(*       (SC: sim_timemap flags_bot b w sc_src sc_tgt) *)
(*       (CONSISTENT: Local.promise_consistent lc_tgt) *)
(*   : *)
(*     Local.promise_consistent lc_src. *)
(* Admitted. *)

(* Lemma sim_cap vm f_tgt w0 lc_src lc_tgt mem_src0 mem_tgt0 mem_tgt1 sc_src sc_tgt *)
(*       (LOCAL: sim_local vm flags_bot f_tgt false w0 lc_src lc_tgt mem_src0 mem_tgt0 sc_src sc_tgt) *)
(*       (MEM: sim_memory flags_bot false w0 mem_src0 mem_tgt0) *)
(*       (SC: sim_timemap flags_bot false w0 sc_src sc_tgt) *)
(*       (CAP: Memory.cap mem_tgt0 mem_tgt1) *)
(*   : *)
(*     exists tm_src mem_src1 w1, *)
(*       (<<TM: forall loc, Time.lt (Memory.max_ts loc mem_src0) (tm_src loc)>>) /\ *)
(*       (<<CAP: CapFlex.cap_flex mem_src0 mem_src1 tm_src>>) /\ *)
(*       (<<MEM: sim_memory flags_bot true w1 mem_src1 mem_tgt1>>) /\ *)
(*       (<<SC: sim_timemap flags_bot true w1 sc_src sc_tgt>>) /\ *)
(*       (<<LOCAL: sim_local vm flags_bot f_tgt true w1 lc_src lc_tgt mem_src1 mem_tgt1 sc_src sc_tgt>>) /\ *)
(*       (<<WORLD: world_messages_le (unchangable mem_src0 lc_src.(Local.promises)) w0 w1>>). *)
(* Admitted. *)

(* Lemma sim_future vm0 f_tgt w0 lc_src lc_tgt mem_src0 mem_tgt0 sc_src0 sc_tgt0 *)
(*       (SIM: sim_local vm0 flags_bot f_tgt false w0 lc_src lc_tgt mem_src0 mem_tgt0 sc_src0 sc_tgt0) *)
(*       (MEM0: sim_memory flags_bot false w0 mem_src0 mem_tgt0) *)
(*       (SC0: sim_timemap flags_bot false w0 sc_src0 sc_tgt0) *)

(*       w1 mem_src1 mem_tgt1 sc_src1 sc_tgt1 *)
(*       (WORLD: world_messages_le (Messages.of_memory lc_src.(Local.promises)) w0 w1) *)
(*       (MEMSRC: Memory.future mem_src0 mem_src1) *)
(*       (MEMTGT: Memory.future mem_tgt0 mem_tgt1) *)
(*       (SCSRC: TimeMap.le sc_src0 sc_src1) *)
(*       (SCTGT: TimeMap.le sc_tgt0 sc_tgt1) *)
(*       (MEM1: sim_memory flags_bot false w1 mem_src1 mem_tgt1) *)
(*       (SC1: sim_timemap flags_bot false w1 sc_src1 sc_tgt1) *)
(*   : *)
(*     exists vm1, *)
(*       (<<SIM: sim_local vm1 flags_bot f_tgt true w1 lc_src lc_tgt mem_src1 mem_tgt1 sc_src1 sc_tgt1>>) /\ *)
(*       (<<VALUES: value_map_le vm0 vm1>>) *)
(* . *)
(* Admitted. *)

(* Lemma sim_make_promise_match lang_src *)
(*       (st_src: lang_src.(Language.state)) *)
(*       vm f_src f_tgt b w0 lc_src lc_tgt mem_src mem_tgt sc_src sc_tgt *)
(*       loc v *)
(*       (FLAG: f_src loc = true) *)
(*       (LOCAL: sim_local vm f_src f_tgt false w0 lc_src lc_tgt mem_src mem_tgt sc_src sc_tgt) *)
(*       (MEM: sim_memory f_src b w0 mem_src mem_tgt) *)
(*       (SC: sim_timemap f_src b w0 sc_src sc_tgt) *)
(*       (VAL: vm loc = Some (v, v)) *)
(*   : *)
(*     exists mem_src' lc_src' w1, *)
(*       (<<STEPS: rtc (@Thread.tau_step _) *)
(*                     (Thread.mk _ st_src lc_src sc_src mem_src) *)
(*                     (Thread.mk _ st_src lc_src' sc_src mem_src')>>) /\ *)
(*       (<<LOCAL: sim_local vm (update_flags f_src loc false) (update_flags f_tgt loc false) false w1 lc_src' lc_tgt mem_src' mem_tgt sc_src sc_tgt>>) /\ *)
(*       (<<MEM: sim_memory (update_flags f_src loc false) b w1 mem_src' mem_tgt>>) /\ *)
(*       (<<WORLD: world_messages_le (unchangable mem_src lc_src.(Local.promises)) w0 w1>>). *)
(* Admitted. *)

(* Lemma sim_make_promise_not_match lang_src *)
(*       (st_src: lang_src.(Language.state)) *)
(*       vm f_src f_tgt b w0 lc_src lc_tgt mem_src mem_tgt sc_src sc_tgt *)
(*       loc v_src v_tgt *)
(*       (FLAG: f_src loc = true) *)
(*       (LOCAL: sim_local vm f_src f_tgt false w0 lc_src lc_tgt mem_src mem_tgt sc_src sc_tgt) *)
(*       (MEM: sim_memory f_src b w0 mem_src mem_tgt) *)
(*       (SC: sim_timemap f_src b w0 sc_src sc_tgt) *)
(*       (VAL: vm loc = Some (v_src, v_tgt)) *)
(*   : *)
(*     exists mem_src' lc_src' w1, *)
(*       (<<STEPS: rtc (@Thread.tau_step _) *)
(*                     (Thread.mk _ st_src lc_src sc_src mem_src) *)
(*                     (Thread.mk _ st_src lc_src' sc_src mem_src')>>) /\ *)
(*       (<<LOCAL: sim_local vm (update_flags f_src loc false) (update_flags f_tgt loc true) false w1 lc_src' lc_tgt mem_src' mem_tgt sc_src sc_tgt>>) /\ *)
(*       (<<MEM: sim_memory (update_flags f_src loc false) b w1 mem_src' mem_tgt>>) /\ *)
(*       (<<WORLD: world_messages_le (unchangable mem_src lc_src.(Local.promises)) w0 w1>>). *)
(* Admitted. *)

(* Lemma sim_make_lower lang_src *)
(*       (st_src: lang_src.(Language.state)) *)
(*       vm f_src f_tgt b w0 lc_src lc_tgt mem_src mem_tgt sc_src sc_tgt *)
(*       loc *)
(*       (LOCAL: sim_local vm f_src f_tgt false w0 lc_src lc_tgt mem_src mem_tgt sc_src sc_tgt) *)
(*       (MEM: sim_memory f_src b w0 mem_src mem_tgt) *)
(*       (SC: sim_timemap f_src b w0 sc_src sc_tgt) *)
(*   : *)
(*     exists mem_src' lc_src' w1, *)
(*       (<<STEPS: rtc (@Thread.tau_step _) *)
(*                     (Thread.mk _ st_src lc_src sc_src mem_src) *)
(*                     (Thread.mk _ st_src lc_src' sc_src mem_src')>>) /\ *)
(*       (<<LOCAL: sim_local vm f_src (update_flags f_tgt loc true) false w1 lc_src' lc_tgt mem_src' mem_tgt sc_src sc_tgt>>) /\ *)
(*       (<<MEM: sim_memory f_src b w1 mem_src' mem_tgt>>) /\ *)
(*       (<<WORLD: world_messages_le (unchangable mem_src lc_src.(Local.promises)) w0 w1>>). *)
(* Admitted. *)

(* Lemma sim_na_racy_read_tgt *)
(*       vm f_src f_tgt b w lc_src lc_tgt mem_src mem_tgt sc_src sc_tgt *)
(*       loc val ord *)
(*       (LOCAL: sim_local vm f_src f_tgt false w lc_src lc_tgt mem_src mem_tgt sc_src sc_tgt) *)
(*       (MEM: sim_memory f_src b w mem_src mem_tgt) *)
(*       (SC: sim_timemap f_src b w sc_src sc_tgt) *)
(*       (READ: Local.racy_read_step lc_tgt mem_tgt loc val ord) *)
(*   : *)
(*     (<<VALUE: vm loc = None>>) /\ *)
(*     (<<ORD: ord = Ordering.na>>). *)
(* Admitted. *)

(* Lemma sim_na_read_tgt *)
(*       vm f_src f_tgt b w lc_src lc_tgt0 mem_src mem_tgt sc_src sc_tgt *)
(*       lc_tgt1 loc ts val released *)
(*       (LOCAL: sim_local vm f_src f_tgt false w lc_src lc_tgt0 mem_src mem_tgt sc_src sc_tgt) *)
(*       (MEM: sim_memory f_src b w mem_src mem_tgt) *)
(*       (SC: sim_timemap f_src b w sc_src sc_tgt) *)
(*       (READ: Local.read_step lc_tgt0 mem_tgt loc ts val released Ordering.na lc_tgt1) *)
(*   : *)
(*     forall v_src v_tgt (VALUE: vm loc = Some (v_src, v_tgt)), v_tgt = val. *)
(* Admitted. *)

(* Lemma sim_na_racy_write_tgt *)
(*       vm f_src f_tgt b w lc_src lc_tgt mem_src mem_tgt sc_src sc_tgt *)
(*       loc ord *)
(*       (LOCAL: sim_local vm f_src f_tgt false w lc_src lc_tgt mem_src mem_tgt sc_src sc_tgt) *)
(*       (MEM: sim_memory f_src b w mem_src mem_tgt) *)
(*       (SC: sim_timemap f_src b w sc_src sc_tgt) *)
(*       (WRITE: Local.racy_write_step lc_tgt mem_tgt loc ord) *)
(*   : *)
(*     (<<VALUE: vm loc = None>>) /\ *)
(*     (<<ORD: ord = Ordering.na>>). *)
(* Admitted. *)

(* Lemma sim_na_write_tgt *)
(*       vm f_src f_tgt b w lc_src lc_tgt0 mem_src mem_tgt0 sc_src sc_tgt0 *)
(*       loc mem_tgt1 lc_tgt1 sc_tgt1 from to val ord msgs kinds kind v_src v_tgt *)
(*       (LOCAL: sim_local vm f_src f_tgt false w lc_src lc_tgt0 mem_src mem_tgt0 sc_src sc_tgt0) *)
(*       (MEM: sim_memory f_src b w mem_src mem_tgt0) *)
(*       (SC: sim_timemap f_src b w sc_src sc_tgt0) *)
(*       (WRITE: Local.write_na_step lc_tgt0 sc_tgt0 mem_tgt0 loc from to val ord lc_tgt1 sc_tgt1 mem_tgt1 msgs kinds kind) *)
(*       (LOWER: lower_memory mem_tgt1 mem_tgt0) *)
(*       (FLAG: f_tgt loc = true) *)
(*       (VALUES: vm loc = Some (v_src, v_tgt)) *)
(*   : *)
(*     (<<LOCAL: sim_local (update_value_map vm loc (Some (v_src, val))) f_src f_tgt false w lc_src lc_tgt1 mem_src mem_tgt1 sc_src sc_tgt1>>) /\ *)
(*     (<<MEM: sim_memory f_src b w mem_src mem_tgt1>>) /\ *)
(*     (<<SC: sim_timemap f_src b w sc_src sc_tgt1>>) /\ *)
(*     (<<ORD: ord = Ordering.na>>) /\ *)
(*     (<<SC: sc_tgt1 = sc_tgt0>>). *)
(* Admitted. *)

(* Lemma sim_na_read_src *)
(*       vm f_src f_tgt b w lc_src lc_tgt mem_src mem_tgt sc_src sc_tgt *)
(*       loc v_src v_tgt *)
(*       (LOCAL: sim_local vm f_src f_tgt false w lc_src lc_tgt mem_src mem_tgt sc_src sc_tgt) *)
(*       (MEM: sim_memory f_src b w mem_src mem_tgt) *)
(*       (SC: sim_timemap f_src b w sc_src sc_tgt) *)
(*       (VALUE: vm loc = Some (v_src, v_tgt)) *)
(*   : *)
(*     exists ts released, *)
(*       (<<READ: Local.read_step lc_src mem_src loc ts v_src released Ordering.na lc_src>>). *)
(* Admitted. *)

(* Lemma sim_na_racy_read_src *)
(*       vm f_src f_tgt b w lc_src lc_tgt mem_src mem_tgt sc_src sc_tgt *)
(*       loc val *)
(*       (LOCAL: sim_local vm f_src f_tgt false w lc_src lc_tgt mem_src mem_tgt sc_src sc_tgt) *)
(*       (MEM: sim_memory f_src b w mem_src mem_tgt) *)
(*       (SC: sim_timemap f_src b w sc_src sc_tgt) *)
(*       (VALUE: vm loc = None) *)
(*   : *)
(*     Local.racy_read_step lc_src mem_src loc val Ordering.na. *)
(* Admitted. *)

(* Lemma sim_na_racy_write_src *)
(*       vm f_src f_tgt b w lc_src lc_tgt mem_src mem_tgt sc_src sc_tgt *)
(*       loc *)
(*       (LOCAL: sim_local vm f_src f_tgt false w lc_src lc_tgt mem_src mem_tgt sc_src sc_tgt) *)
(*       (MEM: sim_memory f_src b w mem_src mem_tgt) *)
(*       (SC: sim_timemap f_src b w sc_src sc_tgt) *)
(*       (VALUE: vm loc = None) *)
(*   : *)
(*     Local.racy_write_step lc_src mem_src loc Ordering.na. *)
(* Admitted. *)

(* Lemma sim_na_write_src *)
(*       vm f_src f_tgt b w lc_src0 lc_tgt mem_src0 mem_tgt sc_src sc_tgt *)
(*       loc v_src v_tgt val *)
(*       (LOCAL: sim_local vm f_src f_tgt false w lc_src0 lc_tgt mem_src0 mem_tgt sc_src sc_tgt) *)
(*       (MEM: sim_memory f_src b w mem_src0 mem_tgt) *)
(*       (SC: sim_timemap f_src b w sc_src sc_tgt) *)
(*       (VALUE: vm loc = Some (v_src, v_tgt)) *)
(*   : *)
(*     let f_src := update_flags f_src loc true in *)
(*     let vm := (update_value_map vm loc (Some (val, v_tgt))) in *)
(*     exists from to msgs kinds kind lc_src1 mem_src1, *)
(*       (<<WRITE: Local.write_na_step lc_src0 sc_src mem_src0 loc from to val Ordering.na lc_src1 sc_src mem_src1 msgs kinds kind>>) /\ *)
(*       (<<LOCAL: sim_local vm f_src f_tgt false w lc_src1 lc_tgt mem_src1 mem_tgt sc_src sc_tgt>>) /\ *)
(*       (<<MEM: sim_memory f_src b w mem_src1 mem_tgt>>) /\ *)
(*       (<<SC: sim_timemap f_src b w sc_src sc_tgt>>). *)
(* Admitted. *)
(* < *)
