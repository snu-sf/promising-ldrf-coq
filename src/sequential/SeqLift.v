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

Definition version := Loc.t -> nat.
Definition version_le (v0 v1: version): Prop := forall loc, le (v0 loc) (v1 loc).

Definition opt_version_le (v0 v1: option version): Prop :=
  match v0, v1 with
  | None, _ => True
  | Some v0, Some v1 => version_le v0 v1
  | _, _ => False
  end.

Program Instance version_le_PreOrder: PreOrder version_le.
Next Obligation.
Proof.
  ii. refl.
Qed.
Next Obligation.
Proof.
  ii. etrans; eauto.
Qed.

Program Instance opt_version_le_PreOrder: PreOrder opt_version_le.
Next Obligation.
Proof.
  ii. destruct x; ss.
Qed.
Next Obligation.
Proof.
  ii. destruct x, y, z; ss. etrans; eauto.
Qed.

Definition version_join (v0 v1: version): version :=
  fun loc => Nat.max (v0 loc) (v1 loc).

Lemma version_join_l v0 v1
  :
    version_le v0 (version_join v0 v1).
Proof.
  ii. unfold version_join. lia.
Qed.

Lemma version_join_r v0 v1
  :
    version_le v1 (version_join v0 v1).
Proof.
  ii. unfold version_join. lia.
Qed.

Lemma version_join_spec v0 v1 v
      (LE0: version_le v0 v)
      (LE1: version_le v1 v)
  :
    version_le (version_join v0 v1) v.
Proof.
  ii. specialize (LE0 loc). specialize (LE1 loc).
  unfold version_join. lia.
Qed.

Definition opt_version_join (v0 v1: option version): option version :=
  match v0, v1 with
  | None, _ => v1
  | _, None => v0
  | Some v0, Some v1 => Some (version_join v0 v1)
  end.

Lemma opt_version_join_l v0 v1
  :
    opt_version_le v0 (opt_version_join v0 v1).
Proof.
  destruct v0, v1; ss. eapply version_join_l; eauto.
Qed.

Lemma opt_version_join_r v0 v1
  :
    opt_version_le v1 (opt_version_join v0 v1).
Proof.
  destruct v0, v1; ss. eapply version_join_r; eauto.
Qed.

Lemma opt_version_join_spec v0 v1 v
      (LE0: opt_version_le v0 v)
      (LE1: opt_version_le v1 v)
  :
    opt_version_le (opt_version_join v0 v1) v.
Proof.
  destruct v0, v1, v; ss. eapply version_join_spec; eauto.
Qed.

Definition versions := Loc.t -> Time.t -> option version.
Definition reserve_versions := Loc.t -> Time.t -> option nat.

Definition versions_le (vers0 vers1: versions): Prop :=
  forall loc ts v (VER: vers0 loc ts = Some v),
    vers1 loc ts = Some v.

Program Instance versions_le_PreOrder: PreOrder versions_le.
Next Obligation.
Proof.
  ii. auto.
Qed.
Next Obligation.
Proof.
  ii. eapply H0; eauto.
Qed.

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
      mapping_map_lt_iff: forall v ts0 ts1 fts0 fts1
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
        f1.(times) v = f0.(times) v>>) /\
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
      erewrite <- mapping_map_lt_iff in l; eauto. timetac. }
    { i. destruct (Time.le_lt_dec ts0 ts1); auto.
      erewrite mapping_map_lt_iff in l; eauto. timetac. }
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
  erewrite <- Mapping.mapping_map_lt_iff; cycle 1; eauto.
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
  erewrite <- Mapping.mapping_map_lt_iff; cycle 1; eauto.
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
  erewrite Mapping.mapping_map_lt_iff; eauto.
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

Lemma sim_disjoint_if f v
      from_tgt0 from_src0 to_tgt0 to_src0
      from_tgt1 from_src1 to_tgt1 to_src1
      (WF: Mapping.wf f)
      (VER: loc_version_wf f v)
      (FROM0: sim_timestamp_exact f v from_src0 from_tgt0)
      (TO0: sim_timestamp_exact f v to_src0 to_tgt0)
      (FROM1: sim_timestamp_exact f v from_src1 from_tgt1)
      (TO1: sim_timestamp_exact f v to_src1 to_tgt1)
      (DISJOINT: Interval.disjoint (from_src0, to_src0) (from_src1, to_src1))
  :
    Interval.disjoint (from_tgt0, to_tgt0) (from_tgt1, to_tgt1).
Proof.
  apply NNPP. ii. revert DISJOINT.
  apply disjoint_equivalent. apply disjoint_equivalent in H. des.
  splits.
  - eapply sim_timestamp_exact_lt; eauto.
  - eapply sim_timestamp_exact_lt; eauto.
  - eapply sim_timestamp_exact_lt; eauto.
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


Definition time_le_timemap (loc: Loc.t) (ts: Time.t) (tm: TimeMap.t): Prop :=
  Time.le (tm loc) ts.

Record time_le_view (loc: Loc.t) (ts: Time.t) (vw: View.t): Prop :=
  time_le_view_intro {
      time_le_view_pln: time_le_timemap loc ts vw.(View.pln);
      time_le_view_rlx: time_le_timemap loc ts vw.(View.rlx);
    }.

Variant time_le_opt_view (loc: Loc.t) (ts: Time.t):
  forall (vw: option View.t), Prop :=
| time_le_opt_view_some
    vw
    (EXACT: time_le_view loc ts vw)
  :
    time_le_opt_view loc ts (Some vw)
| time_le_opt_view_none
  :
    time_le_opt_view loc ts None
.

Definition time_exact_timemap (loc: Loc.t) (ts: Time.t) (tm: TimeMap.t): Prop :=
  tm loc = ts.

Record time_exact_view (loc: Loc.t) (ts: Time.t) (vw: View.t): Prop :=
  time_exact_view_intro {
      time_exact_view_pln: time_exact_timemap loc ts vw.(View.pln);
      time_exact_view_rlx: time_exact_timemap loc ts vw.(View.rlx);
    }.

Variant time_exact_opt_view (loc: Loc.t) (ts: Time.t):
  forall (vw: option View.t), Prop :=
| time_exact_opt_view_some
    vw
    (EXACT: time_exact_view loc ts vw)
  :
    time_exact_opt_view loc ts (Some vw)
| time_exact_opt_view_none
  :
    time_exact_opt_view loc ts None
.

Variant sim_timemap_max (loc: Loc.t) (ts_src: Time.t)
        (f: Mapping.ts) (v: version) (tm_src tm_tgt: TimeMap.t): Prop :=
| sim_timemap_max_intro
    (MAX: forall l (LOC: l <> loc),
        sim_timestamp_max (f l) (v l) (tm_src l) (tm_tgt l))
    (LE: time_exact_timemap loc ts_src tm_src)
.

Lemma sim_timemap_max_sim loc ts_src f v tm_src tm_tgt
      (SIM: sim_timemap_max loc ts_src f v tm_src tm_tgt)
  :
    sim_timemap (fun loc0 => loc0 <> loc) f v tm_src tm_tgt.
Proof.
  ii. eapply sim_timestamp_max_sim; eauto. eapply SIM. auto.
Qed.

Lemma sim_timemap_max_max loc ts_src f v tm_src tm_tgt
      tm
      (MAX: sim_timemap_max loc ts_src f v tm_src tm_tgt)
      (SIM: sim_timemap (fun loc0 => loc0 <> loc) f v tm tm_tgt)
      (LE: time_le_timemap loc ts_src tm)
  :
    TimeMap.le tm tm_src.
Proof.
  ii. destruct (Loc.eq_dec loc0 loc).
  { subst. inv MAX. rewrite LE0. auto. }
  { eapply sim_timestamp_max_max; eauto. eapply MAX. auto. }
Qed.

Lemma sim_timemap_max_mon_mapping loc ts_src f0 f1 v tm_src tm_tgt
      (WF: Mapping.wfs f0)
      (VERWF: version_wf f0 v)
      (MAP: Mapping.les f0 f1)
  :
    sim_timemap_max loc ts_src f0 v tm_src tm_tgt <-> sim_timemap_max loc ts_src f1 v tm_src tm_tgt.
Proof.
  split; ii.
  { inv H. econs; auto.
    i. erewrite <- sim_timestamp_max_mon_mapping; eauto. }
  { inv H. econs; auto.
    i. erewrite sim_timestamp_max_mon_mapping; eauto. }
Qed.

Lemma sim_timemap_max_exists loc ts_src f v tm_tgt
      (WF: Mapping.wfs f)
      (VER: version_wf f v)
  :
    exists tm_src, <<MAX: sim_timemap_max loc ts_src f v tm_src tm_tgt>>.
Proof.
  hexploit (choice (fun loc0 ts => (loc0 <> loc -> sim_timestamp_max (f loc0) (v loc0) ts (tm_tgt loc0)) /\ (loc0 = loc -> ts = ts_src))).
  { i. destruct (Loc.eq_dec x loc).
    { exists ts_src. splits; ss. }
    { hexploit sim_timestamp_max_exists; eauto. i. des.
      exists ts_src0. splits; eauto. i. ss.
    }
  }
  i. des. exists f0. splits. econs.
  { i. specialize (H l). des. auto. }
  { specialize (H loc). des. apply H0; auto. }
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

Record sim_view_max (loc: Loc.t) (ts_src: Time.t)
       (f: Mapping.ts) (v: version) (vw_src vw_tgt: View.t) :=
  sim_view_max_intro {
      sim_view_max_pln: sim_timemap_max loc ts_src f v vw_src.(View.pln) vw_tgt.(View.pln);
      sim_view_max_rlx: sim_timemap_max loc ts_src f v vw_src.(View.rlx) vw_tgt.(View.rlx);
    }.

Lemma sim_view_max_sim loc ts_src f v vw_src vw_tgt
      (SIM: sim_view_max loc ts_src f v vw_src vw_tgt)
  :
    sim_view (fun loc0 => loc0 <> loc) f v vw_src vw_tgt.
Proof.
  econs.
  { eapply sim_timemap_max_sim; eauto. eapply SIM. }
  { eapply sim_timemap_max_sim; eauto. eapply SIM. }
Qed.

Lemma sim_view_max_max loc ts_src f v vw_src vw_tgt
      vw
      (MAX: sim_view_max loc ts_src f v vw_src vw_tgt)
      (SIM: sim_view (fun loc0 => loc0 <> loc) f v vw vw_tgt)
      (LE: time_le_view loc ts_src vw)
  :
    View.le vw vw_src.
Proof.
  econs.
  { eapply sim_timemap_max_max; eauto.
    { eapply MAX. }
    { eapply SIM. }
    { apply LE. }
  }
  { eapply sim_timemap_max_max; eauto.
    { eapply MAX. }
    { eapply SIM. }
    { apply LE. }
  }
Qed.

Lemma sim_view_max_mon_mapping loc ts_src f0 f1 v vw_src vw_tgt
      (WF: Mapping.wfs f0)
      (VERWF: version_wf f0 v)
      (MAP: Mapping.les f0 f1)
  :
    sim_view_max loc ts_src f0 v vw_src vw_tgt <-> sim_view_max loc ts_src f1 v vw_src vw_tgt.
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

Lemma sim_view_max_exists loc ts_src f v vw_tgt
      (WF: Mapping.wfs f)
      (VER: version_wf f v)
  :
    exists vw_src, <<MAX: sim_view_max loc ts_src f v vw_src vw_tgt>>.
Proof.
  hexploit sim_timemap_max_exists; eauto. i. des.
  hexploit sim_timemap_max_exists; eauto. i. des.
  exists (View.mk tm_src tm_src0). econs; eauto.
Qed.



Variant sim_opt_view (L: Loc.t -> Prop)
        (f: Mapping.ts):
  forall (v: option version) (vw_src vw_tgt: option View.t), Prop :=
| sim_opt_view_some
    v vw_src vw_tgt
    (SIM: sim_view L f v vw_src vw_tgt)
  :
    sim_opt_view L f (Some v) (Some vw_src) (Some vw_tgt)
| sim_opt_view_none
    v vw
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
      (VER: opt_version_le v0 v1)
      (WF: Mapping.wfs f)
      (VERWF: opt_version_wf f v1)
  :
    sim_opt_view L f v1 vw_src vw_tgt.
Proof.
  inv SIM.
  { destruct v1; ss. econs. eapply sim_view_mon_ver; eauto. }
  { econs. }
Qed.

Lemma sim_opt_view_mon_mapping L f0 f1 v vw_src vw_tgt
      (WF: Mapping.wfs f0)
      (VERWF: opt_version_wf f0 v)
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

Lemma sim_opt_view_unwrap l f v0 v1
      vw_src vw_tgt
      (SIM: sim_opt_view l f v0 vw_src vw_tgt)
      (WF: Mapping.wfs f)
      (VERWF: version_wf f v1)
      (VER: forall v (VER: v0 = Some v), version_le v v1)
  :
    sim_view l f v1 (View.unwrap vw_src) (View.unwrap vw_tgt).
Proof.
  inv SIM; ss.
  { hexploit VER; eauto. i.
    eapply sim_view_mon_ver; eauto. }
  { eapply sim_view_bot; eauto. }
Qed.

Variant sim_opt_view_max loc ts_src
        (f: Mapping.ts):
  forall (v: option version) (vw_src vw_tgt: option View.t), Prop :=
| sim_opt_view_max_some
    v vw_src vw_tgt
    (SIM: sim_view_max loc ts_src f v vw_src vw_tgt)
  :
    sim_opt_view_max loc ts_src f (Some v) (Some vw_src) (Some vw_tgt)
| sim_opt_view_max_none
    v
  :
    sim_opt_view_max loc ts_src f v None None
.

Lemma sim_opt_view_max_sim loc ts_src f v vw_src vw_tgt
      (SIM: sim_opt_view_max loc ts_src f v vw_src vw_tgt)
  :
    sim_opt_view (fun loc0 => loc0 <> loc) f v vw_src vw_tgt.
Proof.
  inv SIM; econs.
  eapply sim_view_max_sim; eauto.
Qed.

Lemma sim_opt_view_max_max loc ts_src f v vw_src vw_tgt
      vw
      (MAX: sim_opt_view_max loc ts_src f v vw_src vw_tgt)
      (SIM: sim_opt_view (fun loc0 => loc0 <> loc) f v vw vw_tgt)
      (LE: time_le_opt_view loc ts_src vw)
  :
    View.opt_le vw vw_src.
Proof.
  inv MAX; inv SIM.
  { econs. eapply sim_view_max_max; eauto. inv LE. auto. }
  { econs. }
  { econs. }
Qed.

Lemma sim_opt_view_max_mon_mapping loc ts_src f0 f1 v vw_src vw_tgt
      (WF: Mapping.wfs f0)
      (VERWF: opt_version_wf f0 v)
      (MAP: Mapping.les f0 f1)
  :
    sim_opt_view_max loc ts_src f0 v vw_src vw_tgt <-> sim_opt_view_max loc ts_src f1 v vw_src vw_tgt.
Proof.
  split; i.
  { inv H; econs.
    erewrite <- sim_view_max_mon_mapping; eauto.
  }
  { inv H; econs.
    erewrite sim_view_max_mon_mapping; eauto.
  }
Qed.

Lemma sim_opt_view_max_exists loc ts_src f v vw_tgt
      (WF: Mapping.wfs f)
      (VER: forall (SOME: vw_tgt <> None),
          exists v0, (<<EQ: v = Some v0>>) /\ (<<WF: version_wf f v0>>))
  :
    exists vw_src, <<MAX: sim_opt_view_max loc ts_src f v vw_src vw_tgt>>.
Proof.
  destruct vw_tgt as [vw_tgt|].
  { hexploit VER; ss. i. des. clarify.
    hexploit sim_view_max_exists; eauto. i. des.
    eexists (Some _). econs; eauto. }
  { exists None. econs. }
Qed.


Definition top_time (top: Time.t) (f: Mapping.t): Prop :=
  forall ts fts
         (MAP: f.(Mapping.map) f.(Mapping.ver) ts = Some fts),
    Time.lt fts top.

Lemma top_time_mon ts0 ts1 f
      (TOP: top_time ts0 f)
      (TS: Time.le ts0 ts1)
  :
    top_time ts1 f.
Proof.
  ii. eapply TimeFacts.lt_le_lt; eauto.
Qed.

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
        (flag_tgt: bool)
        (loc: Loc.t)
        (f: Mapping.ts):
  forall (v: option version) (msg_src msg_tgt: Message.t), Prop :=
| sim_message_concrete
    v val_src val_tgt vw_src vw_tgt
    (VAL: Const.le val_tgt val_src)
    (SIM: sim_opt_view (fun loc0 => loc0 <> loc) f (Some v) vw_src vw_tgt)
    (FLAG: flag_tgt = false)
  :
    sim_message flag_tgt loc f (Some v) (Message.concrete val_src vw_src) (Message.concrete val_tgt vw_tgt)
| sim_message_undef
    v
  :
    sim_message flag_tgt loc f (Some v) Message.undef Message.undef
| sim_message_reserve
    v
  :
    sim_message flag_tgt loc f v Message.reserve Message.reserve
| sim_message_none
    v val_src val_tgt vw_tgt
    (VAL: Const.le val_tgt val_src)
    (FLAG: flag_tgt = true)
  :
    sim_message flag_tgt loc f (Some v) (Message.concrete val_src None) (Message.concrete val_tgt vw_tgt)
.

Lemma sim_message_flag_mon flag_tgt loc f v msg_src msg_tgt
      (SIM: sim_message flag_tgt loc f v msg_src msg_tgt)
  :
    sim_message false loc f v msg_src msg_tgt.
Proof.
  inv SIM; econs; eauto. econs.
Qed.

Lemma sim_message_mon_tgt flag_tgt loc f v msg_src msg_tgt0 msg_tgt1
      (SIM: sim_message flag_tgt loc f v msg_src msg_tgt0)
      (MSG: Message.le msg_tgt0 msg_tgt1)
  :
    sim_message flag_tgt loc f v msg_src msg_tgt1.
Proof.
  inv SIM; inv MSG.
  { econs; eauto.
    { etrans; eauto. }
    { eapply sim_opt_view_mon_tgt; eauto. }
  }
  { econs. }
  { econs. }
  { econs 4; eauto. etrans; eauto. }
Qed.

Lemma sim_message_mon_ver flag_tgt loc f v0 v1 msg_src msg_tgt
      (SIM: sim_message flag_tgt loc f v0 msg_src msg_tgt)
      (VER: option_rel version_le v0 v1)
      (WF: Mapping.wfs f)
      (VERWF: opt_version_wf f v1)
  :
    sim_message flag_tgt loc f v1 msg_src msg_tgt.
Proof.
  inv SIM.
  { ss. des_ifs. econs; eauto. eapply sim_opt_view_mon_ver; eauto. }
  { ss. des_ifs. econs; eauto. }
  { econs. }
  { ss. des_ifs. econs 4; eauto. }
Qed.

Lemma sim_message_mon_mapping flag_tgt loc f0 f1 v msg_src msg_tgt
      (WF: Mapping.wfs f0)
      (VERWF: opt_version_wf f0 v)
      (MAP: Mapping.les f0 f1)
  :
    sim_message flag_tgt loc f0 v msg_src msg_tgt <-> sim_message flag_tgt loc f1 v msg_src msg_tgt.
Proof.
  split; i.
  { inv H; try by (econs; auto). econs 1; eauto.
    erewrite <- sim_opt_view_mon_mapping; eauto. }
  { inv H; try by (econs; auto). econs 1; eauto. erewrite sim_opt_view_mon_mapping; eauto. }
Qed.

Variant sim_message_max
        (flag_tgt: bool)
        (loc: Loc.t) (ts_src: Time.t)
        (f: Mapping.ts):
  forall (v: option version) (msg_src msg_tgt: Message.t), Prop :=
| sim_message_max_concrete
    v val vw_src vw_tgt
    (SIM: sim_opt_view_max loc ts_src f (Some v) vw_src vw_tgt)
    (FLAG: flag_tgt = false)
  :
    sim_message_max flag_tgt loc ts_src f (Some v) (Message.concrete val vw_src) (Message.concrete val vw_tgt)
| sim_message_max_undef
    v
  :
    sim_message_max flag_tgt loc ts_src f (Some v) Message.undef Message.undef
| sim_message_max_reserve
    v
  :
    sim_message_max flag_tgt loc ts_src f v Message.reserve Message.reserve
| sim_message_max_none
    v val vw_tgt
    (FLAG: flag_tgt = true)
  :
    sim_message_max flag_tgt loc ts_src f (Some v) (Message.concrete val None) (Message.concrete val vw_tgt)
.

Lemma sim_message_max_sim flag_tgt loc ts_src f v msg_src msg_tgt
      (SIM: sim_message_max flag_tgt loc ts_src f v msg_src msg_tgt)
  :
    sim_message flag_tgt loc f v msg_src msg_tgt.
Proof.
  inv SIM.
  { econs 1; eauto.
    { refl. }
    { eapply sim_opt_view_max_sim; eauto. }
  }
  { econs 2. }
  { econs 3. }
  { econs 4; eauto. refl. }
Qed.

Lemma message_to_time_le_opt_view loc to val released
      (MSGTO: Memory.message_to (Message.concrete val released) loc to)
      (MSGWF: Message.wf (Message.concrete val released))
  :
    time_le_opt_view loc to released.
Proof.
  inv MSGTO. destruct released; ss; econs. econs.
  { inv MSGWF. inv WF. red. etrans; eauto. eapply WF0. }
  { eauto. }
Qed.

Lemma sim_message_max_max flag_tgt loc ts_src f v msg_src msg_tgt
      msg
      (MAX: sim_message_max flag_tgt loc ts_src f v msg_src msg_tgt)
      (SIM: sim_message flag_tgt loc f v msg msg_tgt)
      (MSGTO: Memory.message_to msg loc ts_src)
      (MSGWF: Message.wf msg)
  :
    Message.le msg msg_src.
Proof.
  inv MAX; inv SIM.
  { econs; eauto. eapply sim_opt_view_max_max; eauto.
    eapply message_to_time_le_opt_view; eauto.
  }
  { econs; eauto. }
  { econs. }
  { ss. }
  { ss. }
  { econs; eauto. }
Qed.

Lemma sim_message_max_mon_mapping flag_tgt loc ts_src f0 f1 v msg_src msg_tgt
      (WF: Mapping.wfs f0)
      (VERWF: opt_version_wf f0 v)
      (MAP: Mapping.les f0 f1)
  :
    sim_message_max flag_tgt loc ts_src f0 v msg_src msg_tgt <-> sim_message_max flag_tgt loc ts_src f1 v msg_src msg_tgt.
Proof.
  split; i.
  { inv H.
    { econs 1; eauto. erewrite <- sim_opt_view_max_mon_mapping; eauto. }
    { econs 2. }
    { econs 3. }
    { econs 4; eauto. }
  }
  { inv H.
    { econs 1; eauto. erewrite sim_opt_view_max_mon_mapping; eauto. }
    { econs 2. }
    { econs 3. }
    { econs 4; eauto. }
  }
Qed.

Lemma sim_message_max_exists flag_tgt loc ts_src f v msg_tgt
      (WF: Mapping.wfs f)
      (VER: forall (RESERVE: msg_tgt <> Message.reserve),
          exists v0, (<<EQ: v = Some v0>>) /\ (<<WF: version_wf f v0>>))
  :
    exists msg_src, <<MAX: sim_message_max flag_tgt loc ts_src f v msg_src msg_tgt>>.
Proof.
  destruct msg_tgt.
  { hexploit VER; ss. i. des; clarify.
    destruct flag_tgt.
    { exists (Message.concrete val None). econs 4; eauto. }
    { hexploit VER; ss. i. des. clarify.
      hexploit sim_opt_view_max_exists.
      { eauto. }
      { i. eapply VER. ss. }
      i. des. esplits; eauto. econs; eauto.
    }
  }
  { hexploit VER; ss. i. des; clarify.
    esplits. econs. }
  { esplits. econs. }
Qed.

Lemma sim_message_max_msg_to flag_tgt loc ts_src f v msg_src msg_tgt
      (MAX: sim_message_max flag_tgt loc ts_src f v msg_src msg_tgt)
  :
    Memory.message_to msg_src loc ts_src.
Proof.
  inv MAX; econs.
  { inv SIM; ss.
    { eapply sim_view_max_rlx in SIM0.
      inv SIM0. rewrite LE. refl.
    }
    { eapply Time.bot_spec. }
  }
  { ss. eapply Time.bot_spec. }
Qed.

Lemma sim_message_max_msg_wf flag_tgt loc ts_src f v msg_src msg_tgt
      (MAX: sim_message_max flag_tgt loc ts_src f v msg_src msg_tgt)
      (WF: Message.wf msg_tgt)
  :
    Message.wf msg_src.
Proof.
  inv MAX; econs; eauto. inv WF. inv SIM; econs.
  inv WF0. econs. eapply sim_timemap_max_max.
  { eapply SIM0. }
  { eapply sim_timemap_mon_tgt.
    2:{ eapply WF. }
    eapply sim_timemap_max_sim. eapply SIM0.
  }
  { red. eapply sim_view_max_pln in SIM0.
    inv SIM0. rewrite LE. refl.
  }
Qed.

Definition sim_closed_memory (f: Mapping.ts) (mem: Memory.t): Prop :=
  forall loc ts (CLOSED: Mapping.closed (f loc) (f loc).(Mapping.ver) ts),
  exists from val released,
    Memory.get loc ts mem = Some (from, Message.concrete val released).

Lemma sim_closed_memory_future f mem0 mem1
      (CLOSED: sim_closed_memory f mem0)
      (FUTURE: Memory.future_weak mem0 mem1)
  :
    sim_closed_memory f mem1.
Proof.
  ii. exploit CLOSED; eauto. i. des.
  eapply Memory.future_weak_get1 in x; eauto; ss.
  des. inv MSG_LE. esplits; eauto.
Qed.

Lemma sim_closed_memory_sim_timemap loc ts_src f v tm_src tm_tgt mem
      (SIM: sim_timemap_max loc ts_src f v tm_src tm_tgt)
      (MEM: sim_closed_memory f mem)
      (WF: Mapping.wfs f)
      (VER: version_wf f v)
  :
    semi_closed_timemap tm_src mem loc ts_src.
Proof.
  ii. inv SIM. destruct (Loc.eq_dec l loc).
  { subst. right. splits; auto. }
  { left. exploit MAX; eauto. i.
    eapply sim_timestamp_max_sim in x. unfold sim_timestamp in *. des.
    exploit MEM.
    { eapply sim_closed_mon_ver; eauto.
      { eapply VER. }
      { eapply mapping_latest_wf_loc. }
    }
    i. des. eauto.
  }
Qed.

Lemma sim_closed_memory_sim_view loc ts_src f v vw_src vw_tgt mem
      (SIM: sim_view_max loc ts_src f v vw_src vw_tgt)
      (MEM: sim_closed_memory f mem)
      (WF: Mapping.wfs f)
      (VER: version_wf f v)
  :
    semi_closed_view vw_src mem loc ts_src.
Proof.
  econs.
  { eapply sim_closed_memory_sim_timemap; eauto. eapply SIM. }
  { eapply sim_closed_memory_sim_timemap; eauto. eapply SIM. }
Qed.

Lemma sim_closed_memory_sim_opt_view loc ts_src f v vw_src vw_tgt mem
      (SIM: sim_opt_view_max loc ts_src f v vw_src vw_tgt)
      (MEM: sim_closed_memory f mem)
      (WF: Mapping.wfs f)
      (VER: opt_version_wf f v)
  :
    semi_closed_opt_view vw_src mem loc ts_src.
Proof.
  inv SIM; econs. eapply sim_closed_memory_sim_view; eauto.
Qed.

Lemma sim_closed_memory_sim_message flag_tgt loc ts_src f v msg_src msg_tgt mem
      (SIM: sim_message_max flag_tgt loc ts_src f v msg_src msg_tgt)
      (MEM: sim_closed_memory f mem)
      (WF: Mapping.wfs f)
      (VER: opt_version_wf f v)
  :
    semi_closed_message msg_src mem loc ts_src.
Proof.
  inv SIM; econs.
  { eapply sim_closed_memory_sim_opt_view; eauto. }
  { econs. }
Qed.

Definition mapping_update_latest (f: Mapping.t)
           (mapping: Time.t -> option Time.t) (times: Time.t -> Prop) :=
  Mapping.mk
    (fun v => if PeanoNat.Nat.eq_dec v (S f.(Mapping.ver))
              then mapping
              else
                f.(Mapping.map) v)
    (S f.(Mapping.ver))
    (fun v => if PeanoNat.Nat.eq_dec v (S f.(Mapping.ver))
              then
                f.(Mapping.times) f.(Mapping.ver) \1/ times
              else
                f.(Mapping.times) v)
.

Lemma mapping_update_latest_mapping f mapping times
  :
    (mapping_update_latest f mapping times).(Mapping.map) (mapping_update_latest f mapping times).(Mapping.ver) = mapping.
Proof.
  ss. des_ifs.
Qed.

Lemma mapping_update_latest_times f mapping times
  :
    (mapping_update_latest f mapping times).(Mapping.times) (mapping_update_latest f mapping times).(Mapping.ver) = f.(Mapping.times) f.(Mapping.ver) \1/ times.
Proof.
  ss. des_ifs.
Qed.

Lemma mapping_update_latest_wf f mapping (times: Time.t -> Prop)
      (WF: Mapping.wf f)
      (FINMAP: exists l, forall ts fts (MAP: mapping ts = Some fts),
            List.In (ts, fts) l)
      (FINTIMES: exists l, forall to (TIME: times to), List.In to l)
      (MAPLT: forall ts0 ts1 fts0 fts1
                     (MAP0: mapping ts0 = Some fts0) (MAP0: mapping ts1 = Some fts1),
          Time.lt ts0 ts1 <-> Time.lt fts0 fts1)
      (MAPINCR: forall ts fts0
                       (MAP0: f.(Mapping.map) f.(Mapping.ver) ts = Some fts0),
          exists fts1,
            (<<MAP: mapping ts = Some fts1>>) /\
            (<<TS: Time.le fts0 fts1>>))
  :
    (<<MAPWF: Mapping.wf (mapping_update_latest f mapping times)>>) /\
    (<<MAPLE: Mapping.le f (mapping_update_latest f mapping times)>>) /\
    (<<MAPLESTRONG: forall (PRESERVE: forall ts fts
                                             (MAP: f.(Mapping.map) f.(Mapping.ver) ts = Some fts),
                               mapping ts = Some fts),
        Mapping.le_strong f (mapping_update_latest f mapping times)>>)
.
Proof.
  splits.
  { econs; ss.
    { i. des_ifs. eapply Mapping.map_finite; eauto. }
    { i. des_ifs.
      { eapply MAPLT; eauto. }
      { eapply Mapping.mapping_map_lt; eauto. }
    }
    { i. des_ifs.
      { esplits; eauto. refl. }
      { hexploit Mapping.mapping_incr; [..|refl|eapply MAP0|]; eauto.
        { lia. }
        i. des. eapply MAPINCR in MAP; eauto. des.
        esplits; eauto.
      }
      { exfalso. lia. }
      { eapply Mapping.mapping_incr; eauto. lia. }
    }
    { i. des_ifs.
      { exfalso. lia. }
      { eapply Mapping.mapping_empty; eauto. lia. }
    }
    { eapply Mapping.mapping_bot; eauto. }
    { i. des_ifs.
      { hexploit Mapping.times_finite; eauto. i. des.
        exists (l0 ++ l). i. eapply List.in_or_app. des; eauto.
      }
      { eapply Mapping.times_finite; eauto. }
    }
    { i. des_ifs.
      { left. eapply Mapping.times_incr in TIME; eauto. lia. }
      { exfalso. lia. }
      { eapply Mapping.times_incr; eauto. lia. }
    }
    { ii. des_ifs.
      { exfalso. lia. }
      { eapply Mapping.times_empty in H; eauto. lia. }
    }
    { eapply Mapping.times_bot; eauto. }
  }
  { red. splits; ss; eauto.
    { i. des_ifs. exfalso. lia. }
    { i. des_ifs. exfalso. lia. }
  }
  { i. red. splits; ss; eauto.
    { i. des_ifs. exfalso. lia. }
    { i. des_ifs. exfalso. lia. }
    { i. des_ifs.
      { eapply PRESERVE; eauto. }
      { exfalso. lia. }
    }
  }
Qed.

Definition mapping_update (f: Mapping.t) ts fts: Mapping.t :=
  mapping_update_latest
    f
    (fun ts' =>
       if (Time.eq_dec ts ts')
       then Some fts
       else f.(Mapping.map) f.(Mapping.ver) ts')
    (bot1).

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
  ss. des_ifs. split; i; des; ss; auto.
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
  eapply mapping_update_latest_wf; eauto.
  { hexploit (Mapping.map_finite WF f.(Mapping.ver)); eauto. i. des.
    exists ((ts, fts)::l). i.
    unfold mapping_update in *. ss. des_ifs.
    { auto. }
    { right. eapply H; eauto. }
  }
  { exists []. ss. }
  { i. des_ifs.
    { split; i; timetac. }
    { split.
      { i. hexploit LEFT; eauto. }
      { i. destruct (Time.le_lt_dec ts1 ts0); auto. inv l; ss.
        eapply RIGHT in H0; eauto.
        exfalso. eapply Time.lt_strorder. etrans; eauto. }
    }
    { split.
      { i. hexploit RIGHT; eauto. }
      { i. destruct (Time.le_lt_dec ts1 ts0); auto. inv l; ss.
        2:{ exfalso. eapply n; ss. }
        eapply LEFT in H0; eauto.
        exfalso. eapply Time.lt_strorder. etrans; eauto. }
    }
    { eapply Mapping.mapping_map_lt; eauto. }
  }
  { i. des_ifs.
     { esplits; eauto. }
     { esplits; eauto. refl. }
  }
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
    { i. ss. des_ifs. split; i; des; ss; auto. }
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
    { i. ss. des_ifs. split; i; des; ss; auto. }
  }
Qed.

Lemma mapping_update_times (f0: Mapping.t) (times: Time.t -> Prop)
      (WF: Mapping.wf f0)
      (FIN: exists l, forall to (TIME: times to), List.In to l)
  :
    exists f1,
      (<<WF: Mapping.wf f1>>) /\
      (<<MAPLE: Mapping.le_strong f0 f1>>) /\
      (<<TIMES: forall to, (Mapping.closed f0 f0.(Mapping.ver) to \/ times to)
                           <->
                           Mapping.closed f1 f1.(Mapping.ver) to>>).
Proof.
  hexploit (@mapping_update_latest_wf f0 (f0.(Mapping.map) f0.(Mapping.ver)) times); eauto.
  { eapply Mapping.map_finite; eauto. }
  { eapply Mapping.mapping_map_lt; eauto. }
  { i. esplits; eauto. refl. }
  i. des. esplits; eauto.
  { erewrite mapping_update_latest_times. auto. }
Qed.

Fixpoint map_shift (f: Time.t -> option Time.t) (l: list Time.t)
         (ts: Time.t) (fts: Time.t): Loc.t -> option Time.t :=
  match l with
  | [] => f
  | hd::tl =>
    if (Time.le_lt_dec ts hd)
    then map_shift (fun to => if Time.eq_dec to hd then Some fts else f to) tl ts (Time.incr fts)
    else map_shift f tl ts fts
  end.

Lemma map_shift_finite l:
  forall f ts fts
         (FIN: exists l', forall ts' fts' (MAP: f ts' = Some fts'),
               List.In (ts', fts') l'),
  exists l', forall ts' fts' (MAP: map_shift f l ts fts ts' = Some fts'),
      List.In (ts', fts') l'.
Proof.
  induction l; ss; i; des.
  des_ifs.
  { hexploit (IHl (fun to => if TimeSet.Facts.eq_dec to a then Some fts else f to)).
    { exists ((a, fts)::l'). i. des_ifs; ss; auto. }
    i. des. esplits. i. eapply H; eauto.
  }
  { eapply IHl; eauto. }
Qed.

Lemma map_shift_preserved l:
  forall f ts fts to
         (FORALL: List.Forall (Time.lt to) l),
    map_shift f l ts fts to = f to.
Proof.
  induction l; ss. i. inv FORALL. des_ifs.
  { erewrite IHl; eauto. des_ifs. exfalso. timetac. }
  { erewrite IHl; eauto. }
Qed.

Lemma map_shift_correct0 l:
  forall f ts fts
         (SORTED: times_sorted l)
         to
         (TS: Time.lt to ts),
    map_shift f l ts fts to = f to.
Proof.
  induction l; i; ss.
  inv SORTED. des_ifs.
  { erewrite IHl; eauto. des_ifs.
    exfalso. timetac.
  }
  { eapply IHl; eauto. }
Qed.

Lemma map_shift_correct1 l:
  forall f ts fts
         (SORTED: times_sorted l)
         (IN: List.In ts l),
    map_shift f l ts fts ts = Some fts.
Proof.
  induction l; i; ss.
  inv SORTED. des_ifs.
  { des; clarify.
    { erewrite map_shift_preserved; eauto. des_ifs. }
    { eapply List.Forall_forall in IN; eauto. exfalso. timetac. }
  }
  { des; clarify.
    { exfalso. timetac. }
    { eapply IHl; eauto. }
  }
Qed.

Lemma map_shift_correct2 l:
  forall f ts fts
         (SORTED: times_sorted l)
         to
         (TS: Time.le ts to)
         (IN: List.In to l),
  exists fto,
    (<<MAP: map_shift f l ts fts to = Some fto>>) /\
    (<<TS: Time.le fts fto>>) /\
    (<<LARGER: forall to' (TS: Time.lt to to') (IN: List.In to' l),
        exists fto',
          (<<MAP: map_shift f l ts fts to' = Some fto'>>) /\
          (<<TS: Time.lt fto fto'>>)>>)
.
Proof.
  induction l; ss; i. des; clarify.
  { inv SORTED. des_ifs.
    { exists fts. esplits.
      { erewrite map_shift_preserved; eauto. des_ifs. }
      { refl. }
      { i. des; clarify.
        { exfalso. timetac. }
        { hexploit IHl.
          { eauto. }
          { etrans; [eapply TS|]. left. eauto. }
          { eauto. }
          i. des. esplits.
          { eapply MAP. }
          { eapply TimeFacts.lt_le_lt; eauto. eapply Time.incr_spec. }
        }
      }
    }
    { exfalso. timetac. }
  }
  { inv SORTED. des_ifs.
    { hexploit IHl.
      { eauto. }
      { eapply TS. }
      { eauto. }
      i. des. esplits.
      { eapply MAP. }
      { etrans; eauto. left. eapply Time.incr_spec. }
      { i. des; clarify.
        { exfalso. eapply List.Forall_forall in HD; eauto. exfalso.
          eapply Time.lt_strorder. etrans; eauto.
        }
        { eauto. }
      }
    }
    { hexploit IHl.
      { eauto. }
      { eapply TS. }
      { eauto. }
      i. des. esplits.
      { eapply MAP. }
      { auto. }
      i. des; clarify.
      { exfalso. eapply Time.lt_strorder.
        eapply TimeFacts.lt_le_lt.
        { eapply TS1. }
        etrans.
        { left. eapply l0. }
        { eauto. }
      }
      { hexploit LARGER; eauto. }
    }
  }
Qed.

Lemma map_shift_sound_aux l:
  forall f ts fts to fto
         (MAP: map_shift f l ts fts to = Some fto),
    (<<OLD: f to = Some fto>>) \/
    ((<<NEW: List.In to l>>) /\ (<<TS: Time.le ts to>>)).
Proof.
  induction l; ss; auto. i. des_ifs.
  { eapply IHl in MAP. des; eauto.
    des_ifs; eauto.
  }
  { eapply IHl in MAP; eauto. des; auto. }
Qed.

Lemma map_shift_sound l:
  forall f ts fts to fto
         (MAP: map_shift f l ts fts to = Some fto)
         (TOP: forall to' fto'
                      (MAP: f to' = Some fto'),
             Time.lt fto' fts)
         (SORTED: times_sorted l)
         (FIN: forall to' fto' (MAP: f to' = Some fto'),
             List.In to' l),
    ((<<OLD: f to = Some fto>>) /\ (<<TS: Time.lt to ts>>) /\ (<<TS: Time.lt fto fts>>)) \/
    ((<<NEW: List.In to l>>) /\ (<<TS: Time.le ts to>>) /\ (<<TS: Time.le fts fto>>)).
Proof.
  i. hexploit map_shift_sound_aux; eauto. i. des; auto.
  { destruct (Time.le_lt_dec ts to); auto.
    { right. splits; auto.
      { eapply FIN; eauto. }
      { splits; auto. hexploit map_shift_correct2; eauto.
        i. des. rewrite MAP in MAP0. clarify.
      }
    }
    { left. splits; auto. eapply TOP; eauto. }
  }
  { right. splits; auto.
    hexploit map_shift_correct2; eauto.
    i. des. rewrite MAP in MAP0. clarify.
  }
Qed.

Lemma shifted_mapping_exists (f0: Mapping.t)
      (ts: Time.t) (fts: Time.t)
      (TOP: top_time fts f0)
      (WF: Mapping.wf f0)
  :
    exists f1,
      (<<SAME: forall to fto
                      (TS: Time.lt to ts)
                      (MAP: sim_timestamp_exact f0 f0.(Mapping.ver) fto to),
          sim_timestamp_exact f1 f1.(Mapping.ver) fto to>>) /\
      (<<TS: sim_timestamp_exact f1 f1.(Mapping.ver) fts ts>>) /\
      (<<LE: Mapping.le f0 f1>>) /\
      (<<WF: Mapping.wf f1>>).
Proof.
  hexploit mapping_map_finite_exact; eauto. i. des.
  hexploit (@sorting_sorted (ts::(List.map fst l))); eauto. i. des.
  set (l_sorted := sorting (ts::(List.map fst l))).
  hexploit (@mapping_update_latest_wf f0 (map_shift (f0.(Mapping.map) f0.(Mapping.ver)) l_sorted ts fts) bot1); eauto.
  { eapply map_shift_finite; eauto.
    eapply Mapping.map_finite; eauto. }
  { exists []. ss. }
  { i. hexploit map_shift_sound; [apply MAP0|..]; eauto.
    { i. eapply COMPLETE. right.
      refine (List.in_map fst _ (_, _) _). eapply H; eauto.
    }
    hexploit map_shift_sound; [apply MAP1|..]; eauto.
    { i. eapply COMPLETE. right.
      refine (List.in_map fst _ (_, _) _). eapply H; eauto.
    }
    i. des.
    { eapply Mapping.mapping_map_lt; eauto. }
    { split.
      { i. eapply TimeFacts.lt_le_lt; eauto. }
      { i. eapply TimeFacts.lt_le_lt; eauto. }
    }
    { split.
      { i. exfalso. eapply Time.lt_strorder.
        eapply TimeFacts.lt_le_lt.
        { eapply TS1. }
        etrans.
        { eapply TS. }
        left. auto.
      }
      { i. exfalso. eapply Time.lt_strorder.
        eapply TimeFacts.lt_le_lt.
        { eapply TS2. }
        etrans.
        { eapply TS0. }
        left. auto.
      }
    }
    { destruct (Time.le_lt_dec ts1 ts0).
      { destruct l0; cycle 1.
        { inv H0; clarify. split; i; timetac. }
        assert (Time.lt fts1 fts0).
        { hexploit map_shift_correct2; [..|eapply NEW0|]; eauto.
          i. des. hexploit LARGER; eauto. i. des.
          rewrite MAP0 in MAP2. clarify.
        }
        split; i.
        { exfalso. eapply Time.lt_strorder. etrans; [eapply H2|]; eauto. }
        { exfalso. eapply Time.lt_strorder. etrans; [eapply H1|]; eauto. }
      }
      { split; auto. i.
        hexploit map_shift_correct2; [..|eapply NEW|]; eauto.
        i. des. hexploit LARGER; eauto. i. des.
        rewrite MAP1 in MAP2. clarify.
      }
    }
  }
  { i. destruct (Time.le_lt_dec ts ts0).
    { hexploit map_shift_correct2; eauto.
      { eapply COMPLETE. right.
        refine (List.in_map fst _ (_, _) _). eapply H; eauto.
      }
      { i. des. esplits; eauto.
        exploit TOP; eauto. i. etrans; eauto. left. auto.
      }
    }
    { erewrite map_shift_correct0; eauto. esplits; eauto. refl. }
  }
  i. des. esplits; [..|eapply MAPWF]; eauto.
  { i. unfold sim_timestamp_exact in *.
    rewrite mapping_update_latest_mapping.
    erewrite map_shift_correct0; eauto.
  }
  { unfold sim_timestamp_exact.
    rewrite mapping_update_latest_mapping.
    erewrite map_shift_correct1; eauto.
    eapply COMPLETE. ss. auto.
  }
Qed.



Variant sim_promises
        (flag_src: Loc.t -> option Time.t)
        (flag_tgt: Loc.t -> option Time.t)
        (f: Mapping.ts)
        (vers: versions)
        (* (rmap: ReserveMap.t) *)
        (prom_src prom_tgt: Memory.t): Prop :=
| sim_promises_intro
    (MESSAGE: forall loc to from msg_tgt
                     (FLAGSRC: flag_src loc = None)
                     (GET: Memory.get loc to prom_tgt = Some (from, msg_tgt)),
        exists fto ffrom msg_src,
          (<<FROM: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) ffrom from>>) /\
          (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) fto to>>) /\
          (<<GET: Memory.get loc fto prom_src = Some (ffrom, msg_src)>>) /\
          (<<MSG: sim_message_max (flag_tgt loc) loc fto f (vers loc to) msg_src msg_tgt>>))
    (SOUND: forall loc fto ffrom msg_src
                   (GET: Memory.get loc fto prom_src = Some (ffrom, msg_src)),
        ((exists to from msg_tgt,
             (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) fto to>>) /\
             (<<GET: Memory.get loc to prom_tgt = Some (from, msg_tgt)>>)) \/
         (exists vw, (<<FLAG: flag_tgt loc = Some vw>>) /\ (<<TS: msg_src <> Message.reserve -> Time.lt vw fto>>) /\ (<<SYNC: forall val released (MSG: msg_src = Message.concrete val (Some released)), False>>))))
    (NONE: forall loc to ts
                  (FLAGSRC: flag_src loc = Some ts),
        Memory.get loc to prom_src = None)
.

Lemma sim_promises_get flag_src flag_tgt
      f vers prom_src prom_tgt loc from_tgt to_tgt msg_tgt
      (SIM: sim_promises flag_src flag_tgt f vers prom_src prom_tgt)
      (GET: Memory.get loc to_tgt prom_tgt = Some (from_tgt, msg_tgt))
      (FLAG: flag_src loc = None)
  :
    exists from_src to_src msg_src,
      (<<FROM: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) from_src from_tgt>>) /\
      (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src to_tgt>>) /\
      (<<GET: Memory.get loc to_src prom_src = Some (from_src, msg_src)>>) /\
      (<<MSG: sim_message_max (flag_tgt loc) loc to_src f (vers loc to_tgt) msg_src msg_tgt>>).
Proof.
  inv SIM. hexploit MESSAGE; eauto. i. des. esplits; eauto.
Qed.

Lemma sim_promises_get_if flag_src flag_tgt f vers prom_src prom_tgt loc from_src to_src msg_src
      (SIM: sim_promises flag_src flag_tgt f vers prom_src prom_tgt)
      (GET: Memory.get loc to_src prom_src = Some (from_src, msg_src))
  :
    (exists from_tgt to_tgt msg_tgt,
        (<<FROM: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) from_src from_tgt>>) /\
        (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src to_tgt>>) /\
        (<<GET: Memory.get loc to_tgt prom_tgt = Some (from_tgt, msg_tgt)>>) /\
        (<<MSG: sim_message_max (flag_tgt loc) loc to_src f (vers loc to_tgt) msg_src msg_tgt>>)) \/
    (exists vw, (<<FLAG: flag_tgt loc = Some vw>>) /\ (<<TS: msg_src <> Message.reserve -> Time.lt vw to_src>>) /\ (<<SYNC: forall val released (MSG: msg_src = Message.concrete val (Some released)), False>>))
.
Proof.
  inv SIM. hexploit SOUND; eauto. i. des.
  { hexploit MESSAGE; eauto.
    { destruct (flag_src loc) eqn:FLAG; auto.
      hexploit NONE; eauto. rewrite GET. ss.
    }
    i. des.
    hexploit sim_timestamp_exact_inject.
    { eapply TO. }
    { eapply TO0. }
    i. clarify. left. esplits; eauto.
  }
  { right. esplits; eauto. }
Qed.

Lemma sim_promises_none flag_src flag_tgt ts
      f vers prom_src prom_tgt loc
      (SIM: sim_promises flag_src flag_tgt f vers prom_src prom_tgt)
      (FLAG: flag_src loc = Some ts)
  :
    forall to, Memory.get loc to prom_src = None.
Proof.
  inv SIM. eauto.
Qed.


Lemma add_sim_promises flag_src flag_tgt f vers mem_tgt0 mem_tgt1 mem_src0 mem_src1
      loc from_tgt to_tgt from_src to_src msg_tgt msg_src
      (ADDTGT: Memory.add mem_tgt0 loc from_tgt to_tgt msg_tgt mem_tgt1)
      (PROMS: sim_promises flag_src flag_tgt f vers mem_src0 mem_tgt0)
      (ADDSRC: Memory.add mem_src0 loc from_src to_src msg_src mem_src1)
      (FROM: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) from_src from_tgt)
      (TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src to_tgt)
      (MSG: sim_message_max (flag_tgt loc) loc to_src f (vers loc to_tgt) msg_src msg_tgt)
      (WF: Mapping.wfs f)
      (FLAGSRC: flag_src loc = None)
  :
    sim_promises flag_src flag_tgt f vers mem_src1 mem_tgt1.
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
    { ss. des; clarify. left. esplits; eauto.
      eapply Memory.add_get0; eauto. }
    { guardH o. hexploit sim_promises_get_if; eauto. i. des.
      { left. esplits; eauto. eapply Memory.add_get1; eauto. }
      { right. esplits; eauto. }
    }
  }
  { i. erewrite Memory.add_o; eauto. des_ifs.
    { exfalso. ss. des; clarify. }
    { eapply sim_promises_none; eauto. }
  }
Qed.

Lemma remove_sim_promises flag_src flag_tgt f vers mem_tgt0 mem_tgt1 mem_src0 mem_src1
      loc from_tgt to_tgt from_src to_src msg_tgt msg_src
      (REMOVETGT: Memory.remove mem_tgt0 loc from_tgt to_tgt msg_tgt mem_tgt1)
      (PROMS: sim_promises flag_src flag_tgt f vers mem_src0 mem_tgt0)
      (REMOVESRC: Memory.remove mem_src0 loc from_src to_src msg_src mem_src1)
      (TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src to_tgt)
      (WF: Mapping.wfs f)
  :
    sim_promises flag_src flag_tgt f vers mem_src1 mem_tgt1.
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
    { left. esplits; eauto. erewrite <- GET0.
      erewrite Memory.remove_o; eauto. des_ifs. exfalso.
      unguard. ss. des; clarify.
      eapply o. eapply sim_timestamp_exact_inject; eauto.
    }
    { right. esplits; eauto. }
  }
  { i. erewrite Memory.remove_o; eauto. des_ifs.
    eapply sim_promises_none; eauto.
  }
Qed.

Lemma lower_sim_promises flag_src flag_tgt f vers mem_tgt0 mem_tgt1 mem_src0 mem_src1
      loc from_tgt to_tgt from_src to_src
      msg_tgt0 msg_tgt1 msg_src0 msg_src1
      (LOWERTGT: Memory.lower mem_tgt0 loc from_tgt to_tgt msg_tgt0 msg_tgt1 mem_tgt1)
      (PROMS: sim_promises flag_src flag_tgt f vers mem_src0 mem_tgt0)
      (LOWERSRC: Memory.lower mem_src0 loc from_src to_src msg_src0 msg_src1 mem_src1)
      (TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src to_tgt)
      (MSG: sim_message_max (flag_tgt loc) loc to_src f (vers loc to_tgt) msg_src1 msg_tgt1)
      (WF: Mapping.wfs f)
  :
    sim_promises flag_src flag_tgt f vers mem_src1 mem_tgt1.
Proof.
  pose proof (mapping_latest_wf_loc (f loc)) as VERWF.
  hexploit lower_succeed_wf; [eapply LOWERSRC|]. i. des.
  hexploit lower_succeed_wf; [eapply LOWERTGT|]. i. des.
  assert (FLAGSRC: flag_src loc = None).
  { destruct (flag_src loc) eqn:FLAGSRC; auto. exfalso.
    erewrite sim_promises_none in GET; eauto. ss.
  }
  hexploit sim_promises_get; eauto. i. des.
  eapply sim_timestamp_exact_inject in TO; eauto. clarify.
  econs.
  { i. erewrite Memory.lower_o in GET; eauto. des_ifs.
    { ss. des; clarify. esplits; eauto.
      eapply Memory.lower_get0; eauto. }
    { guardH o. hexploit sim_promises_get; eauto. i. des.
      esplits; eauto. erewrite Memory.lower_o; eauto.
      rewrite <- GET2. des_ifs. exfalso.
      unguard. ss. des; clarify.
      eapply o. eapply sim_timestamp_exact_unique; eauto.
    }
  }
  { i. erewrite Memory.lower_o in GET; eauto. des_ifs.
    { ss. des; clarify. left. esplits; eauto.
      eapply Memory.lower_get0; eauto. }
    { guardH o. hexploit sim_promises_get_if; eauto. i. des.
      { left. esplits; eauto. erewrite Memory.lower_o; eauto.
        rewrite <- GET2. des_ifs. exfalso.
        unguard. ss. des; clarify.
        eapply o. eapply sim_timestamp_exact_inject; eauto.
      }
      { right. esplits; eauto. }
    }
  }
  { i. erewrite Memory.lower_o; eauto. des_ifs.
    { ss. des; clarify. }
    { eapply sim_promises_none; eauto. }
  }
Qed.

Lemma split_sim_promises flag_src flag_tgt f vers mem_tgt0 mem_tgt1 mem_src0 mem_src1
      loc ts_tgt0 ts_tgt1 ts_tgt2 ts_src0 ts_src1 ts_src2
      msg_tgt0 msg_tgt1 msg_src0 msg_src1
      (SPLITTGT: Memory.split mem_tgt0 loc ts_tgt0 ts_tgt1 ts_tgt2 msg_tgt0 msg_tgt1 mem_tgt1)
      (MEM: sim_promises flag_src flag_tgt f vers mem_src0 mem_tgt0)
      (SPLITSRC: Memory.split mem_src0 loc ts_src0 ts_src1 ts_src2 msg_src0 msg_src1 mem_src1)
      (TS1: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) ts_src1 ts_tgt1)
      (TS2: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) ts_src2 ts_tgt2)
      (MSG: sim_message_max (flag_tgt loc) loc ts_src1 f (vers loc ts_tgt1) msg_src0 msg_tgt0)
      (RESERVETGT0: msg_tgt0 <> Message.reserve)
      (RESERVETGT1: msg_tgt1 <> Message.reserve)
      (RESERVESRC1: msg_src1 <> Message.reserve)
      (WF: Mapping.wfs f)
  :
    sim_promises flag_src flag_tgt f vers mem_src1 mem_tgt1.
Proof.
  pose proof (mapping_latest_wf_loc (f loc)) as VERWF.
  hexploit Memory.split_get0; [eapply SPLITTGT|]. i. des.
  hexploit Memory.split_get0; [eapply SPLITSRC|]. i. des. clarify.
  assert (FLAGSRC: flag_src loc = None).
  { destruct (flag_src loc) eqn:FLAGSRC; auto. exfalso.
    erewrite sim_promises_none in GET4; eauto. ss.
  }
  hexploit sim_promises_get; eauto. i. des.
  eapply sim_timestamp_exact_inject in TS2; eauto. clarify.
  econs.
  { i. erewrite Memory.split_o in GET4; eauto. des_ifs.
    { ss. des; clarify. esplits; eauto. }
    { ss. des; clarify. esplits; eauto. }
    { guardH o. guardH o0.
      hexploit sim_promises_get; [|eapply GET4|..]; eauto.
      i. des. esplits; eauto.
      erewrite Memory.split_o; eauto. rewrite <- GET8. des_ifs.
      { exfalso. unguard. ss. des; clarify. }
      { exfalso. unguard. ss. des; clarify.
        eapply o0. eapply sim_timestamp_exact_unique; eauto.   }
    }
  }
  { i. erewrite Memory.split_o in GET4; eauto. des_ifs.
    { ss. des; clarify. left. esplits; eauto. }
    { ss. des; clarify. left. esplits; eauto. }
    { guardH o. guardH o0.
      hexploit sim_promises_get_if; eauto. i. des.
      { left. esplits; eauto. erewrite Memory.split_o; eauto.
        rewrite <- GET8. des_ifs.
        { exfalso. unguard. ss. des; clarify. }
        { exfalso. unguard. ss. des; clarify.
          eapply o0. eapply sim_timestamp_exact_inject; eauto. }
      }
      { right. esplits; eauto. }
    }
  }
  { i. erewrite Memory.split_o; eauto. des_ifs.
    { ss. des; clarify. }
    { ss. des; clarify. }
    { eapply sim_promises_none; eauto. }
  }
Qed.


Lemma src_writtten_sim_promises flag_src flag_tgt0 flag_tgt1
      f vers mem_tgt mem_src loc ts
      (PROMS: sim_promises flag_src flag_tgt0 f vers mem_src mem_tgt)
      (FLAGSRC: flag_src loc = Some ts)
      (FLAGTGT: forall loc0 (NEQ: loc0 <> loc), flag_tgt1 loc0 = flag_tgt0 loc0)
  :
    sim_promises flag_src flag_tgt1 f vers mem_src mem_tgt.
Proof.
  econs.
  { i. hexploit sim_promises_get; eauto. i. des. esplits; eauto.
    destruct (Loc.eq_dec loc0 loc); clarify.
    rewrite FLAGTGT; auto.
  }
  { i. hexploit sim_promises_get_if; eauto. i. des.
    { left. esplits; eauto. }
    { right. destruct (Loc.eq_dec loc0 loc); clarify.
      { hexploit sim_promises_none; eauto. i. rewrite GET in H. clarify. }
      { esplits; eauto. rewrite FLAGTGT; auto. }
    }
  }
  { i. eapply sim_promises_none; eauto. }
Qed.

(* Lemma tgt_written_sim_promises flag_src flag_tgt f vers mem_tgt mem_src loc ts *)
(*       (PROMS: sim_promises flag_src flag_tgt f vers mem_src mem_tgt) *)
(*       (CONSISTENT: forall from to msg (GET: Memory.get loc to mem_src = Some (from, msg)) (RESERVE: msg <> Message.reserve), Time.lt ts to) *)
(*       (FLAGTGT: flag_tgt loc = Some ts) *)
(*   : *)
(*     sim_promises flag_src flag_tgt f vers mem_src mem_tgt. *)
(* Proof. *)
(* Qed. *)

Lemma tgt_write_sim_promises flag_src flag_tgt f vers mem_tgt0 mem_tgt1 mem_src ts
      loc from to msg
      (FULFILLTGT: Memory.remove mem_tgt0 loc from to msg mem_tgt1)
      (PROMS: sim_promises flag_src flag_tgt f vers mem_src mem_tgt0)
      (FLAGTGT: flag_tgt loc = Some ts)
      (CONSISTENT: exists ts_tgt,
          (<<SIM: sim_timestamp (f loc) (f loc).(Mapping.ver) ts ts_tgt>>) /\
          (<<LT: Time.lt ts_tgt to>>))
      (WF: Mapping.wfs f)
  :
    sim_promises flag_src flag_tgt f vers mem_src mem_tgt1.
Proof.
  econs.
  { i. erewrite Memory.remove_o in GET; eauto. des_ifs.
    hexploit sim_promises_get; eauto. i. des.
    { esplits; eauto. }
    { esplits; eauto. }
  }
  { i. hexploit sim_promises_get_if; eauto. i. des.
    { destruct (loc_ts_eq_dec (loc, to) (loc0, to_tgt)).
      { ss. des; clarify. right. esplits; eauto.
        { i. eapply sim_timestamp_lt; eauto.
          eapply mapping_latest_wf_loc.
        }
        { i. subst. rewrite FLAGTGT in *. inv MSG. ss. }
      }
      { left. esplits; eauto.
        erewrite Memory.remove_o; eauto. des_ifs.
        { exfalso. ss. des; clarify. }
        { eauto. }
      }
    }
    { right. esplits; eauto. }
  }
  { i. eapply sim_promises_none; eauto. }
Qed.


Lemma sim_promises_cancel flag_src flag_tgt f vers mem_tgt0 mem_tgt1 mem_src0
      loc from_tgt to_tgt
      (REMOVETGT: Memory.remove mem_tgt0 loc from_tgt to_tgt Message.reserve mem_tgt1)
      (PROMS: sim_promises flag_src flag_tgt f vers mem_src0 mem_tgt0)
      (FLAGSRC: flag_src loc = None)
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

Lemma sim_promises_split flag_src flag_tgt f vers mem_tgt0 mem_tgt1 mem_src0
      loc ts_tgt0 ts_tgt1 ts_tgt2 msg_tgt0 msg_tgt1 msg_src0 ts_src1
      (SPLITTGT: Memory.split mem_tgt0 loc ts_tgt0 ts_tgt1 ts_tgt2 msg_tgt0 msg_tgt1 mem_tgt1)
      (TS: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) ts_src1 ts_tgt1)
      (MSGWF: Message.wf msg_src0)
      (PROMS: sim_promises flag_src flag_tgt f vers mem_src0 mem_tgt0)
      (WF: Mapping.wfs f)
      (FLAGSRC: flag_src loc = None)
  :
    exists ts_src0 ts_src2 msg_src1 mem_src1,
      (<<TS0: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) ts_src0 ts_tgt0>>) /\
      (<<TS2: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) ts_src2 ts_tgt2>>) /\
      (<<MSG: sim_message_max (flag_tgt loc) loc ts_src2 f (vers loc ts_tgt2) msg_src1 msg_tgt1>>)/\
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

Lemma sim_promises_lower flag_src flag_tgt f vers mem_tgt0 mem_tgt1 mem_src0
      loc from_tgt to_tgt to_src msg_tgt0 msg_tgt1 msg_src1
      (LOWERTGT: Memory.lower mem_tgt0 loc from_tgt to_tgt msg_tgt0 msg_tgt1 mem_tgt1)
      (TS: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src to_tgt)
      (MSGWF: Message.wf msg_src1)
      (PROMS: sim_promises flag_src flag_tgt f vers mem_src0 mem_tgt0)
      (MSG: sim_message (flag_tgt loc) loc f (vers loc to_tgt) msg_src1 msg_tgt1)
      (MSGTO: Memory.message_to msg_src1 loc to_src)
      (WF: Mapping.wfs f)
      (FLAGSRC: flag_src loc = None)
  :
    exists from_src msg_src0 mem_src1,
      (<<FROM: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) from_src from_tgt>>) /\
      (<<MSG: sim_message_max (flag_tgt loc) loc to_src f (vers loc to_tgt) msg_src0 msg_tgt0>>)/\
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

Lemma src_fulfill_sim_promises flag_src flag_tgt f vers mem_tgt mem_src0 mem_src1 loc ts
      (PROMS: sim_promises flag_src flag_tgt f vers mem_src0 mem_tgt)
      (WF: Mapping.wfs f)
      (MEM: forall loc' ts',
          Memory.get loc' ts' mem_src1 =
          if Loc.eq_dec loc' loc
          then None
          else Memory.get loc' ts' mem_src0)
  :
    sim_promises (fun loc' => if (Loc.eq_dec loc' loc) then Some ts else flag_src loc') flag_tgt f vers mem_src1 mem_tgt.
Proof.
  econs.
  { i. des_ifs. hexploit sim_promises_get; eauto. i. des.
    esplits; eauto. rewrite MEM; eauto. des_ifs.
  }
  { i. rewrite MEM in GET; eauto. des_ifs.
    hexploit sim_promises_get_if; eauto. i. des.
    { left. esplits; eauto. }
    { right. esplits; eauto. }
  }
  { i. rewrite MEM. des_ifs.
    eapply sim_promises_none; eauto.
  }
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

Lemma sim_timestamp_exact_bot f v
      (WF: Mapping.wf f)
      (VERWF: loc_version_wf f v)
  :
    exists fbot,
      (<<SIM: sim_timestamp_exact f v fbot Time.bot>>) /\
      (<<BOT: forall ts fts (MAP: sim_timestamp_exact f v fts ts),
          Time.le fbot fts>>).
Proof.
  hexploit sim_timestamp_exact_mon_ver.
  { eapply Mapping.mapping_bot; eauto. }
  { lia. }
  { eauto. }
  { eauto. }
  i. des. esplits; eauto. i.
  eapply sim_timestamp_exact_le; eauto. eapply Time.bot_spec.
Qed.

Lemma sim_timestamp_exact_bot_if f v ts
      (WF: Mapping.wf f)
      (VERWF: loc_version_wf f v)
      (SIM: sim_timestamp_exact f v Time.bot ts)
  :
    ts = Time.bot.
Proof.
  eapply TimeFacts.antisym; [|eapply Time.bot_spec].
  hexploit sim_timestamp_exact_bot; eauto. i. des.
  eapply sim_timestamp_exact_le_if; eauto. eapply Time.bot_spec.
Qed.

Definition mapped f ts_tgt: Prop :=
  exists ts_src, sim_timestamp_exact f f.(Mapping.ver) ts_src ts_tgt.

Lemma mapped_mon f0 f1 ts
      (MAPPED: mapped f0 ts)
      (MAPLE: Mapping.le f0 f1)
      (WF0: Mapping.wf f0)
      (WF1: Mapping.wf f1)
  :
    mapped f1 ts.
Proof.
  unfold mapped in *. des.
  hexploit sim_timestamp_exact_mon_ver.
  { erewrite <- sim_timestamp_exact_mon_mapping; eauto. eapply mapping_latest_wf_loc. }
  { eapply MAPLE. }
  { eauto. }
  { eapply mapping_latest_wf_loc. }
  i. des. esplits; eauto.
Qed.

Lemma bot_mapped f
      (WF: Mapping.wf f)
  :
    mapped f Time.bot.
Proof.
  hexploit sim_timestamp_exact_bot; eauto.
  { eapply mapping_latest_wf_loc. }
  i. des. red. eauto.
Qed.

Variant sim_memory
        (flag_src: Loc.t -> option Time.t)
        (f: Mapping.ts)
        (vers: versions)
        (* (rmap: Loc.t -> Time.t -> option Time.t) *)
        (mem_src mem_tgt: Memory.t)
  : Prop :=
| sim_memory_intro
    (MESSAGE: forall loc to from msg_tgt
                     (GET: Memory.get loc to mem_tgt = Some (from, msg_tgt))
                     (RESERVE: msg_tgt <> Message.reserve),
        exists fto ffrom msg_src,
          (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) fto to>>) /\
          (<<GET: Memory.get loc fto mem_src = Some (ffrom, msg_src)>>) /\
          (<<MSG: sim_message false loc f (vers loc to) msg_src msg_tgt>>) /\
          (<<CLOSED: Mapping.closed (f loc) (f loc).(Mapping.ver) fto>>))
    (SOUND: forall loc fto0 ffrom1 msg_src
                   (GET: Memory.get loc fto0 mem_src = Some (ffrom1, msg_src)),
        (exists fto1 ffrom0 to from,
            (<<TS0: Time.le ffrom0 ffrom1>>) /\
            (<<TS1: Time.le fto0 fto1>>) /\
            (<<FROM: __guard__((ffrom0 = Time.bot /\ from = Time.bot) \/ sim_timestamp_exact (f loc) (f loc).(Mapping.ver) ffrom0 from)>>) /\
            (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) fto1 to>>) /\
            (<<COVERED: forall ts (ITV: Interval.mem (from, to) ts),
                covered loc ts mem_tgt>>)) \/
        (exists ts,
            (<<FLAG: flag_src loc = Some ts>>) /\
            (<<TS: Time.le fto0 ts>>) /\
            (<<TOP: top_time ffrom1 (f loc)>>)))
    (TOP: forall loc ts
                 (FLAG: flag_src loc = Some ts),
        top_time ts (f loc))
.

Lemma sim_memory_get flag_src f vers mem_src mem_tgt loc from_tgt to_tgt msg_tgt
      (SIM: sim_memory flag_src f vers mem_src mem_tgt)
      (GET: Memory.get loc to_tgt mem_tgt = Some (from_tgt, msg_tgt))
      (RESERVE: msg_tgt <> Message.reserve)
  :
    exists from_src to_src msg_src,
      (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src to_tgt>>) /\
      (<<GET: Memory.get loc to_src mem_src = Some (from_src, msg_src)>>) /\
      (<<MSG: sim_message false loc f (vers loc to_tgt) msg_src msg_tgt>>) /\
      (<<CLOSED: Mapping.closed (f loc) (f loc).(Mapping.ver) to_src>>).
Proof.
  inv SIM. hexploit MESSAGE; eauto. i. des. esplits; eauto.
Qed.

Lemma sim_memory_sound flag_src f vers mem_src mem_tgt loc fto0 ffrom1 msg_src
      (SIM: sim_memory flag_src f vers mem_src mem_tgt)
      (GET: Memory.get loc fto0 mem_src = Some (ffrom1, msg_src))
  :
    (exists fto1 ffrom0 to from,
        (<<TS0: Time.le ffrom0 ffrom1>>) /\
        (<<TS1: Time.le fto0 fto1>>) /\
        (<<FROM: __guard__((ffrom0 = Time.bot /\ from = Time.bot) \/ sim_timestamp_exact (f loc) (f loc).(Mapping.ver) ffrom0 from)>>) /\
        (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) fto1 to>>) /\
        (<<COVERED: forall ts (ITV: Interval.mem (from, to) ts),
            covered loc ts mem_tgt>>)) \/
    (exists ts,
        (<<FLAG: flag_src loc = Some ts>>) /\
        (<<TS: Time.le fto0 ts>>) /\
        (<<TOP: top_time ffrom1 (f loc)>>)).
Proof.
  inv SIM. eauto.
Qed.

Lemma sim_memory_top flag_src f vers mem_src mem_tgt loc ts
      (SIM: sim_memory flag_src f vers mem_src mem_tgt)
      (FLAG: flag_src loc = Some ts)
  :
    top_time ts (f loc).
Proof.
  inv SIM. eauto.
Qed.

Lemma sim_memory_sound_strong flag_src f vers mem_src mem_tgt loc fto0 ffrom1 msg_src
      (SIM: sim_memory flag_src f vers mem_src mem_tgt)
      (GET: Memory.get loc fto0 mem_src = Some (ffrom1, msg_src))
      (WF: Mapping.wfs f)
  :
    (exists fto1 ffrom0 to from,
        (<<TS0: Time.le ffrom0 ffrom1>>) /\
        (<<TS1: Time.le fto0 fto1>>) /\
        (<<FROM: __guard__((ffrom0 = Time.bot /\ from = Time.bot) \/ sim_timestamp_exact (f loc) (f loc).(Mapping.ver) ffrom0 from)>>) /\
        (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) fto1 to>>) /\
        (<<COVERED: forall ts (ITV: Interval.mem (from, to) ts),
            covered loc ts mem_tgt>>) /\
        (<<MAX: forall from' ffrom'
                       (MAP: __guard__((ffrom' = Time.bot /\ from' = Time.bot) \/ sim_timestamp_exact (f loc) (f loc).(Mapping.ver) ffrom' from'))
                       (TS: Time.le ffrom' ffrom1),
            Time.le ffrom' ffrom0>>) /\
        (<<MIN: forall to' fto'
                       (MAP: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) fto' to')
                       (TS: Time.le fto0 fto'),
            Time.le fto1 fto'>>)) \/
    (exists ts,
        (<<FLAG: flag_src loc = Some ts>>) /\
        (<<TS: Time.le fto0 ts>>) /\
        (<<TOP: top_time ffrom1 (f loc)>>)).
Proof.
  pose proof (mapping_latest_wf_loc (f loc)) as VERWF.
  inv SIM. hexploit SOUND; eauto. i. des; eauto. left.
  hexploit mapping_map_finite_exact; eauto. i. des.
  hexploit (@finite_greatest (fun ts => Time.le ts ffrom1) (Time.bot::(List.map snd l))). i. des; cycle 1.
  { exfalso. unguard. des.
    { eapply EMPTY.
      { left. auto. }
      { eapply Time.bot_spec. }
    }
    { eapply EMPTY.
      { right. eapply List.in_map. eapply H. eapply FROM. }
      { eauto. }
    }
  }
  hexploit (@finite_least (fun ts => Time.le fto0 ts) (List.map snd l)). i. des; cycle 1.
  { exfalso. eapply EMPTY.
    { eapply List.in_map. eapply H. eapply TO. }
    { eauto. }
  }
  assert (exists t0, __guard__((to0 = Time.bot /\ t0 = Time.bot) \/ sim_timestamp_exact (f loc) (Mapping.ver (f loc)) to0 t0)).
  { ss. des.
    { exists Time.bot. left. auto. }
    { eapply List.in_map_iff in IN. des. clarify.
      destruct x. eapply H in IN1. esplits. right. eauto.
    }
  }
  des. clear IN.
  eapply List.in_map_iff in IN0. des. clarify.
  destruct x. eapply H in IN1. ss.
  eexists t1, to0. esplits; eauto.
  { i. eapply COVERED. eapply Interval.le_mem; eauto. econs; eauto; ss.
    { unguard. des; clarify; try by eapply Time.bot_spec.
      { hexploit (GREATEST ffrom0); eauto.
        { right. refine (List.in_map snd _ (_, _) _). eapply H; eauto. }
        i. destruct (Time.le_lt_dec from Time.bot); auto.
        hexploit sim_timestamp_lt.
        { eapply sim_timestamp_bot; eauto. }
        { eapply FROM. }
        { eauto. }
        { eauto. }
        { eauto. }
        i. exfalso. timetac.
      }
      { eapply sim_timestamp_exact_le_if; eauto.
        eapply GREATEST; eauto. right. refine (List.in_map snd _ (_, _) _).
        eapply H; eauto.
      }
    }
    { eapply sim_timestamp_exact_le_if; eauto.
      eapply LEAST; eauto. refine (List.in_map snd _ (_, _) _).
      eapply H; eauto.
    }
  }
  { i. eapply GREATEST; eauto. inv MAP; des; clarify; auto.
    right. refine (List.in_map snd _ (_, _) _). eapply H; eauto.
  }
  { i. eapply LEAST; eauto.
    refine (List.in_map snd _ (_, _) _). eapply H; eauto.
  }
Qed.

Lemma sim_memory_attach flag_src f vers mem_src mem_tgt loc ts_tgt ts_src
      (SIM: sim_memory flag_src f vers mem_src mem_tgt)
      (TS: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) ts_src ts_tgt)
      (ATTACH: forall to' msg'
                      (GET: Memory.get loc to' mem_tgt = Some (ts_tgt, msg')), False)
      (COVER: ~ covered loc ts_tgt mem_tgt)
      (NBOT: Time.lt Time.bot ts_tgt)
      (WF: Mapping.wfs f)
      (FLAG: flag_src loc = None)
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
    { i. eapply COVERED. inv ITV. econs; ss.
      eapply TimeFacts.le_lt_lt; eauto.
      unguard. des; clarify.
      { eapply Time.bot_spec. }
      { eapply sim_timestamp_exact_le_if; eauto. }
    }
    i. des. inv TS2.
    { eapply COVER. econs; eauto. econs; ss.
      left. auto. }
    { inv H. eapply ATTACH; eauto. }
  }
  { clarify. }
Qed.

Lemma sim_memory_space flag_src f vers mem_src mem_tgt loc from_tgt to_tgt from_src to_src
      (SIM: sim_memory flag_src f vers mem_src mem_tgt)
      (FROM: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) from_src from_tgt)
      (TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src to_tgt)
      (TS: Time.lt from_tgt to_tgt)
      (DISJOINT: forall to2 from2 msg2
                        (GET: Memory.get loc to2 mem_tgt = Some (from2, msg2)),
          Interval.disjoint (from_tgt, to_tgt) (from2, to2))
      (WF: Mapping.wfs f)
      (FLAG: flag_src loc = None)
  :
    forall to2 from2 msg2
           (GET: Memory.get loc to2 mem_src = Some (from2, msg2)),
      Interval.disjoint (from_src, to_src) (from2, to2).
Proof.
  pose proof (mapping_latest_wf_loc (f loc)) as VERWF.
  eapply covered_disjoint_get_disjoint. ii. inv H.
  hexploit sim_memory_sound; eauto. i. des.
  { assert (Interval.disjoint (from0, to0) (from_tgt, to_tgt)).
    { ii. eapply (get_disjoint_covered_disjoint DISJOINT); eauto. }
    assert (DISJ: Interval.disjoint (ffrom0, fto1) (from_src, to_src)).
    { unguard. des.
      { clarify. hexploit (@sim_timestamp_exact_bot (f loc) (f loc).(Mapping.ver)); eauto.
        i. des. eapply sim_disjoint in H; cycle 1; eauto.
        ii. eapply H; eauto.
        inv LHS. econs; ss.
        inv RHS. ss. eapply TimeFacts.le_lt_lt; [|eauto].
        eapply BOT; eauto.
      }
      { eapply sim_disjoint; eauto. }
    }
    eapply (DISJ ts); auto.
    inv ITV. econs; ss.
    { eapply TimeFacts.le_lt_lt; eauto. }
    { etrans; eauto. }
  }
  { clarify. }
Qed.

Lemma add_sim_memory flag_src f vers mem_tgt0 mem_tgt1 mem_src0 mem_src1
      loc from_tgt to_tgt from_src to_src msg_tgt msg_src
      (ADDTGT: Memory.add mem_tgt0 loc from_tgt to_tgt msg_tgt mem_tgt1)
      (MEM: sim_memory flag_src f vers mem_src0 mem_tgt0)
      (ADDSRC: Memory.add mem_src0 loc from_src to_src msg_src mem_src1)
      (FROM: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) from_src from_tgt)
      (TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src to_tgt)
      (CLOSED: Mapping.closed (f loc) (f loc).(Mapping.ver) to_src)
      (MSG: sim_message false loc f (vers loc to_tgt) msg_src msg_tgt)
      (WF: Mapping.wfs f)
  :
    sim_memory flag_src f vers mem_src1 mem_tgt1.
Proof.
  econs.
  { i. erewrite Memory.add_o in GET; eauto. des_ifs.
    { ss. des; clarify. esplits; eauto.
      eapply Memory.add_get0; eauto.
    }
    { guardH o. hexploit sim_memory_get; eauto. i. des.
      esplits; eauto. erewrite Memory.add_o; eauto. des_ifs; eauto.
      exfalso. ss. des; clarify. unguard. des; ss.
      eapply o. eapply sim_timestamp_exact_unique; eauto.
      eapply mapping_latest_wf_loc.
    }
  }
  { i. erewrite Memory.add_o in GET; eauto. des_ifs.
    { ss. des; clarify. left. esplits.
      { refl. }
      { refl. }
      { right. eauto. }
      { eauto. }
      i. econs.
      { eapply Memory.add_get0; eauto. }
      { eauto. }
    }
    { guardH o. hexploit sim_memory_sound; eauto. i. des.
      { left. esplits; eauto. i. eapply COVERED in ITV.
        eapply add_covered; eauto.
      }
      { right. esplits; eauto. }
    }
  }
  { i. eapply sim_memory_top; eauto. }
Qed.

Lemma remove_sim_memory flag_src f vers mem_tgt0 mem_tgt1 mem_src0 mem_src1
      loc from_tgt to_tgt from_src to_src
      (REMOVETGT: Memory.remove mem_tgt0 loc from_tgt to_tgt Message.reserve mem_tgt1)
      (MEM: sim_memory flag_src f vers mem_src0 mem_tgt0)
      (REMOVESRC: Memory.remove mem_src0 loc from_src to_src Message.reserve mem_src1)
      (TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src to_tgt)
      (FROM: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) from_src from_tgt)
      (WF: Mapping.wfs f)
  :
    sim_memory flag_src f vers mem_src1 mem_tgt1.
Proof.
  pose proof (mapping_latest_wf_loc (f loc)) as VERWF.
  econs.
  { i. erewrite Memory.remove_o in GET; eauto. des_ifs.
    guardH o. hexploit sim_memory_get; eauto. i. des.
    esplits; eauto. erewrite Memory.remove_o; eauto. des_ifs; eauto.
    exfalso. ss. des; clarify. unguard. des; ss.
    eapply o. eapply sim_timestamp_exact_unique; eauto.
  }
  { i. erewrite Memory.remove_o in GET; eauto. des_ifs.
    guardH o. hexploit sim_memory_sound_strong; eauto. i. des; eauto.
    left. esplits; eauto. i. eapply remove_covered; eauto.
    splits; auto. eapply not_and_or. ii. des; subst.
    destruct FROM0 as [FROM0|FROM0]; des; clarify.
    { hexploit (@sim_timestamp_exact_bot (f loc) (f loc).(Mapping.ver)); eauto. i. des.
      eapply sim_disjoint_if; [..|eapply ITV|eapply H0]; eauto.
      ii. ss.
      hexploit memory_get_disjoint_strong.
      { eapply GET. }
      { eapply Memory.remove_get0; eauto. }
      i. unguard. des; clarify.
      { hexploit MIN; [|eapply TS|..]; eauto. i.
        inv LHS. inv RHS. ss.
        eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
        { eapply FROM1. }
        etrans.
        { eapply TO1. }
        { eauto. }
      }
      { hexploit MAX; [|eapply TS|..]; eauto. i.
        inv LHS. inv RHS. ss.
        eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
        { eapply FROM0. }
        etrans.
        { eapply TO2. }
        etrans.
        { eapply H. }
        { eapply Time.bot_spec. }
      }
    }
    { eapply sim_disjoint_if; [..|eapply ITV|eapply H0]; eauto.
      ii. ss.
      hexploit memory_get_disjoint_strong.
      { eapply GET. }
      { eapply Memory.remove_get0; eauto. }
      i. unguard. des; clarify.
      { hexploit MIN; [|eapply TS|..]; eauto. i.
        inv LHS. inv RHS. ss.
        eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
        { eapply FROM2. }
        etrans.
        { eapply TO1. }
        { eauto. }
      }
      { hexploit MAX; [|eapply TS|..]; eauto. i.
        inv LHS. inv RHS. ss.
        eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
        { eapply FROM1. }
        etrans.
        { eapply TO2. }
        { eauto. }
      }
    }
  }
  { i. eapply sim_memory_top; eauto. }
Qed.

Lemma split_sim_memory flag_src f vers mem_tgt0 mem_tgt1 mem_src0 mem_src1
      loc ts_tgt0 ts_tgt1 ts_tgt2 ts_src0 ts_src1 ts_src2
      msg_tgt0 msg_tgt1 msg_src0 msg_src1
      (SPLITTGT: Memory.split mem_tgt0 loc ts_tgt0 ts_tgt1 ts_tgt2 msg_tgt0 msg_tgt1 mem_tgt1)
      (MEM: sim_memory flag_src f vers mem_src0 mem_tgt0)
      (SPLITSRC: Memory.split mem_src0 loc ts_src0 ts_src1 ts_src2 msg_src0 msg_src1 mem_src1)
      (TS: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) ts_src1 ts_tgt1)
      (MSG: sim_message false loc f (vers loc ts_tgt1) msg_src0 msg_tgt0)
      (CLOSED: Mapping.closed (f loc) (f loc).(Mapping.ver) ts_src1)
      (RESERVETGT0: msg_tgt0 <> Message.reserve)
      (RESERVETGT1: msg_tgt1 <> Message.reserve)
      (RESERVESRC1: msg_src1 <> Message.reserve)
      (WF: Mapping.wfs f)
      (FLAG: flag_src loc = None)
  :
    sim_memory flag_src f vers mem_src1 mem_tgt1.
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
      { i. eapply split_covered; eauto. }
    }
    { ss. des; clarify. left. esplits; [| |eapply FROM|eapply TO|..].
      { hexploit split_succeed_wf; [eapply SPLITSRC|]. i. des.
        etrans; eauto. left. auto. }
      { hexploit split_succeed_wf; [eapply SPLITSRC|]. i. des. auto. }
      { i. eapply split_covered; eauto. }
    }
    { guardH o. guardH o0.
      hexploit sim_memory_sound; [|eapply GET7|..]; eauto. i. des.
      { left. esplits; eauto. i.
        eapply split_covered; eauto. }
      { right. esplits; eauto. }
    }
  }
  { i. eapply sim_memory_top; eauto. }
Qed.

Lemma lower_sim_memory flag_src f vers mem_tgt0 mem_tgt1 mem_src0 mem_src1
      loc from_tgt to_tgt from_src to_src
      msg_tgt0 msg_tgt1 msg_src0 msg_src1
      (LOWERTGT: Memory.lower mem_tgt0 loc from_tgt to_tgt msg_tgt0 msg_tgt1 mem_tgt1)
      (MEM: sim_memory flag_src f vers mem_src0 mem_tgt0)
      (LOWERSRC: Memory.lower mem_src0 loc from_src to_src msg_src0 msg_src1 mem_src1)
      (TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src to_tgt)
      (MSG: sim_message false loc f (vers loc to_tgt) msg_src1 msg_tgt1)
      (RESERVE: msg_tgt1 <> Message.reserve)
      (WF: Mapping.wfs f)
  :
    sim_memory flag_src f vers mem_src1 mem_tgt1.
Proof.
  econs.
  { i. erewrite Memory.lower_o in GET; eauto. des_ifs.
    { ss. des; clarify. esplits; eauto.
      { eapply Memory.lower_get0; eauto. }
      { eapply lower_succeed_wf in LOWERTGT. des.
        hexploit sim_memory_get; eauto.
        { inv MSG_LE; ss. }
        i. des. eapply sim_timestamp_exact_inject in TO; eauto.
        subst. auto.
      }
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
      { left. esplits; eauto. i. eapply lower_covered; eauto. }
      { right. esplits; eauto. }
    }
    { guardH o. hexploit sim_memory_sound; eauto. i. des.
      { left. esplits; eauto. i. eapply lower_covered; eauto. }
      { right. esplits; eauto. }
    }
  }
  { i. eapply sim_memory_top; eauto. }
Qed.

Lemma sim_memory_add flag_src f vers mem_tgt0 mem_tgt1 mem_src0
      loc from_tgt to_tgt from_src to_src msg_tgt msg_src
      (ADDTGT: Memory.add mem_tgt0 loc from_tgt to_tgt msg_tgt mem_tgt1)
      (MEM: sim_memory flag_src f vers mem_src0 mem_tgt0)
      (MSG: sim_message false loc f (vers loc to_tgt) msg_src msg_tgt)
      (FROM: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) from_src from_tgt)
      (TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src to_tgt)
      (WF: Mapping.wfs f)
      (MSGWF: Message.wf msg_src)
      (FLAG: flag_src loc = None)
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

Lemma lower_src_sim_memory flag_src f vers mem_tgt mem_src0 mem_src1
      loc from to msg0 val
      (MEM: sim_memory flag_src f vers mem_src0 mem_tgt)
      (LOWERSRC: Memory.lower mem_src0 loc from to msg0 (Message.concrete val None) mem_src1)
  :
    sim_memory flag_src f vers mem_src1 mem_tgt.
Proof.
  hexploit lower_succeed_wf; eauto. i. des.
  econs.
  { i. hexploit sim_memory_get; eauto. i. des.
    hexploit (@Memory.lower_o _ _ _ _ _ _ _ loc0 to_src LOWERSRC). i. des_ifs.
    { ss. des; clarify. esplits; eauto.
      inv MSG; inv MSG_LE.
      { econs; eauto.
        { etrans; eauto. }
        { econs. }
      }
      { econs; eauto.
        { etrans; eauto. }
        { econs. }
      }
    }
    { rewrite GET1 in H. esplits; eauto. }
  }
  { i. assert (exists msg_src', (<<GET: Memory.get loc0 fto0 mem_src0 = Some (ffrom1, msg_src')>>) /\ (<<MSG: Message.le msg_src msg_src'>>)).
    { erewrite Memory.lower_o in GET0; eauto. des_ifs; eauto.
      { ss. des; clarify. eauto. }
      { esplits; eauto. refl. }
    }
    des. hexploit sim_memory_sound; eauto.
  }
  { i. eapply sim_memory_top; eauto. }
Qed.

Lemma add_src_sim_memory flag_src f vers mem_tgt mem_src0 mem_src1 ts
      loc from to msg
      (MEM: sim_memory flag_src f vers mem_src0 mem_tgt)
      (ADDSRC: Memory.add mem_src0 loc from to msg mem_src1)
      (FLAG: flag_src loc = Some ts)
      (TS: Time.le ts from)
  :
    sim_memory ((fun loc' => if (Loc.eq_dec loc' loc) then (Some to) else flag_src loc')) f vers mem_src1 mem_tgt.
Proof.
  assert (TOPLE: Time.le ts to).
  { etrans; eauto. left. eapply add_succeed_wf; eauto. }
  econs.
  { i. hexploit sim_memory_get; eauto. i. des.
    esplits; eauto. eapply Memory.add_get1; eauto. }
  { i. erewrite Memory.add_o in GET; eauto.
    destruct (loc_ts_eq_dec (loc0, fto0) (loc, to)).
    { ss. des; clarify. right. des_ifs. esplits; eauto.
      { refl. }
      { eapply top_time_mon.
        { eapply sim_memory_top; eauto. }
        { auto. }
      }
    }
    { guardH o. hexploit sim_memory_sound; eauto. i. des.
      { left. esplits; eauto. }
      { right. des_ifs.
        { esplits; eauto. }
        { esplits; eauto. }
      }
    }
  }
  { i. des_ifs.
    { eapply top_time_mon.
      { eapply sim_memory_top; eauto. }
      { auto. }
    }
    { eapply sim_memory_top; eauto. }
  }
Qed.

Lemma src_write_sim_memory flag_src f vers mem_tgt mem_src loc ts
      (MEM: sim_memory flag_src f vers mem_src mem_tgt)
      (FLAG: flag_src loc = None)
      (TOP: top_time ts (f loc))
  :
    sim_memory (fun loc' => if (Loc.eq_dec loc' loc) then (Some ts) else flag_src loc') f vers mem_src mem_tgt.
Proof.
  econs.
  { i. hexploit sim_memory_get; eauto. i. des. esplits; eauto. }
  { i. hexploit sim_memory_sound; eauto. i. des.
    { left. esplits; eauto. }
    { right. esplits; eauto. des_ifs. }
  }
  { i. des_ifs. eapply sim_memory_top; eauto. }
Qed.

Variant versioned_memory (vers: versions) (mem: Memory.t): Prop :=
| versioned_memory_intro
    (COMPLETE: forall loc to from val released
                      (GET: Memory.get loc to mem = Some (from, Message.concrete val (Some released))),
        exists ver,
          (<<VER: vers loc to = Some ver>>) /\
          (<<FROM: forall ver_from (VER: vers loc from = Some ver_from),
              version_le ver_from ver>>))
    (SOUND: forall loc to ver (VER: vers loc to = Some ver),
        exists from val released,
          (<<GET: Memory.get loc to mem = Some (from, Message.concrete val released)>>))
.

Lemma versioned_memory_lower vers mem0 loc from to msg0 msg1 mem1
      (LOWER: Memory.lower mem0 loc from to msg0 msg1 mem1)
      (VERS: versioned_memory vers mem0)
  :
    versioned_memory vers mem1.
Proof.
  inv VERS. econs.
  { i. erewrite Memory.lower_o in GET; eauto. des_ifs.
    { ss. des; clarify.
      hexploit lower_succeed_wf; eauto. i. des.
      inv MSG_LE. inv RELEASED.
      eapply COMPLETE; eauto.
    }
    { eapply COMPLETE; eauto. }
  }
  { i. hexploit SOUND; eauto. i. des.
    eapply Memory.lower_get1 in GET; eauto. des. inv MSG_LE. eauto.
  }
Qed.

Lemma versioned_memory_cancel vers mem0 loc from to mem1
      (CANCEL: Memory.remove mem0 loc from to Message.reserve mem1)
      (VERS: versioned_memory vers mem0)
  :
    versioned_memory vers mem1.
Proof.
  inv VERS. econs.
  { i. erewrite Memory.remove_o in GET; eauto. des_ifs.
    eapply COMPLETE; eauto.
  }
  { i. hexploit SOUND; eauto. i. des.
    exists from0, val, released. erewrite Memory.remove_o; eauto. des_ifs.
    ss. des; clarify. eapply Memory.remove_get0 in CANCEL. des. clarify.
  }
Qed.

Lemma versioned_memory_cap vers mem0 mem1
      (CAP: Memory.cap mem0 mem1)
      (VERS: versioned_memory vers mem0)
      (CLOSED: Memory.closed mem0)
  :
    versioned_memory vers mem1.
Proof.
  inv VERS. econs.
  { i. eapply Memory.cap_inv in GET; eauto. des; clarify.
    eapply COMPLETE; eauto.
  }
  { i. hexploit SOUND; eauto. i. des.
    eapply Memory.cap_le in GET; eauto. refl.
  }
Qed.

Lemma versioned_memory_add_non_concrete vers mem0 loc from to msg mem1
      (ADD: Memory.add mem0 loc from to msg mem1)
      (VERS: versioned_memory vers mem0)
      (CONCRETE: forall val released, msg <> Message.concrete val (Some released))
  :
    versioned_memory vers mem1.
Proof.
  inv VERS. econs; eauto.
  { i. erewrite Memory.add_o in GET; eauto. des_ifs.
    { ss. des; clarify. exfalso. eapply CONCRETE; eauto. }
    { eapply COMPLETE; eauto. }
  }
  { i. hexploit SOUND; eauto. i. des. eapply Memory.add_get1 in GET; eauto. }
Qed.

Lemma versioned_memory_add vers mem0 loc from to val released mem1 v
      (ADD: Memory.add mem0 loc from to (Message.concrete val released) mem1)
      (VERS: versioned_memory vers mem0)
      (ATTACH: forall (to' : Time.t) (msg' : Message.t)
                      (GET: Memory.get loc to' mem0 = Some (to, msg')),
          False)
  :
    versioned_memory (fun loc' ts' => if loc_ts_eq_dec (loc', ts') (loc, to) then opt_version_join (vers loc from) (Some v) else (vers loc' ts')) mem1.
Proof.
  hexploit add_succeed_wf; eauto. i. des.
  inv VERS. econs; eauto.
  { i. erewrite Memory.add_o in GET; eauto. des_ifs.
    { ss. des; clarify. exfalso. timetac. }
    { ss. des; clarify. destruct (vers loc from0); ss.
      { esplits; eauto. i. clarify. eapply version_join_l. }
      { esplits; eauto. ii. clarify. }
    }
    { ss. des; clarify. exfalso. eapply ATTACH; eauto. }
    { eapply COMPLETE; eauto. }
  }
  { i. des_ifs.
    { ss. des; clarify. esplits. eapply Memory.add_get0; eauto. }
    { erewrite Memory.add_o; eauto. des_ifs.
      { ss. des; clarify. }
      eapply SOUND; eauto.
    }
  }
Qed.

Lemma versioned_memory_split_non_concrete vers mem0 loc ts0 ts1 ts2 msg0 msg1 mem1
      (SPLIT: Memory.split mem0 loc ts0 ts1 ts2 msg0 msg1 mem1)
      (VERS: versioned_memory vers mem0)
      (CONCRETE: forall val released, msg0 <> Message.concrete val (Some released))
  :
    versioned_memory vers mem1.
Proof.
  hexploit split_succeed_wf; eauto. i. des.
  hexploit Memory.split_get0; eauto. i. des. clarify.
  inv VERS. econs; eauto.
  { i. erewrite Memory.split_o in GET4; eauto. des_ifs.
    { ss. des; clarify. exfalso. eapply CONCRETE; eauto. }
    { ss. des; clarify. hexploit COMPLETE; eauto. i. des.
      esplits; eauto. i. eapply SOUND in VER0; eauto. des. clarify.
    }
    { eapply COMPLETE; eauto. }
  }
  { i. hexploit SOUND; eauto. i. des.
    eapply Memory.split_get1 in GET4; eauto. des.
    esplits; eauto.
  }
Qed.

Lemma versioned_memory_split_concrete vers mem0 loc ts0 ts1 ts2 val released msg1 mem1 v
      (SPLIT: Memory.split mem0 loc ts0 ts1 ts2 (Message.concrete val released) msg1 mem1)
      (VERS: versioned_memory vers mem0)
      (VER: forall val0 released0 (MSG: msg1 = Message.concrete val0 (Some released0)),
          opt_version_le (Some v) (vers loc ts2))
  :
    versioned_memory (fun loc' ts' => if loc_ts_eq_dec (loc', ts') (loc, ts1) then opt_version_join (vers loc ts0) (Some v) else (vers loc' ts')) mem1.
Proof.
  hexploit split_succeed_wf; eauto. i. des.
  hexploit Memory.split_get0; eauto. i. des. clarify.
  inv VERS. econs; eauto.
  { i. erewrite Memory.split_o in GET4; eauto. des_ifs.
    { ss. des; clarify. exfalso. timetac. }
    { ss. des; clarify. destruct (vers loc from); ss.
      { esplits; eauto. i. clarify. eapply version_join_l. }
      { esplits; eauto. i. clarify. }
    }
    { ss. des; clarify.
      hexploit COMPLETE; eauto. i. des.
      hexploit VER; eauto. i. rewrite VER0 in *. esplits; eauto.
      i. destruct (vers loc ts0) eqn:VER2; ss; clarify.
      eapply version_join_spec; eauto.
    }
    { ss. des; clarify. exfalso.
      hexploit (@memory_get_from_inj mem1 loc ts1 ts2 to); eauto.
      { instantiate (1:=Message.concrete val0 (Some released0)).
        erewrite Memory.split_o; eauto. des_ifs; ss; des; clarify.
      }
      { i. des; clarify. }
    }
    { ss. des; clarify. }
    { eapply COMPLETE; eauto. }
  }
  { i. des_ifs.
    { ss. des; clarify. eauto. }
    { guardH o. eapply SOUND in VER0. des.
      eapply Memory.split_get1 in GET4; eauto. des. esplits; eauto.
    }
  }
Qed.

Lemma loc_version_wf_mapping_mon f0 f1 ver
      (WF: loc_version_wf f0 ver)
      (LE: Mapping.le f0 f1)
  :
    loc_version_wf f1 ver.
Proof.
  unfold loc_version_wf in *. etrans; eauto. eapply LE.
Qed.

Lemma version_wf_mapping_mon f0 f1 ver
      (WF: version_wf f0 ver)
      (LE: Mapping.les f0 f1)
  :
    version_wf f1 ver.
Proof.
  ii. eapply loc_version_wf_mapping_mon; eauto.
Qed.

Lemma opt_version_wf_mapping_mon f0 f1 ver
      (WF: opt_version_wf f0 ver)
      (LE: Mapping.les f0 f1)
  :
    opt_version_wf f1 ver.
Proof.
  destruct ver; ss. eapply version_wf_mapping_mon; eauto.
Qed.

Lemma versions_wf_mapping_mon f0 f1 vers
      (WF: versions_wf f0 vers)
      (LE: Mapping.les f0 f1)
  :
    versions_wf f1 vers.
Proof.
  ii. eapply opt_version_wf_mapping_mon; eauto.
Qed.

Lemma sim_timemap_mon_latest L f0 f1 tm_src tm_tgt
      (SIM: sim_timemap L f0 (Mapping.vers f0) tm_src tm_tgt)
      (LE: Mapping.les f0 f1)
      (WF0: Mapping.wfs f0)
      (WF1: Mapping.wfs f1)
  :
    sim_timemap L f1 (Mapping.vers f1) tm_src tm_tgt.
Proof.
  eapply sim_timemap_mon_ver; auto.
  { erewrite <- sim_timemap_mon_mapping; eauto. eapply mapping_latest_wf. }
  { eapply version_le_version_wf.
    eapply version_wf_mapping_mon; eauto. eapply mapping_latest_wf.
  }
  { eapply mapping_latest_wf. }
Qed.

Lemma sim_view_mon_latest L f0 f1 vw_src vw_tgt
      (SIM: sim_view L f0 (Mapping.vers f0) vw_src vw_tgt)
      (LE: Mapping.les f0 f1)
      (WF0: Mapping.wfs f0)
      (WF1: Mapping.wfs f1)
  :
    sim_view L f1 (Mapping.vers f1) vw_src vw_tgt.
Proof.
  econs.
  { eapply sim_timemap_mon_latest; eauto. eapply SIM. }
  { eapply sim_timemap_mon_latest; eauto. eapply SIM. }
Qed.

Lemma sim_closed_mon_latest f0 f1 ts
      (CLOSED: Mapping.closed f0 f0.(Mapping.ver) ts)
      (LE: Mapping.le f0 f1)
      (WF0: Mapping.wf f0)
      (WF1: Mapping.wf f1)
  :
    Mapping.closed f1 f1.(Mapping.ver) ts.
Proof.
  eapply sim_closed_mon_ver.
  { erewrite <- sim_closed_mon_mapping; [..|eauto]; eauto.
    eapply mapping_latest_wf_loc.
  }
  { eapply LE. }
  { eauto. }
  { eapply mapping_latest_wf_loc. }
Qed.

Lemma sim_memory_mon_strong flag_src f0 f1 vers mem_src mem_tgt
      (SIM: sim_memory flag_src f0 vers mem_src mem_tgt)
      (LE: Mapping.les_strong f0 f1)
      (WF0: Mapping.wfs f0)
      (WF1: Mapping.wfs f1)
      (VERS: versions_wf f0 vers)
      (SAME: forall loc ts (FLAG: flag_src loc = Some ts), f1 loc = f0 loc)
  :
    sim_memory flag_src f1 vers mem_src mem_tgt.
Proof.
  econs.
  { ii. hexploit sim_memory_get; eauto. i. des. esplits; eauto.
    { eapply sim_timestamp_exact_mon_strong; eauto. }
    { erewrite <- sim_message_mon_mapping; eauto.
      eapply Mapping.les_strong_les; eauto.
    }
    { eapply sim_closed_mon_latest; eauto.
      eapply Mapping.le_strong_le; eauto.
    }
  }
  { i. hexploit sim_memory_sound; eauto. i. des.
    { left. esplits; eauto.
      { unguard. des; clarify; auto. right. eapply sim_timestamp_exact_mon_strong; eauto. }
      { eapply sim_timestamp_exact_mon_strong; eauto. }
    }
    { right. esplits; eauto. erewrite SAME; eauto. }
  }
  { i. erewrite SAME; eauto. eapply sim_memory_top; eauto. }
Qed.

Lemma cap_sim_memory f0 vers mem_tgt0 mem_tgt1 mem_src0 mem_src1
      (MEM: sim_memory (fun _ => None) f0 vers mem_src0 mem_tgt0)
      (WF: Mapping.wfs f0)
      (CAPTGT: Memory.cap mem_tgt0 mem_tgt1)
      (CAPSRC: Memory.cap mem_src0 mem_src1)
      (CLOSEDTGT: Memory.closed mem_tgt0)
      (CLOSEDSRC: Memory.closed mem_src0)
      (VERS: versions_wf f0 vers)
  :
    exists f1,
      (<<SIM: sim_memory (fun _ => None) f1 vers mem_src1 mem_tgt1>>) /\
      (<<MAPWF: Mapping.wfs f1>>) /\
      (<<MAPLE: Mapping.les f0 f1>>) /\
      (<<PRESERVE: forall loc to from msg
                          (GET: Memory.get loc to mem_tgt0 = Some (from, msg))
                          ts fts
                          (TS: Time.le ts to)
                          (MAP: sim_timestamp_exact (f0 loc) (f0 loc).(Mapping.ver) fts ts),
          sim_timestamp_exact (f1 loc) (f1 loc).(Mapping.ver) fts ts>>).
Proof.
  hexploit (choice (fun loc f =>
                      (<<MAPWF: Mapping.wf f>>) /\
                      (<<MAPLE: Mapping.le (f0 loc) f>>) /\
                      (<<PRESERVE: forall to from msg
                                          (GET: Memory.get loc to mem_tgt0 = Some (from, msg))
                                          ts fts
                                          (TS: Time.le ts to)
                                          (MAP: sim_timestamp_exact (f0 loc) (f0 loc).(Mapping.ver) fts ts),
                          sim_timestamp_exact f f.(Mapping.ver) fts ts>>) /\
                      exists fcap,
                        (<<SIM: sim_timestamp_exact f f.(Mapping.ver) fcap (Time.incr (Memory.max_ts loc mem_tgt0))>>) /\
                        (<<TS: Time.le (Time.incr (Memory.max_ts loc mem_src0)) fcap>>))).
  { intros loc. hexploit top_time_exists; eauto. i. des.
    hexploit shifted_mapping_exists; eauto. i. des. esplits; eauto.
    2:{ left. eauto. }
    i. eapply SAME; eauto. eapply Memory.max_ts_spec in GET. des.
    eapply TimeFacts.le_lt_lt; eauto.
    eapply TimeFacts.le_lt_lt; eauto.
    eapply Time.incr_spec.
  }
  i. des. exists f.
  assert ((<<MAPWF: Mapping.wfs f>>) /\
          (<<MAPLE: Mapping.les f0 f>>) /\
          (<<PRESERVE: forall loc to from msg
                              (GET: Memory.get loc to mem_tgt0 = Some (from, msg))
                              ts fts
                              (TS: Time.le ts to)
                              (MAP: sim_timestamp_exact (f0 loc) (f0 loc).(Mapping.ver) fts ts),
              sim_timestamp_exact (f loc) (f loc).(Mapping.ver) fts ts>>)).
  { splits.
    { ii. specialize (H loc). des; auto. }
    { ii. specialize (H loc). des; auto. }
    { i. hexploit (H loc). i. des; auto. eapply PRESERVE; eauto. }
  }
  des. splits; auto. econs.
  { i. eapply Memory.cap_inv in GET; [..|eauto]; eauto. des; ss.
    hexploit sim_memory_get; eauto. i. des. esplits.
    { eapply PRESERVE; eauto. refl. }
    { eapply Memory.cap_le; eauto. refl. }
    { erewrite <- sim_message_mon_mapping; eauto. }
    { eapply sim_closed_mon_latest; eauto. }
  }
  { i. left. hexploit (H loc). i. des.
    exists fcap, Time.bot, (Time.incr (Memory.max_ts loc mem_tgt0)), Time.bot.
    splits; auto.
    { eapply Time.bot_spec. }
    { etrans; eauto. eapply Memory.max_ts_spec in GET. des.
      erewrite <- Memory.cap_max_ts; eauto.
    }
    { left. auto. }
    { i. eapply memory_cap_covered; eauto. }
  }
  { i. ss. }
Qed.

Lemma added_memory_sim_memory f0 f1 flag_src vers mem_tgt mem_src0 mem_src1 loc
      ts_tgt ts_src from msg msgs from_new msg_new
      (MEM: sim_memory flag_src f0 vers mem_src0 mem_tgt)
      (WF: Mapping.wfs f0)
      (VERS: versions_wf f0 vers)
      (ADDED: added_memory loc msgs mem_src0 mem_src1)
      (FLAG: flag_src loc = Some ts_src)
      (TS: Memory.get loc ts_src mem_src0 = Some (from_new, msg_new))
      (MSGNEW: sim_message false loc f0 (vers loc ts_tgt) msg_new msg)
      (GETTGT: Memory.get loc ts_tgt mem_tgt = Some (from, msg))
      (RESERVE: msg <> Message.reserve)
      (MSGCOMPLETE: forall to_tgt from_tgt msg_tgt
                           (RESERVE: msg_tgt <> Message.reserve)
                           (GETTGT: Memory.get loc to_tgt mem_tgt = Some (from_tgt, msg_tgt))
                           (TS: Time.lt ts_tgt to_tgt),
          exists to_src from_src msg_src,
            (<<TO: sim_timestamp_exact f1 f1.(Mapping.ver) to_src to_tgt>>) /\
            (<<MSG: sim_message false loc f0 (vers loc to_tgt) msg_src msg_tgt>>) /\
            (<<CLOSED: Mapping.closed f1 f1.(Mapping.ver) to_src>>) /\
            (<<IN: List.In (from_src, to_src, msg_src) msgs>>))
      (MSGSOUND: forall to_src from_src msg_src
                        (IN: List.In (from_src, to_src, msg_src) msgs),
          exists to_tgt from_tgt msg_tgt,
            (<<TO: sim_timestamp_exact f1 f1.(Mapping.ver) to_src to_tgt>>) /\
            (<<FROM: sim_timestamp_exact f1 f1.(Mapping.ver) from_src from_tgt>>) /\
            (<<GET: Memory.get loc to_tgt mem_tgt = Some (from_tgt, msg_tgt)>>))
      (MAPWF: Mapping.wf f1)
      (MAPLE: Mapping.le (f0 loc) f1)
      (SHIFTSAME: forall to fto
                         (TS: Time.lt to ts_tgt)
                         (MAP: sim_timestamp_exact (f0 loc) (f0 loc).(Mapping.ver) fto to),
          sim_timestamp_exact f1 f1.(Mapping.ver) fto to)
      (SHIFTTS: sim_timestamp_exact f1 f1.(Mapping.ver) ts_src ts_tgt)
      (CLOSEDTS: Mapping.closed f1 f1.(Mapping.ver) ts_src)
  :
    sim_memory
      (fun loc' => if Loc.eq_dec loc' loc then None else flag_src loc')
      (fun loc' => if Loc.eq_dec loc' loc then f1 else f0 loc')
      vers mem_src1 mem_tgt.
Proof.
  pose proof (mapping_latest_wf_loc (f0 loc)) as VERWF.
  assert (MAPSLE: Mapping.les f0 (fun loc' => if Loc.eq_dec loc' loc then f1 else f0 loc')).
  { ii. des_ifs. refl. }
  assert (MAPSWF: Mapping.wfs (fun loc' => if Loc.eq_dec loc' loc then f1 else f0 loc')).
  { ii. des_ifs. }
  hexploit sim_memory_get; eauto. i. des.
  assert (exists from_src from_tgt,
             (__guard__((<<BOT: (from_src = Time.bot /\ from_tgt = Time.bot)>>) \/ ((<<TS: Time.lt from_tgt ts_tgt>>) /\ (<<MAP0: sim_timestamp_exact (f0 loc) (f0 loc).(Mapping.ver) from_src from_tgt>>) /\ (<<MAP1: sim_timestamp_exact f1 f1.(Mapping.ver) from_src from_tgt>>))) /\
              (<<COVERED: forall ts (ITV: Interval.mem (from_tgt, ts_tgt) ts), covered loc ts mem_tgt>>))).
  { hexploit memory_get_ts_strong.
    { eapply GETTGT. }
    i. des.
    { clarify. esplits.
      { left. eauto. }
      { i. econs; eauto. }
    }
    hexploit sim_memory_sound_strong; eauto. i. des.
    { unguard. des; clarify.
      { esplits; eauto. i. apply COVERED. eapply Interval.le_mem; eauto.
        econs; ss; [refl|]. eapply sim_timestamp_exact_le_if; eauto.
      }
      { assert (LT: Time.lt from0 ts_tgt).
        { eapply sim_timestamp_exact_lt_if; eauto.
          eapply TimeFacts.le_lt_lt; eauto.
          eapply memory_get_ts_strong in GET; eauto. des; clarify.
          exfalso. hexploit sim_timestamp_exact_bot_if; [..|eapply TO|]; eauto.
        }
        exists ffrom0, from0. splits; auto.
        i. eapply COVERED. eapply Interval.le_mem; eauto.
        econs; ss; [refl|]. eapply sim_timestamp_exact_le_if; eauto.
      }
    }
    { exfalso. eapply TOP in TO.
      apply memory_get_ts_le in GET. timetac.
    }
  }
  inv ADDED. econs.
  { i. destruct (Loc.eq_dec loc0 loc); clarify; cycle 1.
    { hexploit sim_memory_get; eauto. i. des.
      esplits; eauto. erewrite <- sim_message_mon_mapping; eauto.
    }
    destruct (Time.le_lt_dec to ts_tgt) as [[LT|EQ]|LT].
    { hexploit sim_memory_get; eauto. i. des. esplits.
      { eapply SHIFTSAME; eauto. }
      { eapply MLE; eauto. }
      { erewrite <- sim_message_mon_mapping; eauto. }
      { eapply sim_closed_mon_latest; eauto. }
    }
    { inv EQ. clarify. esplits; eauto.
      erewrite <- sim_message_mon_mapping; eauto.
    }
    { hexploit MSGCOMPLETE; eauto. i. des. esplits; eauto.
      erewrite <- sim_message_mon_mapping; eauto.
    }
  }
  { i. destruct (Loc.eq_dec loc0 loc); clarify; cycle 1.
    { rewrite OTHER in GET0; auto. hexploit sim_memory_sound; eauto. }
    left. eapply SOUND in GET0. des.
    { hexploit sim_memory_sound_strong; eauto. i. des.
      { destruct (Time.le_lt_dec ts_tgt to).
        { inv l.
          { exists ts_src, from_src0, ts_tgt, from_tgt. splits; auto.
            { inv H; des; clarify.
              { eapply Time.bot_spec. }
              { hexploit memory_get_from_mon.
                { eapply GET. }
                { eapply GET1. }
                { destruct (Time.le_lt_dec fto0 to_src); auto.
                  eapply MIN in l; eauto.
                  eapply sim_timestamp_exact_le_if in l; eauto.
                  exfalso. timetac.
                }
                i. etrans; eauto. left.
                eapply sim_timestamp_exact_lt;[eapply MAP0|..]; eauto.
              }
            }
            { etrans; eauto. left. eapply sim_memory_top; eauto. }
            { inv H; des; clarify.
              { left. auto. }
              { right. auto. }
            }
          }
          { inv H0. eapply sim_timestamp_exact_inject in TO; eauto. clarify.
            hexploit memory_get_ts_strong.
            { eapply GET1. }
            i. des; clarify.
            { assert (ffrom0 = Time.bot).
              { eapply TimeFacts.antisym; ss. eapply Time.bot_spec. }
              subst. eexists _, Time.bot, to, Time.bot. splits; auto.
              { eapply Time.bot_spec. }
              { left. auto. }
              { eauto. }
              { i. eapply COVERED0; eauto. eapply Interval.le_mem; eauto.
                econs; ss; [|refl]. inv FROM; des; clarify.
                eapply sim_timestamp_exact_bot_if in H0; eauto.
                subst. refl.
              }
            }
            esplits; [eauto| | |eauto|..]; eauto.
            { etrans; eauto. left. eapply sim_memory_top; eauto. }
            { inv FROM; des; clarify.
              { left. auto. }
              { right. eapply SHIFTSAME; eauto.
                eapply sim_timestamp_exact_lt_if; eauto.
                eapply TimeFacts.le_lt_lt.
                { eauto. }
                eapply TimeFacts.lt_le_lt; eauto.
              }
            }
          }
        }
        { esplits; eauto. inv FROM.
          { left. auto. }
          { right. eapply SHIFTSAME; eauto.
            eapply sim_timestamp_exact_lt_if; eauto.
            eapply TimeFacts.le_lt_lt; eauto.
            eapply TimeFacts.le_lt_lt.
            { eapply memory_get_ts_le. eapply GET1. }
            eapply TimeFacts.le_lt_lt.
            { eauto. }
            eapply sim_timestamp_exact_lt; eauto.
          }
        }
      }
      { clarify. exists ts_src, from_src0, ts_tgt, from_tgt. splits; auto.
        { inv H; des; clarify.
          { eapply Time.bot_spec. }
          { left. eapply TOP; eauto. }
        }
        { inv H; des.
          { left. auto. }
          { right. auto. }
        }
      }
    }
    { hexploit MSGSOUND; eauto. i. des. esplits.
      { refl. }
      { refl. }
      { right. eauto. }
      { eauto. }
      { i. econs; eauto. }
    }
  }
  { i. des_ifs. eapply sim_memory_top; eauto. }
Qed.

Lemma lower_lower_memory mem0 mem1 loc from to msg0 msg1
      (LOWER: Memory.lower mem0 loc from to msg0 msg1 mem1)
  :
    lower_memory mem1 mem0.
Proof.
  econs. ii. erewrite (@Memory.lower_o mem1); eauto. des_ifs.
  { ss. des; clarify. eapply lower_succeed_wf in LOWER. des.
    rewrite GET. econs; eauto.
  }
  { refl. }
Qed.

Variant lower_none_content: option (Time.t * Message.t) -> option (Time.t * Message.t) -> Prop :=
| lower_none_content_none
  :
    lower_none_content None None
| lower_none_content_reserve
    from
  :
    lower_none_content (Some (from, Message.reserve)) (Some (from, Message.reserve))
| lower_none_content_undef
    from
  :
    lower_none_content (Some (from, Message.undef)) (Some (from, Message.undef))
| lower_none_content_concrete
    from val released
  :
    lower_none_content (Some (from, Message.concrete val None)) (Some (from, Message.concrete val released))
.

Variant lower_none_list mem0 mem1 loc (tos: list Time.t): Prop :=
| lower_list_mem_intro
    (OTHERLOC: forall loc0 ts (NEQ: loc0 <> loc),
        Memory.get loc0 ts mem1 = Memory.get loc0 ts mem0)
    (OTHERTS: forall ts (NIN: ~ List.In ts tos),
        Memory.get loc ts mem1 = Memory.get loc ts mem0)
    (SAMETS: forall ts (IN: List.In ts tos),
        lower_none_content (Memory.get loc ts mem1) (Memory.get loc ts mem0))
.

Lemma memory_lower_o2 mem1 mem2 loc from to msg1 msg2 l t
      (LOWER: Memory.lower mem1 loc from to msg1 msg2 mem2)
  :
    Memory.get l t mem1 =
    (if loc_ts_eq_dec (l, t) (loc, to)
     then Some (from, msg1)
     else Memory.get l t mem2).
Proof.
  erewrite (@Memory.lower_o mem2 mem1); eauto. des_ifs.
  ss. des; clarify. eapply Memory.lower_get0 in LOWER. des; auto.
Qed.

Lemma tgt_flag_up_sim_promises flag_src flag_tgt f vers prom_src0 prom_tgt mem_src0 mem_tgt loc ts
      (PROMS: sim_promises flag_src flag_tgt f vers prom_src0 prom_tgt)
      (MEM: sim_memory flag_src f vers mem_src0 mem_tgt)
      (TS: forall from to msg
                  (GET: Memory.get loc to prom_src0 = Some (from, msg))
                  (MSG: msg <> Message.reserve), Time.lt ts to)
      (MLE: Memory.le prom_src0 mem_src0)
      (INHABITED: Memory.inhabited mem_src0)
  :
    forall tvw lang st sc,
    exists prom_src1 mem_src1,
      (<<STEPS: rtc (@Thread.tau_step _)
                    (Thread.mk lang st (Local.mk tvw prom_src0) sc mem_src0)
                    (Thread.mk _ st (Local.mk tvw prom_src1) sc mem_src1)>>) /\
      (<<PROMS: sim_promises flag_src (fun loc' => if (Loc.eq_dec loc' loc) then (Some ts) else flag_tgt loc') f vers prom_src1 prom_tgt>>) /\
      (<<NONE: forall to from val released (GET: Memory.get loc to prom_src1 = Some (from, Message.concrete val released)),
          released = None>>) /\
      (<<MEM: sim_memory flag_src f vers mem_src1 mem_tgt>>) /\
      (<<VALS: forall loc0 to val released,
          max_readable mem_src0 prom_src0 loc0 to val released
          <->
          max_readable mem_src1 prom_src1 loc0 to val released>>)
.
Proof.
  assert (exists dom,
             (<<DOM: forall to from val released
                            (GET: Memory.get loc to prom_src0 = Some (from, Message.concrete val (Some released))),
                 List.In to dom>>)).
  { hexploit (cell_finite_sound_exists (prom_src0 loc)). i. des.
    hexploit (@list_filter_exists _ (fun to => exists from val released, Memory.get loc to prom_src0 = Some (from, Message.concrete val (Some released)))).
    i. des. exists l'. ii. eapply COMPLETE0. splits; eauto.
    eapply COMPLETE. eauto.
  }
  i. des.
  cut (exists prom_src1 mem_src1,
          (<<STEPS: rtc (@Thread.tau_step _)
                        (Thread.mk lang st (Local.mk tvw prom_src0) sc mem_src0)
                        (Thread.mk _ st (Local.mk tvw prom_src1) sc mem_src1)>>) /\
          (<<LOWERPROMS: lower_none_list prom_src0 prom_src1 loc dom>>) /\
          (<<VALS: forall loc0 to val released,
              max_readable mem_src0 prom_src0 loc0 to val released
              <->
              max_readable mem_src1 prom_src1 loc0 to val released>>) /\
          (<<MEM: sim_memory flag_src f vers mem_src1 mem_tgt>>)).
  { i. des. esplits.
    { eauto. }
    { inv LOWERPROMS. econs.
      { i. hexploit sim_promises_get; eauto. i. des. des_ifs.
        { destruct (classic (List.In to_src dom)).
          { hexploit SAMETS; eauto. i. rewrite GET0 in H0. inv H0.
            { esplits; eauto. inv MSG; try by (econs; auto). }
            { esplits; eauto. inv MSG; try by (econs; auto). }
            { esplits; eauto. inv MSG; try by (econs; auto). }
          }
          { hexploit OTHERTS; eauto. i. esplits; eauto.
            { rewrite H0. eauto. }
            { inv MSG; try by (econs; auto).
              destruct vw_src; try by (econs; auto).
              exfalso. eapply H. eapply DOM. eauto.
            }
          }
        }
        { esplits; eauto. rewrite OTHERLOC; auto. }
      }
      { i. des_ifs.
        { destruct (classic (List.In fto dom)).
          { hexploit SAMETS; eauto. i. right. esplits; eauto.
            { i. rewrite GET in H0. inv H0; ss.
              { eapply TS; eauto. }
              { eapply TS; eauto. ss. }
            }
            { i. subst. rewrite GET in *. inv H0. }
          }
          { hexploit sim_promises_get_if.
            { eauto. }
            { rewrite <- OTHERTS; eauto. }
            i. des; clarify.
            { left. esplits; eauto. }
            { right. esplits; eauto. i.
              eapply TS; eauto. rewrite <- OTHERTS; eauto.
            }
          }
        }
        { hexploit sim_promises_get_if.
          { eauto. }
          { rewrite <- OTHERLOC; eauto. }
          i. des.
          { left. esplits; eauto. }
          { right. esplits; eauto. }
        }
      }
      { i. hexploit sim_promises_none; eauto. i.
        destruct (Loc.eq_dec loc0 loc); subst.
        { destruct (classic (List.In to dom)).
          { hexploit SAMETS; eauto. i.
            rewrite H in H1. inv H1; auto.
          }
          { rewrite OTHERTS; auto. }
        }
        { rewrite OTHERLOC; eauto. }
      }
    }
    { i. inv LOWERPROMS. destruct (classic (List.In to dom)).
      { eapply SAMETS in H. rewrite GET in H. inv H. auto. }
      { rewrite OTHERTS in GET; auto. destruct released; auto.
        eapply DOM in GET; ss.
      }
    }
    { auto. }
    { auto. }
  }
  { clear TS PROMS. revert prom_src0 mem_src0 DOM MEM MLE INHABITED.
    induction dom; i; ss.
    { esplits.
      { refl. }
      { econs; ss. }
      { refl. }
      { auto. }
    }
    { destruct (classic (exists from val released, <<GET: Memory.get loc a prom_src0 = Some (from, Message.concrete val (Some released))>>)).
      { des.
        hexploit (@Memory.lower_exists prom_src0 loc from a (Message.concrete val (Some released)) (Message.concrete val None)); auto.
        { hexploit memory_get_ts_strong.
          { eapply GET. }
          i. des; clarify.
          apply MLE in GET.
          rewrite INHABITED in GET. clarify.
        }
        { econs; eauto. refl. }
        i. des.
        hexploit Memory.lower_exists_le; eauto. i. des.
        assert (LOWER: Memory.promise prom_src0 mem_src0 loc from a (Message.concrete val None) mem2 mem0 (Memory.op_kind_lower (Message.concrete val (Some released)))).
        { econs; eauto; ss. econs. ss. eapply Time.bot_spec. }
        hexploit (@IHdom mem2 mem0); auto.
        { i. erewrite Memory.lower_o in GET0; eauto. des_ifs.
          hexploit DOM; eauto. i. des; clarify.
        }
        { eapply lower_src_sim_memory; eauto. }
        { eapply promise_memory_le; eauto. }
        { eapply Memory.lower_inhabited; eauto. }
        i. des. exists prom_src1, mem_src1. esplits; eauto.
        { econs; [|eapply STEPS]. econs.
          { econs. econs 1. econs; ss. econs; eauto. }
          { ss. }
        }
        { inv LOWERPROMS. econs.
          { i. transitivity (Memory.get loc0 ts0 mem2); auto.
            erewrite (@Memory.lower_o mem2); eauto.
            des_ifs. ss. des; clarify.
          }
          { i. transitivity (Memory.get loc ts0 mem2); auto.
            { apply OTHERTS. ii. apply NIN. ss; auto. }
            { erewrite (@Memory.lower_o mem2); eauto.
              des_ifs. ss. des; clarify. exfalso. eapply NIN; auto.
            }
          }
          { i. ss. des.
            { clarify. destruct (classic (List.In ts0 dom)); auto.
              { apply SAMETS in H1. erewrite (@Memory.lower_o mem2) in H1; eauto.
                des_ifs. ss. des; clarify.
                rewrite GET. inv H1; try econs.
              }
              { apply OTHERTS in H1. rewrite H1.
                erewrite (@Memory.lower_o mem2); eauto. des_ifs.
                { ss. des; clarify. rewrite GET. econs. }
                { ss. des; clarify. }
              }
            }
            { eapply SAMETS in IN. erewrite (@Memory.lower_o mem2) in IN; eauto.
              des_ifs. ss. des; clarify. rewrite GET.
              inv IN; try by econs.
            }
          }
        }
        { i. erewrite <- VALS. split; i; des.
          { inv H1. econs.
            { erewrite Memory.lower_o; eauto. des_ifs; eauto.
              exfalso. ss. des; clarify.
            }
            { erewrite Memory.lower_o; eauto. des_ifs; eauto.
              exfalso. ss. des; clarify.
            }
            { i. erewrite Memory.lower_o in GET1; eauto.
              erewrite (@Memory.lower_o mem2 prom_src0); eauto. des_ifs.
              eapply MAX; eauto.
            }
          }
          { inv H1. erewrite Memory.lower_o in GET0; eauto.
            erewrite Memory.lower_o in NONE; eauto. des_ifs. guardH o.
            econs; eauto. i.
            erewrite memory_lower_o2 in GET1; eauto.
            erewrite (@memory_lower_o2 prom_src0 mem2); eauto. des_ifs.
            eapply MAX; eauto.
          }
        }
      }
      { hexploit (@IHdom prom_src0 mem_src0); auto.
        { i. hexploit DOM; eauto. i. des; clarify.
          exfalso. eapply H; eauto.
        }
        i. des. esplits; eauto. inv LOWERPROMS. econs.
        { i. eapply OTHERLOC. auto. }
        { i. eapply OTHERTS. ii. eapply NIN. ss; auto. }
        { i. ss. des; clarify.
          { destruct (classic (List.In ts0 dom)); auto.
            eapply OTHERTS in H0. rewrite H0.
            destruct (Memory.get loc ts0 prom_src0) as [[? []]|] eqn:EQ; try econs.
            destruct released; try econs.
            exfalso. eapply H; eauto.
          }
          { eapply SAMETS. auto. }
        }
      }
    }
  }
Qed.

Lemma src_cancel_sim_promises flag_src f vers prom_src0 mem_src0 mem_tgt loc from to prom_src1 mem_src1
      (CANCEL: Memory.promise prom_src0 mem_src0 loc from to Message.reserve prom_src1 mem_src1 Memory.op_kind_cancel)
      (MEM: sim_memory flag_src f vers mem_src0 mem_tgt)
      (MLE: Memory.le prom_src0 mem_src0)
      (CLOSED: Memory.closed mem_src0)
  :
    (<<MEM: sim_memory flag_src f vers mem_src1 mem_tgt>>) /\
    (<<PROM: forall loc0 (NEQ: loc0 <> loc) to0, Memory.get loc0 to0 prom_src1 = Memory.get loc0 to0 prom_src0>>) /\
    (<<VALS: forall loc0 to val released,
        max_readable mem_src0 prom_src0 loc0 to val released
        <->
        max_readable mem_src1 prom_src1 loc0 to val released>>)
.
Proof.
  inv CANCEL. splits.
  { econs.
    { i. hexploit sim_memory_get; eauto. i. des. esplits; eauto.
      erewrite (@Memory.remove_o mem_src1 mem_src0); eauto.
      des_ifs; eauto. ss. des; clarify. exfalso.
      eapply Memory.remove_get0 in MEM0. des; clarify. inv MSG0; ss.
    }
    { i. hexploit sim_memory_sound; eauto.
      erewrite Memory.remove_o in GET; eauto. des_ifs. eauto.
    }
    { i. eapply sim_memory_top; eauto. }
  }
  { i. erewrite (@Memory.remove_o prom_src1 prom_src0); eauto. des_ifs.
    ss. des; clarify.
  }
  { i. split.
    { i. inv H. econs.
      { erewrite Memory.remove_o; eauto. des_ifs; eauto.
        eapply Memory.remove_get0 in MEM0. exfalso. ss. des; clarify.
      }
      { erewrite Memory.remove_o; eauto. des_ifs; eauto. }
      { i. erewrite (@Memory.remove_o mem_src1 mem_src0) in GET0; eauto.
        erewrite (@Memory.remove_o prom_src1 prom_src0); eauto. des_ifs; eauto.
      }
    }
    { i. inv H. erewrite (@Memory.remove_o mem_src1 mem_src0) in GET; eauto.
      erewrite (@Memory.remove_o prom_src1 prom_src0) in NONE; eauto. des_ifs; eauto.
      econs; eauto. i. hexploit MAX; eauto.
      { erewrite Memory.remove_o; eauto. des_ifs; eauto.
        exfalso. apply Memory.remove_get0 in MEM0. ss. des; clarify.
      }
      { i. erewrite Memory.remove_o in H; eauto. des_ifs. }
    }
  }
Qed.

Lemma src_cancels_sim_promises flag_src f vers prom_src0 mem_src0 mem_tgt loc
      prom_src1 mem_src1
      (MEM: sim_memory flag_src f vers mem_src0 mem_tgt)
      (CANCEL: cancel_future_memory loc prom_src0 mem_src0 prom_src1 mem_src1)
      (MLE: Memory.le prom_src0 mem_src0)
      (CLOSED: Memory.closed mem_src0)
  :
    (<<MEM: sim_memory flag_src f vers mem_src1 mem_tgt>>) /\
    (<<PROM: forall loc0 (NEQ: loc0 <> loc) to0, Memory.get loc0 to0 prom_src1 = Memory.get loc0 to0 prom_src0>>) /\
    (<<VALS: forall loc0 to val released,
        max_readable mem_src0 prom_src0 loc0 to val released
        <->
        max_readable mem_src1 prom_src1 loc0 to val released>>)
.
Proof.
  revert MLE CLOSED. induction CANCEL.
  { i. splits; auto. }
  { i. hexploit src_cancel_sim_promises; eauto. i. des.
    hexploit IHCANCEL; eauto.
    { eapply promise_memory_le; eauto. }
    { eapply Memory.promise_closed; eauto. }
    i. des. splits; auto.
    { i. transitivity (Memory.get loc0 to0 prom1); auto. }
    { i. transitivity (max_readable mem1 prom1 loc0 to0 val released); auto. }
  }
Qed.

Lemma sim_promises_nonsynch_loc flag_src flag_tgt f vers
      prom_src prom_tgt loc
      (SIM: sim_promises flag_src flag_tgt f vers prom_src prom_tgt)
      (NONSYNCH: flag_tgt loc = None -> Memory.nonsynch_loc loc prom_tgt)
  :
    Memory.nonsynch_loc loc prom_src.
Proof.
  ii. hexploit sim_promises_get_if; eauto. i. des.
  { inv MSG; ss. hexploit NONSYNCH; eauto.
    { destruct (flag_tgt loc); ss. }
    i. eapply H in GET0; eauto. subst. inv SIM0. auto.
  }
  { des_ifs. destruct released; auto. exfalso. eapply SYNC; eauto. }
Qed.

Lemma sim_promises_nonsynch flag_src flag_tgt f vers
      prom_src prom_tgt
      (SIM: sim_promises flag_src flag_tgt f vers prom_src prom_tgt)
      (NONSYNCH: Memory.nonsynch prom_tgt)
  :
    Memory.nonsynch prom_src.
Proof.
  intros loc. eapply sim_promises_nonsynch_loc; eauto.
Qed.

Lemma sim_promises_bot flag_src flag_tgt f vers
      prom_src prom_tgt
      (SIM: sim_promises flag_src flag_tgt f vers prom_src prom_tgt)
      (BOT: prom_tgt = Memory.bot)
      (FLAG: forall loc (NONE: flag_src loc = None), flag_tgt loc = None)
  :
    prom_src = Memory.bot.
Proof.
  subst. eapply Memory.ext. i. rewrite Memory.bot_get.
  destruct (Memory.get loc ts prom_src) eqn:EQ; auto.
  destruct p. hexploit sim_promises_get_if; eauto. i. des.
  { rewrite Memory.bot_get in GET. ss. }
  { destruct (flag_src loc) eqn:SRC.
    { hexploit sim_promises_none; eauto. i. rewrite H in EQ. ss. }
    { exfalso. eapply FLAG in SRC. clarify. }
  }
Qed.
