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

Set Implicit Arguments.



Definition version := nat.
Definition flags := Loc.t -> bool.

Module Mapping.
  Record t: Type :=
    mk
      { map:> version -> Loc.t -> Time.t -> option Time.t;
        ver: version;
      }.

  Definition versions := Loc.t -> Time.t -> option version.

  Definition world := (t * versions)%type.

  Record wf (f: t): Prop :=
    { map_finite: forall ver loc, exists l, forall ts fts (MAP: f ver loc ts = Some fts), List.In (ts, fts) l;
      mapping_map_lt_iff: forall ver loc ts0 ts1 fts0 fts1
                             (MAP0: f.(map) ver loc ts0 = Some fts0) (MAP0: f.(map) ver loc ts1 = Some fts1),
          Time.lt ts0 ts1 <-> Time.lt fts0 fts1;
      version_time_incr: forall v loc ts fts0 fts1
                                (VER: v <= f.(ver))
                                (MAP0: f.(map) f.(ver) loc ts = Some fts0) (MAP0: f.(map) v loc ts = Some fts1),
          Time.le fts0 fts1;
      mapping_empty: forall v (VER: f.(ver) < v) loc ts, f v loc ts = None;
    }.

  Lemma mapping_map_le (f: t) (WF: wf f):
    forall ver loc ts0 ts1 fts0 fts1
           (MAP0: f.(map) ver loc ts0 = Some fts0) (MAP0: f.(map) ver loc ts1 = Some fts1),
      Time.le ts0 ts1 <-> Time.le fts0 fts1.
  Proof.
    i. split.
    { i. destruct (Time.le_lt_dec fts0 fts1); auto.
      erewrite <- mapping_map_lt_iff in l; eauto. timetac. }
    { i. destruct (Time.le_lt_dec ts0 ts1); auto.
      erewrite mapping_map_lt_iff in l; eauto. timetac. }
  Qed.

  Lemma mapping_map_eq (f: t) (WF: wf f):
    forall ver loc ts0 ts1 fts0 fts1
           (MAP0: f.(map) ver loc ts0 = Some fts0) (MAP0: f.(map) ver loc ts1 = Some fts1),
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

  Definition le (f0 f1: t): Prop :=
    (<<VER: f0.(ver) <= f1.(ver)>>) /\
    (<<TIME: forall v loc ts fts
                    (MAP: f0.(map) v loc ts = Some fts), f1.(map) v loc ts = Some fts>>)
  .

  Program Instance le_PreOrder: PreOrder le.
  Next Obligation.
  Proof.
    unfold le. ii. splits; auto.
  Qed.
  Next Obligation.
  Proof.
    unfold le. ii. des. splits; auto. etrans; eauto.
  Qed.

  Section MAP.
    Variable f: t.
    Hypothesis WF: wf f.

    Section VER.
      Variable v: version.

      Definition time_map_ver (loc: Loc.t) (ts_src ts_tgt: Time.t): Prop :=
        f v loc ts_tgt = Some ts_src.

      Definition timemap_map_ver (tm_src tm_tgt: TimeMap.t): Prop :=
        forall loc, time_map_ver loc (tm_src loc) (tm_tgt loc).

      Record view_map_ver (vw_src vw_tgt: View.t): Prop :=
        { pln_map_ver: timemap_map_ver vw_src.(View.pln) vw_tgt.(View.pln);
          rlx_map_ver: timemap_map_ver vw_src.(View.rlx) vw_tgt.(View.rlx);
        }.

      Variant opt_view_map_ver:
        forall (vw_src vw_tgt: option View.t), Prop :=
      | some_view_map_ver
          vw_src vw_tgt
          (MAP: view_map_ver vw_src vw_tgt)
        :
          opt_view_map_ver (Some vw_src) (Some vw_tgt)
      | none_view_map_ver
        :
          opt_view_map_ver None None
      .
    End VER.

    Definition time_map_latest (loc: Loc.t) (ts_src ts_tgt: Time.t): Prop :=
      time_map_ver f.(ver) loc ts_src ts_tgt.

    Definition time_map (loc: Loc.t) (ts_src ts_tgt: Time.t): Prop :=
      exists v ts, (<<MAP: f v loc ts_tgt = Some ts>>) /\ (<<TS: Time.le ts_src ts>>).

    Definition timemap_map (tm_src tm_tgt: TimeMap.t): Prop :=
      forall loc, time_map loc (tm_src loc) (tm_tgt loc).

    Record view_map (vw_src vw_tgt: View.t): Prop :=
      { pln_map: timemap_map vw_src.(View.pln) vw_tgt.(View.pln);
        rlx_map: timemap_map vw_src.(View.rlx) vw_tgt.(View.rlx);
      }.

    Variant opt_view_map:
      forall (vw_src vw_tgt: option View.t), Prop :=
    | some_view_map
        vw_src vw_tgt
        (MAP: view_map vw_src vw_tgt)
      :
        opt_view_map (Some vw_src) (Some vw_tgt)
    | none_view_map
      :
        opt_view_map None None
    .

    Definition released_map (vers: versions) (prom: Memory.t)
               (rel_src: Loc.t -> View.t) (rel_tgt: Loc.t -> View.t): Prop :=
      forall loc ts from val released
             (GET: Memory.get loc ts prom = Some (from, Message.concrete val (Some released))),
      exists v vw, (<<VER: vers loc ts = Some v>>) /\
                   (<<MAP: view_map_ver v vw (rel_tgt loc)>>) /\
                   (<<VIEW: View.le (rel_src loc) vw>>).

    Variant promises_map_latest (vers: versions) (prom_src prom_tgt: Memory.t)
            (flag_src: flags) (flag_tgt: flags): Prop :=
    | promises_map_latest_intro
        (FLAGFALSE: forall loc (SRC: flag_src loc = false) (TGT: flag_tgt loc = true),
            exists to from, (<<GET: Memory.get loc to prom_tgt = Some (from, Message.undef)>>))
        (FLAGTRUE: forall loc (SRC: flag_src loc = true),
            forall to, Memory.get loc to prom_src = None)
        (UNDEF: forall loc to from
                       (FLAGFALSE: flag_src loc = false)
                       (GET: Memory.get loc to prom_tgt = Some (from, Message.undef)),
            exists fto ffrom,
              (<<FROM: time_map_latest loc ffrom from>>) /\
              (<<TO: time_map_latest loc fto to>>) /\
              (<<GET: Memory.get loc fto prom_src = Some (ffrom, Message.undef)>>))
        (CONCRETE: forall loc to from val released
                          (FLAGFALSE: flag_src loc = false)
                          (GET: Memory.get loc to prom_tgt = Some (from, Message.concrete val released)),
            exists v fto ffrom freleased,
              (<<VER: vers loc to = Some v>>) /\
              (<<FROM: time_map_latest loc ffrom from>>) /\
              (<<TO: time_map_latest loc fto to>>) /\
              (<<RELEASED: opt_view_map_ver v freleased released>>) /\
              (<<GET: Memory.get loc fto prom_src = Some (ffrom, Message.concrete val freleased)>>))
        (RESERVE: forall loc to from
                         (FLAGFALSE: flag_src loc = false)
                         (GET: Memory.get loc to prom_tgt = Some (from, Message.reserve)),
            exists fto ffrom,
              (<<FROM: time_map_latest loc ffrom from>>) /\
              (<<TO: time_map_latest loc fto to>>) /\
              (<<GET: Memory.get loc fto prom_src = Some (ffrom, Message.reserve)>>))
        (SOUND: forall loc fto ffrom fmsg
                       (FLAGTRUE: flag_tgt loc = false)
                       (GET: Memory.get loc fto prom_src = Some (ffrom, fmsg)),
            exists to from msg,
              (<<TO: time_map_latest loc fto to>>) /\
              (<<GET: Memory.get loc fto prom_src = Some (from, msg)>>))
    .

    Variant promises_map (vers: versions) (prom_src prom_tgt: Memory.t)
            (flag_src: flags) (flag_tgt: flags): Prop :=
    | promises_map_intro
        (FLAGFALSE: forall loc (SRC: flag_src loc = false) (TGT: flag_tgt loc = true),
            exists to from, (<<GET: Memory.get loc to prom_tgt = Some (from, Message.undef)>>))
        (FLAGTRUE: forall loc (SRC: flag_src loc = true),
            forall to, Memory.get loc to prom_src = None)
        (UNDEF: forall loc to from
                       (FLAGFALSE: flag_src loc = false)
                       (GET: Memory.get loc to prom_tgt = Some (from, Message.undef)),
            exists fto ffrom,
              (<<FROM: time_map_latest loc ffrom from>>) /\
              (<<TO: time_map_latest loc fto to>>) /\
              (<<GET: Memory.get loc fto prom_src = Some (ffrom, Message.undef)>>))
        (CONCRETE: forall loc to from val released
                          (FLAGFALSE: flag_src loc = false)
                          (GET: Memory.get loc to prom_tgt = Some (from, Message.concrete val released)),
            exists v fto ffrom freleased,
              (<<VER: vers loc to = Some v>>) /\
              (<<FROM: time_map_latest loc ffrom from>>) /\
              (<<TO: time_map_latest loc fto to>>) /\
              (<<RELEASED: opt_view_map_ver v freleased released>>) /\
              (<<GET: Memory.get loc fto prom_src = Some (ffrom, Message.concrete val freleased)>>))
        (RESERVE: forall loc to from
                         (FLAGFALSE: flag_src loc = false)
                         (GET: Memory.get loc to prom_tgt = Some (from, Message.reserve)),
            exists v fto ffrom,
              (<<FROM: time_map_ver v loc ffrom from>>) /\
              (<<TO: time_map_ver v loc fto to>>) /\
              (<<GET: Memory.get loc fto prom_src = Some (ffrom, Message.reserve)>>))
        (SOUND: forall loc fto ffrom fmsg
                       (FLAGTRUE: flag_tgt loc = false)
                       (GET: Memory.get loc fto prom_src = Some (ffrom, fmsg))
                       (NRESERVE: fmsg <> Message.reserve),
            exists to from msg,
              (<<TO: time_map_latest loc fto to>>) /\
              (<<GET: Memory.get loc fto prom_src = Some (from, msg)>>))
        (SOUNDRESERVE: forall loc fto ffrom
                              (FLAGTRUE: flag_tgt loc = false)
                              (GET: Memory.get loc fto prom_src = Some (ffrom, Message.reserve)),
            exists v to from,
              (<<FROM: time_map_ver v loc ffrom from>>) /\
              (<<TO: time_map_ver v loc fto to>>) /\
              (<<GET: Memory.get loc to prom_tgt = Some (from, Message.reserve)>>) /\
              (<<UNIQUE: forall v' ffrom' fto' msg'
                                (MAP: time_map_ver v' loc fto' to)
                                (GET: Memory.get loc fto' prom_src = Some (ffrom', msg')),
                  fto' = fto>>))
    .

    Variant sim_memory_latest
            (vers: versions) (mem_src mem_tgt: Memory.t): Prop :=
    | sim_memory_latest_intro
        (CONCRETE: forall loc to from val released
                          (GET: Memory.get loc to mem_tgt = Some (from, Message.concrete val released)),
            exists fto ffrom rel,
              (<<TO: time_map_latest loc fto to>>) /\
              (<<GET: Memory.get loc fto mem_src = Some (ffrom, Message.concrete val rel)>>) /\
              (<<RELEASED: forall freleased (EQ: rel = Some freleased),
                  exists v vw,
                    (<<VER: vers loc to = Some v>>) /\
                    (<<MAP: opt_view_map_ver v vw released>>) /\
                    (<<VIEW: View.opt_le rel vw>>)>>))
        (UNDEF: forall loc to from
                       (GET: Memory.get loc to mem_tgt = Some (from, Message.undef)),
            exists fto ffrom,
              (<<TO: time_map_latest loc fto to>>) /\
              (<<GET: Memory.get loc fto mem_src = Some (ffrom, Message.undef)>>))
        (COVER: forall loc fto ffrom msg
                       (GET: Memory.get loc fto mem_src = Some (ffrom, msg)),
            exists to from fto' ffrom',
              (<<TS: Time.le fto fto'>>) /\
              (<<TS: Time.le ffrom' ffrom>>) /\
              (<<FROM: time_map_latest loc ffrom' from>>) /\
              (<<TO: time_map_latest loc fto' to>>) /\
              (<<COVERED: forall ts (ITV: Interval.mem (from, to) ts), covered loc ts mem_tgt>>))
    .
  End MAP.
End Mapping.
