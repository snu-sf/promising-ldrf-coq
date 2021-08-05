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

Module Mapping.
  Record t: Type :=
    { map:> version -> Loc.t -> Time.t -> option Time.t;
      ver: version;
    }.

  Definition versions := Loc.t -> Time.t -> option version.

  Record wf (f: t): Prop :=
    { map_finite: forall ver loc, exists l, forall ts fts (MAP: f ver loc ts = Some fts), List.In (ts, fts) l;
      mapping_map_lt: forall ver loc ts0 ts1 fts0 fts1
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
      erewrite <- mapping_map_lt in l; eauto. timetac. }
    { i. destruct (Time.le_lt_dec ts0 ts1); auto.
      erewrite mapping_map_lt in l; eauto. timetac. }
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

    Variant promises_map (vers: versions) (prom_src prom_tgt: Memory.t) :=
    | promises_map_intro
        (UNDEF: forall loc to from
                       (GET: Memory.get loc to prom_tgt = Some (from, Message.undef)),
            exists fto ffrom,
              (<<FROM: time_map_latest loc ffrom from>>) /\
              (<<TO: time_map_latest loc fto to>>) /\
              (<<GET: Memory.get loc fto prom_src = Some (ffrom, Message.undef)>>))
        (CONCRETE: forall loc to from val released
                          (GET: Memory.get loc to prom_tgt = Some (from, Message.concrete val released)),
            exists v fto ffrom freleased,
              (<<VER: vers loc to = Some v>>) /\
              (<<FROM: time_map_latest loc ffrom from>>) /\
              (<<TO: time_map_latest loc fto to>>) /\
              (<<RELEASED: opt_view_map_ver v freleased released>>) /\
              (<<GET: Memory.get loc fto prom_src = Some (ffrom, Message.concrete val freleased)>>))
        (RESERVE: forall loc to from
                         (GET: Memory.get loc to prom_tgt = Some (from, Message.reserve)),
            exists v fto ffrom,
              (<<FROM: time_map_ver v loc ffrom from>>) /\
              (<<TO: time_map_ver v loc fto to>>) /\
              (<<GET: Memory.get loc fto prom_src = Some (ffrom, Message.reserve)>>))
        (SOUND: forall loc fto ffrom fmsg
                       (GET: Memory.get loc fto prom_src = Some (ffrom, fmsg))
                       (NRESERVE: fmsg <> Message.reserve),
            exists to from msg,
              (<<TO: time_map_latest loc fto to>>) /\
              (<<GET: Memory.get loc fto prom_src = Some (from, msg)>>))
        (SOUNDRESERVE: forall loc fto ffrom
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

    Variant promises_map_latest (vers: versions) (prom_src prom_tgt: Memory.t) :=
    | promises_map_latest_intro
        (UNDEF: forall loc to from
                       (GET: Memory.get loc to prom_tgt = Some (from, Message.undef)),
            exists fto ffrom,
              (<<FROM: time_map_latest loc ffrom from>>) /\
              (<<TO: time_map_latest loc fto to>>) /\
              (<<GET: Memory.get loc fto prom_src = Some (ffrom, Message.undef)>>))
        (CONCRETE: forall loc to from val released
                          (GET: Memory.get loc to prom_tgt = Some (from, Message.concrete val released)),
            exists v fto ffrom freleased,
              (<<VER: vers loc to = Some v>>) /\
              (<<FROM: time_map_latest loc ffrom from>>) /\
              (<<TO: time_map_latest loc fto to>>) /\
              (<<RELEASED: opt_view_map_ver v freleased released>>) /\
              (<<GET: Memory.get loc fto prom_src = Some (ffrom, Message.concrete val freleased)>>))
        (RESERVE: forall loc to from
                         (GET: Memory.get loc to prom_tgt = Some (from, Message.reserve)),
            exists fto ffrom,
              (<<FROM: time_map_latest loc ffrom from>>) /\
              (<<TO: time_map_latest loc fto to>>) /\
              (<<GET: Memory.get loc fto prom_src = Some (ffrom, Message.reserve)>>))
        (SOUND: forall loc fto ffrom fmsg
                       (GET: Memory.get loc fto prom_src = Some (ffrom, fmsg)),
            exists to from msg,
              (<<TO: time_map_latest loc fto to>>) /\
              (<<GET: Memory.get loc fto prom_src = Some (from, msg)>>))
    .

    Variant sim_memory (vers: versions) (mem_src mem_tgt: Memory.t): Prop :=
    | sim_memory_intro
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
            exists to from ts,
              (<<FROM: time_map_latest loc ffrom ts>>) /\
              (<<TO: time_map_latest loc fto to>>) /\
              (<<GET:

              (<<GET: Memory.get loc fto mem_src = Some (ffrom, Message.undef)>>))
    .





forall Message.concrete




        view_map


          List.In (View.join (rel loc) (View.singleton_ur loc ts)) (views loc ts)



  Definition joined_released
             (views: Loc.t -> Time.t -> list View.t)
             (prom: Memory.t)
             (rel: Loc.t -> View.t): Prop :=
    forall loc ts from val released
           (GET: Memory.get loc ts prom = Some (from, Message.concrete val (Some released))),
      List.In (View.join (rel loc) (View.singleton_ur loc ts)) (views loc ts)
  .



    TView.t

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


    Definition

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




        { pln_map: timemap_map_ver vw_src.(View.pln) vw_tgt.(View.pln);
          rlx_map: timemap_map_ver vw_src.(View.rlx) vw_tgt.(View.rlx);
        }.



(<<VER: v <= f.(ver)>>) /\ (<<MAP: f v loc ts_tgt = Some ts>>) /\ (<<TLE: Time.le ts_src ts>>).

    Definition timemap_map (tm_src tm_tgt: TimeMap.t): Prop :=
      forall loc, time_map loc (tm_src loc) (tm_tgt loc).

    Record view_map (vw_src vw_tgt: View.t): Prop :=
      { pln_map: timemap_map vw_src.(View.pln) vw_tgt.(View.pln);
        rlx_map: timemap_map vw_src.(View.rlx) vw_tgt.(View.rlx);
      }.

    Definition time_map (loc: Loc.t) (ts_src ts_tgt: Time.t): Prop :=
      exists v ts, (<<VER: v <= f.(ver)>>) /\ (<<MAP: f v loc ts_tgt = Some ts>>) /\ (<<TLE: Time.le ts_src ts>>).

    Definition timemap_map (tm_src tm_tgt: TimeMap.t): Prop :=
      forall loc, time_map loc (tm_src loc) (tm_tgt loc).

    Record view_map (vw_src vw_tgt: View.t): Prop :=
      { pln_map: timemap_map vw_src.(View.pln) vw_tgt.(View.pln);
        rlx_map: timemap_map vw_src.(View.rlx) vw_tgt.(View.rlx);
      }.


      forall loc, time_map loc (tm_src loc) (tm_tgt loc).

  End MAP.


  Section MAPLE.
    Variable f0 f1: t.
    Hypothesis WF0: wf f0.
    Hypothesis WF1: wf f1.
    Hypothesis LE: le f0 f1.

    Lemma le_time_map:
      time_map f0 <3= time_map f1.
    Proof.
      ii. unfold time_map in *. dup LE. red in LE0. des.
      exists v. splits; auto. etrans; eauto.
    Qed.
  End MAPLE.

esplits.
      {

    Definition time_map (loc: Loc.t) (ts fts: Time.t): Prop :=
      exists v, (<<VER: v <= f.(ver)>>) /\ (<<MAP: f v loc ts = Some fts>>).
  End MAPPING
.


    Definition timemap_map (tm0 tm1: timemap): Prop :=
      forall loc, exists v,

End Mapping.

Definition


Record mapping: Type :=
  { map:> Loc.t -> list Time.t;
    ver: version;
    map_finite: exists l, forall loc ts (IN: List.In ts (map loc)), List.In (loc, ts) l;
  }.

    finite: exists l, Memory.map



alist_find

Section MAPPED.



  Variable f: Loc.t -> Time.t -> Time.t -> Prop.

  Definition mapping_map_le:=
    forall loc t0 t1 ft0 ft1
           (MAP0: f loc t0 ft0)
           (MAP1: f loc t1 ft1),
      Time.le t0 t1 -> Time.le ft0 ft1.

  Definition mapping_map_bot :=
    forall loc,
      f loc Time.bot Time.bot.

  Definition mapping_map_eq :=
    forall loc to ft0 ft1
           (MAP0: f loc to ft0)
           (MAP1: f loc to ft1),
      ft0 = ft1.

  Hypothesis map_le: mapping_map_le.
  Hypothesis map_bot: mapping_map_bot.
  Hypothesis map_eq: mapping_map_eq.

  Definition dom loc to: Prop :=
    exists fto, f loc to fto.

  Definition collapsed (loc: Loc.t) (t0 t1: Time.t): Prop :=
    exists ft,
      (<<MAP0: f loc t0 ft>>) /\ (<<MAP1: f loc t1 ft>>).

  Global Program Instance collapsed_Symmetric (loc: Loc.t): Symmetric (collapsed loc).
  Next Obligation.
    destruct H. eexists. des. splits; eauto.
  Qed.

  Lemma collapsed_inside
        loc
        t0 t1 t2 t3
        ft0 ft1 ft2 ft3
        (MAP0: f loc t0 ft0)
        (MAP1: f loc t1 ft1)
        (MAP2: f loc t2 ft2)
        (MAP3: f loc t3 ft3)
        (CLPS: collapsed loc t0 t3)
        (TLE0: Time.le t0 t1)
        (TLE1: Time.le t1 t2)
        (TLE2: Time.le t2 t3)
    :
      collapsed loc t1 t2.
  Proof.
    eapply map_le in TLE0; eauto.
    eapply map_le in TLE1; eauto.
    eapply map_le in TLE2; eauto.
    unfold collapsed in *. des.
    hexploit (map_eq MAP0 MAP4). i. subst.
    hexploit (map_eq MAP3 MAP5). i. subst.
    exploit TimeFacts.antisym; eauto. i. subst.
    exploit TimeFacts.antisym; eauto. i. subst.
    esplits; eauto.
  Qed.

  Lemma not_collapsed_outside
        loc
        t0 t1 t2 t3
        ft0 ft1 ft2 ft3
        (MAP0: f loc t0 ft0)
        (MAP1: f loc t1 ft1)
        (MAP2: f loc t2 ft2)
        (MAP3: f loc t3 ft3)
        (NCLPS: ~ collapsed loc t1 t2)
        (TLE0: Time.le t0 t1)
        (TLE1: Time.le t1 t2)
        (TLE2: Time.le t2 t3)
    :
      ~ collapsed loc t0 t3.
  Proof.
    ii. apply NCLPS. eapply collapsed_inside.
    - apply MAP0.
    - apply MAP1.
    - apply MAP2.
    - apply MAP3.
    - auto.
    - auto.
    - auto.
    - auto.
  Qed.

  Lemma map_lt_only_if
        loc t0 t1 ft0 ft1
        (MAP0: f loc t0 ft0)
        (MAP1: f loc t1 ft1)
    :
      Time.lt ft0 ft1 -> Time.lt t0 t1.
  Proof.
    set (TimeFacts.OrderTac.TO.lt_total t0 t1). des; eauto.
    - clarify. i.
      hexploit (map_eq MAP0 MAP1). i. subst.
      timetac.
    - exploit map_le.
      + eapply MAP1.
      + eapply MAP0.
      + left. eauto.
      + i. timetac.
  Qed.
  Hint Resolve map_lt_only_if.

  Definition map_eq_iff
             loc t0 t1 ft0 ft1
             (MAP0: f loc t0 ft0)
             (MAP1: f loc t1 ft1)
             (CLPS: ~ collapsed loc t0 t1)
    :
      t0 = t1 <-> ft0 = ft1.
  Proof.
    split; i; clarify; eauto.
    exfalso. apply CLPS. eexists. eauto.
  Qed.
  Hint Resolve map_eq_iff.

  Definition map_lt_iff
             loc t0 t1 ft0 ft1
             (MAP0: f loc t0 ft0)
             (MAP1: f loc t1 ft1)
             (CLPS: ~ collapsed loc t0 t1)
    :
      Time.lt t0 t1 <-> Time.lt ft0 ft1.
  Proof.
    split; i; cycle 1.
    { eapply map_lt_only_if; eauto. }
    exploit map_le.
    - eapply MAP0.
    - eapply MAP1.
    - left. eauto.
    - i. destruct x; auto. exfalso. apply CLPS.
      destruct H0. eexists. eauto.
  Qed.
  Hint Resolve map_lt_iff.

  Definition map_le_iff
             loc t0 t1 ft0 ft1
             (MAP0: f loc t0 ft0)
             (MAP1: f loc t1 ft1)
             (CLPS: ~ collapsed loc t0 t1)
    :
      Time.le t0 t1 <-> Time.le ft0 ft1.
  Proof.
    repeat rewrite Time.le_lteq.
    split; i; des; clarify; eauto.
    - left. erewrite <- map_lt_iff; eauto.
    - right. eapply map_eq_iff; eauto.
  Qed.
  Hint Resolve map_le_iff.

  Definition timemap_map (tm ftm: TimeMap.t): Prop :=
    forall loc, f loc (tm loc) (ftm loc).


  Record view_map (vw fvw: View.t): Prop :=
    view_map_intro
      { map_pln: timemap_map (View.pln vw) (View.pln fvw);
        map_rlx: timemap_map (View.rlx vw) (View.rlx fvw);
      }.

  Inductive opt_view_map: option View.t -> option View.t -> Prop :=
  | opt_view_map_some
      vw fvw
      (MAP: view_map vw fvw)
    :
      opt_view_map (Some vw) (Some fvw)
  | opt_view_map_none
    :
      opt_view_map None None
  .

  Record tview_map (vw fvw: TView.t): Prop :=
    tview_map_intro
      { map_rel: forall loc, view_map ((TView.rel vw) loc) ((TView.rel fvw) loc);
        map_cur: view_map (TView.cur vw) (TView.cur fvw);
        map_acq: view_map (TView.acq vw) (TView.acq fvw);
      }.

  Inductive msg_map: Message.t -> Message.t -> Prop :=
  | msg_map_reserve
    :
      msg_map Message.reserve Message.reserve
  | msg_map_concrete
      val released freleased
      (MAP: opt_view_map released freleased)
    :
      msg_map (Message.concrete val released) (Message.concrete val freleased)
  .

  Inductive memory_op_kind_map (loc: Loc.t) : Memory.op_kind -> Memory.op_kind -> Prop :=
  | memory_op_kind_map_add
    :
      memory_op_kind_map loc (Memory.op_kind_add) (Memory.op_kind_add)
  | memory_op_kind_map_split
      to fto msg fmsg
      (MSG: msg_map msg fmsg)
      (TO: f loc to fto)
    :
      memory_op_kind_map loc (Memory.op_kind_split to msg) (Memory.op_kind_split fto fmsg)
  | memory_op_kind_map_lower
      msg fmsg
      (MSG: msg_map msg fmsg)
    :
      memory_op_kind_map loc (Memory.op_kind_lower msg) (Memory.op_kind_lower fmsg)
  | memory_op_kind_map_cancel
    :
      memory_op_kind_map loc (Memory.op_kind_cancel) (Memory.op_kind_cancel)
  .
  Hint Constructors memory_op_kind_map.

  Inductive tevent_map: ThreadEvent.t -> ThreadEvent.t -> Prop :=
  | tevent_map_promise
      loc from ffrom to fto msg fmsg kind fkind
      (FROM: f loc from ffrom)
      (TO: f loc to fto)
      (MSG: msg_map msg fmsg)
      (KIND: memory_op_kind_map loc kind fkind)
    :
      tevent_map
        (ThreadEvent.promise loc ffrom fto fmsg fkind)
        (ThreadEvent.promise loc from to msg kind)
  | tevent_map_read
      loc to fto val released freleased freleased' ordr
      (TO: f loc to fto)
      (RELEASED: opt_view_map released freleased')
      (RELEASEDLE: View.opt_le freleased freleased')
    :
      tevent_map
        (ThreadEvent.read loc fto val freleased ordr)
        (ThreadEvent.read loc to val released ordr)
  | tevent_map_write
      loc from ffrom to fto val released freleased freleased' ordw
      (FROM: f loc from ffrom)
      (TO: f loc to fto)
      (RELEASED: opt_view_map released freleased')
      (RELEASEDLE: View.opt_le freleased freleased')
    :
      tevent_map
        (ThreadEvent.write loc ffrom fto val freleased ordw)
        (ThreadEvent.write loc from to val released ordw)
  | tevent_map_update
      loc from ffrom to fto valr valw releasedr freleasedr freleasedr'
      releasedw freleasedw freleasedw' ordr ordw
      (FROM: f loc from ffrom)
      (TO: f loc to fto)
      (RELEASEDR: opt_view_map releasedr freleasedr')
      (RELEASEDW: opt_view_map releasedw freleasedw')
      (RELEASEDRLE: View.opt_le freleasedr freleasedr')
      (RELEASEDWLE: View.opt_le freleasedw freleasedw')
    :
      tevent_map
        (ThreadEvent.update loc ffrom fto valr valw freleasedr freleasedw ordr ordw)
        (ThreadEvent.update loc from to valr valw releasedr releasedw ordr ordw)
  | tevent_map_fence
      or ow
    :
      tevent_map
        (ThreadEvent.fence or ow)
        (ThreadEvent.fence or ow)
  | tevent_map_syscall
      e
    :
      tevent_map
        (ThreadEvent.syscall e)
        (ThreadEvent.syscall e)
  | tevent_map_silent
    :
      tevent_map
        (ThreadEvent.silent)
        (ThreadEvent.silent)
  | tevent_map_failure
    :
      tevent_map
        (ThreadEvent.failure)
        (ThreadEvent.failure)
  .

  Inductive tevent_map_weak
  : ThreadEvent.t -> ThreadEvent.t -> Prop :=
  | tevent_map_weak_promise
      loc from ffrom to fto msg fmsg kind fkind
      (FROM: f loc from ffrom)
      (TO: f loc to fto)
      (MSG: msg = Message.reserve <-> fmsg = Message.reserve)
    :
      tevent_map_weak
        (ThreadEvent.promise loc ffrom fto fmsg fkind)
        (ThreadEvent.promise loc from to msg kind)
  | tevent_map_weak_read
      loc to fto val released freleased ordr
      (TO: f loc to fto)
    :
      tevent_map_weak
        (ThreadEvent.read loc fto val freleased ordr)
        (ThreadEvent.read loc to val released ordr)
  | tevent_map_weak_write
      loc from ffrom to fto val released freleased ordw
      (FROM: f loc from ffrom)
      (TO: f loc to fto)
    :
      tevent_map_weak
        (ThreadEvent.write loc ffrom fto val freleased ordw)
        (ThreadEvent.write loc from to val released ordw)
  | tevent_map_weak_update
      loc from ffrom to fto valr valw releasedr freleasedr
      releasedw freleasedw ordr ordw
      (FROM: f loc from ffrom)
      (TO: f loc to fto)
    :
      tevent_map_weak
        (ThreadEvent.update loc ffrom fto valr valw freleasedr freleasedw ordr ordw)
        (ThreadEvent.update loc from to valr valw releasedr releasedw ordr ordw)
  | tevent_map_weak_fence
      or ow
    :
      tevent_map_weak
        (ThreadEvent.fence or ow)
        (ThreadEvent.fence or ow)
  | tevent_map_weak_syscall
      e
    :
      tevent_map_weak
        (ThreadEvent.syscall e)
        (ThreadEvent.syscall e)
  | tevent_map_weak_silent
    :
      tevent_map_weak
        (ThreadEvent.silent)
        (ThreadEvent.silent)
  | tevent_map_weak_failure
    :
      tevent_map_weak
        (ThreadEvent.failure)
        (ThreadEvent.failure)
  .
  Hint Constructors tevent_map_weak.

  Lemma tevent_map_tevent_map_weak e fe
        (EVENT: tevent_map e fe)
    :
      tevent_map_weak e fe.
  Proof.
    inv EVENT; eauto. econs; eauto. inv MSG; ss.
  Qed.

  Definition non_collapsable (loc: Loc.t) (to: Time.t): Prop :=
    forall to' (TLE: Time.lt to' to),
      ~ collapsed loc to' to.

  Lemma map_lt_non_collapsable
        loc t0 t1 ft0 ft1
        (MAP0: f loc t0 ft0)
        (MAP1: f loc t1 ft1)
        (NCLPS: non_collapsable loc t1)
    :
      Time.lt t0 t1 <-> Time.lt ft0 ft1.
  Proof.
    split; i.
    - erewrite <- map_lt_iff; eauto.
    - eapply map_lt_only_if; eauto.
  Qed.

  Lemma time_join_map loc t0 t1 ft0 ft1
        (MAP0: f loc t0 ft0)
        (MAP1: f loc t1 ft1)
    :
      f loc (Time.join t0 t1) (Time.join ft0 ft1).
  Proof.
    unfold Time.join. des_ifs.
    - eapply map_le in l; eauto. timetac.
    - destruct l0; auto.
      + eapply map_lt_only_if in H; eauto.
        exfalso. eapply Time.lt_strorder. etrans; eauto.
      + destruct H. auto.
  Qed.

  Lemma timemap_bot_map
    :
      timemap_map TimeMap.bot TimeMap.bot.
  Proof.
    ii. eapply map_bot.
  Qed.

  Lemma view_bot_map
    :
      view_map View.bot View.bot.
  Proof.
    econs.
    - eapply timemap_bot_map; eauto.
    - eapply timemap_bot_map; eauto.
  Qed.

  Lemma timemap_singleton_map loc to fto
        (MAP: f loc to fto)
    :
      timemap_map (TimeMap.singleton loc to) (TimeMap.singleton loc fto).
  Proof.
    ii. unfold TimeMap.singleton.
    setoid_rewrite LocFun.add_spec. des_ifs.
  Qed.

  Lemma singleton_ur_map loc to fto
        (MAP: f loc to fto)
    :
      view_map (View.singleton_ur loc to) (View.singleton_ur loc fto).
  Proof.
    unfold View.singleton_ur. econs; ss.
    - eapply timemap_singleton_map; eauto.
    - eapply timemap_singleton_map; eauto.
  Qed.

  Lemma singleton_rw_map loc to fto
        (MAP: f loc to fto)
    :
      view_map (View.singleton_rw loc to) (View.singleton_rw loc fto).
  Proof.
    unfold View.singleton_ur. econs; ss.
    eapply timemap_singleton_map; eauto.
  Qed.

  Lemma singleton_ur_if_map loc to fto cond
        (MAP: f loc to fto)
    :
      view_map (View.singleton_ur_if cond loc to) (View.singleton_ur_if cond loc fto).
  Proof.
    unfold View.singleton_ur_if. des_ifs.
    - eapply singleton_ur_map; eauto.
    - eapply singleton_rw_map; eauto.
  Qed.

  Lemma timemap_join_map tm0 tm1 ftm0 ftm1
        (TM0: timemap_map tm0 ftm0)
        (TM1: timemap_map tm1 ftm1)
    :
      timemap_map (TimeMap.join tm0 tm1) (TimeMap.join ftm0 ftm1).
  Proof.
    ii. unfold TimeMap.join.
    eapply time_join_map; eauto.
  Qed.

  Lemma timemap_le_map tm0 tm1 ftm0 ftm1
        (TM0: timemap_map tm0 ftm0)
        (TM1: timemap_map tm1 ftm1)
        (TMLE: TimeMap.le tm0 tm1)
    :
      TimeMap.le ftm0 ftm1.
  Proof.
    ii. eapply map_le; eauto.
  Qed.

  Inductive memory_map2 m fm: Prop :=
  | memory_map2_intro
      (MAPPED: forall loc to from msg (GET: Memory.get loc to m = Some (from, msg)),
          msg = Message.reserve \/
          exists fto ffrom fmsg' fmsg,
            (<<TO: f loc to fto>>) /\
            (<<MSG: msg_map msg fmsg'>>) /\
            (<<MSGLE: Message.le fmsg fmsg'>>) /\
            (<<GET: Memory.get loc fto fm = Some (ffrom, fmsg)>>))
      (ONLY: forall loc fto ffrom fmsg
                    (GET: Memory.get loc fto fm = Some (ffrom, fmsg)),
          exists to from msg,
            (<<TO: f loc to fto>>) /\
            (<<GET: Memory.get loc to m = Some (from, msg)>>) /\
            (<<FROM: f loc from ffrom>>))
  .

  Inductive memory_map m fm: Prop :=
  | memory_map_intro
      (MAPPED: forall loc to from msg (GET: Memory.get loc to m = Some (from, msg)),
          msg = Message.reserve \/
          exists fto ffrom fmsg' fmsg,
            (<<TO: f loc to fto>>) /\
            (<<MSG: msg_map msg fmsg'>>) /\
            (<<MSGLE: Message.le fmsg fmsg'>>) /\
            (<<GET: Memory.get loc fto fm = Some (ffrom, fmsg)>>))
      (ONLY: forall loc fto ffrom fmsg
                    (GET: Memory.get loc fto fm = Some (ffrom, fmsg)),
          (exists to from fto' ffrom',
              (<<TO: f loc to fto'>>) /\
              (<<TS0: Time.le ffrom' ffrom>>) /\
              (<<TS1: Time.le fto fto'>>) /\
              (<<FROM: f loc from ffrom'>>) /\
              (<<COVERED: forall ts (ITV: Interval.mem (from, to) ts),
                  covered loc ts m>>)) \/
          (<<OUT: forall ts fts (MAP: f loc ts fts), Time.lt fts ffrom>>))
  .

  Lemma memory_map2_memory_map
    :
      memory_map2 <2= memory_map.
  Proof.
    ii. inv PR. econs; eauto.
    i. exploit ONLY; eauto. i. des.
    left. esplits.
    - eapply TO.
    - refl.
    - refl.
    - eapply FROM.
    - i. econs; eauto.
  Qed.

  Inductive promises_map m fm: Prop :=
  | promises_map_intro
      (MAPPED: forall loc to from msg (GET: Memory.get loc to m = Some (from, msg)),
          exists fto ffrom fmsg,
            (<<NCLPS: non_collapsable loc to>>) /\
            (<<TO: f loc to fto>>) /\
            (<<MSG: msg_map msg fmsg>>) /\
            (<<GET: Memory.get loc fto fm = Some (ffrom, fmsg)>>))
      (ONLY: forall loc fto ffrom fmsg
                    (GET: Memory.get loc fto fm = Some (ffrom, fmsg)),
          exists to from msg,
            (<<TO: f loc to fto>>) /\
            (<<GET: Memory.get loc to m = Some (from, msg)>>) /\
            (<<FROM: f loc from ffrom>>))
  .

  Definition collapsable_unwritable prom mem: Prop :=
    forall loc t
           (SAT: (fun loc' t' => exists ts0 ts1,
                      (<<CLPS: collapsed loc' ts0 ts1>>) /\
                      (<<ITV: Interval.mem (ts0, ts1) t'>>)) loc t),
      unwritable mem prom loc t.

  Lemma collapsable_unwritable_step pf e lang (th0 th1: Thread.t lang)
        (STEP: Thread.step pf e th0 th1)
        (WFMEM: collapsable_unwritable (Local.promises (Thread.local th0)) (Thread.memory th0))
    :
      collapsable_unwritable (Local.promises (Thread.local th1)) (Thread.memory th1) .
  Proof.
    ii. eapply unwritable_increase; eauto.
  Qed.

  Lemma collapsable_unwritable_steps P lang (th0 th1: Thread.t lang)
        (STEP: rtc (tau (@pred_step P lang)) th0 th1)
        (WFMEM: collapsable_unwritable (Local.promises (Thread.local th0)) (Thread.memory th0))
    :
      collapsable_unwritable (Local.promises (Thread.local th1)) (Thread.memory th1) .
  Proof.
    revert WFMEM. induction STEP; auto.
    i. eapply IHSTEP. inv H. inv TSTEP. inv STEP0.
    eapply collapsable_unwritable_step; eauto.
  Qed.

  Lemma promises_map_memory_map2 m fm
        (PROMISES: promises_map m fm)
    :
      memory_map2 m fm.
  Proof.
    inv PROMISES. econs; eauto.
    i. exploit MAPPED; eauto. i. des.
    right. esplits; eauto. refl.
  Qed.

  Lemma promises_map_memory_map m fm
        (PROMISES: promises_map m fm)
    :
      memory_map m fm.
  Proof.
    eapply memory_map2_memory_map.
    eapply promises_map_memory_map2; eauto.
  Qed.
  Hint Resolve promises_map_memory_map.

  Lemma closed_timemap_map m fm tm ftm
        (MEM: memory_map m fm)
        (TM: timemap_map tm ftm)
        (CLOSED: Memory.closed_timemap tm m)
    :
      Memory.closed_timemap ftm fm.
  Proof.
    inv MEM. ii. specialize (CLOSED loc). des.
    eapply MAPPED in CLOSED. des; clarify. inv MSG.
    specialize (TM loc).
    hexploit (map_eq TM TO). i. subst.
    inv MSGLE. esplits; eauto.
  Qed.

  Lemma closed_view_map m fm vw fvw
        (MEM: memory_map m fm)
        (VIEW: view_map vw fvw)
        (CLOSED: Memory.closed_view vw m)
    :
      Memory.closed_view fvw fm.
  Proof.
    inv CLOSED. inv VIEW. econs.
    - eapply closed_timemap_map; eauto.
    - eapply closed_timemap_map; eauto.
  Qed.

  Lemma closed_opt_view_map m fm vw fvw
        (MEM: memory_map m fm)
        (VIEW: opt_view_map vw fvw)
        (CLOSED: Memory.closed_opt_view vw m)
    :
      Memory.closed_opt_view fvw fm.
  Proof.
    inv CLOSED.
    - inv VIEW. econs. eapply closed_view_map; eauto.
    - inv VIEW. econs.
  Qed.

  Lemma view_join_map v0 v1 fv0 fv1
        (VIEW0: view_map v0 fv0)
        (VIEW1: view_map v1 fv1)
    :
      view_map (View.join v0 v1) (View.join fv0 fv1).
  Proof.
    inv VIEW0. inv VIEW1.
    unfold View.join. econs; ss.
    - eapply timemap_join_map; eauto.
    - eapply timemap_join_map; eauto.
  Qed.
