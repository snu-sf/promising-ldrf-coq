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

Require Import JoinedView.
Require Import SeqLift.
Require Import gSimulation.
Require Import Simple.


Record sim_tview
       (f: Mapping.ts)
       (flag_src: Loc.t -> bool)
       (rel_vers: Loc.t -> version)
       (tvw_src: TView.t) (tvw_tgt: TView.t)
  :
    Prop :=
  sim_tview_intro {
      sim_tview_rel: forall loc,
        sim_view (fun loc0 => loc0 <> loc) f (rel_vers loc) (tvw_src.(TView.rel) loc) (tvw_tgt.(TView.rel) loc);
      sim_tview_cur: sim_view (fun loc => flag_src loc = false) f (Mapping.vers f) tvw_src.(TView.cur) tvw_tgt.(TView.cur);
      sim_tview_acq: sim_view (fun loc => flag_src loc = false) f (Mapping.vers f) tvw_src.(TView.acq) tvw_tgt.(TView.acq);
      rel_vers_wf: forall loc, version_wf f (rel_vers loc);
    }.

Lemma sim_tview_mon_latest f0 f1 flag_src rel_vers tvw_src tvw_tgt
      (SIM: sim_tview f0 flag_src rel_vers tvw_src tvw_tgt)
      (LE: Mapping.les f0 f1)
      (WF0: Mapping.wfs f0)
      (WF1: Mapping.wfs f1)
  :
    sim_tview f1 flag_src rel_vers tvw_src tvw_tgt.
Proof.
  econs.
  { i. erewrite <- sim_view_mon_mapping; [eapply SIM|..]; eauto. eapply SIM. }
  { eapply sim_view_mon_latest; eauto. eapply SIM. }
  { eapply sim_view_mon_latest; eauto. eapply SIM. }
  { i. eapply version_wf_mapping_mon; eauto. eapply SIM. }
Qed.

Lemma sim_tview_tgt_mon f flag_src rel_vers tvw_src tvw_tgt0 tvw_tgt1
      (SIM: sim_tview f flag_src rel_vers tvw_src tvw_tgt0)
      (TVIEW: TView.le tvw_tgt0 tvw_tgt1)
  :
    sim_tview f flag_src rel_vers tvw_src tvw_tgt1.
Proof.
  econs.
  { i. eapply sim_view_mon_tgt.
    { eapply SIM. }
    { eapply TVIEW. }
  }
  { eapply sim_view_mon_tgt.
    { eapply SIM. }
    { eapply TVIEW. }
  }
  { eapply sim_view_mon_tgt.
    { eapply SIM. }
    { eapply TVIEW. }
  }
  { eapply SIM. }
Qed.

Variant sim_local
        (f: Mapping.ts) (vers: versions)
        (srctm: Loc.t -> Time.t)
        (flag_src: Loc.t -> bool)
        (flag_tgt: Loc.t -> bool)
  :
    Local.t -> Local.t -> Prop :=
| sim_local_intro
    tvw_src tvw_tgt prom_src prom_tgt rel_vers
    (TVIEW: sim_tview f flag_src rel_vers tvw_src tvw_tgt)
    (PROMISES: sim_promises srctm flag_src flag_tgt f vers prom_src prom_tgt)
    (RELVERS: wf_release_vers vers prom_tgt rel_vers)
    (FLAGSRC: forall loc (FLAG: flag_src loc = true),
        (<<RLX: tvw_src.(TView.cur).(View.rlx) loc = tvw_src.(TView.cur).(View.pln) loc>>))
    (SRCTM: forall loc, srctm loc = tvw_src.(TView.cur).(View.rlx) loc)
  :
    sim_local
      f vers srctm flag_src flag_tgt
      (Local.mk tvw_src prom_src)
      (Local.mk tvw_tgt prom_tgt)
.

Lemma sim_local_tgt_mon f vers srctm flag_src flag_tgt lc_src lc_tgt0 lc_tgt1
      (SIM: sim_local f vers srctm flag_src flag_tgt lc_src lc_tgt0)
      (PROM: lc_tgt0.(Local.promises) = lc_tgt1.(Local.promises))
      (TVIEW: TView.le lc_tgt0.(Local.tview) lc_tgt1.(Local.tview))
  :
    sim_local f vers srctm flag_src flag_tgt lc_src lc_tgt1.
Proof.
  inv SIM. destruct lc_tgt1. ss. clarify. econs; eauto.
  eapply sim_tview_tgt_mon; eauto.
Qed.

Lemma sim_local_consistent f vers srctm flag_src flag_tgt lc_src lc_tgt
      (CONSISTENT: Local.promise_consistent lc_tgt)
      (SIM: sim_local f vers srctm flag_src flag_tgt lc_src lc_tgt)
      (WF: Mapping.wfs f)
  :
    Local.promise_consistent lc_src.
Proof.
  inv SIM. ii. ss.
  hexploit sim_promises_get_if; eauto. i. des.
  { eapply sim_timestamp_lt.
    { eapply sim_view_rlx.
      { eapply sim_tview_cur. eauto. }
      { ss. destruct (flag_src loc) eqn:FLAG; auto.
        erewrite sim_promises_none in PROMISE; eauto; ss.
      }
    }
    { eauto. }
    { eapply CONSISTENT; eauto. inv MSG0; ss. }
    { eauto. }
    { eapply mapping_latest_wf_loc. }
  }
  { rewrite SRCTM in *. auto. }
Qed.

Lemma sim_local_consistent_ex f vers flag_src flag_tgt lc_src lc_tgt
      (CONSISTENT: Local.promise_consistent lc_tgt)
      (SIM: exists srctm, sim_local f vers srctm flag_src flag_tgt lc_src lc_tgt)
      (WF: Mapping.wfs f)
  :
    Local.promise_consistent lc_src.
Proof.
  des. eapply sim_local_consistent; eauto.
Qed.

Lemma sim_local_racy f vers srctm flag_src flag_tgt lc_src lc_tgt mem_src mem_tgt loc to ord
      (CONSISTENT: Local.promise_consistent lc_tgt)
      (MEM: sim_memory srctm flag_src f vers mem_src mem_tgt)
      (SIM: sim_local f vers srctm flag_src flag_tgt lc_src lc_tgt)
      (WF: Mapping.wfs f)
      (RACY: Local.is_racy lc_tgt mem_tgt loc to ord)
      (FLAGSRC: flag_src loc = false)
      (FLAGTGT: flag_tgt loc = false)
  :
    exists to_src, Local.is_racy lc_src mem_src loc to_src ord.
Proof.
  inv RACY. hexploit sim_memory_get; eauto. i. des.
  exists to_src. econs; eauto.
  { inv SIM. ss.
    destruct (Memory.get loc to_src prom_src) eqn:EQ; ss.
    destruct p. hexploit sim_promises_get_if; eauto. i. des; ss; clarify.
    eapply sim_timestamp_exact_unique in TO; eauto; clarify.
  }
  { unfold TView.racy_view in *. eapply sim_timestamp_lt; eauto.
    { inv SIM. ss. eapply TVIEW. auto. }
    { eapply mapping_latest_wf_loc. }
  }
  { inv MSG; ss. }
  { i. hexploit MSG2; auto. i. inv MSG; ss. }
Qed.

Variant max_value_src (loc: Loc.t) (v: option Const.t)
        (mem: Memory.t)
  :
    forall (lc: Local.t), Prop :=
| max_value_src_intro
    tvw prom
    (MAX: forall v0 (VAL: v = Some v0),
        exists released,
          (<<MAX: max_readable
                    mem
                    prom
                    loc
                    (tvw.(TView.cur).(View.pln) loc)
                    v0 released>>))
    (NONMAX: forall (VAL: v = None),
        forall val released,
          ~ max_readable mem prom loc (tvw.(TView.cur).(View.pln) loc) val released)
  :
    max_value_src loc v mem (Local.mk tvw prom)
.

Definition max_values_src (vs: Loc.t -> option Const.t)
           (mem: Memory.t) (lc: Local.t): Prop :=
  forall loc, max_value_src loc (vs loc) mem lc.

Variant max_value_tgt (loc: Loc.t) (v: option Const.t)
        (mem: Memory.t)
  :
    forall (lc: Local.t), Prop :=
| max_value_tgt_intro
    tvw prom
    (MAX: forall v0 (VAL: v = Some v0),
        exists released,
          (<<MAX: max_readable
                    mem
                    prom
                    loc
                    (tvw.(TView.cur).(View.pln) loc)
                    v0 released>>))
  :
    max_value_tgt loc v mem (Local.mk tvw prom)
.

Definition max_values_tgt (vs: Loc.t -> option Const.t)
           (mem: Memory.t) (lc: Local.t): Prop :=
  forall loc, max_value_tgt loc (vs loc) mem lc.

Lemma max_value_tgt_mon loc v mem lc0 lc1
      (MAXTGT: max_value_tgt loc v mem lc0)
      (PROM: lc0.(Local.promises) = lc1.(Local.promises))
      (TVIEW: TView.le lc0.(Local.tview) lc1.(Local.tview))
      (LOCAL: Local.wf lc1 mem)
      (CONSISTENT: Local.promise_consistent lc1)
  :
  max_value_tgt loc v mem lc1.
Proof.
  inv MAXTGT. ss. subst. destruct lc1. econs. i.
  hexploit MAX; eauto. i. des. ss.
  hexploit max_readable_view_mon; eauto.
Qed.

Lemma max_values_tgt_mon vs mem lc0 lc1
      (MAXTGT: max_values_tgt vs mem lc0)
      (PROM: lc0.(Local.promises) = lc1.(Local.promises))
      (TVIEW: TView.le lc0.(Local.tview) lc1.(Local.tview))
      (LOCAL: Local.wf lc1 mem)
      (CONSISTENT: Local.promise_consistent lc1)
  :
    max_values_tgt vs mem lc1.
Proof.
  ii. eapply max_value_tgt_mon; eauto.
Qed.

Definition reserved_space_empty (f: Mapping.ts) (flag_src: Loc.t -> bool)
           (prom_tgt: Memory.t) (mem_src: Memory.t): Prop :=
  forall loc to_tgt from_tgt
         (GETTGT: Memory.get loc to_tgt prom_tgt = Some (from_tgt, Message.reserve))
         (FLAG: flag_src loc = true),
  exists to_src from_src,
    (<<FROM: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) from_src from_tgt>>) /\
    (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src to_tgt>>) /\
    (<<DISJOINT: forall from to msg
                        (GETSRC: Memory.get loc to mem_src = Some (from, msg)),
        Interval.disjoint (from_src, to_src) (from, to)>>).

Lemma reserved_space_empty_mon_strong f0 f1 flag_src prom_tgt mem_src
      (RESERVED: reserved_space_empty f0 flag_src prom_tgt mem_src)
      (MAPLE: Mapping.les_strong f0 f1)
      (MAPWF0: Mapping.wfs f0)
      (MAPWF1: Mapping.wfs f1)
  :
    reserved_space_empty f1 flag_src prom_tgt mem_src.
Proof.
  ii. exploit RESERVED; eauto. i. des. esplits; eauto.
  { eapply sim_timestamp_exact_mon_strong; eauto. }
  { eapply sim_timestamp_exact_mon_strong; eauto. }
Qed.

Lemma reserved_space_empty_reserve_decr f flag_src prom_tgt0 prom_tgt1 mem_src
      (RESERVED: reserved_space_empty f flag_src prom_tgt0 mem_src)
      (DECR: forall loc to from
                    (GET: Memory.get loc to prom_tgt1 = Some (from, Message.reserve))
                    (FLAG: flag_src loc = true),
          Memory.get loc to prom_tgt0 = Some (from, Message.reserve))
  :
    reserved_space_empty f flag_src prom_tgt1 mem_src.
Proof.
  ii. exploit RESERVED; eauto.
Qed.

Lemma memory_write_reserve_same prom0 mem0 loc from to msg prom1 mem1 kind
      (WRITE: Memory.write prom0 mem0 loc from to msg prom1 mem1 kind)
  :
    forall loc to from
           (GET: Memory.get loc to prom1 = Some (from, Message.reserve)),
      Memory.get loc to prom0 = Some (from, Message.reserve).
Proof.
  inv WRITE. i. erewrite Memory.remove_o in GET; eauto.
  inv PROMISE.
  { i. erewrite Memory.add_o in GET; eauto. des_ifs. }
  { i. erewrite Memory.split_o in GET; eauto. des_ifs. }
  { i. erewrite Memory.lower_o in GET; eauto. des_ifs. }
  { i. erewrite Memory.remove_o in GET; eauto. des_ifs. }
Qed.

Lemma memory_write_reserve_same_rev prom0 mem0 loc from to msg prom1 mem1 kind
      (WRITE: Memory.write prom0 mem0 loc from to msg prom1 mem1 kind)
      (MSG: msg <> Message.reserve)
  :
    forall loc to from
           (GET: Memory.get loc to prom0 = Some (from, Message.reserve)),
      Memory.get loc to prom1 = Some (from, Message.reserve).
Proof.
  inv WRITE. i. erewrite Memory.remove_o; eauto. inv PROMISE.
  { i. erewrite Memory.add_o; eauto. des_ifs.
    ss. des; clarify. eapply Memory.add_get0 in PROMISES. des; clarify.
  }
  { i. erewrite Memory.split_o; eauto. des_ifs.
    { ss. des; clarify. eapply Memory.split_get0 in PROMISES. des; clarify. }
    { ss. des; clarify. eapply Memory.split_get0 in PROMISES. des; clarify. }
  }
  { i. erewrite Memory.lower_o; eauto. des_ifs.
    ss. des; clarify. eapply Memory.lower_get0 in PROMISES. des; clarify. inv MSG_LE; ss.
  }
  { des_ifs. }
Qed.

Lemma memory_write_na_reserve_same prom0 mem0 loc ts from to val prom1 mem1 kind kinds msgs
      (WRITE: Memory.write_na ts prom0 mem0 loc from to val prom1 mem1 kinds msgs kind)
  :
    forall loc to from
           (GET: Memory.get loc to prom1 = Some (from, Message.reserve)),
      Memory.get loc to prom0 = Some (from, Message.reserve).
Proof.
  induction WRITE.
  { eapply memory_write_reserve_same; eauto. }
  { i. eapply IHWRITE in GET.
    eapply memory_write_reserve_same; eauto.
  }
Qed.

Lemma memory_write_na_reserve_same_rev prom0 mem0 loc ts from to val prom1 mem1 kind kinds msgs
      (WRITE: Memory.write_na ts prom0 mem0 loc from to val prom1 mem1 kinds msgs kind)
  :
    forall loc to from
           (GET: Memory.get loc to prom0 = Some (from, Message.reserve)),
      Memory.get loc to prom1 = Some (from, Message.reserve).
Proof.
  induction WRITE.
  { eapply memory_write_reserve_same_rev; eauto; ss. }
  { i. eapply IHWRITE.
    eapply memory_write_reserve_same_rev; eauto; ss.
    unguard. des; clarify.
  }
Qed.

Lemma reserved_space_empty_covered_decr f flag_src prom_tgt mem_src0 mem_src1
      (RESERVED: reserved_space_empty f flag_src prom_tgt mem_src0)
      (DECR: forall loc ts (FLAG: flag_src loc = true) (COVER: covered loc ts mem_src1), covered loc ts mem_src0)
  :
    reserved_space_empty f flag_src prom_tgt mem_src1.
Proof.
  ii. exploit RESERVED; eauto. i. des. esplits; eauto.
  ii. exploit DECR; eauto.
  { econs; eauto. }
  i. inv x0. eapply DISJOINT; eauto.
Qed.

Lemma reserved_space_empty_unchanged_loc
      f flag_src prom_tgt mem_src0 mem_src1
      (RESERVED: reserved_space_empty f flag_src prom_tgt mem_src0)
      (UNCH: forall loc (FLAG: flag_src loc = true), unchanged_loc_memory loc mem_src0 mem_src1)
  :
    reserved_space_empty f flag_src prom_tgt mem_src1.
Proof.
  ii. exploit RESERVED; eauto. i. des. esplits; eauto.
  ii. hexploit UNCH; eauto. i. inv H. rewrite UNCH0 in GETSRC; eauto.
  eapply DISJOINT; eauto.
Qed.

Lemma reserved_space_empty_add f flag_src prom_tgt mem_src0 mem_src1
      loc from to msg
      (RESERVED: reserved_space_empty f flag_src prom_tgt mem_src0)
      (ADD: Memory.add mem_src0 loc from to msg mem_src1)
      (TOP: top_time from (f loc))
  :
    reserved_space_empty f flag_src prom_tgt mem_src1.
Proof.
  ii. exploit RESERVED; eauto. i. des. esplits; eauto.
  i. erewrite Memory.add_o in GETSRC; eauto. des_ifs; eauto.
  ss. des; clarify. eapply interval_le_disjoint.
  eapply TOP in TO. left. auto.
Qed.

Lemma cancel_future_memory_le loc prom0 mem0 prom1 mem1
      (CANCEL: cancel_future_memory loc prom0 mem0 prom1 mem1)
  :
    Memory.le prom1 prom0.
Proof.
  induction CANCEL.
  { refl. }
  etrans; eauto. inv CANCEL. eapply remove_le; eauto.
Qed.

Lemma cancel_future_memory_get loc prom0 mem0 prom1 mem1
      (CANCEL: cancel_future_memory loc prom0 mem0 prom1 mem1)
  :
    forall to,
      Memory.get loc to mem1 =
      match Memory.get loc to mem0 with
      | None => None
      | Some (from, msg) =>
        match Memory.get loc to prom0 with
        | None => Some (from, msg)
        | Some _ =>
          match Memory.get loc to prom1 with
          | None => None
          | Some _ => Some (from, msg)
          end
        end
      end.
Proof.
  induction CANCEL.
  { i. des_ifs. }
  i. inv CANCEL. rewrite IHCANCEL.
  erewrite (@Memory.remove_o mem1); eauto.
  erewrite (@Memory.remove_o prom1); eauto. des_ifs.
  { ss. des; clarify. destruct p0.
    eapply cancel_future_memory_le in Heq2; eauto.
    eapply Memory.remove_get0 in PROMISES. des; clarify.
  }
  { ss. des; clarify.
    eapply Memory.remove_get0 in PROMISES. des; clarify.
  }
Qed.

Lemma cancel_future_memory_memory_le loc prom0 mem0 prom1 mem1
      (CANCEL: cancel_future_memory loc prom0 mem0 prom1 mem1)
      (MLE: Memory.le prom0 mem0)
  :
    Memory.le prom1 mem1.
Proof.
  revert MLE. induction CANCEL; auto. i. eapply IHCANCEL.
  eapply promise_memory_le; eauto.
Qed.

Lemma reserved_space_empty_fulfilled_memory f srctm vers
      flag_src0 flag_src1 flag_tgt prom_tgt mem_src0 mem_src1
      loc prom_src0 prom_src1
      (RESERVED: reserved_space_empty f flag_src0 prom_tgt mem_src0)
      (CANCEL: cancel_future_memory loc prom_src0 mem_src0 prom_src1 mem_src1)
      (PROMISE: sim_promises srctm flag_src0 flag_tgt f vers prom_src0 prom_tgt)
      (MLE: Memory.le prom_src0 mem_src0)
      (NONE: forall from to msg
                    (GET: Memory.get loc to prom_src1 = Some (from, msg)),
          msg <> Message.reserve)
      (FLAGS: forall loc0 (FLAG: flag_src1 loc0 = true), flag_src0 loc0 = true \/ loc0 = loc)
  :
    reserved_space_empty f flag_src1 prom_tgt mem_src1.
Proof.
  destruct (flag_src0 loc) eqn:EQ.
  { revert RESERVED. clear MLE NONE PROMISE. induction CANCEL; auto.
    { ii. exploit RESERVED; eauto. exploit FLAGS; eauto. i. des; clarify. }
    i. eapply IHCANCEL.
    inv CANCEL. eapply reserved_space_empty_covered_decr; eauto.
    i. eapply remove_covered in COVER; eauto. des; eauto.
  }
  { ii. hexploit cancel_future_memory_memory_le; eauto. intros MLE1.
    destruct (Loc.eq_dec loc0 loc).
    { subst. hexploit sim_promises_get; eauto. i. des. esplits; eauto.
      i. hexploit GET; eauto. i. des. dup GET0. eapply MLE in GET0.
      dup GETSRC. erewrite cancel_future_memory_get in GETSRC; eauto. des_ifs.
      { hexploit Memory.get_disjoint.
        { eapply GET0. }
        { eapply Heq. }
        i. des; clarify. exfalso.
        destruct p0. dup Heq1. eapply MLE1 in Heq1. clarify.
        inv MSG. eapply NONE in Heq2; eauto.
      }
      { hexploit Memory.get_disjoint.
        { eapply GET0. }
        { eapply Heq. }
        i. des; clarify.
      }
    }
    { exploit RESERVED; eauto.
      { eapply FLAGS in FLAG. des; clarify. }
      i. des. esplits; eauto.
      i. eapply cancel_future_unchanged_loc in CANCEL; eauto. des.
      inv MEM. rewrite UNCH in GETSRC. eauto.
    }
  }
Qed.

Variant sim_thread
        (f: Mapping.ts) (vers: versions)
        (flag_src: Loc.t -> bool)
        (flag_tgt: Loc.t -> bool)
        (vs_src: Loc.t -> option Const.t)
        (vs_tgt: Loc.t -> option Const.t)
        mem_src mem_tgt lc_src lc_tgt sc_src sc_tgt: Prop :=
| sim_thread_intro
    srctm
    (SC: sim_timemap (fun _ => True) f (Mapping.vers f) sc_src sc_tgt)
    (MEM: sim_memory srctm flag_src f vers mem_src mem_tgt)
    (LOCAL: sim_local f vers srctm flag_src flag_tgt lc_src lc_tgt)
    (MAXSRC: max_values_src vs_src mem_src lc_src)
    (MAXTGT: max_values_tgt vs_tgt mem_tgt lc_tgt)
    (PERM: forall loc, option_rel (fun _ _ => True) (vs_src loc) (vs_tgt loc))
    (FIN: __guard__(exists dom, (<<DOM: forall loc, (flag_src loc = true) <-> (List.In loc dom)>>)))
    (VERSIONED: versioned_memory vers mem_tgt)
    (SIMCLOSED: sim_closed_memory f mem_src)
    (MAXTIMES: forall loc (FLAG: flag_src loc = true),
        srctm loc = Memory.max_ts loc mem_src)
    (RESERVED: reserved_space_empty f flag_src lc_tgt.(Local.promises) mem_src)
    (FINALIZED: promise_finalized f lc_src.(Local.promises) mem_tgt)
.

Lemma max_value_src_exists loc mem lc
  :
    exists v,
      (<<MAX: max_value_src loc v mem lc>>).
Proof.
  destruct (classic (exists val released, max_readable mem lc.(Local.promises) loc (View.pln (TView.cur lc.(Local.tview)) loc) val released)).
  { des. exists (Some val). splits. destruct lc. econs; ss.
    i. clarify. esplits; eauto.
  }
  { exists None. splits. destruct lc. econs; ss.
    ii. eapply H. eauto.
  }
Qed.

Lemma max_values_src_exists mem lc
  :
    exists vs,
      (<<MAX: max_values_src vs mem lc>>).
Proof.
  eapply (choice (fun loc v => max_value_src loc v mem lc)).
  i. eapply max_value_src_exists.
Qed.

Lemma max_value_src_inj loc mem lc v0 v1
      (MAX0: max_value_src loc v0 mem lc)
      (MAX1: max_value_src loc v1 mem lc)
  :
    v0 = v1.
Proof.
  inv MAX0. inv MAX1. destruct v0, v1; auto.
  { hexploit MAX; eauto. hexploit MAX0; eauto. i. des.
    f_equal. eapply max_readable_inj; eauto.
  }
  { exfalso. hexploit MAX; eauto. i. des. eapply NONMAX0; eauto. }
  { exfalso. hexploit MAX0; eauto. i. des. eapply NONMAX; eauto. }
Qed.

Lemma max_value_src_mon loc v mem lc0 lc1
      (MAXSRC: max_value_src loc (Some v) mem lc0)
      (PROM: lc0.(Local.promises) = lc1.(Local.promises))
      (TVIEW: TView.le lc0.(Local.tview) lc1.(Local.tview))
      (LOCAL: Local.wf lc1 mem)
      (CONSISTENT: Local.promise_consistent lc1)
  :
    max_value_src loc (Some v) mem lc1.
Proof.
  inv MAXSRC. ss. subst. destruct lc1. econs; ss.
  i. clarify.
  hexploit MAX; eauto. i. des. esplits.
  hexploit max_readable_view_mon; eauto.
Qed.

Lemma race_non_max_readable mem prom tvw loc to
      (MAX: Local.is_racy (Local.mk tvw prom) mem loc to Ordering.na)
  :
    forall val released, ~ max_readable mem prom loc (tvw.(TView.cur).(View.pln) loc) val released.
Proof.
  ii. inv H. inv MAX.
  eapply MAX0 in RACE; eauto. ss. clarify.
Qed.

Lemma sim_memory_src_flag_max_concrete
      f vers srctm flag_src
      mem_src mem_tgt
      (SIM: sim_memory srctm flag_src f vers mem_src mem_tgt)
      loc
      (FLAG: flag_src loc = true)
      (CLOSED: exists from msg, Memory.get loc (srctm loc) mem_src = Some (from, msg))
  :
    Memory.max_ts loc mem_src = srctm loc.
Proof.
  des. hexploit Memory.max_ts_spec.
  { eapply CLOSED. }
  i. des. eapply TimeFacts.antisym; eauto.
  hexploit sim_memory_top; eauto. intros TOP.
  hexploit sim_memory_sound.
  { eauto. }
  { eapply GET. }
  i. des.
  { eapply TOP in TO. left. eapply TimeFacts.le_lt_lt; eauto. }
  { clarify. }
Qed.

Lemma max_value_src_flag_none f vers srctm flag_src flag_tgt lc_src lc_tgt mem_src mem_tgt loc
      (MEM: sim_memory srctm flag_src f vers mem_src mem_tgt)
      (LOCAL: sim_local f vers srctm flag_src flag_tgt lc_src lc_tgt)
      (MAX: max_value_src loc None mem_src lc_src)
      (LOCALWF: Local.wf lc_src mem_src)
      (WF: Mapping.wfs f)
  :
    flag_src loc = false.
Proof.
  destruct (flag_src loc) eqn:FLAG; auto. exfalso.
  inv LOCAL. hexploit FLAGSRC; eauto. i. des. subst.
  inv LOCALWF. inv TVIEW_CLOSED.
  inv CUR. exploit RLX; eauto. i. des. ss.
  inv MAX. hexploit NONMAX; eauto. ii. eapply H0. econs.
  { rewrite <- H. eauto. }
  { inv PROMISES. eapply NONE; eauto. }
  { i. hexploit sim_memory_src_flag_max_concrete; eauto.
    { rewrite SRCTM. eauto. }
    i. eapply Memory.max_ts_spec in GET. des.
    rewrite H1 in MAX. exfalso.
    eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
    { eapply TS. }
    { rewrite <- H. rewrite <- SRCTM. eauto. }
  }
Qed.

Lemma promise_max_readable
      prom0 mem0 loc from to msg prom1 mem1 kind tvw
      (PROMISE: Memory.promise prom0 mem0 loc from to msg prom1 mem1 kind)
  :
  forall val0 released0,
    max_readable mem0 prom0 loc tvw val0 released0 <-> max_readable mem1 prom1 loc tvw val0 released0.
Proof.
  i. split.
  { intros MAX. inv MAX.
    hexploit unchangable_promise.
    { eauto. }
    { econs; eauto. }
    i. inv H. ss. econs; eauto.
    i. inv PROMISE.
    { erewrite Memory.add_o; eauto.
      erewrite (@Memory.add_o mem1 mem0) in GET1; eauto. des_ifs.
      eapply MAX0; eauto.
    }
    { erewrite Memory.split_o; eauto.
      erewrite (@Memory.split_o mem1 mem0) in GET1; eauto. des_ifs.
      eapply MAX0; eauto.
    }
    { erewrite Memory.lower_o; eauto.
      erewrite (@Memory.lower_o mem1 mem0) in GET1; eauto. des_ifs.
      eapply MAX0; eauto.
    }
    { erewrite Memory.remove_o; eauto.
      erewrite (@Memory.remove_o mem1 mem0) in GET1; eauto. des_ifs.
      eapply MAX0; eauto.
    }
  }
  { i. inv H. inv PROMISE.
    { erewrite Memory.add_o in GET; eauto.
      erewrite Memory.add_o in NONE; eauto. des_ifs.
      econs; eauto. i.
      hexploit MAX; eauto.
      { eapply Memory.add_get1; eauto. }
      i. erewrite Memory.add_o in H; eauto.
      des_ifs. ss. des; clarify.
      eapply Memory.add_get0 in MEM. des; clarify.
    }
    { erewrite Memory.split_o in GET; eauto.
      erewrite Memory.split_o in NONE; eauto. des_ifs.
      econs; eauto. i.
      hexploit Memory.split_o; [eapply MEM|]. i.
      rewrite GET0 in H. des_ifs.
      { ss. des; clarify. eapply Memory.split_get0 in MEM. des; clarify. }
      { ss. des; clarify. eapply Memory.split_get0 in PROMISES.
        eapply Memory.split_get0 in MEM. des; clarify.
      }
      { ss. des; clarify. hexploit MAX; eauto. i.
        erewrite Memory.split_o in H0; eauto.
        des_ifs; ss; des; clarify.
      }
    }
    { erewrite Memory.lower_o in GET; eauto.
      erewrite Memory.lower_o in NONE; eauto. des_ifs.
      econs; eauto. i.
      hexploit Memory.lower_o; [eapply MEM|]. i.
      rewrite GET0 in H. des_ifs.
      { ss. des; clarify. eapply Memory.lower_get0 in MEM. des; clarify.
        eapply Memory.lower_get0 in PROMISES. des; eauto.
      }
      { ss. des; clarify. hexploit MAX; eauto. i.
        erewrite Memory.lower_o in H0; eauto.
        des_ifs; ss; des; clarify.
      }
    }
    { erewrite Memory.remove_o in GET; eauto.
      erewrite Memory.remove_o in NONE; eauto. des_ifs.
      econs; eauto. i.
      hexploit Memory.remove_o; [eapply MEM|]. i.
      rewrite GET0 in H. des_ifs.
      { ss. des; clarify. eapply Memory.remove_get0 in MEM. des; clarify. }
      { ss. des; clarify. hexploit MAX; eauto. i.
        erewrite Memory.remove_o in H0; eauto.
        des_ifs; ss; des; clarify.
      }
    }
  }
Qed.

Lemma promise_max_values_src
      lc0 mem0 loc from to msg lc1 mem1 kind vs
      (PROMISE: Local.promise_step lc0 mem0 loc from to msg lc1 mem1 kind)
      (MAX: max_values_src vs mem0 lc0)
  :
  max_values_src vs mem1 lc1.
Proof.
  inv PROMISE. ii. specialize (MAX loc0). inv MAX.
  destruct (Loc.eq_dec loc0 loc); subst.
  { econs.
    { i. hexploit MAX0; eauto. i. des. esplits. ss.
      erewrite <- promise_max_readable; eauto.
    }
    { i. hexploit NONMAX; eauto. ii. eapply H. ss.
      erewrite promise_max_readable; eauto.
    }
  }
  { eapply promise_unchanged_loc in PROMISE0; eauto. des.
    econs.
    { i. hexploit MAX0; eauto. i. des. esplits. ss.
      erewrite <- unchanged_loc_max_readable; eauto.
    }
    { i. hexploit NONMAX; eauto. ii. eapply H. ss.
      erewrite unchanged_loc_max_readable; eauto.
    }
  }
Qed.

Lemma promise_step_max_values_src
      lang st0 st1 pf e lc0 lc1 sc0 sc1 mem0 mem1 vs
      (PROMISE: Thread.promise_step pf e (Thread.mk lang st0 lc0 sc0 mem0) (Thread.mk _ st1 lc1 sc1 mem1))
      (MAX: max_values_src vs mem0 lc0)
  :
  max_values_src vs mem1 lc1.
Proof.
  inv PROMISE. eapply promise_max_values_src; eauto.
Qed.

Require Import Pred.

Lemma promise_steps_max_values_src
      lang st0 st1 lc0 lc1 sc0 sc1 mem0 mem1 vs
      (PROMISE: rtc (tau (@pred_step is_promise _)) (Thread.mk lang st0 lc0 sc0 mem0) (Thread.mk _ st1 lc1 sc1 mem1))
      (MAX: max_values_src vs mem0 lc0)
  :
  max_values_src vs mem1 lc1.
Proof.
  remember (Thread.mk lang st0 lc0 sc0 mem0).
  remember (Thread.mk lang st1 lc1 sc1 mem1).
  revert st0 st1 lc0 lc1 sc0 sc1 mem0 mem1 Heqt Heqt0 MAX. induction PROMISE; i; clarify.
  inv H. inv TSTEP. inv STEP. inv STEP0; [|inv STEP; inv LOCAL; ss].
  destruct y. eapply promise_step_max_values_src in STEP; eauto.
Qed.

Lemma no_flag_max_value_same f vers srctm flag_src flag_tgt lc_src lc_tgt mem_src mem_tgt loc v_src
      (MEM: sim_memory srctm flag_src f vers mem_src mem_tgt)
      (LOCAL: sim_local f vers srctm flag_src flag_tgt lc_src lc_tgt)
      (FLAGSRC: flag_src loc = false)
      (FLAGTGT: flag_tgt loc = false)
      (MAX: max_value_src loc (Some v_src) mem_src lc_src)
      (LOCALWF: Local.wf lc_tgt mem_tgt)
      (CONSISTENT: Local.promise_consistent lc_tgt)
      (WF: Mapping.wfs f)
  :
  exists v_tgt,
    (<<MAX: max_value_tgt loc (Some v_tgt) mem_tgt lc_tgt>>) /\ (<<VAL: Const.le v_tgt v_src>>).
Proof.
  inv MAX. destruct lc_tgt. i. clarify.
  hexploit MAX0; eauto. i. des.
  assert (exists val released, max_readable mem_tgt promises loc (View.pln (TView.cur tview) loc) val released).
  { apply NNPP. ii. hexploit non_max_readable_race.
    { ii. eapply H; eauto. }
    { eauto. }
    { eauto. }
    { i. des. eapply sim_local_racy in H0; eauto. des.
      eapply race_non_max_readable in H0; eauto. }
  }
  des. exists val. esplits.
  { econs; eauto. i. clarify. esplits; eauto. }
  inv H. hexploit sim_memory_get; eauto; ss. i. des.
  hexploit sim_timestamp_le.
  2:{ eapply TO. }
  2:{ refl. }
  { inv LOCAL. eapply TVIEW; ss. }
  { eauto. }
  { eapply mapping_latest_wf_loc. }
  i. inv MAX. inv H.
  { hexploit MAX2; eauto.
    { inv MSG; ss. }
    i. inv LOCAL. hexploit sim_promises_get_if; eauto.
    i. des.
    2:{ rewrite FLAGTGT in *; ss. }
    eapply sim_timestamp_exact_unique in TO; eauto.
    2:{ eapply mapping_latest_wf_loc. }
    subst. clarify.
  }
  { inv H0. clarify. esplits; eauto. inv MSG; auto. }
Qed.

Lemma sim_thread_tgt_read_na
      f vers flag_src flag_tgt vs_src vs_tgt
      mem_src mem_tgt lc_src lc_tgt0 sc_src sc_tgt
      loc to_tgt val_tgt vw_tgt lc_tgt1
      (READ: Local.read_step lc_tgt0 mem_tgt loc to_tgt val_tgt vw_tgt Ordering.na lc_tgt1)
      (SIM: sim_thread
              f vers flag_src flag_tgt vs_src vs_tgt
              mem_src mem_tgt lc_src lc_tgt0 sc_src sc_tgt)
      (CONSISTENT: Local.promise_consistent lc_tgt1)
      (LOCAL: Local.wf lc_tgt0 mem_tgt)
      (MEM: Memory.closed mem_tgt)
  :
    (<<SIM: sim_thread
              f vers flag_src flag_tgt vs_src vs_tgt
              mem_src mem_tgt lc_src lc_tgt1 sc_src sc_tgt>>) /\
    (<<VAL: forall val (VALS: vs_tgt loc = Some val), Const.le val_tgt val>>).
Proof.
  hexploit Local.read_step_future; eauto.
  i. des. splits.
  { inv SIM. econs; eauto.
    { eapply sim_local_tgt_mon; eauto.
      { inv READ; ss. }
    }
    { eapply max_values_tgt_mon; eauto.
      { inv READ; ss. }
    }
    { inv READ. ss. }
  }
  { i. inv SIM. specialize (MAXTGT loc). inv MAXTGT.
    hexploit MAX; eauto. i. des.
    hexploit max_readable_read_only; eauto.
    i. des; auto.
  }
Qed.

Lemma sim_thread_tgt_read_na_racy
      f vers flag_src flag_tgt vs_src vs_tgt
      mem_src mem_tgt lc_src lc_tgt0 sc_src sc_tgt
      loc to val_tgt ord
      (READ: Local.racy_read_step lc_tgt0 mem_tgt loc to val_tgt ord)
      (SIM: sim_thread
              f vers flag_src flag_tgt vs_src vs_tgt
              mem_src mem_tgt lc_src lc_tgt0 sc_src sc_tgt)
      (LOCAL: Local.wf lc_tgt0 mem_tgt)
  :
    vs_tgt loc = None.
Proof.
  destruct (vs_tgt loc) eqn:VAL; auto.
  inv SIM. specialize (MAXTGT loc). inv MAXTGT. hexploit MAX; eauto. i. des.
  exfalso. eapply max_readable_not_read_race; eauto.
  Unshelve.
Qed.

Lemma sim_thread_src_read_na
      f vers flag_src flag_tgt vs_src vs_tgt
      mem_src mem_tgt lc_src lc_tgt sc_src sc_tgt
      loc val_src val
      (SIM: sim_thread
              f vers flag_src flag_tgt vs_src vs_tgt
              mem_src mem_tgt lc_src lc_tgt sc_src sc_tgt)
      (VALS: vs_src loc = Some val)
      (VAL: Const.le val_src val)
      (LOCAL: Local.wf lc_src mem_src)
  :
    exists to vw,
      Local.read_step lc_src mem_src loc to val_src vw Ordering.na lc_src.
Proof.
  inv SIM. specialize (MAXSRC loc). inv MAXSRC. hexploit MAX; eauto. i. des.
  hexploit max_readable_read.
  { eauto. }
  { eauto. }
  { eauto. }
  { instantiate (1:=val_src). auto. }
  i. des. esplits; eauto.
Qed.

Lemma sim_thread_src_read_na_racy
      f vers flag_src flag_tgt vs_src vs_tgt
      mem_src mem_tgt lc_src lc_tgt sc_src sc_tgt
      loc val_src
      (SIM: sim_thread
              f vers flag_src flag_tgt vs_src vs_tgt
              mem_src mem_tgt lc_src lc_tgt sc_src sc_tgt)
      (CONSISTENT: Local.promise_consistent lc_tgt)
      (LOCAL: Local.wf lc_src mem_src)
      (VALS: vs_src loc = None)
      (WF: Mapping.wfs f)
  :
    exists to_src, Local.racy_read_step lc_src mem_src loc to_src val_src Ordering.na.
Proof.
  inv SIM. specialize (MAXSRC loc). inv MAXSRC.
  hexploit non_max_readable_read; eauto.
  eapply sim_local_consistent; eauto.
Qed.

Lemma sim_thread_tgt_write_na_racy
      f vers flag_src flag_tgt vs_src vs_tgt
      mem_src mem_tgt lc_src lc_tgt0 sc_src sc_tgt
      loc to
      (WRITE: Local.racy_write_step lc_tgt0 mem_tgt loc to Ordering.na)
      (SIM: sim_thread
              f vers flag_src flag_tgt vs_src vs_tgt
              mem_src mem_tgt lc_src lc_tgt0 sc_src sc_tgt)
      (LOCAL: Local.wf lc_tgt0 mem_tgt)
  :
    vs_tgt loc = None.
Proof.
  destruct (vs_tgt loc) eqn:VAL; auto.
  inv SIM. specialize (MAXTGT loc). inv MAXTGT. hexploit MAX; eauto. i. des.
  exfalso. eapply max_readable_not_write_race; eauto.
Qed.

Lemma sim_thread_src_write_na_racy
      f vers flag_src flag_tgt vs_src vs_tgt
      mem_src mem_tgt lc_src lc_tgt sc_src sc_tgt
      loc
      (SIM: sim_thread
              f vers flag_src flag_tgt vs_src vs_tgt
              mem_src mem_tgt lc_src lc_tgt sc_src sc_tgt)
      (CONSISTENT: Local.promise_consistent lc_tgt)
      (LOCAL: Local.wf lc_src mem_src)
      (VALS: vs_src loc = None)
      (WF: Mapping.wfs f)
  :
    exists to_src, Local.racy_write_step lc_src mem_src loc to_src Ordering.na.
Proof.
  inv SIM. specialize (MAXSRC loc). inv MAXSRC.
  hexploit non_max_readable_write; eauto.
  eapply sim_local_consistent; eauto.
Qed.

Lemma local_write_step_write_na_step
      lc0 sc0 mem0 loc from to val releasedm released lc1 sc1 mem1 kind
      (WRITE: Local.write_step lc0 sc0 mem0 loc from to val releasedm released Ordering.na lc1 sc1 mem1 kind)
  :
    Local.write_na_step lc0 sc0 mem0 loc from to val Ordering.na lc1 sc1 mem1 [] [] kind.
Proof.
  inv WRITE. econs; eauto. econs.
  { eapply WRITABLE. }
  exact WRITE0.
Qed.

Lemma sim_thread_tgt_flag_up
      f vers flag_src flag_tgt vs_src vs_tgt mem_src0 mem_tgt lc_src0 lc_tgt sc_src sc_tgt loc
      (SIM: sim_thread
              f vers flag_src flag_tgt vs_src vs_tgt
              mem_src0 mem_tgt lc_src0 lc_tgt sc_src sc_tgt)
      (CONSISTENT: Local.promise_consistent lc_tgt)
      (LOCAL: Local.wf lc_src0 mem_src0)
      (MEM: Memory.closed mem_src0)
      (SC: Memory.closed_timemap sc_src mem_src0)
      (WF: Mapping.wfs f)
      lang st
  :
    exists mem_src1 lc_src1,
      (<<STEPS: rtc (@Thread.tau_step _)
                    (Thread.mk lang st lc_src0 sc_src mem_src0)
                    (Thread.mk _ st lc_src1 sc_src mem_src1)>>) /\
      (<<NONE: forall to from val released (GET: Memory.get loc to lc_src1.(Local.promises) = Some (from, Message.concrete val released)),
          released = None>>) /\
      (<<SIM: sim_thread
                f vers flag_src (fun loc0 => if Loc.eq_dec loc0 loc
                                             then true
                                             else flag_tgt loc0)
                vs_src vs_tgt
                mem_src1 mem_tgt lc_src1 lc_tgt sc_src sc_tgt>>) /\
      (<<SPACE: space_future_memory (unchangable mem_tgt lc_tgt.(Local.promises)) f mem_src0 f mem_src1>>)
.
Proof.
  inv SIM. dup LOCAL0. inv LOCAL0.
  hexploit tgt_flag_up_sim_promises.
  { eauto. }
  { eauto. }
  { eapply sim_local_consistent in CONSISTENT; eauto.
    i. rewrite SRCTM. eapply CONSISTENT; eauto.
  }
  { eapply LOCAL. }
  { eapply MEM. }
  { auto. }
  i. des. esplits; [eapply STEPS|..].
  { i. ss. eapply NONE; eauto. }
  { econs; auto.
    { eauto. }
    { econs; eauto. }
    { ii. hexploit (MAXSRC loc0). i. inv H. econs.
      { i. hexploit MAX; eauto. i. des. esplits. eapply VALS; eauto. }
      { i. hexploit NONMAX; eauto. ii. eapply H. eapply VALS; eauto. }
    }
    { eapply sim_closed_memory_future; eauto.
      eapply Thread.rtc_tau_step_future in STEPS; eauto.
      ss. des. eapply Memory.future_future_weak; eauto.
    }
    { i. rewrite MAXTS. auto. }
    { eapply reserved_space_empty_covered_decr; eauto.
      i. eapply COVERED; eauto.
    }
  }
  { eapply space_future_covered_decr. i. eapply COVERED; eauto. }
Qed.

Lemma lower_write_memory_le prom0 mem0 loc from to msg prom1 mem1 kind
      (WRITE: Memory.write prom0 mem0 loc from to msg prom1 mem1 kind)
      (KIND: Memory.op_kind_is_lower kind)
  :
    Memory.le prom1 prom0.
Proof.
  destruct kind; ss. inv WRITE. inv PROMISE. ii.
  erewrite Memory.remove_o in LHS; eauto.
  erewrite Memory.lower_o in LHS; eauto. des_ifs.
Qed.

Lemma na_write_max_readable
      mem0 prom0 loc ts val_old released
      prom1 mem1 msgs kinds kind from to val_new
      (MAX: max_readable mem0 prom0 loc ts val_old released)
      (WRITE: Memory.write_na ts prom0 mem0 loc from to val_new prom1 mem1 msgs kinds kind)
      (LOWER: mem1 = mem0)
  :
    max_readable mem1 prom1 loc to val_new None.
Proof.
  hexploit write_na_lower_memory_lower; eauto. i. des.
  destruct MAX.
  remember (Message.concrete val_old released) as msg_old. clear Heqmsg_old.
  revert from0 msg_old GET NONE MAX KINDS KIND. induction WRITE.
  { i. destruct kind; ss. inv WRITE. inv PROMISE.
    hexploit lower_same_same; [apply PROMISES|]. i. subst.
    hexploit lower_same_same; [apply MEM|]. i. subst.
    econs.
    { eapply Memory.lower_get0; eauto. }
    { erewrite Memory.remove_o; eauto. des_ifs. ss. des; clarify. }
    { i. erewrite Memory.remove_o; eauto. des_ifs.
      { ss. des; clarify. exfalso. eapply Time.lt_strorder; eauto. }
      { eapply MAX; eauto. }
    }
  }
  { i. inv KINDS. destruct kind'; ss. clarify.
    inv WRITE_EX. inv PROMISE.
    hexploit lower_same_same; [apply PROMISES|]. i. subst.
    hexploit lower_same_same; [apply MEM|]. i. subst.
    eapply IHWRITE; auto.
    { eapply Memory.lower_get0; eauto. }
    { erewrite Memory.remove_o; eauto. des_ifs. ss. des; clarify. }
    { i. erewrite Memory.remove_o; eauto. des_ifs.
      { ss. des; clarify. exfalso. eapply Time.lt_strorder; eauto. }
      { eapply MAX; eauto. }
    }
  }
Qed.

Lemma na_write_step_max_readable
      mem0 lc0 loc ts val_old released ord
      lc1 mem1 msgs kinds kind sc0 sc1 from to val_new
      (MAX: max_readable mem0 lc0.(Local.promises) loc ts val_old released)
      (TS: lc0.(Local.tview).(TView.cur).(View.pln) loc = ts)
      (WRITE: Local.write_na_step lc0 sc0 mem0 loc from to val_new ord lc1 sc1 mem1
                                  msgs kinds kind)
      (LOWER: mem1 = mem0)
      (WF: Local.wf lc0 mem0)
  :
    max_readable mem1 lc1.(Local.promises) loc (lc1.(Local.tview).(TView.cur).(View.pln) loc) val_new None.
Proof.
  inv WRITE. ss.
  exploit na_write_max_readable.
  { eauto. }
  { eapply ts_le_memory_write_na.
    { eauto. }
    { eapply WF. }
  }
  { auto. }
  i.
  match goal with
  | |- _ ?vw _ _ => replace vw with to
  end; auto.
  unfold TimeMap.join.
  replace ((TimeMap.singleton loc to) loc) with to.
  2:{ unfold TimeMap.singleton. setoid_rewrite LocFun.add_spec. des_ifs. }
  symmetry. eapply TimeFacts.le_join_r.
  etrans.
  2:{ left. eapply write_na_ts_lt; eauto. }
  eapply WF.
Qed.

Lemma write_promise_reserve_same
      prom0 mem0 loc from to msg prom1 mem1 kind
      loc0 to0 from0
      (WRITE: Memory.write prom0 mem0 loc from to msg prom1 mem1 kind)
      (RESERVE: Memory.get loc0 to0 prom0 = Some (from0, Message.reserve))
      (MSG: msg <> Message.reserve)
  :
  Memory.get loc0 to0 prom1 = Some (from0, Message.reserve).
Proof.
  inv WRITE. erewrite Memory.remove_o; eauto. inv PROMISE.
  { erewrite Memory.add_o; eauto. des_ifs. ss. des; clarify.
    eapply Memory.add_get0 in PROMISES. des; clarify. }
  { erewrite Memory.split_o; eauto. des_ifs.
    { ss. des; clarify. eapply Memory.split_get0 in PROMISES. des; clarify. }
    { ss. des; clarify. eapply Memory.split_get0 in PROMISES. des; clarify. }
  }
  { erewrite Memory.lower_o; eauto. des_ifs. ss. des; clarify.
    eapply Memory.lower_get0 in PROMISES. des; clarify. inv MSG_LE; ss. }
  { ss. }
Qed.

Lemma write_na_promise_reserve_same
      ts prom0 mem0 loc from to val prom1 mem1 msgs kinds kind
      loc0 to0 from0
      (WRITE: Memory.write_na ts prom0 mem0 loc from to val prom1 mem1 msgs kinds kind)
      (RESERVE: Memory.get loc0 to0 prom0 = Some (from0, Message.reserve))
  :
  Memory.get loc0 to0 prom1 = Some (from0, Message.reserve).
Proof.
  revert loc0 to0 from0 RESERVE. induction WRITE.
  { i. eapply write_promise_reserve_same; eauto. ss. }
  { i. eapply IHWRITE. eapply write_promise_reserve_same; eauto.
    unguard. des; clarify.
  }
Qed.

Lemma sim_thread_tgt_write_na_aux
      f vers flag_src flag_tgt vs_src vs_tgt
      mem_src mem_tgt0 lc_src lc_tgt0 sc_src sc_tgt0
      loc from to val_old val_new lc_tgt1 sc_tgt1 mem_tgt1 ord msgs kinds kind
      (WRITE: Local.write_na_step lc_tgt0 sc_tgt0 mem_tgt0 loc from to val_new ord lc_tgt1 sc_tgt1 mem_tgt1 msgs kinds kind)
      (LOWER: mem_tgt1 = mem_tgt0)
      (SIM: sim_thread
              f vers flag_src flag_tgt vs_src vs_tgt
              mem_src mem_tgt0 lc_src lc_tgt0 sc_src sc_tgt0)
      (VAL: vs_tgt loc = Some val_old)
      (FLAG: flag_tgt loc = true)
      (CONSISTENT: Local.promise_consistent lc_tgt1)
      (LOCAL: Local.wf lc_tgt0 mem_tgt0)
      (MEM: Memory.closed mem_tgt0)
      (WF: Mapping.wfs f)
  :
    (<<SIM: sim_thread
              f vers flag_src flag_tgt vs_src (fun loc0 => if Loc.eq_dec loc0 loc then Some val_new else vs_tgt loc0)
              mem_src mem_tgt1 lc_src lc_tgt1 sc_src sc_tgt1>>) /\
    (<<ORD: ord = Ordering.na>>) /\
    (<<SC: sc_tgt1 = sc_tgt0>>)
.
Proof.
  subst. hexploit write_na_step_lower_memory_lower; eauto. i. des.
  assert ((<<MLE: Memory.le lc_tgt1.(Local.promises) lc_tgt0.(Local.promises)>>) /\
          (<<OTHERS: forall loc0 (NEQ: loc0 <> loc) to,
              Memory.get loc0 to lc_tgt1.(Local.promises)
              =
              Memory.get loc0 to lc_tgt0.(Local.promises)>>)).
  { inv WRITE. ss.
    revert KINDS KIND. clear CONSISTENT. induction WRITE0; i.
    { splits.
      { eapply lower_write_memory_le; eauto. destruct kind; ss. }
      { i. inv WRITE. destruct kind; ss. inv PROMISE.
        erewrite (@Memory.remove_o promises2); eauto.
        erewrite (@Memory.lower_o promises0); eauto.
        des_ifs. des; clarify.
      }
    }
    { inv KINDS. splits.
      { transitivity promises'.
        { eapply IHWRITE0; eauto. }
        { eapply lower_write_memory_le; eauto. destruct kind'; ss. }
      }
      { i. inv WRITE_EX. destruct kind'; ss. inv PROMISE.
        transitivity (Memory.get loc0 to0 promises').
        { eapply IHWRITE0; eauto. }
        { erewrite (@Memory.remove_o promises'); eauto.
          erewrite (@Memory.lower_o promises0); eauto.
          des_ifs. des; clarify.
        }
      }
    }
  }
  hexploit sim_local_consistent_ex.
  { eapply PromiseConsistent.write_na_step_promise_consistent; eauto. }
  { inv SIM. eauto. }
  { auto. }
  intros CONSSRC. des. splits.
  2:{ inv WRITE. destruct ord; ss. }
  2:{ inv WRITE. auto. }
  inv SIM. econs; auto.
  { inv WRITE. auto. }
  { eauto. }
  { inv WRITE. inv LOCAL0. econs; ss; auto.
    { eapply sim_tview_tgt_mon; eauto.
      eapply TViewFacts.write_tview_incr. eapply LOCAL.
    }
    { econs.
      { i. eapply MLE in GET. hexploit sim_promises_get; eauto.
        i. des. esplits; eauto.
      }
      { i. destruct (Loc.eq_dec loc0 loc).
        { subst. destruct (classic (msg_src = Message.reserve)).
          { subst. hexploit sim_promises_get_if; eauto. i. des; ss.
            left. inv MSG. esplits; eauto.
            eapply write_na_promise_reserve_same; eauto.
          }
          { right. esplits; eauto.
            { rewrite SRCTM. eapply CONSSRC; eauto. }
            { i. subst. eapply sim_promises_nonsynch_loc in GET; eauto; ss.
              rewrite FLAG. ss.
            }
          }
        }
        { hexploit sim_promises_get_if; eauto. i. des.
          { left. esplits; eauto. rewrite OTHERS; eauto. }
          { right. esplits; eauto. }
        }
      }
      { i. eapply sim_promises_none; eauto. }
    }
    { inv RELVERS. econs. i. eapply MLE in GET. eauto. }
  }
  { ii. des_ifs.
    { specialize (MAXTGT loc). inv MAXTGT.
      hexploit MAX; eauto. i. des.
      hexploit na_write_step_max_readable.
      { instantiate (5:=Local.mk _ _). eapply MAX0. }
      all: ss; eauto.
      i. destruct lc_tgt1. ss. econs. i. clarify.
      esplits; eauto.
    }
    { inv WRITE. ss. specialize (MAXTGT loc0). inv MAXTGT. econs; eauto.
      i. ss. hexploit MAX; eauto. i. des. esplits; eauto.
      match goal with
      | |- _ ?vw _ _ => replace vw with (tvw.(TView.cur).(View.pln) loc0)
      end.
      { inv MAX0. econs; eauto.
        { rewrite OTHERS; eauto. }
        { i. rewrite OTHERS; eauto. }
      }
      { symmetry. eapply TimeFacts.le_join_l. unfold TimeMap.singleton.
        setoid_rewrite LocFun.add_spec_neq; auto. eapply Time.bot_spec.
      }
    }
  }
  { i. des_ifs. specialize (PERM loc).
    rewrite VAL in PERM. unfold option_rel in *. des_ifs.
  }
  { eapply reserved_space_empty_reserve_decr; eauto. }
Qed.

Lemma sim_thread_tgt_write_na
      f vers flag_src flag_tgt vs_src vs_tgt
      mem_src0 mem_tgt0 lc_src0 lc_tgt0 sc_src sc_tgt0
      loc from to val_old val_new lc_tgt1 sc_tgt1 mem_tgt1 ord msgs kinds kind
      (WRITE: Local.write_na_step lc_tgt0 sc_tgt0 mem_tgt0 loc from to val_new ord lc_tgt1 sc_tgt1 mem_tgt1 msgs kinds kind)
      (LOWER: mem_tgt1 = mem_tgt0)
      (SIM: sim_thread
              f vers flag_src flag_tgt vs_src vs_tgt
              mem_src0 mem_tgt0 lc_src0 lc_tgt0 sc_src sc_tgt0)
      (VAL: vs_tgt loc = Some val_old)
      (CONSISTENT: Local.promise_consistent lc_tgt1)
      (LOCALSRC: Local.wf lc_src0 mem_src0)
      (LOCALTGT: Local.wf lc_tgt0 mem_tgt0)
      (MEMSRC: Memory.closed mem_src0)
      (MEMTGT: Memory.closed mem_tgt0)
      (SCSRC: Memory.closed_timemap sc_src mem_src0)
      (WF: Mapping.wfs f)
      lang st
  :
    exists mem_src1 lc_src1,
      (<<STEPS: rtc (@Thread.tau_step _)
                    (Thread.mk lang st lc_src0 sc_src mem_src0)
                    (Thread.mk _ st lc_src1 sc_src mem_src1)>>) /\
      (<<SIM: sim_thread
                f vers flag_src
                (fun loc0 => if Loc.eq_dec loc0 loc then true else flag_tgt loc0)
                vs_src
                (fun loc0 => if Loc.eq_dec loc0 loc then Some val_new else vs_tgt loc0)
                mem_src1 mem_tgt1 lc_src1 lc_tgt1 sc_src sc_tgt1>>) /\
      (<<ORD: ord = Ordering.na>>) /\
      (<<SC: sc_tgt1 = sc_tgt0>>) /\
      (<<SPACE: space_future_memory (unchangable mem_tgt0 lc_tgt0.(Local.promises)) f mem_src0 f mem_src1>>)
.
Proof.
  hexploit sim_thread_tgt_flag_up; eauto.
  { eapply PromiseConsistent.write_na_step_promise_consistent; eauto. }
  i. des.
  hexploit sim_thread_tgt_write_na_aux; eauto.
  { ss. des_ifs. }
  i. des. esplits; eauto.
Qed.

Lemma reserve_future_steps prom0 mem0 prom1 mem1
      (FUTURE: reserve_future_memory prom0 mem0 prom1 mem1)
      tvw sc lang st
  :
    rtc (@Thread.tau_step _)
        (Thread.mk lang st (Local.mk tvw prom0) sc mem0)
        (Thread.mk _ st (Local.mk tvw prom1) sc mem1).
Proof.
  induction FUTURE.
  { refl. }
  econs; [|eauto]. econs.
  { econs. econs 1. econs; eauto. }
  { ss. }
Qed.

Lemma cap_max_readable mem cap prom loc ts val released
      (CAP: Memory.cap mem cap)
      (MLE: Memory.le prom mem)
      (MEM: Memory.closed mem)
  :
    max_readable mem prom loc ts val released
    <->
    max_readable cap prom loc ts val released.
Proof.
  split.
  { i. inv H. econs; eauto.
    { eapply Memory.cap_le; [..|eauto]; eauto. refl. }
    { i. eapply Memory.cap_inv in GET0; eauto. des; clarify.
      eapply MAX in GET0; eauto.
    }
  }
  { i. inv H. eapply Memory.cap_inv in GET; eauto. des; clarify.
    econs; eauto. i. eapply MAX; eauto.
    eapply Memory.cap_le; [..|eauto]; eauto. refl.
  }
Qed.

Lemma cap_max_values_src vs mem cap lc
      (MAX: max_values_src vs mem lc)
      (CAP: Memory.cap mem cap)
      (LOCAL: Local.wf lc mem)
      (MEM: Memory.closed mem)
  :
    max_values_src vs cap lc.
Proof.
  ii. specialize (MAX loc). inv MAX. econs.
  { i. hexploit MAX0; eauto. i. des. esplits; eauto.
    erewrite <- cap_max_readable; eauto. eapply LOCAL.
  }
  { i. hexploit NONMAX; eauto. ii. eapply H.
    erewrite cap_max_readable; eauto. eapply LOCAL.
  }
Qed.

Lemma cap_max_values_tgt vs mem cap lc
      (MAX: max_values_tgt vs mem lc)
      (CAP: Memory.cap mem cap)
      (LOCAL: Local.wf lc mem)
      (MEM: Memory.closed mem)
  :
    max_values_tgt vs cap lc.
Proof.
  ii. specialize (MAX loc). inv MAX. econs.
  i. hexploit MAX0; eauto. i. des. esplits; eauto.
  erewrite <- cap_max_readable; eauto. eapply LOCAL.
Qed.

Lemma sim_promises_preserve
      srctm prom_src prom_tgt flag_src flag_tgt f0 f1 vers mem
      (SIM: sim_promises srctm flag_src flag_tgt f0 vers prom_src prom_tgt)
      (MAPLE: Mapping.les f0 f1)
      (PRESERVE: forall loc to from msg
                        (GET: Memory.get loc to mem = Some (from, msg))
                        ts fts
                        (TS: Time.le ts to)
                        (MAP: sim_timestamp_exact (f0 loc) (f0 loc).(Mapping.ver) fts ts),
          sim_timestamp_exact (f1 loc) (f1 loc).(Mapping.ver) fts ts)
      (MLE: Memory.le prom_tgt mem)
      (WF: Mapping.wfs f0)
      (VERS: versions_wf f0 vers)
  :
    sim_promises srctm flag_src flag_tgt f1 vers prom_src prom_tgt.
Proof.
  econs.
  { i. hexploit sim_promises_get; eauto. i. des. esplits.
    { eapply PRESERVE; eauto. eapply memory_get_ts_le; eauto. }
    { eapply PRESERVE; eauto. refl. }
    { auto. }
    { i. hexploit GET0; eauto. i. des. esplits; eauto.
      erewrite <- sim_message_max_mon_mapping; eauto.
    }
  }
  { i. hexploit sim_promises_get_if; eauto. i. des.
    { left. esplits.
      { eapply PRESERVE; eauto. refl. }
      { eauto. }
    }
    { right. esplits; eauto. }
  }
  { i. eapply sim_promises_none; eauto. }
Qed.

Lemma sim_thread_cap
      f0 vers flag_tgt vs_src vs_tgt
      mem_src mem_tgt lc_src lc_tgt sc_src sc_tgt
      cap_src cap_tgt
      (SIM: sim_thread
              f0 vers (fun _ => false) flag_tgt vs_src vs_tgt
              mem_src mem_tgt lc_src lc_tgt sc_src sc_tgt)
      (CAPSRC: Memory.cap mem_src cap_src)
      (CAPTGT: Memory.cap mem_tgt cap_tgt)
      (WF: Mapping.wfs f0)
      (VERS: versions_wf f0 vers)
      (MEMSRC: Memory.closed mem_src)
      (MEMTGT: Memory.closed mem_tgt)
      (LOCALSRC: Local.wf lc_src mem_src)
      (LOCALTGT: Local.wf lc_tgt mem_tgt)
  :
    exists f1,
      (<<MAPLE: Mapping.les f0 f1>>) /\
      (<<MAPWF: Mapping.wfs f1>>) /\
      (<<SIM: sim_thread
                f1 vers (fun _ => false) flag_tgt vs_src vs_tgt
                cap_src cap_tgt lc_src lc_tgt sc_src sc_tgt>>) /\
      (<<VERS: versions_wf f1 vers>>)
.
Proof.
  inv SIM. hexploit cap_sim_memory; eauto. i. des. esplits; eauto.
  2:{ eapply versions_wf_mapping_mon; eauto. }
  econs; eauto.
  { eapply sim_timemap_mon_latest; eauto. }
  { inv LOCAL. econs; eauto.
    { eapply sim_tview_mon_latest; eauto. }
    { eapply sim_promises_preserve; eauto. eapply LOCALTGT. }
  }
  { eapply cap_max_values_src; eauto. }
  { eapply cap_max_values_tgt; eauto. }
  { eapply versioned_memory_cap; eauto. }
  { i. ss. }
  { ss. }
  { ii. exploit FINALIZED; eauto. i. des. esplits; eauto.
    { eapply PRESERVE; eauto. refl. }
    { eapply Memory.cap_le; eauto. refl. }
  }
Qed.

Lemma sim_readable L f vw_src vw_tgt loc to_src to_tgt released_src released_tgt ord
      (READABLE: TView.readable vw_tgt loc to_tgt released_tgt ord)
      (SIM: sim_view L f (Mapping.vers f) vw_src vw_tgt)
      (TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src to_tgt)
      (WF: Mapping.wfs f)
      (LOC: L loc)
  :
    TView.readable vw_src loc to_src released_src ord.
Proof.
  inv READABLE. econs.
  { eapply sim_timestamp_le.
    { eapply SIM. auto. }
    { eauto. }
    { eauto. }
    { eauto. }
    { eapply mapping_latest_wf_loc. }
  }
  { i. eapply sim_timestamp_le.
    { eapply SIM. auto. }
    { eauto. }
    { eauto. }
    { eauto. }
    { eapply mapping_latest_wf_loc. }
  }
Qed.

Lemma sim_writable L f vw_src vw_tgt loc to_src to_tgt sc_src sc_tgt ord
      (WRITABLE: TView.writable vw_tgt sc_tgt loc to_tgt ord)
      (SIM: sim_view L f (Mapping.vers f) vw_src vw_tgt)
      (TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src to_tgt)
      (WF: Mapping.wfs f)
      (LOC: L loc)
  :
    TView.writable vw_src sc_src loc to_src ord.
Proof.
  inv WRITABLE. econs.
  eapply sim_timestamp_lt.
  { eapply SIM. auto. }
  { eauto. }
  { eauto. }
  { eauto. }
  { eapply mapping_latest_wf_loc. }
Qed.

Lemma semi_sim_timemap_join loc f v to_src to_tgt tm_src tm_tgt
      (SIM: sim_timemap (fun loc0 => loc0 <> loc) f v tm_src tm_tgt)
      (TS: sim_timestamp (f loc) (v loc) to_src to_tgt)
      (LESRC: time_le_timemap loc to_src tm_src)
      (LETGT: time_le_timemap loc to_tgt tm_tgt)
      (WF: Mapping.wfs f)
      (VER: version_wf f v)
  :
    sim_timemap (fun _ => True) f v (TimeMap.join (TimeMap.singleton loc to_src) tm_src) (TimeMap.join (TimeMap.singleton loc to_tgt) tm_tgt).
Proof.
  ii. destruct (Loc.eq_dec l loc).
  { subst. unfold TimeMap.join.
    repeat rewrite TimeFacts.le_join_l.
    { eapply sim_timemap_singleton; ss. }
    { unfold TimeMap.singleton. setoid_rewrite LocFun.add_spec_eq.
      eapply LETGT. }
    { unfold TimeMap.singleton. setoid_rewrite LocFun.add_spec_eq.
      eapply LESRC. }
  }
  { eapply sim_timestamp_join; eauto.
    unfold TimeMap.singleton. setoid_rewrite LocFun.add_spec_neq; eauto.
    eapply sim_timestamp_bot; eauto.
  }
Qed.

Lemma semi_sim_view_join loc f v to_src to_tgt vw_src vw_tgt
      (SIM: sim_view (fun loc0 => loc0 <> loc) f v vw_src vw_tgt)
      (TS: sim_timestamp (f loc) (v loc) to_src to_tgt)
      (LESRC: time_le_view loc to_src vw_src)
      (LETGT: time_le_view loc to_tgt vw_tgt)
      (WF: Mapping.wfs f)
      (VER: version_wf f v)
  :
    sim_view (fun _ => True) f v (View.join (View.singleton_ur loc to_src) vw_src) (View.join (View.singleton_ur loc to_tgt) vw_tgt).
Proof.
  econs.
  { eapply semi_sim_timemap_join; eauto.
    { eapply SIM. }
    { eapply LESRC. }
    { eapply LETGT. }
  }
  { eapply semi_sim_timemap_join; eauto.
    { eapply SIM. }
    { eapply LESRC. }
    { eapply LETGT. }
  }
Qed.

Lemma semi_sim_opt_view_join loc f v to_src to_tgt released_src released_tgt
      (SIM: sim_opt_view (fun loc0 => loc0 <> loc) f (Some v) released_src released_tgt)
      (TS: sim_timestamp (f loc) (v loc) to_src to_tgt)
      (LESRC: time_le_opt_view loc to_src released_src)
      (LETGT: time_le_opt_view loc to_tgt released_tgt)
      (WF: Mapping.wfs f)
      (VER: version_wf f v)
  :
    sim_view (fun _ => True) f v (View.join (View.singleton_ur loc to_src) (View.unwrap released_src)) (View.join (View.singleton_ur loc to_tgt) (View.unwrap released_tgt)).
Proof.
  inv SIM; ss.
  { inv LESRC. inv LETGT. eapply semi_sim_view_join; eauto. }
  { eapply sim_view_join; eauto.
    { eapply sim_view_singleton_ur; eauto. }
    { eapply sim_view_bot; eauto. }
  }
Qed.

Lemma sim_opt_view_mon_opt_ver L f v0 v1 vw_src vw_tgt
      (SIM: sim_opt_view L f v0 vw_src vw_tgt)
      (VER: forall v0' (VER: v0 = Some v0'),
          exists v1', (<<VER: v1 = Some v1'>>) /\(<<VERLE: version_le v0' v1'>>))
      (WF: Mapping.wfs f)
      (VERWF: opt_version_wf f v1)
  :
    sim_opt_view L f v1 vw_src vw_tgt.
Proof.
  destruct v0.
  { hexploit VER; eauto. i. des. clarify.
    eapply sim_opt_view_mon_ver; eauto.
  }
  { inv SIM. econs. }
Qed.

Lemma sim_read_tview f flag_src rel_vers tvw_src tvw_tgt v
      loc to_src released_src ord to_tgt released_tgt
      (SIM: sim_tview f flag_src rel_vers tvw_src tvw_tgt)
      (TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src to_tgt)
      (CLOSED: Mapping.closed (f loc) (Mapping.vers f loc) to_src)
      (RELEASED: sim_opt_view (fun loc0 => loc0 <> loc) f v released_src released_tgt)
      (WF: Mapping.wfs f)
      (VERWF: opt_version_wf f v)
      (LESRC: time_le_opt_view loc to_src released_src)
      (LETGT: time_le_opt_view loc to_tgt released_tgt)
  :
    sim_tview f flag_src rel_vers (TView.read_tview tvw_src loc to_src released_src ord) (TView.read_tview tvw_tgt loc to_tgt released_tgt ord).
Proof.
  pose proof (mapping_latest_wf f).
  assert (TM: sim_timestamp (f loc) (Mapping.vers f loc) to_src to_tgt).
  { eapply sim_timestamp_exact_sim; eauto. }
  assert (JOIN: sim_view (fun loc0 => flag_src loc0 = false) f (Mapping.vers f)
                         (View.join (View.singleton_ur loc to_src) (View.unwrap released_src))
                         (View.join (View.singleton_ur loc to_tgt) (View.unwrap released_tgt))).
  { eapply sim_view_mon_locs.
    { eapply semi_sim_opt_view_join; eauto.
      eapply sim_opt_view_mon_opt_ver; eauto.
      i. clarify. splits; eauto.
    }
    { ss. }
  }
  econs.
  { eapply SIM. }
  { ss. rewrite View.join_assoc. rewrite View.join_assoc.
    eapply sim_view_join; eauto.
    { eapply SIM. }
    unfold View.singleton_ur_if. des_ifs.
    { eapply sim_view_join; eauto.
      { eapply sim_view_singleton_ur; eauto. }
      { eapply sim_view_bot; eauto. }
    }
    { destruct ord; ss. }
    { eapply sim_view_join; eauto.
      { eapply sim_view_singleton_rw; eauto. }
      { eapply sim_view_bot; eauto. }
    }
  }
  { ss. rewrite View.join_assoc. rewrite View.join_assoc.
    eapply sim_view_join; eauto.
    { eapply SIM. }
    unfold View.singleton_ur_if. des_ifs.
    { eapply sim_view_join; eauto.
      { eapply sim_view_singleton_rw; eauto. }
      { eapply sim_view_bot; eauto. }
    }
  }
  { i. eapply SIM. }
Qed.

Lemma sim_write_tview_normal f flag_src rel_vers tvw_src tvw_tgt sc_src sc_tgt
      loc to_src ord to_tgt
      (SIM: sim_tview f flag_src rel_vers tvw_src tvw_tgt)
      (TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src to_tgt)
      (ORD: ~ Ordering.le Ordering.acqrel ord)
      (CLOSED: Mapping.closed (f loc) (Mapping.vers f loc) to_src)
      (WF: Mapping.wfs f)
  :
    sim_tview f flag_src rel_vers (TView.write_tview tvw_src sc_src loc to_src ord) (TView.write_tview tvw_tgt sc_tgt loc to_tgt ord).
Proof.
  pose proof (mapping_latest_wf f).
  assert (TM: sim_timestamp (f loc) (Mapping.vers f loc) to_src to_tgt).
  { eapply sim_timestamp_exact_sim; eauto. }
  assert (JOIN: sim_view (fun loc0 => flag_src loc0 = false) f (Mapping.vers f)
                         (View.singleton_ur loc to_src)
                         (View.singleton_ur loc to_tgt)).
  { apply sim_view_singleton_ur; eauto. }
  econs; ss.
  { ii. setoid_rewrite LocFun.add_spec. des_ifs.
    { eapply sim_view_join; eauto.
      { eapply SIM. }
      { apply sim_view_singleton_ur; eauto; ss. eapply SIM. }
      { eapply SIM. }
    }
    { eapply SIM. }
  }
  { eapply sim_view_join; eauto. eapply SIM. }
  { eapply sim_view_join; eauto. eapply SIM. }
  { eapply SIM. }
Qed.

Lemma sim_write_tview_release f flag_src rel_vers tvw_src tvw_tgt sc_src sc_tgt
      loc to_src ord to_tgt
      (SIM: sim_tview f flag_src rel_vers tvw_src tvw_tgt)
      (TO: sim_timestamp (f loc) (f loc).(Mapping.ver) to_src to_tgt)
      (FLAG: forall loc, flag_src loc = false)
      (WF: Mapping.wfs f)
  :
    sim_tview f flag_src (fun loc0 => if Loc.eq_dec loc0 loc then (Mapping.vers f) else rel_vers loc0) (TView.write_tview tvw_src sc_src loc to_src ord) (TView.write_tview tvw_tgt sc_tgt loc to_tgt ord).
Proof.
  pose proof (mapping_latest_wf f).
  assert (JOIN: forall L, sim_view L f (Mapping.vers f)
                                   (View.singleton_ur loc to_src)
                                   (View.singleton_ur loc to_tgt)).
  { i. apply sim_view_singleton_ur; eauto. }
  econs; ss.
  { ii. setoid_rewrite LocFun.add_spec. des_ifs.
    { eapply sim_view_join; eauto.
      { eapply sim_view_mon_locs.
        { eapply SIM. }
        { i. ss. }
      }
    }
    { eapply sim_view_join; eauto.
      { eapply sim_view_mon_ver; auto.
        { eapply SIM. }
        { eapply version_le_version_wf. eapply SIM. }
      }
    }
    { eapply SIM. }
  }
  { eapply sim_view_join; eauto. eapply SIM. }
  { eapply sim_view_join; eauto. eapply SIM. }
  { i. des_ifs. eapply SIM. }
Qed.

Lemma sim_read_fence_tview f flag_src rel_vers tvw_src tvw_tgt
      ord
      (SIM: sim_tview f flag_src rel_vers tvw_src tvw_tgt)
      (WF: Mapping.wfs f)
  :
    sim_tview f flag_src rel_vers (TView.read_fence_tview tvw_src ord) (TView.read_fence_tview tvw_tgt ord).
Proof.
  pose proof (mapping_latest_wf f).
  econs; ss.
  { eapply SIM. }
  { des_ifs.
    { eapply SIM. }
    { eapply SIM. }
  }
  { eapply SIM. }
  { eapply SIM. }
Qed.

Lemma sim_write_fence_tview_normal f flag_src rel_vers tvw_src tvw_tgt sc_src sc_tgt
      ord
      (SIM: sim_tview f flag_src rel_vers tvw_src tvw_tgt)
      (ORD: ~ Ordering.le Ordering.acqrel ord)
      (WF: Mapping.wfs f)
  :
    sim_tview f flag_src rel_vers (TView.write_fence_tview tvw_src sc_src ord) (TView.write_fence_tview tvw_tgt sc_tgt ord).
Proof.
  pose proof (mapping_latest_wf f).
  econs; ss.
  { des_ifs. eapply SIM. }
  { des_ifs.
    { destruct ord; ss. }
    { eapply SIM. }
  }
  { des_ifs.
    { destruct ord; ss. }
    { rewrite ! View.join_bot_r. eapply SIM. }
  }
  { eapply SIM. }
Qed.

Lemma sim_write_fence_tview_release f flag_src rel_vers tvw_src tvw_tgt sc_src sc_tgt
      ord
      (SIM: sim_tview f flag_src rel_vers tvw_src tvw_tgt)
      (SC: sim_timemap (fun _ => True) f (Mapping.vers f) sc_src sc_tgt)
      (FLAG: forall loc, flag_src loc = false)
      (WF: Mapping.wfs f)
  :
    sim_tview f flag_src (fun _ => Mapping.vers f) (TView.write_fence_tview tvw_src sc_src ord) (TView.write_fence_tview tvw_tgt sc_tgt ord).
Proof.
  pose proof (mapping_latest_wf f).
  assert (JOIN: forall L, sim_timemap L f (Mapping.vers f)
                                      (TView.write_fence_sc tvw_src sc_src ord)
                                      (TView.write_fence_sc tvw_tgt sc_tgt ord)).
  { i. unfold TView.write_fence_sc. des_ifs.
    { eapply sim_timemap_join; eauto.
      { eapply sim_timemap_mon_locs; eauto. ss. }
      { eapply sim_timemap_mon_locs.
        { eapply SIM. }
        { ss. }
      }
    }
    { eapply sim_timemap_mon_locs; eauto. ss. }
  }
  econs; ss.
  { des_ifs.
    { i. eapply sim_view_mon_locs.
      { eapply SIM. }
      { ss. }
    }
    { i. eapply sim_view_mon_locs.
      { eapply sim_view_mon_ver; auto.
        { eapply SIM. }
        { eapply version_le_version_wf. eapply SIM. }
      }
      { ss. }
    }
  }
  { des_ifs. eapply SIM. }
  { eapply sim_view_join; auto.
    { eapply SIM. }
    { des_ifs. eapply sim_view_bot; auto. }
  }
Qed.

Lemma sim_write_fence_sc f flag_src rel_vers tvw_src tvw_tgt sc_src sc_tgt
      ord
      (SIM: sim_tview f flag_src rel_vers tvw_src tvw_tgt)
      (SC: sim_timemap (fun loc => flag_src loc = false) f (Mapping.vers f) sc_src sc_tgt)
      (WF: Mapping.wfs f)
  :
    sim_timemap (fun loc => flag_src loc = false) f (Mapping.vers f) (TView.write_fence_sc tvw_src sc_src ord) (TView.write_fence_sc tvw_tgt sc_tgt ord).
Proof.
  pose proof (mapping_latest_wf f).
  unfold TView.write_fence_sc. des_ifs. eapply sim_timemap_join; auto.
  eapply SIM.
Qed.

Lemma sim_write_released_normal f flag_src rel_vers tvw_src tvw_tgt sc_src sc_tgt
      loc to_src ord to_tgt released_src released_tgt v
      (SIM: sim_tview f flag_src rel_vers tvw_src tvw_tgt)
      (RELEASED: sim_opt_view (fun loc0 => loc0 <> loc) f v released_src released_tgt)
      (ORD: ~ Ordering.le Ordering.acqrel ord)
      (VER: Ordering.le Ordering.relaxed ord -> opt_version_le (Some (rel_vers loc)) v)
      (WF: Mapping.wfs f)
      (VERWF: opt_version_wf f v)
  :
    sim_opt_view (fun loc0 => loc0 <> loc) f v
                 (TView.write_released tvw_src sc_src loc to_src released_src ord)
                 (TView.write_released tvw_tgt sc_tgt loc to_tgt released_tgt ord).
Proof.
  pose proof (mapping_latest_wf f).
  unfold TView.write_released. des_ifs.
  { destruct v; ss. econs.
    eapply sim_view_join; auto.
    { eapply sim_opt_view_unwrap; eauto. i. clarify. }
    { ss. setoid_rewrite LocFun.add_spec_eq. des_ifs.
      eapply sim_view_join; auto.
      { eapply sim_view_mon_ver; eauto. eapply SIM. }
      { eapply sim_view_singleton_ur; auto; ss. }
    }
  }
  { econs. }
Qed.

Lemma sim_write_released_release f flag_src rel_vers tvw_src tvw_tgt sc_src sc_tgt
      loc to_src ord to_tgt released_src released_tgt v
      (SIM: sim_tview f flag_src rel_vers tvw_src tvw_tgt)
      (TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src to_tgt)
      (RELEASED: sim_opt_view (fun loc0 => loc0 <> loc) f v released_src released_tgt)
      (VERWF: opt_version_wf f v)
      (FLAG: forall loc, flag_src loc = false)
      (CLOSED: Mapping.closed (f loc) (Mapping.vers f loc) to_src)
      (WF: Mapping.wfs f)
  :
    sim_opt_view (fun loc0 => loc0 <> loc) f (Some (Mapping.vers f))
                 (TView.write_released tvw_src sc_src loc to_src released_src ord)
                 (TView.write_released tvw_tgt sc_tgt loc to_tgt released_tgt ord).
Proof.
  pose proof (mapping_latest_wf f).
  unfold TView.write_released. des_ifs; econs.
  eapply sim_view_join; auto.
  { eapply sim_opt_view_unwrap; eauto. i. clarify. }
  { ss. setoid_rewrite LocFun.add_spec_eq. des_ifs.
    { eapply sim_view_join; auto.
      { eapply sim_view_mon_locs; eauto.
        { eapply SIM. }
        { i. ss. }
      }
      { eapply sim_view_singleton_ur; auto; ss. }
    }
    { eapply sim_view_join; auto.
      { eapply sim_view_mon_ver; auto.
        { eapply SIM. }
        { eapply version_le_version_wf. eapply SIM. }
      }
      { eapply sim_view_singleton_ur; auto; ss. }
    }
  }
Qed.

Lemma sim_src_na_write_tview f flag_src rel_vers tvw_src tvw_tgt
      sc loc to
      (SIM: sim_tview f flag_src rel_vers tvw_src tvw_tgt)
      (WF: Mapping.wfs f)
  :
    sim_tview f (fun loc0 => if Loc.eq_dec loc0 loc then Some to else flag_src loc0) rel_vers (TView.write_tview tvw_src sc loc to Ordering.na) tvw_tgt.
Proof.
  pose proof (mapping_latest_wf f).
  econs; ss.
  { i. des_ifs. econs.
    { ii. setoid_rewrite LocFun.add_spec; auto. des_ifs; ss.
      { unfold TimeMap.join.
        erewrite timemap_singleton_neq; auto.
        erewrite TimeFacts.le_join_l; auto.
        { eapply SIM; auto. }
        { eapply Time.bot_spec. }
      }
      { eapply SIM; auto. }
    }
    { ii. setoid_rewrite LocFun.add_spec; auto. des_ifs; ss.
      { unfold TimeMap.join.
        erewrite timemap_singleton_neq; auto.
        erewrite TimeFacts.le_join_l; auto.
        { eapply SIM; auto. }
        { eapply Time.bot_spec. }
      }
      { eapply SIM; auto. }
    }
  }
  { i. econs.
    { ii. des_ifs. ss.
      unfold TimeMap.join.
      erewrite timemap_singleton_neq; auto.
      erewrite TimeFacts.le_join_l; auto.
      { eapply SIM; auto. }
      { eapply Time.bot_spec. }
    }
    { ii. des_ifs. ss.
      unfold TimeMap.join.
      erewrite timemap_singleton_neq; auto.
      erewrite TimeFacts.le_join_l; auto.
      { eapply SIM; auto. }
      { eapply Time.bot_spec. }
    }
  }
  { econs.
    { ii. des_ifs. ss. unfold TimeMap.join.
      erewrite timemap_singleton_neq; auto.
      erewrite TimeFacts.le_join_l; auto.
      { eapply SIM; auto. }
      { eapply Time.bot_spec. }
    }
    { ii. des_ifs. ss. unfold TimeMap.join.
      erewrite timemap_singleton_neq; auto.
      erewrite TimeFacts.le_join_l; auto.
      { eapply SIM; auto. }
      { eapply Time.bot_spec. }
    }
  }
  { eapply SIM. }
Qed.

Lemma cancel_future_memory_decr loc prom0 mem0 prom1 mem1
      (FUTURE: cancel_future_memory loc prom0 mem0 prom1 mem1)
  :
  Memory.le mem1 mem0.
Proof.
  induction FUTURE; auto.
  { refl. }
  { etrans; eauto. inv CANCEL. eapply remove_le; eauto. }
Qed.

Lemma space_future_memory_trans_memory
      msgs mem0 mem1 mem2 f
      (FUTURE0: space_future_memory msgs f mem0 f mem1)
      (FUTURE1: space_future_memory msgs f mem1 f mem2)
      (MAPWF0: Mapping.wfs f)
  :
    space_future_memory msgs f mem0 f mem2.
Proof.
  eapply space_future_memory_trans; eauto.
  { refl. }
  { refl. }
  Qed.

Lemma unchanged_loc_max_ts mem0 mem1 loc
      (UNCH: unchanged_loc_memory loc mem0 mem1)
      (INHABITED: Memory.inhabited mem0)
  :
    Memory.max_ts loc mem0 = Memory.max_ts loc mem1.
Proof.
  specialize (INHABITED loc). eapply TimeFacts.antisym.
  { eapply Memory.max_ts_spec in INHABITED. des.
    inv UNCH. rewrite <- UNCH0 in GET.
    eapply Memory.max_ts_spec in GET. des. auto.
  }
  { inv UNCH. rewrite <- UNCH0 in INHABITED.
    eapply Memory.max_ts_spec in INHABITED. des.
    rewrite UNCH0 in GET.
    eapply Memory.max_ts_spec in GET. des. auto.
  }
Qed.

Lemma sim_thread_src_write_na
      f vers flag_src flag_tgt vs_src vs_tgt
      mem_src0 mem_tgt lc_src0 lc_tgt sc_src sc_tgt
      loc val_old val_new
      (SIM: sim_thread
              f vers flag_src flag_tgt vs_src vs_tgt
              mem_src0 mem_tgt lc_src0 lc_tgt sc_src sc_tgt)
      (VAL: vs_src loc = Some val_old)
      (CONSISTENT: Local.promise_consistent lc_tgt)
      (LOCALSRC: Local.wf lc_src0 mem_src0)
      (LOCALTGT: Local.wf lc_tgt mem_tgt)
      (MEMSRC: Memory.closed mem_src0)
      (MEMTGT: Memory.closed mem_tgt)
      (SCSRC: Memory.closed_timemap sc_src mem_src0)
      (WF: Mapping.wfs f)
      lang st
  :
    exists mem_src1 mem_src2 lc_src1 lc_src2 from to msgs kinds kind,
      (<<STEPS: rtc (@Thread.tau_step _)
                    (Thread.mk lang st lc_src0 sc_src mem_src0)
                    (Thread.mk _ st lc_src1 sc_src mem_src1)>>) /\
      (<<WRITE: Local.write_na_step lc_src1 sc_src mem_src1 loc from to val_new Ordering.na lc_src2 sc_src mem_src2 msgs kinds kind>>) /\
      (<<SIM: sim_thread
                f vers
                (fun loc0 => if Loc.eq_dec loc0 loc then true else flag_src loc0)
                (fun loc0 => if Loc.eq_dec loc0 loc then true else flag_tgt loc0)
                (fun loc0 => if Loc.eq_dec loc0 loc then Some val_new else vs_src loc0)
                vs_tgt
                mem_src2 mem_tgt lc_src2 lc_tgt sc_src sc_tgt>>) /\
        (<<SPACE: space_future_memory (unchangable mem_tgt lc_tgt.(Local.promises)) f mem_src0 f mem_src2>>)
.
Proof.
  hexploit sim_thread_tgt_flag_up; eauto.
  instantiate (1:=loc). clear SIM. i. des.
  inv SIM. hexploit (MAXSRC loc). i.
  inv H. hexploit MAX; eauto. i. des.
  hexploit top_time_exists.
  { eauto. }
  i. des.
  hexploit Thread.rtc_tau_step_future; eauto. i. ss. des.
  hexploit max_readable_na_write_step.
  { eauto. }
  { eauto. }
  { eauto. }
  { eauto. }
  { eauto. }
  { eapply sim_local_consistent; eauto. }
  { instantiate (1:=top). left. eapply TS. }
  { eapply Time.incr_spec. }
  { eapply Time.incr_spec. }
  i. des.
  hexploit reserve_future_steps.
  { eapply cancel_future_reserve_future; eauto. }
  i. des.
  hexploit Thread.rtc_tau_step_future; eauto. i. ss. des.
  subst. hexploit src_cancels_sim_promises; eauto.
  { eapply WF2. }
  i. des.
  hexploit Local.write_na_step_future; eauto. i. des.
  assert (RLX: View.rlx (TView.cur tvw1) loc = Time.incr (Time.incr top)).
  { eapply TimeFacts.antisym.
    { rewrite <- MAXTS. inv WF1. ss.
      inv TVIEW_CLOSED. inv CUR. exploit RLX; eauto. i. des.
      eapply Memory.max_ts_spec in x. des. eauto.
    }
    { rewrite <- VIEW. inv WF1. ss. inv TVIEW_WF. eapply CUR. }
  }
  assert (OTHERRLX: forall loc0 (NEQ: loc0 <> loc),
             View.rlx (TView.cur tvw1) loc0 = View.rlx (TView.cur tvw) loc0).
  { i. inv WRITE. clarify. ss.
    eapply TimeFacts.le_join_l. unfold TimeMap.singleton.
    setoid_rewrite LocFun.add_spec_neq; auto. eapply Time.bot_spec.
  }
  assert (OTHERPLN: forall loc0 (NEQ: loc0 <> loc),
             View.pln (TView.cur tvw1) loc0 = View.pln (TView.cur tvw) loc0).
  { i. inv WRITE. clarify. ss.
    eapply TimeFacts.le_join_l. unfold TimeMap.singleton.
    setoid_rewrite LocFun.add_spec_neq; auto. eapply Time.bot_spec.
  }
  assert (FLAGTOP: flag_src loc = true -> Time.le (srctm loc) top).
  { i. etransitivity; [|left; eapply TS].
    inv LOCAL. hexploit FLAGSRC; eauto. i. des. subst.
    inv WF2. ss. inv TVIEW_CLOSED. inv CUR.
    exploit RLX0. i. des. rewrite SRCTM.
    eapply Memory.max_ts_spec in x. des. eauto.
  }
  esplits.
  { etrans; eauto. }
  { eauto. }
  { econs; auto.
    { eapply add_src_sim_memory; eauto. i. clarify. }
    { dup LOCAL. ss. inv LOCAL0. econs.
      { inv WRITE. clarify. ss.
        eapply sim_src_na_write_tview; eauto.
      }
      { eapply src_writtten_sim_promises.
        { eapply src_fulfill_sim_promises; eauto. }
        { des_ifs. }
        { i. des_ifs. }
      }
      { eauto. }
      { i. des_ifs.
        { rewrite VIEW. rewrite RLX. auto. }
        { hexploit FLAGSRC; eauto. i. des.
          rewrite OTHERRLX; auto. rewrite OTHERPLN; auto.
        }
      }
      { i. des_ifs. rewrite OTHERRLX; auto. }
    }
    { ii. specialize (MAXSRC loc0). inv MAXSRC. des_ifs.
      { econs; ss. i. clarify. rewrite VIEW. eauto. }
      { econs; ss.
        { i. hexploit MAX2; eauto. i. des.
          rewrite OTHERPLN; auto. esplits.
          erewrite unchanged_loc_max_readable; eauto.
          { econs. i. rewrite PROMISES. des_ifs. }
          { symmetry. etrans.
            { eapply cancel_future_unchanged_loc in RESERVE; eauto. des; eauto.  }
            { etrans.
              { eapply add_unchanged_loc; eauto. }
              { eapply add_unchanged_loc; eauto. }
            }
          }
        }
        { i. hexploit NONMAX0; eauto. i.
          rewrite OTHERPLN; auto.
          erewrite unchanged_loc_max_readable; eauto.
          { econs. i. rewrite PROMISES. des_ifs. }
          { symmetry. etrans.
            { eapply cancel_future_unchanged_loc in RESERVE; eauto. des; eauto.  }
            { etrans.
              { eapply add_unchanged_loc; eauto. }
              { eapply add_unchanged_loc; eauto. }
            }
          }
        }
      }
    }
    { i. des_ifs. hexploit (PERM loc). i.
      rewrite VAL in H0. destruct (vs_tgt loc); auto.
    }
    { red in FIN. des. exists (loc::dom). ii. split; i.
      { des. des_ifs; ss; auto. right. eapply DOM. eauto. }
      { des_ifs; eauto. eapply DOM. ss. des; ss. intuition. }
    }
    { eapply sim_closed_memory_future; eauto.
      eapply Memory.future_future_weak. etrans; eauto.
    }
    { i. ss. des_ifs. rewrite MAXTIMES; auto.
      eapply unchanged_loc_max_ts.
      2:{ eapply CLOSED2. }
      etrans.
      { eapply cancel_future_unchanged_loc in RESERVE; eauto. des; eauto. }
      etrans.
      { eapply add_unchanged_loc; eauto. }
      { eapply add_unchanged_loc; eauto. }
    }
    { inv LOCAL. eapply reserved_space_empty_fulfilled_memory in RESERVE; try exact PROMISES0.
      { ss. eapply reserved_space_empty_add.
        { eapply reserved_space_empty_add.
          { eapply RESERVE. }
          { eauto. }
          { eauto. }
        }
        { eauto. }
        { eapply top_time_mon; eauto. left. eapply Time.incr_spec. }
      }
      { eauto. }
      { eapply WF2. }
      { ii. subst. inv WRITE. ss. clarify.
        eapply memory_write_na_reserve_same_rev in GET; eauto.
        rewrite PROMISES in GET. des_ifs.
      }
      { i. ss. des_ifs; auto. }
    }
    { eapply promise_finalized_promise_decr.
      { eapply FINALIZED. }
      i. ss. left. rewrite PROMISES in GETSRC. des_ifs.
      esplits; eauto.
    }
  }
  { eapply space_future_memory_trans_memory; eauto.
    eapply space_future_memory_trans_memory; [..|eauto].
    { eapply space_future_covered_decr.
      { i. eapply memory_le_covered; [|eauto].
        eapply cancel_future_memory_decr; eauto.
      }
    }
    eapply space_future_memory_mon_msgs.
    { eapply add_src_sim_memory_space_future; eauto. }
    { eapply unchangable_messages_of_memory. }
  }
Qed.

Lemma sim_thread_acquire
      f vers flag_src flag_tgt vs_src0 vs_tgt0
      mem_src mem_tgt prom_src prom_tgt tvw_src0 tvw_tgt0 sc_src sc_tgt
      tvw_src1 tvw_tgt1 rel_vers
      (SIM: sim_thread
              f vers flag_src flag_tgt vs_src0 vs_tgt0
              mem_src mem_tgt (Local.mk tvw_src0 prom_src) (Local.mk tvw_tgt0 prom_tgt) sc_src sc_tgt)
      (TVIEW: sim_tview f flag_src rel_vers tvw_src1 tvw_tgt1)
      (CONSISTENT: Local.promise_consistent (Local.mk tvw_tgt1 prom_tgt))
      (LOCALSRC0: Local.wf (Local.mk tvw_src0 prom_src) mem_src)
      (LOCALSRC1: Local.wf (Local.mk tvw_src1 prom_src) mem_src)
      (LOCALTGT0: Local.wf (Local.mk tvw_tgt0 prom_tgt) mem_tgt)
      (LOCALTGT1: Local.wf (Local.mk tvw_tgt1 prom_tgt) mem_tgt)
      (MEMSRC: Memory.closed mem_src)
      (SCSRC: Memory.closed_timemap sc_src mem_src)
      (WF: Mapping.wfs f)
      (LESRC: TView.le tvw_src0 tvw_src1)
      (LETGT: TView.le tvw_tgt0 tvw_tgt1)
      (RELVERS: wf_release_vers vers prom_tgt rel_vers)
      (FLAGS: forall loc
                     (SRC: flag_src loc = false)
                     (TGT: flag_tgt loc = true),
          (<<PLN: tvw_src1.(TView.cur).(View.pln) loc = tvw_src0.(TView.cur).(View.pln) loc>>) /\
          (<<RLX: tvw_src1.(TView.cur).(View.rlx) loc = tvw_src0.(TView.cur).(View.rlx) loc>>))
  :
    exists vs_src1 vs_tgt1,
      (<<SIM: sim_thread
                f vers flag_src flag_tgt vs_src1 vs_tgt1
                mem_src mem_tgt (Local.mk tvw_src1 prom_src) (Local.mk tvw_tgt1 prom_tgt) sc_src sc_tgt>>) /\
      (<<VALS: forall loc,
          ((<<SRC: vs_src1 loc = vs_src0 loc>>) /\ (<<TGT: vs_tgt1 loc = vs_tgt0 loc>>)) \/
          (exists val_src val_tgt,
              (<<FLAGSRC: flag_src loc = false>>) /\
                (<<FLAGTGT: flag_tgt loc = false>>) /\
                (<<NONESRC: vs_src0 loc = None>>) /\ (<<NONETGT: vs_tgt0 loc = None>>) /\
                (<<VALSRC: vs_src1 loc = Some val_src>>) /\ (<<VALTGT: vs_tgt1 loc = Some val_tgt>>) /\
                (<<VALLE: Const.le val_tgt val_src>>) /\
                (<<TS: Time.lt (tvw_src0.(TView.cur).(View.pln) loc) (tvw_src1.(TView.cur).(View.pln) loc)>>) /\
                (<<VALSRC: __guard__(exists from released, Memory.get loc (tvw_src1.(TView.cur).(View.pln) loc) mem_src = Some (from, Message.concrete val_src released))>>) /\
                (<<VALTGT: __guard__(exists from released, Memory.get loc (tvw_tgt1.(TView.cur).(View.pln) loc) mem_tgt = Some (from, Message.concrete val_tgt released))>>))>>)
.
Proof.
  assert (VIEWEQ: forall loc
                         (SRC: flag_src loc = true),
             (<<PLN: tvw_src1.(TView.cur).(View.pln) loc = tvw_src0.(TView.cur).(View.pln) loc>>) /\
             (<<RLX: tvw_src1.(TView.cur).(View.rlx) loc = tvw_src0.(TView.cur).(View.rlx) loc>>)).
  { inv SIM. inv LOCAL. i. hexploit FLAGSRC; eauto. i. des.
    hexploit sim_memory_src_flag_max_concrete; eauto.
    { rewrite SRCTM; eauto. inv LOCALSRC0. inv TVIEW_CLOSED. inv CUR.
      exploit RLX. i. des. eauto.
    }
    i. subst.
    inv LOCALSRC1. inv TVIEW_CLOSED. inv CUR. ss. splits.
    { eapply TimeFacts.antisym.
      { hexploit (PLN loc). i. des.
        eapply Memory.max_ts_spec in H1. des.
        rewrite H0 in MAX. rewrite SRCTM in MAX. auto. rewrite H in MAX. auto.
      }
      { eapply LESRC. }
    }
    { eapply TimeFacts.antisym.
      { hexploit (RLX loc). i. des.
        eapply Memory.max_ts_spec in H1. des.
        rewrite H0 in MAX. rewrite SRCTM in MAX. auto.
      }
      { eapply LESRC. }
    }
  }
  assert (SIMLOCAL: sim_local f vers tvw_src1.(TView.cur).(View.rlx) flag_src flag_tgt (Local.mk tvw_src1 prom_src) (Local.mk tvw_tgt1 prom_tgt)).
  { inv SIM. inv LOCAL. econs; eauto.
    { eapply sim_promises_change_no_flag; eauto. i.
      rewrite SRCTM. destruct (flag_src loc) eqn:EQ.
      { eapply VIEWEQ; auto. }
      { eapply FLAGS; auto. }
    }
    { i. hexploit VIEWEQ; eauto. i. des.
      rewrite PLN. rewrite RLX. eapply FLAGSRC; eauto.
    }
  }
  hexploit (@max_values_src_exists mem_src (Local.mk tvw_src1 prom_src)).
  i. des. rename vs into vs_src1.
  assert (VALSRC: forall loc,
             (<<SRC: vs_src1 loc = vs_src0 loc>>) \/
             (exists val,
                 (<<FLAGSRC: flag_src loc = false>>) /\
                 (<<NONESRC: vs_src0 loc = None>>) /\
                 (<<VALSRC: vs_src1 loc = Some val>>) /\
                 (<<TS: Time.lt (tvw_src0.(TView.cur).(View.pln) loc) (tvw_src1.(TView.cur).(View.pln) loc)>>) /\
                 (<<VALSRC: __guard__(exists from released, Memory.get loc (tvw_src1.(TView.cur).(View.pln) loc) mem_src = Some (from, Message.concrete val released))>>))).
  { inv SIM. i. destruct (vs_src0 loc) eqn:VAL0.
    { left. eapply max_value_src_inj; eauto.
      eapply max_value_src_mon.
      { rewrite <- VAL0. eapply MAXSRC. }
      { eauto. }
      { eauto. }
      { eauto. }
      { eapply sim_local_consistent; eauto. }
    }
    destruct (vs_src1 loc) eqn:VAL1; auto. right.
    esplits; eauto.
    { eapply max_value_src_flag_none; eauto.
      rewrite <- VAL0. auto.
    }
    { assert (TS: Time.le (View.pln (TView.cur tvw_src0) loc) (View.pln (TView.cur tvw_src1) loc)).
      { eapply LESRC. }
      inv TS; auto. exfalso.
      specialize (MAXSRC loc). specialize (MAX loc).
      rewrite VAL0 in MAXSRC. rewrite VAL1 in MAX.
      inv MAX. inv MAXSRC. hexploit MAX0; eauto. i. des.
      eapply NONMAX0; eauto. rewrite H. eauto.
    }
    { specialize (MAX loc). rewrite VAL1 in MAX.
      inv MAX. hexploit MAX0; eauto. i. des. inv MAX.
      red. esplits; eauto.
    }
  }
  assert (MEM: sim_memory (View.rlx (TView.cur tvw_src1)) flag_src f vers mem_src mem_tgt).
  { inv SIM. inv LOCAL. eapply sim_memory_change_no_flag; eauto.
    i. rewrite SRCTM. hexploit VIEWEQ; eauto. i. des. rewrite RLX. auto.
  }
  hexploit (choice (fun loc v =>
                      (<<MAXTGT: max_value_tgt loc v mem_tgt (Local.mk tvw_tgt1 prom_tgt)>>) /\
                      (((<<SRC: vs_src1 loc = vs_src0 loc>>) /\ (<<TGT: v = vs_tgt0 loc>>)) \/
                         (exists val_src val_tgt,
                             (<<FLAGSRC: flag_src loc = false>>) /\
                               (<<FLAGTGT: flag_tgt loc = false>>) /\
                               (<<NONESRC: vs_src0 loc = None>>) /\ (<<NONETGT: vs_tgt0 loc = None>>) /\
                               (<<VALSRC: vs_src1 loc = Some val_src>>) /\ (<<VALTGT: v = Some val_tgt>>) /\
                               (<<VALLE: Const.le val_tgt val_src>>) /\
                               (<<TS: Time.lt (tvw_src0.(TView.cur).(View.pln) loc) (tvw_src1.(TView.cur).(View.pln) loc)>>) /\
                               (<<VALRC: __guard__(exists from released, Memory.get loc (tvw_src1.(TView.cur).(View.pln) loc) mem_src = Some (from, Message.concrete val_src released))>>) /\
                               (<<VALTGT: __guard__(exists from released, Memory.get loc (tvw_tgt1.(TView.cur).(View.pln) loc) mem_tgt = Some (from, Message.concrete val_tgt released))>>))))).
  { intros loc. hexploit (VALSRC loc). i. des.
    { exists (vs_tgt0 loc). esplits; auto.
      { inv SIM. eapply max_value_tgt_mon; eauto. }
    }
    { assert (FLAG: flag_tgt loc = false).
      { destruct (flag_tgt loc) eqn:FLAG; auto.
        hexploit FLAGS; eauto. i. des. rewrite PLN in TS. timetac.
      }
      hexploit no_flag_max_value_same; eauto.
      { specialize (MAX loc). rewrite VALSRC0 in MAX. eauto. }
      i. des. exists (Some v_tgt). esplits; auto.
      right. esplits; eauto.
      { inv SIM. specialize (PERM loc).
        rewrite NONESRC in PERM. ss. des_ifs.
      }
      { inv MAX0. hexploit MAX1; eauto. i. des.
        inv MAX0. red. esplits; eauto.
      }
    }
  }
  clear VALSRC. intros [vs_tgt1 MAXTGT].
  exists vs_src1, vs_tgt1. splits; auto.
  { inv SIM. econs.
    { auto. }
    { eapply MEM. }
    { eauto. }
    { eauto. }
    { ii. hexploit (MAXTGT loc). i. des; auto. }
    { i. hexploit (MAXTGT loc). i. des.
      { rewrite SRC. rewrite TGT. auto. }
      { rewrite VALSRC. rewrite VALTGT. ss. }
    }
    { auto. }
    { auto. }
    { auto. }
    { i. rewrite <- MAXTIMES; auto. inv LOCAL. rewrite SRCTM. eapply VIEWEQ; auto. }
    { auto. }
    { auto. }
  }
  { i. hexploit (MAXTGT loc). i. des; eauto.
    right. esplits; eauto.
  }
Qed.

Lemma write_fence_tview_na tvw sc
  :
    TView.write_fence_tview tvw sc Ordering.na = tvw.
Proof.
  unfold TView.write_fence_tview. des_ifs.
  rewrite View.join_bot_r.
  destruct tvw; ss.
Qed.

Lemma write_fence_sc_na tvw sc
  :
    TView.write_fence_sc tvw sc Ordering.na = sc.
Proof.
  unfold TView.write_fence_sc. des_ifs.
Qed.

Lemma read_fence_tview_na tvw
  :
    TView.read_fence_tview tvw Ordering.na = tvw.
Proof.
  unfold TView.read_fence_tview. des_ifs.
  destruct tvw; ss.
Qed.

Lemma fence_step_merge
      lc0 sc0 ordr ordw lc1 sc1 lc2 sc2
      (STEP0: Local.fence_step lc0 sc0 ordr Ordering.na lc1 sc1)
      (STEP1: Local.fence_step lc1 sc1 Ordering.na ordw lc2 sc2)
  :
    Local.fence_step lc0 sc0 ordr ordw lc2 sc2.
Proof.
  inv STEP0. inv STEP1. ss. econs; eauto. f_equal.
  rewrite write_fence_tview_na. rewrite write_fence_sc_na.
  rewrite read_fence_tview_na. auto.
Qed.

Lemma fence_step_split
      lc0 sc0 ordr ordw lc2 sc2
      (STEP: Local.fence_step lc0 sc0 ordr ordw lc2 sc2)
  :
    exists lc1 sc1,
      (<<STEP0: Local.fence_step lc0 sc0 ordr Ordering.na lc1 sc1>>) /\
      (<<STEP1: Local.fence_step lc1 sc1 Ordering.na ordw lc2 sc2>>).
Proof.
  inv STEP. esplits.
  { econs; ss. }
  { econs; eauto. ss. f_equal.
    rewrite write_fence_tview_na. rewrite write_fence_sc_na.
    rewrite read_fence_tview_na. auto.
  }
Qed.

Definition local_read_fence_tview (tview1: TView.t) (sc1: TimeMap.t)
           (ordr ordw: Ordering.t): TView.t :=
  let tview2 := TView.read_fence_tview tview1 ordr in
  let sc2 := TView.write_fence_sc tview2 sc1 ordw in
  let cur2 :=
      if Ordering.le Ordering.seqcst ordw
      then View.mk sc2 sc2
      else TView.cur tview2 in
  let acq2 :=
      View.join
        (TView.acq tview2)
        (if Ordering.le Ordering.seqcst ordw
         then (View.mk sc2 sc2)
         else View.bot) in
  TView.mk
    (tview1.(TView.rel))
    cur2
    acq2.

Lemma local_read_fence_tview_wf tview sc ordr ordw
      (WF: TView.wf tview)
  :
    TView.wf (local_read_fence_tview tview sc ordr ordw).
Proof.
  econs; ss; des_ifs; ss; try by (eapply WF).
  { econs; ss. refl. }
  { econs; ss. eapply timemap_join_mon; [|refl]. eapply WF. }
  { rewrite View.join_bot_r. apply WF. }
  { i. unfold TView.write_fence_sc. des_ifs. econs; ss.
    { des_ifs.
      { etrans; [|eapply TimeMap.join_r].
        transitivity (View.pln (TView.cur tview)); [apply WF|].
        transitivity (View.rlx (TView.cur tview)); [apply WF|].
        apply WF.
      }
      { etrans; [|eapply TimeMap.join_r].
        transitivity (View.pln (TView.cur tview)); [apply WF|].
        apply WF.
      }
    }
    { des_ifs.
      { etrans; [|eapply TimeMap.join_r].
        transitivity (View.rlx (TView.cur tview)); [apply WF|].
        apply WF.
      }
      { etrans; [|eapply TimeMap.join_r]. apply WF. }
    }
  }
  { i. transitivity (TView.cur tview); apply WF. }
  { eapply View.join_r. }
  { apply View.join_l. }
  { rewrite View.join_bot_r. apply WF. }
Qed.

Lemma local_read_fence_tview_closed mem tview sc ordr ordw
      (TVIEW: TView.closed tview mem)
      (SC: Memory.closed_timemap sc mem)
  :
    TView.closed (local_read_fence_tview tview sc ordr ordw) mem.
Proof.
  unfold local_read_fence_tview, TView.write_fence_sc. econs; ss.
  { eapply TVIEW. }
  { des_ifs.
    { econs; ss.
      { eapply Memory.join_closed_timemap; eauto. eapply TVIEW. }
      { eapply Memory.join_closed_timemap; eauto. eapply TVIEW. }
    }
    { econs; ss.
      { eapply Memory.join_closed_timemap; eauto. eapply TVIEW. }
      { eapply Memory.join_closed_timemap; eauto. eapply TVIEW. }
    }
    { eapply TVIEW. }
    { eapply TVIEW. }
  }
  { des_ifs.
    { eapply Memory.join_closed_view.
      { eapply TVIEW. }
      econs; ss.
      { eapply Memory.join_closed_timemap; eauto. eapply TVIEW. }
      { eapply Memory.join_closed_timemap; eauto. eapply TVIEW. }
    }
    { eapply Memory.join_closed_view.
      { eapply TVIEW. }
      econs; ss.
      { eapply Memory.join_closed_timemap; eauto. eapply TVIEW. }
      { eapply Memory.join_closed_timemap; eauto. eapply TVIEW. }
    }
    { rewrite View.join_bot_r. apply TVIEW. }
  }
Qed.

Lemma local_read_fence_tview_incr tview sc ordr ordw
      (WF: TView.wf tview)
  :
    TView.le tview (local_read_fence_tview tview sc ordr ordw).
Proof.
  econs; ss.
  { i. refl. }
  { unfold TView.write_fence_sc. ss. des_ifs.
    { econs; ss.
      { etrans; [|eapply TimeMap.join_r].
        transitivity (View.rlx (TView.cur tview)); apply WF.
      }
      { etrans; [|eapply TimeMap.join_r]. apply WF.
      }
    }
    { econs; ss.
      { etrans; [|eapply TimeMap.join_r]. apply WF. }
      { eapply TimeMap.join_r. }
    }
    { apply WF. }
    { refl. }
  }
  { eapply View.join_l. }
Qed.

Definition local_write_fence_tview (tview1: TView.t) (ord: Ordering.t): TView.t :=
  TView.mk
    (fun loc =>
       if Ordering.le Ordering.acqrel ord
       then (TView.cur tview1) else (TView.rel tview1 loc))
    (TView.cur tview1)
    (TView.acq tview1)
.

Lemma local_write_fence_tview_wf tview ord
      (WF: TView.wf tview)
  :
    TView.wf (local_write_fence_tview tview ord).
Proof.
  econs; ss; des_ifs; ss; try by (eapply WF).
  { i. eapply WF. }
  { i. refl. }
Qed.

Lemma local_write_fence_tview_closed mem tview ord
      (TVIEW: TView.closed tview mem)
  :
    TView.closed (local_write_fence_tview tview ord) mem.
Proof.
  econs; ss.
  { i. des_ifs.
    { eapply TVIEW. }
    { eapply TVIEW. }
  }
  { eapply TVIEW. }
  { eapply TVIEW. }
Qed.

Lemma local_write_fence_tview_incr tview ord
      (WF: TView.wf tview)
  :
    TView.le tview (local_write_fence_tview tview ord).
Proof.
  econs; ss.
  { i. des_ifs.
    { eapply WF. }
    { refl. }
  }
  { refl. }
  { refl. }
Qed.

Definition local_write_fence_sc (tview1: TView.t) (sc: TimeMap.t) (ord: Ordering.t): TimeMap.t :=
  if Ordering.le Ordering.seqcst ord
  then (TimeMap.join sc (View.rlx (TView.cur tview1)))
  else sc
.

Lemma local_write_fence_sc_closed mem tview sc ord
      (TVIEW: TView.closed tview mem)
      (SC: Memory.closed_timemap sc mem)
  :
    Memory.closed_timemap (local_write_fence_sc tview sc ord) mem.
Proof.
  unfold local_write_fence_sc. des_ifs.
  eapply Memory.join_closed_timemap; auto. eapply TVIEW.
Qed.

Lemma local_write_fence_sc_incr tview sc ord
  :
    TimeMap.le sc (local_write_fence_sc tview sc ord).
Proof.
  unfold local_write_fence_sc. des_ifs.
  { eapply TimeMap.join_l. }
  { refl. }
Qed.

Lemma timemap_bot_join_l tm
  :
    TimeMap.join TimeMap.bot tm = tm.
Proof.
  eapply TimeMap.le_join_r. eapply TimeMap.bot_spec.
Qed.

Lemma timemap_bot_join_r tm
  :
    TimeMap.join tm TimeMap.bot = tm.
Proof.
  eapply TimeMap.le_join_l. eapply TimeMap.bot_spec.
Qed.

Lemma read_tview_incr_rlx
      tvw loc ts vw ord
      (WF: time_le_opt_view loc ts vw)
      (READABLE: Time.le (View.pln (TView.cur tvw) loc) ts)
      (ORD: Ordering.le Ordering.relaxed ord)
  :
    View.pln (TView.cur (TView.read_tview tvw loc ts vw ord)) loc = ts.
Proof.
  unfold TView.read_tview, View.singleton_ur_if in *. ss. des_ifs; ss.
  { unfold TimeMap.join. rewrite timemap_singleton_eq.
    rewrite TimeFacts.le_join_l.
    { apply TimeFacts.le_join_r. auto. }
    { inv WF; ss.
      { inv EXACT. unfold time_le_timemap in *. etrans; eauto.
        eapply Time.join_r.
      }
      { eapply Time.bot_spec. }
    }
  }
  { rewrite ! timemap_bot_join_r.
    unfold TimeMap.join. rewrite timemap_singleton_eq.
    eapply TimeFacts.le_join_r. auto.
  }
Qed.

Lemma read_tview_pln
      tvw loc ts vw ord
      (READABLE: Time.le (View.pln (TView.cur tvw) loc) ts)
      (ORD: ~ Ordering.le Ordering.relaxed ord)
  :
  View.pln (TView.cur (TView.read_tview tvw loc ts vw ord)) loc = View.pln (TView.cur tvw) loc.
Proof.
  unfold TView.read_tview, View.singleton_ur_if. ss. des_ifs; ss.
  { destruct ord; ss. }
  rewrite ! timemap_bot_join_r. auto.
Qed.

Variant local_fence_read_step lc1 sc1 ordr ordw lc2: Prop :=
| local_fence_read_step_intro
    (LOCAL: lc2 = Local.mk
                    (local_read_fence_tview lc1.(Local.tview) sc1 ordr ordw)
                    (lc1.(Local.promises)))
    (RELEASE: Ordering.le Ordering.strong_relaxed ordw -> Memory.nonsynch lc1.(Local.promises))
    (PROMISES: ordw = Ordering.seqcst -> lc1.(Local.promises) = Memory.bot)
.

Lemma local_fence_read_step_future mem lc1 sc1 ordr ordw lc2
      (STEP: local_fence_read_step lc1 sc1 ordr ordw lc2)
      (LOCAL: Local.wf lc1 mem)
      (SC: Memory.closed_timemap sc1 mem)
  :
    (<<LOCAL: Local.wf lc2 mem>>) /\
    (<<INCR: TView.le lc1.(Local.tview) lc2.(Local.tview)>>).
Proof.
  inv STEP. splits.
  { inv LOCAL. econs; ss.
    { eapply local_read_fence_tview_wf; eauto. }
    { eapply local_read_fence_tview_closed; eauto. }
  }
  { eapply local_read_fence_tview_incr; eauto. eapply LOCAL. }
Qed.

Variant local_fence_write_step lc1 sc1 ord lc2 sc2: Prop :=
| local_fence_write_step_intro
    (LOCAL: lc2 = Local.mk
                    (local_write_fence_tview lc1.(Local.tview) ord)
                    (lc1.(Local.promises)))
    (SC: sc2 = local_write_fence_sc lc1.(Local.tview) sc1 ord)
.

Lemma local_fence_write_step_future mem lc1 sc1 ord lc2 sc2
      (STEP: local_fence_write_step lc1 sc1 ord lc2 sc2)
      (LOCAL: Local.wf lc1 mem)
      (SC: Memory.closed_timemap sc1 mem)
  :
    (<<LOCAL: Local.wf lc2 mem>>) /\
    (<<SC: Memory.closed_timemap sc2 mem>>) /\
    (<<INCR: TView.le lc1.(Local.tview) lc2.(Local.tview)>>).
Proof.
  inv STEP. splits.
  { inv LOCAL. econs; ss.
    { eapply local_write_fence_tview_wf; eauto. }
    { eapply local_write_fence_tview_closed; eauto. }
  }
  { eapply local_write_fence_sc_closed; eauto. eapply LOCAL. }
  { eapply local_write_fence_tview_incr; eauto. eapply LOCAL. }
Qed.

Lemma local_fence_tview_merge
      tvw sc ordr ordw
      (WF: TView.wf tvw)
  :
    local_write_fence_tview (local_read_fence_tview tvw sc ordr ordw) ordw
    =
    TView.write_fence_tview (TView.read_fence_tview tvw ordr) sc ordw.
Proof.
  ss.
Qed.

Lemma local_fence_sc_merge
      tvw sc ordr ordw
      (WF: TView.wf tvw)
  :
    local_write_fence_sc (local_read_fence_tview tvw sc ordr ordw) sc ordw =
    TView.write_fence_sc (TView.read_fence_tview tvw ordr) sc ordw.
Proof.
  assert (IDEM: forall tm, TimeMap.join tm tm = tm).
  { i. apply TimeMap.le_join_l. refl. }
  Local Transparent Ordering.le.
  unfold local_write_fence_sc, local_read_fence_tview, TView.read_fence_tview, TView.write_fence_tview, TView.write_fence_sc.
  destruct ordr eqn:ORDR, ordw eqn:ORDW; ss.
  { rewrite <- TimeMap.join_assoc. f_equal. auto. }
  { rewrite <- TimeMap.join_assoc. f_equal. auto. }
  { rewrite <- TimeMap.join_assoc. f_equal. auto. }
  { rewrite <- TimeMap.join_assoc. f_equal. auto. }
  { rewrite <- TimeMap.join_assoc. f_equal. auto. }
  { rewrite <- TimeMap.join_assoc. f_equal. auto. }
  Local Opaque Ordering.le.
Qed.

Lemma local_fence_step_merge
      lc0 sc0 ordr lc1 ordw lc2 sc1
      (STEP0: local_fence_read_step lc0 sc0 ordr ordw lc1)
      (STEP1: local_fence_write_step lc1 sc0 ordw lc2 sc1)
      (WF: TView.wf lc0.(Local.tview))
  :
    Local.fence_step lc0 sc0 ordr ordw lc2 sc1.
Proof.
  inv STEP0. inv STEP1. ss. econs; ss.
  rewrite local_fence_sc_merge; eauto.
Qed.

Lemma local_fence_step_split
      lc0 sc0 ordr ordw lc2 sc1
      (STEP: Local.fence_step lc0 sc0 ordr ordw lc2 sc1)
      (WF: TView.wf lc0.(Local.tview))
  :
    exists lc1,
      (<<STEP0: local_fence_read_step lc0 sc0 ordr ordw lc1>>) /\
      (<<STEP1: local_fence_write_step lc1 sc0 ordw lc2 sc1>>).
Proof.
  inv STEP. esplits.
  { econs; eauto. }
  { econs; ss. rewrite local_fence_sc_merge; auto. }
Qed.

Lemma sim_local_read_fence_tview f flag_src rel_vers tvw_src tvw_tgt sc_src sc_tgt
      ordr ordw
      (SIM: sim_tview f flag_src rel_vers tvw_src tvw_tgt)
      (SC: sim_timemap (fun loc => flag_src loc = false) f (Mapping.vers f) sc_src sc_tgt)
      (WF: Mapping.wfs f)
  :
    sim_tview f flag_src rel_vers (local_read_fence_tview tvw_src sc_src ordr ordw) (local_read_fence_tview tvw_tgt sc_tgt ordr ordw).
Proof.
  pose proof (mapping_latest_wf f).
  assert (READ: sim_tview f flag_src rel_vers (TView.read_fence_tview tvw_src ordr) (TView.read_fence_tview tvw_tgt ordr)).
  { eapply sim_read_fence_tview; eauto. }
  assert (WRITE: sim_timemap (fun loc => flag_src loc = false) f (Mapping.vers f) (TView.write_fence_sc (TView.read_fence_tview tvw_src ordr) sc_src ordw) (TView.write_fence_sc (TView.read_fence_tview tvw_tgt ordr) sc_tgt ordw)).
  { eapply sim_write_fence_sc; eauto. }
  econs; ss.
  { eapply SIM. }
  { des_ifs.
    { eapply SIM. }
    { eapply SIM. }
  }
  { eapply sim_view_join; eauto.
    { eapply SIM. }
    { des_ifs. eapply sim_view_bot; eauto. }
  }
  { eapply SIM. }
Qed.

Lemma sim_local_write_fence_tview_normal f flag_src rel_vers tvw_src tvw_tgt
      ord
      (SIM: sim_tview f flag_src rel_vers tvw_src tvw_tgt)
      (ORD: ~ Ordering.le Ordering.acqrel ord)
      (WF: Mapping.wfs f)
  :
    sim_tview f flag_src rel_vers (local_write_fence_tview tvw_src ord) (local_write_fence_tview tvw_tgt ord).
Proof.
  pose proof (mapping_latest_wf f).
  econs; ss.
  { i. des_ifs. eapply SIM. }
  { eapply SIM. }
  { eapply SIM. }
  { eapply SIM. }
Qed.

Lemma sim_local_write_fence_tview_release f flag_src rel_vers tvw_src tvw_tgt
      ord
      (SIM: sim_tview f flag_src rel_vers tvw_src tvw_tgt)
      (FLAG: forall loc, flag_src loc = false)
      (WF: Mapping.wfs f)
  :
    sim_tview f flag_src (fun _ => Mapping.vers f) (local_write_fence_tview tvw_src ord) (local_write_fence_tview tvw_tgt ord).
Proof.
  pose proof (mapping_latest_wf f).
  econs; ss.
  { i. des_ifs.
    { eapply sim_view_mon_locs.
      { eapply SIM. }
      { i. ss. }
    }
    { eapply sim_view_mon_ver; auto.
      { eapply SIM. }
      { eapply version_le_version_wf. eapply SIM. }
    }
  }
  { eapply SIM. }
  { eapply SIM. }
Qed.

Lemma sim_local_write_fence_sc f flag_src rel_vers tvw_src tvw_tgt sc_src sc_tgt
      ord
      (SIM: sim_tview f flag_src rel_vers tvw_src tvw_tgt)
      (SC: sim_timemap (fun _ => True) f (Mapping.vers f) sc_src sc_tgt)
      (FLAG: Ordering.le Ordering.seqcst ord -> forall loc, flag_src loc = false)
      (WF: Mapping.wfs f)
  :
    sim_timemap (fun _ => True) f (Mapping.vers f) (local_write_fence_sc tvw_src sc_src ord) (local_write_fence_sc tvw_tgt sc_tgt ord).
Proof.
  pose proof (mapping_latest_wf f).
  unfold local_write_fence_sc. des_ifs. eapply sim_timemap_join; auto.
  eapply sim_timemap_mon_locs.
  { eapply SIM. }
  { i. eapply FLAG. auto. }
Qed.

Lemma sim_thread_read
      f vers flag_src flag_tgt vs_src0 vs_tgt0
      mem_src mem_tgt lc_src0 lc_tgt0 sc_src sc_tgt
      lc_tgt1 loc to_tgt val_tgt0 released_tgt ord
      (SIM: sim_thread
              f vers flag_src flag_tgt vs_src0 vs_tgt0
              mem_src mem_tgt lc_src0 lc_tgt0 sc_src sc_tgt)
      (READ: Local.read_step lc_tgt0 mem_tgt loc to_tgt val_tgt0 released_tgt ord lc_tgt1)
      (CONSISTENT: Local.promise_consistent lc_tgt1)
      (LOCALSRC: Local.wf lc_src0 mem_src)
      (LOCALTGT: Local.wf lc_tgt0 mem_tgt)
      (MEMSRC: Memory.closed mem_src)
      (MEMTGT: Memory.closed mem_tgt)
      (SCSRC: Memory.closed_timemap sc_src mem_src)
      (SCTGT: Memory.closed_timemap sc_tgt mem_tgt)
      (WF: Mapping.wfs f)
      (VERS: versions_wf f vers)
      (FLAGSRC: flag_src loc = false)
      (FLAGTGT: flag_tgt loc = false)
      (FLAG: forall loc
                    (SRC: flag_src loc = false) (TGT: flag_tgt loc = true),
          ~ Ordering.le Ordering.acqrel ord)
  :
    exists val_tgt1 val_src1 to_src released_src lc_src1 vs_src1 vs_tgt1,
      (<<READ: forall val (VAL: Const.le val val_src1), Local.read_step lc_src0 mem_src loc to_src val released_src ord lc_src1>>) /\
      (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src to_tgt>>) /\
      (<<RELEASED: sim_opt_view (fun loc0 => loc0 <> loc) f (vers loc to_tgt) released_src released_tgt>>) /\
      (<<SIM: sim_thread
                f vers flag_src flag_tgt vs_src1 vs_tgt1
                mem_src mem_tgt lc_src1 lc_tgt1 sc_src sc_tgt>>) /\
      (<<VAL: Const.le val_tgt1 val_src1>>) /\
      (<<VALTGT: Const.le val_tgt0 val_tgt1>>) /\
      (<<NUPDATESRC: forall val (VAL: vs_src0 loc = Some val), val = val_src1>>) /\
      (<<NUPDATETGT: forall val (VAL: vs_tgt0 loc = Some val), val = val_tgt1>>) /\
      (<<VALS: forall loc0,
          ((<<SRC: vs_src1 loc0 = vs_src0 loc0>>) /\ (<<TGT: vs_tgt1 loc0 = vs_tgt0 loc0>>)) \/
          (exists val_src val_tgt,
              (<<NONESRC: vs_src0 loc0 = None>>) /\ (<<NONETGT: vs_tgt0 loc0 = None>>) /\
              (<<VALSRC: vs_src1 loc0 = Some val_src>>) /\ (<<VALTGT: vs_tgt1 loc0 = Some val_tgt>>) /\
              (<<VALLE: Const.le val_tgt val_src>>) /\
              (((<<LOC: loc0 <> loc>>) /\ (<<ORD: Ordering.le Ordering.acqrel ord>>)) \/
               ((<<LOC: loc0 = loc>>) /\ (<<SRC: val_src = val_src1>>) /\ (<<TGT: val_tgt = val_tgt1>>))))>>).
Proof.
  hexploit Local.read_step_future; eauto. i. des.
  destruct lc_src0 as [tvw_src0 prom_src].
  destruct lc_tgt0 as [tvw_tgt0 prom_tgt].
  dup SIM. inv SIM. inv LOCAL. inv READ.
  hexploit sim_memory_get; eauto; ss. i. des. inv MSG; ss.
  assert (READSRC: exists tvw_src1, (<<READSRC: forall val (VAL: Const.le val val_src), Local.read_step (Local.mk tvw_src0 prom_src) mem_src loc to_src val vw_src ord (Local.mk tvw_src1 prom_src)>>) /\
                                    (<<SIM: sim_tview f flag_src rel_vers tvw_src1 (TView.read_tview tvw_tgt0 loc to_tgt released_tgt ord)>>)).
  { esplits.
    { i. econs; eauto.
      { ss. inv TVIEW. eapply sim_readable; eauto. }
    }
    { ss. eapply sim_read_tview; eauto.
      { rewrite H0. eapply VERS. }
      { eapply MEMSRC in GET0. des.
        eapply message_to_time_le_opt_view; eauto.
      }
      { eapply MEMTGT in GET. des.
        eapply message_to_time_le_opt_view; eauto.
      }
    }
  }
  des. hexploit READSRC0; [refl|..]. intros READSRC.
  hexploit Local.read_step_future; eauto. i. des. ss.
  hexploit sim_thread_acquire; eauto.
  { i. hexploit FLAG; eauto. i.
    assert (LOC: loc0 <> loc).
    { ii. subst. rewrite FLAGTGT in TGT. ss. }
    inv READSRC. ss. inv LC2. splits.
    { ss. destruct (Ordering.le Ordering.acqrel ord); ss.
      rewrite timemap_bot_join_r.
      unfold TimeMap.join.
      rewrite TimeFacts.le_join_l; auto.
      destruct (Ordering.le Ordering.relaxed ord); ss.
      { rewrite timemap_singleton_neq; auto. eapply Time.bot_spec. }
      { eapply Time.bot_spec. }
    }
    { ss. destruct (Ordering.le Ordering.acqrel ord); ss.
      rewrite timemap_bot_join_r.
      unfold TimeMap.join.
      rewrite TimeFacts.le_join_l; auto.
      destruct (Ordering.le Ordering.relaxed ord); ss.
      { rewrite timemap_singleton_neq; auto. eapply Time.bot_spec. }
      { rewrite timemap_singleton_neq; auto. eapply Time.bot_spec. }
    }
  }
  i. des. esplits; eauto.
  { i. specialize (MAXSRC loc). rewrite VAL1 in MAXSRC. inv MAXSRC.
    hexploit MAX; eauto. i. des.
    hexploit max_readable_read_only_aux; eauto.
    { inv SIM2. eapply sim_local_consistent; eauto. }
    i. des. subst. inv MAX0.
    rewrite GET1 in GET0. inv GET0. auto.
  }
  { i. specialize (MAXTGT loc). rewrite VAL1 in MAXTGT. inv MAXTGT.
    hexploit MAX; eauto. i. des.
    hexploit max_readable_read_only_aux; eauto.
    i. des. subst. inv MAX0.
    rewrite GET1 in GET. inv GET. auto.
  }
  i. hexploit VALS; eauto. i. des.
  { left. eauto. }
  { right. esplits; eauto. destruct (Loc.eq_dec loc0 loc).
    { assert (ORD: Ordering.le Ordering.relaxed ord).
      { inv READSRC. inv LC2.
        eapply NNPP. ii. eapply read_tview_pln in H.
        { rewrite H in TS. timetac. }
        { inv READABLE0. ss. }
      }
      subst. right. splits; auto.
      { red in VALSRC0. des.
        replace (View.pln (TView.cur tvw_src1) loc) with to_src in VALSRC0.
        { rewrite GET0 in VALSRC0. inv VALSRC0. auto. }
        symmetry. inv READSRC. inv LC2.
        ss. eapply read_tview_incr_rlx; eauto.
        { eapply message_to_time_le_opt_view; eauto.
          eapply MEMSRC; eauto.
        }
        { inv READABLE0. ss. }
      }
      { red in VALTGT0. des.
        replace (View.pln (TView.cur (TView.read_tview tvw_tgt0 loc to_tgt released_tgt ord)) loc) with to_tgt in VALTGT0.
        { rewrite GET in VALTGT0. inv VALTGT0. auto. }
        symmetry. eapply read_tview_incr_rlx; eauto.
        { eapply message_to_time_le_opt_view; eauto.
          eapply MEMTGT; eauto.
        }
        { inv READABLE. ss. }
      }
    }
    { left. inv READSRC. inv LC2. ss.
      destruct (Ordering.le Ordering.acqrel ord); auto.
      ss. rewrite timemap_bot_join_r in TS.
      unfold TimeMap.join in TS. rewrite TimeFacts.le_join_l in TS; auto.
      { timetac. }
      { destruct (Ordering.le Ordering.relaxed ord); ss.
        { rewrite timemap_singleton_neq; auto. eapply Time.bot_spec. }
        { apply Time.bot_spec. }
      }
    }
  }
Qed.

Lemma sim_thread_read_fence_step
      f vers flag_src flag_tgt vs_src0 vs_tgt0
      mem_src mem_tgt lc_src0 lc_tgt0 sc_src sc_tgt
      lc_tgt1 ordr ordw
      (SIM: sim_thread
              f vers flag_src flag_tgt vs_src0 vs_tgt0
              mem_src mem_tgt lc_src0 lc_tgt0 sc_src sc_tgt)
      (READ: local_fence_read_step lc_tgt0 sc_tgt ordr ordw lc_tgt1)
      (CONSISTENT: Local.promise_consistent lc_tgt1)
      (LOCALSRC: Local.wf lc_src0 mem_src)
      (LOCALTGT: Local.wf lc_tgt0 mem_tgt)
      (MEMSRC: Memory.closed mem_src)
      (MEMTGT: Memory.closed mem_tgt)
      (SCSRC: Memory.closed_timemap sc_src mem_src)
      (SCTGT: Memory.closed_timemap sc_tgt mem_tgt)
      (WF: Mapping.wfs f)
      (VERS: versions_wf f vers)
      (ACQFLAG: forall loc
                       (SRC: flag_src loc = false) (TGT: flag_tgt loc = true),
          ~ Ordering.le Ordering.acqrel ordr)
      (RELFLAG: forall loc
                       (SRC: flag_src loc = false) (TGT: flag_tgt loc = true),
          ~ Ordering.le Ordering.seqcst ordw)
  :
    exists lc_src1 vs_src1 vs_tgt1,
      (<<READ: local_fence_read_step lc_src0 sc_src ordr ordw lc_src1>>) /\
      (<<SIM: sim_thread
                f vers flag_src flag_tgt vs_src1 vs_tgt1
                mem_src mem_tgt lc_src1 lc_tgt1 sc_src sc_tgt>>) /\
      (<<VALS: forall loc0,
          ((<<SRC: vs_src1 loc0 = vs_src0 loc0>>) /\ (<<TGT: vs_tgt1 loc0 = vs_tgt0 loc0>>)) \/
          (exists val_src val_tgt,
              (<<NONESRC: vs_src0 loc0 = None>>) /\ (<<NONETGT: vs_tgt0 loc0 = None>>) /\
              (<<VALSRC: vs_src1 loc0 = Some val_src>>) /\ (<<VALTGT: vs_tgt1 loc0 = Some val_tgt>>) /\
              (<<VALLE: Const.le val_tgt val_src>>) /\
              (<<ORD: Ordering.le Ordering.acqrel ordr \/ Ordering.le Ordering.seqcst ordw>>))>>).
Proof.
  assert (exists lc_src1, (<<READ: local_fence_read_step lc_src0 sc_src ordr ordw lc_src1>>)).
  { inv READ. inv SIM. inv LOCAL. esplits. econs; eauto.
    { i. eapply sim_promises_nonsynch; eauto. }
    { i. subst. ss. eapply sim_promises_bot; eauto. i.
      destruct (flag_tgt loc) eqn:EQ; auto.
      exfalso. eapply RELFLAG; eauto.
    }
  }
  des. hexploit local_fence_read_step_future; [eapply READ|..]; eauto. i. des.
  hexploit local_fence_read_step_future; [eapply READ0|..]; eauto. i. des.
  destruct lc_src0 as [tvw_src0 prom_src].
  destruct lc_tgt0 as [tvw_tgt0 prom_tgt].
  inv READ. inv READ0. ss.
  dup SIM. inv SIM. inv LOCAL1.
  assert (VIEW: sim_tview f flag_src rel_vers (local_read_fence_tview tvw_src0 sc_src ordr ordw) (local_read_fence_tview tvw_tgt0 sc_tgt ordr ordw)).
  { eapply sim_local_read_fence_tview; eauto. eapply sim_timemap_mon_locs; eauto; ss. }
  hexploit sim_thread_acquire; eauto.
  { i. hexploit ACQFLAG; eauto. hexploit RELFLAG; eauto. i. ss. des_ifs; ss. }
  i. des. esplits; eauto.
  { econs; eauto. }
  { i. hexploit (VALS loc0). i. des; eauto.
    right. esplits; eauto. clear - TS.
    unfold local_read_fence_tview, TView.write_fence_sc, TView.read_fence_tview in TS; ss.
    des_ifs; auto. timetac.
  }
Qed.

Lemma mapped_msgs_exists_aux f0 f1 vers msgs_tgt prom_tgt loc flag_new
      mem_src
      (PROM: exists srctm flag_src flag_tgt prom_src, sim_promises srctm flag_src flag_tgt f0 vers prom_src prom_tgt)
      (MAPLE: Mapping.le (f0 loc) f1)
      (MSGS: forall from to msg (IN: List.In (from, to, msg) msgs_tgt), Memory.get loc to prom_tgt = Some (from, msg))
      (WF0: Mapping.wfs f0)
      (WF1: Mapping.wf f1)
      (VERSWF: versions_wf f0 vers)
      (BOTNONE: Memory.bot_none prom_tgt)
      (MSGSWF: wf_cell_msgs msgs_tgt)
      (SIM: sim_closed_memory f0 mem_src)

      ts_tgt ts_src
      (SIMTIME: sim_timestamp_exact f1 f1.(Mapping.ver) ts_src ts_tgt)
      (MAX: Time.le (Memory.max_ts loc mem_src) ts_src)
      (RESERVE: forall from_tgt to_tgt msg_tgt from_src to_src
                       (GET: Memory.get loc to_tgt prom_tgt = Some (from_tgt, msg_tgt))
                       (TS: Time.lt from_tgt ts_tgt)
                       (TO: sim_timestamp_exact (f0 loc) (f0 loc).(Mapping.ver) to_src to_tgt)
                       (FROM: sim_timestamp_exact (f0 loc) (f0 loc).(Mapping.ver) from_src from_tgt),
          (<<RESERVE: msg_tgt = Message.reserve>>) /\
          (<<TS: Time.lt to_tgt ts_tgt>>) /\
          (<<DISJOINT: forall from to msg (GET: Memory.get loc to mem_src = Some (from, msg)),
              Interval.disjoint (from_src, to_src) (from, to)>>))
      (SAME: forall to_tgt to_src
                    (TS: Time.lt to_tgt ts_tgt)
                    (MAP: sim_timestamp_exact (f0 loc) (f0 loc).(Mapping.ver) to_src to_tgt),
          sim_timestamp_exact f1 f1.(Mapping.ver) to_src to_tgt)
  :
    exists msgs_src,
      (<<FORALL: List.Forall2
                   (fun '(from_src, to_src, msg_src) '(from_tgt, to_tgt, msg_tgt) =>
                      (<<FROM: sim_timestamp_exact f1 f1.(Mapping.ver) from_src from_tgt>>) /\
                      (<<TO: sim_timestamp_exact f1 f1.(Mapping.ver) to_src to_tgt>>) /\
                      (<<MESSAGE: sim_message_max flag_new loc to_src f0 (vers loc to_tgt) msg_src msg_tgt>>))
                   msgs_src msgs_tgt>>) /\
      (<<DISJOINT: List.Forall
                     (fun '(from, to, msg) => (__guard__((<<MAX: Time.le (Memory.max_ts loc mem_src) from>>) \/ (<<RESERVE: msg = Message.reserve>>) /\ (<<DISJOINT: forall to2 from2 msg2 (GET: Memory.get loc to2 mem_src = Some (from2, msg2)), Interval.disjoint (from, to) (from2, to2)>>))) /\ (<<TS: Time.lt from to>>) /\ (<<MSGTO: Memory.message_to msg loc to>>) /\ (<<WF: Message.wf msg>>) /\ (<<CLOSED: semi_closed_message msg mem_src loc to>>)) msgs_src>>) /\
      (<<MSGSWF: wf_cell_msgs msgs_src>>)
.
Proof.
  pose proof mapping_latest_wf_loc as VERWF.
  revert MSGS MSGSWF. induction msgs_tgt; i.
  { exists []. splits.
    { econs. }
    { econs. }
    { red. splits; econs. }
  }
  des. destruct a as [[from_tgt to_tgt] msg_tgt].
  hexploit MSGS.
  { left. eauto. }
  intros GETTGT. hexploit sim_promises_get; eauto. i. des.
  hexploit sim_timestamp_exact_mon_exists; [eapply FROM|..]; eauto. i. des.
  hexploit sim_timestamp_exact_mon_exists; [eapply TO|..]; eauto. i. des.
  hexploit (@sim_message_max_exists flag_new loc ts_src0 f0 (vers loc to_tgt) msg_tgt); eauto.
  { i. hexploit VERS; eauto. i. des. esplits; eauto.
    exploit VERSWF. rewrite VER. ss.
  }
  i. des. red in MSGSWF. des. inv DISJOINT. inv MSGSWF0.
  hexploit IHmsgs_tgt; eauto.
  { i. eapply MSGS. right. auto. }
  { red. splits; auto. }
  i. destruct H1 as [MSGWF TIMEWF]. guardH TIMEWF.
  des.
  assert (FROMTO: Time.lt ts_src1 ts_src0).
  { eapply sim_timestamp_exact_lt; eauto.
    hexploit memory_get_ts_strong; eauto. i. des; clarify.
    rewrite BOTNONE in GETTGT. ss.
  }
  exists ((ts_src1, ts_src0, msg_src)::msgs_src). splits.
  { econs; eauto. }
  { econs; eauto. splits.
    { destruct (Time.le_lt_dec ts_tgt from_tgt).
      { left. transitivity ts_src; auto. eapply sim_timestamp_exact_le; eauto. }
      { right. hexploit RESERVE; eauto. i. des. subst.
        hexploit (@SAME to_tgt to_src); eauto. i.
        eapply sim_timestamp_exact_inject in SIM1; eauto. subst.
        hexploit (@SAME from_tgt from_src); eauto. i.
        eapply sim_timestamp_exact_inject in SIM0; eauto. subst.
        splits.
        { inv MAX0; ss. }
        { i. eauto. }
      }
    }
    { auto. }
    { eapply sim_message_max_msg_to; eauto. }
    { eapply sim_message_max_msg_wf; eauto. }
    { eapply sim_closed_memory_sim_message; eauto. }
  }
  { red in MSGSWF. des. red. splits.
    { econs; eauto.
      eapply List.Forall_forall. intros [[from_src0 to_src0] msg_src0] IN.
      eapply list_Forall2_in2 in IN; eauto. des.
      destruct b as [[from_tgt0 to_tgt0] msg_tgt0]. des.
      eapply List.Forall_forall in HD; eauto. ss.
      eapply sim_timestamp_exact_le; eauto.
    }
    { econs; eauto. splits; auto.
      eapply sim_message_max_msg_wf; eauto.
    }
  }
Qed.

Lemma messages_times_exists (msgs: list (Time.t * Time.t * Message.t)) (f0: Mapping.t) ts
      (MAPWF: Mapping.wf f0)
  :
    exists (f1: Mapping.t),
      (<<MAPWF: Mapping.wf f1>>) /\
      (<<MAPLE: Mapping.le_strong f0 f1>>) /\
      (<<CLOSEDIF: forall to (CLOSED: Mapping.closed f1 f1.(Mapping.ver) to),
          (<<CLOSED: Mapping.closed f0 f0.(Mapping.ver) to>>) \/
          (exists from val released, (<<IN: List.In (from, to, Message.concrete val released) msgs>>)) \/
          (<<TS: to = ts>>)>>) /\
      (<<CLOSED: List.Forall (fun '(from_src, to_src, msg_src) =>
                                forall val released (MSG: msg_src = Message.concrete val released),
                                  Mapping.closed f1 f1.(Mapping.ver) to_src) msgs>>) /\
      (<<CLOSEDTS: Mapping.closed f1 f1.(Mapping.ver) ts>>)
.
Proof.
  hexploit (@mapping_update_times f0 (fun to => to = ts \/ exists from val released, List.In (from, to, Message.concrete val released) msgs)).
  { eauto. }
  { induction msgs.
    { exists [ts]. i. des; ss; auto. }
    { des. destruct a as [[from to] msg]. destruct msg.
      { exists (to::l). i. ss. des; clarify.
        { right. eapply IHmsgs. left. auto. }
        { auto. }
        { right. eapply IHmsgs. right. eauto. }
      }
      { exists l. i. eapply IHmsgs. ss. des; clarify; eauto. }
      { exists l. i. eapply IHmsgs. ss. des; clarify; eauto. }
    }
  }
  i. des. exists f1. splits; eauto.
  { i. eapply TIMES in CLOSED. des; auto.
    right. esplits; eauto.
  }
  { eapply List.Forall_forall. intros [[from to] msg] IN. i. subst.
    eapply TIMES. right. esplits; eauto.
  }
  { eapply TIMES. right. left. auto. }
Qed.

Lemma mapped_msgs_complete f0 f1 msgs_src msgs_tgt loc vers flag_new
      (WF1: Mapping.wf f1)
      (FORALL: List.Forall2
                 (fun '(from_src, to_src, msg_src) '(from_tgt, to_tgt, msg_tgt) =>
                    (<<FROM: sim_timestamp_exact f1 f1.(Mapping.ver) from_src from_tgt>>) /\
                    (<<TO: sim_timestamp_exact f1 f1.(Mapping.ver) to_src to_tgt>>) /\
                    (<<MESSAGE: sim_message_max flag_new loc to_src f0 (vers loc to_tgt) msg_src msg_tgt>>))
                 msgs_src msgs_tgt)
      (CLOSED: List.Forall (fun '(from_src, to_src, msg_src) =>
                              forall val released (MSG: msg_src = Message.concrete val released),
                                Mapping.closed f1 f1.(Mapping.ver) to_src) msgs_src)
  :
    forall to_tgt from_tgt msg_tgt
           (RESERVE: msg_tgt <> Message.reserve)
           (GETTGT: List.In (from_tgt, to_tgt, msg_tgt) msgs_tgt),
    exists to_src from_src msg_src,
      (<<TO: sim_timestamp_exact f1 f1.(Mapping.ver) to_src to_tgt>>) /\
      (<<MSG: sim_message false loc f0 (vers loc to_tgt) msg_src msg_tgt>>) /\
      (<<CLOSED: forall val released (MSG: msg_tgt = Message.concrete val released), Mapping.closed f1 f1.(Mapping.ver) to_src>>) /\
      (<<IN: List.In (from_src, to_src, msg_src) msgs_src>>).
Proof.
  i. eapply list_Forall2_in in GETTGT; eauto. des.
  destruct a as [[from_src to_src] msg_src]. des. esplits; eauto.
  { eapply sim_message_flag_mon. eapply sim_message_max_sim; eauto. }
  { i. subst. eapply List.Forall_forall in CLOSED; eauto. ss.
    inv MESSAGE; eauto.
  }
Qed.

Lemma mapped_msgs_sound f0 f1 msgs_src msgs_tgt loc vers flag_new
      (WF1: Mapping.wf f1)
      (FORALL: List.Forall2
                 (fun '(from_src, to_src, msg_src) '(from_tgt, to_tgt, msg_tgt) =>
                    (<<FROM: sim_timestamp_exact f1 f1.(Mapping.ver) from_src from_tgt>>) /\
                    (<<TO: sim_timestamp_exact f1 f1.(Mapping.ver) to_src to_tgt>>) /\
                    (<<MESSAGE: sim_message_max flag_new loc to_src f0 (vers loc to_tgt) msg_src msg_tgt>>))
                 msgs_src msgs_tgt)
  :
    forall to_src from_src msg_src
           (IN: List.In (from_src, to_src, msg_src) msgs_src),
    exists to_tgt from_tgt msg_tgt,
      (<<TO: sim_timestamp_exact f1 f1.(Mapping.ver) to_src to_tgt>>) /\
      (<<FROM: sim_timestamp_exact f1 f1.(Mapping.ver) from_src from_tgt>>) /\
      (<<GET: List.In (from_tgt, to_tgt, msg_tgt) msgs_tgt>>).
Proof.
  i. eapply list_Forall2_in2 in IN; eauto. des.
  destruct b as [[from_tgt to_tgt] msg_tgt]. des. esplits; eauto.
Qed.

Lemma mapped_msgs_complete_promise f0 f1 msgs_src msgs_tgt loc vers flag_new
      (WF1: Mapping.wf f1)
      (FORALL: List.Forall2
                 (fun '(from_src, to_src, msg_src) '(from_tgt, to_tgt, msg_tgt) =>
                    (<<FROM: sim_timestamp_exact f1 f1.(Mapping.ver) from_src from_tgt>>) /\
                    (<<TO: sim_timestamp_exact f1 f1.(Mapping.ver) to_src to_tgt>>) /\
                    (<<MESSAGE: sim_message_max flag_new loc to_src f0 (vers loc to_tgt) msg_src msg_tgt>>))
                 msgs_src msgs_tgt)
      (CLOSED: List.Forall (fun '(from_src, to_src, msg_src) =>
                              forall val released (MSG: msg_src = Message.concrete val released),
                                Mapping.closed f1 f1.(Mapping.ver) to_src) msgs_src)
  :
    forall to_tgt from_tgt msg_tgt
           (GETTGT: List.In (from_tgt, to_tgt, msg_tgt) msgs_tgt),
    exists to_src from_src msg_src,
      (<<TO: sim_timestamp_exact f1 f1.(Mapping.ver) to_src to_tgt>>) /\
      (<<MSG: sim_message_max flag_new loc to_src f0 (vers loc to_tgt) msg_src msg_tgt>>) /\
      (<<CLOSED: forall val released (MSG: msg_tgt = Message.concrete val released), Mapping.closed f1 f1.(Mapping.ver) to_src>>) /\
      (<<IN: List.In (from_src, to_src, msg_src) msgs_src>>).
Proof.
  i. eapply list_Forall2_in in GETTGT; eauto. des.
  destruct a as [[from_src to_src] msg_src]. des. esplits; eauto.
  eapply List.Forall_forall in CLOSED; eauto. ss.
  inv MESSAGE; eauto.
Qed.

Lemma mapped_msgs_sound_promise f0 f1 msgs_src msgs_tgt loc vers flag_new
      (WF1: Mapping.wf f1)
      (FORALL: List.Forall2
                 (fun '(from_src, to_src, msg_src) '(from_tgt, to_tgt, msg_tgt) =>
                    (<<FROM: sim_timestamp_exact f1 f1.(Mapping.ver) from_src from_tgt>>) /\
                    (<<TO: sim_timestamp_exact f1 f1.(Mapping.ver) to_src to_tgt>>) /\
                    (<<MESSAGE: sim_message_max flag_new loc to_src f0 (vers loc to_tgt) msg_src msg_tgt>>))
                 msgs_src msgs_tgt)
      (CLOSED: List.Forall (fun '(from_src, to_src, msg_src) =>
                              forall val released (MSG: msg_src = Message.concrete val released),
                                Mapping.closed f1 f1.(Mapping.ver) to_src) msgs_src)
  :
    forall to_src from_src msg_src
           (IN: List.In (from_src, to_src, msg_src) msgs_src),
    exists to_tgt from_tgt msg_tgt,
      (<<TO: sim_timestamp_exact f1 f1.(Mapping.ver) to_src to_tgt>>) /\
      (<<FROM: sim_timestamp_exact f1 f1.(Mapping.ver) from_src from_tgt>>) /\
      (<<GET: List.In (from_tgt, to_tgt, msg_tgt) msgs_tgt>>).
Proof.
  i. eapply list_Forall2_in2 in IN; eauto. des.
  destruct b as [[from_tgt to_tgt] msg_tgt]. des. esplits; eauto.
Qed.

Lemma shited_mapping_space_future_memory srctm flag_src f0 vers mem_src mem_tgt
      loc f1 ts_src ts_tgt from val released
      (SIM: sim_memory srctm flag_src f0 vers mem_src mem_tgt)
      (MAPLE: Mapping.le (f0 loc) f1)
      (MAPWF0: Mapping.wfs f0)
      (MAPWF1: Mapping.wf f1)
      (PRESERVE: forall to_tgt to_src
                        (TS: Time.lt to_tgt ts_tgt)
                        (SIM: sim_timestamp_exact (f0 loc) (f0 loc).(Mapping.ver) to_src to_tgt),
          sim_timestamp_exact f1 f1.(Mapping.ver) to_src to_tgt)
      (SIMTS: sim_timestamp_exact f1 f1.(Mapping.ver) ts_src ts_tgt)
      (MAX: ts_src = Memory.max_ts loc mem_src)
      (GET: Memory.get loc ts_tgt mem_tgt = Some (from, Message.concrete val released))
  :
    space_future_memory
      (Messages.of_memory mem_tgt)
      f0 mem_src
      (fun loc0 => if Loc.eq_dec loc0 loc then f1 else f0 loc0) mem_src.
Proof.
  pose proof mapping_latest_wf_loc as VERWF.
  econs. i. inv MSGS. destruct (Loc.eq_dec loc0 loc); cycle 1.
  { eapply sim_timestamp_exact_inject in FROM0; eauto.
    eapply sim_timestamp_exact_inject in TO0; eauto.
  }
  subst. destruct (Time.le_lt_dec to_tgt ts_tgt).
  { inv l.
    2:{ inv H. clarify. }
    hexploit PRESERVE; [|eapply TO0|..]; eauto.
    i. eapply sim_timestamp_exact_inject in TO1; eauto.
    hexploit PRESERVE; [|eapply FROM0|..]; eauto.
    { eapply TimeFacts.le_lt_lt; eauto. eapply memory_get_ts_le; eauto. }
    i. eapply sim_timestamp_exact_inject in FROM1; eauto.
  }
  { hexploit memory_get_from_mon.
    { eapply GET. }
    { eapply GET0. }
    { eauto. }
    i. exfalso.
    hexploit sim_timestamp_exact_le; [| |eapply H|..]; eauto. i.
    inv COVERED. eapply Memory.max_ts_spec in GET1. des.
    inv ITV0. ss. inv ITV. ss. eapply Time.lt_strorder.
    eapply TimeFacts.le_lt_lt.
    { eapply TO. }
    eapply TimeFacts.le_lt_lt.
    { eapply MAX. }
    eapply TimeFacts.le_lt_lt.
    { eapply H0. }
    { eapply FROM2. }
  }
Qed.

Lemma added_memory_space_future_memory f loc msgs_src prom_tgt mem_src0 mem_src1 mem_tgt
      (MAPWF: Mapping.wfs f)
      (ADDED: added_memory loc msgs_src mem_src0 mem_src1)
      (SOUND: forall to_src from_src msg_src
                     (IN: List.In (from_src, to_src, msg_src) msgs_src),
          exists to_tgt from_tgt msg_tgt,
            (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src to_tgt>>) /\
            (<<FROM: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) from_src from_tgt>>) /\
            (<<GET: Memory.get loc to_tgt prom_tgt = Some (from_tgt, msg_tgt)>>))
      (MLE: Memory.le prom_tgt mem_tgt)
  :
    space_future_memory
      (unchangable mem_tgt prom_tgt)
      f mem_src0
      f mem_src1.
Proof.
  pose proof mapping_latest_wf_loc as VERWF.
  inv ADDED. econs. i.
  eapply sim_timestamp_exact_inject in FROM0; eauto.
  eapply sim_timestamp_exact_inject in TO0; eauto. subst. splits; auto.
  inv COVERED. econs; eauto.
  destruct (Loc.eq_dec loc0 loc); subst.
  2:{ rewrite OTHER in GET; eauto. }
  eapply SOUND0 in GET. des; eauto. exfalso.
  eapply SOUND in IN. des. inv MSGS.
  hexploit Memory.get_disjoint.
  { eapply GET0. }
  { eapply MLE. eapply GET. }
  i. des; clarify.
  hexploit sim_disjoint; [..|eapply H|]; eauto.
Qed.

Lemma sim_timemap_shifted (L0 L1: Loc.t -> Prop) f0 f1 tm_src tm_tgt
      loc ts_src ts_tgt
      (SIM: sim_timemap L0 f0 (Mapping.vers f0) tm_src tm_tgt)
      (MAPLE: Mapping.les f0 f1)
      (MAPWF0: Mapping.wfs f0)
      (MAPWF1: Mapping.wfs f1)
      (TS: sim_timestamp_exact (f1 loc) (f1 loc).(Mapping.ver) ts_src ts_tgt)
      (CLOSED: Mapping.closed (f1 loc) (f1 loc).(Mapping.ver) (tm_src loc))
      (TMSRC: Time.le (tm_src loc) ts_src)
      (TMTGT: Time.le ts_tgt (tm_tgt loc))
      (LOCS: forall loc0 (IN: L1 loc0), L0 loc0 \/ loc0 = loc)
  :
    sim_timemap L1 f1 (Mapping.vers f1) tm_src tm_tgt.
Proof.
  pose proof mapping_latest_wf_loc as VERWF.
  ii. eapply LOCS in LOC. des.
  { eapply sim_timestamp_mon_ver.
    { erewrite <- sim_timestamp_mon_mapping.
      { eauto. }
      { eauto. }
      { eauto. }
      { eauto. }
    }
    { eapply MAPLE. }
    { eauto. }
    { eauto. }
  }
  subst. red. esplits; eauto.
Qed.

Lemma sim_thread_flag_src_view
      f vers flag_src flag_tgt vs_src vs_tgt
      mem_src mem_tgt lc_src lc_tgt sc_src sc_tgt
      loc
      (SIM: sim_thread
              f vers flag_src flag_tgt vs_src vs_tgt
              mem_src mem_tgt lc_src lc_tgt sc_src sc_tgt)
      (LOCALSRC: Local.wf lc_src mem_src)
      (FLAG: flag_src loc = true)
  :
    (<<ACQRLX: lc_src.(Local.tview).(TView.acq).(View.rlx) loc = lc_src.(Local.tview).(TView.cur).(View.rlx) loc>>) /\
    (<<ACQPLN: lc_src.(Local.tview).(TView.acq).(View.pln) loc = lc_src.(Local.tview).(TView.cur).(View.rlx) loc>>).
Proof.
  inv SIM. inv LOCAL. ss.
  hexploit FLAGSRC; eauto. i.
  hexploit MAXTIMES; eauto. i.
  rewrite SRCTM in *. des.
  inv LOCALSRC. inv TVIEW_CLOSED. inv CUR. inv ACQ. ss. splits; auto.
  { eapply TimeFacts.antisym.
    { rewrite H0.
      specialize (RLX0 loc). des. eapply Memory.max_ts_spec in RLX0. des. eauto.
    }
    { eapply TVIEW_WF. }
  }
  { eapply TimeFacts.antisym.
    { rewrite H0.
      specialize (PLN0 loc). des. eapply Memory.max_ts_spec in PLN0. des. eauto.
    }
    { rewrite H. eapply TVIEW_WF. }
  }
Qed.

Lemma sim_view_shifted (L0 L1: Loc.t -> Prop) f0 f1 vw_src vw_tgt
      loc ts_src ts_tgt
      (SIM: sim_view L0 f0 (Mapping.vers f0) vw_src vw_tgt)
      (MAPLE: Mapping.les f0 f1)
      (MAPWF0: Mapping.wfs f0)
      (MAPWF1: Mapping.wfs f1)
      (TS: sim_timestamp_exact (f1 loc) (f1 loc).(Mapping.ver) ts_src ts_tgt)
      (CLOSED: Mapping.closed (f1 loc) (f1 loc).(Mapping.ver) (vw_src.(View.rlx) loc))
      (TMSRC: Time.le (vw_src.(View.rlx) loc) ts_src)
      (TMTGT: Time.le ts_tgt (vw_tgt.(View.pln) loc))
      (LOCS: forall loc0 (IN: L1 loc0), L0 loc0 \/ loc0 = loc)
      (VIEWWF: View.wf vw_tgt)
      (SRCMAX: vw_src.(View.rlx) loc = vw_src.(View.pln) loc)
  :
    sim_view L1 f1 (Mapping.vers f1) vw_src vw_tgt.
Proof.
  econs.
  { eapply sim_timemap_shifted; eauto.
    { eapply SIM. }
    { rewrite <- SRCMAX. auto. }
    { rewrite <- SRCMAX. auto. }
  }
  { eapply sim_timemap_shifted; eauto.
    { eapply SIM. }
    { etrans; eauto. eapply VIEWWF. }
  }
Qed.

Lemma sim_tview_shifted flag_src0 flag_src1 f0 f1 rel_vers tvw_src tvw_tgt
      loc ts_src ts_tgt
      (SIM: sim_tview f0 flag_src0 rel_vers tvw_src tvw_tgt)
      (MAPLE: Mapping.les f0 f1)
      (MAPWF0: Mapping.wfs f0)
      (MAPWF1: Mapping.wfs f1)
      (TS: sim_timestamp_exact (f1 loc) (f1 loc).(Mapping.ver) ts_src ts_tgt)
      (CLOSED: Mapping.closed (f1 loc) (f1 loc).(Mapping.ver) (tvw_src.(TView.cur).(View.rlx) loc))
      (TMSRC: Time.le (tvw_src.(TView.cur).(View.rlx) loc) ts_src)
      (TMTGT: Time.le ts_tgt (tvw_tgt.(TView.cur).(View.pln) loc))
      (LOCS: forall loc0 (IN: flag_src1 loc0 = false), flag_src0 loc0 = false \/ loc0 = loc)
      (VIEWWF: TView.wf tvw_tgt)
      (SRCMAX0: tvw_src.(TView.cur).(View.pln) loc = tvw_src.(TView.cur).(View.rlx) loc)
      (SRCMAX1: tvw_src.(TView.acq).(View.rlx) loc = tvw_src.(TView.cur).(View.rlx) loc)
      (SRCMAX2: tvw_src.(TView.acq).(View.pln) loc = tvw_src.(TView.cur).(View.rlx) loc)
  :
    sim_tview f1 flag_src1 rel_vers tvw_src tvw_tgt.
Proof.
  inv SIM. econs.
  { i. erewrite <- sim_view_mon_mapping; eauto. }
  { eapply sim_view_shifted; eauto. eapply VIEWWF. }
  { eapply sim_view_shifted; eauto.
    { rewrite SRCMAX1. auto. }
    { rewrite SRCMAX1. auto. }
    { etrans; eauto. eapply VIEWWF. }
    { eapply VIEWWF. }
    { rewrite SRCMAX1. auto. }
  }
  { i. eapply version_wf_mapping_mon; eauto. }
Qed.

Lemma sim_thread_deflag_match_aux
      f0 vers flag_src flag_tgt vs_src vs_tgt
      mem_src0 mem_tgt lc_src0 lc_tgt sc_src sc_tgt
      loc
      (SIM: sim_thread
              f0 vers flag_src flag_tgt vs_src vs_tgt
              mem_src0 mem_tgt lc_src0 lc_tgt sc_src sc_tgt)
      (CONSISTENT: Local.promise_consistent lc_tgt)
      (LOCALSRC: Local.wf lc_src0 mem_src0)
      (LOCALTGT: Local.wf lc_tgt mem_tgt)
      (MEMSRC: Memory.closed mem_src0)
      (MEMTGT: Memory.closed mem_tgt)
      (SCSRC: Memory.closed_timemap sc_src mem_src0)
      (SCTGT: Memory.closed_timemap sc_tgt mem_tgt)
      (WF: Mapping.wfs f0)
      (VERSWF: versions_wf f0 vers)
      (FLAG: flag_src loc = true)
      (VAL: option_rel Const.le (vs_tgt loc) (vs_src loc))
      lang st
  :
    exists lc_src1 mem_src1 f1,
      (<<STEPS: rtc (tau (@pred_step is_promise _))
                    (Thread.mk lang st lc_src0 sc_src mem_src0)
                    (Thread.mk _ st lc_src1 sc_src mem_src1)>>) /\
      (<<SIM: sim_thread
                f1 vers
                (fun loc0 => if Loc.eq_dec loc0 loc then false else flag_src loc0)
                (fun loc0 => if Loc.eq_dec loc0 loc then false else flag_tgt loc0)
                vs_src vs_tgt
                mem_src1 mem_tgt lc_src1 lc_tgt sc_src sc_tgt>>) /\
      (<<WF: Mapping.wfs f1>>) /\
      (<<MAPLE: Mapping.les f0 f1>>) /\
      (<<UNCH: forall loc0 (NEQ: loc0 <> loc), f1 loc0 = f0 loc0>>) /\
      (<<MAPFUTURE: map_future_memory f0 f1 mem_src1>>) /\
      (<<SPACE: space_future_memory (unchangable mem_tgt lc_tgt.(Local.promises)) f0 mem_src0 f1 mem_src1>>)
.
Proof.
  hexploit sim_thread_flag_src_view; eauto. i. des.
  inv SIM. hexploit (MAXSRC loc). intros MAXTSSRC.
  hexploit (MAXTGT loc). intros MAXTSTGT.
  destruct (vs_src loc) eqn:VSRC; cycle 1.
  { hexploit max_value_src_flag_none; eauto. i. clarify. }
  inv MAXTSSRC. hexploit MAX; eauto. i. des.
  destruct (vs_tgt loc) eqn:VTGT; ss.
  inv MAXTSTGT. hexploit MAX1; eauto. i. des.
  assert (TS: srctm loc = View.rlx (TView.cur tvw) loc).
  { inv LOCAL. auto. }
  hexploit sim_memory_top; eauto. intros TOP.
  hexploit (@shifted_mapping_exists (f0 loc) (View.pln (TView.cur tvw0) loc) (srctm loc)); eauto. i. des.
  hexploit (@wf_cell_msgs_exists (prom0 loc)). intros [msgs_tgt ?]. des.
  hexploit mapped_msgs_exists_aux.
  { inv LOCAL. eauto. }
  { eauto. }
  { i. eapply COMPLETE. eauto. }
  { eauto. }
  { eauto. }
  { eauto. }
  { eapply LOCALTGT. }
  { eauto. }
  { eauto. }
  { eapply TS0. }
  { rewrite MAXTIMES; auto. refl. }
  { i. inv MAX2. destruct (Time.le_lt_dec (View.pln (TView.cur tvw0) loc) to_tgt).
    { exfalso. inv l.
      { hexploit memory_get_from_mon.
        { eapply GET0. }
        { eapply LOCALTGT. eapply GET. }
        { eauto. }
        i. timetac.
      }
      { inv H. rewrite GET in NONE. ss. }
    }
    { destruct (classic (msg_tgt = Message.reserve)); cycle 1.
      { exfalso. exploit CONSISTENT; eauto. i. ss. eapply Time.lt_strorder.
        eapply TimeFacts.lt_le_lt.
        { eapply x. }
        { etrans.
          { left. eapply l. }
          { eapply LOCALTGT. }
        }
      }
      splits; auto. i. subst.
      exploit RESERVED; eauto. i. des.
      eapply sim_timestamp_exact_inject in TO; eauto. subst.
      eapply sim_timestamp_exact_inject in FROM; eauto. subst.
      eauto.
    }
  }
  { eauto. }
  i. des.
  inv MAX0. inv MAX2. ss.
  hexploit sim_memory_sound; eauto. i. des.
  { exfalso. eapply TOP in TO. eapply Time.lt_strorder.
    eapply TimeFacts.lt_le_lt.
    { eapply TO. }
    { inv LOCAL. rewrite SRCTM. rewrite FLAGSRC; auto. }
  }
  hexploit NONE1; eauto. i. subst.
  hexploit (messages_times_exists msgs_src f1); auto. i. des.
  eapply list_Forall2_impl in FORALL; cycle 1.
  { i. instantiate (1:= fun '(from_src, to_src, msg_src) '(from_tgt, to_tgt, msg_tgt) =>
                          (<<FROM: sim_timestamp_exact f2 f2.(Mapping.ver) from_src from_tgt>>) /\
                          (<<TO: sim_timestamp_exact f2 f2.(Mapping.ver) to_src to_tgt>>) /\
                          (<<MESSAGE: sim_message_max false loc to_src f0 (vers loc to_tgt) msg_src msg_tgt>>)).
    destruct a as [[from_src to_src] msg_src]. destruct b as [[from_tgt to_tgt] msg_tgt].
    des. splits; eauto.
    { eapply sim_timestamp_exact_mon_strong; [..|eauto]; eauto.  }
    { eapply sim_timestamp_exact_mon_strong; [..|eauto]; eauto.  }
  }
  pose proof (mapped_msgs_complete _ _ _ _ _ _ _ MAPWF FORALL CLOSED0) as COMPLETEMEM.
  pose proof (mapped_msgs_sound _ _ _ _ _ _ _ MAPWF FORALL) as SOUNDMEM.
  pose proof (mapped_msgs_complete_promise _ _ _ _ _ _ _ MAPWF FORALL) as COMPLETEPROM.
  pose proof (mapped_msgs_sound_promise _ _ _ _ _ _ _ MAPWF FORALL) as SOUNDPROM.
  set (f' := fun loc0 => if Loc.eq_dec loc0 loc then f2 else f0 loc0).
  assert (MAPSLE: Mapping.les f0 f').
  { unfold f'. ii. condtac; subst.
    { etrans; eauto. eapply Mapping.le_strong_le; eauto. }
    { refl. }
  }
  assert (MAPSWF: Mapping.wfs f').
  { unfold f'. ii. condtac; subst; eauto. }
  hexploit add_promises_latest.
  { eapply MSGSWF. }
  { eapply LOCALSRC. }
  { eapply MEMSRC. }
  { eauto. }
  i. des. inv LOCAL.
  hexploit added_memory_sim_memory; eauto.
  { rewrite TS. rewrite FLAGSRC; eauto. }
  {  hexploit sim_memory_get; eauto; ss. i. des.
     inv MSG; econs; eauto; econs.
  }
  { ss. }
  { i. eapply MAX0 in GETTGT; eauto.
    eapply COMPLETE in GETTGT. eapply COMPLETEMEM; eauto.
  }
  { i. eapply SOUNDMEM in IN. des. esplits; eauto.
    eapply LOCALTGT. eapply COMPLETE; eauto.
  }
  { etrans; eauto. eapply Mapping.le_strong_le; eauto. }
  { i. eapply sim_timestamp_exact_mon_strong; [|eauto|..]; eauto. }
  { eapply sim_timestamp_exact_mon_strong; [|eauto|..]; eauto. }
  { i. eapply CLOSEDIF in CLOSED1. des.
    { left. eapply CLOSED. auto. }
    { right. left. eauto. }
    { subst. right. right. esplits; eauto. }
  }
  i. destruct H as [MEM1 ?]. des.
  esplits.
  { eapply STEPS. }
  { econs.
    { instantiate (1:=f'). eapply sim_timemap_mon_latest; eauto. }
    { eauto. }
    { econs.
      { eapply sim_tview_shifted; eauto.
        { eapply sim_timestamp_exact_mon_strong; [..|eapply TS0]; eauto.
          unfold f'. des_ifs.
        }
        { unfold f'. des_ifs. rewrite <- SRCTM. auto. }
        { rewrite <- SRCTM. refl. }
        { refl. }
        { i. des_ifs; auto. }
        { eapply LOCALTGT. }
        { rewrite FLAGSRC; auto. }
      }
      { eapply added_memory_sim_promise_match; eauto.
        { i. eapply COMPLETE in GETTGT. eapply COMPLETEPROM in GETTGT; eauto. }
        { i. eapply SOUNDPROM in IN; eauto. des.
          esplits; eauto. eapply COMPLETE; eauto.
        }
        { etrans; eauto. eapply Mapping.le_strong_le; eauto. }
      }
      { eauto. }
      { i. des_ifs. eauto. }
      { eauto. }
    }
    { eapply promise_steps_max_values_src; eauto. }
    { eauto. }
    { eauto. }
    { red in FIN. des.
      hexploit (list_filter_exists (fun loc0 => loc0 <> loc) dom). i. des.
      exists l'. splits. i. etrans; [|eapply COMPLETE0]. condtac; subst.
      { split; i; des; ss. }
      { split; i.
        { split; auto. eapply DOM; auto. }
        { des. eapply DOM; eauto. }
      }
    }
    { eauto. }
    { eauto. }
    { i. des_ifs. rewrite MAXTIMES; auto.
      eapply unchanged_loc_max_ts.
      { eapply added_memory_unchanged_loc; eauto. }
      { eapply MEMSRC. }
    }
    { ss. ii. unfold f'. des_ifs. hexploit (RESERVED loc0); eauto.
      i. des. esplits; eauto. i.
      inv MEM0. rewrite OTHER in GETSRC; eauto.
    }
    { unfold f'. ii. ss. inv PROMISES.
      destruct (Loc.eq_dec loc0 loc); subst.
      { eapply SOUND in GETSRC. des.
        { hexploit sim_promises_none; eauto. i. rewrite GET1 in H. ss. }
        { eapply list_Forall2_in2 in FORALL; eauto. des.
          destruct b as [[from_tgt to_tgt] msg_tgt]. des.
          eapply COMPLETE in IN0. eapply LOCALTGT in IN0.
          esplits; eauto. inv MESSAGE; ss.
        }
      }
      { erewrite OTHER in GETSRC; eauto. }
    }
  }
  { eauto. }
  { eauto. }
  { i. unfold f'. des_ifs. }
  { eauto. }
  { eapply space_future_memory_trans.
    { eapply space_future_memory_mon_msgs.
      { eapply shited_mapping_space_future_memory.
        { eauto. }
        { etrans; eauto. eapply Mapping.le_strong_le; eauto. }
        { eauto. }
        { eauto. }
        { i. eapply sim_timestamp_exact_mon_strong; [..|eapply SAME]; eauto. }
        { eapply sim_timestamp_exact_mon_strong; [..|eauto]; eauto. }
        { eauto. }
        { eauto. }
      }
      { eapply unchangable_messages_of_memory. }
    }
    { eapply added_memory_space_future_memory; eauto.
      { i. eapply SOUNDPROM in IN; eauto. des. esplits; eauto.
        { des_ifs; eauto. }
        { des_ifs; eauto. }
        { eapply COMPLETE; eauto. }
      }
      { eapply LOCALTGT. }
    }
    { eauto. }
    { refl. }
    { eauto. }
    { eauto. }
    { eauto. }
  }
Qed.

Lemma sim_thread_deflag_unmatch_aux
      f0 vers flag_src flag_tgt vs_src vs_tgt
      mem_src0 mem_tgt lc_src0 lc_tgt sc_src sc_tgt
      loc
      (SIM: sim_thread
              f0 vers flag_src flag_tgt vs_src vs_tgt
              mem_src0 mem_tgt lc_src0 lc_tgt sc_src sc_tgt)
      (CONSISTENT: Local.promise_consistent lc_tgt)
      (LOCALSRC: Local.wf lc_src0 mem_src0)
      (LOCALTGT: Local.wf lc_tgt mem_tgt)
      (MEMSRC: Memory.closed mem_src0)
      (MEMTGT: Memory.closed mem_tgt)
      (SCSRC: Memory.closed_timemap sc_src mem_src0)
      (SCTGT: Memory.closed_timemap sc_tgt mem_tgt)
      (WF: Mapping.wfs f0)
      (VERSWF: versions_wf f0 vers)
      (FLAG: flag_src loc = true)
      lang st
  :
    exists lc_src1 mem_src1 f1 flag,
      (<<STEPS: rtc (tau (@pred_step is_promise _))
                    (Thread.mk lang st lc_src0 sc_src mem_src0)
                    (Thread.mk _ st lc_src1 sc_src mem_src1)>>) /\
      (<<SIM: sim_thread
                f1 vers
                (fun loc0 => if Loc.eq_dec loc0 loc then false else flag_src loc0)
                (fun loc0 => if Loc.eq_dec loc0 loc then flag else flag_tgt loc0)
                vs_src vs_tgt
                mem_src1 mem_tgt lc_src1 lc_tgt sc_src sc_tgt>>) /\
      (<<WF: Mapping.wfs f1>>) /\
      (<<MAPLE: Mapping.les f0 f1>>) /\
      (<<UNCH: forall loc0 (NEQ: loc0 <> loc), f1 loc0 = f0 loc0>>) /\
      (<<MAPFUTURE: map_future_memory f0 f1 mem_src1>>) /\
      (<<SPACE: space_future_memory (unchangable mem_tgt lc_tgt.(Local.promises)) f0 mem_src0 f1 mem_src1>>)
.
Proof.
  hexploit sim_thread_flag_src_view; eauto. i. des.
  inv SIM. hexploit (MAXSRC loc). intros MAXTSSRC.
  hexploit (MAXTGT loc). intros MAXTSTGT.
  destruct (vs_src loc) eqn:VSRC; cycle 1.
  { hexploit max_value_src_flag_none; eauto. i. clarify. }
  inv MAXTSSRC. hexploit MAX; eauto. i. des.
  destruct (vs_tgt loc) eqn:VTGT; ss.
  2:{ exfalso. specialize (PERM loc). rewrite VSRC in PERM. rewrite VTGT in PERM. ss. }
  inv MAXTSTGT. hexploit MAX1; eauto. i. des.
  assert (TS: srctm loc = View.rlx (TView.cur tvw) loc).
  { inv LOCAL. auto. }
  hexploit sim_memory_top; eauto. intros TOP.
  set (max1 := Time.incr (Memory.max_ts loc mem_src0)).
  assert (TOP1: top_time max1 (f0 loc)).
  { unfold max1. eapply top_time_mon; eauto. rewrite MAXTIMES; auto.
    left. eapply Time.incr_spec.
  }
  hexploit Memory.add_exists_max_ts.
  { instantiate (1:=max1). eapply Time.incr_spec. }
  { instantiate (1:=Message.concrete t0 None). econs; ss. }
  intros [mem_src1 ADDMEM].
  hexploit Memory.add_exists_le.
  { eapply LOCALSRC. }
  { eauto. }
  intros [prom_src1 ADDPROM].
  hexploit add_src_sim_memory_flag_up; eauto.
  { rewrite <- MAXTIMES; auto. }
  { rewrite <- MAXTIMES; auto. refl. }
  { i. clarify. }
  intros SIMMEM1.
  assert (PROMISESTEP: Local.promise_step (Local.mk tvw prom) mem_src0 loc (Memory.max_ts loc mem_src0) max1 (Message.concrete t0 None) (Local.mk tvw prom_src1) mem_src1 Memory.op_kind_add).
  { econs; eauto. econs; eauto.
    { econs; eauto. eapply Time.bot_spec. }
    { i. dup GET. eapply Memory.max_ts_spec in GET. des.
      eapply memory_get_ts_le in GET0. eapply Time.lt_strorder.
      eapply TimeFacts.le_lt_lt.
      { eapply MAX3. }
      eapply TimeFacts.lt_le_lt.
      { eapply Time.incr_spec. }
      { eapply GET0. }
    }
  }
  hexploit Local.promise_step_future; eauto. i. des.
  hexploit (@shifted_mapping_exists (f0 loc) (View.pln (TView.cur tvw0) loc) max1); eauto.
  i. des.
  hexploit (@wf_cell_msgs_exists (prom0 loc)). intros [msgs_tgt ?]. des.
  hexploit mapped_msgs_exists_aux.
  { inv LOCAL. eauto. }
  { eauto. }
  { i. eapply COMPLETE. eauto. }
  { eauto. }
  { eauto. }
  { eauto. }
  { eapply LOCALTGT. }
  { eauto. }
  { eapply sim_closed_memory_future.
    { eauto. }
    { eapply Memory.future_future_weak; eauto. }
  }
  { eapply TS0. }
  { erewrite le_add_max_ts; eauto.
    { refl. }
    { left. eapply Time.incr_spec. }
  }
  { i. inv MAX2. destruct (Time.le_lt_dec (View.pln (TView.cur tvw0) loc) to_tgt).
    { exfalso. inv l.
      { hexploit memory_get_from_mon.
        { eapply GET0. }
        { eapply LOCALTGT. eapply GET. }
        { eauto. }
        i. timetac.
      }
      { inv H. rewrite GET in NONE. ss. }
    }
    { destruct (classic (msg_tgt = Message.reserve)); cycle 1.
      { exfalso. exploit CONSISTENT; eauto. i. ss. eapply Time.lt_strorder.
        eapply TimeFacts.lt_le_lt.
        { eapply x. }
        { etrans.
          { left. eapply l. }
          { eapply LOCALTGT. }
        }
      }
      splits; auto. i. subst.
      exploit RESERVED; eauto. i. des.
      eapply sim_timestamp_exact_inject in TO; eauto. subst.
      eapply sim_timestamp_exact_inject in FROM; eauto. subst.
      erewrite Memory.add_o in GET1; eauto. des_ifs.
      { ss. des; subst. eapply interval_le_disjoint. rewrite <- MAXTIMES; auto.
        eapply TOP in TO0. left. auto.
      }
      { eapply DISJOINT; eauto. }
    }
  }
  { eauto. }
  i. des.
  inv MAX0. inv MAX2. ss.
  hexploit sim_memory_sound; [eapply MEM|..]; eauto. i. des.
  { exfalso. eapply TOP in TO. eapply Time.lt_strorder.
    eapply TimeFacts.lt_le_lt.
    { eapply TO. }
    { inv LOCAL. rewrite SRCTM. rewrite FLAGSRC; auto. }
  }
  hexploit NONE1; eauto. i. subst.
  hexploit (messages_times_exists ((srctm loc, max1, Message.concrete t0 None)::msgs_src) f1 (srctm loc)); auto. i. des.
  eapply list_Forall2_impl in FORALL; cycle 1.
  { i. instantiate (1:= fun '(from_src, to_src, msg_src) '(from_tgt, to_tgt, msg_tgt) =>
                          (<<FROM: sim_timestamp_exact f2 f2.(Mapping.ver) from_src from_tgt>>) /\
                          (<<TO: sim_timestamp_exact f2 f2.(Mapping.ver) to_src to_tgt>>) /\
                          (<<MESSAGE: sim_message_max true loc to_src f0 (vers loc to_tgt) msg_src msg_tgt>>)).
    destruct a as [[from_src to_src] msg_src]. destruct b as [[from_tgt to_tgt] msg_tgt].
    des. splits; eauto.
    { eapply sim_timestamp_exact_mon_strong; [..|eauto]; eauto.  }
    { eapply sim_timestamp_exact_mon_strong; [..|eauto]; eauto.  }
  }
  inv CLOSED0. hexploit H1; eauto. intros CLOSEDMAX. clear H1. rename H2 into CLOSED0.
  pose proof (mapped_msgs_complete _ _ _ _ _ _ _ MAPWF FORALL CLOSED0) as COMPLETEMEM.
  pose proof (mapped_msgs_sound _ _ _ _ _ _ _ MAPWF FORALL) as SOUNDMEM.
  pose proof (mapped_msgs_complete_promise _ _ _ _ _ _ _ MAPWF FORALL) as COMPLETEPROM.
  pose proof (mapped_msgs_sound_promise _ _ _ _ _ _ _ MAPWF FORALL) as SOUNDPROM.
  set (f' := fun loc0 => if Loc.eq_dec loc0 loc then f2 else f0 loc0).
  assert (MAPSLE: Mapping.les f0 f').
  { unfold f'. ii. condtac; subst.
    { etrans; eauto. eapply Mapping.le_strong_le; eauto. }
    { refl. }
  }
  assert (MAPSWF: Mapping.wfs f').
  { unfold f'. ii. condtac; subst; eauto. }
  hexploit add_promises_latest.
  { eapply MSGSWF. }
  { eapply WF2. }
  { eapply CLOSED2. }
  { eauto.  }
  i. des. inv LOCAL.
  hexploit added_memory_sim_memory; eauto.
  { eapply sim_closed_memory_future; eauto. eapply Memory.future_future_weak; eauto. }
  { ss. des_ifs. eapply Memory.add_get0; eauto. }
  { hexploit sim_memory_get; eauto; ss. i. des. inv MSG.
    { econs; eauto.
      { refl. }
      { econs. }
    }
    { econs; eauto.
      { refl. }
      { econs. }
    }
  }
  { ss. }
  { i. eapply MAX0 in GETTGT; eauto.
    eapply COMPLETE in GETTGT. eapply COMPLETEMEM; eauto.
  }
  { i. eapply SOUNDMEM in IN. des. esplits; eauto.
    eapply LOCALTGT. eapply COMPLETE; eauto.
  }
  { etrans; eauto. eapply Mapping.le_strong_le; eauto. }
  { i. eapply sim_timestamp_exact_mon_strong; [|eauto|..]; eauto. }
  { ss. des_ifs. eapply sim_timestamp_exact_mon_strong; [|eauto|..]; eauto. }
  { ss. des_ifs. }
  { i. eapply CLOSEDIF in CLOSED1. des.
    { left. eapply CLOSED. auto. }
    { ss. des; clarify.
      { right. right. left. esplits; eauto. des_ifs. }
      { right. left. eauto. }
    }
    { subst. right. right. right. esplits; eauto.
      rewrite TS. rewrite FLAGSRC; eauto. eapply Memory.add_get1; eauto.
    }
  }
  i. destruct H as [MEM1 ?]. des.
  esplits.
  { econs 2.
    { econs.
      { econs.
        { econs. econs 1. econs 1; eauto. }
        { ss. }
      }
      { ss. }
    }
    eapply STEPS.
  }
  { econs.
    { instantiate (1:=f'). eapply sim_timemap_mon_latest; eauto. }
    { eapply sim_memory_change_no_flag.
      { eauto. }
      { instantiate (1:=srctm). i. des_ifs. }
    }
    { econs.
      { eapply sim_tview_shifted; eauto.
        { eapply sim_timestamp_exact_mon_strong; [..|eapply TS0]; eauto.
          unfold f'. des_ifs.
        }
        { unfold f'. des_ifs. rewrite <- SRCTM. auto. }
        { rewrite <- SRCTM. rewrite MAXTIMES; auto. left. eapply Time.incr_spec. }
        { refl. }
        { i. des_ifs; auto. }
        { eapply LOCALTGT. }
        { rewrite FLAGSRC; auto. }
      }
      { eapply added_memory_sim_promise_unmatch; eauto.
        { eapply added_memory_cons; eauto. }
        { i. eapply COMPLETE in GETTGT. eapply COMPLETEPROM in GETTGT; eauto.
          des. esplits; eauto. right. eauto.
        }
        { i. ss. des.
          { clarify. esplits.
            { eapply sim_timestamp_exact_mon_strong; [..|eauto]; eauto. }
            { right. splits; ss. rewrite MAXTIMES; auto. eapply Time.incr_spec. }
          }
          { eapply SOUNDPROM in IN; eauto. des.
            esplits; eauto. left. esplits; eauto. eapply COMPLETE; eauto.
          }
        }
        { etrans; eauto. eapply Mapping.le_strong_le; eauto. }
      }
      { eauto. }
      { i. des_ifs. eauto. }
      { eauto. }
    }
    { eapply promise_steps_max_values_src; eauto. eapply promise_max_values_src; eauto. }
    { eauto. }
    { eauto. }
    { red in FIN. des.
      hexploit (list_filter_exists (fun loc0 => loc0 <> loc) dom). i. des.
      exists l'. splits. i. etrans; [|eapply COMPLETE0]. condtac; subst.
      { split; i; des; ss. }
      { split; i.
        { split; auto. eapply DOM; auto. }
        { des. eapply DOM; eauto. }
      }
    }
    { eauto. }
    { eauto. }
    { i. des_ifs. rewrite MAXTIMES; auto.
      eapply unchanged_loc_max_ts.
      { eapply added_memory_unchanged_loc; eauto. eapply added_memory_cons; eauto. }
      { eapply MEMSRC. }
    }
    { ss. ii. unfold f'. des_ifs. hexploit (RESERVED loc0); eauto.
      i. des. esplits; eauto. i.
      inv MEM0. rewrite OTHER in GETSRC; eauto.
      erewrite Memory.add_o in GETSRC; eauto. des_ifs; eauto.
      ss. des; clarify.
    }
    { unfold f'. ii. ss. inv PROMISES.
      destruct (Loc.eq_dec loc0 loc); subst.
      { eapply SOUND in GETSRC. des.
        { erewrite Memory.add_o in GET1; eauto. des_ifs.
          { ss. des; clarify. esplits.
            { eapply sim_timestamp_exact_mon_strong; [..|eauto]; eauto. }
            { eauto. }
            { ss. }
          }
          { hexploit sim_promises_none; eauto. i. rewrite GET1 in H. ss. }
        }
        { eapply list_Forall2_in2 in FORALL; eauto. des.
          destruct b as [[from_tgt to_tgt] msg_tgt]. des.
          eapply COMPLETE in IN0. eapply LOCALTGT in IN0.
          esplits; eauto. inv MESSAGE; ss.
        }
      }
      { erewrite OTHER in GETSRC; eauto.
        erewrite Memory.add_o in GETSRC; eauto. des_ifs; eauto.
        ss. des; clarify.
      }
    }
  }
  { eauto. }
  { eauto. }
  { i. unfold f'. des_ifs. }
  { eauto. }
  { eapply space_future_memory_trans.
    { eapply space_future_memory_mon_msgs.
      { eapply space_future_memory_trans.
        { eapply add_src_sim_memory_space_future_aux; eauto.
          { rewrite <- MAXTIMES; auto. }
          { i. rewrite <- MAXTIMES; auto. refl. }
        }
        { eapply shited_mapping_space_future_memory.
          { eauto. }
          { etrans; eauto. eapply Mapping.le_strong_le; eauto. }
          { eauto. }
          { eauto. }
          { i. eapply sim_timestamp_exact_mon_strong; [..|eapply SAME]; eauto. }
          { eapply sim_timestamp_exact_mon_strong; [..|eauto]; eauto. }
          { erewrite le_add_max_ts; eauto. left. eapply Time.incr_spec. }
          { eauto. }
        }
        { refl. }
        { eauto. }
        { eauto. }
        { eauto. }
        { eauto. }
      }
      { eapply unchangable_messages_of_memory. }
    }
    { eapply added_memory_space_future_memory; eauto.
      { i. eapply SOUNDPROM in IN; eauto. des. esplits; eauto.
        { des_ifs; eauto. }
        { des_ifs; eauto. }
        { eapply COMPLETE; eauto. }
      }
      { eapply LOCALTGT. }
    }
    { eauto. }
    { refl. }
    { eauto. }
    { eauto. }
    { eauto. }
  }
Qed.

Lemma sim_thread_deflag_match
      f0 vers flag_src flag_tgt vs_src vs_tgt
      mem_src0 mem_tgt lc_src0 lc_tgt sc_src sc_tgt
      loc
      (SIM: sim_thread
              f0 vers flag_src flag_tgt vs_src vs_tgt
              mem_src0 mem_tgt lc_src0 lc_tgt sc_src sc_tgt)
      (CONSISTENT: Local.promise_consistent lc_tgt)
      (LOCALSRC: Local.wf lc_src0 mem_src0)
      (LOCALTGT: Local.wf lc_tgt mem_tgt)
      (MEMSRC: Memory.closed mem_src0)
      (MEMTGT: Memory.closed mem_tgt)
      (SCSRC: Memory.closed_timemap sc_src mem_src0)
      (SCTGT: Memory.closed_timemap sc_tgt mem_tgt)
      (WF: Mapping.wfs f0)
      (VERSWF: versions_wf f0 vers)
      (FLAG: flag_src loc = false -> flag_tgt loc = false)
      (VAL: option_rel Const.le (vs_tgt loc) (vs_src loc) \/ flag_src loc = false)
      lang st
  :
    exists lc_src1 mem_src1 f1,
      (<<STEPS: rtc (tau (@pred_step is_promise _))
                    (Thread.mk lang st lc_src0 sc_src mem_src0)
                    (Thread.mk _ st lc_src1 sc_src mem_src1)>>) /\
      (<<SIM: sim_thread
                f1 vers
                (fun loc0 => if Loc.eq_dec loc0 loc then false else flag_src loc0)
                (fun loc0 => if Loc.eq_dec loc0 loc then false else flag_tgt loc0)
                vs_src vs_tgt
                mem_src1 mem_tgt lc_src1 lc_tgt sc_src sc_tgt>>) /\
      (<<WF: Mapping.wfs f1>>) /\
      (<<MAPLE: Mapping.les f0 f1>>) /\
      (<<UNCH: forall loc0 (NEQ: loc0 <> loc), f1 loc0 = f0 loc0>>) /\
      (<<MAPFUTURE: map_future_memory f0 f1 mem_src1>>) /\
      (<<SPACE: space_future_memory (unchangable mem_tgt lc_tgt.(Local.promises)) f0 mem_src0 f1 mem_src1>>)
.
Proof.
  destruct (flag_src loc) eqn:EQ.
  { des; ss. eapply sim_thread_deflag_match_aux; eauto. }
  { esplits.
    { refl. }
    { replace (fun (loc0: Loc.t) => if LocSet.Facts.eq_dec loc0 loc then false else flag_src loc0) with flag_src.
      2:{ extensionality loc0. des_ifs. }
      replace (fun (loc0: Loc.t) => if LocSet.Facts.eq_dec loc0 loc then false else flag_tgt loc0) with flag_tgt.
      2:{ extensionality loc0. des_ifs. eauto. }
      eauto.
    }
    { eauto. }
    { refl. }
    { auto. }
    { eapply map_future_memory_refl. }
    { eapply space_future_memory_refl; eauto. refl. }
  }
Qed.

Lemma sim_thread_deflag_unmatch
      f0 vers flag_src flag_tgt vs_src vs_tgt
      mem_src0 mem_tgt lc_src0 lc_tgt sc_src sc_tgt
      loc
      (SIM: sim_thread
              f0 vers flag_src flag_tgt vs_src vs_tgt
              mem_src0 mem_tgt lc_src0 lc_tgt sc_src sc_tgt)
      (CONSISTENT: Local.promise_consistent lc_tgt)
      (LOCALSRC: Local.wf lc_src0 mem_src0)
      (LOCALTGT: Local.wf lc_tgt mem_tgt)
      (MEMSRC: Memory.closed mem_src0)
      (MEMTGT: Memory.closed mem_tgt)
      (SCSRC: Memory.closed_timemap sc_src mem_src0)
      (SCTGT: Memory.closed_timemap sc_tgt mem_tgt)
      (WF: Mapping.wfs f0)
      (VERSWF: versions_wf f0 vers)
      lang st
  :
    exists lc_src1 mem_src1 f1 flag,
      (<<STEPS: rtc (tau (@pred_step is_promise _))
                    (Thread.mk lang st lc_src0 sc_src mem_src0)
                    (Thread.mk _ st lc_src1 sc_src mem_src1)>>) /\
      (<<SIM: sim_thread
                f1 vers
                (fun loc0 => if Loc.eq_dec loc0 loc then false else flag_src loc0)
                (fun loc0 => if Loc.eq_dec loc0 loc then flag else flag_tgt loc0)
                vs_src vs_tgt
                mem_src1 mem_tgt lc_src1 lc_tgt sc_src sc_tgt>>) /\
      (<<WF: Mapping.wfs f1>>) /\
      (<<MAPLE: Mapping.les f0 f1>>) /\
      (<<UNCH: forall loc0 (NEQ: loc0 <> loc), f1 loc0 = f0 loc0>>) /\
      (<<MAPFUTURE: map_future_memory f0 f1 mem_src1>>) /\
      (<<SPACE: space_future_memory (unchangable mem_tgt lc_tgt.(Local.promises)) f0 mem_src0 f1 mem_src1>>)
.
Proof.
  destruct (flag_src loc) eqn:FLAG.
  { eapply sim_thread_deflag_unmatch_aux; eauto. }
  { esplits.
    { refl. }
    { instantiate (1:=flag_tgt loc).
      replace (fun (loc0: Loc.t) => if LocSet.Facts.eq_dec loc0 loc then false else flag_src loc0) with flag_src.
      2:{ extensionality loc0. des_ifs. }
      replace (fun (loc0: Loc.t) => if LocSet.Facts.eq_dec loc0 loc then flag_tgt loc else flag_tgt loc0) with flag_tgt.
      2:{ extensionality loc0. des_ifs. }
      eauto.
    }
    { eauto. }
    { refl. }
    { auto. }
    { eapply map_future_memory_refl. }
    { eapply space_future_memory_refl; eauto. refl. }
  }
Qed.

Lemma sim_thread_deflag_all_aux
      dom
  :
    forall
      f0 vers flag_src flag_tgt0 vs_src vs_tgt
      mem_src0 mem_tgt lc_src0 lc_tgt sc_src sc_tgt
      (D: Loc.t -> Prop)
      (SIM: sim_thread
              f0 vers flag_src flag_tgt0 vs_src vs_tgt
              mem_src0 mem_tgt lc_src0 lc_tgt sc_src sc_tgt)
      (CONSISTENT: Local.promise_consistent lc_tgt)
      (LOCALSRC: Local.wf lc_src0 mem_src0)
      (LOCALTGT: Local.wf lc_tgt mem_tgt)
      (MEMSRC: Memory.closed mem_src0)
      (MEMTGT: Memory.closed mem_tgt)
      (SCSRC: Memory.closed_timemap sc_src mem_src0)
      (SCTGT: Memory.closed_timemap sc_tgt mem_tgt)
      (WF: Mapping.wfs f0)
      (VERSWF: versions_wf f0 vers)
      (DEBT: forall loc, (<<DEBT: D loc>>) \/
                         ((<<FLAG: flag_src loc = false -> flag_tgt0 loc = false>>) /\
                          (<<VAL: option_rel Const.le (vs_tgt loc) (vs_src loc) \/ flag_src loc = false>>)))
      (FIN: forall loc (FLAG: flag_src loc = true), List.In loc dom)
      lang st,
    exists lc_src1 mem_src1 f1 flag_tgt1,
      (<<STEPS: rtc (tau (@pred_step is_promise _))
                    (Thread.mk lang st lc_src0 sc_src mem_src0)
                    (Thread.mk _ st lc_src1 sc_src mem_src1)>>) /\
      (<<SIM: sim_thread
                f1 vers
                (fun _ => false)
                flag_tgt1
                vs_src vs_tgt
                mem_src1 mem_tgt lc_src1 lc_tgt sc_src sc_tgt>>) /\
      (<<WF: Mapping.wfs f1>>) /\
      (<<MAPLE: Mapping.les f0 f1>>) /\
      (<<FLAG: forall loc, (<<DEBT: D loc>>) \/ (<<FLAG: flag_tgt1 loc = false>>)>>) /\
      (<<UNCH: forall loc (NIN: ~ List.In loc dom), f1 loc = f0 loc>>) /\
      (<<MAPFUTURE: map_future_memory f0 f1 mem_src1>>) /\
      (<<SPACE: space_future_memory (unchangable mem_tgt lc_tgt.(Local.promises)) f0 mem_src0 f1 mem_src1>>)
.
Proof.
  induction dom.
  { i. assert (FLAG: flag_src = fun _ => false).
    { extensionality loc. destruct (flag_src loc) eqn:FLAG; auto.
      hexploit (FIN loc); eauto. ss.
    }
    subst. esplits.
    { refl. }
    { eauto. }
    { auto. }
    { refl. }
    { i. hexploit DEBT; eauto. i. des; eauto. }
    { ss. }
    { eapply map_future_memory_refl. }
    { eapply space_future_memory_refl; eauto. refl. }
  }
  i.
  cut (exists lc_src1 mem_src1 f1 flag,
          (<<STEPS: rtc (tau (@pred_step is_promise _))
                        (Thread.mk lang st lc_src0 sc_src mem_src0)
                        (Thread.mk _ st lc_src1 sc_src mem_src1)>>) /\
          (<<SIM: sim_thread
                    f1 vers
                    (fun loc0 => if Loc.eq_dec loc0 a then false else flag_src loc0)
                    (fun loc0 => if Loc.eq_dec loc0 a then flag else flag_tgt0 loc0)
                    vs_src vs_tgt
                    mem_src1 mem_tgt lc_src1 lc_tgt sc_src sc_tgt>>) /\
          (<<WF: Mapping.wfs f1>>) /\
          (<<MAPLE: Mapping.les f0 f1>>) /\
          (<<FLAG: __guard__(flag = false \/ D a)>>) /\
          (<<UNCH: forall loc (NEQ: loc <> a), f1 loc = f0 loc>>) /\
          (<<MAPFUTURE: map_future_memory f0 f1 mem_src1>>) /\
          (<<SPACE: space_future_memory (unchangable mem_tgt lc_tgt.(Local.promises)) f0 mem_src0 f1 mem_src1>>) /\
          (<<VERSWF: versions_wf f1 vers>>)
      ).
  { i. des.
    hexploit Thread.rtc_tau_step_future.
    { eapply rtc_implies; [|eapply STEPS]. i.
      inv H. inv TSTEP. econs; eauto.
    }
    { eauto. }
    { eauto. }
    { eauto. }
    i. ss. des.
    hexploit IHdom; eauto.
    { instantiate (1:=D). i. destruct (classic (D loc)); auto.
      hexploit (DEBT loc). intros [|]; ss.
      right. des_ifs. splits; auto.
      i. red in FLAG. des; ss.
    }
    { i. ss. des_ifs.
      eapply FIN in FLAG0. des; ss. intuition.
    }
    i. des. esplits.
    { etrans; eauto. }
    { eauto. }
    { eauto. }
    { etrans; eauto. }
    { auto. }
    { i. rewrite UNCH0; auto. }
    { eapply map_future_memory_trans; eauto.
      hexploit Thread.rtc_tau_step_future.
      { eapply rtc_implies; [|eapply STEPS0].
        i. inv H. econs; eauto. inv TSTEP. auto.
      }
      { eauto. }
      { eauto. }
      { eauto. }
      i. ss. des. eapply Memory.future_future_weak; eauto.
    }
    { eapply space_future_memory_trans; eauto. }
  }
  hexploit (DEBT a). intros [|[]].
  { hexploit sim_thread_deflag_unmatch; eauto. i. des.
    esplits; eauto.
    { right. eauto. }
    { eapply versions_wf_mapping_mon; eauto. }
  }
  { guardH H0. hexploit sim_thread_deflag_match; eauto. i. des.
    esplits; eauto.
    { left. eauto. }
    { eapply versions_wf_mapping_mon; eauto. }
  }
Qed.

Lemma sim_thread_deflag_all
      (D: Loc.t -> Prop)
      f0 vers flag_src flag_tgt0 vs_src vs_tgt
      mem_src0 mem_tgt lc_src0 lc_tgt sc_src sc_tgt
      (SIM: sim_thread
              f0 vers flag_src flag_tgt0 vs_src vs_tgt
              mem_src0 mem_tgt lc_src0 lc_tgt sc_src sc_tgt)
      (CONSISTENT: Local.promise_consistent lc_tgt)
      (LOCALSRC: Local.wf lc_src0 mem_src0)
      (LOCALTGT: Local.wf lc_tgt mem_tgt)
      (MEMSRC: Memory.closed mem_src0)
      (MEMTGT: Memory.closed mem_tgt)
      (SCSRC: Memory.closed_timemap sc_src mem_src0)
      (SCTGT: Memory.closed_timemap sc_tgt mem_tgt)
      (WF: Mapping.wfs f0)
      (VERSWF: versions_wf f0 vers)
      (DEBT: forall loc, (<<DEBT: D loc>>) \/
                         ((<<FLAG: flag_src loc = false -> flag_tgt0 loc = false>>) /\
                          (<<VAL: option_rel Const.le (vs_tgt loc) (vs_src loc) \/ flag_src loc = false>>)))
      lang st
  :
    exists lc_src1 mem_src1 f1 flag_tgt1,
      (<<STEPS: rtc (tau (@pred_step is_promise _))
                    (Thread.mk lang st lc_src0 sc_src mem_src0)
                    (Thread.mk _ st lc_src1 sc_src mem_src1)>>) /\
      (<<SIM: sim_thread
                f1 vers
                (fun _ => false)
                flag_tgt1
                vs_src vs_tgt
                mem_src1 mem_tgt lc_src1 lc_tgt sc_src sc_tgt>>) /\
      (<<WF: Mapping.wfs f1>>) /\
      (<<MAPLE: Mapping.les f0 f1>>) /\
      (<<FLAG: forall loc, (<<DEBT: D loc>>) \/ (<<FLAG: flag_tgt1 loc = false>>)>>) /\
      (<<UNCH: forall loc (FLAG: flag_src loc = false), f1 loc = f0 loc>>) /\
      (<<MAPFUTURE: map_future_memory f0 f1 mem_src1>>) /\
      (<<SPACE: space_future_memory (unchangable mem_tgt lc_tgt.(Local.promises)) f0 mem_src0 f1 mem_src1>>)
.
Proof.
  dup SIM. inv SIM. red in FIN. des.
  hexploit (@sim_thread_deflag_all_aux dom); eauto.
  { i. eapply DOM. eauto. }
  i. des. esplits; eauto.
  { i. eapply UNCH. ii. eapply DOM in H. des. clarify. }
Qed.

Lemma local_write_fence_step_promise_step
      lc0 ordw lc1
      mem0 loc from to msg lc2 mem1 kind sc0 sc1
      (PROMISE: Local.promise_step lc0 mem0 loc from to msg lc1 mem1 kind)
      (FENCE: local_fence_write_step lc1 sc0 ordw lc2 sc1)
  :
    exists lc1',
      (<<FENCE: local_fence_write_step lc0 sc0 ordw lc1' sc1>>) /\
      (<<PROMISE: Local.promise_step lc1' mem0 loc from to msg lc2 mem1 kind>>).
Proof.
  inv FENCE. inv PROMISE. ss. esplits.
  { econs; eauto. }
  { econs; eauto; ss. }
Qed.

Lemma local_write_fence_step_promise_steps
      lc0 sc0 ordw lc1
      mem0 lc2 mem1 sc1
      lang st
      (STEPS: rtc (tau (@pred_step is_promise _))
                  (Thread.mk lang st lc0 sc0 mem0)
                  (Thread.mk _ st lc1 sc0 mem1))
      (FENCE: local_fence_write_step lc1 sc0 ordw lc2 sc1)
  :
    exists lc1',
      (<<FENCE: local_fence_write_step lc0 sc0 ordw lc1' sc1>>) /\
      (<<STEPS: rtc (tau (@pred_step is_promise _))
                    (Thread.mk lang st lc1' sc1 mem0)
                    (Thread.mk _ st lc2 sc1 mem1)>>).
Proof.
  remember (Thread.mk lang st lc0 sc0 mem0).
  remember (Thread.mk lang st lc1 sc0 mem1).
  revert lc0 st lc1 lc2 sc0 sc1 mem0 mem1 Heqt Heqt0 FENCE.
  induction STEPS; i; clarify.
  { esplits.
    { eauto. }
    { refl. }
  }
  { inv H. inv TSTEP. inv STEP.
    inv STEP0; [inv STEP|inv STEP; inv LOCAL; ss].
    hexploit IHSTEPS; eauto. i. des.
    hexploit local_write_fence_step_promise_step; eauto. i. des.
    esplits; [eauto|]. etrans.
    { eauto. }
    { econs; eauto. econs; eauto. econs; eauto.
      econs; eauto. econs; eauto. econs; eauto.
    }
  }
Qed.

Lemma promise_step_local_read_step lc0 lc1 lc2 mem0 mem1
      loc0 loc1 ts val released ord from to msg kind
      (READ: Local.read_step lc0 mem0 loc0 ts val released ord lc1)
      (PROMISE: Local.promise_step lc1 mem0 loc1 from to msg lc2 mem1 kind)
      (CONS: Local.promise_consistent lc2)
  :
    exists lc1',
      (<<PROMISE: Local.promise_step lc0 mem0 loc1 from to msg lc1' mem1 kind>>) /\
      (<<READ: Local.read_step lc1' mem1 loc0 ts val released ord lc2>>).
Proof.
  inv READ. inv PROMISE. esplits.
  { econs; eauto. }
  { ss. cut (exists from1, Memory.get loc0 ts mem1 = Some (from1, Message.concrete val' released)).
    { i. des. econs; eauto. }
    inv PROMISE0.
    { esplits. eapply Memory.add_get1; eauto. }
    { eapply Memory.split_get1 in MEM; eauto. des. eauto. }
    { erewrite Memory.lower_o; eauto. des_ifs; eauto.
      exfalso. ss. des; clarify. exploit CONS; eauto.
      { eapply Memory.lower_get0; eauto. }
      i. ss. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt; [eapply x|].
      clear x. etrans; [|eapply Time.join_l]. etrans; [|eapply Time.join_r].
      unfold View.singleton_ur_if. des_ifs; ss.
      { rewrite timemap_singleton_eq. refl. }
      { rewrite timemap_singleton_eq. refl. }
    }
    { erewrite Memory.remove_o; eauto. des_ifs; eauto.
      ss. des; clarify. eapply Memory.remove_get0 in MEM. des; clarify.
    }
  }
Qed.

Lemma rtc_promise_step_promise_consistent
      lang th1 th2
      (STEPS: rtc (tau (@pred_step is_promise lang)) th1 th2)
      (CONS: Local.promise_consistent (Thread.local th2)):
  Local.promise_consistent (Thread.local th1).
Proof.
  ginduction STEPS; eauto. i. eapply IHSTEPS in CONS.
  inv H. inv TSTEP. inv STEP. inv STEP0; [inv STEP|inv STEP; inv LOCAL; ss].
  eapply PromiseConsistent.promise_step_promise_consistent; eauto.
Qed.

Lemma promise_steps_local_read_step lc0 lc1 lc2 mem0 mem1
      loc ts val released ord
      lang st0 st1 sc0 sc1
      (READ: Local.read_step lc0 mem0 loc ts val released ord lc1)
      (STEPS: rtc (tau (@pred_step is_promise _))
                  (Thread.mk lang st0 lc1 sc0 mem0)
                  (Thread.mk _ st1 lc2 sc1 mem1))
      (CONS: Local.promise_consistent lc2)
  :
    exists lc1',
      (<<STEPS: rtc (tau (@pred_step is_promise _))
                    (Thread.mk lang st0 lc0 sc0 mem0)
                    (Thread.mk _ st1 lc1' sc1 mem1)>>) /\
      (<<READ: Local.read_step lc1' mem1 loc ts val released ord lc2>>)
.
Proof.
  remember (Thread.mk lang st0 lc1 sc0 mem0).
  remember (Thread.mk lang st1 lc2 sc1 mem1).
  revert lc0 st0 st1 lc1 lc2 sc0 sc1 mem0 mem1 Heqt Heqt0 READ CONS.
  induction STEPS; i; clarify.
  { esplits.
    { refl. }
    { eauto. }
  }
  { inv H. inv TSTEP. inv STEP.
    inv STEP0; [inv STEP|inv STEP; inv LOCAL; ss].
    hexploit promise_step_local_read_step; eauto.
    { eapply rtc_promise_step_promise_consistent in STEPS; eauto. }
    i. des. hexploit IHSTEPS; eauto.
    i. des. esplits; [|eauto].
    econs 2; [|eauto]. econs; eauto. econs; eauto.
    econs; eauto. econs; eauto. econs; eauto.
  }
Qed.

Lemma sim_thread_write_fence_step
      f vers flag_src flag_tgt vs_src0 vs_tgt0
      mem_src mem_tgt lc_src0 lc_tgt0 sc_src0 sc_tgt0 sc_tgt1
      lc_tgt1 ordw
      (SIM: sim_thread
              f vers flag_src flag_tgt vs_src0 vs_tgt0
              mem_src mem_tgt lc_src0 lc_tgt0 sc_src0 sc_tgt0)
      (WRITE: local_fence_write_step lc_tgt0 sc_tgt0 ordw lc_tgt1 sc_tgt1)
      (CONSISTENT: Local.promise_consistent lc_tgt1)
      (LOCALSRC: Local.wf lc_src0 mem_src)
      (LOCALTGT: Local.wf lc_tgt0 mem_tgt)
      (MEMSRC: Memory.closed mem_src)
      (MEMTGT: Memory.closed mem_tgt)
      (SCSRC: Memory.closed_timemap sc_src0 mem_src)
      (SCTGT: Memory.closed_timemap sc_tgt0 mem_tgt)
      (WF: Mapping.wfs f)
      (VERS: versions_wf f vers)
      (RELFLAG: forall loc (ORD: Ordering.le Ordering.acqrel ordw), flag_src loc = false)
      (SYNC: forall (ORD: Ordering.le Ordering.acqrel ordw), Memory.nonsynch lc_tgt0.(Local.promises))
  :
    exists lc_src1 sc_src1,
      (<<READ: local_fence_write_step lc_src0 sc_src0 ordw lc_src1 sc_src1>>) /\
      (<<SIM: sim_thread
                f vers flag_src flag_tgt vs_src0 vs_tgt0
                mem_src mem_tgt lc_src1 lc_tgt1 sc_src1 sc_tgt1>>)
.
Proof.
  assert (exists lc_src1 sc_src1, (<<WRITE: local_fence_write_step lc_src0 sc_src0 ordw lc_src1 sc_src1>>)).
  { esplits. econs; eauto. }
  des. hexploit local_fence_write_step_future; [eapply WRITE|..]; eauto. i. des.
  hexploit local_fence_write_step_future; [eapply WRITE0|..]; eauto. i. des.
  destruct lc_src0 as [tvw_src0 prom_src].
  destruct lc_tgt0 as [tvw_tgt0 prom_tgt].
  inv WRITE. inv WRITE0. ss.
  dup SIM. inv SIM. inv LOCAL1.
  esplits; eauto.
  { econs; eauto. }
  { econs; eauto; ss.
    { eapply sim_local_write_fence_sc; eauto. i. eapply RELFLAG. destruct ordw; ss. }
    { destruct (Ordering.le Ordering.acqrel ordw) eqn:ORD.
      { econs.
        { eapply sim_local_write_fence_tview_release; eauto. }
        { eauto. }
        { econs. i. inv RELVERS. hexploit PROM; eauto. i. des.
          esplits; eauto. i. eapply SYNC in GET; eauto. subst. ss.
        }
        { eauto. }
        { eauto. }
      }
      { econs; eauto. eapply sim_local_write_fence_tview_normal; eauto.
        rewrite ORD. auto.
      }
    }
    { ii. hexploit (MAXSRC loc). i. inv H. econs; eauto. }
    { ii. hexploit (MAXTGT loc). i. inv H. econs; eauto. }
  }
Qed.

Lemma local_fence_read_step_promise_consistent
      lc0 sc ordr ordw lc1
      (READ: local_fence_read_step lc0 sc ordr ordw lc1)
      (CONS: Local.promise_consistent lc1)
      (LOCAL: TView.wf (Local.tview lc0))
  :
    Local.promise_consistent lc0.
Proof.
  inv READ. ii. eapply TimeFacts.le_lt_lt.
  { eapply local_read_fence_tview_incr. eauto. }
  eapply CONS; eauto.
Qed.

Lemma local_fence_write_step_promise_consistent
      lc0 sc0 ordw lc1 sc1
      (WRITE: local_fence_write_step lc0 sc0 ordw lc1 sc1)
      (CONS: Local.promise_consistent lc1)
      (LOCAL: TView.wf (Local.tview lc0))
  :
    Local.promise_consistent lc0.
Proof.
  inv WRITE. ii. eapply TimeFacts.le_lt_lt.
  { eapply local_write_fence_tview_incr. eauto. }
  eapply CONS; eauto.
Qed.

Lemma sim_thread_fence_step_normal
      f vers flag_src flag_tgt vs_src0 vs_tgt0
      mem_src mem_tgt lc_src0 lc_tgt0 sc_src0 sc_tgt0 sc_tgt1
      lc_tgt1 ordr ordw
      (SIM: sim_thread
              f vers flag_src flag_tgt vs_src0 vs_tgt0
              mem_src mem_tgt lc_src0 lc_tgt0 sc_src0 sc_tgt0)
      (WRITE: Local.fence_step lc_tgt0 sc_tgt0 ordr ordw lc_tgt1 sc_tgt1)
      (CONSISTENT: Local.promise_consistent lc_tgt1)
      (LOCALSRC: Local.wf lc_src0 mem_src)
      (LOCALTGT: Local.wf lc_tgt0 mem_tgt)
      (MEMSRC: Memory.closed mem_src)
      (MEMTGT: Memory.closed mem_tgt)
      (SCSRC: Memory.closed_timemap sc_src0 mem_src)
      (SCTGT: Memory.closed_timemap sc_tgt0 mem_tgt)
      (WF: Mapping.wfs f)
      (VERS: versions_wf f vers)
      (ACQFLAG: forall loc
                       (SRC: flag_src loc = false) (TGT: flag_tgt loc = true),
          ~ Ordering.le Ordering.acqrel ordr)
      (ORD: ~ Ordering.le Ordering.acqrel ordw)
  :
    exists lc_src1 sc_src1 vs_src1 vs_tgt1,
      (<<READ: Local.fence_step lc_src0 sc_src0 ordr ordw lc_src1 sc_src1>>) /\
      (<<SIM: sim_thread
                f vers flag_src flag_tgt vs_src1 vs_tgt1
                mem_src mem_tgt lc_src1 lc_tgt1 sc_src1 sc_tgt1>>) /\
      (<<VALS: forall loc0,
          ((<<SRC: vs_src1 loc0 = vs_src0 loc0>>) /\ (<<TGT: vs_tgt1 loc0 = vs_tgt0 loc0>>)) \/
          (exists val_src val_tgt,
              (<<NONESRC: vs_src0 loc0 = None>>) /\ (<<NONETGT: vs_tgt0 loc0 = None>>) /\
              (<<VALSRC: vs_src1 loc0 = Some val_src>>) /\ (<<VALTGT: vs_tgt1 loc0 = Some val_tgt>>) /\
              (<<VALLE: Const.le val_tgt val_src>>) /\
              (<<ORD: Ordering.le Ordering.acqrel ordr \/ Ordering.le Ordering.seqcst ordw>>))>>).
Proof.
  hexploit local_fence_step_split; eauto.
  { eapply LOCALTGT. }
  i. des.
  hexploit local_fence_read_step_future; eauto. i. des.
  hexploit sim_thread_read_fence_step; eauto.
  { eapply local_fence_write_step_promise_consistent; eauto. eapply LOCAL. }
  { i. destruct ordw; ss. }
  i. des.
  hexploit local_fence_read_step_future; eauto. i. des.
  hexploit sim_thread_write_fence_step; eauto.
  { i. destruct ordw; ss. }
  { i. destruct ordw; ss. }
  i. des. esplits; eauto.
  { eapply local_fence_step_merge; eauto. eapply LOCALSRC. }
Qed.

Lemma sim_thread_fence_step_release
      f0 vers flag_src flag_tgt vs_src0 vs_tgt0
      mem_src mem_tgt lc_src0 lc_tgt0 sc_src0 sc_tgt0 sc_tgt1
      lc_tgt1 ordr ordw D
      (SIM: sim_thread
              f0 vers flag_src flag_tgt vs_src0 vs_tgt0
              mem_src mem_tgt lc_src0 lc_tgt0 sc_src0 sc_tgt0)
      (WRITE: Local.fence_step lc_tgt0 sc_tgt0 ordr ordw lc_tgt1 sc_tgt1)
      (CONSISTENT: Local.promise_consistent lc_tgt1)
      (LOCALSRC: Local.wf lc_src0 mem_src)
      (LOCALTGT: Local.wf lc_tgt0 mem_tgt)
      (MEMSRC: Memory.closed mem_src)
      (MEMTGT: Memory.closed mem_tgt)
      (SCSRC: Memory.closed_timemap sc_src0 mem_src)
      (SCTGT: Memory.closed_timemap sc_tgt0 mem_tgt)
      (WF: Mapping.wfs f0)
      (VERS: versions_wf f0 vers)
      (ACQFLAG: forall loc
                       (SRC: flag_src loc = false) (TGT: flag_tgt loc = true),
          ~ Ordering.le Ordering.acqrel ordr)
      (RELFLAG: forall loc
                       (SRC: flag_src loc = false) (TGT: flag_tgt loc = true),
          ~ Ordering.le Ordering.seqcst ordw)
      (DEBT: forall loc, (<<DEBT: D loc>>) \/
                         ((<<FLAG: flag_src loc = false -> flag_tgt loc = false>>) /\
                          (<<VAL: option_rel Const.le (vs_tgt0 loc) (vs_src0 loc) \/ flag_src loc = false>>)))
      lang st
  :
    exists lc_src1 lc_src2 sc_src1 vs_src1 vs_tgt1 f1 flag_tgt1 mem_src1,
      (<<READ: Local.fence_step lc_src0 sc_src0 ordr ordw lc_src1 sc_src1>>) /\
      (<<STEPS: rtc (tau (@pred_step is_promise _))
                    (Thread.mk lang st lc_src1 sc_src1 mem_src)
                    (Thread.mk _ st lc_src2 sc_src1 mem_src1)>>) /\
      (<<SIM: sim_thread
                f1 vers (fun _ => false) flag_tgt1 vs_src1 vs_tgt1
                mem_src1 mem_tgt lc_src2 lc_tgt1 sc_src1 sc_tgt1>>) /\
      (<<VALS: forall loc0,
          ((<<SRC: vs_src1 loc0 = vs_src0 loc0>>) /\ (<<TGT: vs_tgt1 loc0 = vs_tgt0 loc0>>)) \/
          (exists val_src val_tgt,
              (<<NONESRC: vs_src0 loc0 = None>>) /\ (<<NONETGT: vs_tgt0 loc0 = None>>) /\
              (<<VALSRC: vs_src1 loc0 = Some val_src>>) /\ (<<VALTGT: vs_tgt1 loc0 = Some val_tgt>>) /\
              (<<VALLE: Const.le val_tgt val_src>>) /\
              (<<ORD: Ordering.le Ordering.acqrel ordr \/ Ordering.le Ordering.seqcst ordw>>))>>) /\
      (<<WF: Mapping.wfs f1>>) /\
      (<<MAPLE: Mapping.les f0 f1>>) /\
      (<<VERSWF: versions_wf f1 vers>>) /\
      (<<FLAG: forall loc, (<<DEBT: D loc>>) \/ (<<FLAG: flag_tgt1 loc = false>>)>>) /\
      (<<MAPFUTURE: map_future_memory f0 f1 mem_src1>>) /\
      (<<SPACE: space_future_memory (unchangable mem_tgt lc_tgt0.(Local.promises)) f0 mem_src f1 mem_src1>>)
.
Proof.
  hexploit local_fence_step_split; eauto.
  { eapply LOCALTGT. }
  i. des.
  hexploit local_fence_read_step_future; eauto. i. des.
  hexploit sim_thread_read_fence_step; eauto.
  { eapply local_fence_write_step_promise_consistent; eauto. eapply LOCAL. }
  i. des.
  hexploit local_fence_read_step_future; eauto. i. des.
  hexploit sim_thread_deflag_all; eauto.
  { eapply local_fence_write_step_promise_consistent; eauto. eapply LOCAL. }
  { i. hexploit (DEBT loc). i. des; eauto. right. esplits; eauto.
    hexploit (VALS loc). i. des.
    { rewrite SRC. rewrite TGT. auto. }
    { left. rewrite VALTGT. rewrite VALSRC. ss. }
    { left. rewrite VALTGT. rewrite VALSRC. ss. }
  }
  i. des. hexploit Thread.rtc_tau_step_future.
  { eapply rtc_implies; [|eauto]. i. inv H. inv TSTEP. econs; eauto. }
  { eauto. }
  { eauto. }
  { eauto. }
  i. des.
  hexploit sim_thread_write_fence_step; eauto.
  { eapply versions_wf_mapping_mon; eauto. }
  { i. inv STEP0. ss. eapply RELEASE. destruct ordw; ss. }
  i. des. hexploit local_write_fence_step_promise_steps; eauto. i. des.
  esplits.
  { eapply local_fence_step_merge; eauto. eapply LOCALSRC. }
  { eauto. }
  { eauto. }
  { i. hexploit (VALS loc0). i. des; eauto. }
  { eauto. }
  { eauto. }
  { eapply versions_wf_mapping_mon; eauto. }
  { eauto. }
  { eauto. }
  { inv STEP0. eauto. }
Qed.

Lemma write_max_readable_none
      lc0 sc0 mem0 loc from to val releasedm released ord lc1 sc1 mem1 kind
      val0 released0
      (WRITE: Local.write_step lc0 sc0 mem0 loc from to val releasedm released ord lc1 sc1 mem1 kind)
      (WF: Local.wf lc0 mem0)
      (MAX: max_readable mem0 lc0.(Local.promises) loc (lc0.(Local.tview).(TView.cur).(View.pln) loc) val0 released0)
  :
  max_readable mem1 lc1.(Local.promises) loc (lc1.(Local.tview).(TView.cur).(View.pln) loc) val released.
Proof.
  hexploit local_write_step_timestamp; eauto. i.
  destruct lc0, lc1. ss; clarify.
  inv WRITE. hexploit Memory.write_get2; eauto. i. des. clarify.
  inv MAX. econs; eauto. i.
  destruct (Memory.get loc ts' promises2) eqn:EQ.
  { destruct p. eapply write_promises_le in WRITE0; eauto.
    { eapply WRITE0 in EQ. clarify. }
    { eapply WF. }
  }
  ss. exfalso.
  assert (exists from', Memory.get loc ts' mem0 = Some (from', msg)).
  { inv WRITE0. eapply MemoryFacts.promise_get_inv_diff in GET0; eauto.
    ii. clarify. timetac.
  }
  des. hexploit MAX0; eauto.
  { eapply TimeFacts.le_lt_lt; eauto. rewrite H1. ss. eapply Time.join_l. }
  i. inv WRITE0. erewrite Memory.remove_o in EQ; eauto. des_ifs.
  { ss. des; clarify. timetac. }
  ss. des; auto. inv PROMISE.
  { erewrite Memory.add_o in EQ; eauto. des_ifs. }
  { erewrite Memory.split_o in EQ; eauto. des_ifs. }
  { erewrite Memory.lower_o in EQ; eauto. des_ifs. }
  { ss. }
Qed.

Lemma writable_message_to tvw sc loc from to releasedm ord
      (WRITABLE: TView.writable (TView.cur tvw) sc loc to ord)
      (WF: TView.wf tvw)
      (TS: Time.lt from to)
      (MSG: Time.le (View.rlx (View.unwrap releasedm) loc) from)
  :
  Time.le (View.rlx (View.unwrap (TView.write_released tvw sc loc to releasedm ord)) loc) to.
Proof.
  assert (TIME: Time.le (View.rlx (View.unwrap releasedm) loc) to).
  { etrans; eauto. left. auto. }
  unfold TView.write_released. ss. des_ifs; ss.
  { eapply Time.join_spec; auto.
    setoid_rewrite LocFun.add_spec_eq.
    eapply Time.join_spec; auto; ss.
    { left. eapply WRITABLE. }
    { rewrite timemap_singleton_eq. refl. }
  }
  { eapply Time.join_spec; auto.
    setoid_rewrite LocFun.add_spec_eq.
    eapply Time.join_spec; auto; ss.
    { etrans.
      { eapply WF. }
      { left. eapply WRITABLE. }
    }
    { rewrite timemap_singleton_eq. refl. }
  }
  { eapply Time.bot_spec. }
Qed.

Lemma sim_thread_write_aux
      f0 vers0 flag_src flag_tgt vs_src0 vs_tgt0
      mem_src0 mem_tgt0 lc_src0 lc_tgt0 sc_src0 sc_tgt0
      val_tgt val_src releasedm_tgt releasedm_src
      lc_tgt1 mem_tgt1 loc from_tgt to_tgt to_src from_src
      released_tgt ord sc_tgt1 kind_tgt
      (SIM: sim_thread
              f0 vers0 flag_src flag_tgt vs_src0 vs_tgt0
              mem_src0 mem_tgt0 lc_src0 lc_tgt0 sc_src0 sc_tgt0)
      (WRITE: Local.write_step lc_tgt0 sc_tgt0 mem_tgt0 loc from_tgt to_tgt val_tgt releasedm_tgt released_tgt ord lc_tgt1 sc_tgt1 mem_tgt1 kind_tgt)
      (RELEASEDM: sim_opt_view (fun loc0 => loc0 <> loc) f0 (vers0 loc from_tgt) releasedm_src releasedm_tgt)
      (MSGTOSRC: Time.le (View.rlx (View.unwrap releasedm_src) loc) from_src)
      (TO: sim_timestamp_exact (f0 loc) (f0 loc).(Mapping.ver) to_src to_tgt)
      (FROM: sim_timestamp_exact (f0 loc) (f0 loc).(Mapping.ver) from_src from_tgt)
      (CONSISTENT: Local.promise_consistent lc_tgt1)
      (LOCALSRC: Local.wf lc_src0 mem_src0)
      (LOCALTGT: Local.wf lc_tgt0 mem_tgt0)
      (MEMSRC: Memory.closed mem_src0)
      (MEMTGT: Memory.closed mem_tgt0)
      (SCSRC: Memory.closed_timemap sc_src0 mem_src0)
      (SCTGT: Memory.closed_timemap sc_tgt0 mem_tgt0)
      (WF: Mapping.wfs f0)
      (VERS: versions_wf f0 vers0)
      (FLAGSRC: flag_src loc = false)
      (FLAGTGT: flag_tgt loc = false)
      (VAL: Const.le val_tgt val_src)
      (ORD: ~ Ordering.le Ordering.strong_relaxed ord)
      (WFSRC: View.opt_wf releasedm_src)
      (WFTGT: View.opt_wf releasedm_tgt)
      (CLOSEDMSRC: Memory.closed_opt_view releasedm_src mem_src0)
      (CLOSEDMTGT: Memory.closed_opt_view releasedm_tgt mem_tgt0)
  :
  exists f1 vers1 released_src lc_src1 vs_src1 vs_tgt1 mem_src1 sc_src1 kind_src,
    (<<WRITE: Local.write_step lc_src0 sc_src0 mem_src0 loc from_src to_src val_src releasedm_src released_src ord lc_src1 sc_src1 mem_src1 kind_src>>) /\
      (<<SIM: sim_thread
                f1 vers1 flag_src flag_tgt vs_src1 vs_tgt1
                mem_src1 mem_tgt1 lc_src1 lc_tgt1 sc_src1 sc_tgt1>>) /\
      (<<WF: Mapping.wfs f1>>) /\
      (<<MAPLE: Mapping.les_strong f0 f1>>) /\
      (<<VERSLE: versions_le vers0 vers1>>) /\
      (<<VERSWF: versions_wf f1 vers1>>) /\
      (<<VALS: forall loc0,
          ((<<SRC: vs_src1 loc0 = vs_src0 loc0>>) /\ (<<TGT: vs_tgt1 loc0 = vs_tgt0 loc0>>) /\ (<<LOC: loc0 <> loc>>)) \/
            ((<<LOC: loc0 = loc>>) /\
               ((<<VALSRC: vs_src1 loc0 = Some val_src>> /\ <<VALTGT: vs_tgt1 loc0 = Some val_tgt>>) \/
                  (<<VALSRC0: vs_src0 loc0 = None>> /\ <<VALTGT0: vs_tgt0 loc0 = None>> /\ <<VALSRC1: vs_src1 loc0 = None>> /\ <<VALTGT1: vs_tgt1 loc0 = None>>)))>>) /\
      (<<SPACE: space_future_memory (unchangable mem_tgt0 lc_tgt0.(Local.promises)) f0 mem_src0 f1 mem_src1>>).
Proof.
  hexploit Local.write_step_future; eauto. i. des.
  destruct lc_src0 as [tvw_src0 prom_src].
  destruct lc_tgt0 as [tvw_tgt0 prom_tgt].
  dup SIM. inv SIM. inv LOCAL. dup WRITE. guardH WRITE. inv WRITE. ss.
  set (msg_src := Message.concrete val_tgt (TView.write_released tvw_tgt0 sc_tgt0 loc to_tgt releasedm_tgt ord)).
  assert (SIMMSG: sim_message (flag_tgt loc) loc f0 (opt_version_join (vers0 loc from_tgt) (Some (rel_vers loc)))
                              (Message.concrete val_src (TView.write_released tvw_src0 sc_src0 loc to_src releasedm_src ord))
                              (Message.concrete val_tgt (TView.write_released tvw_tgt0 sc_tgt0 loc to_tgt releasedm_tgt ord))).
  { clear WRITE0.
    replace (opt_version_join (vers0 loc from_tgt) (Some (rel_vers loc))) with
      (Some (match (vers0 loc from_tgt) with
             | Some v => version_join v (rel_vers loc)
             | None => (rel_vers loc)
             end)).
    { rewrite FLAGTGT. econs; auto.
      assert (VERWF: version_wf f0 match vers0 loc from_tgt with
                                   | Some v => version_join v (rel_vers loc)
                                   | None => rel_vers loc
                                   end).
      { des_ifs; ss.
        { eapply version_wf_join; eauto.
          { exploit VERS. rewrite Heq. ss. }
          { inv TVIEW. auto. }
        }
        { inv TVIEW. auto. }
      }
      eapply sim_write_released_normal; eauto.
      { eapply sim_opt_view_mon_ver; eauto.
        { des_ifs. ss. eapply version_join_l. }
      }
      { destruct ord; ss. }
      { i. ss. des_ifs. eapply version_join_r; eauto. }
    }
    { destruct (vers0 loc from_tgt); auto. }
  }
  assert (WRITABLE0: TView.writable (TView.cur tvw_src0) sc_src0 loc to_src ord).
  { eapply sim_writable; eauto.
    { inv TVIEW. eauto. }
    { ss. }
  }
  hexploit sim_memory_write; eauto.
  { eapply LOCALSRC. }
  { inv TVIEW. eauto. }
  { econs. eapply TViewFacts.write_future0; eauto. eapply LOCALSRC. }
  { econs; ss. eapply writable_message_to; eauto.
    { eapply LOCALSRC. }
    { eapply sim_timestamp_exact_lt; eauto.
      { eapply MemoryFacts.write_time_lt; eauto. }
      { eapply mapping_latest_wf_loc. }
    }
  }
  { red. eauto. }
  i. des.
  assert (from_src0 = from_src).
  { eapply sim_timestamp_exact_inject; eauto.
    eapply sim_timestamp_exact_mon_strong; eauto.
  }
  subst.
  set (tvw_src1 := TView.write_tview tvw_src0 sc_src0 loc to_src ord).
  set (tvw_tgt1 := TView.write_tview tvw_tgt0 sc_tgt0 loc to_tgt ord).
  assert (exists released_src,
             (<<WRITE: Local.write_step (Local.mk tvw_src0 prom_src) sc_src0 mem_src0 loc from_src
                                        to_src val_src releasedm_src released_src ord (Local.mk tvw_src1 prom_src1) sc_src0 mem_src1 kind_src>>) /\
               (<<LOCAL: sim_local f1 vers1 tvw_src1.(TView.cur).(View.rlx) flag_src flag_tgt (Local.mk tvw_src1 prom_src1) (Local.mk (TView.write_tview tvw_tgt0 sc_tgt0 loc to_tgt ord) promises2)>>)).
  { esplits.
    { econs; eauto. ss. }
    { ss. econs.
      { eapply sim_write_tview_normal; eauto.
        { eapply sim_tview_mon_latest; eauto. eapply Mapping.les_strong_les; eauto. }
        { eapply sim_timestamp_exact_mon_strong; eauto. }
        { destruct ord; ss. }
      }
      { eapply sim_promises_change_no_flag; eauto. i. rewrite SRCTM.
        unfold TimeMap.join. rewrite TimeFacts.le_join_l; auto.
        rewrite timemap_singleton_neq; auto.
        { eapply Time.bot_spec. }
        { ii. subst. rewrite FLAG in *. ss. }
      }
      { eauto. }
      { i. ss. unfold TimeMap.join. rewrite FLAGSRC0; ss. }
      { ss. }
    }
  }
  des.
  hexploit max_value_src_exists. i. des.
  set (vs_src1 := fun loc0 => if Loc.eq_dec loc0 loc then v else vs_src0 loc0).
  set (vs_tgt1 := fun loc0 => if Loc.eq_dec loc0 loc then match v with
                                                          | Some _ => Some val_tgt
                                                          | None => None
                                                          end else vs_tgt0 loc0).
  assert (MEM1: sim_memory tvw_src1.(TView.cur).(View.rlx) flag_src f1 vers1 mem_src1 mem_tgt1).
  { eapply sim_memory_change_no_flag; eauto. i.
    subst tvw_src1. ss. rewrite SRCTM. eapply TimeFacts.le_join_l.
    rewrite timemap_singleton_neq; auto.
    { eapply Time.bot_spec. }
    { ii. subst. rewrite FLAG in *. ss. }
  }
  assert (PLNTS: forall loc0 (NEQ: loc0 <> loc), View.pln (TView.cur tvw_src1) loc0 = View.pln (TView.cur tvw_src0) loc0).
  { i. ss. unfold TimeMap.join. rewrite timemap_singleton_neq; auto.
    rewrite TimeFacts.le_join_l; auto. eapply Time.bot_spec.
  }
  assert (RLXTS: forall loc0 (NEQ: loc0 <> loc), View.rlx (TView.cur tvw_src1) loc0 = View.rlx (TView.cur tvw_src0) loc0).
  { i. ss. unfold TimeMap.join. rewrite timemap_singleton_neq; auto.
    rewrite TimeFacts.le_join_l; auto. eapply Time.bot_spec.
  }
  esplits.
  { eauto. }
  { econs.
    { eapply sim_timemap_mon_latest; eauto. eapply Mapping.les_strong_les; eauto. }
    { eauto. }
    { eauto. }
    { instantiate (1:=vs_src1). ii. unfold vs_src1.
      clear WRITE0. des_ifs.
      { eauto. }
      { specialize (MAXSRC loc0). inv MAXSRC. econs.
        { i. hexploit MAX0; eauto. i. des. esplits; eauto. rewrite PLNTS; eauto.
          eapply write_unchanged_loc in CANCEL; eauto. des.
          erewrite <- unchanged_loc_max_readable; eauto.
        }
        { rewrite PLNTS; eauto. i. eapply write_unchanged_loc in CANCEL; eauto. des.
          erewrite <- unchanged_loc_max_readable; eauto.
        }
      }
    }
    { instantiate (1:=vs_tgt1). ii. unfold vs_tgt1. condtac.
      { econs. i. destruct v; ss. subst. inv VAL0.
        hexploit no_flag_max_value_same; eauto.
        i. des. inv MAX0. hexploit MAX1; auto. i. des.
        eapply write_max_readable in WRITE0; eauto.
        des. subst. esplits; eauto.
      }
      { assert (TS: View.pln (TView.cur (tvw_tgt1)) loc0 = View.pln (TView.cur tvw_tgt0) loc0).
        { ss. unfold TimeMap.join. rewrite timemap_singleton_neq; auto.
          rewrite TimeFacts.le_join_l; auto. eapply Time.bot_spec.
        }
        specialize (MAXTGT loc0). inv MAXTGT. econs. i. hexploit MAX0; eauto.
        i. des. esplits. rewrite TS.
        eapply write_unchanged_loc in WRITE1; eauto. des.
        erewrite <- unchanged_loc_max_readable; eauto.
      }
    }
    { unfold vs_src1, vs_tgt1. i. clear WRITE0. des_ifs. }
    { eauto. }
    { eauto. }
    { eauto. }
    { i. assert (NEQ: loc0 <> loc).
      { ii. subst. rewrite FLAG in *. ss. }
      rewrite RLXTS; auto. rewrite <- SRCTM. rewrite MAXTIMES; auto.
      eapply unchanged_loc_max_ts.
      2:{ eapply MEMSRC. }
      eapply write_unchanged_loc in CANCEL; eauto. des. auto.
    }
    { ss. eapply reserved_space_empty_mon_strong; eauto.
      eapply reserved_space_empty_reserve_decr.
      { eapply reserved_space_empty_covered_decr; eauto.
        i. inv WRITE. ss. inv LC2. eapply write_unchanged_loc in WRITE2.
        { des. inv MEM2. inv COVER. erewrite UNCH in GET. econs; eauto. }
        { ii. subst. rewrite FLAG in *. ss. }
      }
      { i. inv WRITE0. ss. inv LC2. eapply write_unchanged_loc in WRITE2.
        { des. inv PROM0. erewrite UNCH in GET. eauto. }
        { ii. subst. rewrite FLAG in *. ss. }
      }
    }
    { auto. }
  }
  { eauto. }
  { eauto. }
  { eauto. }
  { eauto. }
  { i. unfold vs_src1, vs_tgt1. clear WRITE0. des_ifs.
    { right. splits; auto. left. splits; auto. f_equal.
      inv MAX. hexploit MAX0; eauto. i. des.
      eapply write_max_readable in WRITE; eauto. des; auto.
    }
    { right. splits; auto. right.
      assert (NONE: vs_src0 loc = None).
      { destruct (vs_src0 loc) eqn:SOME; auto.
        specialize (MAXSRC loc). inv MAXSRC. hexploit MAX0; eauto.
        i. des. eapply write_max_readable_none in WRITE; eauto.
        inv MAX. exfalso. eapply NONMAX0; eauto.
      }
      splits; auto. specialize (PERM loc).
      rewrite NONE in PERM. destruct (vs_tgt0 loc); ss.
    }
    { left. auto. }
  }
  { auto. }
Qed.

Lemma sim_thread_mapping_add
      loc ts_tgt
      f0 vers flag_src flag_tgt vs_src vs_tgt
      mem_src mem_tgt lc_src lc_tgt sc_src sc_tgt
      (SIM: sim_thread
              f0 vers flag_src flag_tgt vs_src vs_tgt
              mem_src mem_tgt lc_src lc_tgt sc_src sc_tgt)
      (WF: Mapping.wfs f0)
      (VERS: versions_wf f0 vers)
      (FLAG: flag_src loc = false)
  :
  exists f1 ts_src,
      (<<SIM: sim_thread
                f1 vers flag_src flag_tgt vs_src vs_tgt
                mem_src mem_tgt lc_src lc_tgt sc_src sc_tgt>>) /\
      (<<WF: Mapping.wfs f1>>) /\
      (<<MAPLE: Mapping.les_strong f0 f1>>) /\
      (<<VERS: versions_wf f1 vers>>) /\
      (<<TS: sim_timestamp_exact (f1 loc) (f1 loc).(Mapping.ver) ts_src ts_tgt>>)
.
Proof.
  hexploit (@mapping_add (f0 loc) ts_tgt); eauto. i. des.
  set (f' := (fun loc0 => if Loc.eq_dec loc0 loc then f1 else f0 loc0)).
  assert (LES: Mapping.les_strong f0 f').
  { unfold f'. ii. des_ifs. refl. }
  assert (LE: Mapping.les f0 f').
  { eapply Mapping.les_strong_les. auto. }
  assert (WF1: Mapping.wfs f').
  { unfold f'. ii. des_ifs. }
  exists f', fts. splits; auto.
  { inv SIM. econs; eauto.
    { eapply sim_timemap_mon_latest; eauto. }
    { eapply sim_memory_mon_strong; eauto.
      unfold f'. ii. des_ifs.
    }
    { inv LOCAL. econs; eauto.
      { eapply sim_tview_mon_latest; eauto. }
      { eapply sim_promises_mon_strong; eauto.
        unfold f'. ii. des_ifs.
      }
    }
    { unfold f'. ii. eapply SIMCLOSED. des_ifs. eapply TIMES. auto. }
    { eapply reserved_space_empty_mon_strong; eauto. }
    { eapply promise_finalized_mon_strong; eauto. }
  }
  { eapply versions_wf_mapping_mon; eauto. }
  { unfold f'. des_ifs. }
Qed.

Lemma space_future_memory_mon_map msgs f0 f1 f2 mem0 mem1
      (SPACE: space_future_memory msgs f1 mem0 f2 mem1)
      (MAP0: Mapping.les_strong f0 f1)
      (MAP1: Mapping.les f1 f2)
      (WF0: Mapping.wfs f0)
      (WF1: Mapping.wfs f1)
      (WF2: Mapping.wfs f2)
  :
  space_future_memory msgs f0 mem0 f2 mem1.
Proof.
  eapply space_future_memory_trans.
  2:{ eauto. }
  { eapply space_future_memory_refl; eauto. }
  { eapply Mapping.les_strong_les; auto. }
  { auto. }
  { auto. }
  { auto. }
  { auto. }
Qed.

Lemma sim_thread_write_step_normal
      f0 vers0 flag_src flag_tgt vs_src0 vs_tgt0
      mem_src0 mem_tgt0 lc_src0 lc_tgt0 sc_src0 sc_tgt0
      val_tgt val_src
      lc_tgt1 mem_tgt1 loc from_tgt to_tgt
      released_tgt ord sc_tgt1 kind_tgt
      (SIM: sim_thread
              f0 vers0 flag_src flag_tgt vs_src0 vs_tgt0
              mem_src0 mem_tgt0 lc_src0 lc_tgt0 sc_src0 sc_tgt0)
      (WRITE: Local.write_step lc_tgt0 sc_tgt0 mem_tgt0 loc from_tgt to_tgt val_tgt None released_tgt ord lc_tgt1 sc_tgt1 mem_tgt1 kind_tgt)
      (CONSISTENT: Local.promise_consistent lc_tgt1)
      (LOCALSRC: Local.wf lc_src0 mem_src0)
      (LOCALTGT: Local.wf lc_tgt0 mem_tgt0)
      (MEMSRC: Memory.closed mem_src0)
      (MEMTGT: Memory.closed mem_tgt0)
      (SCSRC: Memory.closed_timemap sc_src0 mem_src0)
      (SCTGT: Memory.closed_timemap sc_tgt0 mem_tgt0)
      (WF: Mapping.wfs f0)
      (VERS: versions_wf f0 vers0)
      (FLAGSRC: flag_src loc = false)
      (FLAGTGT: flag_tgt loc = false)
      (VAL: Const.le val_tgt val_src)
      (ORD: ~ Ordering.le Ordering.strong_relaxed ord)
  :
  exists f1 vers1 released_src lc_src1 vs_src1 vs_tgt1 mem_src1 sc_src1 kind_src from_src to_src,
    (<<WRITE: Local.write_step lc_src0 sc_src0 mem_src0 loc from_src to_src val_src None released_src ord lc_src1 sc_src1 mem_src1 kind_src>>) /\
      (<<SIM: sim_thread
                f1 vers1 flag_src flag_tgt vs_src1 vs_tgt1
                mem_src1 mem_tgt1 lc_src1 lc_tgt1 sc_src1 sc_tgt1>>) /\
      (<<WF: Mapping.wfs f1>>) /\
      (<<MAPLE: Mapping.les_strong f0 f1>>) /\
      (<<VERSLE: versions_le vers0 vers1>>) /\
      (<<VERSWF: versions_wf f1 vers1>>) /\
      (<<VALS: forall loc0,
          ((<<SRC: vs_src1 loc0 = vs_src0 loc0>>) /\ (<<TGT: vs_tgt1 loc0 = vs_tgt0 loc0>>) /\ (<<LOC: loc0 <> loc>>)) \/
            ((<<LOC: loc0 = loc>>) /\
               ((<<VALSRC: vs_src1 loc0 = Some val_src>> /\ <<VALTGT: vs_tgt1 loc0 = Some val_tgt>>) \/
                  (<<VALSRC0: vs_src0 loc0 = None>> /\ <<VALTGT0: vs_tgt0 loc0 = None>> /\ <<VALSRC1: vs_src1 loc0 = None>> /\ <<VALTGT1: vs_tgt1 loc0 = None>>)))>>) /\
      (<<SPACE: space_future_memory (unchangable mem_tgt0 lc_tgt0.(Local.promises)) f0 mem_src0 f1 mem_src1>>).
Proof.
  hexploit (@sim_thread_mapping_add loc from_tgt); eauto. i. des.
  hexploit (@sim_thread_mapping_add loc to_tgt); eauto. i. des.
  hexploit sim_thread_write_aux; eauto.
  { econs. }
  { eapply Time.bot_spec. }
  { eapply sim_timestamp_exact_mon_strong; [..|eapply TS]; eauto. }
  i. des. esplits; eauto.
  { etrans; eauto. etrans; eauto. }
  { eapply space_future_memory_mon_map; eauto.
    { etrans; eauto. }
    { eapply Mapping.les_strong_les; auto. }
  }
Qed.

Lemma sim_thread_write_update_normal
      f0 vers0 flag_src flag_tgt vs_src0 vs_tgt0
      mem_src0 mem_tgt0 lc_src0 lc_tgt0 sc_src0 sc_tgt0
      val_tgt val_src releasedm_tgt releasedm_src
      lc_tgt1 mem_tgt1 loc from_tgt to_tgt from_src
      released_tgt ord sc_tgt1 kind_tgt
      (SIM: sim_thread
              f0 vers0 flag_src flag_tgt vs_src0 vs_tgt0
              mem_src0 mem_tgt0 lc_src0 lc_tgt0 sc_src0 sc_tgt0)
      (WRITE: Local.write_step lc_tgt0 sc_tgt0 mem_tgt0 loc from_tgt to_tgt val_tgt releasedm_tgt released_tgt ord lc_tgt1 sc_tgt1 mem_tgt1 kind_tgt)
      (RELEASEDM: sim_opt_view (fun loc0 => loc0 <> loc) f0 (vers0 loc from_tgt) releasedm_src releasedm_tgt)
      (MSGTOSRC: Time.le (View.rlx (View.unwrap releasedm_src) loc) from_src)
      (FROM: sim_timestamp_exact (f0 loc) (f0 loc).(Mapping.ver) from_src from_tgt)
      (CONSISTENT: Local.promise_consistent lc_tgt1)
      (LOCALSRC: Local.wf lc_src0 mem_src0)
      (LOCALTGT: Local.wf lc_tgt0 mem_tgt0)
      (MEMSRC: Memory.closed mem_src0)
      (MEMTGT: Memory.closed mem_tgt0)
      (SCSRC: Memory.closed_timemap sc_src0 mem_src0)
      (SCTGT: Memory.closed_timemap sc_tgt0 mem_tgt0)
      (WF: Mapping.wfs f0)
      (VERS: versions_wf f0 vers0)
      (FLAGSRC: flag_src loc = false)
      (FLAGTGT: flag_tgt loc = false)
      (VAL: Const.le val_tgt val_src)
      (ORD: ~ Ordering.le Ordering.strong_relaxed ord)
      (WFSRC: View.opt_wf releasedm_src)
      (WFTGT: View.opt_wf releasedm_tgt)
      (CLOSEDMSRC: Memory.closed_opt_view releasedm_src mem_src0)
      (CLOSEDMTGT: Memory.closed_opt_view releasedm_tgt mem_tgt0)
  :
  exists f1 vers1 released_src lc_src1 vs_src1 vs_tgt1 mem_src1 sc_src1 kind_src to_src,
    (<<WRITE: Local.write_step lc_src0 sc_src0 mem_src0 loc from_src to_src val_src releasedm_src released_src ord lc_src1 sc_src1 mem_src1 kind_src>>) /\
      (<<SIM: sim_thread
                f1 vers1 flag_src flag_tgt vs_src1 vs_tgt1
                mem_src1 mem_tgt1 lc_src1 lc_tgt1 sc_src1 sc_tgt1>>) /\
      (<<WF: Mapping.wfs f1>>) /\
      (<<MAPLE: Mapping.les_strong f0 f1>>) /\
      (<<VERSLE: versions_le vers0 vers1>>) /\
      (<<VERSWF: versions_wf f1 vers1>>) /\
      (<<VALS: forall loc0,
          ((<<SRC: vs_src1 loc0 = vs_src0 loc0>>) /\ (<<TGT: vs_tgt1 loc0 = vs_tgt0 loc0>>) /\ (<<LOC: loc0 <> loc>>)) \/
            ((<<LOC: loc0 = loc>>) /\
               ((<<VALSRC: vs_src1 loc0 = Some val_src>> /\ <<VALTGT: vs_tgt1 loc0 = Some val_tgt>>) \/
                  (<<VALSRC0: vs_src0 loc0 = None>> /\ <<VALTGT0: vs_tgt0 loc0 = None>> /\ <<VALSRC1: vs_src1 loc0 = None>> /\ <<VALTGT1: vs_tgt1 loc0 = None>>)))>>) /\
      (<<SPACE: space_future_memory (unchangable mem_tgt0 lc_tgt0.(Local.promises)) f0 mem_src0 f1 mem_src1>>).
Proof.
  hexploit (@sim_thread_mapping_add loc to_tgt); eauto. i. des.
  hexploit sim_thread_write_aux; eauto.
  { erewrite <- sim_opt_view_mon_mapping; eauto.
    eapply Mapping.les_strong_les; eauto.
  }
  { eapply sim_timestamp_exact_mon_strong; [..|eauto]; eauto. }
  i. des. esplits; eauto.
  { etrans; eauto. }
  { eapply space_future_memory_mon_map; eauto.
    eapply Mapping.les_strong_les; auto.
  }
Qed.

Definition local_write_sync_tview (tview1: TView.t) (loc: Loc.t) (ord: Ordering.t): TView.t :=
  TView.mk
    (if Ordering.le Ordering.acqrel ord
     then fun loc0 =>
            if (Loc.eq_dec loc0 loc)
            then tview1.(TView.cur)
            else tview1.(TView.rel) loc0
     else tview1.(TView.rel))
    (tview1.(TView.cur))
    (tview1.(TView.acq)).

Lemma local_write_sync_tview_wf tview loc ord
      (WF: TView.wf tview)
  :
  TView.wf (local_write_sync_tview tview loc ord).
Proof.
  econs; ss; i; des_ifs; try by (eapply WF). refl.
Qed.

Lemma local_write_sync_tview_closed mem tview loc ord
      (TVIEW: TView.closed tview mem)
  :
  TView.closed (local_write_sync_tview tview loc ord) mem.
Proof.
  unfold local_write_sync_tview.
  econs; i; ss; des_ifs; try by (eapply TVIEW).
Qed.

Lemma local_write_sync_tview_incr tview loc ord
      (WF: TView.wf tview)
  :
    TView.le tview (local_write_sync_tview tview loc ord).
Proof.
  econs; ss.
  { i. des_ifs.
    { unfold LocFun.find. des_ifs.
      { eapply WF. }
      { refl. }
    }
    { refl. }
  }
  { refl. }
  { refl. }
Qed.

Variant local_write_sync_step lc1 loc ord lc2: Prop :=
| local_write_sync_step_intro
    (LOCAL: lc2 = Local.mk
                    (local_write_sync_tview lc1.(Local.tview) loc ord)
                    (lc1.(Local.promises)))
    (SYNC: forall (ORD: Ordering.le Ordering.strong_relaxed ord),
        Memory.nonsynch_loc loc (Local.promises lc1))
.

Definition non_sync_ord (ord: Ordering.t): Ordering.t :=
  if Ordering.le Ordering.relaxed ord then Ordering.relaxed else ord.

Lemma local_write_sync_tview_merge tvw loc ord sc to
  :
  TView.write_tview (local_write_sync_tview tvw loc ord) sc loc to (non_sync_ord ord) = TView.write_tview tvw sc loc to ord.
Proof.
  unfold TView.write_tview. f_equal.
  unfold LocFun.add, LocFun.find. extensionality loc0.
  ss. des_ifs. destruct ord; ss.
Qed.

Lemma local_write_released_merge tvw loc ord sc to releasedm
  :
  TView.write_released (local_write_sync_tview tvw loc ord) sc loc to releasedm (non_sync_ord ord) = TView.write_released tvw sc loc to releasedm ord.
Proof.
  unfold TView.write_released. des_ifs.
  { f_equal. f_equal. rewrite local_write_sync_tview_merge. auto. }
  { destruct ord; ss. }
  { destruct ord; ss. }
Qed.

Lemma local_write_step_merge
      lc0 sc0 mem0 loc from to val releasedm released ord lc1 sc1 mem1 kind lc2
      (STEP0: local_write_sync_step lc0 loc ord lc1)
      (STEP1: Local.write_step lc1 sc0 mem0 loc from to val releasedm released (non_sync_ord ord) lc2 sc1 mem1 kind)
  :
  Local.write_step lc0 sc0 mem0 loc from to val releasedm released ord lc2 sc1 mem1 kind.
Proof.
  inv STEP0. inv STEP1. ss. econs; ss; eauto.
  { eapply local_write_released_merge; eauto. }
  { inv WRITABLE. econs; eauto. }
  { f_equal. eapply local_write_sync_tview_merge; auto. }
Qed.

Lemma local_write_step_split
      lc0 sc0 mem0 loc from to val releasedm released ord sc1 mem1 kind lc2
      (STEP: Local.write_step lc0 sc0 mem0 loc from to val releasedm released ord lc2 sc1 mem1 kind)
  :
  exists lc1,
    (<<STEP0: local_write_sync_step lc0 loc ord lc1>>) /\
    (<<STEP1: Local.write_step lc1 sc0 mem0 loc from to val releasedm released (non_sync_ord ord) lc2 sc1 mem1 kind>>).
Proof.
  inv STEP. esplits.
  { econs; eauto. }
  { econs; ss; eauto.
    { symmetry. apply local_write_released_merge. }
    { inv WRITABLE. econs; auto. }
    { destruct ord; ss. }
    { f_equal. symmetry. apply local_write_sync_tview_merge. }
  }
Qed.

Lemma local_write_sync_step_future lc1 loc ord lc2 mem
      (STEP: local_write_sync_step lc1 loc ord lc2)
      (LOCAL: Local.wf lc1 mem)
  :
    (<<LOCAL: Local.wf lc2 mem>>) /\
    (<<INCR: TView.le lc1.(Local.tview) lc2.(Local.tview)>>).
Proof.
  inv STEP. splits.
  { inv LOCAL. econs; ss.
    { eapply local_write_sync_tview_wf; eauto. }
    { eapply local_write_sync_tview_closed; eauto. }
  }
  { eapply local_write_sync_tview_incr. eapply LOCAL. }
Qed.

Lemma sim_write_sync_tview_normal f flag_src rel_vers tvw_src tvw_tgt
      loc ord
      (SIM: sim_tview f flag_src rel_vers tvw_src tvw_tgt)
      (WF: Mapping.wfs f)
      (ORD: ~ Ordering.le Ordering.strong_relaxed ord)
  :
  sim_tview f flag_src rel_vers (local_write_sync_tview tvw_src loc ord) (local_write_sync_tview tvw_tgt loc ord).
Proof.
  unfold local_write_sync_tview. econs; ss.
  { des_ifs.
    { destruct ord; ss. }
    i. eapply SIM.
  }
  { eapply SIM. }
  { eapply SIM. }
  { eapply SIM. }
Qed.

Lemma sim_write_sync_tview_release f flag_src rel_vers tvw_src tvw_tgt
      loc ord
      (SIM: sim_tview f flag_src rel_vers tvw_src tvw_tgt)
      (FLAG: forall loc, flag_src loc = false)
      (WF: Mapping.wfs f)
  :
  sim_tview f flag_src (fun loc0 => if Loc.eq_dec loc0 loc then (Mapping.vers f) else rel_vers loc0) (local_write_sync_tview tvw_src loc ord) (local_write_sync_tview tvw_tgt loc ord).
Proof.
  assert (VERLE: forall loc0, version_wf f (rel_vers loc0)).
  { eapply SIM. }
  pose proof (mapping_latest_wf f) as VERWF.
  unfold local_write_sync_tview. econs; ss.
  { i. des_ifs.
    { eapply sim_view_mon_locs.
      { eapply SIM. }
      i. ss.
    }
    { eapply sim_view_mon_ver; [eapply SIM|..]; eauto. eapply VERLE. }
    { eapply SIM. }
    { eapply SIM. }
  }
  { eapply SIM. }
  { eapply SIM. }
  { i. des_ifs. }
Qed.

Lemma sim_thread_write_sync_step
      f vers flag_src flag_tgt vs_src vs_tgt
      mem_src mem_tgt lc_src0 lc_tgt0 sc_src sc_tgt
      lc_tgt1 loc ord
      (SIM: sim_thread
              f vers flag_src flag_tgt vs_src vs_tgt
              mem_src mem_tgt lc_src0 lc_tgt0 sc_src sc_tgt)
      (WRITE: local_write_sync_step lc_tgt0 loc ord lc_tgt1)
      (CONSISTENT: Local.promise_consistent lc_tgt1)
      (LOCALSRC: Local.wf lc_src0 mem_src)
      (LOCALTGT: Local.wf lc_tgt0 mem_tgt)
      (MEMSRC: Memory.closed mem_src)
      (MEMTGT: Memory.closed mem_tgt)
      (SCSRC: Memory.closed_timemap sc_src mem_src)
      (SCTGT: Memory.closed_timemap sc_tgt mem_tgt)
      (WF: Mapping.wfs f)
      (VERS: versions_wf f vers)
      (RELFLAG: forall loc (ORD: Ordering.le Ordering.strong_relaxed ord), flag_src loc = false)
  :
    exists lc_src1,
      (<<READ: local_write_sync_step lc_src0 loc ord lc_src1>>) /\
      (<<SIM: sim_thread
                f vers flag_src flag_tgt vs_src vs_tgt
                mem_src mem_tgt lc_src1 lc_tgt1 sc_src sc_tgt>>)
.
Proof.
  hexploit local_write_sync_step_future; eauto. i. des.
  esplits.
  { econs; eauto. i. inv SIM. inv LOCAL0.
    eapply sim_promises_nonsynch_loc; eauto. i. inv WRITE. eauto.
  }
  inv SIM. inv WRITE. econs; eauto.
  { inv LOCAL0. ss.
    destruct (Ordering.le Ordering.strong_relaxed ord) eqn:ORD.
    { econs.
      { eapply sim_write_sync_tview_release; eauto. }
      { eauto. }
      { inv RELVERS. econs. i. hexploit PROM; eauto.
        i. des. des_ifs; eauto. esplits; eauto.
        i. exfalso. subst.
        eapply SYNC in GET; eauto. ss.
      }
      { i. ss. eauto. }
      { i. ss. }
    }
    { econs; eauto. eapply sim_write_sync_tview_normal; eauto.
      destruct ord; ss.
    }
  }
  { ii. hexploit (MAXSRC loc0). i. inv H. econs; ss. }
  { eapply max_values_tgt_mon; eauto. }
Qed.

Lemma sim_thread_write_step_release
      f0 vers0 flag_src flag_tgt0 vs_src0 vs_tgt0
      mem_src0 mem_tgt0 lc_src0 lc_tgt0 sc_src0 sc_tgt0
      val_tgt val_src
      lc_tgt1 mem_tgt1 loc from_tgt to_tgt
      released_tgt ord sc_tgt1 kind_tgt D
      (SIM: sim_thread
              f0 vers0 flag_src flag_tgt0 vs_src0 vs_tgt0
              mem_src0 mem_tgt0 lc_src0 lc_tgt0 sc_src0 sc_tgt0)
      (WRITE: Local.write_step lc_tgt0 sc_tgt0 mem_tgt0 loc from_tgt to_tgt val_tgt None released_tgt ord lc_tgt1 sc_tgt1 mem_tgt1 kind_tgt)
      (CONSISTENT: Local.promise_consistent lc_tgt1)
      (LOCALSRC: Local.wf lc_src0 mem_src0)
      (LOCALTGT: Local.wf lc_tgt0 mem_tgt0)
      (MEMSRC: Memory.closed mem_src0)
      (MEMTGT: Memory.closed mem_tgt0)
      (SCSRC: Memory.closed_timemap sc_src0 mem_src0)
      (SCTGT: Memory.closed_timemap sc_tgt0 mem_tgt0)
      (WF: Mapping.wfs f0)
      (VERS: versions_wf f0 vers0)
      (FLAGSRC: flag_src loc = false)
      (FLAGTGT: flag_tgt0 loc = false)
      (VAL: Const.le val_tgt val_src)
      (DEBT: forall loc, (<<DEBT: D loc>>) \/
                           ((<<FLAG: flag_src loc = false -> flag_tgt0 loc = false>>) /\
                            (<<VAL: option_rel Const.le (vs_tgt0 loc) (vs_src0 loc) \/ flag_src loc = false>>)))
      lang st
  :
  exists f1 vers1 released_src lc_src1 lc_src2 vs_src1 vs_tgt1 mem_src1 mem_src2 sc_src1 kind_src from_src to_src flag_tgt1,
    (<<STEPS: rtc (tau (@pred_step is_promise _))
                    (Thread.mk lang st lc_src0 sc_src0 mem_src0)
                    (Thread.mk _ st lc_src1 sc_src0 mem_src1)>>) /\
      (<<WRITE: Local.write_step lc_src1 sc_src0 mem_src1 loc from_src to_src val_src None released_src ord lc_src2 sc_src1 mem_src2 kind_src>>) /\
      (<<SIM: sim_thread
                f1 vers1 (fun _ => false) flag_tgt1 vs_src1 vs_tgt1
                mem_src2 mem_tgt1 lc_src2 lc_tgt1 sc_src1 sc_tgt1>>) /\
      (<<WF: Mapping.wfs f1>>) /\
      (<<MAPLE: Mapping.les f0 f1>>) /\
      (<<VERSLE: versions_le vers0 vers1>>) /\
      (<<VERSWF: versions_wf f1 vers1>>) /\
      (<<VALS: forall loc0,
          ((<<SRC: vs_src1 loc0 = vs_src0 loc0>>) /\ (<<TGT: vs_tgt1 loc0 = vs_tgt0 loc0>>) /\ (<<LOC: loc0 <> loc>>)) \/
            ((<<LOC: loc0 = loc>>) /\
               ((<<VALSRC: vs_src1 loc0 = Some val_src>> /\ <<VALTGT: vs_tgt1 loc0 = Some val_tgt>>) \/
                  (<<VALSRC0: vs_src0 loc0 = None>> /\ <<VALTGT0: vs_tgt0 loc0 = None>> /\ <<VALSRC1: vs_src1 loc0 = None>> /\ <<VALTGT1: vs_tgt1 loc0 = None>>)))>>) /\
      (<<FLAG: forall loc, (<<DEBT: D loc>>) \/ (<<FLAG: flag_tgt1 loc = false>>)>>) /\
      (<<MAPFUTURE: map_future_memory f0 f1 mem_src2>>) /\
      (<<SPACE: space_future_memory (unchangable mem_tgt0 lc_tgt0.(Local.promises)) f0 mem_src0 f1 mem_src2>>)
.
Proof.
  hexploit (@sim_thread_deflag_all (fun loc0 => D loc0 /\ loc0 <> loc)); eauto.
  { eapply PromiseConsistent.write_step_promise_consistent; eauto. }
  { i. hexploit (DEBT loc0). i. des; auto.
    destruct (Loc.eq_dec loc0 loc); auto. subst. right. splits; auto.
  }
  i. des.
  hexploit local_write_step_split; eauto. i. des.
  hexploit local_write_sync_step_future; eauto. i. des.
  hexploit Thread.rtc_tau_step_future.
  { eapply rtc_implies; [|eauto]. i. inv H. inv TSTEP. econs; eauto. }
  { eauto. }
  { eauto. }
  { eauto. }
  i. des. ss.
  hexploit sim_thread_write_sync_step; eauto.
  { eapply PromiseConsistent.write_step_promise_consistent; eauto. }
  { eapply versions_wf_mapping_mon; eauto. }
  i. des.
  hexploit local_write_sync_step_future; eauto. i. des.
  hexploit sim_thread_write_step_normal; eauto.
  { eapply versions_wf_mapping_mon; eauto. }
  { specialize (FLAG loc). des; ss. }
  { destruct ord; ss. }
  i. des. esplits; eauto.
  { eapply local_write_step_merge; eauto. }
  { etrans; eauto. eapply Mapping.les_strong_les; eauto. }
  { i. specialize (FLAG loc0). des; auto. }
  { eapply map_future_memory_trans; eauto.
    { eapply map_future_memory_les_strong; eauto. }
    { eapply Local.write_step_future in WRITE0; eauto. des.
      eapply Memory.future_future_weak; auto.
    }
  }
  { eapply space_future_memory_trans; eauto.
    { inv STEP0. auto. }
    { eapply Mapping.les_strong_les; eauto. }
  }
Qed.

Lemma sim_thread_update_step_normal
      f0 vers0 flag_src flag_tgt vs_src0 vs_tgt0
      mem_src0 mem_tgt0 lc_src0 lc_tgt0 sc_src0 sc_tgt0
      valr_tgt valw_tgt valw_src
      lc_tgt1 lc_tgt2 mem_tgt1 loc from_tgt to_tgt releasedm_tgt
      released_tgt ordr ordw sc_tgt1 kind_tgt
      (SIM: sim_thread
              f0 vers0 flag_src flag_tgt vs_src0 vs_tgt0
              mem_src0 mem_tgt0 lc_src0 lc_tgt0 sc_src0 sc_tgt0)
      (READ: Local.read_step lc_tgt0 mem_tgt0 loc from_tgt valr_tgt releasedm_tgt ordr lc_tgt1)
      (WRITE: Local.write_step lc_tgt1 sc_tgt0 mem_tgt0 loc from_tgt to_tgt valw_tgt releasedm_tgt released_tgt ordw lc_tgt2 sc_tgt1 mem_tgt1 kind_tgt)
      (CONSISTENT: Local.promise_consistent lc_tgt2)
      (LOCALSRC: Local.wf lc_src0 mem_src0)
      (LOCALTGT: Local.wf lc_tgt0 mem_tgt0)
      (MEMSRC: Memory.closed mem_src0)
      (MEMTGT: Memory.closed mem_tgt0)
      (SCSRC: Memory.closed_timemap sc_src0 mem_src0)
      (SCTGT: Memory.closed_timemap sc_tgt0 mem_tgt0)
      (WF: Mapping.wfs f0)
      (VERS: versions_wf f0 vers0)
      (FLAGSRC: flag_src loc = false)
      (FLAGTGT: flag_tgt loc = false)
      (FLAG: forall loc
                    (SRC: flag_src loc = false) (TGT: flag_tgt loc = true),
          ~ Ordering.le Ordering.acqrel ordr)
      (VAL: Const.le valw_tgt valw_src)
      (ORD: ~ Ordering.le Ordering.strong_relaxed ordw)
  :
    exists f1 vers1 val_tgt1 val_src1 from_src to_src releasedm_src released_src mem_src1 lc_src1 lc_src2 vs_src1 vs_tgt1 sc_src1 kind_src,
      (<<READ: forall val (VAL: Const.le val val_src1), Local.read_step lc_src0 mem_src0 loc from_src val releasedm_src ordr lc_src1>>) /\
      (<<WRITE: Local.write_step lc_src1 sc_src0 mem_src0 loc from_src to_src valw_src releasedm_src released_src ordw lc_src2 sc_src1 mem_src1 kind_src>>) /\
      (<<WF: Mapping.wfs f1>>) /\
      (<<MAPLE: Mapping.les_strong f0 f1>>) /\
      (<<VERSLE: versions_le vers0 vers1>>) /\
      (<<VERSWF: versions_wf f1 vers1>>) /\
      (<<SIM: sim_thread
                f1 vers1 flag_src flag_tgt vs_src1 vs_tgt1
                mem_src1 mem_tgt1 lc_src2 lc_tgt2 sc_src1 sc_tgt1>>) /\
      (<<VAL: Const.le val_tgt1 val_src1>>) /\
      (<<VALTGT: Const.le valr_tgt val_tgt1>>) /\
      (<<NUPDATESRC: forall val (VAL: vs_src0 loc = Some val), val = val_src1>>) /\
      (<<NUPDATETGT: forall val (VAL: vs_tgt0 loc = Some val), val = val_tgt1>>) /\
      (<<VALS: forall loc0 (LOC: loc0 <> loc),
          ((<<SRC: vs_src1 loc0 = vs_src0 loc0>>) /\ (<<TGT: vs_tgt1 loc0 = vs_tgt0 loc0>>)) \/
          (exists val_src val_tgt,
              (<<NONESRC: vs_src0 loc0 = None>>) /\ (<<NONETGT: vs_tgt0 loc0 = None>>) /\
              (<<VALSRC: vs_src1 loc0 = Some val_src>>) /\ (<<VALTGT: vs_tgt1 loc0 = Some val_tgt>>) /\
              (<<VALLE: Const.le val_tgt val_src>>) /\
              (<<ORD: Ordering.le Ordering.acqrel ordr>>))>>) /\
      (<<UPDATED:
        __guard__(((<<SRC: vs_src1 loc = Some valw_src>>) /\ (<<TGT: vs_tgt1 loc = Some valw_tgt>>)) \/
        ((<<SRCNONE0: vs_src0 loc = None>>) /\ (<<TGTNONE0: vs_tgt0 loc = None>>) /\
         (<<SRCNONE1: vs_src1 loc = None>>) /\ (<<TGTNONE0: vs_tgt1 loc = None>>)))>>) /\
      (<<SPACE: space_future_memory (unchangable mem_tgt0 lc_tgt0.(Local.promises)) f0 mem_src0 f1 mem_src1>>)
.
Proof.
  hexploit Local.read_step_future; eauto. i. des.
  hexploit Local.write_step_future; eauto. i. des. ss.
  hexploit sim_thread_read; eauto.
  { eapply PromiseConsistent.write_step_promise_consistent; eauto. }
  i. des.
  hexploit READ0.
  { refl. }
  intros READSRC.
  hexploit Local.read_step_future; eauto. i. des.
  hexploit sim_thread_write_update_normal; eauto.
  { inv READSRC. eapply MEMSRC in GET. des. inv MSG_TS. ss. }
  i. des. esplits; eauto.
  { i. hexploit (VALS loc0). hexploit (VALS0 loc0). i. des; subst; ss.
    { left. esplits; etrans; eauto. }
    { right. esplits; eauto.
      { rewrite SRC. auto. }
      { rewrite TGT. auto. }
    }
  }
  { red. specialize (VALS loc). specialize (VALS0 loc).
    des; ss; auto. right. splits; auto.
    { rewrite <- SRC. auto. }
    { rewrite <- TGT. auto. }
  }
  { inv READ. auto. }
Qed.

Lemma sim_thread_update_step_release
      f0 vers0 flag_src flag_tgt0 vs_src0 vs_tgt0
      mem_src0 mem_tgt0 lc_src0 lc_tgt0 sc_src0 sc_tgt0
      valr_tgt valw_tgt valw_src
      lc_tgt1 lc_tgt2 mem_tgt1 loc from_tgt to_tgt releasedm_tgt
      released_tgt ordr ordw sc_tgt1 kind_tgt D
      (SIM: sim_thread
              f0 vers0 flag_src flag_tgt0 vs_src0 vs_tgt0
              mem_src0 mem_tgt0 lc_src0 lc_tgt0 sc_src0 sc_tgt0)
      (READ: Local.read_step lc_tgt0 mem_tgt0 loc from_tgt valr_tgt releasedm_tgt ordr lc_tgt1)
      (WRITE: Local.write_step lc_tgt1 sc_tgt0 mem_tgt0 loc from_tgt to_tgt valw_tgt releasedm_tgt released_tgt ordw lc_tgt2 sc_tgt1 mem_tgt1 kind_tgt)
      (CONSISTENT: Local.promise_consistent lc_tgt2)
      (LOCALSRC: Local.wf lc_src0 mem_src0)
      (LOCALTGT: Local.wf lc_tgt0 mem_tgt0)
      (MEMSRC: Memory.closed mem_src0)
      (MEMTGT: Memory.closed mem_tgt0)
      (SCSRC: Memory.closed_timemap sc_src0 mem_src0)
      (SCTGT: Memory.closed_timemap sc_tgt0 mem_tgt0)
      (WF: Mapping.wfs f0)
      (VERS: versions_wf f0 vers0)
      (FLAGSRC: flag_src loc = false)
      (FLAGTGT: flag_tgt0 loc = false)
      (FLAG: forall loc
                    (SRC: flag_src loc = false) (TGT: flag_tgt0 loc = true),
          ~ Ordering.le Ordering.acqrel ordr)
      (DEBT: forall loc, (<<DEBT: D loc>>) \/
                           ((<<FLAG: flag_src loc = false -> flag_tgt0 loc = false>>) /\
                            (<<VAL: option_rel Const.le (vs_tgt0 loc) (vs_src0 loc) \/ flag_src loc = false>>)))
      (VAL: Const.le valw_tgt valw_src)
      lang st
  :
    exists val_src1 f1 vers1 val_tgt1 from_src to_src releasedm_src released_src mem_src1 mem_src2 lc_src1 lc_src2 lc_src3 vs_src1 vs_tgt1 sc_src1 kind_src flag_tgt1,
      (<<STEPS: rtc (tau (@pred_step is_promise _))
                    (Thread.mk lang st lc_src0 sc_src0 mem_src0)
                    (Thread.mk _ st lc_src1 sc_src0 mem_src1)>>) /\
      (<<READ: forall val (VAL: Const.le val val_src1), Local.read_step lc_src1 mem_src1 loc from_src val releasedm_src ordr lc_src2>>) /\
      (<<WRITE: Local.write_step lc_src2 sc_src0 mem_src1 loc from_src to_src valw_src releasedm_src released_src ordw lc_src3 sc_src1 mem_src2 kind_src>>) /\
      (<<WF: Mapping.wfs f1>>) /\
      (<<MAPLE: Mapping.les f0 f1>>) /\
      (<<VERSLE: versions_le vers0 vers1>>) /\
      (<<VERSWF: versions_wf f1 vers1>>) /\
      (<<SIM: sim_thread
                f1 vers1 (fun _ => false) flag_tgt1 vs_src1 vs_tgt1
                mem_src2 mem_tgt1 lc_src3 lc_tgt2 sc_src1 sc_tgt1>>) /\
      (<<VAL: Const.le val_tgt1 val_src1>>) /\
      (<<VALTGT: Const.le valr_tgt val_tgt1>>) /\
      (<<NUPDATESRC: forall val (VAL: vs_src0 loc = Some val), val = val_src1>>) /\
      (<<NUPDATETGT: forall val (VAL: vs_tgt0 loc = Some val), val = val_tgt1>>) /\
      (<<VALS: forall loc0 (LOC: loc0 <> loc),
          ((<<SRC: vs_src1 loc0 = vs_src0 loc0>>) /\ (<<TGT: vs_tgt1 loc0 = vs_tgt0 loc0>>)) \/
          (exists val_src val_tgt,
              (<<NONESRC: vs_src0 loc0 = None>>) /\ (<<NONETGT: vs_tgt0 loc0 = None>>) /\
              (<<VALSRC: vs_src1 loc0 = Some val_src>>) /\ (<<VALTGT: vs_tgt1 loc0 = Some val_tgt>>) /\
              (<<VALLE: Const.le val_tgt val_src>>) /\
              (<<ORD: Ordering.le Ordering.acqrel ordr>>))>>) /\
      (<<UPDATED:
        __guard__(((<<SRC: vs_src1 loc = Some valw_src>>) /\ (<<TGT: vs_tgt1 loc = Some valw_tgt>>)) \/
        ((<<SRCNONE0: vs_src0 loc = None>>) /\ (<<TGTNONE0: vs_tgt0 loc = None>>) /\
           (<<SRCNONE1: vs_src1 loc = None>>) /\ (<<TGTNONE0: vs_tgt1 loc = None>>)))>>) /\
      (<<FLAG: forall loc, (<<DEBT: D loc>>) \/ (<<FLAG: flag_tgt1 loc = false>>)>>) /\
      (<<MAPFUTURE: map_future_memory f0 f1 mem_src2>>) /\
      (<<SPACE: space_future_memory (unchangable mem_tgt0 lc_tgt0.(Local.promises)) f0 mem_src0 f1 mem_src2>>)
.
Proof.
  assert (CONSISTENT0: Local.promise_consistent lc_tgt1).
  { eapply PromiseConsistent.write_step_promise_consistent; eauto. }
  eapply local_write_step_split in WRITE. des.
  hexploit Local.read_step_future; eauto. i. des.
  hexploit local_write_sync_step_future; eauto. i. des.
  hexploit Local.write_step_future; eauto. i. des. ss.
  hexploit sim_thread_read; eauto. i. des.
  hexploit READ0.
  { refl. }
  intros READSRC.
  hexploit Local.read_step_future; eauto. i. des.
  hexploit (@sim_thread_deflag_all (fun loc0 => D loc0 /\ loc0 <> loc)); eauto.
  { i. destruct (Loc.eq_dec loc0 loc).
    { right. subst. splits; auto. }
    hexploit (DEBT loc0). i. des; auto. right. splits; auto.
    hexploit (VALS loc0). i. des.
    { rewrite SRC. rewrite TGT. auto. }
    { left. rewrite VALTGT0. rewrite VALSRC. ss. }
    { left. rewrite VALTGT0. rewrite VALSRC. ss. }
  }
  i. des. hexploit Thread.rtc_tau_step_future.
  { eapply rtc_implies; [|eauto]. i. inv H. inv TSTEP. econs; eauto. }
  { eauto. }
  { eauto. }
  { eauto. }
  ss. i. des.
  hexploit sim_thread_write_sync_step; eauto.
  { eapply PromiseConsistent.write_step_promise_consistent; eauto. }
  { eapply versions_wf_mapping_mon; eauto. }
  i. des.
  hexploit local_write_sync_step_future; eauto. i. des.
  assert (RELEASEDM: sim_opt_view (fun loc0 => loc0 <> loc) f1 (vers0 loc from_tgt) released_src releasedm_tgt).
  { erewrite <- sim_opt_view_mon_mapping; eauto. }
  hexploit sim_thread_write_update_normal; eauto.
  { instantiate (1:=to_src). inv READSRC. eapply MEMSRC in GET. des. inv MSG_TS. ss. }
  { rewrite UNCH; auto. }
  { eapply versions_wf_mapping_mon; eauto. }
  { specialize (FLAG0 loc). des; ss. }
  { destruct ordw; ss. }
  { eapply Memory.future_weak_closed_opt_view; eauto.
    eapply Memory.future_future_weak; eauto.
  }
  i. des.
  hexploit promise_steps_local_read_step; eauto.
  { eapply sim_local_consistent_ex.
    { eapply CONSISTENT0. }
    { inv SIM1. eauto. }
    { eauto. }
  }
  i. des. exists val_src1. esplits; eauto.
  { inv READ2. i. econs; eauto. etrans; eauto. }
  { eapply local_write_step_merge; eauto. }
  { etrans; eauto. eapply Mapping.les_strong_les; eauto. }
  { i. hexploit (VALS loc0). hexploit (VALS0 loc0). i. des; subst; ss.
    { left. esplits; etrans; eauto. }
    { right. esplits; eauto.
      { rewrite SRC. auto. }
      { rewrite TGT. auto. }
    }
  }
  { red. specialize (VALS loc). specialize (VALS0 loc).
    des; ss; auto. right. splits; auto.
    { rewrite <- SRC. auto. }
    { rewrite <- TGT. auto. }
  }
  { i. specialize (FLAG0 loc0). des; auto. }
  { eapply map_future_memory_trans; eauto.
    { eapply map_future_memory_les_strong; eauto. }
    { eapply Local.write_step_future in WRITE; eauto.
      { des. eapply Memory.future_future_weak; auto. }
      { eapply Memory.future_closed_opt_view; eauto. }
    }
  }
  { eapply space_future_memory_trans.
    { inv READ. eauto. }
    { inv READ. inv STEP0. eauto. }
    { eauto. }
    { eapply Mapping.les_strong_les; eauto. }
    { eauto. }
    { eauto. }
    { eauto. }
  }
Qed.

Lemma semi_closed_timemap_closed
      tm mem loc ts
      (SEMI: semi_closed_timemap tm mem loc ts)
      (CLOSED: exists from val released, Memory.get loc ts mem = Some (from, Message.concrete val released))
  :
  Memory.closed_timemap tm mem.
Proof.
  ii. exploit SEMI. i. des; eauto.
  subst. esplits; eauto.
Qed.

Lemma semi_closed_view_closed
      vw mem loc ts
      (SEMI: semi_closed_view vw mem loc ts)
      (CLOSED: exists from val released, Memory.get loc ts mem = Some (from, Message.concrete val released))
  :
  Memory.closed_view vw mem.
Proof.
  econs.
  { eapply semi_closed_timemap_closed; eauto. eapply SEMI. }
  { eapply semi_closed_timemap_closed; eauto. eapply SEMI. }
Qed.

Lemma semi_closed_opt_view_closed
      vw mem loc ts
      (SEMI: semi_closed_opt_view vw mem loc ts)
      (CLOSED: exists from val released, Memory.get loc ts mem = Some (from, Message.concrete val released))
  :
  Memory.closed_opt_view vw mem.
Proof.
  inv SEMI; econs.
  eapply semi_closed_view_closed; eauto.
Qed.

Lemma semi_closed_message_closed
      msg mem loc ts
      (SEMI: semi_closed_message msg mem loc ts)
      (CLOSED: forall val released (MSG: msg = Message.concrete val released),
        exists from val released, Memory.get loc ts mem = Some (from, Message.concrete val released))
  :
  Memory.closed_message msg mem.
Proof.
  inv SEMI; econs.
  eapply semi_closed_opt_view_closed; eauto.
Qed.

Lemma sim_thread_promise_step
      f0 vers0 flag_src flag_tgt vs_src vs_tgt
      mem_src0 mem_tgt0 lc_src0 lc_tgt0 sc_src sc_tgt
      lc_tgt1 mem_tgt1 loc from_tgt to_tgt
      msg_tgt kind_tgt
      (SIM: sim_thread
              f0 vers0 flag_src flag_tgt vs_src vs_tgt
              mem_src0 mem_tgt0 lc_src0 lc_tgt0 sc_src sc_tgt)
      (PROMISE: Local.promise_step lc_tgt0 mem_tgt0 loc from_tgt to_tgt msg_tgt lc_tgt1 mem_tgt1 kind_tgt)
      (CONSISTENT: Local.promise_consistent lc_tgt1)
      (LOCALSRC: Local.wf lc_src0 mem_src0)
      (LOCALTGT: Local.wf lc_tgt0 mem_tgt0)
      (MEMSRC: Memory.closed mem_src0)
      (MEMTGT: Memory.closed mem_tgt0)
      (SCSRC: Memory.closed_timemap sc_src mem_src0)
      (SCTGT: Memory.closed_timemap sc_tgt mem_tgt0)
      (WF: Mapping.wfs f0)
      (VERS: versions_wf f0 vers0)
      (FLAGSRC: flag_src loc = false)
  :
  exists f1 vers1 from_src to_src msg_src lc_src1 mem_src1 kind_src,
    (<<PROMISE: Local.promise_step lc_src0 mem_src0 loc from_src to_src msg_src lc_src1 mem_src1 kind_src>>) /\
    (<<SIM: sim_thread
              f1 vers1 flag_src flag_tgt vs_src vs_tgt
              mem_src1 mem_tgt1 lc_src1 lc_tgt1 sc_src sc_tgt>>) /\
    (<<WF: Mapping.wfs f1>>) /\
    (<<MAPLE: Mapping.les_strong f0 f1>>) /\
    (<<VERSLE: versions_le vers0 vers1>>) /\
    (<<VERSWF: versions_wf f1 vers1>>) /\
    (<<SPACE: space_future_memory (unchangable mem_tgt0 lc_tgt0.(Local.promises)) f0 mem_src0 f1 mem_src1>>)
.
Proof.
  inv SIM. inv LOCAL. inv PROMISE.
  hexploit sim_memory_promise; eauto.
  { eapply LOCALSRC. }
  { eapply TVIEW. }
  i. des.
  assert (MAPLES: Mapping.les f0 f1).
  { eapply Mapping.les_strong_les; eauto. }
  esplits; eauto.
  { econs; eauto. hexploit sim_closed_memory_sim_message; eauto. i.
    eapply semi_closed_message_closed; eauto. i. subst.
    eapply Memory.promise_get0 in CANCEL.
    { des; eauto. }
    { inv CANCEL; ss. }
  }
  { econs; eauto; ss.
    { eapply sim_timemap_mon_latest; eauto. }
    { econs; eauto. ss. eapply sim_tview_mon_latest; eauto. }
    { ii. specialize (MAXSRC loc0). inv MAXSRC.
      destruct (Loc.eq_dec loc0 loc).
      { subst. econs.
        { i. hexploit MAX; eauto. i. des.
          esplits. erewrite <- promise_max_readable; eauto.
        }
        { ii. eapply NONMAX; auto. erewrite promise_max_readable; eauto. }
      }
      { eapply promise_unchanged_loc in CANCEL; eauto.
        des. econs.
        { i. hexploit MAX; eauto. i. des.
          esplits. erewrite <- unchanged_loc_max_readable; eauto.
        }
        { ii. eapply NONMAX; auto. erewrite unchanged_loc_max_readable; eauto. }
      }
    }
    { ii. specialize (MAXTGT loc0). inv MAXTGT.
      destruct (Loc.eq_dec loc0 loc).
      { subst. econs.
        i. hexploit MAX; eauto. i. des.
        esplits. erewrite <- promise_max_readable; eauto.
      }
      { eapply promise_unchanged_loc in PROMISE0; eauto.
        des. econs. i. hexploit MAX; eauto. i. des.
        esplits. erewrite <- unchanged_loc_max_readable; eauto.
      }
    }
    { i. assert (NEQ: loc0 <> loc).
      { ii. subst. rewrite FLAG in *. ss. }
      rewrite MAXTIMES; auto. eapply unchanged_loc_max_ts.
      2:{ eapply MEMSRC. }
      { eapply promise_unchanged_loc in CANCEL; eauto. des; eauto. }
    }
    { eapply reserved_space_empty_mon_strong; eauto.
      eapply reserved_space_empty_reserve_decr.
      { eapply reserved_space_empty_covered_decr; eauto.
        i. eapply promise_unchanged_loc in CANCEL.
        { des. inv MEM1. inv COVER. erewrite UNCH in GET. econs; eauto. }
        { ii. subst. rewrite FLAG in *. ss. }
      }
      { i. eapply promise_unchanged_loc in PROMISE0.
        { des. inv PROM0. erewrite UNCH in GET. eauto. }
        { ii. subst. rewrite FLAG in *. ss. }
      }
    }
  }
Qed.

Lemma sim_thread_racy_write_step
      f vers flag_src flag_tgt vs_src vs_tgt
      mem_src mem_tgt lc_src lc_tgt sc_src sc_tgt
      loc to_tgt ord
      (SIM: sim_thread
              f vers flag_src flag_tgt vs_src vs_tgt
              mem_src mem_tgt lc_src lc_tgt sc_src sc_tgt)
      (CONSISTENT: Local.promise_consistent lc_tgt)
      (RACE: Local.racy_write_step lc_tgt mem_tgt loc to_tgt ord)
      (FLAGSRC: flag_src loc = false)
      (FLAGTGT: flag_tgt loc = false)
      (WF: Mapping.wfs f)
  :
  exists to_src, Local.racy_write_step lc_src mem_src loc to_src ord.
Proof.
  inv SIM. inv RACE.
  exploit sim_local_racy; eauto. i. des.
  esplits. econs; eauto.
  eapply sim_local_consistent; eauto.
Qed.

Lemma sim_thread_racy_update_step
      f vers flag_src flag_tgt vs_src vs_tgt
      mem_src mem_tgt lc_src lc_tgt sc_src sc_tgt
      loc to_tgt ordr ordw
      (SIM: sim_thread
              f vers flag_src flag_tgt vs_src vs_tgt
              mem_src mem_tgt lc_src lc_tgt sc_src sc_tgt)
      (CONSISTENT: Local.promise_consistent lc_tgt)
      (RACE: Local.racy_update_step lc_tgt mem_tgt loc to_tgt ordr ordw)
      (FLAGSRC: flag_src loc = false)
      (FLAGTGT: flag_tgt loc = false)
      (WF: Mapping.wfs f)
  :
  exists to_src, Local.racy_update_step lc_src mem_src loc to_src ordr ordw.
Proof.
  inv SIM. inv RACE.
  { esplits. econs 1; eauto. eapply sim_local_consistent; eauto. }
  { esplits. econs 2; eauto. eapply sim_local_consistent; eauto. }
  { exploit sim_local_racy; eauto. i. des.
    esplits. econs 3; eauto.
    eapply sim_local_consistent; eauto.
  }
Qed.

Lemma sim_thread_racy_read_step
      f vers flag_src flag_tgt vs_src vs_tgt
      mem_src mem_tgt lc_src lc_tgt sc_src sc_tgt
      loc to_tgt val_tgt ord
      (SIM: sim_thread
              f vers flag_src flag_tgt vs_src vs_tgt
              mem_src mem_tgt lc_src lc_tgt sc_src sc_tgt)
      (READ: Local.racy_read_step lc_tgt mem_tgt loc to_tgt val_tgt ord)
      (CONSISTENT: Local.promise_consistent lc_tgt)
      (WF: Mapping.wfs f)
      (FLAGSRC: flag_src loc = false)
      (FLAGTGT: flag_tgt loc = false)
  :
    forall val_src,
      exists to_src, Local.racy_read_step lc_src mem_src loc to_src val_src ord.
Proof.
  inv SIM. inv READ. inv RACE.
  exploit sim_local_racy; eauto. i. des.
  esplits. econs; eauto.
Qed.
