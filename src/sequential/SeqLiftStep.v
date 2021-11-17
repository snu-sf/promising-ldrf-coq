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

Require Import SeqLift.
(* Require Import Simple. *)


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

Record sim_tview
       (f: Mapping.ts)
       (flag_src: Loc.t -> option Time.t)
       (rel_vers: Loc.t -> version)
       (tvw_src: TView.t) (tvw_tgt: TView.t)
  :
    Prop :=
  sim_tview_intro {
      sim_tview_rel: forall loc,
        sim_view (fun loc0 => loc0 <> loc) f (rel_vers loc) (tvw_src.(TView.rel) loc) (tvw_tgt.(TView.rel) loc);
      sim_tview_cur: sim_view (fun loc => flag_src loc = None) f (Mapping.vers f) tvw_src.(TView.cur) tvw_tgt.(TView.cur);
      sim_tview_acq: sim_view (fun loc => flag_src loc = None) f (Mapping.vers f) tvw_src.(TView.acq) tvw_tgt.(TView.acq);
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

Variant wf_release_vers (vers: versions) (prom_tgt: Memory.t) (rel_vers: Loc.t -> version): Prop :=
| wf_release_vers_intro
    (PROM: forall loc from to val released
                  (GET: Memory.get loc to prom_tgt = Some (from, Message.concrete val (Some released))),
        exists v,
          (<<VER: vers loc to = Some v>>) /\
          (<<REL: rel_vers loc = v>>))
.

Variant sim_local
        (f: Mapping.ts) (vers: versions)
        (flag_src: Loc.t -> option Time.t)
        (flag_tgt: Loc.t -> option Time.t)
  :
    Local.t -> Local.t -> Prop :=
| sim_local_intro
    tvw_src tvw_tgt prom_src prom_tgt rel_vers
    (TVIEWW: sim_tview f flag_src rel_vers tvw_src tvw_tgt)
    (PROMISES: sim_promises flag_src flag_tgt f vers prom_src prom_tgt)
    (RELVERS: wf_release_vers vers prom_tgt rel_vers)
    (FLAGTGT: forall loc ts (FLAG: flag_tgt loc = Some ts),
        tvw_src.(TView.cur).(View.rlx) loc = ts)
    (FLAGSRC: forall loc ts (FLAG: flag_src loc = Some ts),
        tvw_src.(TView.cur).(View.rlx) loc = ts)
  :
    sim_local
      f vers flag_src flag_tgt
      (Local.mk tvw_src prom_src)
      (Local.mk tvw_tgt prom_tgt)
.

Lemma sim_local_tgt_mon f vers flag_src flag_tgt lc_src lc_tgt0 lc_tgt1
      (SIM: sim_local f vers flag_src flag_tgt lc_src lc_tgt0)
      (PROM: lc_tgt0.(Local.promises) = lc_tgt1.(Local.promises))
      (TVIEW: TView.le lc_tgt0.(Local.tview) lc_tgt1.(Local.tview))
  :
    sim_local f vers flag_src flag_tgt lc_src lc_tgt1.
Proof.
  inv SIM. destruct lc_tgt1. ss. clarify. econs; eauto.
  eapply sim_tview_tgt_mon; eauto.
Qed.

Lemma sim_local_consistent f vers flag_src flag_tgt lc_src lc_tgt
      (CONSISTENT: Local.promise_consistent lc_tgt)
      (SIM: sim_local f vers flag_src flag_tgt lc_src lc_tgt)
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
        erewrite sim_promises_none in PROMISE; eauto. ss.
      }
    }
    { eauto. }
    { eapply CONSISTENT; eauto. inv MSG0; ss. }
    { eauto. }
    { eapply mapping_latest_wf_loc. }
  }
  { eapply FLAGTGT in FLAG. subst. auto. }
Qed.

Variant max_values_src (vs: Loc.t -> option Const.t)
        (mem: Memory.t)
  :
    forall (lc: Local.t), Prop :=
| max_values_src_intro
    tvw prom
    (MAX: forall loc v0 (VAL: vs loc = Some v0),
        exists released v1,
          (<<MAX: max_readable
                    mem
                    prom
                    loc
                    (tvw.(TView.cur).(View.pln) loc)
                    v1 released>>) /\
          (<<VAL: Const.le v0 v1>>))
    (NONMAX: forall loc (VAL: vs loc = None),
        forall val released,
          ~ max_readable mem prom loc (tvw.(TView.cur).(View.pln) loc) val released)
  :
    max_values_src vs mem (Local.mk tvw prom)
.

Variant max_values_tgt (vs: Loc.t -> option Const.t)
        (mem: Memory.t)
  :
    forall (lc: Local.t), Prop :=
| max_values_tgt_intro
    tvw prom
    (MAX: forall loc v1 (VAL: vs loc = Some v1),
        exists released v0,
          (<<MAX: max_readable
                    mem
                    prom
                    loc
                    (tvw.(TView.cur).(View.pln) loc)
                    v0 released>>) /\
          (<<VAL: Const.le v0 v1>>))
  :
    max_values_tgt vs mem (Local.mk tvw prom)
.

Lemma max_values_tgt_mon vs mem lc0 lc1
      (MAXTGT: max_values_tgt vs mem lc0)
      (PROM: lc0.(Local.promises) = lc1.(Local.promises))
      (TVIEW: TView.le lc0.(Local.tview) lc1.(Local.tview))
      (LOCAL: Local.wf lc1 mem)
      (CONSISTENT: Local.promise_consistent lc1)
  :
    max_values_tgt vs mem lc1.
Proof.
  inv MAXTGT. ss. subst. destruct lc1. econs. i.
  hexploit MAX; eauto. i. des. ss.
  hexploit max_readable_view_mon; eauto.
Qed.

Variant sim_thread
        (f: Mapping.ts) (vers: versions)
        (flag_src: Loc.t -> option Time.t)
        (flag_tgt: Loc.t -> option Time.t)
        (vs_src: Loc.t -> option Const.t)
        (vs_tgt: Loc.t -> option Const.t)
        mem_src mem_tgt lc_src lc_tgt sc_src sc_tgt: Prop :=
| sim_thread_intro
    (SC: sim_timemap (fun _ => True) f (Mapping.vers f) sc_src sc_tgt)
    (MEM: sim_memory flag_src f vers mem_src mem_tgt)
    (LOCAL: sim_local f vers flag_src flag_tgt lc_src lc_tgt)
    (MAXSRC: max_values_src vs_src mem_src lc_src)
    (MAXTGT: max_values_tgt vs_tgt mem_tgt lc_tgt)
    (PERM: forall loc, option_rel (fun _ _ => True) (vs_src loc) (vs_tgt loc))
.

Lemma sim_thread_tgt_read_na
      f vers flag_src flag_tgt vs_src vs_tgt
      mem_src mem_tgt lc_src lc_tgt0 sc_src sc_tgt
      loc to_tgt val_tgt vw_tgt lc_tgt1
      (READ: Local.read_step lc_tgt0 mem_tgt loc to_tgt val_tgt vw_tgt Ordering.na lc_tgt1)
      (SIM: sim_thread
              f vers flag_src flag_tgt vs_src vs_tgt
              mem_src mem_tgt lc_src lc_tgt0 sc_src sc_tgt)
      (CONSISTNET: Local.promise_consistent lc_tgt1)
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
  }
  { i. inv SIM. inv MAXTGT.
    hexploit MAX; eauto. i. des.
    hexploit max_readable_read_only; eauto.
    i. des; auto. etrans; eauto.
  }
Qed.

Lemma sim_thread_tgt_read_na_racy
      f vers flag_src flag_tgt vs_src vs_tgt
      mem_src mem_tgt lc_src lc_tgt0 sc_src sc_tgt
      loc val_tgt ord
      (READ: Local.racy_read_step lc_tgt0 mem_tgt loc val_tgt ord)
      (SIM: sim_thread
              f vers flag_src flag_tgt vs_src vs_tgt
              mem_src mem_tgt lc_src lc_tgt0 sc_src sc_tgt)
      (LOCAL: Local.wf lc_tgt0 mem_tgt)
  :
    vs_tgt loc = None.
Proof.
  destruct (vs_tgt loc) eqn:VAL; auto.
  inv SIM. inv MAXTGT. hexploit MAX; eauto. i. des.
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
  inv SIM. inv MAXSRC. hexploit MAX; eauto. i. des.
  hexploit max_readable_read.
  { eauto. }
  { eauto. }
  { eauto. }
  { instantiate (1:=val_src). etrans; eauto. }
  i. des. esplits; eauto.
Qed.

Lemma sim_thread_src_read_na_racy
      f vers flag_src flag_tgt vs_src vs_tgt
      mem_src mem_tgt lc_src lc_tgt sc_src sc_tgt
      loc val_src
      (SIM: sim_thread
              f vers flag_src flag_tgt vs_src vs_tgt
              mem_src mem_tgt lc_src lc_tgt sc_src sc_tgt)
      (CONSISTNET: Local.promise_consistent lc_tgt)
      (LOCAL: Local.wf lc_src mem_src)
      (VALS: vs_src loc = None)
      (WF: Mapping.wfs f)
  :
    Local.racy_read_step lc_src mem_src loc val_src Ordering.na.
Proof.
  inv SIM. inv MAXSRC.
  hexploit non_max_readable_read; eauto.
  eapply sim_local_consistent; eauto.
Qed.

Lemma sim_thread_tgt_write_na_racy
      f vers flag_src flag_tgt vs_src vs_tgt
      mem_src mem_tgt lc_src lc_tgt0 sc_src sc_tgt
      loc
      (WRITE: Local.racy_write_step lc_tgt0 mem_tgt loc Ordering.na)
      (SIM: sim_thread
              f vers flag_src flag_tgt vs_src vs_tgt
              mem_src mem_tgt lc_src lc_tgt0 sc_src sc_tgt)
      (LOCAL: Local.wf lc_tgt0 mem_tgt)
  :
    vs_tgt loc = None.
Proof.
  destruct (vs_tgt loc) eqn:VAL; auto.
  inv SIM. inv MAXTGT. hexploit MAX; eauto. i. des.
  exfalso. eapply max_readable_not_write_race; eauto.
Qed.

Lemma sim_thread_src_write_na_racy
      f vers flag_src flag_tgt vs_src vs_tgt
      mem_src mem_tgt lc_src lc_tgt sc_src sc_tgt
      loc
      (SIM: sim_thread
              f vers flag_src flag_tgt vs_src vs_tgt
              mem_src mem_tgt lc_src lc_tgt sc_src sc_tgt)
      (CONSISTNET: Local.promise_consistent lc_tgt)
      (LOCAL: Local.wf lc_src mem_src)
      (VALS: vs_src loc = None)
      (WF: Mapping.wfs f)
  :
    Local.racy_write_step lc_src mem_src loc Ordering.na.
Proof.
  inv SIM. inv MAXSRC.
  hexploit non_max_readable_write; eauto.
  eapply sim_local_consistent; eauto.
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
  inv MAX. econs.
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
  inv MAX. econs.
  i. hexploit MAX0; eauto. i. des. esplits; eauto.
  erewrite <- cap_max_readable; eauto. eapply LOCAL.
Qed.

Lemma sim_promises_preserve
      prom_src prom_tgt flag_src flag_tgt f0 f1 vers mem
      (SIM: sim_promises flag_src flag_tgt f0 vers prom_src prom_tgt)
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
    sim_promises flag_src flag_tgt f1 vers prom_src prom_tgt.
Proof.
  econs.
  { i. hexploit sim_promises_get; eauto. i. des. esplits.
    { eapply PRESERVE; eauto. eapply memory_get_ts_le; eauto. }
    { eapply PRESERVE; eauto. refl. }
    { eauto. }
    { erewrite <- sim_message_max_mon_mapping; eauto. }
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
              f0 vers (fun _ => None) flag_tgt vs_src vs_tgt
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
                f1 vers (fun _ => None) flag_tgt vs_src vs_tgt
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

Lemma sim_view_singleton_ur_if l (L: Loc.t -> Prop) f v
      ts_src ts_tgt cond
      (SIM: L l -> sim_timestamp (f l) (v l) ts_src ts_tgt)
      (WF: Mapping.wfs f)
      (VERWF: version_wf f v)
  :
    sim_view L f v (View.singleton_ur_if cond l ts_src) (View.singleton_ur_if cond l ts_tgt).
Proof.
  unfold View.singleton_ur_if. des_ifs.
  { eapply sim_view_singleton_ur; eauto. }
  { eapply sim_view_singleton_rw; eauto. }
Qed.

Lemma message_to_time_le_opt_view loc to val released
      (MSGTO: Memory.message_to (Message.concrete val released) loc to)
  :
    time_le_opt_view loc to released.
Proof.
  invMS

      loc to


time_le_opt_view

Lemma sim_read_tview f flag_src flag_tgt tvw_src tvw_tgt
      loc to_src released_src ord to_tgt released_tgt
      (SIM: sim_tview f flag_src flag_tgt tvw_src tvw_tgt)
      (TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src to_tgt)
      (CLOSED: Mapping.closed (f loc) (Mapping.vers f loc) to_src)
      (WF: Mapping.wfs f)
  :
    sim_tview f flag_src flag_tgt (TView.read_tview tvw_src loc to_src released_src ord) (TView.read_tview tvw_tgt loc to_tgt released_tgt ord).
Proof.
  pose proof (mapping_latest_wf f).
  econs.
  { eapply SIM. }
  { ss. rewrite View.join_assoc. rewrite View.join_assoc.
    eapply sim_view_join; eauto.
    { eapply SIM. }
    unfold View.singleton_ur_if. des_ifs.
    { admit. }
    { admit. }
    { destruct ord; ss. }
    { admit. }
  }

    {


eapply sim_view_join; eauto.
      { eapply SIM. }
      { eapply sim_view_singleton_ur_if; eauto.
        i. eapply sim_timestamp_exact_sim; eauto.
      }
    }
    { des_ifs.
      { admit. }
      { eapply sim_view_join; eauto.
        { eapply sim_view_join; eauto.
          { eapply SIM. }
          { ss. eapply sim_view_singleton_rw; eauto.
            i. eapply sim_timestamp_exact_sim; eauto.
          }
        }
        { eapply sim_view_bot; eauto. }
      }
    }
    { eapply SIM. }
Admitted.

Lemma sim_thread_read
      f vers flag_src flag_tgt vs_src0 vs_tgt0
      mem_src mem_tgt lc_src0 lc_tgt0 sc_src sc_tgt
      loc to_tgt val released_tgt ord lc_tgt1
      (READ: Local.read_step lc_tgt0 mem_tgt loc to_tgt val released_tgt ord lc_tgt1)
      (SIM: sim_thread
              f vers flag_src flag_tgt vs_src0 vs_tgt0
              mem_src mem_tgt lc_src0 lc_tgt0 sc_src sc_tgt)
      (CONSISTNET: Local.promise_consistent lc_tgt1)
      (LOCAL: Local.wf lc_tgt0 mem_tgt)
      (MEM: Memory.closed mem_tgt)
      (FLAGSRC: flag_src loc = None)
      (FLAGTGT: flag_tgt loc = None)
      (ACQ: forall loc (ORD: Ordering.le Ordering.acqrel ord)
                   (FLAG: flag_src loc = None),
          flag_tgt loc = None)
      (WF: Mapping.wfs f)
  :
    exists lc_src1 to_src released_src vs_src1 vs_tgt1,
      (<<READ: Local.read_step lc_src0 mem_src loc to_src val released_src ord lc_src1>>) /\
      (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src to_tgt>>) /\
      (<<RELEASED: sim_opt_view (fun loc0 => loc0 <> loc) f (vers loc to_tgt) released_src released_tgt>>) /\
      (<<SIM: sim_thread
                f vers flag_src flag_tgt vs_src1 vs_tgt1
                mem_src mem_tgt lc_src0 lc_tgt1 sc_src sc_tgt>>)
.
Proof.
  inv READ. inv SIM.
  hexploit sim_memory_get; eauto; ss. i. des.
  inv MSG; ss. esplits.
  { econs; ss.
    { eauto. }
    { etrans; eauto. }
    { inv LOCAL0. eapply sim_readable; eauto.
      { eapply sim_tview_cur. eauto. }
      { ss. }
    }
  }
  { eauto. }
  { rewrite H0. admit. }
  { econs; eauto.
    { inv LOCAL0. econs; eauto. ss. admit. }
    { admit. }
  }
Admitted.

Lemma sim_thread_tgt_write_na
      f vers flag_src flag_tgt vs_src vs_tgt
      mem_src mem_tgt0 lc_src lc_tgt0 sc_src sc_tgt0
      loc from_tgt to_tgt val_tgt lc_tgt1 sc_tgt1 mem_tgt1 msgs kinds kind
      (WRITE: Local.write_na_step lc_tgt0 sc_tgt0 mem_tgt0 loc from_tgt to_tgt val_tgt Ordering.na lc_tgt1 sc_tgt1 mem_tgt1 msgs kinds kind)
      (SIM: sim_thread
              f vers flag_src flag_tgt vs_src vs_tgt
              mem_src mem_tgt0 lc_src lc_tgt0 sc_src sc_tgt0)
      (CONSISTNET: Local.promise_consistent lc_tgt1)
      (LOCAL: Local.wf lc_tgt0 mem_tgt0)
      (MEM: Memory.closed mem_tgt0)
      (VAL: vs_tgt loc <> None)
      (LOWER: mem_tgt1 = mem_tgt0)
  :
    sim_thread
      f vers flag_src flag_tgt vs_src
      (fun loc0 => if Loc.eq_dec loc0 loc then (Some val_tgt) else (vs_tgt loc0))
      mem_src mem_tgt1 lc_src lc_tgt1 sc_src sc_tgt1.
Proof.
  inv SIM. econs; eauto.
  { inv WRITE. eauto. }
  { inv WRITE. econs; eauto. ss. inv LOCAL. econs.

admit. }
  { admit. }
  { i. specialize (PERM loc0). unfold option_rel in *. des_ifs. }
Qed.

    inv PERM.

  econs.



  hexploit Local.read_step_future; eauto.
  i. des. splits.
  { inv SIM. econs; eauto.
    { eapply sim_local_tgt_mon; eauto.
      { inv READ; ss. }
    }
    { eapply max_values_tgt_mon; eauto.
      { inv READ; ss. }
    }
  }
  { i. inv SIM. inv MAXTGT.
    hexploit MAX; eauto. i. des.
    hexploit max_readable_read_only; eauto.
    i. des. auto.
  }
Qed.




  | future
  | promise
  | cap (done)
  | promise_to_max_match
  | promise_to_max_unmatch

  | na_read_src (done)
  | na_read_tgt (done)
  | na_racy_read_src (done)
  | na_racy_read_tgt (done)
  | na_write_src
  | na_write_tgt
  | na_racy_write_src (done)
  | na_racy_write_tgt (done)

  | step_silent (done)
  | step_read
  | step_write
  | step_update
  | step_fence
  | step_syscall

  | step_failure (done)




  Lemma sim_thread_cap
        f0 vers flag_src flag_tgt vs_src vs_tgt
        mem_src mem_tgt lc_src lc_tgt sc_src sc_tgt
        cap_src cap_tgt
        (SIM: sim_thread
                f vers flag_src flag_tgt vs_src vs_tgt
                mem_src mem_tgt lc_src lc_tgt sc_src sc_tgt)
        (CAPSRC: Memory.cap_tgt mem_src cap_src)
        (CAPTGT: Memory.cap_tgt mem_tgt cap_tgt)
    :
      exists f1,
        (<<MAPLE: Mapping.le f0 f1>>) /\
        (<<MAPWF: Mapping.wf f1>>) /\
        (<<SIM: sim_thread
                  f vers flag_src flag_tgt vs_src vs_tgt
                  mem_src mem_tgt lc_src lc_tgt sc_src sc_tgt>>).


read


  Variant sim_thread
          (f: Mapping.ts) (vers: versions)
          (flag_src: Loc.t -> option Time.t)
          (flag_tgt: Loc.t -> option Time.t)
          (vs: Loc.t -> option (Time.t * Time.t))
          (st_src: lang_src.(Language.state))
          (st_tgt: lang_tgt.(Language.state))
    :
      forall
        (th_src: Thread.t lang_src)
        (th_tgt: Thread.t lang_tgt), Prop :=
  | sim_thread_intro
      mem_src mem_tgt lc_src lc_tgt sc_src sc_tgt
      (SC: sim_timemap (fun _ => True) f (Mapping.vers f) sc_src sc_tgt)
      (MEM: sim_memory flag_src f vers mem_src mem_tgt)
      (LOCAL: sim_local f vers flag_src flag_tgt lc_src lc_tgt)
      (FLAGTGT: forall loc ts (FLAG: flag_tgt loc = Some ts),
          lc_tgt.(Local.tview).(TView.cur).(View.rlx) loc = ts)
      (FLAGSRC: forall loc ts (FLAG: flag_src loc = Some ts),
          lc_tgt.(Local.tview).(TView.cur).(View.rlx) loc = ts)
      (MAX: max_readable


    :
      sim_thread
        f vers flag_src flag_tgt vs st_src st_tgt
        (Thread.mk _ st_src lc_src sc_src mem_src)
        (Thread.mk _ st_tgt lc_tgt sc_tgt mem_tgt)
  .

Local.program_step


      (MAX: forall val released, ~ max_readable mem prom loc (tvw.(TView.cur).(View.pln) loc) val released)



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
          (<<MSG: sim_message_max (flag_tgt loc) f (vers loc to) msg_src msg_tgt>>))
    (SOUND: forall loc fto ffrom msg_src
                   (GET: Memory.get loc fto prom_src = Some (ffrom, msg_src)),
        (exists to from msg_tgt,
            (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) fto to>>) /\
            (<<GET: Memory.get loc to prom_tgt = Some (from, msg_tgt)>>)) \/
        (exists vw, (<<FLAG: flag_tgt loc = Some vw>>) /\ (<<TS: msg_src <> Message.reserve -> Time.lt vw fto>>)))
    (NONE: forall loc to ts
                  (FLAGSRC: flag_src loc = Some ts),
        Memory.get loc to prom_src = None)
.



Variant max_readable (mem prom: Memory.t) (loc: Loc.t) (ts: Time.t) (val: Const.t) (released: option View.t): Prop :=



perm, flag, flag

        (vals_src val_tgt: Time.t -> option Time.t)
  :


 flag






  Variant _sim_seq
          (sim_seq:
             forall
               (p0: Perms.t) (d0: Flags.t)
               (st_src0: SeqState.t lang_src)
               (st_tgt0: SeqState.t lang_tgt), Prop)
          (p0: Perms.t) (d0: Flags.t)
          (st_src0: SeqState.t lang_src)
          (st_tgt0: SeqState.t lang_tgt): Prop :=
  | sim_seq_normal
      (TERMINAL: sim_seq_terminal_case p0 d0 st_src0 st_tgt0)
      (NASTEP: sim_seq_na_step_case sim_seq p0 d0 st_src0 st_tgt0)
      (ATSTEP: sim_seq_at_step_case sim_seq p0 d0 st_src0 st_tgt0)
      (PARTIAL: sim_seq_partial_case p0 d0 st_src0 st_tgt0)
  | sim_seq_failure
      (FAILURE: sim_seq_failure_case p0 d0 st_src0)
  .
