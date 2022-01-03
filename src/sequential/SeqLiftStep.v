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
    (TVIEW: sim_tview f flag_src rel_vers tvw_src tvw_tgt)
    (PROMISES: sim_promises flag_src flag_tgt f vers prom_src prom_tgt)
    (RELVERS: wf_release_vers vers prom_tgt rel_vers)
    (FLAGTGT: forall loc ts (FLAG: flag_tgt loc = Some ts),
        tvw_src.(TView.cur).(View.rlx) loc = ts)
    (FLAGSRC: forall loc ts (FLAG: flag_src loc = Some ts),
        (<<RLX: tvw_src.(TView.cur).(View.rlx) loc = ts>>) /\
        (<<PLN: tvw_src.(TView.cur).(View.pln) loc = ts>>))
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

Lemma sim_local_racy f vers flag_src flag_tgt lc_src lc_tgt mem_src mem_tgt loc
      (CONSISTENT: Local.promise_consistent lc_tgt)
      (MEM: sim_memory flag_src f vers mem_src mem_tgt)
      (SIM: sim_local f vers flag_src flag_tgt lc_src lc_tgt)
      (WF: Mapping.wfs f)
      (RACY: Local.is_racy lc_tgt mem_tgt loc Ordering.na)
      (FLAGSRC: flag_src loc = None)
      (FLAGTGT: flag_tgt loc = None)
  :
    Local.is_racy lc_src mem_src loc Ordering.na.
Proof.
  inv RACY. hexploit sim_memory_get; eauto. i. des. econs; eauto.
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
    (MAX: forall v1 (VAL: v = Some v1),
        exists released v0,
          (<<MAX: max_readable
                    mem
                    prom
                    loc
                    (tvw.(TView.cur).(View.pln) loc)
                    v0 released>>) /\
          (<<VAL: Const.le v0 v1>>))
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
    (FIN: __guard__(exists dom, (<<DOM: forall loc, (exists ts, flag_src loc = Some ts) <-> (List.In loc dom)>>)))
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

Lemma race_non_max_readable mem prom tvw loc
      (MAX: Local.is_racy (Local.mk tvw prom) mem loc Ordering.na)
  :
    forall val released, ~ max_readable mem prom loc (tvw.(TView.cur).(View.pln) loc) val released.
Proof.
  ii. inv H. inv MAX.
  eapply MAX0 in RACE; eauto. ss. clarify.
Qed.

Lemma sim_memory_src_flag_max_concrete
      f vers flag_src
      mem_src mem_tgt
      (SIM: sim_memory flag_src f vers mem_src mem_tgt)
      loc ts
      (FLAG: flag_src loc = Some ts)
      (CLOSED: exists from msg, Memory.get loc ts mem_src = Some (from, msg))
  :
    Memory.max_ts loc mem_src = ts.
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

Lemma max_value_src_flag_none f vers flag_src flag_tgt lc_src lc_tgt mem_src mem_tgt loc
      (MEM: sim_memory flag_src f vers mem_src mem_tgt)
      (LOCAL: sim_local f vers flag_src flag_tgt lc_src lc_tgt)
      (MAX: max_value_src loc None mem_src lc_src)
      (LOCALWF: Local.wf lc_src mem_src)
      (WF: Mapping.wfs f)
  :
    flag_src loc = None.
Proof.
  destruct (flag_src loc) eqn:FLAG; auto. exfalso.
  inv LOCAL. hexploit FLAGSRC; eauto. i. des. subst.
  inv LOCALWF. inv TVIEW_CLOSED.
  inv CUR. exploit RLX; eauto. i. des. ss.
  inv MAX. hexploit NONMAX; eauto. ii. eapply H. econs.
  { rewrite PLN. eauto. }
  { inv PROMISES. eapply NONE; eauto. }
  { i. hexploit sim_memory_src_flag_max_concrete; eauto. i.
    eapply Memory.max_ts_spec in GET. des.
    rewrite H0 in MAX. exfalso.
    eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
    { eapply TS. }
    { rewrite PLN. eauto. }
  }
Qed.
Lemma no_flag_max_value_same f vers flag_src flag_tgt lc_src lc_tgt mem_src mem_tgt loc v
      (MEM: sim_memory flag_src f vers mem_src mem_tgt)
      (LOCAL: sim_local f vers flag_src flag_tgt lc_src lc_tgt)
      (FLAGSRC: flag_src loc = None)
      (FLAGTGT: flag_tgt loc = None)
      (MAX: max_value_src loc (Some v) mem_src lc_src)
      (LOCALWF: Local.wf lc_tgt mem_tgt)
      (CONSISTENT: Local.promise_consistent lc_tgt)
      (WF: Mapping.wfs f)
  :
    max_value_tgt loc (Some v) mem_tgt lc_tgt.
Proof.
  inv MAX. destruct lc_tgt. econs. i. clarify.
  hexploit MAX0; eauto. i. des.
  assert (exists val released, max_readable mem_tgt promises loc (View.pln (TView.cur tview) loc) val released).
  { apply NNPP. ii. hexploit non_max_readable_race.
    { ii. eapply H; eauto. }
    { eauto. }
    { eauto. }
    { i. eapply sim_local_racy in H0; eauto.
      eapply race_non_max_readable in H0; eauto. }
  }
  des. esplits; eauto. inv H.
  hexploit sim_memory_get; eauto; ss. i. des.
  hexploit sim_timestamp_le.
  2:{ eapply TO. }
  2:{ refl. }
  { inv LOCAL. eapply TVIEW; ss. }
  { eauto. }
  { eapply mapping_latest_wf_loc. }
  i. inv MAX. inv H.
  { hexploit MAX2; eauto.
    { inv MSG; ss. }
    i. hexploit sim_promises_get_if; eauto.
    { inv LOCAL. eauto. }
    i. des.
    2:{ rewrite FLAGTGT in *; ss. }
    eapply sim_timestamp_exact_unique in TO; eauto.
    2:{ eapply mapping_latest_wf_loc. }
    subst. clarify.
  }
  { inv H0. clarify. inv MSG; auto. }
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
  }
  { i. inv SIM. specialize (MAXTGT loc). inv MAXTGT.
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
    Local.racy_read_step lc_src mem_src loc val_src Ordering.na.
Proof.
  inv SIM. specialize (MAXSRC loc). inv MAXSRC.
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
    Local.racy_write_step lc_src mem_src loc Ordering.na.
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
                                             then Some (lc_src1.(Local.tview).(TView.cur).(View.rlx) loc)
                                             else flag_tgt loc0)
                vs_src vs_tgt
                mem_src1 mem_tgt lc_src1 lc_tgt sc_src sc_tgt>>).
Proof.
  inv SIM. dup LOCAL0. inv LOCAL0.
  hexploit tgt_flag_up_sim_promises.
  { eauto. }
  { eauto. }
  { eapply sim_local_consistent in CONSISTENT; eauto.
    i. eapply CONSISTENT; eauto.
  }
  { eapply LOCAL. }
  { eapply MEM. }
  i. des. esplits; [eapply STEPS|..].
  { i. ss. eapply NONE; eauto. }
  econs; auto.
  { econs; eauto. i. des_ifs. auto. }
  { ii. hexploit (MAXSRC loc0). i. inv H. econs.
    { i. hexploit MAX; eauto. i. des. esplits. eapply VALS; eauto. }
    { i. hexploit NONMAX; eauto. ii. eapply H. eapply VALS; eauto. }
  }
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
      { eapply MAX; eauto. etrans; eauto. }
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
      { eapply MAX; eauto. etrans; eauto. }
    }
  }
Qed.

Lemma ts_le_memory_write_na
      ts0 prom0 mem0 loc from to val prom1 mem1 msgs kinds kind ts1
      (WRITE: Memory.write_na ts1 prom0 mem0 loc from to val prom1 mem1 msgs kinds kind)
      (TS: Time.le ts0 ts1)
  :
    Memory.write_na ts0 prom0 mem0 loc from to val prom1 mem1 msgs kinds kind.
Proof.
  revert ts0 TS. induction WRITE; i.
  { econs 1; eauto. eapply TimeFacts.le_lt_lt; eauto. }
  { econs 2; eauto. eapply TimeFacts.le_lt_lt; eauto. }
Qed.

Lemma write_na_ts_lt ts prom0 mem0 loc from to val prom1 mem1 msgs kinds kind
      (WRITE: Memory.write_na ts prom0 mem0 loc from to val prom1 mem1 msgs kinds kind)
  :
    Time.lt ts to.
Proof.
  induction WRITE; auto. etrans; eauto.
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

Lemma sim_thread_tgt_write_na_aux
      f vers flag_src flag_tgt vs_src vs_tgt
      mem_src mem_tgt0 lc_src lc_tgt0 sc_src sc_tgt0
      loc from to val_old val_new lc_tgt1 sc_tgt1 mem_tgt1 ord msgs kinds kind ts
      (WRITE: Local.write_na_step lc_tgt0 sc_tgt0 mem_tgt0 loc from to val_new ord lc_tgt1 sc_tgt1 mem_tgt1 msgs kinds kind)
      (LOWER: mem_tgt1 = mem_tgt0)
      (SIM: sim_thread
              f vers flag_src flag_tgt vs_src vs_tgt
              mem_src mem_tgt0 lc_src lc_tgt0 sc_src sc_tgt0)
      (VAL: vs_tgt loc = Some val_old)
      (FLAG: flag_tgt loc = Some ts)
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
  hexploit sim_local_consistent.
  { eapply PromiseConsistent.write_na_step_promise_consistent; eauto. }
  { inv SIM. eauto. }
  { auto. }
  intros CONSSRC. des. splits.
  2:{ inv WRITE. destruct ord; ss. }
  2:{ inv WRITE. auto. }
  inv SIM. econs; auto.
  { inv WRITE. auto. }
  { inv WRITE. inv LOCAL0. econs; ss; auto.
    { eapply sim_tview_tgt_mon; eauto.
      eapply TViewFacts.write_tview_incr. eapply LOCAL.
    }
    { econs.
      { i. eapply MLE in GET. hexploit sim_promises_get; eauto.
        i. des. esplits; eauto.
      }
      { i. destruct (Loc.eq_dec loc0 loc).
        { subst. right. esplits; eauto. eapply FLAGTGT in FLAG. subst.
          i. eapply CONSSRC; eauto.
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
      i. destruct lc_tgt1. ss. econs. i. esplits; eauto.
      clear - VAL1. clarify. refl.
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
      (WF: Mapping.wfs f)
      lang st
  :
    exists mem_src1 lc_src1 ts,
      (<<STEPS: rtc (@Thread.tau_step _)
                    (Thread.mk lang st lc_src0 sc_src mem_src0)
                    (Thread.mk _ st lc_src1 sc_src mem_src1)>>) /\
      (<<SIM: sim_thread
                f vers flag_src
                (fun loc0 => if Loc.eq_dec loc0 loc then Some ts else flag_tgt loc0)
                vs_src
                (fun loc0 => if Loc.eq_dec loc0 loc then Some val_new else vs_tgt loc0)
                mem_src1 mem_tgt1 lc_src1 lc_tgt1 sc_src sc_tgt1>>) /\
      (<<ORD: ord = Ordering.na>>) /\
      (<<SC: sc_tgt1 = sc_tgt0>>)
.
Proof.
  hexploit sim_thread_tgt_flag_up; eauto.
  { eapply PromiseConsistent.write_na_step_promise_consistent; eauto. }
  i. des.
  hexploit sim_thread_tgt_write_na_aux; eauto.
  { ss. des_ifs. }
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
  assert (JOIN: sim_view (fun loc0 => flag_src loc0 = None) f (Mapping.vers f)
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
  assert (JOIN: sim_view (fun loc0 => flag_src loc0 = None) f (Mapping.vers f)
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
      (TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src to_tgt)
      (FLAG: forall loc, flag_src loc = None)
      (CLOSED: Mapping.closed (f loc) (Mapping.vers f loc) to_src)
      (WF: Mapping.wfs f)
  :
    sim_tview f flag_src (fun loc0 => if Loc.eq_dec loc0 loc then (Mapping.vers f) else rel_vers loc0) (TView.write_tview tvw_src sc_src loc to_src ord) (TView.write_tview tvw_tgt sc_tgt loc to_tgt ord).
Proof.
  pose proof (mapping_latest_wf f).
  assert (TM: sim_timestamp (f loc) (Mapping.vers f loc) to_src to_tgt).
  { eapply sim_timestamp_exact_sim; eauto. }
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
      (FLAG: forall loc, flag_src loc = None)
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
      (SC: sim_timemap (fun _ => True) f (Mapping.vers f) sc_src sc_tgt)
      (FLAG: Ordering.le Ordering.seqcst ord -> forall loc, flag_src loc = None)
      (WF: Mapping.wfs f)
  :
    sim_timemap (fun _ => True) f (Mapping.vers f) (TView.write_fence_sc tvw_src sc_src ord) (TView.write_fence_sc tvw_tgt sc_tgt ord).
Proof.
  pose proof (mapping_latest_wf f).
  unfold TView.write_fence_sc. des_ifs. eapply sim_timemap_join; auto.
  eapply sim_timemap_mon_locs; eauto.
  { eapply SIM. }
  { ss. i. auto. }
Qed.

Lemma sim_write_released_normal f flag_src rel_vers tvw_src tvw_tgt sc_src sc_tgt
      loc to_src ord to_tgt released_src released_tgt v
      (SIM: sim_tview f flag_src rel_vers tvw_src tvw_tgt)
      (TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src to_tgt)
      (RELEASED: sim_opt_view (fun loc0 => loc0 <> loc) f v released_src released_tgt)
      (ORD: ~ Ordering.le Ordering.acqrel ord)
      (VER: Ordering.le Ordering.relaxed ord -> v = Some (rel_vers loc))
      (CLOSED: Mapping.closed (f loc) (Mapping.vers f loc) to_src)
      (WF: Mapping.wfs f)
  :
    sim_opt_view (fun loc0 => loc0 <> loc) f v
                 (TView.write_released tvw_src sc_src loc to_src released_src ord)
                 (TView.write_released tvw_tgt sc_tgt loc to_tgt released_tgt ord).
Proof.
  pose proof (mapping_latest_wf f).
  unfold TView.write_released. des_ifs.
  { rewrite VER in *; auto. econs.
    eapply sim_view_join; auto.
    { eapply sim_opt_view_unwrap; eauto.
      { eapply SIM. }
      { i. clarify. }
    }
    { ss. setoid_rewrite LocFun.add_spec_eq. des_ifs.
      eapply sim_view_join; auto.
      { eapply SIM. }
      { eapply sim_view_singleton_ur; auto; ss. apply SIM. }
      { apply SIM. }
    }
    { apply SIM. }
  }
  { econs. }
Qed.

Lemma sim_write_released_release f flag_src rel_vers tvw_src tvw_tgt sc_src sc_tgt
      loc to_src ord to_tgt released_src released_tgt v
      (SIM: sim_tview f flag_src rel_vers tvw_src tvw_tgt)
      (TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src to_tgt)
      (RELEASED: sim_opt_view (fun loc0 => loc0 <> loc) f v released_src released_tgt)
      (VERWF: opt_version_wf f v)
      (FLAG: forall loc, flag_src loc = None)
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
                (fun loc0 => if Loc.eq_dec loc0 loc then Some to else flag_src loc0)
                (fun loc0 => if Loc.eq_dec loc0 loc then Some to else flag_tgt loc0)
                (fun loc0 => if Loc.eq_dec loc0 loc then Some val_new else vs_src loc0)
                vs_tgt
                mem_src2 mem_tgt lc_src2 lc_tgt sc_src sc_tgt>>)
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
  i. des.
  hexploit reserve_future_steps.
  { eapply cancel_future_reserve_future; eauto. }
  i. des.
  hexploit Thread.rtc_tau_step_future; eauto. i. ss. des.
  esplits.
  { etrans; eauto. }
  { eauto. }
  subst. hexploit src_cancels_sim_promises; eauto.
  { eapply WF2. }
  i. des.
  hexploit Local.write_na_step_future; eauto. i. des.
  assert (RLX: View.rlx (TView.cur tvw1) loc = Time.incr top).
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
  econs; auto.
  { destruct (flag_src loc) eqn:FLAG.
    { eapply add_src_sim_memory; eauto.
      etransitivity; [|left; eapply TS].
      inv LOCAL. hexploit FLAGSRC; eauto. i. des. subst.
      inv WF2. ss. inv TVIEW_CLOSED. inv CUR.
      exploit RLX0. i. des.
      eapply Memory.max_ts_spec in x. des. eauto.
    }
    { eapply src_write_sim_memory in MEM0; eauto.
      match goal with
      | |- _ ?flag _ _ _ _ =>
        replace flag with
            (fun loc' =>
               if LocSet.Facts.eq_dec loc' loc
               then Some (Time.incr top)
               else (fun loc'' =>
                       if LocSet.Facts.eq_dec loc'' loc
                       then Some top
                       else flag_src loc'') loc')
      end.
      2:{ extensionality loc'. des_ifs. }
      eapply add_src_sim_memory; try eassumption.
      { des_ifs. }
      { refl. }
    }
  }
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
    { i. des_ifs. hexploit (FLAGTGT loc0 ts); eauto.
      { des_ifs. }
      i. subst. auto.
    }
    { i. des_ifs. eapply FLAGSRC in FLAG. des. subst.
      splits; auto. rewrite OTHERPLN; auto.
    }
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
          { eapply add_unchanged_loc; eauto. }
        }
      }
      { i. hexploit NONMAX0; eauto. i.
        rewrite OTHERPLN; auto.
        erewrite unchanged_loc_max_readable; eauto.
        { econs. i. rewrite PROMISES. des_ifs. }
        { symmetry. etrans.
          { eapply cancel_future_unchanged_loc in RESERVE; eauto. des; eauto.  }
          { eapply add_unchanged_loc; eauto. }
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
      (FLAGS: forall loc ts
                     (SRC: flag_src loc = None)
                     (TGT: flag_tgt loc = Some ts),
          (<<PLN: tvw_src1.(TView.cur).(View.pln) loc = tvw_src0.(TView.cur).(View.pln) loc>>) /\
          (<<RLX: tvw_src1.(TView.cur).(View.rlx) loc = tvw_src0.(TView.cur).(View.rlx) loc>>))
  :
    exists vs_src1 vs_tgt1,
      (<<SIM: sim_thread
                f vers flag_src flag_tgt vs_src1 vs_tgt1
                mem_src mem_tgt (Local.mk tvw_src1 prom_src) (Local.mk tvw_tgt1 prom_tgt) sc_src sc_tgt>>) /\
      (<<VALS: forall loc,
          ((<<SRC: vs_src1 loc = vs_src0 loc>>) /\ (<<TGT: vs_tgt1 loc = vs_tgt0 loc>>)) \/
          (exists val,
              (<<FLAGSRC: flag_src loc = None>>) /\
              (<<FLAGTGT: flag_tgt loc = None>>) /\
              (<<NONESRC: vs_src0 loc = None>>) /\ (<<NONETGT: vs_tgt0 loc = None>>) /\
              (<<VALSRC: vs_src1 loc = Some val>>) /\ (<<VALTGT: vs_tgt1 loc = Some val>>) /\
              (<<TS: Time.lt (tvw_src0.(TView.cur).(View.pln) loc) (tvw_src1.(TView.cur).(View.pln) loc)>>) /\
              (<<VAL: __guard__(exists from released, Memory.get loc (tvw_src1.(TView.cur).(View.pln) loc) mem_src = Some (from, Message.concrete val released))>>))>>)
.
Proof.
  assert (SIMLOCAL: sim_local f vers flag_src flag_tgt (Local.mk tvw_src1 prom_src) (Local.mk tvw_tgt1 prom_tgt)).
  { inv SIM. inv LOCAL.
    assert (VIEWEQ: forall loc ts
                           (SRC: flag_src loc = Some ts),
               (<<PLN: tvw_src1.(TView.cur).(View.pln) loc = tvw_src0.(TView.cur).(View.pln) loc>>) /\
               (<<RLX: tvw_src1.(TView.cur).(View.rlx) loc = tvw_src0.(TView.cur).(View.rlx) loc>>)).
    { i. hexploit FLAGSRC; eauto. i. des.
      hexploit sim_memory_src_flag_max_concrete; eauto.
      { inv LOCALSRC0. inv TVIEW_CLOSED. inv CUR. exploit RLX. i. des. eauto. }
      i. subst.
      inv LOCALSRC1. inv TVIEW_CLOSED. inv CUR. ss. splits.
      { eapply TimeFacts.antisym.
        { hexploit (PLN0 loc). i. des.
          eapply Memory.max_ts_spec in H0. des.
          rewrite H in MAX. rewrite <- PLN in MAX. auto.
        }
        { eapply LESRC. }
      }
      { eapply TimeFacts.antisym.
        { hexploit (RLX loc). i. des.
          eapply Memory.max_ts_spec in H0. des.
          rewrite H in MAX. auto.
        }
        { eapply LESRC. }
      }
    }
    econs; eauto.
    { i. destruct (flag_src loc) eqn:EQ.
      { hexploit VIEWEQ; eauto. i. des.
        rewrite RLX. eapply FLAGTGT; eauto.
      }
      { hexploit FLAGS; eauto. i. des.
        rewrite RLX. eapply FLAGTGT; eauto.
      }
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
                 (<<FLAGSRC: flag_src loc = None>>) /\
                 (<<NONESRC: vs_src0 loc = None>>) /\
                 (<<VALSRC: vs_src1 loc = Some val>>) /\
                 (<<TS: Time.lt (tvw_src0.(TView.cur).(View.pln) loc) (tvw_src1.(TView.cur).(View.pln) loc)>>) /\
                 (<<VAL: __guard__(exists from released, Memory.get loc (tvw_src1.(TView.cur).(View.pln) loc) mem_src = Some (from, Message.concrete val released))>>))).
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
  set (vs_tgt1 := fun loc => match (vs_src0 loc), (vs_src1 loc) with
                             | None, Some v => Some v
                             | _, _ => vs_tgt0 loc
                             end).
  assert (VALS: forall loc,
             ((<<SRC: vs_src1 loc = vs_src0 loc>>) /\ (<<TGT: vs_tgt1 loc = vs_tgt0 loc>>)) \/
             (exists val,
                 (<<FLAGSRC: flag_src loc = None>>) /\
                 (<<FLAGTGT: flag_tgt loc = None>>) /\
                 (<<NONESRC: vs_src0 loc = None>>) /\ (<<NONETGT: vs_tgt0 loc = None>>) /\
                 (<<VALSRC: vs_src1 loc = Some val>>) /\ (<<VALTGT: vs_tgt1 loc = Some val>>) /\
                 (<<TS: Time.lt (tvw_src0.(TView.cur).(View.pln) loc) (tvw_src1.(TView.cur).(View.pln) loc)>>) /\
                 (<<VAL: __guard__(exists from released, Memory.get loc (tvw_src1.(TView.cur).(View.pln) loc) mem_src = Some (from, Message.concrete val released))>>))).
  { subst vs_tgt1. i. hexploit (VALSRC loc). i. des.
    { left. esplits; eauto. rewrite <- SRC. des_ifs. }
    { right. esplits; eauto.
      { destruct (flag_tgt loc) eqn:FLAG; auto. exfalso.
        exploit FLAGS; eauto. i. des. rewrite PLN in TS. timetac.
      }
      { inv SIM. specialize (PERM loc).
        rewrite NONESRC in PERM. ss. des_ifs.
      }
      { rewrite NONESRC. rewrite VALSRC0. auto. }
    }
  }
  clear VALSRC. exists vs_src1, vs_tgt1. splits; auto.
  inv SIM.
 econs; auto.
  { ii. specialize (VALS loc). des.
    { rewrite TGT. eapply max_value_tgt_mon; eauto. }
    { rewrite VALTGT. eapply no_flag_max_value_same; eauto.
      specialize (MAX loc). rewrite VALSRC in MAX. auto.
    }
  }
  { i. hexploit (VALS loc). i. des.
    { rewrite SRC. rewrite TGT. auto. }
    { rewrite VALSRC. rewrite VALTGT. ss. }
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

Definition local_write_fence_sc (tview1: TView.t) (ord: Ordering.t) (sc: TimeMap.t): TimeMap.t :=
  if Ordering.le Ordering.seqcst ord
  then (TimeMap.join sc (View.rlx (TView.cur tview1)))
  else sc
.

Lemma local_write_fence_sc_closed mem tview sc ord
      (TVIEW: TView.closed tview mem)
      (SC: Memory.closed_timemap sc mem)
  :
    Memory.closed_timemap (local_write_fence_sc tview ord sc) mem.
Proof.
  unfold local_write_fence_sc. des_ifs.
  eapply Memory.join_closed_timemap; auto. eapply TVIEW.
Qed.

Lemma local_write_fence_sc_incr tview sc ord
  :
    TimeMap.le sc (local_write_fence_sc tview ord sc).
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

Lemma read_tview_incr
      tvw loc ts vw ord
      (WF: time_le_opt_view loc ts vw)
      (READABLE: Time.le (View.pln (TView.cur tvw) loc) ts)
      (TS: Time.lt (View.pln (TView.cur tvw) loc)
                   (View.pln (TView.cur (TView.read_tview tvw loc ts vw ord)) loc))
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
  { rewrite ! timemap_bot_join_r. rewrite ! timemap_bot_join_r in TS.
    unfold TimeMap.join, Time.join in *. des_ifs.
    { rewrite timemap_singleton_eq. auto. }
    { timetac. }
  }
  { destruct ord; ss. }
  { rewrite ! timemap_bot_join_r. rewrite ! timemap_bot_join_r in TS. timetac. }
Qed.

Variant local_fence_read_step lc1 sc1 ordr ordw lc2: Prop :=
| local_fence_read_step_intro
    (LOCAL: lc2 = Local.mk
                    (local_read_fence_tview lc1.(Local.tview) sc1 ordr ordw)
                    (lc1.(Local.promises)))
.

Variant local_fence_write_step lc1 sc1 ord lc2 sc2: Prop :=
| local_fence_write_step_intro
    (LOCAL: lc2 = Local.mk
                    (local_write_fence_tview lc1.(Local.tview) ord)
                    (lc1.(Local.promises)))
    (SC: sc2 = local_write_fence_sc lc1.(Local.tview) ord sc1)
    (RELEASE: Ordering.le Ordering.strong_relaxed ord -> Memory.nonsynch lc1.(Local.promises))
    (PROMISES: ord = Ordering.seqcst -> lc1.(Local.promises) = Memory.bot)
.

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
    local_write_fence_sc (local_read_fence_tview tvw sc ordr ordw) ordw sc =
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

Lemma sim_thread_read
      f vers flag_src flag_tgt vs_src0 vs_tgt0
      mem_src mem_tgt lc_src0 lc_tgt0 sc_src sc_tgt
      lc_tgt1 loc to_tgt val_tgt released_tgt ord
      (SIM: sim_thread
              f vers flag_src flag_tgt vs_src0 vs_tgt0
              mem_src mem_tgt lc_src0 lc_tgt0 sc_src sc_tgt)
      (READ: Local.read_step lc_tgt0 mem_tgt loc to_tgt val_tgt released_tgt ord lc_tgt1)
      (CONSISTENT: Local.promise_consistent lc_tgt1)
      (LOCALSRC: Local.wf lc_src0 mem_src)
      (LOCALTGT: Local.wf lc_tgt0 mem_tgt)
      (MEMSRC: Memory.closed mem_src)
      (MEMTGT: Memory.closed mem_tgt)
      (SCSRC: Memory.closed_timemap sc_src mem_src)
      (SCTGT: Memory.closed_timemap sc_tgt mem_tgt)
      (WF: Mapping.wfs f)
      (VERS: versions_wf f vers)
      (FLAGSRC: flag_src loc = None)
      (FLAGTGT: flag_tgt loc = None)
      (FLAG: forall loc ts
                    (SRC: flag_src loc = None) (TGT: flag_tgt loc = Some ts),
          ~ Ordering.le Ordering.acqrel ord)
  :
    exists val_src to_src released_src lc_src1 vs_src1 vs_tgt1,
      (<<READ: forall val (VAL: Const.le val val_src), Local.read_step lc_src0 mem_src loc to_src val released_src ord lc_src1>>) /\
      (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src to_tgt>>) /\
      (<<RELEASED: sim_opt_view (fun loc0 => loc0 <> loc) f (vers loc to_tgt) released_src released_tgt>>) /\
      (<<SIM: sim_thread
                f vers flag_src flag_tgt vs_src1 vs_tgt1
                mem_src mem_tgt lc_src1 lc_tgt1 sc_src sc_tgt>>) /\
      (<<VAL: Const.le val_tgt val_src>>) /\
      (<<NUPDATE: forall val (VAL: vs_src0 loc = Some val), val = val_src>>) /\
      (<<VALS: forall loc0,
          ((<<SRC: vs_src1 loc0 = vs_src0 loc0>>) /\ (<<TGT: vs_tgt1 loc0 = vs_tgt0 loc0>>)) \/
          (exists val0,
              (<<NONESRC: vs_src0 loc0 = None>>) /\ (<<NONETGT: vs_tgt0 loc0 = None>>) /\
              (<<VALSRC: vs_src1 loc0 = Some val0>>) /\ (<<VALTGT: vs_tgt1 loc0 = Some val0>>) /\
              ((<<ORD: Ordering.le Ordering.acqrel ord>>) \/
               ((<<LOC: loc0 = loc>>) /\ (<<VAL: val0 = val_src>>))))>>).
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
  { etrans; eauto. }
  { i. specialize (MAXSRC loc). rewrite VAL1 in MAXSRC. inv MAXSRC.
    hexploit MAX; eauto. i. des.
    hexploit max_readable_read_only_aux; eauto.
    { inv SIM2. eapply sim_local_consistent; eauto. }
    i. des. subst. inv MAX0.
    rewrite GET1 in GET0. inv GET0. auto.
  }
  i. hexploit VALS; eauto. i. des.
  { left. eauto. }
  { right. esplits; eauto. destruct (Loc.eq_dec loc0 loc).
    { subst. right. splits; auto. red in VAL1. des.
      replace (View.pln (TView.cur tvw_src1) loc) with to_src in VAL1.
      { rewrite GET0 in VAL1. inv VAL1. etrans; eauto. }
      symmetry. inv READSRC. inv LC2. ss.
      eapply read_tview_incr; eauto.
      { eapply message_to_time_le_opt_view; eauto.
        eapply MEMSRC; eauto.
      }
      { inv READABLE0. ss. }
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

Require Import Pred.

Lemma sim_thread_deflag_match_aux
      f0 vers flag_src flag_tgt vs_src vs_tgt
      mem_src0 mem_tgt lc_src0 lc_tgt sc_src sc_tgt
      loc ts
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
      (FLAG: flag_src loc = Some ts)
      (VAL: option_rel Const.le (vs_tgt loc) (vs_src loc))
      lang st
  :
    exists lc_src1 mem_src1 f1,
      (<<STEPS: rtc (tau (@pred_step is_promise _))
                    (Thread.mk lang st lc_src0 sc_src mem_src0)
                    (Thread.mk _ st lc_src1 sc_src mem_src1)>>) /\
      (<<SIM: sim_thread
                f1 vers
                (fun loc0 => if Loc.eq_dec loc0 loc then None else flag_src loc0)
                (fun loc0 => if Loc.eq_dec loc0 loc then None else flag_tgt loc0)
                vs_src vs_tgt
                mem_src1 mem_tgt lc_src1 lc_tgt sc_src sc_tgt>>) /\
      (<<WF: Mapping.wfs f1>>) /\
      (<<MAPLE: Mapping.les f0 f1>>).
Proof.
Admitted.

Lemma sim_thread_deflag_unmatch_aux
      f0 vers flag_src flag_tgt vs_src vs_tgt
      mem_src0 mem_tgt lc_src0 lc_tgt sc_src sc_tgt
      loc ts
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
      (FLAG: flag_src loc = Some ts)
      lang st
  :
    exists lc_src1 mem_src1 f1 flag,
      (<<STEPS: rtc (tau (@pred_step is_promise _))
                    (Thread.mk lang st lc_src0 sc_src mem_src0)
                    (Thread.mk _ st lc_src1 sc_src mem_src1)>>) /\
      (<<SIM: sim_thread
                f1 vers
                (fun loc0 => if Loc.eq_dec loc0 loc then None else flag_src loc0)
                (fun loc0 => if Loc.eq_dec loc0 loc then flag else flag_tgt loc0)
                vs_src vs_tgt
                mem_src1 mem_tgt lc_src1 lc_tgt sc_src sc_tgt>>) /\
      (<<WF: Mapping.wfs f1>>) /\
      (<<MAPLE: Mapping.les f0 f1>>).
Proof.
Admitted.

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
      (FLAG: flag_src loc = None -> flag_tgt loc = None)
      (VAL: option_rel Const.le (vs_tgt loc) (vs_src loc))
      lang st
  :
    exists lc_src1 mem_src1 f1,
      (<<STEPS: rtc (tau (@pred_step is_promise _))
                    (Thread.mk lang st lc_src0 sc_src mem_src0)
                    (Thread.mk _ st lc_src1 sc_src mem_src1)>>) /\
      (<<SIM: sim_thread
                f1 vers
                (fun loc0 => if Loc.eq_dec loc0 loc then None else flag_src loc0)
                (fun loc0 => if Loc.eq_dec loc0 loc then None else flag_tgt loc0)
                vs_src vs_tgt
                mem_src1 mem_tgt lc_src1 lc_tgt sc_src sc_tgt>>) /\
      (<<WF: Mapping.wfs f1>>) /\
      (<<MAPLE: Mapping.les f0 f1>>).
Proof.
  destruct (flag_src loc) eqn:EQ.
  { eapply sim_thread_deflag_match_aux; eauto. }
  { esplits.
    { refl. }
    { replace (fun (loc0: Loc.t) => if LocSet.Facts.eq_dec loc0 loc then None else flag_src loc0) with flag_src.
      2:{ extensionality loc0. des_ifs. }
      replace (fun (loc0: Loc.t) => if LocSet.Facts.eq_dec loc0 loc then None else flag_tgt loc0) with flag_tgt.
      2:{ extensionality loc0. des_ifs. eauto. }
      eauto.
    }
    { eauto. }
    { refl. }
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
      lang st
  :
    exists lc_src1 mem_src1 f1 flag,
      (<<STEPS: rtc (tau (@pred_step is_promise _))
                    (Thread.mk lang st lc_src0 sc_src mem_src0)
                    (Thread.mk _ st lc_src1 sc_src mem_src1)>>) /\
      (<<SIM: sim_thread
                f1 vers
                (fun loc0 => if Loc.eq_dec loc0 loc then None else flag_src loc0)
                (fun loc0 => if Loc.eq_dec loc0 loc then flag else flag_tgt loc0)
                vs_src vs_tgt
                mem_src1 mem_tgt lc_src1 lc_tgt sc_src sc_tgt>>) /\
      (<<WF: Mapping.wfs f1>>) /\
      (<<MAPLE: Mapping.les f0 f1>>).
Proof.
  destruct (flag_src loc) eqn:FLAG.
  { eapply sim_thread_deflag_unmatch_aux; eauto. }
  { esplits.
    { refl. }
    { instantiate (1:=flag_tgt loc).
      replace (fun (loc0: Loc.t) => if LocSet.Facts.eq_dec loc0 loc then None else flag_src loc0) with flag_src.
      2:{ extensionality loc0. des_ifs. }
      replace (fun (loc0: Loc.t) => if LocSet.Facts.eq_dec loc0 loc then flag_tgt loc else flag_tgt loc0) with flag_tgt.
      2:{ extensionality loc0. des_ifs. }
      eauto.
    }
    { eauto. }
    { refl. }
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
      (DEBT: forall loc, (<<DEBT: D loc>>) \/
                         ((<<FLAG: flag_src loc = None -> flag_tgt0 loc = None>>) /\
                          (<<VAL: option_rel Const.le (vs_tgt loc) (vs_src loc)>>)))
      (FIN: forall loc ts (FLAG: flag_src loc = Some ts), List.In loc dom)
      lang st,
    exists lc_src1 mem_src1 f1 flag_tgt1,
      (<<STEPS: rtc (tau (@pred_step is_promise _))
                    (Thread.mk lang st lc_src0 sc_src mem_src0)
                    (Thread.mk _ st lc_src1 sc_src mem_src1)>>) /\
      (<<SIM: sim_thread
                f1 vers
                (fun _ => None)
                flag_tgt1
                vs_src vs_tgt
                mem_src1 mem_tgt lc_src1 lc_tgt sc_src sc_tgt>>) /\
      (<<WF: Mapping.wfs f1>>) /\
      (<<MAPLE: Mapping.les f0 f1>>) /\
      (<<FLAG: forall loc, (<<DEBT: D loc>>) \/ (<<FLAG: flag_tgt1 loc = None>>)>>)
.
Proof.
  induction dom.
  { i. assert (FLAG: flag_src = fun _ => None).
    { extensionality loc. destruct (flag_src loc) eqn:FLAG; auto.
      hexploit (FIN loc); eauto. ss.
    }
    subst. esplits.
    { refl. }
    { eauto. }
    { auto. }
    { refl. }
    { i. hexploit DEBT; eauto. i. des; eauto. }
  }
  i.
  cut (exists lc_src1 mem_src1 f1 flag,
          (<<STEPS: rtc (tau (@pred_step is_promise _))
                        (Thread.mk lang st lc_src0 sc_src mem_src0)
                        (Thread.mk _ st lc_src1 sc_src mem_src1)>>) /\
          (<<SIM: sim_thread
                    f1 vers
                    (fun loc0 => if Loc.eq_dec loc0 a then None else flag_src loc0)
                    (fun loc0 => if Loc.eq_dec loc0 a then flag else flag_tgt0 loc0)
                    vs_src vs_tgt
                    mem_src1 mem_tgt lc_src1 lc_tgt sc_src sc_tgt>>) /\
          (<<WF: Mapping.wfs f1>>) /\
          (<<MAPLE: Mapping.les f0 f1>>) /\
          (<<FLAG: __guard__(flag = None \/ D a)>>)).
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
      hexploit (DEBT loc). i. des; eauto.
      right. splits; auto. des_ifs.
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
  }
  hexploit (DEBT a). i. des.
  { hexploit sim_thread_deflag_unmatch; eauto. i. des.
    esplits; eauto. right. eauto.
  }
  { hexploit sim_thread_deflag_match; eauto. i. des.
    esplits; eauto. left. eauto.
  }
Qed.

Lemma sim_thread_deflag_all
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
      (DEBT: forall loc, (<<DEBT: D loc>>) \/
                         ((<<FLAG: flag_src loc = None -> flag_tgt0 loc = None>>) /\
                          (<<VAL: option_rel Const.le (vs_tgt loc) (vs_src loc)>>)))
      lang st
  :
    exists lc_src1 mem_src1 f1 flag_tgt1,
      (<<STEPS: rtc (tau (@pred_step is_promise _))
                    (Thread.mk lang st lc_src0 sc_src mem_src0)
                    (Thread.mk _ st lc_src1 sc_src mem_src1)>>) /\
      (<<SIM: sim_thread
                f1 vers
                (fun _ => None)
                flag_tgt1
                vs_src vs_tgt
                mem_src1 mem_tgt lc_src1 lc_tgt sc_src sc_tgt>>) /\
      (<<WF: Mapping.wfs f1>>) /\
      (<<MAPLE: Mapping.les f0 f1>>) /\
      (<<FLAG: forall loc, (<<DEBT: D loc>>) \/ (<<FLAG: flag_tgt1 loc = None>>)>>)
.
Proof.
  dup SIM. inv SIM. red in FIN. des.
  eapply (@sim_thread_deflag_all_aux dom); eauto.
  i. eapply DOM. eauto.
Qed.

(* Lemma sim_thread_write *)
(*       f vers flag_src flag_tgt vs_src0 vs_tgt0 *)
(*       mem_src0 mem_tgt0 lc_src0 lc_tgt0 sc_src0 sc_tgt0 *)
(*       val_tgt val_src releasedm_tgt releasedm_src *)
(*       lc_tgt1 mem_tgt1 loc from_tgt to_tgt *)
(*       released_tgt ord sc_tgt1 kind_tgt *)
(*       (SIM: sim_thread *)
(*               f vers flag_src flag_tgt vs_src0 vs_tgt0 *)
(*               mem_src0 mem_tgt0 lc_src0 lc_tgt0 sc_src0 sc_tgt0) *)
(*       (READ: Local.write_step lc_tgt0 sc_tgt0 mem_tgt0 loc from_tgt to_tgt val_tgt releasedm_tgt released_tgt ord lc_tgt1 sc_tgt1 mem_tgt1 kind_tgt) *)
(*       (RELEASEDM: sim_opt_view (fun loc0 => loc0 <> loc) f (vers loc to_tgt) releasedm_src releasedm_tgt) *)
(*       (CONSISTENT: Local.promise_consistent lc_tgt1) *)
(*       (LOCALSRC: Local.wf lc_src0 mem_src0) *)
(*       (LOCALTGT: Local.wf lc_tgt0 mem_tgt0) *)
(*       (MEMSRC: Memory.closed mem_src0) *)
(*       (MEMTGT: Memory.closed mem_tgt0) *)
(*       (SCSRC: Memory.closed_timemap sc_src0 mem_src0) *)
(*       (SCTGT: Memory.closed_timemap sc_tgt0 mem_tgt0) *)
(*       (WF: Mapping.wfs f) *)
(*       (VERS: versions_wf f vers) *)
(*       (FLAGSRC: flag_src loc = None) *)
(*       (FLAGTGT: flag_tgt loc = None) *)
(*       (FLAG: forall loc ts *)
(*                     (SRC: flag_src loc = None) (TGT: flag_tgt loc = Some ts), *)
(*           ~ Ordering.le Ordering.acqrel ord) *)
(*       (LOWER: Memory.op_kind_is_lower kind_tgt) *)
(*       (ORD: ~ Ordering.le Ordering.strong_relaxed ord) *)
(*       (VAL: Const.le val_tgt val_src) *)
(*   : *)
(*     exists from_src to_src released_src lc_src1 vs_src1 vs_tgt1 mem_src1 sc_src1, *)
(*       (<<READ: Local.read_step lc_src0 mem_src0 loc to_src val_src released_src ord lc_src1>>) /\ *)
(*       (<<FROM: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) from_src from_tgt>>) /\ *)
(*       (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src to_tgt>>) /\ *)
(*       (<<RELEASED: sim_opt_view (fun loc0 => loc0 <> loc) f (vers loc to_tgt) released_src released_tgt>>) /\ *)
(*       (<<SIM: sim_thread *)
(*                 f vers flag_src flag_tgt vs_src1 vs_tgt1 *)
(*                 mem_src1 mem_tgt1 lc_src1 lc_tgt1 sc_src1 sc_tgt1>>) /\ *)
(*       (<<VALS: forall loc0, *)
(*           ((<<SRC: vs_src1 loc0 = vs_src0 loc0>>) /\ (<<TGT: vs_tgt1 loc0 = vs_tgt0 loc0>>)) \/ *)
(*           (exists val0, *)
(*               (<<VALSRC: vs_src1 loc0 = Some val0>>) /\ (<<VALTGT: vs_tgt1 loc0 = Some val0>>) /\ *)
(*               ((<<ORD: Ordering.le Ordering.acqrel ord>>) \/ *)
(*                ((<<LOC: loc0 = loc>>) /\ (<<VAL: Const.le val val0>>))))>>). *)
(* Proof. *)
(*   hexploit Local.read_step_future; eauto. i. des. *)
(*   destruct lc_src0 as [tvw_src0 prom_src]. *)
(*   destruct lc_tgt0 as [tvw_tgt0 prom_tgt]. *)
(*   dup SIM. inv SIM. inv LOCAL. inv READ. *)
(*   hexploit sim_memory_get; eauto; ss. i. des. inv MSG; ss. *)
(*   assert (exists tvw_src1, (<<READSRC: Local.read_step (Local.mk tvw_src0 prom_src) mem_src loc to_src val vw_src ord (Local.mk tvw_src1 prom_src)>>) /\ *)
(*                            (<<SIM: sim_tview f flag_src rel_vers tvw_src1 (TView.read_tview tvw_tgt0 loc to_tgt released_tgt ord)>>)). *)
(*   { esplits. *)
(*     { econs; eauto. *)
(*       { etrans; eauto. } *)
(*       { ss. inv TVIEW. eapply sim_readable; eauto. } *)
(*     } *)
(*     { ss. eapply sim_read_tview; eauto. *)
(*       { rewrite H0. eapply VERS. } *)
(*       { eapply MEMSRC in GET0. des. *)
(*         eapply message_to_time_le_opt_view; eauto. *)
(*       } *)
(*       { eapply MEMTGT in GET. des. *)
(*         eapply message_to_time_le_opt_view; eauto. *)
(*       } *)
(*     } *)
(*   } *)
(*   des. hexploit Local.read_step_future; eauto. i. des. ss. *)
(*   hexploit sim_thread_acquire; eauto. *)
(*   { i. hexploit FLAG; eauto. i. *)
(*     assert (LOC: loc0 <> loc). *)
(*     { ii. subst. rewrite FLAGTGT in TGT. ss. } *)
(*     inv READSRC. ss. inv LC2. splits. *)
(*     { ss. destruct (Ordering.le Ordering.acqrel ord); ss. *)
(*       rewrite timemap_bot_join_r. *)
(*       unfold TimeMap.join. *)
(*       rewrite TimeFacts.le_join_l; auto. *)
(*       destruct (Ordering.le Ordering.relaxed ord); ss. *)
(*       { rewrite timemap_singleton_neq; auto. eapply Time.bot_spec. } *)
(*       { eapply Time.bot_spec. } *)
(*     } *)
(*     { ss. destruct (Ordering.le Ordering.acqrel ord); ss. *)
(*       rewrite timemap_bot_join_r. *)
(*       unfold TimeMap.join. *)
(*       rewrite TimeFacts.le_join_l; auto. *)
(*       destruct (Ordering.le Ordering.relaxed ord); ss. *)
(*       { rewrite timemap_singleton_neq; auto. eapply Time.bot_spec. } *)
(*       { rewrite timemap_singleton_neq; auto. eapply Time.bot_spec. } *)
(*     } *)
(*   } *)
(*   i. des. esplits; eauto. i. hexploit VALS; eauto. i. des. *)
(*   { left. eauto. } *)
(*   { right. esplits; eauto. destruct (Loc.eq_dec loc0 loc). *)
(*     { subst. right. splits; auto. red in VAL1. des. *)
(*       replace (View.pln (TView.cur tvw_src1) loc) with to_src in VAL1. *)
(*       { rewrite GET0 in VAL1. inv VAL1. etrans; eauto. } *)
(*       symmetry. inv READSRC. inv LC2. ss. *)
(*       eapply read_tview_incr; eauto. *)
(*       { eapply message_to_time_le_opt_view; eauto. *)
(*         eapply MEMSRC; eauto. *)
(*       } *)
(*       { inv READABLE0. ss. } *)
(*     } *)
(*     { left. inv READSRC. inv LC2. ss. *)
(*       destruct (Ordering.le Ordering.acqrel ord); auto. *)
(*       ss. rewrite timemap_bot_join_r in TS. *)
(*       unfold TimeMap.join in TS. rewrite TimeFacts.le_join_l in TS; auto. *)
(*       { timetac. } *)
(*       { destruct (Ordering.le Ordering.relaxed ord); ss. *)
(*         { rewrite timemap_singleton_neq; auto. eapply Time.bot_spec. } *)
(*         { apply Time.bot_spec. } *)
(*       } *)
(*     } *)
(*   } *)
(* Qed. *)





Variant initial_finalized: Messages.t :=
| initial_finalized_intro
    loc
  :
    initial_finalized loc Time.bot Time.bot Message.elt
.

Lemma configuration_initial_finalized s
  :
    finalized (Configuration.init s) = initial_finalized.
Proof.
  extensionality loc.
  extensionality from.
  extensionality to.
  extensionality msg.
  apply Coq.Logic.PropExtensionality.propositional_extensionality.
  split; i.
  { inv H. ss. unfold Memory.init, Memory.get in GET.
    rewrite Cell.init_get in GET. des_ifs. }
  { inv H. econs; eauto. i. ss. unfold Threads.init in *.
    rewrite IdentMap.Facts.map_o in TID. unfold option_map in *. des_ifs.
  }
Qed.

Definition initial_mapping: Mapping.t :=
  Mapping.mk
    (fun v ts =>
       if PeanoNat.Nat.eq_dec v 0 then
         if (Time.eq_dec ts Time.bot) then Some (Time.bot)
         else None
       else None)
    0
    (fun _ ts => ts = Time.bot)
.

Definition initial_vers: versions :=
  fun loc ts =>
    if (Time.eq_dec ts Time.bot) then Some (fun _ => 0) else None.

Section LIFT.
  Let world := (Mapping.ts * versions)%type.

  Let world_bot: world := (fun _ => initial_mapping, initial_vers).

  Let world_messages_le (msgs: Messages.t) (w0: world) (w1: world): Prop :=
    let (f0, vers0) := w0 in
    let (f1, vers1) := w1 in
    Mapping.les f0 f1 /\ versions_le vers0 vers1.

  Let sim_memory (b: bool) (w: world) (views: Loc.t -> Time.t -> list View.t)
      (mem_src: Memory.t) (mem_tgt: Memory.t): Prop :=
    let (f, vers) := w in
    sim_memory (fun _ => None) f vers mem_src mem_tgt.

  Let sim_timemap (w: world)
      (tm_src: TimeMap.t) (tm_tgt: TimeMap.t): Prop :=
    let (f, vers) := w in
    sim_timemap (fun _ => True) f (Mapping.vers f) tm_src tm_tgt.

  Let sim_local (w: world) (views: Loc.t -> Time.t -> list View.t) (lc_src: Local.t) (lc_tgt: Local.t): Prop :=
    let (f, vers) := w in
    sim_local f vers (fun _ => None) (fun _ => None) lc_src lc_tgt.



  Lemma world_messages_le_PreOrder: forall msgs, PreOrder (world_messages_le msgs).
  Proof.
    ii. econs.
    { ii. red. des_ifs. splits; auto.
      { refl. }
      { refl. }
    }
    { ii. unfold world_messages_le in *. des_ifs. des. splits; auto.
      { etrans; eauto. }
      { etrans; eauto. }
    }
  Qed.

  Lemma sim_local_memory_bot:
    forall w views lc_src lc_tgt
           (SIM: sim_local w views lc_src lc_tgt)
           (BOT: (Local.promises lc_tgt) = Memory.bot),
      (Local.promises lc_src) = Memory.bot.
  Proof.
    ii. unfold sim_local in *. des_ifs. inv SIM. ss. subst.
    inv PROMISES. eapply Memory.ext. ii.
    rewrite Memory.bot_get.
    destruct (Memory.get loc ts prom_src) eqn:EQ; auto. destruct p.
    hexploit SOUND; eauto. i. des; ss. rewrite Memory.bot_get in GET. ss.
  Qed.

  Lemma world_messages_le_mon:
    forall msgs0 msgs1 w0 w1
           (LE: world_messages_le msgs1 w0 w1)
           (MSGS: msgs0 <4= msgs1),
      world_messages_le msgs0 w0 w1.
  Proof.
    unfold world_messages_le. ii. des_ifs.
  Qed.

  Lemma sim_lift_gsim lang_src lang_tgt sim_terminal
        (st_src: lang_src.(Language.state)) (st_tgt: lang_tgt.(Language.state))
        (SIM: @sim_seq_all _ _ sim_terminal st_src st_tgt)
    :
      @sim_thread_past
        world world_messages_le sim_memory sim_timemap sim_local
        lang_src lang_tgt sim_terminal false world_bot st_src Local.init TimeMap.bot Memory.init st_tgt Local.init TimeMap.bot Memory.init (JConfiguration.init_views, initial_finalized).
  Proof.
  Admitted.
End LIFT.
