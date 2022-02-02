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

Require Import gSimulation.

Require Import JoinedView.
Require Import SeqLift.
Require Import Simple.

Require Import Pred.

Require Import SeqLiftStep.


Lemma wf_release_vers_versions_le
      vers0 vers1 prom rel_vers
      (WF: wf_release_vers vers0 prom rel_vers)
      (VERSLE: versions_le vers0 vers1)
  :
  wf_release_vers vers1 prom rel_vers.
Proof.
  inv WF. econs. i. hexploit PROM; eauto. i. des.
  esplits; eauto.
Qed.

Lemma sim_local_racy f vers flag_src flag_tgt lc_src lc_tgt mem_src mem_tgt loc ord
      (CONSISTENT: Local.promise_consistent lc_tgt)
      (MEM: sim_memory flag_src f vers mem_src mem_tgt)
      (SIM: sim_local f vers flag_src flag_tgt lc_src lc_tgt)
      (WF: Mapping.wfs f)
      (RACY: Local.is_racy lc_tgt mem_tgt loc ord)
      (FLAGSRC: flag_src loc = None)
  :
    Local.is_racy lc_src mem_src loc ord.
Proof.
  assert (CONSSRC: Local.promise_consistent lc_src).
  { eapply sim_local_consistent; eauto. }
  inv RACY. hexploit sim_memory_get; eauto. i. des. econs; eauto.
  { inv SIM. ss.
    destruct (Memory.get loc to_src prom_src) eqn:EQ; ss.
    destruct p. hexploit sim_promises_get_if; eauto. i. des; ss; clarify.
    { eapply sim_timestamp_exact_unique in TO; eauto; clarify. }
    { hexploit FLAGTGT; eauto. i. subst.
      exploit CONSSRC; eauto. ss. i.



        in EQ; .
  }
  { unfold TView.racy_view in *. eapply sim_timestamp_lt; eauto.
    { inv SIM. ss. eapply TVIEW. auto. }
    { eapply mapping_latest_wf_loc. }
  }
  { inv MSG; ss. }
  { i. hexploit MSG2; auto. i. inv MSG; ss. }
Qed.


Lemma max_value_exists f vers flag_src flag_tgt lc_src lc_tgt mem_src mem_tgt loc v_src
      (MEM: sim_memory flag_src f vers mem_src mem_tgt)
      (LOCAL: sim_local f vers flag_src flag_tgt lc_src lc_tgt)
      (FLAGSRC: flag_src loc = None)
      (MAX: max_value_src loc (Some v_src) mem_src lc_src)
      (LOCALWF: Local.wf lc_tgt mem_tgt)
      (CONSISTENT: Local.promise_consistent lc_tgt)
      (WF: Mapping.wfs f)
  :
  exists v_tgt,
    (<<MAX: max_value_tgt loc (Some v_tgt) mem_tgt lc_tgt>>).
Proof.
  inv MAX. destruct lc_tgt. i. clarify.
  hexploit MAX0; eauto. i. des.
  assert (exists val released, max_readable mem_tgt promises loc (View.pln (TView.cur tview) loc) val released).
  { apply NNPP. ii. hexploit non_max_readable_race.
    { ii. eapply H; eauto. }
    { eauto. }
    { eauto. }
    { i. eapply sim_local_racy in H0; eauto.
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
    i. hexploit sim_promises_get_if; eauto.
    { inv LOCAL. eauto. }
    i. des.
    2:{ rewrite FLAGTGT in *; ss. }
    eapply sim_timestamp_exact_unique in TO; eauto.
    2:{ eapply mapping_latest_wf_loc. }
    subst. clarify.
  }
  { inv H0. clarify. esplits; eauto. inv MSG; auto. }
Qed.


Lemma sim_thread_future
      f0 vers0 flag_tgt vs_src0 vs_tgt0
      mem_src0 mem_tgt0 lc_src0 lc_tgt0 sc_src0 sc_tgt0

      f1 vers1 mem_src1 mem_tgt1 sc_src1 sc_tgt1
      (SIM: sim_thread
              f0 vers0 (fun _ => None) flag_tgt vs_src0 vs_tgt0
              mem_src0 mem_tgt0 lc_src0 lc_tgt0 sc_src0 sc_tgt0)

      (MEMLESRC: Memory.future_weak mem_src0 mem_src1)
      (MEMLETGT: Memory.future_weak mem_tgt0 mem_tgt1)
      (SCSLESRC: TimeMap.le sc_src0 sc_src1)
      (SCSLETGT: TimeMap.le sc_tgt0 sc_tgt1)
      (SIMMEM: sim_memory (fun _ => None) f1 vers1 mem_src1 mem_tgt1)
      (VERSIONED: versioned_memory vers1 mem_tgt1)
      (SIMCLOSED: sim_closed_memory f1 mem_src1)

      (SIMSC: sim_timemap (fun _ => True) f1 (Mapping.vers f1) sc_src1 sc_tgt1)
      (MAPLE: Mapping.les f0 f1)
      (VERSLE: versions_le vers0 vers1)

      (CONSISTENT: Local.promise_consistent lc_tgt0)
      (LOCALSRC: Local.wf lc_src0 mem_src0)
      (LOCALTGT: Local.wf lc_tgt0 mem_tgt0)
      (MEMSRC0: Memory.closed mem_src0)
      (MEMTGT0: Memory.closed mem_tgt0)
      (SCSRC0: Memory.closed_timemap sc_src0 mem_src0)
      (SCTGT0: Memory.closed_timemap sc_tgt0 mem_tgt0)
      (WF0: Mapping.wfs f0)
      (VERS0: versions_wf f0 vers0)

      (MEMSRC1: Memory.closed mem_src1)
      (MEMTGT1: Memory.closed mem_tgt1)
      (SCSRC1: Memory.closed_timemap sc_src1 mem_src1)
      (SCTGT1: Memory.closed_timemap sc_tgt1 mem_tgt1)
      (WF1: Mapping.wfs f1)
      (VERS1: versions_wf f1 vers1)
  :
  exists vs_src1 vs_tgt1,
    (<<SIM: sim_thread
              f1 vers1 (fun _ => None) flag_tgt vs_src1 vs_tgt1
              mem_src1 mem_tgt1 lc_src0 lc_tgt0 sc_src1 sc_tgt1>>) /\
    (<<VALSRC: forall loc val (VAL: vs_src1 loc = Some val), vs_src0 loc = Some val>>) /\
    (<<VALTGT: forall loc val (VAL: vs_tgt1 loc = Some val), vs_tgt0 loc = Some val>>)
.
Proof.
  hexploit (@max_values_src_exists mem_src1 lc_src0).
  intros [vs_src1 MAXSRC1]. des.
  assert (VALSRC: forall loc val (VAL: vs_src1 loc = Some val), vs_src0 loc = Some val).
  { admit. }
  set (vs_tgt1 := fun loc => match vs_src1 loc with
                             | Some _ => vs_tgt0 loc
                             | None => None
                             end).
  esplits.
  { inv SIM. econs.
    { eapply sim_timemap_mon_locs; eauto. i. ss. }
    { eauto. }
    { inv LOCAL. econs; eauto.
      { eapply sim_tview_mon_latest; eauto. }
      { admit. }
      { eapply wf_release_vers_versions_le; eauto. }
    }
    { eauto. }
    { instantiate (1:=vs_tgt1). unfold vs_tgt1.
      ii. hexploit (MAXTGT loc). i. inv H. econs.
      i. des_ifs. hexploit MAX; eauto. i. des.
      max_value_src


      admit.
    }
    { i. unfold vs_tgt1. des_ifs.
      hexploit VALSRC; eauto. i. hexploit (PERM loc).
      rewrite H. auto.
    }
    { eauto. }
    { eauto. }
    { eauto. }
  }
  { auto. }
  { unfold vs_tgt1. i. des_ifs. }
Qed.

  admit.

      eapply


        eauto.

    econs; auto.
    {

  assert (MAXTGT1: max_values_tgt vs_tgt1 mem_tgt1 lc_tgt0).
  { ii.



  hexploit (@max_values__exists mem_src0 lc_src0). i. des.



  max_values_src

Variant sim_thread_sol
        (vs: Loc.t -> Const.t)
        (P: Loc.t -> Prop)
        (D: Loc.t -> Prop)
        mem lc: Prop :=
  | sim_thread_intro
      (CONS: Local.promise_consistent lc)
      (DEBT: forall loc to from msg
                    (GET: Memory.get loc to lc.(Local.promises) = Some (from, msg)),
          (<<MSG: msg <> Message.reserve>>) /\ (<<DEBT: D loc>>))
      (NSYNC: forall loc, Memory.nonsynch_loc loc lc.(Local.promises))
      (VALS: forall loc,
        exists from released,
          (<<GET: Memory.get loc (lc.(Local.tview).(TView.cur).(View.rlx) loc) mem = Some (from, Message.concrete (vs loc) released)>>))
      (PERM: forall loc val released (MAX: max_readable mem lc.(Local.promises) loc (lc.(Local.tview).(TView.cur).(View.pln) loc) val released),
          P loc)
.

Lemma sim_thread_sim_thread_sol
      f vers flag_src flag_tgt vs_src vs_tgt
      mem_src mem_tgt lc_src lc_tgt sc_src sc_tgt D
      (SIM: sim_thread
              f vers flag_src flag_tgt vs_src vs_tgt
              mem_src mem_tgt lc_src lc_tgt sc_src sc_tgt)
      (BOT: lc_tgt.(Local.promises) = Memory.bot)
      (DEBT: forall loc (TGT: flag_src loc = None), flag_tgt loc = None \/ D loc)
      (WF: Mapping.wfs f)
      (LOCAL: Local.wf lc_src mem_src)
  :
  exists vs,
    (<<SIM: sim_thread_sol vs (fun loc => vs_src loc) D mem_src lc_src>>) /\
    (<<VALS: forall loc val (VAL: vs_src loc = Some val), vs loc = val>>)
.
Proof.
  hexploit (choice (fun loc val =>
                      exists from released,
                        (<<GET: Memory.get loc (lc_src.(Local.tview).(TView.cur).(View.rlx) loc) mem_src = Some (from, Message.concrete val released)>>))).
  { inv LOCAL. inv TVIEW_CLOSED. inv CUR.
    intros loc. hexploit (RLX loc). i. des. eauto.
  }
  intros [vs VALS]. inv SIM.
  assert (CONSSRC: Local.promise_consistent lc_src).
  { eapply sim_local_consistent; eauto. eapply Local.bot_promise_consistent; eauto. }
  exists vs. splits.
  { econs; eauto.
    { inv LOCAL0. i. ss.
      hexploit sim_promises_get_if; eauto. i. des.
      { subst. rewrite Memory.bot_get in GET0. ss. }
      { destruct (flag_src loc) eqn:EQ.
        { erewrite sim_promises_none in GET; eauto. ss. }
        { hexploit DEBT; eauto. i. des; clarify. }
      }
    }
    { inv LOCAL0. ss.
      ii. des_ifs. hexploit sim_promises_get_if; eauto. i. des.
      { subst. rewrite Memory.bot_get in GET0. ss. }
      { destruct released; ss. exfalso. eapply SYNC; eauto. }
    }
    { i. ss. hexploit (MAXSRC loc). i. inv H.
      destruct (vs_src loc) eqn:VAL; ss.
      exfalso. eapply NONMAX; eauto.
    }
  }
  { i. hexploit (MAXSRC loc). i. inv H.
    hexploit (VALS loc). i.
    hexploit MAX; eauto. i. des. ss. inv MAX0.
    assert (TS: View.pln (TView.cur tvw) loc = View.rlx (TView.cur tvw) loc).
    { eapply TimeFacts.antisym.
      { eapply LOCAL. }
      destruct (Time.le_lt_dec (View.rlx (TView.cur tvw) loc) (View.pln (TView.cur tvw) loc)); auto.
      exfalso. eapply MAX1 in l; eauto; ss.
      exploit CONSSRC; eauto; ss. i. timetac.
    }
    rewrite TS in *. clarify.
  }
Qed.

Lemma sim_thread_none
      vs P D mem lc
      (SIM: sim_thread_sol vs P D mem lc)
      (DEBT: forall loc, ~ D loc)
  :
  lc.(Local.promises) = Memory.bot.
Proof.
  eapply Memory.ext. i. rewrite Memory.bot_get.
  inv SIM. destruct (Memory.get loc ts lc.(Local.promises)) eqn:GET; auto.
  destruct p. exploit DEBT0; eauto. i. des.
  exfalso. eapply DEBT; eauto.
Qed.

Lemma sim_thread_sol_failure
      vs P D mem lc
      (SIM: sim_thread_sol vs P D mem lc)
  :
  Local.failure_step lc.
Proof.
  inv SIM. econs. eauto.
Qed.

Lemma sim_thread_sol_fence
      vs P D mem lc0 sc ordr ordw
      (SIM: sim_thread_sol vs P D mem lc0)
      (ORDR: ~ Ordering.le Ordering.acqrel ordr)
      (ORDW: ~ Ordering.le Ordering.seqcst ordw)
  :
  exists lc1,
    (<<FENCE: Local.fence_step lc0 sc ordr ordw lc1 sc>>) /\
    (<<SIM: sim_thread_sol vs P D mem lc1>>)
.
Proof.
  inv SIM. esplits.
  { econs; eauto.
    { destruct ordw; ss. }
    { i. destruct ordw; ss. }
  }
  econs; eauto; ss.
  { ii. ss. des_ifs. eapply CONS; eauto. }
  { ii. des_ifs. }
  { ii. des_ifs. eapply PERM; eauto. }
Qed.

Lemma sim_thread_sol_racy
      vs P D mem lc loc
      (SIM: sim_thread_sol vs P D mem lc)
      (LOCAL: Local.wf lc mem)
      (ORD: ~ P loc)
  :
  Local.is_racy lc mem loc Ordering.na.
Proof.
  inv SIM. destruct lc.
  hexploit non_max_readable_race; eauto.
Qed.

Lemma sim_thread_sol_read_na_racy
      vs P D mem lc loc
      (SIM: sim_thread_sol vs P D mem lc)
      (LOCAL: Local.wf lc mem)
      (ORD: ~ P loc)
      val
  :
  Local.racy_read_step lc mem loc val Ordering.na.
Proof.
  econs. eapply sim_thread_sol_racy; eauto.
Qed.

Lemma sim_thread_sol_write_na_racy
      vs P D mem lc loc
      (SIM: sim_thread_sol vs P D mem lc)
      (LOCAL: Local.wf lc mem)
      (ORD: ~ P loc)
  :
  Local.racy_write_step lc mem loc Ordering.na.
Proof.
  econs.
  { eapply sim_thread_sol_racy; eauto. }
  { inv SIM. auto. }
Qed.

Lemma sim_thread_sol_read_na
      vs P D mem lc loc val
      (SIM: sim_thread_sol vs P D mem lc)
      (LOCAL: Local.wf lc mem)
      (VAL: Const.le val (vs loc))
  :
  exists ts released,
    (<<READ: Local.read_step lc mem loc ts val released Ordering.na lc>>)
.
Proof.
  inv SIM. hexploit (VALS loc); eauto. i. des.
  esplits. econs; eauto.
  { econs; ss. eapply LOCAL. }
  destruct lc. f_equal. ss. unfold TView.read_tview. des_ifs.
  ss. rewrite ! View.join_bot_r. rewrite ! View.le_join_l.
  { destruct tview; auto. }
  { eapply View.singleton_rw_spec.
    { eapply LOCAL. }
    { eapply LOCAL. }
  }
  { eapply View.singleton_rw_spec.
    { eapply LOCAL. }
    { refl. }
  }
Qed.

Lemma sim_thread_sol_read
      vs P D mem lc0 loc ord val
      (SIM: sim_thread_sol vs P D mem lc0)
      (LOCAL: Local.wf lc0 mem)
      (ORD: ~ Ordering.le Ordering.acqrel ord)
      (VAL: Const.le val (vs loc))
  :
  exists ts released lc1,
    (<<READ: Local.read_step lc0 mem loc ts val released ord lc1>>) /\
    (<<SIM: sim_thread_sol vs (fun loc0 => P loc0 \/ loc0 = loc) D mem lc1>>)
.
Proof.
  inv SIM. hexploit (VALS loc); eauto. i. des.
  esplits. econs; eauto.
  { econs; ss.
    { eapply LOCAL. }
    { i. refl. }
  }
  destruct lc0 as [tvw0 prom]. ss.
  set (tvw1 := (TView.read_tview
                  tvw0 loc
                  (View.rlx (TView.cur tvw0) loc) released ord)).
  assert (OTHERPLN: forall loc0 (NEQ: loc0 <> loc),
             tvw1.(TView.cur).(View.pln) loc0 = tvw0.(TView.cur).(View.pln) loc0).
  { i. ss. des_ifs. ss. rewrite timemap_bot_join_r.
    unfold TimeMap.join. eapply TimeFacts.le_join_l.
    unfold View.singleton_ur_if. des_ifs; ss.
    { rewrite timemap_singleton_neq; auto. eapply Time.bot_spec. }
    { eapply Time.bot_spec. }
  }
  assert (RLX: forall loc0, tvw1.(TView.cur).(View.rlx) loc0 = tvw0.(TView.cur).(View.rlx) loc0).
  { i. ss. des_ifs. ss. rewrite timemap_bot_join_r.
    unfold TimeMap.join. eapply TimeFacts.le_join_l.
    unfold View.singleton_ur_if. des_ifs; ss.
    { eapply TimeMap.singleton_spec. refl. }
    { eapply TimeMap.singleton_spec. refl. }
  }
  remember tvw1. clear tvw1 Heqt.
  econs; eauto; ss.
  { ii. ss. rewrite RLX. eapply CONS; eauto. }
  { i. rewrite RLX. eauto. }
  { i. destruct (Loc.eq_dec loc0 loc); auto.
    rewrite OTHERPLN in MAX; eauto.
  }
Qed.

Lemma sim_thread_sol_write_na
      vs P D mem0 lc0 sc loc val
      (SIM: sim_thread_sol vs P D mem0 lc0)
      (LOCAL: Local.wf lc0 mem0)
      (MEM: Memory.closed mem0)
      lang st
  :
  Local.racy_write_step lc0 mem0 loc Ordering.na
  \/
  exists lc1 mem1 lc2 mem2 from to msgs kinds kind,
    (<<STEPS: rtc (@Thread.tau_step _)
                  (Thread.mk lang st lc0 sc mem0)
                  (Thread.mk _ st lc1 sc mem1)>>) /\
    (<<WRITE: Local.write_na_step lc1 sc mem1 loc from to val Ordering.na lc2 sc mem2 msgs kinds kind>>) /\
    (<<SIM: sim_thread_sol (fun loc0 => if Loc.eq_dec loc0 loc then val else vs loc0) (fun loc0 => P loc0 \/ loc0 = loc) D mem2 lc2>>)
.
Proof.
  destruct lc0 as [tvw0 prom0].
  destruct (classic (exists val released, <<MAX: max_readable mem0 prom0 loc (tvw0.(TView.cur).(View.pln) loc) val released>>)).
  2:{ left. inv SIM. econs; eauto. eapply non_max_readable_race; eauto. }
  right. des.
  inv SIM. hexploit max_readable_na_write_step; eauto.
  { i. exploit NSYNC; eauto. }
  { refl. }
  { eapply Time.incr_spec. }
  i. des. esplits.
  { eapply reserve_future_steps. eapply cancel_future_reserve_future; eauto. }
  { eauto. }
  assert (OTHERPLN: forall loc0 (NEQ: loc0 <> loc),
             tvw1.(TView.cur).(View.pln) loc0 = tvw0.(TView.cur).(View.pln) loc0).
  { inv WRITE. i. ss. des_ifs. ss.
    unfold TimeMap.join. eapply TimeFacts.le_join_l.
    rewrite timemap_singleton_neq; auto. eapply Time.bot_spec.
  }
  assert (OTHERRLX: forall loc0 (NEQ: loc0 <> loc),
             tvw1.(TView.cur).(View.rlx) loc0 = tvw0.(TView.cur).(View.rlx) loc0).
  { inv WRITE. i. ss. des_ifs. ss.
    unfold TimeMap.join. eapply TimeFacts.le_join_l.
    rewrite timemap_singleton_neq; auto. eapply Time.bot_spec.
  }
  assert (SAMERLX: tvw1.(TView.cur).(View.rlx) loc = tvw1.(TView.cur).(View.pln) loc).
  { rewrite VIEW. inv WRITE. clarify. ss.
    unfold TimeMap.join. rewrite timemap_singleton_eq.
    eapply TimeFacts.le_join_r.
    hexploit (VALS loc). i. des.
    eapply Memory.max_ts_spec in GET. des. etrans; eauto.
    left. eapply Time.incr_spec.
  }
  econs.
  { ii. ss. rewrite PROMISES in PROMISE. des_ifs.
    rewrite OTHERRLX; eauto.
  }
  { ii. ss. rewrite PROMISES in GET. des_ifs. eauto. }
  { ii. ss. rewrite PROMISES in GET. des_ifs. eapply NSYNC in GET; eauto. }
  { ii. ss. des_ifs.
    { rewrite SAMERLX. rewrite VIEW. inv MAX0. eauto. }
    { erewrite Memory.add_o; eauto. des_ifs.
      { ss. des; clarify. }
      clear o. rewrite OTHERRLX; auto.
      inv LOWER. rewrite OTHER; auto.
    }
  }
  { i. ss. destruct (Loc.eq_dec loc0 loc); auto. left.
    inv WRITE. clarify. eapply na_write_unchanged_loc in WRITE0; eauto.
    eapply cancel_future_unchanged_loc in RESERVE; eauto. des.
    rewrite OTHERPLN in MAX1; auto.
    des. eapply PERM. eapply unchanged_loc_max_readable; [..|eauto].
    { etrans; eauto. }
    { etrans; eauto. }
  }
Qed.

Lemma write_tview_other_rlx
      tvw sc loc ts ord loc0
      (NEQ: loc0 <> loc)
  :
  (TView.write_tview tvw sc loc ts ord).(TView.cur).(View.rlx) loc0 = tvw.(TView.cur).(View.rlx) loc0.
Proof.
  ss. des_ifs. ss.
  unfold TimeMap.join. eapply TimeFacts.le_join_l.
  rewrite timemap_singleton_neq; auto. eapply Time.bot_spec.
Qed.

Lemma write_tview_other_pln
      tvw sc loc ts ord loc0
      (NEQ: loc0 <> loc)
  :
  (TView.write_tview tvw sc loc ts ord).(TView.cur).(View.pln) loc0 = tvw.(TView.cur).(View.pln) loc0.
Proof.
  ss. des_ifs. ss.
  unfold TimeMap.join. eapply TimeFacts.le_join_l.
  rewrite timemap_singleton_neq; auto. eapply Time.bot_spec.
Qed.

Lemma write_tview_same_pln
      tvw sc loc ts ord
      (WRITABLE: TView.writable tvw.(TView.cur) sc loc ts ord)
      (TVIEW: TView.wf tvw)
  :
  (TView.write_tview tvw sc loc ts ord).(TView.cur).(View.pln) loc = ts.
Proof.
  ss. unfold TimeMap.join.
  rewrite timemap_singleton_eq; auto. eapply TimeFacts.le_join_r.
  transitivity (View.rlx (TView.cur tvw) loc).
  { eapply TVIEW. }
  { left. eapply WRITABLE. }
Qed.

Lemma write_tview_same_rlx
      tvw sc loc ts ord
      (WRITABLE: TView.writable tvw.(TView.cur) sc loc ts ord)
  :
  (TView.write_tview tvw sc loc ts ord).(TView.cur).(View.rlx) loc = ts.
Proof.
  ss. unfold TimeMap.join.
  rewrite timemap_singleton_eq; auto. eapply TimeFacts.le_join_r.
  left. eapply WRITABLE.
Qed.

Lemma sim_thread_sol_write
      vs P D mem0 lc0 sc loc ord val
      (SIM: sim_thread_sol vs P D mem0 lc0)
      (LOCAL: Local.wf lc0 mem0)
      (MEM: Memory.closed mem0)
  :
  exists lc1 mem1 from to released kind,
    (<<WRITE: Local.write_step lc0 sc mem0 loc from to val None released ord lc1 sc mem1 kind>>) /\
    (<<SIM: sim_thread_sol (fun loc0 => if Loc.eq_dec loc0 loc then val else vs loc0) (fun loc0 => P loc0 \/ loc0 = loc) D mem1 lc1>>)
.
Proof.
  Local Opaque TView.write_tview.
  destruct lc0 as [tvw0 prom0].
  assert (exists lc1 mem1 from to released kind,
             (<<WRITE: Local.write_step (Local.mk tvw0 prom0) sc mem0 loc from to val None released ord lc1 sc mem1 kind>>) /\
             (<<CONS: Local.promise_consistent lc1>>) /\
             (<<NSYNC: forall loc, Memory.nonsynch_loc loc lc1.(Local.promises)>>) /\
             (<<GET: forall from0 to0 msg0 (GET: Memory.get loc to0 lc1.(Local.promises) = Some (from0, msg0)),
               exists from1, Memory.get loc to0 prom0 = Some (from1, msg0)>>)).
  { set (msg := fun ts => Message.concrete val (TView.write_released tvw0 sc loc ts None ord)).
    assert (MSGWF: forall ts, Message.wf (msg ts)).
    { i. unfold msg. econs.
      eapply TViewFacts.write_future0; eauto. eapply LOCAL.
    }
    assert (MSGTO: forall ts (WRITABLE: TView.writable tvw0.(TView.cur) sc loc ts ord), Memory.message_to (msg ts) loc ts).
    { i. econs. eapply writable_message_to; eauto.
      { eapply LOCAL. }
      { eapply WRITABLE. }
      { eapply Time.bot_spec. }
    }
    hexploit (cell_elements_least (prom0 loc) (fun _ => True)).
    i. des.
    { assert (TS: Time.lt from to).
      { hexploit memory_get_ts_strong; eauto. i. des; clarify.
        inv LOCAL. ss. specialize (BOT loc). setoid_rewrite GET in BOT. ss.
      }
      set (ts := Time.middle from to).
      hexploit (Time.middle_spec TS). i. des.
      assert (WRITABLE: TView.writable tvw0.(TView.cur) sc loc ts ord).
      { econs. eapply TimeFacts.le_lt_lt; [|eauto].
        inv SIM. hexploit (VALS loc). i. des.
        eapply memory_get_from_mon; eauto.
        { eapply LOCAL. eauto. }
        exploit CONS; eauto. eapply DEBT; eauto.
      }
      hexploit (@Memory.split_exists prom0 loc from ts to (msg ts) msg0); eauto.
      i. des.
      hexploit Memory.split_exists_le.
      { eapply LOCAL. }
      { eauto. }
      i. des.
      hexploit Memory.remove_exists.
      { eapply Memory.split_get0 in H1. des. eapply GET2. }
      i. des.
      assert (WRITE: Memory.write prom0 mem0 loc from ts (msg ts) mem3 mem1 (Memory.op_kind_split to msg0)).
      { econs; eauto.
        { econs 2; eauto.
          { ss. }
          { inv SIM. eapply DEBT; eauto. }
        }
      }
      esplits.
      { econs; eauto. inv SIM. eauto. }
      { ii. ss. destruct (Loc.eq_dec loc0 loc).
        { subst. rewrite write_tview_same_rlx; auto.
          erewrite Memory.remove_o in PROMISE; eauto.
          erewrite Memory.split_o in PROMISE; eauto. des_ifs.
          { ss. des; clarify. }
          { ss. des; clarify. eapply LEAST in PROMISE; eauto.
            eapply TimeFacts.lt_le_lt; eauto.
          }
        }
        { rewrite write_tview_other_rlx; auto. inv SIM. eapply CONS; eauto.
          ss. erewrite <- Memory.write_get_diff_promise; eauto.
        }
      }
      { ii. ss. inv SIM. erewrite Memory.remove_o in GET0; eauto.
        erewrite Memory.split_o in GET0; eauto. des_ifs.
        { ss. des; clarify. eapply NSYNC in GET; eauto. }
        { eapply NSYNC in GET0; eauto. }
      }
      { i. ss. erewrite Memory.remove_o in GET0; eauto.
        erewrite Memory.split_o in GET0; eauto. des_ifs.
        { ss. des; clarify. esplits. eauto. }
        { eauto. }
      }
    }
    { assert (WRITABLE: TView.writable tvw0.(TView.cur) sc loc (Time.incr (Memory.max_ts loc mem0)) ord).
      { econs. inv SIM. hexploit (VALS loc). i. des.
        eapply Memory.max_ts_spec in GET. des.
        eapply TimeFacts.le_lt_lt.
        { eapply MAX. }
        { eapply Time.incr_spec. }
      }
      hexploit (@Memory.add_exists mem0 loc (Memory.max_ts loc mem0) (Time.incr (Memory.max_ts loc mem0))); eauto.
      { i. eapply Memory.max_ts_spec in GET2. des.
        symmetry. eapply interval_le_disjoint. auto.
      }
      { eapply Time.incr_spec. }
      i. des.
      hexploit Memory.add_exists_le.
      { eapply LOCAL. }
      { eauto. }
      i. des. esplits.
      { econs; eauto.
        { econs; eauto.
          { econs; eauto. i. ss.
            hexploit Memory.max_ts_spec; eauto. i. des.
            eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
            { eapply Time.incr_spec. }
            etrans.
            { eapply memory_get_ts_le. eauto. }
            { eauto. }
          }
          { hexploit Memory.remove_exists.
            { eapply Memory.add_get0. eapply H0. }
            i. des. eapply MemoryMerge.add_remove in H0; eauto.
            subst. eauto.
          }
        }
        { inv SIM. eauto. }
      }
      { ii. ss. destruct (Loc.eq_dec loc0 loc).
        { subst. eapply EMPTY in PROMISE. ss. }
        { rewrite write_tview_other_rlx; auto. inv SIM. eapply CONS; eauto. }
      }
      { inv SIM. eauto. }
      { eauto. }
    }
  }
  des. esplits; eauto. inv SIM. inv WRITE. ss. econs; eauto; ss.
  { i. destruct (Loc.eq_dec loc0 loc).
    { subst. eapply GET in GET0. des. eauto. }
    { erewrite Memory.write_get_diff_promise in GET0; eauto. }
  }
  { i. des_ifs.
    { rewrite write_tview_same_rlx; auto.
      esplits. eapply Memory.write_get2; eauto.
    }
    { rewrite write_tview_other_rlx; auto.
      erewrite Memory.write_get_diff; eauto.
    }
  }
  { i. destruct (Loc.eq_dec loc0 loc); auto. left.
    rewrite write_tview_other_pln in MAX; auto.
    eapply write_unchanged_loc in WRITE0; eauto. des.
    eapply PERM; eauto. eapply unchanged_loc_max_readable; eauto.
  }
Qed.
