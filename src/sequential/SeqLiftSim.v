Require Import RelationClasses.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import Loc.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Language.

From PromisingLib Require Import Event.
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

Require Import LowerMemory.
Require Import JoinedView.

Require Import MaxView.
Require Import Delayed.

Require Import Lia.

Require Import JoinedView.
Require Import SeqLift.
Require Import SeqLiftStep.
Require Import SeqLiftCertification.
Require Import SeqLiftInterference.
Require Import DelayedSimulation.
Require Import SequentialRefinement.
Require Import Sequential.

Require Import Pred.

Require Import SimAux.
Require Import FlagAux.
Require Import SeqAux.
Require Import NoMix.

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
    (fun v ts => v = 0 /\ ts = Time.bot)
.

Definition initial_mappings: Mapping.ts :=
  fun _ => initial_mapping.

Lemma initial_mapping_wf:
  Mapping.wf initial_mapping.
Proof.
  econs.
  { i. ss. exists ([(Time.bot, Time.bot)]).
    i. des_ifs. ss. auto.
  }
  { i. ss. des_ifs. }
  { i. ss. des_ifs.
    { esplits; eauto. refl. }
    { exfalso. lia. }
  }
  { i. ss. des_ifs. exfalso. lia. }
  { ss. }
  { i. ss. exists [Time.bot]. i. des; subst. ss. auto. }
  { i. ss. des; subst. splits; auto. lia. }
  { ss. ii. des. lia. }
  { ss. }
Qed.

Lemma initial_mappings_wf:
  Mapping.wfs initial_mappings.
Proof.
  ii. eapply initial_mapping_wf.
Qed.

Definition initial_ver: version := fun _ => 0.

Definition initial_vers: versions :=
  fun loc ts =>
    if (Time.eq_dec ts Time.bot) then Some initial_ver else None.

Lemma initial_version_wf
  :
  version_wf initial_mappings initial_ver.
Proof.
  ii. ss.
Qed.

Lemma initial_versions_wf:
  versions_wf initial_mappings initial_vers.
Proof.
  ii. unfold initial_vers. des_ifs.
  ss. eapply initial_version_wf.
Qed.

Lemma initial_sim_timestamp_exact
  :
  sim_timestamp_exact initial_mapping 0 Time.bot Time.bot.
Proof.
  ss.
Qed.

Lemma initial_time_closed
  :
  Mapping.closed initial_mapping 0 Time.bot.
Proof.
  ss.
Qed.

Lemma initial_sim_timestamp
  :
  sim_timestamp initial_mapping 0 Time.bot Time.bot.
Proof.
  red. esplits.
  { refl. }
  { refl. }
  { eapply initial_sim_timestamp_exact. }
  { eapply initial_time_closed. }
Qed.

Lemma initial_sim_timemap L:
  sim_timemap L initial_mappings initial_ver TimeMap.bot TimeMap.bot.
Proof.
  ii. eapply initial_sim_timestamp.
Qed.

Lemma initial_sim_view L:
  sim_view L initial_mappings initial_ver View.bot View.bot.
Proof.
  econs.
  { eapply initial_sim_timemap. }
  { eapply initial_sim_timemap. }
Qed.

Lemma initial_sim_tview:
  sim_tview initial_mappings (fun _ => false) (fun _ => initial_ver) TView.bot TView.bot.
Proof.
  econs.
  { i. eapply initial_sim_view. }
  { i. eapply initial_sim_view. }
  { i. eapply initial_sim_view. }
  { i. eapply initial_version_wf. }
Qed.

Lemma initial_sim_promises:
  sim_promises TimeMap.bot (fun _ => false) (fun _ => false) initial_mappings initial_vers Memory.bot Memory.bot.
Proof.
  econs.
  { i. rewrite Memory.bot_get in GET. ss. }
  { i. rewrite Memory.bot_get in GET. ss. }
  { i. ss. }
Qed.

Lemma initial_sim_local
  :
  sim_local initial_mappings initial_vers TimeMap.bot (fun _ => false) (fun _ => false) Local.init Local.init.
Proof.
  econs.
  { eapply initial_sim_tview. }
  { eapply initial_sim_promises. }
  { econs. i. rewrite Memory.bot_get in GET. ss. }
  { i. ss. }
  { i. ss. }
Qed.

Lemma initial_sim_message loc
  :
  sim_message false loc initial_mappings (Some initial_ver) Message.elt Message.elt.
Proof.
  econs; ss. econs.
Qed.

Lemma initial_sim_memory
  :
  sim_memory_interference initial_mappings initial_vers Memory.init Memory.init.
Proof.
  econs.
  { i. eapply memory_init_get_if in GET. des; clarify. esplits.
    { ss. }
    { ss. }
    { eapply initial_sim_message. }
    { i. eapply initial_time_closed. }
  }
  { i. eapply memory_init_get_if in GET. des; clarify. esplits.
    { refl. }
    { refl. }
    { left. splits; eauto. }
    { eapply initial_sim_timestamp_exact. }
    { i. inv ITV. ss. timetac. }
  }
Qed.

Lemma initial_versioned_memory
  :
  versioned_memory initial_vers Memory.init.
Proof.
  econs.
  { i. eapply memory_init_get_if in GET. des; clarify. }
  { i. unfold initial_vers in VER. des_ifs. esplits.
    { eapply memory_init_get. }
    { ss. }
  }
Qed.

Lemma initial_sim_closed_memory
  :
  sim_closed_memory initial_mappings Memory.init.
Proof.
  ii. ss. des; subst. esplits. eapply memory_init_get.
Qed.

Lemma initial_max_readable loc
  :
  max_readable Memory.init Memory.bot loc Time.bot Const.undef None.
Proof.
  econs.
  { eapply memory_init_get. }
  { rewrite Memory.bot_get. auto. }
  { i. eapply memory_init_get_if in GET. des; clarify. timetac. }
Qed.

Lemma initial_sim_thread
  :
  SeqLiftStep.sim_thread
    initial_mappings initial_vers
    (fun _ => false) (fun _ => false)
    (fun _ => Some Const.undef) (fun _ => Some Const.undef)
    Memory.init Memory.init Local.init Local.init TimeMap.bot TimeMap.bot.
Proof.
  econs.
  { eapply initial_sim_timemap. }
  { eapply sim_memory_interference_sim_memory; ss. eapply initial_sim_memory. }
  { eapply initial_sim_local. }
  { ii. econs.
    { i. clarify. esplits. eapply initial_max_readable. }
    { i. ss. }
  }
  { ii. econs.
    i. clarify. esplits. eapply initial_max_readable.
  }
  { ss. }
  { exists []. splits. i. split; i; des; ss. }
  { eapply initial_versioned_memory. }
  { eapply initial_sim_closed_memory. }
  { i. ss. }
  { ii. ss. }
  { ii. ss. erewrite Memory.bot_get in GETSRC. ss. }
Qed.

Require Import Program.

Module CertOracle.
  Definition t := Loc.t -> Const.t.

  Definition output (e: ProgramEvent.t): Oracle.output :=
    Oracle.mk_output
      (if is_accessing e then Some Perm.high else None)
      (if is_acquire e then Some (fun _ => Perm.low, fun _ => Const.undef) else None)
      (if is_release e then Some (fun _ => Perm.high) else None)
  .

  Variant step (e: ProgramEvent.t) (i: Oracle.input) (o: Oracle.output) (vs: t): t -> Prop :=
    | step_read
        loc ord
        (EVENT: e = ProgramEvent.read loc (vs loc) ord)
        (INPUT: Oracle.wf_input e i)
        (OUTPUT: o = output e)
      :
      step e i o vs vs
    | step_write
        loc val ord
        (EVENT: e = ProgramEvent.write loc val ord)
        (INPUT: Oracle.wf_input e i)
        (OUTPUT: o = output e)
      :
      step e i o vs (fun loc0 => if Loc.eq_dec loc0 loc then val else vs loc0)
    | step_update
        loc valw ordr ordw
        (EVENT: e = ProgramEvent.update loc (vs loc) valw ordr ordw)
        (INPUT: Oracle.wf_input e i)
        (OUTPUT: o = output e)
      :
      step e i o vs (fun loc0 => if Loc.eq_dec loc0 loc then valw else vs loc0)
    | step_fence
        ordr ordw
        (EVENT: e = ProgramEvent.fence ordr ordw)
        (INPUT: Oracle.wf_input e i)
        (OUTPUT: o = output e)
      :
      step e i o vs vs
    | step_syscall
        ev
        (EVENT: e = ProgramEvent.syscall ev)
        (INPUT: Oracle.wf_input e i)
        (OUTPUT: o = output e)
      :
      step e i o vs vs
  .

  Definition to_oracle (vs: t): Oracle.t := @Oracle.mk t step vs.

  Lemma to_oracle_wf vs: Oracle.wf (to_oracle vs).
  Proof.
    revert vs. pcofix CIH. i. pfold. econs.
    { i. dependent destruction STEP. inv STEP.
      { splits; auto. red. splits; ss; des_ifs. }
      { splits; auto. red. splits; ss; des_ifs. }
      { splits; auto. red. splits; ss; des_ifs. }
      { splits; auto. red. splits; ss; des_ifs. }
      { splits; auto. red. splits; ss; des_ifs. }
    }
    { i. exists (vs loc). splits.
      { econs. esplits.
        { econs. eapply step_read; eauto. }
        { red. splits; ss; des_ifs. }
      }
      { i. econs. esplits.
        { econs. eapply step_update; eauto. }
        { red. splits; ss; des_ifs. }
      }
    }
    { i. econs. esplits.
      { econs. eapply step_write; eauto. }
      { red. splits; ss; des_ifs. }
    }
    { i. econs. esplits.
      { econs. eapply step_fence; eauto. }
      { red. splits; ss; des_ifs. }
    }
    { i. econs. esplits.
      { econs. eapply step_syscall; eauto. }
      { red. splits; ss; des_ifs. }
    }
  Qed.
End CertOracle.


Section LIFT.
  Variable loc_na: Loc.t -> Prop.
  Variable loc_at: Loc.t -> Prop.
  Hypothesis LOCDISJOINT: forall loc (NA: loc_na loc) (AT: loc_at loc), False.

  Definition sim_seq_interference lang_src lang_tgt sim_terminal p0 D st_src st_tgt :=
    forall p1 (PERM: Perms.le p1 p0),
      @sim_seq lang_src lang_tgt sim_terminal p1 D st_src st_tgt.

  Lemma sim_seq_interference_mon lang_src lang_tgt sim_terminal p0 D st_src st_tgt
        (SIM: @sim_seq_interference _ _ sim_terminal p0 D st_src st_tgt)
        p1 (PERM: Perms.le p1 p0)
    :
    @sim_seq_interference lang_src lang_tgt sim_terminal p1 D st_src st_tgt.
  Proof.
    ii. eapply SIM. etrans; eauto.
  Qed.

  Lemma sim_seq_interference_sim_seq lang_src lang_tgt sim_terminal p D st_src st_tgt
        (SIM: @sim_seq_interference _ _ sim_terminal p D st_src st_tgt)
    :
    @sim_seq lang_src lang_tgt sim_terminal p D st_src st_tgt.
  Proof.
    eapply SIM. refl.
  Qed.

  Lemma perm_antisym p0 p1
        (LE0: Perm.le p0 p1)
        (LE1: Perm.le p1 p0)
    :
    p0 = p1.
  Proof.
    destruct p0, p1; ss.
  Qed.

  Lemma perms_antisym p0 p1
        (LE0: Perms.le p0 p1)
        (LE1: Perms.le p1 p0)
    :
    p0 = p1.
  Proof.
    extensionality loc. eapply perm_antisym; eauto.
  Qed.

  Definition perms_top: Perms.t := fun _ => Perm.high.

  Definition seq_memory_init: SeqMemory.t := (SeqMemory.mk (fun _ => Const.undef) Flags.bot).

  Lemma sim_seq_init lang_src lang_tgt sim_terminal st_src st_tgt
        (SIM: @sim_seq_all lang_src lang_tgt sim_terminal st_src st_tgt)
    :
    sim_seq_interference
      _ _ sim_terminal
      perms_top Flags.bot
      (SeqState.mk _ st_src seq_memory_init)
      (SeqState.mk _ st_tgt seq_memory_init).
  Proof.
    ii. eapply SIM.
  Qed.

  Definition world := (Mapping.ts * versions * Memory.t)%type.

  Definition world_bot: world := (fun _ => initial_mapping, initial_vers, Memory.init).

  Definition sim_seq_cond (c: bool)
             lang_src lang_tgt sim_terminal p D st_src st_tgt :=
    if c
    then @sim_seq lang_src lang_tgt sim_terminal p D st_src st_tgt
    else @sim_seq_interference lang_src lang_tgt sim_terminal p D st_src st_tgt.

  Definition world_messages_le (msgs_src msgs_tgt: Messages.t) (w0: world) (w1: world): Prop :=
        match w0, w1 with
        | (f0, vers0, mem_src0), (f1, vers1, mem_src1) =>
            forall (WF: Mapping.wfs f0),
              (<<MAPLE: Mapping.les f0 f1>>) /\ (<<VERLE: versions_le vers0 vers1>>) /\
                (<<MEMSRC: Memory.future_weak mem_src0 mem_src1>>) /\
                (<<FUTURE: map_future_memory f0 f1 mem_src1>>) /\
                (<<WF: Mapping.wfs f1>>) /\
                (<<SPACE: space_future_memory msgs_tgt f0 mem_src0 f1 mem_src1>>)
        end
  .

  Global Program Instance world_messages_le_PreOrder msgs_src msgs_tgt: PreOrder (world_messages_le msgs_src msgs_tgt).
  Next Obligation.
    unfold world_messages_le. ii. des_ifs. splits.
    { refl. }
    { refl. }
    { refl. }
    { eapply map_future_memory_refl. }
    { auto. }
    { eapply space_future_memory_refl; eauto. refl. }
  Qed.
  Next Obligation.
    unfold world_messages_le. ii. des_ifs. i.
    hexploit H; eauto. i. des.
    hexploit H0; eauto. i. des.
    splits.
    { etrans; eauto. }
    { etrans; eauto. }
    { etrans; eauto. }
    { eapply map_future_memory_trans; eauto. }
    { eauto. }
    { eapply space_future_memory_trans; eauto. }
  Qed.

  Definition initial_world: world := (initial_mappings, initial_vers, Memory.init).

  Lemma world_messages_le_mon:
    forall msgs_src0 msgs_tgt0 msgs_src1 msgs_tgt1 w0 w1
           (LE: world_messages_le msgs_src1 msgs_tgt1 w0 w1)
           (MSGSRC: msgs_src0 <4= msgs_src1)
           (MSGTGT: msgs_tgt0 <4= msgs_tgt1),
      world_messages_le msgs_src0 msgs_tgt0 w0 w1.
  Proof.
    unfold world_messages_le. i. des_ifs. i.
    hexploit LE; eauto. i. des. splits; auto.
    eapply space_future_memory_mon_msgs; eauto.
  Qed.

  Definition sim_memory_lift: forall (w: world) (mem_src mem_tgt:Memory.t), Prop :=
    fun w mem_src mem_tgt =>
      match w with
      | (f, vers, mem_src') =>
          (<<MEMSRC: mem_src = mem_src'>>) /\
            (<<SIM: sim_memory_interference f vers mem_src mem_tgt>>) /\
            (<<VERSIONED: versioned_memory vers mem_tgt>>) /\
            (<<SIMCLOSED: sim_closed_memory f mem_src>>) /\
            (<<VERSWF: versions_wf f vers>>)
      end.

  Lemma initial_sim_memory_lift:
    sim_memory_lift initial_world Memory.init Memory.init.
  Proof.
    ss. splits; auto.
    { eapply initial_sim_memory. }
    { eapply initial_versioned_memory. }
    { eapply initial_sim_closed_memory. }
    { eapply initial_versions_wf. }
  Qed.

  Definition sim_timemap_lift: forall (w: world) (tm_src: TimeMap.t) (tm_tgt: TimeMap.t), Prop :=
    fun w tm_src tm_tgt =>
      match w with
      | (f, vers, _) =>
          (<<SIM: sim_timemap (fun _ => True) f (Mapping.vers f) tm_src tm_tgt>>)
      end.

  Lemma initial_sim_timemap_lift:
    sim_timemap_lift initial_world TimeMap.bot TimeMap.bot.
  Proof.
    ss. splits; auto.
    eapply initial_sim_timemap.
  Qed.

  Variant sim_val_lift: forall
      (p: Perm.t)
      (sv_src: Const.t) (sv_tgt: Const.t)
      (v_src: option Const.t) (v_tgt: option Const.t), Prop :=
    | sim_val_lift_low
        sv_src sv_tgt
      :
      sim_val_lift Perm.low sv_src sv_tgt None None
    | sim_val_lift_high
        sv_src sv_tgt v_src v_tgt
        (VALSRC: Const.le sv_src v_src)
        (VALTGT: Const.le v_tgt sv_tgt)
      :
      sim_val_lift Perm.high sv_src sv_tgt (Some v_src) (Some v_tgt)
  .

  Definition sim_vals_lift
             (p: Perms.t) (svs_src: ValueMap.t) (svs_tgt: ValueMap.t)
             (vs_src: Loc.t -> option Const.t) (vs_tgt: Loc.t -> option Const.t): Prop :=
    forall loc (NA: loc_na loc), sim_val_lift (p loc) (svs_src loc) (svs_tgt loc) (vs_src loc) (vs_tgt loc).

  Variant sim_flag_lift
          (d: Flag.t) (sflag_src: Flag.t) (sflag_tgt: Flag.t)
          (flag_src: bool) (flag_tgt: bool): Prop :=
    | sim_flag_lift_intro
        (TGT: Flag.le flag_tgt (Flag.join flag_src (Flag.join d sflag_tgt)))
        (SRC: sflag_src = flag_src)
  .

  Definition sim_flags_lift
             (d: Flags.t) (sflag_src: Flags.t) (sflag_tgt: Flags.t)
             (flag_src: Loc.t -> bool) (flag_tgt: Loc.t -> bool): Prop :=
    forall loc, sim_flag_lift (d loc) (sflag_src loc) (sflag_tgt loc) (flag_src loc) (flag_tgt loc).

  Variant sim_state_lift c:
    forall (w: world)
           (smem_src: SeqMemory.t) (smem_tgt: SeqMemory.t)
           (p: Perms.t)
           (D: Flags.t)
           (mem_src: Memory.t)
           (mem_tgt: Memory.t)
           (lc_src: Local.t)
           (lc_tgt: Local.t)
           (sc_src: TimeMap.t)
           (sc_tgt: TimeMap.t), Prop :=
    | sim_state_lift_intro
        svs_src sflag_src svs_tgt sflag_tgt
        p D f vers flag_src flag_tgt vs_src vs_tgt
        mem_src mem_tgt lc_src lc_tgt sc_src sc_tgt
        (SIM: SeqLiftStep.sim_thread f vers flag_src flag_tgt vs_src vs_tgt mem_src mem_tgt lc_src lc_tgt sc_src sc_tgt)
        (VALS: sim_vals_lift p svs_src svs_tgt vs_src vs_tgt)
        (FLAGS: sim_flags_lift D sflag_src sflag_tgt flag_src flag_tgt)
        (ATLOCS: forall loc (NNA: ~ loc_na loc),
            (<<FLAGSRC: flag_src loc = false>>) /\
              (<<FLAGTGT: flag_tgt loc = false>>) /\
              (<<VAL: option_rel Const.le (vs_tgt loc) (vs_src loc)>>))
        (INTERFERENCE: c = false -> flag_src = fun _ => false)
        (MAPWF: Mapping.wfs f)
        (VERSWF: versions_wf f vers)
      :
      sim_state_lift
        c
        (f, vers, mem_src)
        (SeqMemory.mk svs_src sflag_src) (SeqMemory.mk svs_tgt sflag_tgt)
        p D
        mem_src mem_tgt lc_src lc_tgt sc_src sc_tgt
  .

  Lemma sim_state_lift_cond_mon c0 c1
        w smem_src smem_tgt p D mem_src mem_tgt lc_src lc_tgt sc_src sc_tgt
        (SIM: sim_state_lift c0 w smem_src smem_tgt p D mem_src mem_tgt lc_src lc_tgt sc_src sc_tgt)
        (COND: c1 = false -> c0 = false)
    :
    sim_state_lift c1 w smem_src smem_tgt p D mem_src mem_tgt lc_src lc_tgt sc_src sc_tgt.
  Proof.
    inv SIM. econs; eauto.
  Qed.

  Lemma rtc_steps_thread_failure lang th0 th1
        (STEPS: rtc (@Thread.tau_step lang) th0 th1)
        (FAILURE: Thread.steps_failure th1)
    :
    Thread.steps_failure th0.
  Proof.
    unfold Thread.steps_failure in *. des. esplits.
    { etrans; eauto. }
    { eauto. }
    { eauto. }
  Qed.

  Lemma sim_thread_lift_init
    :
    sim_state_lift
      false initial_world seq_memory_init seq_memory_init perms_top Flags.bot
      Memory.init Memory.init Local.init Local.init TimeMap.bot TimeMap.bot.
  Proof.
    econs.
    { eapply initial_sim_thread. }
    { ii. econs; auto. }
    { ii. econs; auto. }
    { i. splits; ss. }
    { ss. }
    { eapply initial_mappings_wf. }
    { eapply initial_versions_wf. }
  Qed.

  Lemma sim_lift_tgt_na_write_step:
    forall
      c w0 p D smem_src smem_tgt0 mem_src0 mem_tgt0 lc_src0 lc_tgt0 sc_src0 sc_tgt0
      mem_tgt1 lc_tgt1 sc_tgt1
      loc from to val msgs kinds kind
      (LIFT: sim_state_lift c w0 smem_src smem_tgt0 p D mem_src0 mem_tgt0 lc_src0 lc_tgt0 sc_src0 sc_tgt0)
      (STEP: Local.write_na_step lc_tgt0 sc_tgt0 mem_tgt0 loc from to val Ordering.na lc_tgt1 sc_tgt1 mem_tgt1 msgs kinds kind)
      (NALOCS: loc_na loc)
      (LOWER: mem_tgt1 = mem_tgt0)
      (CONSISTENT: Local.promise_consistent lc_tgt1)
      (WF_SRC: Local.wf lc_src0 mem_src0)
      (WF_TGT: Local.wf lc_tgt0 mem_tgt0)
      (SC_SRC: Memory.closed_timemap sc_src0 mem_src0)
      (SC_TGT: Memory.closed_timemap sc_tgt0 mem_tgt0)
      (MEM_SRC: Memory.closed mem_src0)
      (MEM_TGT: Memory.closed mem_tgt0)
      lang_src st_src,
    exists lc_src1 mem_src1 sc_src1 me smem_tgt1,
      (<<STEPS: rtc (@Thread.tau_step lang_src) (Thread.mk _ st_src lc_src0 sc_src0 mem_src0) (Thread.mk _ st_src lc_src1 sc_src1 mem_src1)>>) /\
        (<<STEP: SeqState.na_local_step p me (ProgramEvent.write loc val Ordering.na) smem_tgt0 smem_tgt1>>) /\
        (<<LIFTAUX: forall (FAILURE: me = MachineEvent.failure),
            exists w1,
              (<<LIFT: sim_state_lift true w1 smem_src smem_tgt0 p D mem_src1 mem_tgt0 lc_src1 lc_tgt0 sc_src1 sc_tgt0>>) /\
              (<<WORLD: world_messages_le (unchangable mem_src0 lc_src0.(Local.promises)) (unchangable mem_tgt0 lc_tgt0.(Local.promises)) w0 w1>>)>>) /\
        (<<LIFT: forall (NORMAL: me <> MachineEvent.failure),
          exists w1,
            (<<LIFT: sim_state_lift true w1 smem_src smem_tgt1 p D mem_src1 mem_tgt1 lc_src1 lc_tgt1 sc_src1 sc_tgt1>>) /\
              (<<WORLD: world_messages_le (unchangable mem_src0 lc_src0.(Local.promises)) (unchangable mem_tgt0 lc_tgt0.(Local.promises)) w0 w1>>)>>).
  Proof.
    i. inv LIFT. destruct (vs_tgt loc) eqn:VAL.
    { hexploit sim_thread_tgt_write_na; eauto. i. des. esplits.
      { eauto. }
      { econs 3; eauto. }
      { i. hexploit (VALS loc); auto. i.
        rewrite VAL in H. inv H.
        rewrite <- H1 in *. ss.
      }
      { i. subst. esplits; eauto.
        { econs; eauto.
          { ii. unfold ValueMap.write. des_ifs; ss.
            { des_ifs. hexploit (VALS loc); auto. i.
              rewrite VAL in *. rewrite Heq0 in *.
              inv H. econs; eauto. refl.
            }
            { eapply VALS; eauto. }
          }
          { ss. unfold Flags.update. ii. des_ifs.
            { econs; ss; auto.
              { i. destruct (flag_src loc), (D loc); ss. }
              { eapply FLAGS; auto. }
            }
          }
          { i. ss. des_ifs. eapply ATLOCS; eauto. }
          { ss. }
        }
        { ss. splits; auto.
          { refl. }
          { refl. }
          { eapply Thread.rtc_tau_step_future in STEPS; eauto.
            i. des; ss. eapply Memory.future_future_weak; auto.
          }
          { eapply map_future_memory_refl. }
        }
      }
    }
    { esplits.
      { refl. }
      { econs 3; ss. }
      { i. esplits.
        { econs; eauto. ss. }
        { refl. }
      }
      { i. hexploit (VALS loc); auto. i.
        rewrite VAL in H. inv H.
        rewrite <- H1 in *. ss.
      }
    }
  Qed.

  Lemma sim_lift_tgt_na_local_step:
    forall
      c w0 p D smem_src smem_tgt0 mem_src0 mem_tgt0 lc_src0 lc_tgt0 sc_src0 sc_tgt0
      e pe mem_tgt1 lc_tgt1 sc_tgt1
      (LIFT: sim_state_lift c w0 smem_src smem_tgt0 p D mem_src0 mem_tgt0 lc_src0 lc_tgt0 sc_src0 sc_tgt0)
      (STEP: Local.program_step e lc_tgt0 sc_tgt0 mem_tgt0 lc_tgt1 sc_tgt1 mem_tgt1)
      (EVENT: ThreadEvent.get_program_event e = pe)
      (NA: ~ is_atomic_event pe)
      (NALOCS: forall loc val (ACCESS: is_accessing pe = Some (loc, val)), loc_na loc)
      (LOWER: is_na_write e -> mem_tgt1 = mem_tgt0)

      (CONSISTENT: Local.promise_consistent lc_tgt1)
      (WF_SRC: Local.wf lc_src0 mem_src0)
      (WF_TGT: Local.wf lc_tgt0 mem_tgt0)
      (SC_SRC: Memory.closed_timemap sc_src0 mem_src0)
      (SC_TGT: Memory.closed_timemap sc_tgt0 mem_tgt0)
      (MEM_SRC: Memory.closed mem_src0)
      (MEM_TGT: Memory.closed mem_tgt0)
      lang_src st_src,
    exists lc_src1 mem_src1 sc_src1 me smem_tgt1,
      (<<STEPS: rtc (@Thread.tau_step lang_src) (Thread.mk _ st_src lc_src0 sc_src0 mem_src0) (Thread.mk _ st_src lc_src1 sc_src1 mem_src1)>>) /\
        (<<STEP: SeqState.na_local_step p me pe smem_tgt0 smem_tgt1>>) /\
        (<<LIFTAUX: forall (FAILURE: me = MachineEvent.failure),
            exists w1,
              (<<LIFT: sim_state_lift true w1 smem_src smem_tgt0 p D mem_src1 mem_tgt0 lc_src1 lc_tgt0 sc_src1 sc_tgt0>>) /\
                (<<WORLD: world_messages_le (unchangable mem_src0 lc_src0.(Local.promises)) (unchangable mem_tgt0 lc_tgt0.(Local.promises)) w0 w1>>)>>) /\
        (<<LIFT: forall (NORMAL: me <> MachineEvent.failure),
            exists w1,
              (<<LIFT: sim_state_lift true w1 smem_src smem_tgt1 p D mem_src1 mem_tgt1 lc_src1 lc_tgt1 sc_src1 sc_tgt1>>) /\
                (<<WORLD: world_messages_le (unchangable mem_src0 lc_src0.(Local.promises)) (unchangable mem_tgt0 lc_tgt0.(Local.promises)) w0 w1>>) /\
                (<<NFAILURE: ThreadEvent.get_machine_event e = MachineEvent.silent>>)>>)
  .
  Proof.
    i. inv STEP; ss.
    { esplits.
      { refl. }
      { econs 1. }
      { ss. }
      { i. esplits; eauto.
        { eapply sim_state_lift_cond_mon; eauto. ss. }
        { refl. }
      }
    }
    { inv LIFT. destruct ord; ss. hexploit sim_thread_tgt_read_na; eauto.
      i. des. esplits.
      { refl. }
      { econs 2; eauto. i. ss. hexploit (VALS loc); eauto. i. inv H0.
        { des_ifs. }
        hexploit VAL; eauto. i. etrans; eauto.
      }
      { ss. }
      { i. esplits.
        { econs; eauto. ss. }
        { ss. i. splits; auto; try refl.
          { eapply map_future_memory_refl. }
          { eapply space_future_memory_refl; eauto. refl. }
        }
        { ss. }
      }
    }
    { destruct ord; ss. eapply local_write_step_write_na_step in LOCAL.
      hexploit sim_lift_tgt_na_write_step; eauto. i. des. esplits; eauto.
      i. hexploit LIFT0; eauto. i. des. esplits; eauto.
    }
    { esplits.
      { refl. }
      { econs 5. red. destruct ordr, ordw; ss; auto. }
      { i. esplits; eauto.
        { eapply sim_state_lift_cond_mon; eauto. ss. }
        { refl. }
      }
      { ss. }
    }
    { esplits.
      { refl. }
      { econs 4. }
      { i. esplits; eauto.
        { eapply sim_state_lift_cond_mon; eauto. ss. }
        { refl. }
      }
      { ss. }
    }
    { destruct ord; ss. hexploit sim_lift_tgt_na_write_step; eauto.
      i. des. esplits; eauto. i. hexploit LIFT0; eauto. i. des. esplits; eauto.
    }
    { inv LIFT. destruct ord; ss. hexploit sim_thread_tgt_read_na_racy; eauto.
      i. esplits.
      { refl. }
      { econs 2; eauto. i. hexploit (VALS loc); eauto. i.
        rewrite H in H1. inv H1.
        rewrite <- H3 in *. ss.
      }
      { ss. }
      { i. esplits.
        { econs; eauto. ss. }
        { ss. i. splits; auto; try refl.
          { eapply map_future_memory_refl. }
          { eapply space_future_memory_refl; eauto. refl. }
        }
        { ss. }
      }
    }
    { inv LIFT. destruct ord; ss. hexploit sim_thread_tgt_write_na_racy; eauto.
      i. esplits.
      { refl. }
      { econs 3; eauto. }
      { i. esplits.
        { econs; eauto. ss. }
        { ss. i. splits; auto; try refl.
          { eapply map_future_memory_refl. }
          { eapply space_future_memory_refl; eauto. refl. }
        }
      }
      { i. hexploit (VALS loc); eauto. i. rewrite H in H0. inv H0.
        rewrite <- H2 in *. ss.
      }
    }
    { esplits.
      { refl. }
      { econs 5. red. destruct ordr, ordw; ss; auto. }
      { i. esplits.
        { eapply sim_state_lift_cond_mon; eauto. ss. }
        { refl. }
      }
      { ss. }
    }
  Qed.

  Lemma sim_lift_src_na_local_step:
    forall
      c w0 p D smem_src0 smem_tgt mem_src0 mem_tgt lc_src0 lc_tgt sc_src0 sc_tgt
      pe me smem_src1
      (LIFT: sim_state_lift c w0 smem_src0 smem_tgt p D mem_src0 mem_tgt lc_src0 lc_tgt sc_src0 sc_tgt)
      (STEP: SeqState.na_local_step p me pe smem_src0 smem_src1)
      (NA: ~ is_atomic_event pe)
      (NALOCS: forall loc val (ACCESS: is_accessing pe = Some (loc, val)), loc_na loc)

      (CONSISTENT: Local.promise_consistent lc_tgt)
      (WF_SRC: Local.wf lc_src0 mem_src0)
      (WF_TGT: Local.wf lc_tgt mem_tgt)
      (SC_SRC: Memory.closed_timemap sc_src0 mem_src0)
      (SC_TGT: Memory.closed_timemap sc_tgt mem_tgt)
      (MEM_SRC: Memory.closed mem_src0)
      (MEM_TGT: Memory.closed mem_tgt)
      lang_src st_src,
    exists lc_src1 mem_src1 sc_src1 lc_src2 mem_src2 sc_src2 e,
      (<<STEPS: rtc (@Thread.tau_step lang_src) (Thread.mk _ st_src lc_src0 sc_src0 mem_src0) (Thread.mk _ st_src lc_src1 sc_src1 mem_src1)>>) /\
        (<<STEP: Local.program_step e lc_src1 sc_src1 mem_src1 lc_src2 sc_src2 mem_src2>>) /\
        (<<MACHINE: ThreadEvent.get_machine_event e = me>>) /\
        (<<EVENT: ThreadEvent.get_program_event e = pe>>) /\
        (<<LIFT: forall (NORMAL: ThreadEvent.get_machine_event e <> MachineEvent.failure),
          exists w1,
            (<<LIFT: sim_state_lift true w1 smem_src1 smem_tgt p D mem_src2 mem_tgt lc_src2 lc_tgt sc_src2 sc_tgt>>) /\
              (<<WORLD: world_messages_le (unchangable mem_src0 lc_src0.(Local.promises)) (unchangable mem_tgt lc_tgt.(Local.promises)) w0 w1>>)>>).
  Proof.
    i. inv STEP.
    { esplits.
      { refl. }
      { eapply Local.step_silent. }
      { ss. }
      { ss. }
      { i. esplits; eauto.
        { eapply sim_state_lift_cond_mon; eauto. ss. }
        { refl. }
      }
    }
    { inv LIFT. ss. hexploit (VALS loc); eauto. i. inv H.
      { hexploit sim_thread_src_read_na_racy; eauto. i. des.
        esplits.
        { refl. }
        { eapply Local.step_racy_read; eauto. }
        { ss. }
        { ss. destruct ord; ss. }
        { i. esplits; eauto.
          { econs; eauto. ss. }
          { ss. i. splits; auto; try refl.
            { eapply map_future_memory_refl. }
            { eapply space_future_memory_refl; eauto. refl. }
          }
        }
      }
      { hexploit sim_thread_src_read_na.
        { eauto. }
        { eauto. }
        { instantiate (1:=val). etrans; eauto.
          ss. rewrite <- H1 in *. auto.
        }
        { auto. }
        i. des.
        esplits.
        { refl. }
        { eapply Local.step_read; eauto. }
        { ss. }
        { ss. destruct ord; ss. }
        { i. esplits.
          { econs; eauto. ss. }
          { ss. i. splits; auto; try refl.
            { eapply map_future_memory_refl. }
            { eapply space_future_memory_refl; eauto. refl. }
          }
        }
      }
    }
    { inv LIFT. ss. hexploit (VALS loc); eauto. i. inv H.
      { hexploit sim_thread_src_write_na_racy; eauto.
        i. des. esplits.
        { refl. }
        { eapply Local.step_racy_write; eauto. }
        { ss. }
        { ss. destruct ord; ss. }
        { ss. }
      }
      { hexploit sim_thread_src_write_na; eauto.
        i. des. esplits.
        { eauto. }
        { eapply Local.step_write_na; eauto. }
        { ss. }
        { ss. destruct ord; ss. }
        { i. esplits.
          { econs; eauto.
            { ss. unfold ValueMap.write. ii. des_ifs.
              { rewrite <- H1. rewrite <- H5. econs; eauto. refl. }
              { eapply VALS; auto. }
            }
            { ss. unfold Flags.update. ii. des_ifs.
            }
            { i. ss. des_ifs.
              { exfalso. eapply NNA; eauto. }
              { eapply ATLOCS; eauto. }
            }
            { ss. }
          }
          { ss. i. splits; auto; try refl.
            { eapply Thread.rtc_tau_step_future in STEPS; eauto.
              des; ss.
              hexploit Local.write_na_step_future; eauto.
              i. des; ss.
              eapply Memory.future_future_weak; eauto. etrans; eauto.
            }
            { eapply map_future_memory_refl. }
          }
        }
      }
    }
    { inv LIFT. esplits.
      { refl. }
      { eapply Local.step_failure. econs.
        inv SIM. eapply sim_local_consistent; eauto.
      }
      { ss. }
      { ss. }
      { ss. }
    }
    { inv LIFT. esplits.
      { refl. }
      { instantiate (4:=ThreadEvent.racy_update loc Time.bot valr valw ordr ordw).
        inv SIM. eapply sim_local_consistent in CONSISTENT; eauto.
        eapply Local.step_racy_update. red in ORD. des.
        { econs 1; eauto. }
        { econs 2; eauto. }
      }
      { ss. }
      { ss. }
      { ss. }
    }
  Qed.

  Lemma sim_lift_src_na_step:
    forall
      c w0 p D smem_src0 smem_tgt mem_src0 mem_tgt lc_src0 lc_tgt sc_src0 sc_tgt
      me smem_src1
      lang_src st_src0 st_src1
      (LIFT: sim_state_lift c w0 smem_src0 smem_tgt p D mem_src0 mem_tgt lc_src0 lc_tgt sc_src0 sc_tgt)
      (STEP: SeqState.na_step p me (SeqState.mk _ st_src0 smem_src0) (SeqState.mk _ st_src1 smem_src1))
      (NOMIX: nomix loc_na loc_at _ st_src0)
      (CONSISTENT: Local.promise_consistent lc_tgt)
      (WF_SRC: Local.wf lc_src0 mem_src0)
      (WF_TGT: Local.wf lc_tgt mem_tgt)
      (SC_SRC: Memory.closed_timemap sc_src0 mem_src0)
      (SC_TGT: Memory.closed_timemap sc_tgt mem_tgt)
      (MEM_SRC: Memory.closed mem_src0)
      (MEM_TGT: Memory.closed mem_tgt),
    exists lc_src1 mem_src1 sc_src1 lc_src2 mem_src2 sc_src2 e pf,
      (<<STEPS: rtc (@Thread.tau_step lang_src) (Thread.mk _ st_src0 lc_src0 sc_src0 mem_src0) (Thread.mk _ st_src0 lc_src1 sc_src1 mem_src1)>>) /\
        (<<STEP: Thread.step pf e (Thread.mk _ st_src0 lc_src1 sc_src1 mem_src1) (Thread.mk _ st_src1 lc_src2 sc_src2 mem_src2)>>) /\
        (<<MACHINE: ThreadEvent.get_machine_event e = me>>) /\
        (<<LIFT: forall (NORMAL: ThreadEvent.get_machine_event e <> MachineEvent.failure),
          exists w1,
            (<<LIFT: sim_state_lift true w1 smem_src1 smem_tgt p D mem_src2 mem_tgt lc_src2 lc_tgt sc_src2 sc_tgt>>) /\
              (<<WORLD: world_messages_le (unchangable mem_src0 lc_src0.(Local.promises)) (unchangable mem_tgt lc_tgt.(Local.promises)) w0 w1>>)>>) /\
        (<<NOMIX: nomix loc_na loc_at _ st_src1>>)
  .
  Proof.
    i. inv STEP.
    punfold NOMIX. exploit NOMIX; eauto. i. des.
    hexploit sim_lift_src_na_local_step; eauto.
    { inv LOCAL; ss.
      { destruct ord; ss. }
      { destruct ord; ss. }
      { red in ORD. des; destruct ordr, ordw; ss. }
    }
    { i. eapply NA; eauto. inv LOCAL; ss.
      { destruct ord; ss. }
      { destruct ord; ss. }
      { red in ORD. destruct ordr, ordw; des; ss. }
    }
    i. des. subst. esplits; eauto.
    { econs 2; eauto. econs; eauto. }
    pclearbot. auto.
  Qed.

  Lemma sim_lift_src_na_opt_step:
    forall
      c w0 p D smem_src0 smem_tgt mem_src0 mem_tgt lc_src0 lc_tgt sc_src0 sc_tgt
      me smem_src1
      lang_src st_src0 st_src1
      (LIFT: sim_state_lift c w0 smem_src0 smem_tgt p D mem_src0 mem_tgt lc_src0 lc_tgt sc_src0 sc_tgt)
      (STEP: SeqState.na_opt_step p me (SeqState.mk _ st_src0 smem_src0) (SeqState.mk _ st_src1 smem_src1))
      (NOMIX: nomix loc_na loc_at _ st_src0)
      (CONSISTENT: Local.promise_consistent lc_tgt)
      (WF_SRC: Local.wf lc_src0 mem_src0)
      (WF_TGT: Local.wf lc_tgt mem_tgt)
      (SC_SRC: Memory.closed_timemap sc_src0 mem_src0)
      (SC_TGT: Memory.closed_timemap sc_tgt mem_tgt)
      (MEM_SRC: Memory.closed mem_src0)
      (MEM_TGT: Memory.closed mem_tgt),
    exists lc_src1 mem_src1 sc_src1 lc_src2 mem_src2 sc_src2 e,
      (<<STEPS: rtc (@Thread.tau_step lang_src) (Thread.mk _ st_src0 lc_src0 sc_src0 mem_src0) (Thread.mk _ st_src0 lc_src1 sc_src1 mem_src1)>>) /\
        (<<STEP: Thread.opt_step e (Thread.mk _ st_src0 lc_src1 sc_src1 mem_src1) (Thread.mk _ st_src1 lc_src2 sc_src2 mem_src2)>>) /\
        (<<MACHINE: ThreadEvent.get_machine_event e = me>>) /\
        (<<LIFT: forall (NORMAL: ThreadEvent.get_machine_event e <> MachineEvent.failure),
          exists w1,
            (<<LIFT: sim_state_lift true w1 smem_src1 smem_tgt p D mem_src2 mem_tgt lc_src2 lc_tgt sc_src2 sc_tgt>>) /\
              (<<WORLD: world_messages_le (unchangable mem_src0 lc_src0.(Local.promises)) (unchangable mem_tgt lc_tgt.(Local.promises)) w0 w1>>)>>) /\
        (<<NOMIX: nomix loc_na loc_at _ st_src1>>)
  .
  Proof.
    i. inv STEP.
    { hexploit sim_lift_src_na_step; eauto.
      i. des. esplits; eauto. econs 2; eauto.
    }
    { esplits; eauto.
      { econs 1. }
      { ss. }
      { esplits; eauto.
        { eapply sim_state_lift_cond_mon; eauto. ss. }
        { refl. }
      }
    }
  Qed.

  Lemma sim_lift_src_na_steps:
    forall
      c lang_src st_src0 st_src1
      p smem_src0 smem_src1
      (STEPS: rtc (SeqState.na_step p MachineEvent.silent) (SeqState.mk _ st_src0 smem_src0) (SeqState.mk _ st_src1 smem_src1))
      w0 D smem_tgt mem_src0 mem_tgt lc_src0 lc_tgt sc_src0 sc_tgt
      (LIFT: sim_state_lift c w0 smem_src0 smem_tgt p D mem_src0 mem_tgt lc_src0 lc_tgt sc_src0 sc_tgt)
      (NOMIX: nomix loc_na loc_at _ st_src0)
      (CONSISTENT: Local.promise_consistent lc_tgt)
      (WF_SRC: Local.wf lc_src0 mem_src0)
      (WF_TGT: Local.wf lc_tgt mem_tgt)
      (SC_SRC: Memory.closed_timemap sc_src0 mem_src0)
      (SC_TGT: Memory.closed_timemap sc_tgt mem_tgt)
      (MEM_SRC: Memory.closed mem_src0)
      (MEM_TGT: Memory.closed mem_tgt),
    exists lc_src1 mem_src1 sc_src1,
      (<<STEPS: rtc (@Thread.tau_step lang_src) (Thread.mk _ st_src0 lc_src0 sc_src0 mem_src0) (Thread.mk _ st_src1 lc_src1 sc_src1 mem_src1)>>) /\
        (<<LIFT: exists w1,
            (<<LIFT: sim_state_lift true w1 smem_src1 smem_tgt p D mem_src1 mem_tgt lc_src1 lc_tgt sc_src1 sc_tgt>>) /\
              (<<WORLD: world_messages_le (unchangable mem_src0 lc_src0.(Local.promises)) (unchangable mem_tgt lc_tgt.(Local.promises)) w0 w1>>)>>) /\
        (<<NOMIX: nomix loc_na loc_at _ st_src1>>)
  .
  Proof.
    intros c lang_src st_src0 st_src1 p smem_src0 smem_src1 STEPS.
    remember (SeqState.mk _ st_src0 smem_src0) as th_src0.
    remember (SeqState.mk _ st_src1 smem_src1) as th_src1.
    revert c st_src0 st_src1 smem_src0 smem_src1 Heqth_src0 Heqth_src1.
    induction STEPS; i; clarify.
    { esplits.
      { refl. }
      { eapply sim_state_lift_cond_mon; eauto. ss. }
      { refl. }
      { auto. }
    }
    destruct y. hexploit sim_lift_src_na_step; eauto. i. des.
    hexploit Thread.rtc_tau_step_future; eauto. i. des; ss.
    hexploit Thread.step_future; eauto. i. des; ss.
    hexploit LIFT0; eauto.
    { rewrite MACHINE. ss. }
    i. des. hexploit IHSTEPS; eauto. i. des. esplits.
    { etrans; [eauto|]. econs.
      { econs; eauto. econs; eauto. }
      { eauto. }
    }
    { eauto. }
    { etrans; eauto. }
    { eauto. }
  Qed.

  Variant sim_val_sol_lift: forall (p: Perm.t) (P: bool) (sv: Const.t) (v: Const.t), Prop :=
    | sim_val_sol_lift_high
        sv v
        (VAL: Const.le sv v)
      :
      sim_val_sol_lift Perm.high true sv v
    | sim_val_sol_lift_low
        sv v
      :
      sim_val_sol_lift Perm.low false sv v
  .

  Definition sim_vals_sol_lift (p: Perms.t) (P: Loc.t -> bool) (svs: ValueMap.t) (vs: Loc.t -> Const.t) :=
    forall loc (NA: loc_na loc), sim_val_sol_lift (p loc) (P loc) (svs loc) (vs loc).

  Variant sim_flag_sol_lift (D: Flag.t) (d: bool) (W: Flag.t) (flag: Flag.t): Prop :=
    | sim_flag_sol_lift_intro
        (DEBT: d -> D)
        (WRITTEN: Flag.join W flag -> ~ d)
  .

  Definition sim_flags_sol_lift (D: Flags.t) (d: Loc.t -> bool) (W: Flags.t) (flag: Flags.t): Prop :=
    forall loc, sim_flag_sol_lift (D loc) (d loc) (W loc) (flag loc).

  Variant sim_state_sol_lift (c: bool):
    forall (smem: SeqMemory.t) (p: Perms.t) (D: Flags.t) (W: Flags.t)
           (mem: Memory.t) (lc: Local.t) (sc: TimeMap.t) (o: Oracle.t), Prop :=
    | sim_state_sol_lift_intro
        svs flag
        p P W d D vs ovs
        mem lc sc
        (SIM: sim_thread_sol c vs P d mem lc)
        (VAL: sim_vals_sol_lift p P svs vs)
        (FLAG: sim_flags_sol_lift D d W flag)
        (OVALS: forall loc (NA: loc_at loc), Const.le (ovs loc) (vs loc))
      :
      sim_state_sol_lift
        c
        (SeqMemory.mk svs flag)
        p D W
        mem lc sc (CertOracle.to_oracle ovs)
  .

  Lemma sim_lift_sim_lift_sol c:
    forall
      c1 w p D smem_src smem_tgt mem_src0 mem_tgt lc_src0 lc_tgt sc_src0 sc_tgt
      lang_src st_src
      (LIFT: sim_state_lift c1 w smem_src smem_tgt p D mem_src0 mem_tgt lc_src0 lc_tgt sc_src0 sc_tgt)
      (CONSISTENT: Local.promise_consistent lc_tgt)
      (WF_SRC: Local.wf lc_src0 mem_src0)
      (WF_TGT: Local.wf lc_tgt mem_tgt)
      (SC_SRC: Memory.closed_timemap sc_src0 mem_src0)
      (SC_TGT: Memory.closed_timemap sc_tgt mem_tgt)
      (MEM_SRC: Memory.closed mem_src0)
      (MEM_TGT: Memory.closed mem_tgt)
      (CERTIFIED: c = true -> lc_tgt.(Local.promises) = Memory.bot),
    exists lc_src1 mem_src1 sc_src1 o,
      (<<STEPS: rtc (@Thread.tau_step lang_src) (Thread.mk _ st_src lc_src0 sc_src0 mem_src0) (Thread.mk _ st_src lc_src1 sc_src1 mem_src1)>>) /\
        (<<LIFT: sim_state_sol_lift
                   c smem_src p (Flags.join D smem_tgt.(SeqMemory.flags)) smem_src.(SeqMemory.flags) mem_src1 lc_src1 sc_src1 o>>) /\
        (<<ORACLE: Oracle.wf o>>)
  .
  Proof.
    i. inv LIFT.
    hexploit (@sim_thread_sim_thread_sol c (fun loc => Flag.minus (flag_tgt loc) (flag_src loc))); eauto.
    { i. destruct (flag_src loc), (flag_tgt loc); ss. }
    i. des. esplits; eauto.
    econs; eauto.
    { ii. hexploit (VALS loc); eauto. i. inv H.
      { econs; eauto. }
      { hexploit VALS0; eauto. i. rewrite H. econs; eauto. }
    }
    { ii. ss. hexploit (FLAGS loc); eauto. i. inv H. econs.
      { unfold Flags.minus, Flags.join.
        destruct (D loc), (sflag_tgt loc), (sflag_src loc), (flag_tgt loc), (flag_src loc); auto.
      }
      { unfold Flags.minus, Flags.join. ii.
        destruct (D loc), (sflag_tgt loc), (sflag_src loc), (flag_tgt loc), (flag_src loc); ss.
      }
    }
    { i. refl. }
    { eapply CertOracle.to_oracle_wf. }
  Qed.

  Lemma sim_lift_sol_na_local_step c:
    forall
      p D W smem0 mem0 lc0 sc0 o
      smem1 me pe
      (LIFT: sim_state_sol_lift c smem0 p D W mem0 lc0 sc0 o)
      (STEP: SeqState.na_local_step p me pe smem0 smem1)
      (NALOCS: forall loc val (ACCESS: is_accessing pe = Some (loc, val)), loc_na loc)
      (WF_SRC: Local.wf lc0 mem0)
      (SC_SRC: Memory.closed_timemap sc0 mem0)
      (MEM_SRC: Memory.closed mem0)
      lang st,
    exists lc1 mem1 sc1 lc2 mem2 sc2 e,
      (<<STEPS: rtc (@Thread.tau_step lang) (Thread.mk _ st lc0 sc0 mem0) (Thread.mk _ st lc1 sc1 mem1)>>) /\
        (<<STEP: Local.program_step e lc1 sc1 mem1 lc2 sc2 mem2>>) /\
        (<<MACHINE: ThreadEvent.get_machine_event e = me \/ ThreadEvent.get_machine_event e = MachineEvent.failure>>) /\
        (<<EVENT: ThreadEvent.get_program_event e = pe>>) /\
        (<<LIFT: forall (NORMAL: ThreadEvent.get_machine_event e <> MachineEvent.failure),
            sim_state_sol_lift c smem1 p D W mem2 lc2 sc2 o>>).
  Proof.
    i. inv STEP.
    { esplits.
      { refl. }
      { eapply Local.step_silent. }
      { eauto. }
      { eauto. }
      { eauto. }
    }
    { inv LIFT. destruct ord; ss.
      hexploit (VAL0 loc); eauto. i. inv H.
      { rewrite <- H1 in *.
        hexploit sim_thread_sol_read_na.
        { eauto. }
        { eauto. }
        { etrans; [eapply VAL; auto|eapply VAL1]. }
        i. des. esplits.
        { refl. }
        { eapply Local.step_read; eauto. }
        { eauto. }
        { ss. }
        { i. econs; eauto. }
      }
      { rewrite <- H1 in *.
        hexploit sim_thread_sol_read_na_racy; eauto.
        { rewrite <- H2. ss. }
        i. des. esplits.
        { refl. }
        { eapply Local.step_racy_read; eauto. }
        { eauto. }
        { ss. }
        { i. econs; eauto. }
      }
    }
    { inv LIFT. destruct ord; ss.
      hexploit (VAL loc); eauto. i. inv H.
      { hexploit sim_thread_sol_write_na; eauto. i. des.
        { esplits.
          { refl. }
          { eapply Local.step_racy_write; eauto. }
          { eauto. }
          { ss. }
          { ss. }
        }
        { esplits.
          { eauto. }
          { eapply Local.step_write_na; eauto. }
          { eauto. }
          { ss. }
          { i. econs; eauto.
            { ii. unfold ValueMap.write. ss. des_ifs.
              { rewrite <- H1. econs. refl. }
              { eapply VAL; auto. }
            }
            { ii. unfold Flags.update. ss. des_ifs.
            }
            { i. ss. des_ifs.
              { exfalso. eapply LOCDISJOINT; eauto. }
              { eapply OVALS; eauto. }
            }
          }
        }
      }
      { hexploit sim_thread_sol_write_na_racy; eauto.
        { rewrite <- H2. ss. }
        i. des. esplits.
        { refl. }
        { eapply Local.step_racy_write; eauto. }
        { eauto. }
        { ss. }
        { ss. }
      }
    }
    { inv LIFT. hexploit sim_thread_sol_failure; eauto. i.
      esplits.
      { refl. }
      { eapply Local.step_failure; eauto. }
      { eauto. }
      { ss. }
      { ss. }
    }
    { inv LIFT. esplits.
      { refl. }
      { eapply Local.step_racy_update.
        instantiate (1:=ordw). instantiate (1:=ordr).
        red in ORD. des.
        { econs 1; eauto. inv SIM. auto. }
        { econs 2; eauto. inv SIM. auto. }
      }
      { auto. }
      { ss. }
      { ss. }
    }
  Qed.

  Lemma perm_meet_high_r p
    :
    Perm.meet p Perm.high = p.
  Proof.
    destruct p; ss.
  Qed.

  Lemma sim_lift_sol_at_step c:
    forall
      D W smem0 mem0 lc0 sc0
      smem1 pe i o
      lang st0 st1 p0 p1 o0 o1
      (LIFT: sim_state_sol_lift c smem0 p0 D W mem0 lc0 sc0 o0)
      (STEP: SeqThread.at_step pe i o (SeqThread.mk (SeqState.mk _ st0 smem0) p0 o0) (SeqThread.mk (SeqState.mk _ st1 smem1) p1 o1))
      (ATLOCS: forall loc val (ACCESS: is_accessing pe = Some (loc, val)), loc_at loc)
      (NUPDATE: ~ is_updating pe)
      (NACQUIRE: ~ is_acquire pe)
      (WF_SRC: Local.wf lc0 mem0)
      (SC_SRC: Memory.closed_timemap sc0 mem0)
      (MEM_SRC: Memory.closed mem0),
    exists lc1 mem1 e sc1 pf,
      (<<STEP: Thread.step pf e (Thread.mk lang st0 lc0 sc0 mem0) (Thread.mk _ st1 lc1 sc1 mem1)>>) /\
        (<<EVENT: ThreadEvent.get_program_event e = pe>>) /\
        (<<LIFT: forall (NORMAL: ThreadEvent.get_machine_event e <> MachineEvent.failure),
            sim_state_sol_lift c smem1 p1 D (Flags.join W (SeqEvent.written i)) mem1 lc1 sc1 o1>>).
  Proof.
    i. inv LIFT. inv STEP. inv MEM.
    assert (exists ovs1,
               (<<ORACLE: o1 = (CertOracle.to_oracle ovs1)>>) /\
                 (<<OSTEP: CertOracle.step e0 i0 o ovs ovs1>>)).
    { dependent destruction ORACLE. esplits; eauto. }
    clear ORACLE. des; clarify.
    red in INPUT0. des. inv ACQ.
    2:{ rewrite <- H0 in *. hexploit ACQUIRE; eauto. i. ss. }
    inv OSTEP; ss; clarify.
    { des_ifs; ss. hexploit OVALS; eauto. i.
      hexploit sim_thread_sol_read; eauto.
      i. des. esplits.
      { econs 2. econs; cycle 1.
        { eapply Local.step_read; eauto. }
        { eauto. }
      }
      { ss. }
      { i. inv REL. inv UPD.
        specialize (UPDATE loc0 v_new). des.
        hexploit UPDATE; eauto. i. inv H2.
        inv MEM. ss. econs; eauto.
        { ii. unfold Perms.update, ValueMap.write.
          destruct (LocSet.Facts.eq_dec loc0 loc), (LocSet.Facts.eq_dec loc loc0); subst; ss; auto.
          econs. auto.
        }
        { ii. unfold SeqEvent.written. rewrite <- H4. rewrite <- H3. ss.
          unfold Flags.add, Flags.join, Flags.update, Flags.bot.
          hexploit (FLAG loc); eauto. i. inv H2.
          destruct (flag loc0) eqn:EQ0, (LocSet.Facts.eq_dec loc loc0); subst; ss.
          { rewrite EQ0 in *. econs; auto. }
          { rewrite flag_join_bot_r. auto. }
          { rewrite EQ0 in *. rewrite flag_join_bot_r. auto. econs; auto. }
          { rewrite flag_join_bot_r. auto. }
        }
      }
    }
    { destruct pe; ss. des. clarify.
      inv UPD. inv MEM. ss. red in INPUT. des. ss.
      rewrite <- H2 in *. ss.
      destruct (Oracle.in_access i0) as [[[loc1 val1] flag1]|] eqn:ACCESS0; ss.
      des; subst. hexploit (UPDATE loc v_new); eauto. i. des.
      hexploit H1; eauto. i. inv H4.
      hexploit sim_thread_sol_write; eauto.
      i. des. esplits.
      { econs 2. econs; cycle 1.
        { eapply Local.step_write; eauto. }
        { eauto. }
      }
      { ss. }
      i. inv REL.
      { ss. econs; eauto.
        { unfold Perms.update, ValueMap.write. ii.
          repeat des_if; subst; ss.
          { econs. refl. }
          { eapply VAL; eauto. }
        }
        { unfold SeqEvent.written. rewrite <- H2. rewrite <- H5.
          ss. rewrite flags_join_bot_r.
          unfold Flags.add, Flags.update, Flags.join, Flags.bot. ii.
          hexploit (FLAG loc0); eauto. i. inv H4. econs; auto.
          destruct (flag loc) eqn:EQ0, (LocSet.Facts.eq_dec loc0 loc); subst.
          { subst. rewrite flag_join_bot_r. rewrite EQ0 in *. auto. }
          { rewrite flag_join_bot_r. auto. }
          { subst. rewrite flag_join_bot_r. rewrite EQ0 in *. auto. }
          { rewrite flag_join_bot_r. auto. }
        }
        { i. ss. condtac; subst; auto. }
      }
      { inv MEM. ss.
        destruct (Ordering.le Ordering.strong_relaxed ord0); ss. inv H6.
        econs; eauto.
        { unfold Perms.meet, Perms.update, ValueMap.write. ii.
          repeat condtac; subst; ss.
          { econs. refl. }
          { rewrite perm_meet_high_r. eapply VAL; eauto. }
        }
        { unfold SeqEvent.written. rewrite <- H2. rewrite <- H5. ss.
          unfold Flags.add, Flags.update, Flags.join, Flags.bot. ii.
          hexploit (FLAG loc0); eauto. i. inv H4. econs; auto.
          destruct (flag loc) eqn:EQ0, (LocSet.Facts.eq_dec loc0 loc); subst.
          { subst. rewrite flag_join_bot_r. rewrite EQ0 in *. auto. }
          { rewrite flag_join_bot_r. auto. }
          { subst. rewrite flag_join_bot_r. rewrite EQ0 in *. auto. }
          { rewrite flag_join_bot_r. auto. }
        }
        { i. ss. condtac; subst; auto. }
      }
    }
    { destruct pe; ss. }
    { hexploit sim_thread_sol_fence; eauto.
      { instantiate (1:=ordr). destruct ordr, ordw; ss. }
      { instantiate (1:=ordw). destruct ordr, ordw; ss. }
      i. des. esplits.
      { econs 2. econs; cycle 1.
        { eapply Local.step_fence; eauto. }
        { eauto. }
      }
      { ss. }
      i. inv UPD. inv REL.
      { econs; eauto. unfold SeqEvent.written.
        rewrite <- H2. rewrite <- H3. ss.
        rewrite flags_join_bot_r. auto.
      }
      { destruct (Ordering.le Ordering.strong_relaxed ordw); ss. clarify.
        inv MEM. ss. econs; eauto.
        { unfold Perms.meet. ii. rewrite perm_meet_high_r. auto. }
        { unfold SeqEvent.written. rewrite <- H2. rewrite <- H3.
          ss. rewrite flags_join_bot_l. unfold Flags.join, Flags.bot. ii.
          hexploit (FLAG loc); eauto. i. inv H1. econs; auto.
          rewrite flag_join_bot_r. auto.
        }
      }
    }
  Qed.

  Lemma sim_lift_sol_steps c
        tr
        lang st0 st1 smem0 smem1 p0 p1 o0 o1
        (STEPS: SeqThread.steps (@SeqState.na_step _) tr (SeqThread.mk (SeqState.mk _ st0 smem0) p0 o0) (SeqThread.mk (SeqState.mk _ st1 smem1) p1 o1))
    :
    forall mem0 lc0 sc0 w D W
           (LIFT: sim_state_sol_lift c smem0 p0 D W mem0 lc0 sc0 o0)
           (NOMIX: nomix loc_na loc_at _ st0)
           (TRACE: SeqThread.writing_trace tr w)
           (WF_SRC: Local.wf lc0 mem0)
           (SC_SRC: Memory.closed_timemap sc0 mem0)
           (MEM_SRC: Memory.closed mem0),
      (<<FAILURE: Thread.steps_failure (Thread.mk _ st0 lc0 sc0 mem0)>>) \/
        exists lc1 mem1 sc1,
          (<<STEPS: rtc (@Thread.tau_step lang) (Thread.mk _ st0 lc0 sc0 mem0) (Thread.mk _ st1 lc1 sc1 mem1)>>) /\
            (<<LIFT: sim_state_sol_lift c smem1 p1 D (Flags.join w W) mem1 lc1 sc1 o1>>) /\
            (<<NOMIX: nomix loc_na loc_at _ st1>>)
  .
  Proof.
    remember (SeqThread.mk (SeqState.mk _ st0 smem0) p0 o0) as th0.
    remember (SeqThread.mk (SeqState.mk _ st1 smem1) p1 o1) as th1.
    revert st0 st1 smem0 smem1 p0 p1 o0 o1 Heqth0 Heqth1. induction STEPS; i; clarify.
    { inv TRACE. right. esplits.
      { refl. }
      { rewrite flags_join_bot_l. auto. }
      { auto. }
    }
    { inv STEP. inv STEP0. hexploit sim_lift_sol_na_local_step; eauto.
      { punfold NOMIX. exploit NOMIX; eauto. i. des.
        eapply NA in ACCESS; auto. inv LOCAL; ss.
        { destruct ord; ss. }
        { destruct ord; ss. }
      }
      i. ss. des; subst.
      { assert (STEPS1: rtc (@Thread.tau_step _) (Thread.mk _ st0 lc0 sc0 mem0) (Thread.mk _ st4 lc2 sc2 mem2)).
        { etrans; [eauto|]. econs; [|refl]. econs; eauto.
          econs. econs 2; eauto. econs; eauto.
        }
        clear STEPS0 STEP.
        hexploit Thread.rtc_tau_step_future; eauto. i. des; ss.
        hexploit LIFT0.
        { rewrite MACHINE. ss. }
        i. hexploit IHSTEPS; eauto.
        { punfold NOMIX. exploit NOMIX; eauto. i. des. pclearbot. auto. }
        i. des.
        { left. eapply rtc_steps_thread_failure; eauto. }
        { right. esplits.
          { etrans; eauto. }
          { eauto. }
          { auto. }
        }
      }
      { left. splits. red. esplits; eauto. econs 2; eauto. econs; eauto. }
    }
    { destruct th1. destruct state0. inv TRACE.
      hexploit sim_lift_sol_at_step; eauto.
      { inv STEP. punfold NOMIX. exploit NOMIX; eauto. i. des.
        eapply AT in ACCESS; auto.
      }
      i. ss. des; subst.
      { destruct (ThreadEvent.get_machine_event e0) eqn:EVENT.
        { assert (STEP1: rtc (@Thread.tau_step _) (Thread.mk _ st0 lc0 sc0 mem0) (Thread.mk _ state0 lc1 sc1 mem1)).
          { econs; [|refl]. econs; eauto. econs; eauto. }
          hexploit Thread.rtc_tau_step_future; eauto. i. des; ss.
          hexploit LIFT0; ss.
          i. hexploit IHSTEPS; eauto.
          { punfold NOMIX. inv STEP. exploit NOMIX; eauto. i. des. pclearbot. auto. }
          i. des.
          { left. eapply rtc_steps_thread_failure; eauto. }
          { right. esplits.
            { etrans; eauto. }
            { replace (Flags.join (Flags.join (SeqEvent.written i) w0) W) with
                (Flags.join w0 (Flags.join W (SeqEvent.written i))); auto.
              unfold Flags.join. extensionality loc.
              destruct (w0 loc), (W loc), (SeqEvent.written i loc); auto.
            }
            { auto. }
          }
        }
        { destruct e0; ss. }
        { left. splits. red. esplits; [refl| |eauto].
          replace pf with true in STEP0; eauto.
          inv STEP0; ss. inv STEP1; ss.
        }
      }
    }
  Qed.

  Lemma sim_lift_failure_case:
    forall
      c w p D smem_src smem_tgt mem_src mem_tgt lc_src lc_tgt sc_src sc_tgt
      lang st
      (LIFT: sim_state_lift c w smem_src smem_tgt p D mem_src mem_tgt lc_src lc_tgt sc_src sc_tgt)
      (FAILURE: sim_seq_failure_case p (SeqState.mk _ st smem_src))
      (NOMIX: nomix loc_na loc_at _ st)
      (CONSISTENT: Local.promise_consistent lc_tgt)
      (WF_SRC: Local.wf lc_src mem_src)
      (WF_TGT: Local.wf lc_tgt mem_tgt)
      (SC_SRC: Memory.closed_timemap sc_src mem_src)
      (SC_TGT: Memory.closed_timemap sc_tgt mem_tgt)
      (MEM_SRC: Memory.closed mem_src)
      (MEM_TGT: Memory.closed mem_tgt),
      (<<FAILURE: Thread.steps_failure (Thread.mk lang st lc_src sc_src mem_src)>>).
  Proof.
    i. hexploit sim_lift_sim_lift_sol; eauto.
    { instantiate (1:=false). ss. }
    i. des.
    eapply rtc_steps_thread_failure; eauto.
    hexploit Thread.rtc_tau_step_future; eauto. i. des; ss.
    exploit FAILURE; eauto. i. des.
    destruct th. destruct state0.
    hexploit sim_lift_sol_steps; eauto. i. des; eauto.
    inv FAILURE0. des. inv H. inv STEP.
    hexploit Thread.rtc_tau_step_future; eauto. i. des; ss.
    hexploit sim_lift_sol_na_local_step; eauto.
    { punfold NOMIX0. exploit NOMIX0; eauto. i. des. eapply NA; eauto.
      inv LOCAL; ss.
      { destruct ord; ss. }
      { red in ORD. destruct ordr, ordw; des; ss. }
    }
    i. des.
    { eapply rtc_steps_thread_failure; eauto.
      red. esplits; eauto. econs 2. econs; eauto.
      rewrite EVENT. eauto.
    }
    { eapply rtc_steps_thread_failure; eauto.
      red. esplits; eauto. econs 2. econs; eauto.
      rewrite EVENT. eauto.
    }
  Qed.

  Lemma sim_lift_partial_case c:
    forall
      w p D smem_src smem_tgt mem_src0 mem_tgt lc_src0 lc_tgt sc_src0 sc_tgt
      lang_src lang_tgt
      (st_src0: lang_src.(Language.state)) (st_tgt: lang_tgt.(Language.state))
      (LIFT: sim_state_lift c w smem_src smem_tgt p D mem_src0 mem_tgt lc_src0 lc_tgt sc_src0 sc_tgt)
      (PARTIAL: sim_seq_partial_case p D (SeqState.mk _ st_src0 smem_src) (SeqState.mk _ st_tgt smem_tgt))
      (BOT: lc_tgt.(Local.promises) = Memory.bot)
      (NOMIX: nomix loc_na loc_at _ st_src0)
      (CONSISTENT: Local.promise_consistent lc_tgt)
      (WF_SRC: Local.wf lc_src0 mem_src0)
      (WF_TGT: Local.wf lc_tgt mem_tgt)
      (SC_SRC: Memory.closed_timemap sc_src0 mem_src0)
      (SC_TGT: Memory.closed_timemap sc_tgt mem_tgt)
      (MEM_SRC: Memory.closed mem_src0)
      (MEM_TGT: Memory.closed mem_tgt),
    exists st_src1 lc_src1 sc_src1 mem_src1,
      (<<STEPS: rtc (@Thread.tau_step lang_src)
                    (Thread.mk _ st_src0 lc_src0 sc_src0 mem_src0)
                    (Thread.mk _ st_src1 lc_src1 sc_src1 mem_src1)>>) /\
        ((<<FAILURE: Thread.steps_failure (Thread.mk _ st_src1 lc_src1 sc_src1 mem_src1)>>) \/
           (<<BOT: lc_src1.(Local.promises) = Memory.bot>>)).
  Proof.
    i. hexploit sim_lift_sim_lift_sol; eauto.
    i. des.
    hexploit Thread.rtc_tau_step_future; eauto. i. des; ss.
    exploit PARTIAL; eauto. intros x.
    destruct x as [?th [?tr [?w [STEPS0 [WRITING FINAL]]]]].
    guardH FINAL. destruct th. destruct state0. des.
    hexploit sim_lift_sol_steps; eauto. i. des; eauto.
    { esplits; eauto. } esplits.
    { etrans; eauto. }
    hexploit Thread.rtc_tau_step_future; eauto. i. des; ss.
    red in FINAL. des.
    { right. inv LIFT1. eapply sim_thread_none; eauto.
      i. hexploit (FLAG loc). i. inv H.
      specialize (FLAGS loc). unfold Flags.join in *.
      destruct (d loc); auto. exfalso. eapply WRITTEN; auto.
      ss. rewrite DEBT in FLAGS; auto.
      destruct (w0 loc), (flag loc), (SeqMemory.flags smem_src loc); ss.
    }
    { left. inv FAILURE. des. inv H. inv STEP.
      hexploit sim_lift_sol_na_local_step; eauto.
      { punfold NOMIX0. exploit NOMIX0; eauto. i. des. eapply NA; eauto.
        inv LOCAL; ss.
        { destruct ord; ss. }
        { red in ORD. destruct ordr, ordw; des; ss. }
      }
      i. des.
      { eapply rtc_steps_thread_failure; eauto.
        red. esplits; eauto. econs 2. econs; eauto.
        rewrite EVENT. eauto.
      }
      { eapply rtc_steps_thread_failure; eauto.
        red. esplits; eauto. econs 2. econs; eauto.
        rewrite EVENT. eauto.
      }
    }
  Qed.

  Lemma sim_lift_terminal_case c:
    forall
      w0 p D smem_src smem_tgt mem_src0 mem_tgt lc_src0 lc_tgt sc_src0 sc_tgt
      lang_src lang_tgt sim_terminal
      (st_src0: lang_src.(Language.state)) (st_tgt: lang_tgt.(Language.state))
      (LIFT: sim_state_lift c w0 smem_src smem_tgt p D mem_src0 mem_tgt lc_src0 lc_tgt sc_src0 sc_tgt)
      (SIM: sim_seq_terminal_case sim_terminal p D (SeqState.mk _ st_src0 smem_src) (SeqState.mk _ st_tgt smem_tgt))
      (TERMINAL: lang_tgt.(Language.is_terminal) st_tgt)
      (BOT: lc_tgt.(Local.promises) = Memory.bot)
      (NOMIX: nomix loc_na loc_at _ st_src0)
      (CONSISTENT: Local.promise_consistent lc_tgt)
      (WF_SRC: Local.wf lc_src0 mem_src0)
      (WF_TGT: Local.wf lc_tgt mem_tgt)
      (SC_SRC: Memory.closed_timemap sc_src0 mem_src0)
      (SC_TGT: Memory.closed_timemap sc_tgt mem_tgt)
      (MEM_SRC: Memory.closed mem_src0)
      (MEM_TGT: Memory.closed mem_tgt),
    exists st_src1 lc_src1 sc_src1 mem_src1,
      (<<STEPS: rtc (@Thread.tau_step _)
                    (Thread.mk _ st_src0 lc_src0 sc_src0 mem_src0)
                    (Thread.mk _ st_src1 lc_src1 sc_src1 mem_src1)>>) /\
        ((<<FAILURE: Thread.steps_failure (Thread.mk _ st_src1 lc_src1 sc_src1 mem_src1)>>) \/
           exists w1,
             (<<TERMINAL_SRC: (Language.is_terminal lang_src) st_src1>>) /\
               (<<BOT: lc_src1.(Local.promises) = Memory.bot>>) /\
               (<<SC: sim_timemap_lift w1 sc_src1 sc_tgt>>) /\
               (<<MEMORY: sim_memory_lift w1 mem_src1 mem_tgt>>) /\
               (<<WORLD: world_messages_le (unchangable mem_src1 lc_src1.(Local.promises)) (unchangable mem_tgt lc_tgt.(Local.promises)) w0 w1>>)).
  Proof.
    i. exploit SIM; eauto. i. des.
    destruct st_src1. hexploit sim_lift_src_na_steps; eauto.
    i. des. ss.
    hexploit Thread.rtc_tau_step_future; eauto. i. des; ss.
    inv LIFT1. ss. hexploit sim_thread_deflag_all; eauto.
    { instantiate (1:=fun _ => False).
      i. right. specialize (FLAGS loc). specialize (FLAG loc).
      inv FLAGS. splits.
      { i. rewrite H in *. ss. rewrite SRC in *.
        unfold Flags.join in FLAG.
        destruct (flag_tgt loc), (Flag.join (D loc) (sflag_tgt loc)); ss.
      }
      { specialize (VALUE loc). specialize (VALS loc). i.
        left. destruct (classic (loc_na loc)).
        { hexploit VALS; auto. i. inv H0; ss.
          etrans; eauto. etrans; eauto.
        }
        { eapply ATLOCS; eauto. }
      }
    }
    i. des. eapply rtc_implies in STEPS1; cycle 1.
    { instantiate (1:=@Thread.tau_step _). i. inv H.
      inv TSTEP. econs; eauto.
    }
    esplits.
    { etrans; eauto. }
    right. eexists (f1,  vers, mem_src2). esplits; eauto.
    { inv SIM1. inv LOCAL.
      eapply sim_promises_bot in PROMISES; eauto.
      i. specialize (FLAG0 loc). des; ss.
    }
    { ss. inv SIM1. eapply sim_timemap_mon_locs; eauto; ss. }
    { ss. inv SIM1. splits; auto.
      { eapply sim_memory_sim_memory_interference; eauto. }
      { eapply versions_wf_mapping_mon; eauto. }
    }
    { etrans; eauto. ss. i. splits; auto.
      { refl. }
      { eapply Thread.rtc_tau_step_future in STEPS1; eauto. des; ss.
        eapply Memory.future_future_weak; eauto.
      }
    }
  Qed.

  Lemma sim_lift_interference_future:
    forall
      w0 p0 D smem_src smem_tgt mem_src0 mem_tgt0 lc_src0 lc_tgt sc_src0 sc_tgt0
      w1 mem_src1 mem_tgt1 sc_src1 sc_tgt1
      lang_src lang_tgt sim_terminal st_src st_tgt
      (LIFT: sim_state_lift false w0 smem_src smem_tgt p0 D mem_src0 mem_tgt0 lc_src0 lc_tgt sc_src0 sc_tgt0)
      (SIM: sim_seq_interference _ _ sim_terminal p0 D (SeqState.mk lang_src st_src smem_src) (SeqState.mk lang_tgt st_tgt smem_tgt))
      (NOMIX: nomix loc_na loc_at _ st_src)
      (CONSISTENT: Local.promise_consistent lc_tgt)
      (WF_SRC0: Local.wf lc_src0 mem_src0)
      (WF_TGT0: Local.wf lc_tgt mem_tgt0)
      (SC_SRC0: Memory.closed_timemap sc_src0 mem_src0)
      (SC_TGT0: Memory.closed_timemap sc_tgt0 mem_tgt0)
      (MEM_SRC0: Memory.closed mem_src0)
      (MEM_TGT0: Memory.closed mem_tgt0)
      (CONS: Thread.consistent (Thread.mk lang_src st_src lc_src0 sc_src0 mem_src0))
      (WF_SRC1: Local.wf lc_src0 mem_src1)
      (WF_TGT1: Local.wf lc_tgt mem_tgt1)
      (SC_SRC1: Memory.closed_timemap sc_src1 mem_src1)
      (SC_TGT1: Memory.closed_timemap sc_tgt1 mem_tgt1)
      (MEM_SRC1: Memory.closed mem_src1)
      (MEM_TGT1: Memory.closed mem_tgt1)
      (MEMSRC: Memory.future_weak mem_src0 mem_src1)
      (MEMTGT: Memory.future_weak mem_tgt0 mem_tgt1)
      (CLOSEDFUTURE: closed_future_tview loc_na lc_tgt.(Local.tview) mem_tgt0 mem_tgt1)
      (SCSRC: TimeMap.le sc_src0 sc_src1)
      (SCTGT: TimeMap.le sc_tgt0 sc_tgt1)
      (WORLD: world_messages_le (Messages.of_memory lc_src0.(Local.promises)) (Messages.of_memory lc_tgt.(Local.promises)) w0 w1)
      (MEM: sim_memory_lift w1 mem_src1 mem_tgt1)
      (SC: sim_timemap_lift w1 sc_src1 sc_tgt1)
    ,
    exists lc_src2 sc_src2 mem_src2,
      (<<STEPS: rtc (@Thread.tau_step _)
                    (Thread.mk _ st_src lc_src0 sc_src1 mem_src1)
                    (Thread.mk _ st_src lc_src2 sc_src2 mem_src2)>>) /\
        ((<<FAILURE: Thread.steps_failure (Thread.mk _ st_src lc_src2 sc_src2 mem_src2)>>) \/
           (exists w2 p1,
               (<<LIFT: sim_state_lift false w2 smem_src smem_tgt p1 D mem_src2 mem_tgt1 lc_src2 lc_tgt sc_src2 sc_tgt1>>) /\
                 (<<SIM: sim_seq_interference _ _ sim_terminal p1 D (SeqState.mk lang_src st_src smem_src) (SeqState.mk lang_tgt st_tgt smem_tgt)>>) /\
                 (<<SC: sim_timemap_lift w2 sc_src2 sc_tgt1>>) /\
                 (<<MEM: sim_memory_lift w2 mem_src2 mem_tgt1>>) /\
                 (<<WORLD: world_messages_le (unchangable mem_src1 lc_src0.(Local.promises)) (unchangable mem_tgt1 lc_tgt.(Local.promises)) w1 w2>>))).
  Proof.
    i. inv LIFT. destruct w1 as [[f1 vers1] mem_src1'].
    red in WORLD. red in MEM. red in SC.
    hexploit WORLD; eauto. i. des. subst.
    hexploit INTERFERENCE; eauto. i. subst.
    hexploit SeqLiftInterference.sim_thread_future; eauto.
    { i. eapply ATLOCS; auto. }
    i. des.
    { esplits; eauto. }
    esplits; eauto. right.
    hexploit (choice (fun loc p =>
                        (<<NA: loc_na loc -> p = if (vs_src1 loc) then Perm.high else Perm.low>>) /\
                          (<<AT: ~ loc_na loc -> p = p0 loc>>))).
    { intros loc. destruct (classic (loc_na loc)).
      { esplits; [eauto|]. ss. }
      { esplits; [|eauto]. ss. }
    }
    intros [p1 PERM1].
    esplits.
    { econs; eauto.
      { instantiate (1:=p1). ii.
        specialize (PERM1 loc). des. rewrite NA0; auto.
        hexploit (VALS loc); auto. i. des_ifs.
        { inv SIM2. specialize (PERM loc).
          rewrite Heq in PERM. destruct (vs_tgt1 loc) eqn:VAL; ss.
          hexploit VALTGT; eauto. i.
          hexploit VALSRC; eauto. i. des.
          rewrite VS in H. rewrite H0 in H. inv H.
          econs.
          { etrans; eauto. }
          { auto. }
        }
        { inv SIM2. specialize (PERM loc).
          rewrite Heq in PERM. destruct (vs_tgt1 loc) eqn:VAL; ss.
          econs.
        }
      }
      { ii. ss. hexploit ATLOCS; eauto. i. des. splits; auto.
        inv SIM2. specialize (PERM loc).
        destruct (vs_src1 loc) eqn:VSRC, (vs_tgt1 loc) eqn:VTGT; ss.
        hexploit no_flag_max_value_same; eauto.
        { rewrite <- VSRC. eauto. }
        i. des. inv MAX. hexploit (MAXTGT loc); eauto. i. inv H.
        hexploit MAX; eauto. i. des. hexploit MAX0; eauto. i. des.
        eapply max_readable_inj in MAX1; eauto. des. subst. auto.
      }
      { eapply versions_wf_mapping_mon; eauto. eapply Mapping.les_strong_les; eauto. }
    }
    { eapply sim_seq_interference_mon; eauto.
      ii. specialize (PERM1 loc). des.
      destruct (classic (loc_na loc)).
      { rewrite NA; auto. des_ifs. hexploit VALSRC; eauto. i. des.
        hexploit (VALS loc); auto. i. rewrite VS in H0. inv H0. refl.
      }
      { rewrite AT; auto. refl. }
    }
    { inv SIM2. ss. }
    { inv SIM2. ss. splits; auto.
      { eapply sim_memory_sim_memory_interference; eauto. }
      { eapply versions_wf_mapping_mon; eauto. eapply Mapping.les_strong_les; eauto. }
    }
    { ss. i. splits; auto; try refl.
      { eapply Mapping.les_strong_les; eauto. }
      { hexploit Thread.rtc_tau_step_future; eauto. i. des; ss.
        eapply Memory.future_future_weak; eauto.
      }
      { eapply map_future_memory_les_strong; eauto. }
    }
  Qed.

  Lemma sim_lift_interference_promise:
    forall
      w0 p D smem_src smem_tgt mem_src0 mem_tgt0 lc_src0 lc_tgt0 sc_src0 sc_tgt0
      lang_src lang_tgt sim_terminal st_src st_tgt
      lc_tgt1 mem_tgt1 loc from_tgt to_tgt msg_tgt kind_tgt
      (LIFT: sim_state_lift false w0 smem_src smem_tgt p D mem_src0 mem_tgt0 lc_src0 lc_tgt0 sc_src0 sc_tgt0)
      (SIM: sim_seq_interference _ _ sim_terminal p D (SeqState.mk lang_src st_src smem_src) (SeqState.mk lang_tgt st_tgt smem_tgt))
      (NOMIX: nomix loc_na loc_at _ st_src)
      (CONSISTENT: Local.promise_consistent lc_tgt1)
      (WF_SRC0: Local.wf lc_src0 mem_src0)
      (WF_TGT0: Local.wf lc_tgt0 mem_tgt0)
      (SC_SRC0: Memory.closed_timemap sc_src0 mem_src0)
      (SC_TGT0: Memory.closed_timemap sc_tgt0 mem_tgt0)
      (MEM_SRC0: Memory.closed mem_src0)
      (MEM_TGT0: Memory.closed mem_tgt0)
      (PROMISE: Local.promise_step lc_tgt0 mem_tgt0 loc from_tgt to_tgt msg_tgt lc_tgt1 mem_tgt1 kind_tgt),
    exists lc_src1 sc_src1 mem_src1,
      (<<STEPS: rtc (@Thread.tau_step _)
                    (Thread.mk _ st_src lc_src0 sc_src0 mem_src0)
                    (Thread.mk _ st_src lc_src1 sc_src1 mem_src1)>>) /\
        ((<<FAILURE: Thread.steps_failure (Thread.mk _ st_src lc_src1 sc_src1 mem_src1)>>) \/
           (exists w1,
               (<<LIFT: sim_state_lift false w1 smem_src smem_tgt p D mem_src1 mem_tgt1 lc_src1 lc_tgt1 sc_src1 sc_tgt0>>) /\
                 (<<SC: sim_timemap_lift w1 sc_src1 sc_tgt0>>) /\
                 (<<MEM: sim_memory_lift w1 mem_src1 mem_tgt1>>) /\
                 (<<WORLD: world_messages_le (unchangable mem_src0 lc_src0.(Local.promises)) (unchangable mem_tgt0 lc_tgt0.(Local.promises)) w0 w1>>))).
  Proof.
    i. inv LIFT.
    hexploit INTERFERENCE; eauto. i. subst.
    hexploit sim_thread_promise_step; eauto.
    i. des. esplits.
    { econs 2; [|refl]. econs.
      { econs. econs 1. econs; eauto. }
      { ss. }
    }
    right. esplits.
    { econs; eauto. }
    { inv SIM1. ss. }
    { inv SIM1. ss. splits; auto. eapply sim_memory_sim_memory_interference; eauto. }
    { ss. i. splits; auto.
      { eapply Mapping.les_strong_les; eauto. }
      { hexploit Local.promise_step_future; eauto. i. des; ss.
        eapply Memory.future_future_weak; eauto.
      }
      { eapply map_future_memory_les_strong; eauto. }
    }
  Qed.

  Lemma sim_lift_interference_cap:
    forall
      w0 p D smem_src smem_tgt mem_src0 mem_tgt0 lc_src0 lc_tgt0 sc_src0 sc_tgt0
      lang_src lang_tgt sim_terminal st_src st_tgt
      cap_src cap_tgt
      (LIFT: sim_state_lift false w0 smem_src smem_tgt p D mem_src0 mem_tgt0 lc_src0 lc_tgt0 sc_src0 sc_tgt0)
      (SIM: sim_seq_interference _ _ sim_terminal p D (SeqState.mk lang_src st_src smem_src) (SeqState.mk lang_tgt st_tgt smem_tgt))
      (NOMIX: nomix loc_na loc_at _ st_src)
      (CONSISTENT: Local.promise_consistent lc_tgt0)
      (WF_SRC0: Local.wf lc_src0 mem_src0)
      (WF_TGT0: Local.wf lc_tgt0 mem_tgt0)
      (SC_SRC0: Memory.closed_timemap sc_src0 mem_src0)
      (SC_TGT0: Memory.closed_timemap sc_tgt0 mem_tgt0)
      (MEM_SRC0: Memory.closed mem_src0)
      (MEM_TGT0: Memory.closed mem_tgt0)
      (CAPSRC: Memory.cap mem_src0 cap_src)
      (CAPTGT: Memory.cap mem_tgt0 cap_tgt),
      (exists w1,
          (<<LIFT: sim_state_lift false w1 smem_src smem_tgt p D cap_src cap_tgt lc_src0 lc_tgt0 sc_src0 sc_tgt0>>) /\
            (<<SC: sim_timemap_lift w1 sc_src0 sc_tgt0>>) /\
            (<<MEM: sim_memory_lift w1 cap_src cap_tgt>>)).
  Proof.
    i. inv LIFT.
    hexploit INTERFERENCE; eauto. i. subst.
    hexploit sim_thread_cap; eauto.
    i. des. esplits.
    { econs; eauto. }
    { inv SIM1. ss. }
    { inv SIM1. ss. splits; auto. eapply sim_memory_sim_memory_interference; eauto. }
  Qed.

  Lemma wf_oracle_output_exists e
    :
    exists o, (<<WFOUT: Oracle.wf_output e o>>).
  Proof.
    exists (Oracle.mk_output
              (if is_accessing e then (Some Perm.high) else None)
              (if is_acquire e then (Some (perms_top, fun _ => Const.undef)) else None)
              (if is_release e then (Some perms_top) else None)).
    splits. red. ss. des_ifs.
  Qed.

  Lemma flag_join_false_r f0
    :
      Flag.join f0 false = f0.
  Proof.
    destruct f0; ss.
  Qed.

  Lemma sim_seq_atomic_step lang_src lang_tgt sim_terminal
        p0 d0 st_src0 st_tgt0
        (SIM: sim_seq_at_step_case (@sim_seq lang_src lang_tgt sim_terminal) p0 d0 st_src0 st_tgt0)
    :
    forall st_tgt1 e_tgt
           (STEP_TGT: lang_tgt.(Language.step) e_tgt st_tgt0.(SeqState.state) st_tgt1)
           (ATOMIC: is_atomic_event e_tgt),
    exists st_src1 st_src2 e_src,
      (<<STEPS: rtc (SeqState.na_step p0 MachineEvent.silent) st_src0 st_src1>>) /\
        (<<STEP: lang_src.(Language.step) e_src st_src1.(SeqState.state) st_src2>>) /\
        (<<EVENT: ProgramEvent.le e_tgt e_src>>) /\
        (<<ACQ: forall (ACQUIRE: is_acquire e_tgt),
            Flags.le (Flags.join st_tgt0.(SeqState.memory).(SeqMemory.flags) d0) (st_src1.(SeqState.memory).(SeqMemory.flags))>>) /\
        (<<SIM: forall i_tgt o p1 mem_tgt
                       (INPUT: SeqEvent.wf_input e_tgt i_tgt)
                       (OUTPUT: Oracle.wf_output e_tgt o)
                       (STEP_TGT: SeqEvent.step i_tgt o p0 st_tgt0.(SeqState.memory) p1 mem_tgt),
          exists i_src mem_src d1,
            (<<STEP_SRC: SeqEvent.step i_src o p0 st_src1.(SeqState.memory) p1 mem_src>>) /\
              (<<MATCH: SeqEvent.input_match d0 d1 i_src i_tgt>>) /\
              (<<INPUT: SeqEvent.wf_input e_src i_src>>) /\
              (<<SIM: sim_seq_cond
                        (negb (is_release e_tgt))
                        _ _ sim_terminal
                        p1 d1
                        (SeqState.mk _ st_src2 mem_src)
                        (SeqState.mk _ st_tgt1 mem_tgt)>>)>>).
  Proof.
    i. exploit SIM; eauto. i. des. esplits; eauto.
    { i. hexploit wf_oracle_output_exists. i. des.
      hexploit event_step_exists; eauto. i. des.
      hexploit SIM0; eauto. i. des.
      red in WF. des. inv MATCH. inv STEP0; ss. inv ACQUIRE2.
      { hexploit ACQUIRE1; eauto. rewrite <- H3. ss. }
      inv STEP_SRC. rewrite <- H2 in *. rewrite <- H3 in *.
      inv ACQ. inv ACQ0. inv MEM. inv MEM0. ss.
      inv ACCESS.
      { inv UPD.
        2:{ rewrite <- H1 in *. ss. }
        inv UPD0.
        2:{ rewrite <- H8 in *. ss. }
        etrans; eauto. eapply Flags.join_mon_r; auto.
      }
      { inv UPD.
        { rewrite <- H1 in *. ss. }
        inv UPD0.
        { rewrite <- H8 in *. ss. }
        inv MEM. inv MEM0. ss.
        rewrite <- H7 in H1. rewrite <- H6 in H8. inv H8. inv H1.
        move FLAG0 at bottom. move FLAG at bottom.
        ii. specialize (FLAG loc). clear - FLAG0 FLAG DEFERRED.
        unfold Flags.update, Flags.join in FLAG. unfold Flags.join. des_ifs.
        etrans; eauto. eapply Flag.join_mon_r; auto.
      }
    }
    i. hexploit SIM0; eauto. i. des.
    hexploit min_input_match_exists; eauto. i. des. inv MIN.
    destruct (is_release e_tgt) eqn:RELEASE; ss; eauto.
    inv STEP_TGT0. inv REL.
    { red in OUTPUT. des. hexploit RELEASE1; eauto.
      i. rewrite <- H in *. ss.
    }
    esplits; eauto. ii.
    hexploit (SIM0 i_tgt (Oracle.mk_output o.(Oracle.out_access) o.(Oracle.out_acquire) (Some p1))); eauto.
    { red in OUTPUT. des. red. splits; auto. }
    { econs.
      { eauto. }
      { eauto. }
      { ss. rewrite <- H0. econs 2; eauto. }
    }
    i. des. inv STEP_SRC0. inv STEP_SRC. ss.
    hexploit SeqEvent.step_update_inj.
    { eapply UPD0. }
    { eapply UPD1. }
    { i. red in INPUT1. red in INPUT0. des; ss.
      hexploit UPDATE0; eauto. i. des.
      hexploit UPDATE; eauto. i. des.
      hexploit H3.
      { esplits. eapply IN1. }
      i.
      hexploit H1.
      { esplits. eapply IN2. }
      i. clarify.
    }
    { auto. }
    i. des; clarify.
    hexploit SeqEvent.step_acquire_inj.
    { eapply ACQ0. }
    { eapply ACQ1. }
    { auto. }
    i. des; clarify. inv REL0.
    { rewrite <- H in H5. ss. }
    inv REL. inv MEM0. inv MEM1.
    assert (PERMEQ: Perms.meet p4 p1 = p1).
    { clear - PERM. eapply perms_antisym.
      { eapply Perms.meet_le_r. }
      { eapply Perms.meet_spec.
        { etrans; eauto. eapply Perms.meet_le_l. }
        { reflexivity . }
      }
    }
    rewrite PERMEQ in SIM2. ginit.
    guclo deferred_le_sf_ctx_spec. econs.
    2:{ gfinal. right. eapply SIM2. }
    ss. rewrite flags_join_bot_r.
    eapply MIN0; eauto.
    destruct i_src, i_src0; ss. clarify.
  Qed.

  Definition lift_out_access (e: ProgramEvent.t): option Perm.t :=
    (if (is_accessing e) then Some Perm.low else None).

  Definition lift_out_acquire (e: ProgramEvent.t) (vs: Loc.t -> option Const.t):
    option (Perms.t * ValueMap.t) :=
    if (is_acquire e)
    then
      Some ((fun loc => if vs loc then Perm.high else Perm.low),
            (fun loc => match vs loc with | Some v => v | _ => Const.undef end))
    else
      None.

  Definition lift_out_release (e: ProgramEvent.t): option (Perms.t) :=
    if (is_release e) then Some (fun _ => Perm.high) else None.

  Definition lift_output (e: ProgramEvent.t) (vs: Loc.t -> option Const.t): Oracle.output :=
    Oracle.mk_output (lift_out_access e) (lift_out_acquire e vs) (lift_out_release e).

  Lemma lift_out_access_wf e:
    lift_out_access e <-> is_accessing e.
  Proof.
    ss. unfold lift_out_access. des_ifs.
  Qed.

  Lemma lift_out_acquire_wf e vs:
    lift_out_acquire e vs <-> is_acquire e.
  Proof.
    ss. unfold lift_out_acquire. des_ifs.
  Qed.

  Lemma lift_out_release_wf e:
    lift_out_release e <-> is_release e.
  Proof.
    ss. unfold lift_out_release. des_ifs.
  Qed.

  Lemma lift_output_wf e vs
    :
      Oracle.wf_output e (lift_output e vs).
  Proof.
    red. splits.
    { eapply lift_out_access_wf. }
    { eapply lift_out_acquire_wf. }
    { eapply lift_out_release_wf. }
  Qed.

  Definition seqevent_wf_in_access
             (e: ProgramEvent.t) (i: option (Loc.t * Const.t * Flag.t * Const.t)): Prop :=
    forall loc v_new,
      (exists v_old f_old,
          i = Some (loc, v_old, f_old, v_new)) <->
      is_accessing e = Some (loc, v_new).

  Definition seqevent_wf_in_acquire
             (e: ProgramEvent.t) (i: option Flags.t): Prop :=
    i <-> is_acquire e.

  Definition seqevent_wf_in_release
             (e: ProgramEvent.t) (i: option (ValueMap.t * Flags.t)): Prop :=
    i <-> is_release e.

  Lemma seqevent_wf_cons e i
        (ACCESS: seqevent_wf_in_access e i.(SeqEvent.in_access))
        (ACQUIRE: seqevent_wf_in_acquire e i.(SeqEvent.in_acquire))
        (RELEASE: seqevent_wf_in_release e i.(SeqEvent.in_release))
    :
      SeqEvent.wf_input e i.
  Proof.
    red. splits; auto.
  Qed.

  Lemma seqevent_wf_destruct e i
        (WF: SeqEvent.wf_input e i)
    :
      (<<ACCESS: seqevent_wf_in_access e i.(SeqEvent.in_access)>>) /\
      (<<ACQUIRE: seqevent_wf_in_acquire e i.(SeqEvent.in_acquire)>>) /\
      (<<RELEASE: seqevent_wf_in_release e i.(SeqEvent.in_release)>>).
  Proof.
    auto.
  Qed.

  Lemma sim_lift_event_step_access:
    forall
      vs_src0 vs_tgt0 vs_src1 vs_tgt1
      flag_src0 flag_tgt0
      e_tgt e_src
      p0 svs_src0 svs_tgt0 D0 sflag_src0 sflag_tgt0
      (EVENT: ProgramEvent.le e_tgt e_src)
      (VALS: sim_vals_lift p0 svs_src0 svs_tgt0 vs_src0 vs_tgt0)
      (FLAGS: sim_flags_lift D0 sflag_src0 sflag_tgt0 flag_src0 flag_tgt0)
      (ATLOCS: forall loc (NNA: ~ loc_na loc),
          (<<FLAGSRC: flag_src0 loc = false>>) /\
            (<<FLAGTGT: flag_tgt0 loc = false>>) /\
            (<<VAL: option_rel Const.le (vs_tgt0 loc) (vs_src0 loc)>>))
      (AT: forall loc val (ACC: is_accessing e_tgt = Some (loc, val)), loc_at loc)
      (VAL: forall loc (NA: loc_na loc),
          (<<SRC: vs_src1 loc = vs_src0 loc>>) /\ (<<TGT: vs_tgt1 loc = vs_tgt0 loc>>)),
    forall i_src svs_src1 sflag_src1 D1 i_tgt svs_tgt1 sflag_tgt1 p1 p'
           (INPUT_SRC: seqevent_wf_in_access e_src i_src)
           (INPUT_TGT: seqevent_wf_in_access e_tgt i_tgt)
           (MATCH: SeqEvent.in_access_match D0 D1 i_src i_tgt)
           (STEP_SRC: SeqEvent.step_update
                        i_src (lift_out_access e_tgt)
                        p0 (SeqMemory.mk svs_src0 sflag_src0)
                        p1 (SeqMemory.mk svs_src1 sflag_src1))
           (STEP_TGT: SeqEvent.step_update
                        i_tgt (lift_out_access e_tgt)
                        p0 (SeqMemory.mk svs_tgt0 sflag_tgt0)
                        p' (SeqMemory.mk svs_tgt1 sflag_tgt1)),
      (<<PERMEQ: p' = p1>>) /\
      (<<VALS: sim_vals_lift p1 svs_src1 svs_tgt1 vs_src1 vs_tgt1>>) /\
        (<<FLAGS: sim_flags_lift D1 sflag_src1 sflag_tgt1 flag_src0 flag_tgt0>>).
  Proof.
    i. inv MATCH.
    { inv STEP_TGT. inv STEP_SRC. splits; auto.
      { ii. hexploit (VAL loc); auto. i. des.
        rewrite SRC. rewrite TGT. auto.
      }
      { ii. specialize (FLAGS loc). inv FLAGS. econs; auto.
        etrans; eauto. eapply Flag.join_mon_r. eapply Flag.join_mon_l. auto.
      }
    }
    { inv STEP_TGT. inv STEP_SRC. inv MEM. inv MEM0. ss.
      exploit INPUT_TGT. intros x. des. exploit x; eauto. i. rewrite x2 in *.
      splits.
      { rewrite <- H in H5. inv H5. auto. }
      { ii. unfold ValueMap.write, Perms.update. condtac; subst.
        { exfalso. eapply LOCDISJOINT; eauto. }
        condtac; subst; ss.
        hexploit (VAL loc); auto. i. des.
        rewrite SRC. rewrite TGT. auto.
      }
      { ii. unfold Flags.update. specialize (FLAGS loc). inv FLAGS. condtac; subst.
        { econs.
          { rewrite SRC in FLAG. rewrite flag_join_false_r.
            etrans; eauto. etrans; [|eapply Flag.join_ge_l].
            eapply Flag.join_spec; [refl|]. rewrite flag_join_comm. auto.
          }
          { hexploit ATLOCS; eauto. i. des. rewrite FLAGSRC. ss. }
        }
        { econs; auto. etrans; eauto.
          eapply Flag.join_mon_r. eapply Flag.join_mon_l. eapply DEFERRED; auto.
        }
      }
    }
  Qed.

  Lemma sim_lift_event_step_acquire:
    forall
      vs_src0 vs_tgt0 vs_src1 vs_tgt1
      e_tgt e_src
      p0 svs_src0 svs_tgt0
      D0 sflag_src0 sflag_tgt0 flag_src0 flag_tgt0
      (EVENT: ProgramEvent.le e_tgt e_src)
      (VALS: sim_vals_lift p0 svs_src0 svs_tgt0 vs_src0 vs_tgt0)
      (FLAGS: sim_flags_lift D0 sflag_src0 sflag_tgt0 flag_src0 flag_tgt0)
      (ATLOCS: forall loc (NNA: ~ loc_na loc),
          (<<FLAGSRC: flag_src0 loc = false>>) /\
          (<<FLAGTGT: flag_tgt0 loc = false>>) /\
          (<<VAL: option_rel Const.le (vs_tgt0 loc) (vs_src0 loc)>>))
      (VAL: forall loc (NA: loc_na loc),
          ((<<SRC: vs_src1 loc = vs_src0 loc>>) /\ (<<TGT: vs_tgt1 loc = vs_tgt0 loc>>)) \/
          (exists val_src val_tgt,
              (<<NONESRC: vs_src0 loc = None>>) /\ (<<NONETGT: vs_tgt0 loc = None>>) /\
              (<<VALSRC: vs_src1 loc = Some val_src>>) /\ (<<VALTGT: vs_tgt1 loc = Some val_tgt>>) /\
              (<<VALLE: Const.le val_tgt val_src>>) /\
              (<<ACQ: is_acquire e_tgt>>)))
      (ACQFLAG: forall loc
                       (SRC: flag_src0 loc = false) (TGT: flag_tgt0 loc = true),
          ~ is_acquire e_tgt),
    forall i_src svs_src1 sflag_src1 D1
           i_tgt svs_tgt1 sflag_tgt1 p1 p'
           (INPUT_SRC: seqevent_wf_in_acquire e_src i_src)
           (INPUT_TGT: seqevent_wf_in_acquire e_tgt i_tgt)
           (MATCH: SeqEvent.in_acquire_match D0 D1 i_src i_tgt)
           (STEP_SRC: SeqEvent.step_acquire
                        i_src (lift_out_acquire e_tgt vs_src1)
                        p0 (SeqMemory.mk svs_src0 sflag_src0)
                        p1 (SeqMemory.mk svs_src1 sflag_src1))
           (STEP_TGT: SeqEvent.step_acquire
                        i_tgt (lift_out_acquire e_tgt vs_src1)
                        p0 (SeqMemory.mk svs_tgt0 sflag_tgt0)
                        p' (SeqMemory.mk svs_tgt1 sflag_tgt1)),
      (<<PERMEQ: p' = p1>>) /\
      (<<VALS: sim_vals_lift p1 svs_src1 svs_tgt1 vs_src1 vs_tgt1>>) /\
        (<<FLAGS: sim_flags_lift D1 sflag_src1 sflag_tgt1 flag_src0 flag_tgt0>>).
  Proof.
    i. inv MATCH.
    { inv STEP_TGT. inv STEP_SRC.
      splits; auto.
      { ii. hexploit (VAL loc); auto. i. des.
        { rewrite SRC. rewrite TGT. auto. }
        { red in INPUT_TGT. rewrite ACQ in INPUT_TGT. des. hexploit INPUT_TGT0; ss.
        }
      }
      { ii. specialize (FLAGS loc). inv FLAGS. econs; auto.
        etrans; eauto. eapply Flag.join_mon_r. eapply Flag.join_mon_l. auto.
      }
    }
    { inv STEP_TGT. inv STEP_SRC. inv MEM. inv MEM0.
      unfold lift_out_acquire in *. des_ifs. ss. splits.
      { auto. }
      { ii. hexploit (VALS loc); eauto. i.
        unfold lift_out_acquire in *. des_ifs.
        unfold ValueMap.acquire, Perms.acquired, Perms.join.
        hexploit VAL; eauto. i. des.
        { rewrite SRC. rewrite TGT. inv H; ss.
          { econs. }
          { econs; eauto. }
        }
        { rewrite VALSRC. rewrite VALTGT.
          rewrite NONESRC in *. rewrite NONETGT in *. inv H; ss.
          econs; eauto. refl.
        }
      }
      { ii. hexploit (FLAGS loc); eauto. i.
        specialize (FLAGS loc). inv FLAGS. econs; auto.
        etrans; [|eapply Flag.join_ge_l].
        destruct (flag_tgt0 loc) eqn:FLAGSRC, (flag_src0 loc) eqn:FLATGT; ss.
        hexploit ACQFLAG; eauto. ss.
      }
    }
  Qed.

  Lemma sim_lift_event_step_release_normal:
    forall
      e_tgt e_src
      p0 svs_src0 svs_tgt0 vs_src0 vs_tgt0
      D0 sflag_src0 sflag_tgt0 flag_src0 flag_tgt0
      (EVENT: ProgramEvent.le e_tgt e_src)
      (VALS: sim_vals_lift p0 svs_src0 svs_tgt0 vs_src0 vs_tgt0)
      (FLAGS: sim_flags_lift D0 sflag_src0 sflag_tgt0 flag_src0 flag_tgt0)
      (NORMAL: ~ is_release e_tgt),
    forall i_src svs_src1 sflag_src1 D1 i_tgt svs_tgt1 sflag_tgt1 p1 p'
           (INPUT_SRC: seqevent_wf_in_release e_src i_src)
           (INPUT_TGT: seqevent_wf_in_release e_tgt i_tgt)
           (MATCH: SeqEvent.in_release_match D0 D1 i_src i_tgt)
           (STEP_SRC: SeqEvent.step_release
                        i_src (lift_out_release e_tgt)
                        p0 (SeqMemory.mk svs_src0 sflag_src0)
                        p1 (SeqMemory.mk svs_src1 sflag_src1))
           (STEP_TGT: SeqEvent.step_release
                        i_tgt (lift_out_release e_tgt)
                        p0 (SeqMemory.mk svs_tgt0 sflag_tgt0)
                        p' (SeqMemory.mk svs_tgt1 sflag_tgt1)),
      (<<PERMEQ: p' = p1>>) /\
      (<<VALS: sim_vals_lift p1 svs_src1 svs_tgt1 vs_src0 vs_tgt0>>) /\
        (<<FLAGS: sim_flags_lift D1 sflag_src1 sflag_tgt1 flag_src0 flag_tgt0>>).
  Proof.
    i. inv MATCH.
    { inv STEP_TGT. inv STEP_SRC.
      splits; auto.
      { ii. specialize (FLAGS loc). inv FLAGS. econs; auto.
        etrans; eauto. eapply Flag.join_mon_r. eapply Flag.join_mon_l. auto.
      }
    }
    { exfalso. eapply NORMAL. eapply INPUT_TGT. ss. }
  Qed.

  Lemma sim_lift_event_step_release_release:
    forall
      e_tgt e_src
      p0 svs_src0 svs_tgt0 vs_src0 vs_tgt0
      D0 sflag_src0 sflag_tgt0 flag_src0 flag_tgt0 flag_tgt1
      (EVENT: ProgramEvent.le e_tgt e_src)
      (VALS: sim_vals_lift p0 svs_src0 svs_tgt0 vs_src0 vs_tgt0)
      (FLAGS: sim_flags_lift D0 sflag_src0 sflag_tgt0 flag_src0 flag_tgt0)
      (NORMAL: is_release e_tgt)
      (ATLOCS: forall loc (NNA: ~ loc_na loc),
          (<<FLAGSRC: flag_src0 loc = false>>) /\
          (<<FLAGTGT: flag_tgt0 loc = false>>) /\
          (<<VAL: option_rel Const.le (vs_tgt0 loc) (vs_src0 loc)>>))
      (DEBT: forall loc
                    (FLAG: flag_src0 loc = false -> flag_tgt0 loc = false)
                    (VAL: option_rel Const.le (vs_tgt0 loc) (vs_src0 loc)),
          flag_tgt1 loc = false),
    forall i_src svs_src1 sflag_src1 D1 i_tgt svs_tgt1 sflag_tgt1 p1 p'
           (INPUT_SRC: seqevent_wf_in_release e_src i_src)
           (INPUT_TGT: seqevent_wf_in_release e_tgt i_tgt)
           (MATCH: SeqEvent.in_release_match D0 D1 i_src i_tgt)
           (STEP_SRC: SeqEvent.step_release
                        i_src (lift_out_release e_tgt)
                        p0 (SeqMemory.mk svs_src0 sflag_src0)
                        p1 (SeqMemory.mk svs_src1 sflag_src1))
           (STEP_TGT: SeqEvent.step_release
                        i_tgt (lift_out_release e_tgt)
                        p0 (SeqMemory.mk svs_tgt0 sflag_tgt0)
                        p' (SeqMemory.mk svs_tgt1 sflag_tgt1)),
      (<<PERMEQ: p' = p1>>) /\
      (<<VALS: sim_vals_lift p1 svs_src1 svs_tgt1 vs_src0 vs_tgt0>>) /\
      (<<FLAGS: sim_flags_lift D1 sflag_src1 sflag_tgt1 (fun _ => false) flag_tgt1>>).
  Proof.
    i. inv MATCH.
    { exfalso. red in INPUT_TGT. rewrite NORMAL in INPUT_TGT.
      des. hexploit INPUT_TGT0; ss.
    }
    inv STEP_TGT. inv STEP_SRC. inv MEM. inv MEM0. ss.
    unfold lift_out_release in *. rewrite NORMAL in *. clarify. splits; auto.
    { ii. unfold Perms.meet. rewrite perm_meet_high_r. auto. }
    { ii. specialize (FLAGS loc). inv FLAGS.
      econs; ss. unfold Flags.bot. rewrite flag_join_false_r.
      specialize (DEBT loc). specialize (VAL loc).
      specialize (DEFERRED loc). unfold Flags.join in DEFERRED.
      destruct (flag_tgt1 loc), (D1 loc); ss. hexploit DEBT; ss.
      { i. rewrite H in *. ss. rewrite flag_join_false_r in *.
        rewrite SRC in *. rewrite flag_join_comm in TGT.
        destruct (flag_tgt0 loc); ss. rewrite TGT in *. ss.
      }
      { destruct (classic (loc_na loc)).
        { hexploit (VALS loc); eauto. i. inv H0; ss. etrans; eauto. etrans; eauto. }
        { hexploit ATLOCS; eauto. i. des. auto. }
      }
    }
  Qed.

  Lemma sim_lift_event_step_normal:
    forall
      e_tgt e_src
      p0 svs_src0 svs_tgt0 vs_src0 vs_tgt0
      D0 sflag_src0 sflag_tgt0 flag_src0 flag_tgt0
      vs_src1 vs_tgt1
      (EVENT: ProgramEvent.le e_tgt e_src)
      (VALS: sim_vals_lift p0 svs_src0 svs_tgt0 vs_src0 vs_tgt0)
      (FLAGS: sim_flags_lift D0 sflag_src0 sflag_tgt0 flag_src0 flag_tgt0)
      (ATLOCS: forall loc (NNA: ~ loc_na loc),
          (<<FLAGSRC: flag_src0 loc = false>>) /\
            (<<FLAGTGT: flag_tgt0 loc = false>>) /\
            (<<VAL: option_rel Const.le (vs_tgt0 loc) (vs_src0 loc)>>))
      (NORMAL: ~ is_release e_tgt)
      (AT: forall loc val (ACC: is_accessing e_tgt = Some (loc, val)), loc_at loc)
      (VAL: forall loc (NA: loc_na loc),
          ((<<SRC: vs_src1 loc = vs_src0 loc>>) /\ (<<TGT: vs_tgt1 loc = vs_tgt0 loc>>)) \/
            (exists val_src val_tgt,
                (<<NONESRC: vs_src0 loc = None>>) /\ (<<NONETGT: vs_tgt0 loc = None>>) /\
                  (<<VALSRC: vs_src1 loc = Some val_src>>) /\ (<<VALTGT: vs_tgt1 loc = Some val_tgt>>) /\
                  (<<VALLE: Const.le val_tgt val_src>>) /\
                  (<<ACQ: is_acquire e_tgt>>)))
      (ACQFLAG: forall loc
                       (SRC: flag_src0 loc = false) (TGT: flag_tgt0 loc = true),
          ~ is_acquire e_tgt),
    forall i_src svs_src1 sflag_src1 D1 i_tgt svs_tgt1 sflag_tgt1 p1 p'
           (INPUT_SRC: SeqEvent.wf_input e_src i_src)
           (INPUT_TGT: SeqEvent.wf_input e_tgt i_tgt)
           (MATCH: SeqEvent.input_match D0 D1 i_src i_tgt)
           (STEP_SRC: SeqEvent.step
                        i_src (lift_output e_tgt vs_src1)
                        p0 (SeqMemory.mk svs_src0 sflag_src0)
                        p1 (SeqMemory.mk svs_src1 sflag_src1))
           (STEP_TGT: SeqEvent.step
                        i_tgt (lift_output e_tgt vs_src1)
                        p0 (SeqMemory.mk svs_tgt0 sflag_tgt0)
                        p' (SeqMemory.mk svs_tgt1 sflag_tgt1)),
      (<<PERMEQ: p' = p1>>) /\
      (<<VALS: sim_vals_lift p1 svs_src1 svs_tgt1 vs_src1 vs_tgt1>>) /\
        (<<FLAGS: sim_flags_lift D1 sflag_src1 sflag_tgt1 flag_src0 flag_tgt0>>).
  Proof.
    i. inv MATCH. inv STEP_SRC. inv STEP_TGT.
    eapply seqevent_wf_destruct in INPUT_SRC.
    eapply seqevent_wf_destruct in INPUT_TGT. des.
    destruct m1, m2, m3, m4. ss.
    hexploit sim_lift_event_step_access; eauto. i. des; subst.
    hexploit sim_lift_event_step_acquire; eauto. i. des; subst.
    hexploit sim_lift_event_step_release_normal; eauto.
  Qed.

  Lemma sim_lift_event_step_release:
    forall
      e_tgt e_src
      p0 svs_src0 svs_tgt0 vs_src0 vs_tgt0
      D0 sflag_src0 sflag_tgt0 flag_src0 flag_tgt0 flag_tgt1
      vs_src1 vs_tgt1 i_src svs_src1 sflag_src1 D1 i_tgt svs_tgt1 sflag_tgt1 p1 p'
      (STEP_SRC: SeqEvent.step
                   i_src (lift_output e_tgt vs_src1)
                   p0 (SeqMemory.mk svs_src0 sflag_src0)
                   p1 (SeqMemory.mk svs_src1 sflag_src1))
      (STEP_TGT: SeqEvent.step
                   i_tgt (lift_output e_tgt vs_src1)
                   p0 (SeqMemory.mk svs_tgt0 sflag_tgt0)
                   p' (SeqMemory.mk svs_tgt1 sflag_tgt1))
      (EVENT: ProgramEvent.le e_tgt e_src)
      (VALS: sim_vals_lift p0 svs_src0 svs_tgt0 vs_src0 vs_tgt0)
      (FLAGS: sim_flags_lift D0 sflag_src0 sflag_tgt0 flag_src0 flag_tgt0)
      (ATLOCS: forall loc (NNA: ~ loc_na loc),
          (<<FLAGSRC: flag_src0 loc = false>>) /\
          (<<FLAGTGT: flag_tgt0 loc = false>>) /\
          (<<VAL: option_rel Const.le (vs_tgt0 loc) (vs_src0 loc)>>))
      (RELEASE: is_release e_tgt)
      (AT: forall loc val (ACC: is_accessing e_tgt = Some (loc, val)), loc_at loc)
      (VAL: forall loc,
          ((<<SRC: vs_src1 loc = vs_src0 loc>>) /\ (<<TGT: vs_tgt1 loc = vs_tgt0 loc>>)) \/
          (exists val_src val_tgt,
              ((<<NNA: ~ loc_na loc>>) \/ ((<<NONESRC: vs_src0 loc = None>>) /\ (<<NONETGT: vs_tgt0 loc = None>>) /\ (<<ACQ: is_acquire e_tgt>>))) /\
              (<<VALSRC: vs_src1 loc = Some val_src>>) /\ (<<VALTGT: vs_tgt1 loc = Some val_tgt>>) /\
              (<<VALLE: Const.le val_tgt val_src>>)))
      (ACQFLAG: forall loc
                       (SRC: flag_src0 loc = false) (TGT: flag_tgt0 loc = true),
          ~ is_acquire e_tgt)
      (DEBT: forall loc
                    (FLAG: flag_src0 loc = false -> flag_tgt0 loc = false)
                    (VAL: option_rel Const.le (vs_tgt0 loc) (vs_src0 loc)),
          flag_tgt1 loc = false)
      (INPUT_SRC: SeqEvent.wf_input e_src i_src)
      (INPUT_TGT: SeqEvent.wf_input e_tgt i_tgt)
      (MATCH: SeqEvent.input_match D0 D1 i_src i_tgt),
      (<<PERMEQ: p' = p1>>) /\
      (<<VALS: sim_vals_lift p1 svs_src1 svs_tgt1 vs_src1 vs_tgt1>>) /\
      (<<FLAGS: sim_flags_lift D1 sflag_src1 sflag_tgt1 (fun _ => false) flag_tgt1>>).
  Proof.
    i. inv MATCH. inv STEP_SRC. inv STEP_TGT.
    eapply seqevent_wf_destruct in INPUT_SRC.
    eapply seqevent_wf_destruct in INPUT_TGT. des.
    destruct m1, m2, m3, m4. ss.
    hexploit sim_lift_event_step_access; eauto. i. des; subst.
    assert (VAL0: forall loc (NA: loc_na loc),
               ((<<SRC: vs_src1 loc = vs_src0 loc>>) /\ (<<TGT: vs_tgt1 loc = vs_tgt0 loc>>)) \/
               (exists val_src val_tgt,
                   (<<NONESRC: vs_src0 loc = None>>) /\ (<<NONETGT: vs_tgt0 loc = None>>) /\
                   (<<VALSRC: vs_src1 loc = Some val_src>>) /\ (<<VALTGT: vs_tgt1 loc = Some val_tgt>>) /\
                   (<<VALLE: Const.le val_tgt val_src>>) /\
                   (<<ACQ: is_acquire e_tgt>>))).
    { i. hexploit VAL; eauto. i. des.
      { left. splits; eauto. }
      { ss. }
      { right. esplits; eauto. }
    }
    hexploit sim_lift_event_step_acquire; eauto. i. des; subst.
    hexploit sim_lift_event_step_release_release; eauto.
    { i. hexploit ATLOCS; eauto. i. des. splits; auto.
      hexploit (VAL loc); eauto. i. des.
      { rewrite SRC. rewrite TGT. auto. }
      { rewrite VALSRC. rewrite VALTGT. auto. }
      { rewrite VALSRC. rewrite VALTGT. auto. }
    }
    { i. eapply DEBT; auto. destruct (classic (loc_na loc)).
      { hexploit VAL0; eauto. i. des.
        { rewrite SRC in VAL1. rewrite TGT in VAL1. ss. }
        { rewrite NONESRC. rewrite NONETGT. ss. }
      }
      { hexploit ATLOCS; eauto. i. des. auto. }
    }
  Qed.

  Lemma sim_thread_local_program_step_normal
        f0 vers0 flag_src0 flag_tgt0 vs_src0 vs_tgt0
        mem_src0 mem_tgt0 lc_src0 lc_tgt0 sc_src0 sc_tgt0
        pe_tgt pe_src
        e_tgt lc_tgt1 mem_tgt1 sc_tgt1
        lang st0 st1
        (SIM: SeqLiftStep.sim_thread
                f0 vers0 flag_src0 flag_tgt0 vs_src0 vs_tgt0
                mem_src0 mem_tgt0 lc_src0 lc_tgt0 sc_src0 sc_tgt0)
        (STEP: Local.program_step e_tgt lc_tgt0 sc_tgt0 mem_tgt0 lc_tgt1 sc_tgt1 mem_tgt1)
        (EVENTTGT: ThreadEvent.get_program_event e_tgt = pe_tgt)
        (EVENTLE: ProgramEvent.le pe_tgt pe_src)
        (LANGSTEP: lang.(Language.step) pe_src st0 st1)
        (CONSISTENT: Local.promise_consistent lc_tgt1)
        (LOCALSRC: Local.wf lc_src0 mem_src0)
        (LOCALTGT: Local.wf lc_tgt0 mem_tgt0)
        (MEMSRC: Memory.closed mem_src0)
        (MEMTGT: Memory.closed mem_tgt0)
        (SCSRC: Memory.closed_timemap sc_src0 mem_src0)
        (SCTGT: Memory.closed_timemap sc_tgt0 mem_tgt0)
        (WF: Mapping.wfs f0)
        (VERS: versions_wf f0 vers0)
        (ATOMIC: is_atomic_event pe_tgt)
        (NORMAL: ~ is_release pe_tgt)
        (ATLOCS: forall loc (NNA: ~ loc_na loc),
            (<<FLAGSRC: flag_src0 loc = false>>) /\
              (<<FLAGTGT: flag_tgt0 loc = false>>) /\
              (<<VAL: option_rel Const.le (vs_tgt0 loc) (vs_src0 loc)>>))
        (AT: forall loc val (ACC: is_accessing pe_tgt = Some (loc, val)), loc_at loc)
        (ACQFLAG: forall loc
                         (SRC: flag_src0 loc = false) (TGT: flag_tgt0 loc = true),
            ~ is_acquire pe_tgt)
    :
    (<<FAILURE: Thread.steps_failure (Thread.mk lang st0 lc_src0 sc_src0 mem_src0)>>) \/
    exists lc_src1 mem_src1 sc_src1 f1 vers1 vs_src1 vs_tgt1,
      (<<STEPS: rtc (@Thread.tau_step _) (Thread.mk lang st0 lc_src0 sc_src0 mem_src0) (Thread.mk lang st1 lc_src1 sc_src1 mem_src1)>>) /\
        (<<SIM: SeqLiftStep.sim_thread
                  f1 vers1 flag_src0 flag_tgt0 vs_src1 vs_tgt1
                  mem_src1 mem_tgt1 lc_src1 lc_tgt1 sc_src1 sc_tgt1>>) /\
        (<<WF: Mapping.wfs f1>>) /\
        (<<MAPLE: Mapping.les f0 f1>>) /\
        (<<VERSLE: versions_le vers0 vers1>>) /\
        (<<VERSWF: versions_wf f1 vers1>>) /\
        (<<MAPFUTURE: map_future_memory f0 f1 mem_src1>>) /\
        (<<ATLOCS: forall loc (NNA: ~ loc_na loc), option_rel Const.le (vs_tgt1 loc) (vs_src1 loc)>>) /\
        (<<VAL: forall loc (NA: loc_na loc),
            ((<<SRC: vs_src1 loc = vs_src0 loc>>) /\ (<<TGT: vs_tgt1 loc = vs_tgt0 loc>>)) \/
              (exists val_src val_tgt,
                  (<<NONESRC: vs_src0 loc = None>>) /\ (<<NONETGT: vs_tgt0 loc = None>>) /\
                    (<<VALSRC: vs_src1 loc = Some val_src>>) /\ (<<VALTGT: vs_tgt1 loc = Some val_tgt>>) /\
                    (<<VALLE: Const.le val_tgt val_src>>) /\
                    (<<ACQ: is_acquire pe_tgt>>))>>) /\
          (<<NFAILURE: ThreadEvent.get_machine_event e_tgt = MachineEvent.silent>>) /\
        (<<SPACE: space_future_memory (unchangable mem_tgt0 lc_tgt0.(Local.promises)) f0 mem_src0 f1 mem_src1>>)
  .
  Proof.
    inv STEP; ss; clarify.
    (* read *)
    { hexploit (ATLOCS loc); eauto. i. des.
      hexploit sim_thread_read; eauto.
      i. des. right. esplits.
      { econs 2; [|refl]. econs.
        { econs. econs 2. econs; cycle 1.
          { eapply Local.step_read. eapply READ.
            instantiate (1:=val). etrans; eauto.
          }
          { ss. }
        }
        { ss. }
      }
      { eauto. }
      { eauto. }
      { refl. }
      { refl. }
      { eauto. }
      { eapply map_future_memory_refl. }
      { i. hexploit ATLOCS; eauto. i. des.
        hexploit (VALS loc0); eauto. i. des.
        { rewrite SRC. rewrite TGT. auto. }
        { rewrite VALSRC. rewrite VALTGT0. ss. }
        { rewrite VALSRC. rewrite VALTGT0. ss. }
      }
      { i. hexploit (VALS loc0); eauto. i. des.
        { left. auto. }
        { right. esplits; eauto. }
        { subst. exfalso. eapply LOCDISJOINT; eauto. }
      }
      { ss. }
      { eapply space_future_memory_refl; eauto. refl. }
    }
    (* write *)
    { hexploit (ATLOCS loc); eauto. i. des_ifs. des. subst.
      hexploit sim_thread_write_step_normal; eauto.
      i. des. right. esplits.
      { econs 2; [|refl]. econs.
        { econs. econs 2. econs; cycle 1.
          { eapply Local.step_write; eauto. }
          { ss. }
        }
        { ss. }
      }
      { eauto. }
      { eauto. }
      { eapply Mapping.les_strong_les; eauto. }
      { eauto. }
      { eauto. }
      { eapply map_future_memory_les_strong; eauto. }
      { i. hexploit ATLOCS; eauto. i. des.
        hexploit (VALS loc); eauto. i. des.
        { rewrite SRC. rewrite TGT. auto. }
        { rewrite VALSRC. rewrite VALTGT. ss. }
        { rewrite VALSRC1. rewrite VALTGT1. ss. }
      }
      { i. hexploit (VALS loc); eauto. i. des.
        { left. auto. }
        { subst. exfalso. eapply LOCDISJOINT; eauto. }
        { left. rewrite VALSRC0. rewrite VALTGT0. auto. }
      }
      { ss. }
      { auto. }
    }
    (* update *)
    { hexploit (ATLOCS loc); eauto. i. des_ifs. des. subst.
      hexploit sim_thread_update_step_normal; eauto.
      i. des. right. esplits.
      { econs 2; [|refl]. econs.
        { econs. econs 2. econs; cycle 1.
          { eapply Local.step_update.
            { eapply READ. instantiate (1:=valr0). etrans; eauto. }
            { eauto. }
          }
          { ss. }
        }
        { ss. }
      }
      { eauto. }
      { eauto. }
      { eapply Mapping.les_strong_les; eauto. }
      { eauto. }
      { eauto. }
      { eapply map_future_memory_les_strong; eauto. }
      { i. hexploit ATLOCS; eauto. i. des. destruct (Loc.eq_dec loc0 loc).
        { red in UPDATED. des; subst.
          { rewrite TGT. rewrite SRC. ss. }
          { rewrite TGTNONE1. rewrite SRCNONE1. ss. }
        }
        { hexploit VALS; eauto. i. des.
          { rewrite SRC. rewrite TGT. auto. }
          { rewrite VALSRC. rewrite VALTGT0. ss. }
        }
      }
      { i. hexploit (VALS loc); eauto.
        { ii. subst. eapply LOCDISJOINT; eauto. }
      }
      { ss. }
      { auto. }
    }
    (* fence *)
    { hexploit sim_thread_fence_step_normal; eauto.
      { ii. hexploit ACQFLAG; eauto. rewrite H. destruct ordw; ss. }
      { destruct ordw; ss. }
      i. des. right. esplits.
      { econs 2; [|refl]. econs.
        { econs. econs 2. econs; cycle 1.
          { eapply Local.step_fence; eauto. }
          { ss. }
        }
        { ss. }
      }
      { eauto. }
      { eauto. }
      { refl. }
      { refl. }
      { eauto. }
      { eapply map_future_memory_refl. }
      { i. hexploit ATLOCS; eauto. i. des.
        hexploit (VALS loc); eauto. i. des.
        { rewrite SRC. rewrite TGT. auto. }
        { rewrite VALSRC. rewrite VALTGT. ss. }
        { rewrite VALSRC. rewrite VALTGT. ss. }
      }
      { i. hexploit (VALS loc); eauto. i. des.
        { left. auto. }
        { right. esplits; eauto. rewrite ORD. destruct ordw; ss. }
        { right. esplits; eauto. rewrite ORD. ss. }
      }
      { ss. }
      { eapply space_future_memory_refl; eauto. refl. }
    }
    (* na write *)
    { inv LOCAL; ss. destruct ord; ss. }
    (* racy read *)
    { hexploit (ATLOCS loc); eauto. i. des.
      hexploit sim_thread_racy_read_step; eauto.
      i. des. right. esplits.
      { econs 2; [|refl]. econs.
        { econs. econs 2. econs; cycle 1.
          { eapply Local.step_racy_read; eauto. }
          { ss. eauto. }
        }
        { ss. }
      }
      { eauto. }
      { eauto. }
      { refl. }
      { refl. }
      { eauto. }
      { eapply map_future_memory_refl. }
      { i. hexploit ATLOCS; eauto. i. des. auto. }
      { i. left. auto. }
      { ss. }
      { eapply space_future_memory_refl; eauto. refl. }
    }
    (* racy write *)
    { des_ifs. hexploit (ATLOCS loc); eauto. i. des. subst.
      hexploit sim_thread_racy_write_step; eauto.
      i. des. left. esplits. red. esplits.
      { refl. }
      { econs 2. econs; cycle 1.
        { eapply Local.step_racy_write; eauto. }
        { ss. eauto. }
      }
      { ss. }
    }
    (* racy update *)
    { des_ifs. hexploit (ATLOCS loc); eauto. i. des. subst.
      hexploit sim_thread_racy_update_step; eauto.
      i. des. left. esplits. red. esplits.
      { refl. }
      { econs 2. econs; cycle 1.
        { eapply Local.step_racy_update; eauto. }
        { ss. eauto. }
      }
      { ss. }
    }
  Qed.

  Lemma sim_thread_local_program_step_release
        f0 vers0 flag_src0 flag_tgt0 vs_src0 vs_tgt0
        mem_src0 mem_tgt0 lc_src0 lc_tgt0 sc_src0 sc_tgt0
        pe_tgt pe_src
        e_tgt lc_tgt1 mem_tgt1 sc_tgt1
        lang st0 st1
        (SIM: SeqLiftStep.sim_thread
                f0 vers0 flag_src0 flag_tgt0 vs_src0 vs_tgt0
                mem_src0 mem_tgt0 lc_src0 lc_tgt0 sc_src0 sc_tgt0)
        (STEP: Local.program_step e_tgt lc_tgt0 sc_tgt0 mem_tgt0 lc_tgt1 sc_tgt1 mem_tgt1)
        (EVENTTGT: ThreadEvent.get_program_event e_tgt = pe_tgt)
        (EVENTLE: ProgramEvent.le pe_tgt pe_src)
        (LANGSTEP: lang.(Language.step) pe_src st0 st1)
        (CONSISTENT: Local.promise_consistent lc_tgt1)
        (LOCALSRC: Local.wf lc_src0 mem_src0)
        (LOCALTGT: Local.wf lc_tgt0 mem_tgt0)
        (MEMSRC: Memory.closed mem_src0)
        (MEMTGT: Memory.closed mem_tgt0)
        (SCSRC: Memory.closed_timemap sc_src0 mem_src0)
        (SCTGT: Memory.closed_timemap sc_tgt0 mem_tgt0)
        (WF: Mapping.wfs f0)
        (VERS: versions_wf f0 vers0)
        (ATOMIC: is_atomic_event pe_tgt)
        (NORMAL: is_release pe_tgt)
        (ATLOCS: forall loc (NNA: ~ loc_na loc),
            (<<FLAGSRC: flag_src0 loc = false>>) /\
            (<<FLAGTGT: flag_tgt0 loc = false>>) /\
            (<<VAL: option_rel Const.le (vs_tgt0 loc) (vs_src0 loc)>>))
        (AT: forall loc val (ACC: is_accessing pe_tgt = Some (loc, val)), loc_at loc)
        (ACQFLAG: forall loc
                         (SRC: flag_src0 loc = false) (TGT: flag_tgt0 loc = true),
            ~ is_acquire pe_tgt)
    :
      (<<FAILURE: Thread.steps_failure (Thread.mk lang st0 lc_src0 sc_src0 mem_src0)>>) \/
      exists lc_src1 mem_src1 sc_src1 lc_src2 mem_src2 sc_src2 lc_src3 mem_src3 sc_src3 f1 vers1 vs_src1 vs_tgt1 flag_tgt1 e_src,
        (<<STEPS0: rtc (@Thread.tau_step _) (Thread.mk lang st0 lc_src0 sc_src0 mem_src0) (Thread.mk lang st0 lc_src1 sc_src1 mem_src1)>>) /\
        (<<STEP: Thread.opt_step e_src (Thread.mk lang st0 lc_src1 sc_src1 mem_src1) (Thread.mk lang st1 lc_src2 sc_src2 mem_src2)>>) /\
        (<<STEPS1: rtc (@Thread.tau_step _) (Thread.mk lang st1 lc_src2 sc_src2 mem_src2) (Thread.mk lang st1 lc_src3 sc_src3 mem_src3)>>) /\
        (<<SIM: SeqLiftStep.sim_thread
                  f1 vers1 (fun _ => false) flag_tgt1 vs_src1 vs_tgt1
                  mem_src3 mem_tgt1 lc_src3 lc_tgt1 sc_src3 sc_tgt1>>) /\
        (<<WF: Mapping.wfs f1>>) /\
        (<<MAPLE: Mapping.les f0 f1>>) /\
        (<<VERSLE: versions_le vers0 vers1>>) /\
        (<<VERSWF: versions_wf f1 vers1>>) /\
        (<<MAPFUTURE: map_future_memory f0 f1 mem_src3>>) /\
        (<<SPACE: space_future_memory (unchangable mem_tgt0 lc_tgt0.(Local.promises)) f0 mem_src0 f1 mem_src3>>) /\
        (<<ATLOCS: forall loc (NNA: ~ loc_na loc), option_rel Const.le (vs_tgt1 loc) (vs_src1 loc)>>) /\
        (<<VAL: forall loc,
            (((<<SRC: vs_src1 loc = vs_src0 loc>>) /\ (<<TGT: vs_tgt1 loc = vs_tgt0 loc>>))) \/
            (exists val_src val_tgt,
                ((<<NNA: ~ loc_na loc>>) \/ ((<<NONESRC: vs_src0 loc = None>>) /\ (<<NONETGT: vs_tgt0 loc = None>>) /\ (<<ACQ: is_acquire pe_tgt>>))) /\
                (<<VALSRC: vs_src1 loc = Some val_src>>) /\ (<<VALTGT: vs_tgt1 loc = Some val_tgt>>) /\
                (<<VALLE: Const.le val_tgt val_src>>))>>) /\
        (<<DEBT: forall loc
                        (FLAG: flag_src0 loc = false -> flag_tgt0 loc = false)
                        (VAL: option_rel Const.le (vs_tgt0 loc) (vs_src0 loc)),
            flag_tgt1 loc = false>>) /\
        (<<EVENT: machine_event_le (ThreadEvent.get_machine_event e_tgt) (ThreadEvent.get_machine_event e_src)>>)
  .
  Proof.
    assert (exists (D: Loc.t -> Prop),
               (<<MIN: forall loc
                              (FLAG: flag_src0 loc = false -> flag_tgt0 loc = false)
                              (VAL: option_rel Const.le (vs_tgt0 loc) (vs_src0 loc)),
                   ~ D loc>>) /\
               (<<DEBT: forall loc, (<<DEBT: D loc>>) \/
                                    ((<<FLAG: flag_src0 loc = false -> flag_tgt0 loc = false>>) /\
                                     (<<VAL: option_rel Const.le (vs_tgt0 loc) (vs_src0 loc) \/ flag_src0 loc = false>>))>>)).
    { exists (fun loc => ~ ((<<FLAG: flag_src0 loc = false -> flag_tgt0 loc = false>>) /\
                            (<<VAL: option_rel Const.le (vs_tgt0 loc) (vs_src0 loc) \/ flag_src0 loc = false>>))).
      splits.
      { i. ii. eapply H. auto. }
      { ii. eapply or_comm. eapply classic. }
    }
    des. inv STEP; ss; clarify.
    (* write *)
    { hexploit (ATLOCS loc); eauto. i. des_ifs. des. subst.
      hexploit sim_thread_write_step_release; eauto.
      i. des. right. esplits.
      { eapply rtc_implies; [|eapply STEPS]. i.
        inv H. econs; eauto. inv TSTEP. auto.
      }
      { econs. econs 2. econs; cycle 1.
        { eapply Local.step_write; eauto. }
        { ss. }
      }
      { refl. }
      { eauto. }
      { eauto. }
      { eauto. }
      { eauto. }
      { eauto. }
      { eauto. }
      { eauto. }
      { i. hexploit ATLOCS; eauto. i. des.
        hexploit (VALS loc); eauto. i. des.
        { rewrite SRC. rewrite TGT. auto. }
        { rewrite VALSRC. rewrite VALTGT. ss. }
        { rewrite VALSRC1. rewrite VALTGT1. ss. }
      }
      { i. hexploit (VALS loc); eauto. i. des.
        { left. auto. }
        { subst. right. esplits; eauto. }
        { left. rewrite VALSRC0. rewrite VALTGT0. auto. }
      }
      { i. specialize (FLAG loc). des; ss. exfalso. eapply MIN; eauto. }
      { ss. econs. }
    }
    (* update *)
    { hexploit (ATLOCS loc); eauto. i. des_ifs. des. subst.
      hexploit sim_thread_update_step_release; eauto.
      i. des. right. esplits.
      { eapply rtc_implies; [|eapply STEPS]. i.
        inv H0. econs; eauto. inv TSTEP. auto.
      }
      { econs. econs 2. econs; cycle 1.
        { eapply Local.step_update.
          { eapply READ. instantiate (1:=valr0). etrans; eauto. }
          { eauto. }
        }
        { ss. }
      }
      { refl. }
      { eauto. }
      { eauto. }
      { eauto. }
      { eauto. }
      { eauto. }
      { eauto. }
      { eauto. }
      { i. hexploit ATLOCS; eauto. i. des. destruct (Loc.eq_dec loc0 loc).
        { red in UPDATED. des; subst.
          { rewrite TGT. rewrite SRC. ss. }
          { rewrite TGTNONE1. rewrite SRCNONE1. ss. }
        }
        { hexploit VALS; eauto. i. des.
          { rewrite SRC. rewrite TGT. auto. }
          { rewrite VALSRC. rewrite VALTGT0. ss. }
        }
      }
      { i. destruct (Loc.eq_dec loc loc0).
        { subst. red in UPDATED. des.
          { right. esplits; eauto. }
          { left. rewrite SRCNONE0. rewrite TGTNONE0. splits; auto. }
        }
        { hexploit (VALS loc); eauto. i. des; auto.
          right. esplits; eauto.
        }
      }
      { i. specialize (FLAG loc). des; ss. exfalso. eapply MIN; eauto. }
      { ss. econs. }
    }
    (* fence *)
    { hexploit sim_thread_fence_step_release; eauto.
      { ii. eapply ACQFLAG; eauto. rewrite H. destruct ordw; ss. }
      { ii. eapply ACQFLAG; eauto. rewrite H. destruct ordr; ss. }
      i. des. right. esplits.
      { refl. }
      { econs. econs 2. econs; cycle 1.
        { eapply Local.step_fence; eauto. }
        { ss. }
      }
      { eapply rtc_implies; [|eapply STEPS]. i.
        inv H. econs; eauto. inv TSTEP. auto.
      }
      { eauto. }
      { eauto. }
      { eauto. }
      { refl. }
      { eauto. }
      { eauto. }
      { eauto. }
      { i. hexploit ATLOCS; eauto. i. des.
        hexploit (VALS loc); eauto. i. des.
        { rewrite SRC. rewrite TGT. auto. }
        { rewrite VALSRC. rewrite VALTGT. ss. }
        { rewrite VALSRC. rewrite VALTGT. ss. }
      }
      { i. hexploit (VALS loc); eauto. i. des.
        { left. auto. }
        { right. esplits; eauto. right. rewrite ORD. destruct ordw; ss. }
        { right. esplits; eauto. right. rewrite ORD. ss. }
      }
      { i. specialize (FLAG loc). des; ss. exfalso. eapply MIN; eauto. }
      { ss. econs. }
    }
    (* syscall *)
    { des_ifs. hexploit sim_thread_fence_step_release; eauto.
      i. des. right. esplits.
      { refl. }
      { econs. econs 2. econs; cycle 1.
        { eapply Local.step_syscall; eauto. }
        { eauto. }
      }
      { eapply rtc_implies; [|eapply STEPS]. i.
        inv H. econs; eauto. inv TSTEP. auto.
      }
      { eauto. }
      { eauto. }
      { eauto. }
      { refl. }
      { eauto. }
      { eauto. }
      { eauto. }
      { i. hexploit ATLOCS; eauto. i. des.
        hexploit (VALS loc); eauto. i. des.
        { rewrite SRC. rewrite TGT. auto. }
        { rewrite VALSRC. rewrite VALTGT. ss. }
        { rewrite VALSRC. rewrite VALTGT. ss. }
      }
      { i. hexploit (VALS loc); eauto. i. des.
        { left. auto. }
        { right. esplits; eauto. }
        { right. esplits; eauto. }
      }
      { i. specialize (FLAG loc). des; ss. exfalso. eapply MIN; eauto. }
      { ss. econs. auto. }
    }
    (* na write *)
    { exfalso. inv LOCAL. destruct ord; ss. }
    (* racy write *)
    { left. des_ifs. hexploit (ATLOCS loc); eauto. i. des. subst.
      hexploit sim_thread_racy_write_step; eauto.
      i. des. esplits. red. esplits.
      { refl. }
      { econs 2. econs; cycle 1.
        { eapply Local.step_racy_write; eauto. }
        { ss. eauto. }
      }
      { ss. }
    }
    (* racy update *)
    { left. des_ifs. hexploit (ATLOCS loc); eauto. i. des. subst.
      hexploit sim_thread_racy_update_step; eauto.
      i. des. esplits. red. esplits.
      { refl. }
      { econs 2. econs; cycle 1.
        { eapply Local.step_racy_update; eauto. }
        { ss. eauto. }
      }
      { ss. }
    }
  Qed.

  Lemma sim_lift_at_step_normal c:
    forall
      w0 p0 D0 smem_src0 smem_tgt0 mem_src0 mem_tgt0 lc_src0 lc_tgt0 sc_src0 sc_tgt0
      lang_src lang_tgt sim_terminal st_src0 st_tgt0
      e st_tgt1 lc_tgt1 sc_tgt1 mem_tgt1
      (LIFT: sim_state_lift c w0 smem_src0 smem_tgt0 p0 D0 mem_src0 mem_tgt0 lc_src0 lc_tgt0 sc_src0 sc_tgt0)
      (STEP: Thread.program_step e (Thread.mk lang_tgt st_tgt0 lc_tgt0 sc_tgt0 mem_tgt0) (Thread.mk _ st_tgt1 lc_tgt1 sc_tgt1 mem_tgt1))
      (SIM: sim_seq_at_step_case (@sim_seq lang_src lang_tgt sim_terminal) p0 D0 (SeqState.mk lang_src st_src0 smem_src0) (SeqState.mk lang_tgt st_tgt0 smem_tgt0))
      (ATOMIC: is_atomic_event (ThreadEvent.get_program_event e))
      (RELEASE: is_release (ThreadEvent.get_program_event e) = false)
      (NOMIXSRC: nomix loc_na loc_at _ st_src0)
      (NOMIXTGT: nomix loc_na loc_at _ st_tgt0)
      (CONSISTENT: Local.promise_consistent lc_tgt1)
      (WF_SRC0: Local.wf lc_src0 mem_src0)
      (WF_TGT0: Local.wf lc_tgt0 mem_tgt0)
      (SC_SRC0: Memory.closed_timemap sc_src0 mem_src0)
      (SC_TGT0: Memory.closed_timemap sc_tgt0 mem_tgt0)
      (MEM_SRC0: Memory.closed mem_src0)
      (MEM_TGT0: Memory.closed mem_tgt0),
    exists st_src1 lc_src1 sc_src1 mem_src1,
      (<<STEPS: rtc (@Thread.tau_step _)
                    (Thread.mk _ st_src0 lc_src0 sc_src0 mem_src0)
                    (Thread.mk _ st_src1 lc_src1 sc_src1 mem_src1)>>) /\
        ((<<FAILURE: Thread.steps_failure (Thread.mk _ st_src1 lc_src1 sc_src1 mem_src1)>>) \/
           (exists w1 p1 D1 smem_src1 smem_tgt1,
               (<<LIFT: sim_state_lift true w1 smem_src1 smem_tgt1 p1 D1 mem_src1 mem_tgt1 lc_src1 lc_tgt1 sc_src1 sc_tgt1>>) /\
                 (<<SIM: @sim_seq _ _ sim_terminal p1 D1 (SeqState.mk lang_src st_src1 smem_src1) (SeqState.mk lang_tgt st_tgt1 smem_tgt1)>>) /\
                 (<<WORLD: world_messages_le (unchangable mem_src0 lc_src0.(Local.promises)) (unchangable mem_tgt0 lc_tgt0.(Local.promises)) w0 w1>>) /\
                 (<<NOMIXSRC: nomix loc_na loc_at _ st_src1>>) /\
                 (<<NOMIXTGT: nomix loc_na loc_at _ st_tgt1>>) /\
                 (<<NFAILURE: ThreadEvent.get_machine_event e = MachineEvent.silent>>))).
  Proof.
    i. hexploit PromiseConsistent.step_promise_consistent.
    { econs 2; eauto. }
    { eauto. }
    { eauto. }
    { eauto. }
    { eauto. }
    intros CONSTGT0. ss.
    inv STEP.
    hexploit sim_seq_atomic_step; eauto. i. des.
    destruct st_src1 as [st_src1 smem_src1].
    hexploit sim_lift_src_na_steps; eauto. i. des.
    hexploit Thread.rtc_tau_step_future; eauto. i. des; ss.
    punfold NOMIXTGT. exploit NOMIXTGT; eauto. i. des.
    punfold NOMIX. exploit NOMIX; eauto. i. des. pclearbot.
    inv LIFT1.
    assert (ACQFLAG: forall loc
                            (NONE: flag_src loc = false)
                            (SOME: flag_tgt loc = true),
               ~ is_acquire (ThreadEvent.get_program_event e)).
    { ii. hexploit ACQ; eauto. i. ss.
      hexploit (FLAGS loc); eauto. i. inv H1.
      rewrite NONE in *. rewrite SOME in *. ss.
      hexploit TGT; auto. rewrite flag_join_comm. i.
      specialize (H0 loc). unfold Flags.join in H0.
      rewrite H1 in H0. rewrite SRC in H0. ss.
    }
    hexploit sim_thread_local_program_step_normal; eauto.
    { ii. clarify. }
    i. des.
    { esplits.
      { eauto. }
      { left. eauto. }
    }
    hexploit event_step_exists.
    { eapply (@lift_output_wf (ThreadEvent.get_program_event e) vs_src1). }
    i. des. hexploit SIM0; eauto.
    { eapply lift_output_wf. }
    i. des. destruct mem_src, m2.
    hexploit sim_lift_event_step_normal; eauto.
    { ii. clarify. }
    i. des. ss. esplits.
    { etrans; eassumption. }
    right. eexists (_, _, _). esplits; auto.
    { econs; eauto. i. hexploit (ATLOCS loc); eauto. i. des. splits; auto. }
    { ss. rewrite RELEASE in *. auto. }
    { etrans; eauto. ss. splits; auto.
      eapply Thread.rtc_tau_step_future in STEPS1; eauto. ss. des.
      eapply Memory.future_future_weak; eauto.
    }
  Qed.

  Lemma sim_lift_at_step_release c:
    forall
      w0 p0 D0 smem_src0 smem_tgt0 mem_src0 mem_tgt0 lc_src0 lc_tgt0 sc_src0 sc_tgt0
      lang_src lang_tgt sim_terminal st_src0 st_tgt0
      e_tgt st_tgt1 lc_tgt1 sc_tgt1 mem_tgt1
      (LIFT: sim_state_lift c w0 smem_src0 smem_tgt0 p0 D0 mem_src0 mem_tgt0 lc_src0 lc_tgt0 sc_src0 sc_tgt0)
      (STEP: Thread.program_step e_tgt (Thread.mk lang_tgt st_tgt0 lc_tgt0 sc_tgt0 mem_tgt0) (Thread.mk _ st_tgt1 lc_tgt1 sc_tgt1 mem_tgt1))
      (SIM: sim_seq_at_step_case (@sim_seq lang_src lang_tgt sim_terminal) p0 D0 (SeqState.mk lang_src st_src0 smem_src0) (SeqState.mk lang_tgt st_tgt0 smem_tgt0))
      (ATOMIC: is_atomic_event (ThreadEvent.get_program_event e_tgt))
      (RELEASE: is_release (ThreadEvent.get_program_event e_tgt) = true)
      (NOMIXSRC: nomix loc_na loc_at _ st_src0)
      (NOMIXTGT: nomix loc_na loc_at _ st_tgt0)
      (CONSISTENT: Local.promise_consistent lc_tgt1)
      (WF_SRC0: Local.wf lc_src0 mem_src0)
      (WF_TGT0: Local.wf lc_tgt0 mem_tgt0)
      (SC_SRC0: Memory.closed_timemap sc_src0 mem_src0)
      (SC_TGT0: Memory.closed_timemap sc_tgt0 mem_tgt0)
      (MEM_SRC0: Memory.closed mem_src0)
      (MEM_TGT0: Memory.closed mem_tgt0),
      (<<FAILURE: Thread.steps_failure (Thread.mk _ st_src0 lc_src0 sc_src0 mem_src0)>>) \/
      exists st_src1 st_src2 lc_src1 sc_src1 mem_src1 lc_src2 sc_src2 mem_src2 lc_src3 sc_src3 mem_src3 w1 p1 D1 smem_src1 smem_tgt1 e_src,
        (<<STEPS0: rtc (@Thread.tau_step _)
                       (Thread.mk _ st_src0 lc_src0 sc_src0 mem_src0)
                       (Thread.mk _ st_src1 lc_src1 sc_src1 mem_src1)>>) /\
        (<<STEPS: Thread.opt_step
                    e_src
                    (Thread.mk _ st_src1 lc_src1 sc_src1 mem_src1)
                    (Thread.mk _ st_src2 lc_src2 sc_src2 mem_src2)>>) /\
        (<<STEPS1: rtc (@Thread.tau_step _)
                       (Thread.mk _ st_src2 lc_src2 sc_src2 mem_src2)
                       (Thread.mk _ st_src2 lc_src3 sc_src3 mem_src3)>>) /\
        (<<LIFT: sim_state_lift false w1 smem_src1 smem_tgt1 p1 D1 mem_src3 mem_tgt1 lc_src3 lc_tgt1 sc_src3 sc_tgt1>>) /\
        (<<SIM: @sim_seq_interference _ _ sim_terminal p1 D1 (SeqState.mk lang_src st_src2 smem_src1) (SeqState.mk lang_tgt st_tgt1 smem_tgt1)>>) /\
        (<<SC: sim_timemap_lift w1 sc_src3 sc_tgt1>>) /\
        (<<MEM: sim_memory_lift w1 mem_src3 mem_tgt1>>) /\
        (<<WORLD: world_messages_le (unchangable mem_src0 lc_src0.(Local.promises)) (unchangable mem_tgt0 lc_tgt0.(Local.promises)) w0 w1>>) /\
        (<<NOMIXSRC: nomix loc_na loc_at _ st_src2>>) /\
        (<<NOMIXTGT: nomix loc_na loc_at _ st_tgt1>>) /\
        (<<EVENT: machine_event_le (ThreadEvent.get_machine_event e_tgt) (ThreadEvent.get_machine_event e_src)>>)
  .
  Proof.
    i. hexploit PromiseConsistent.step_promise_consistent.
    { econs 2; eauto. }
    { eauto. }
    { eauto. }
    { eauto. }
    { eauto. }
    intros CONSTGT0. ss.
    inv STEP. hexploit sim_seq_atomic_step; eauto. i. des.
    destruct st_src1 as [st_src1 smem_src1].
    hexploit sim_lift_src_na_steps; eauto. i. des.
    hexploit Thread.rtc_tau_step_future; eauto. i. des; ss.
    punfold NOMIXTGT. exploit NOMIXTGT; eauto. i. des.
    punfold NOMIX. exploit NOMIX; eauto. i. des. pclearbot.
    inv LIFT1.
    assert (ACQFLAG: forall loc
                            (NONE: flag_src loc = false)
                            (SOME: flag_tgt loc = true),
               ~ is_acquire (ThreadEvent.get_program_event e_tgt)).
    { ii. hexploit ACQ; eauto. i. ss.
      hexploit (FLAGS loc); eauto. i. inv H1.
      rewrite NONE in *. rewrite SOME in *. ss.
      hexploit TGT; auto. rewrite flag_join_comm. i.
      specialize (H0 loc). unfold Flags.join in H0.
      rewrite H1 in H0. rewrite SRC in H0. ss.
    }
    hexploit sim_thread_local_program_step_release; eauto. i. des.
    { left. eapply rtc_steps_thread_failure; eauto. }
    hexploit event_step_exists.
    { eapply (@lift_output_wf (ThreadEvent.get_program_event e_tgt) vs_src1). }
    i. des. hexploit SIM0; eauto.
    { eapply lift_output_wf. }
    i. des. destruct mem_src, m2.
    hexploit sim_lift_event_step_release; [eapply STEP_SRC|eapply STEP1|..]; eauto.
    i. des. esplits. right. esplits.
    { etrans; eauto. }
    { eauto. }
    { eapply STEPS2. }
    { econs; eauto. i. ss. hexploit (ATLOCS loc); eauto. i. des.
      hexploit DEBT; eauto. i. splits; auto.
    }
    { rewrite RELEASE in SIM3. ss. }
    { inv SIM2. ss. }
    { inv SIM2. ss. splits; auto. eapply sim_memory_sim_memory_interference; eauto. }
    { etrans; eauto. ss. i. splits; eauto.
      eapply Thread.rtc_tau_step_future in STEPS1; eauto. ss. des.
      eapply Thread.opt_step_future in STEP0; eauto. ss. des.
      eapply Thread.rtc_tau_step_future in STEPS2; eauto. ss. des.
      eapply Memory.future_future_weak; eauto. etrans; eauto. etrans; eauto.
    }
    { auto. }
    { auto. }
    { auto. }
  Qed.

  Definition racy_update_event (e: ThreadEvent.t): Prop :=
    match e with
    | ThreadEvent.update _ _ _ _ _ _ _ ordr ordw =>
      orb (Ordering.le ordw Ordering.na) (Ordering.le ordr Ordering.na)
    | _ => False
    end.

  Lemma program_step_unchangable e lc0 sc0 mem0 lc1 sc1 mem1
        (STEP: Local.program_step e lc0 sc0 mem0 lc1 sc1 mem1)
    :
    unchangable mem0 lc0.(Local.promises) <4= unchangable mem1 lc1.(Local.promises).
  Proof.
    i. inv STEP; ss; try inv LOCAL; ss.
    - eapply unchangable_write; eauto.
    - inv LOCAL1. inv LOCAL2. ss. inv WRITE.
      eapply unchangable_write; eauto.
    - eapply unchangable_write_na; eauto.
  Qed.

  Lemma sim_lift_na_step_aux c:
    forall
      w0 p0 D0 smem_src0 smem_tgt0 mem_src0 mem_tgt0 lc_src0 lc_tgt0 sc_src0 sc_tgt0
      lang_src lang_tgt sim_terminal st_src0 st_tgt0
      e st_tgt1 lc_tgt1 sc_tgt1 mem_tgt1
      (LIFT: sim_state_lift c w0 smem_src0 smem_tgt0 p0 D0 mem_src0 mem_tgt0 lc_src0 lc_tgt0 sc_src0 sc_tgt0)
      (STEP: Thread.program_step e (Thread.mk lang_tgt st_tgt0 lc_tgt0 sc_tgt0 mem_tgt0) (Thread.mk _ st_tgt1 lc_tgt1 sc_tgt1 mem_tgt1))
      (SIM: sim_seq_na_step_case (@sim_seq lang_src lang_tgt sim_terminal) p0 D0 (SeqState.mk lang_src st_src0 smem_src0) (SeqState.mk lang_tgt st_tgt0 smem_tgt0))
      (ATOMIC: is_atomic_event (ThreadEvent.get_program_event e) = false)
      (LOWER: is_na_write e -> mem_tgt1 = mem_tgt0)
      (NOMIXSRC: nomix loc_na loc_at _ st_src0)
      (NOMIXTGT: nomix loc_na loc_at _ st_tgt0)
      (CONSISTENT: Local.promise_consistent lc_tgt1)
      (WF_SRC0: Local.wf lc_src0 mem_src0)
      (WF_TGT0: Local.wf lc_tgt0 mem_tgt0)
      (SC_SRC0: Memory.closed_timemap sc_src0 mem_src0)
      (SC_TGT0: Memory.closed_timemap sc_tgt0 mem_tgt0)
      (MEM_SRC0: Memory.closed mem_src0)
      (MEM_TGT0: Memory.closed mem_tgt0),
    exists st_src1 lc_src1 sc_src1 mem_src1,
      (<<STEPS: rtc (@Thread.tau_step _)
                    (Thread.mk _ st_src0 lc_src0 sc_src0 mem_src0)
                    (Thread.mk _ st_src1 lc_src1 sc_src1 mem_src1)>>) /\
        ((<<FAILURE: Thread.steps_failure (Thread.mk _ st_src1 lc_src1 sc_src1 mem_src1)>>) \/
           (exists w1 p1 D1 smem_src1 smem_tgt1,
               (<<LIFT: sim_state_lift true w1 smem_src1 smem_tgt1 p1 D1 mem_src1 mem_tgt1 lc_src1 lc_tgt1 sc_src1 sc_tgt1>>) /\
                 (<<SIM: @sim_seq _ _ sim_terminal p1 D1 (SeqState.mk lang_src st_src1 smem_src1) (SeqState.mk lang_tgt st_tgt1 smem_tgt1)>>) /\
                 (<<WORLD: world_messages_le (unchangable mem_src0 lc_src0.(Local.promises)) (unchangable mem_tgt0 lc_tgt0.(Local.promises)) w0 w1>>) /\
                 (<<NOMIXSRC: nomix loc_na loc_at _ st_src1>>) /\
                 (<<NOMIXTGT: nomix loc_na loc_at _ st_tgt1>>) /\
                 (<<FAILURE: ThreadEvent.get_machine_event e = MachineEvent.silent>>))).
  Proof.
    i. hexploit PromiseConsistent.step_promise_consistent.
    { econs 2; eauto. }
    { eauto. }
    { eauto. }
    { eauto. }
    { eauto. }
    intros CONSTGT0. ss.
    hexploit Thread.program_step_future; eauto. i. des; ss.
    inv STEP. punfold NOMIXTGT. exploit NOMIXTGT; eauto. i. des. pclearbot.
    hexploit sim_lift_tgt_na_local_step; eauto.
    { ii. clarify. }
    i. des.
    hexploit Thread.rtc_tau_step_future; eauto. i. des; ss.
    exploit SIM; eauto.
    { econs; eauto. }
    i. des. destruct (classic (me = MachineEvent.failure)).
    { subst. inv STEP0. hexploit LIFTAUX; eauto. i. des. destruct st_src1.
      hexploit sim_lift_src_na_steps; eauto. i. des; ss. destruct st_src2.
      hexploit Thread.rtc_tau_step_future; eauto. i. des; ss.
      hexploit sim_lift_src_na_step; eauto. i. des; ss.
      esplits; [refl|]. left. red. esplits.
      { etrans; [eauto|]. etrans; eauto. }
      { replace pf with true in *; [eauto|].
        inv STEP0; ss. inv STEP2; ss.
      }
      { eauto. }
    }
    { hexploit LIFT0; eauto. i. des. destruct st_src1.
      hexploit sim_lift_src_na_steps; eauto. i. des; ss. destruct st_src2.
      hexploit Thread.rtc_tau_step_future; eauto. i. des; ss.
      hexploit sim_lift_src_na_opt_step; eauto. i. des; ss. subst.
      esplits.
      { etrans; [eauto|]. etrans; [eauto|]. eapply Thread.tau_opt_tau; eauto.
        inv STEP; ss.
        { rewrite PERM in *. destruct (p0 loc); ss. }
        { rewrite <- H1 in *. ss. }
        { rewrite <- H1 in *. ss. }
      }
      { right. hexploit LIFT2; eauto. i. des. esplits; eauto.
        etrans; eauto. eapply world_messages_le_mon.
        { etrans; eauto. }
        { i. eapply unchangable_rtc_tau_step_increase in STEPS; eauto. }
        { i. eapply program_step_unchangable; eauto. }
      }
    }
  Qed.

  Lemma sim_lift_na_step c:
    forall
      w0 p0 D0 smem_src0 smem_tgt0 mem_src0 mem_tgt0 lc_src0 lc_tgt0 sc_src0 sc_tgt0
      lang_src lang_tgt sim_terminal st_src0 st_tgt0
      e st_tgt1 lc_tgt1 sc_tgt1 mem_tgt1
      (LIFT: sim_state_lift c w0 smem_src0 smem_tgt0 p0 D0 mem_src0 mem_tgt0 lc_src0 lc_tgt0 sc_src0 sc_tgt0)
      (STEP: Thread.program_step e (Thread.mk lang_tgt st_tgt0 lc_tgt0 sc_tgt0 mem_tgt0) (Thread.mk _ st_tgt1 lc_tgt1 sc_tgt1 mem_tgt1))
      (SIM: sim_seq_na_step_case (@sim_seq lang_src lang_tgt sim_terminal) p0 D0 (SeqState.mk lang_src st_src0 smem_src0) (SeqState.mk lang_tgt st_tgt0 smem_tgt0))
      (ATOMIC: is_atomic_event (ThreadEvent.get_program_event e) = false)
      (LOWER: is_na_write e -> mem_tgt1 = mem_tgt0)
      (NOMIXSRC: nomix loc_na loc_at _ st_src0)
      (NOMIXTGT: nomix loc_na loc_at _ st_tgt0)
      (CONSISTENT: Local.promise_consistent lc_tgt1)
      (WF_SRC0: Local.wf lc_src0 mem_src0)
      (WF_TGT0: Local.wf lc_tgt0 mem_tgt0)
      (SC_SRC0: Memory.closed_timemap sc_src0 mem_src0)
      (SC_TGT0: Memory.closed_timemap sc_tgt0 mem_tgt0)
      (MEM_SRC0: Memory.closed mem_src0)
      (MEM_TGT0: Memory.closed mem_tgt0),
    exists st_src1 lc_src1 sc_src1 mem_src1,
      (<<STEPS: rtc (@Thread.tau_step _)
                    (Thread.mk _ st_src0 lc_src0 sc_src0 mem_src0)
                    (Thread.mk _ st_src1 lc_src1 sc_src1 mem_src1)>>) /\
        ((<<FAILURE: Thread.steps_failure (Thread.mk _ st_src1 lc_src1 sc_src1 mem_src1)>>) \/
           (exists w1 p1 D1 smem_src1 smem_tgt1,
               (<<LIFT: sim_state_lift true w1 smem_src1 smem_tgt1 p1 D1 mem_src1 mem_tgt1 lc_src1 lc_tgt1 sc_src1 sc_tgt1>>) /\
                 (<<SIM: @sim_seq _ _ sim_terminal p1 D1 (SeqState.mk lang_src st_src1 smem_src1) (SeqState.mk lang_tgt st_tgt1 smem_tgt1)>>) /\
                 (<<WORLD: world_messages_le (unchangable mem_src0 lc_src0.(Local.promises)) (unchangable mem_tgt0 lc_tgt0.(Local.promises)) w0 w1>>) /\
                 (<<NOMIXSRC: nomix loc_na loc_at _ st_src1>>) /\
                 (<<NOMIXTGT: nomix loc_na loc_at _ st_tgt1>>) /\
                 (<<FAILURE: ThreadEvent.get_machine_event e = MachineEvent.silent>>) /\
                 (<<UPDATE: ~ racy_update_event e>>))).
  Proof.
    i. hexploit PromiseConsistent.step_promise_consistent.
    { econs 2; eauto. }
    { eauto. }
    { eauto. }
    { eauto. }
    { eauto. }
    i. ss. destruct (classic (racy_update_event e)).
    { destruct e; ss.
      assert (RACE: Thread.program_step (ThreadEvent.racy_update loc Time.bot valr valw ordr ordw) (Thread.mk lang_tgt st_tgt0 lc_tgt0 sc_tgt0 mem_tgt0) (Thread.mk lang_tgt st_tgt1 lc_tgt0 sc_tgt0 mem_tgt0)).
      { inv STEP; ss. econs; ss. econs.
        destruct (Ordering.le ordw Ordering.na) eqn:ORDR; ss.
        { econs 2; eauto. }
        { econs 1; eauto. }
      }
      hexploit sim_lift_na_step_aux; eauto. i. des; ss. esplits; eauto.
    }
    { hexploit sim_lift_na_step_aux; eauto. i. des.
      { esplits; eauto. }
      { esplits; eauto. right. esplits; eauto. }
    }
  Qed.

  Lemma sim_seq_cond_sim_seq
        c lang_src lang_tgt sim_terminal p D st_src st_tgt
        (SIM: @sim_seq_cond c lang_src lang_tgt sim_terminal p D st_src st_tgt)
    :
      @sim_seq lang_src lang_tgt sim_terminal p D st_src st_tgt.
  Proof.
    destruct c; ss. eapply sim_seq_interference_sim_seq; auto.
  Qed.

  Lemma sim_lift lang_src lang_tgt sim_terminal:
    forall
      c (st_src: lang_src.(Language.state)) (st_tgt: lang_tgt.(Language.state))
      w p D smem_src smem_tgt mem_src mem_tgt lc_src lc_tgt sc_src sc_tgt
      (SIM: @sim_seq_cond c _ _ sim_terminal p D (SeqState.mk _ st_src smem_src) (SeqState.mk _ st_tgt smem_tgt))
      (NOMIXSRC: nomix loc_na loc_at _ st_src)
      (NOMIXTGT: nomix loc_na loc_at _ st_tgt)
      (LIFT: sim_state_lift c w smem_src smem_tgt p D mem_src mem_tgt lc_src lc_tgt sc_src sc_tgt),
      @sim_thread
        world world_messages_le sim_memory_lift sim_timemap_lift loc_na
        lang_src lang_tgt c w st_src lc_src sc_src mem_src st_tgt lc_tgt sc_tgt mem_tgt.
  Proof.
    assert (UPACO: upaco7 _sim_seq bot7 = sim_seq).
    { repeat (let x := fresh "x" in extensionality x).
      apply Coq.Logic.PropExtensionality.propositional_extensionality.
      split; auto. i. pclearbot. auto.
    }
    pcofix CIH. i. pfold. ii.
    destruct (classic (sim_seq_failure_case p (SeqState.mk _ st_src smem_src))).
    { right. splits. red. esplits; [refl|].
      eapply sim_lift_failure_case; eauto.
    }
    left. splits.
    { ii. eapply sim_seq_cond_sim_seq in SIM. punfold SIM. inv SIM; ss.
      rewrite UPACO in *. inv STEP_TGT.
      { inv STEP; ss. }
      destruct (is_atomic_event (ThreadEvent.get_program_event e_tgt)) eqn:NA.
      { destruct (is_release (ThreadEvent.get_program_event e_tgt)) eqn:ISRELEASE.
        { hexploit sim_lift_at_step_release; eauto. i. des.
          { esplits; eauto. }
          { esplits; eauto. right. esplits; eauto. }
        }
        { hexploit sim_lift_at_step_normal; eauto. i. des.
          { esplits; eauto. }
          { exfalso. destruct e_tgt eqn:EVENT; ss.
            { destruct ord; ss. }
            { rewrite RELEASE in *. ss. }
            { destruct ordw; ss. }
          }
        }
      }
      { hexploit sim_lift_na_step; eauto.
        { ii. destruct e_tgt eqn:EQ; ss. destruct ord; ss. }
        i. des.
        { esplits; eauto. }
        { exfalso. destruct e_tgt eqn:EVENT; ss.
          { destruct ord; ss. }
          { exfalso. eapply UPDATE. destruct ordr, ordw; ss. }
        }
      }
    }
    { ii. eapply sim_seq_cond_sim_seq in SIM. punfold SIM. inv SIM; ss.
      hexploit sim_lift_partial_case; eauto.
    }
    { ii. eapply sim_seq_cond_sim_seq in SIM. punfold SIM. inv SIM; ss.
      rewrite UPACO in *. inv STEP_TGT. ss.
      destruct (is_atomic_event (ThreadEvent.get_program_event e_tgt)) eqn:NA.
      { destruct (is_release (ThreadEvent.get_program_event e_tgt)) eqn:ISRELEASE.
        { hexploit sim_lift_at_step_release; eauto. i. des.
          { esplits; eauto. }
          { exfalso. destruct e_tgt eqn:EQ; ss.
            inv STEP. inv LOCAL. inv LOCAL0. destruct ord; ss.
          }
        }
        { hexploit sim_lift_at_step_normal; eauto. i. des.
          { esplits; eauto. }
          {  esplits; eauto. right. esplits; eauto. }
        }
      }
      { hexploit sim_lift_na_step; eauto. i. des.
        { esplits; eauto. }
        { esplits; eauto. right. esplits; eauto. }
      }
    }
    { ii. eapply sim_seq_cond_sim_seq in SIM. punfold SIM. inv SIM; ss.
      hexploit sim_lift_terminal_case; eauto.
    }
    { ii. subst. inv STEP_TGT.
      2:{ inv STEP. inv LOCAL; ss. }
      inv STEP. hexploit sim_lift_interference_promise; eauto. i. des.
      { esplits; eauto. }
      { esplits; eauto. right. esplits; eauto. }
    }
    { ii. subst. hexploit sim_lift_interference_cap; eauto. i. des.
      esplits; eauto.
    }
    { ii. subst. hexploit sim_lift_interference_future; try eassumption. i. des.
      { esplits; eauto. }
      { esplits; eauto. right. esplits; eauto. }
    }
  Qed.

  Lemma sim_lift_init lang_src lang_tgt sim_terminal:
    forall
      (st_src: lang_src.(Language.state)) (st_tgt: lang_tgt.(Language.state))
      (SIM: @sim_seq_all lang_src lang_tgt sim_terminal st_src st_tgt)
      (NOMIXSRC: nomix loc_na loc_at _ st_src)
      (NOMIXTGT: nomix loc_na loc_at _ st_tgt),
      @sim_thread
        world world_messages_le sim_memory_lift sim_timemap_lift loc_na
        lang_src lang_tgt false initial_world
        st_src Local.init TimeMap.bot Memory.init
        st_tgt Local.init TimeMap.bot Memory.init.
  Proof.
    i. eapply sim_lift; eauto.
    { simpl. eapply sim_seq_init. eauto. }
    { econs; eauto.
      { eapply initial_sim_thread. }
      { ii. econs; refl. }
      { ii. econs; ss. }
      { i. splits; ss. }
      { i. ss. }
      { eapply initial_mappings_wf. }
      { eapply initial_versions_wf. }
    }
  Qed.
End LIFT.
