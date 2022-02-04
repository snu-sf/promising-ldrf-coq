Require Import Bool.
Require Import RelationClasses.
Require Import Program.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Language.
From PromisingLib Require Import Loc.

Require Import Event.
Require Import List.

Require Import SeqLib.
Require Import Simple.
Require Import OracleFacts.

Require Import SimAux.
Require Import SeqAux.
Require Import SequentialBehavior.

Require Import SequentialAdequacy.

Set Implicit Arguments.

Section ADEQUACY2.

  Variable lang_src lang_tgt: language.

  Lemma thread_steps_app_behavior
        th0 tr0 th1 tr1 R
        (STEPS: SeqThread.steps (SeqState.na_step (lang:=lang_src)) tr0 th0 th1)
        (BEH: SeqBehavior.behavior (SeqState.na_step (lang:=lang_src)) th1 (tr1, R))
    :
      SeqBehavior.behavior (SeqState.na_step (lang:=lang_src)) th0 (tr0 ++ tr1, R).
  Proof.
    depgen tr1. depgen R. induction STEPS; i; ss.
    { econs 4; eauto. }
    { econs 5; eauto. }
  Qed.

  Lemma sim_fail_ub
        st p o tr d
        (WF: Oracle.wf o)
        (FAILURE: sim_seq_failure_case p st)
    :
      exists tr1 : SeqTrace.t,
        SeqBehavior.behavior
          (SeqState.na_step (lang:=lang_src))
          {| SeqThread.state := st; SeqThread.perm := p; SeqThread.oracle := o |} tr1 /\
        SeqTrace.le d tr tr1.
  Proof.
    unfold sim_seq_failure_case in FAILURE. hexploit FAILURE; clear FAILURE. eauto. i; des.
    exists (tr0, SeqTrace.ub). split.
    2:{ eapply SeqTrace.le_ub; eauto. }
    dup FAILURE. rename FAILURE0 into THREADFAIL.
    unfold SeqThread.failure in FAILURE. des. inv FAILURE0.
    replace tr0 with (tr0 ++ []).
    2:{ apply app_nil_r. }
    destruct st0. eapply thread_steps_app_behavior.
    2:{ eapply SeqBehavior.behavior_ub. eauto. }
    auto.
  Qed.


        (* (STEPS_SRC: state_steps state_step tr_src (SeqState.mk _ st_src m) st1_src p p1) *)
        (* (STEPS_TGT: state_steps (@SeqState.na_step lang_tgt) tr_tgt (SeqState.mk _ st_tgt m) st0_tgt p p1) *)
        (* (NASTEPS_TGT: rtc (SeqState.na_step p1 MachineEvent.silent) st0_tgt st1_tgt) *)
        (* (TRACES: match_trace (min_match SeqEvent.input_match) Flags.bot d tr_src tr_tgt): *)

  Lemma simulation_implies_refinement_aux
        (st_src: lang_src.(Language.state)) (st_tgt: lang_tgt.(Language.state))
        p d m_src m_tgt
        (SIM: sim_seq (fun _ _ => True) p d (SeqState.mk _ st_src m_src) (SeqState.mk _ st_tgt m_tgt))
        o (WF: Oracle.wf o)
        (* (SIM: sim_seq_all _ _ (fun _ _ => True) st_src st_tgt) *)
        (RECEPTIVE: receptive _ st_tgt) (*maybe not needed*)
    :
      SeqTrace.incl
        (SeqBehavior.behavior
           (SeqState.na_step (lang:=lang_tgt))
           {| SeqThread.state := {| SeqState.state := st_tgt; SeqState.memory := m_tgt |};
              SeqThread.perm := p; SeqThread.oracle := o |})
        (SeqBehavior.behavior
           (SeqState.na_step (lang:=lang_src))
           {| SeqThread.state := {| SeqState.state := st_src; SeqState.memory := m_src |};
              SeqThread.perm := p; SeqThread.oracle := o |}).
  Proof.
    unfold SeqTrace.incl. i.
    cut 
  (exists tr1 : SeqTrace.t,
    SeqBehavior.behavior (SeqState.na_step (lang:=lang_src))
      {| SeqThread.state := {| SeqState.state := st_src; SeqState.memory := m_src |}; SeqThread.perm := p; SeqThread.oracle := o |}
      tr1 /\ SeqTrace.le d tr0 tr1).
    { i; des. esplits; eauto. eapply SeqTrace.le_deferred_mon; eauto. eapply Flags.bot_spec. }

    match goal with | [H: SeqBehavior.behavior _ ?a _ |- _] => remember a as th_tgt0 end.
    depgen st_src. depgen st_tgt. depgen o. depgen p. depgen m_src. depgen m_tgt. depgen d.
    induction H.

    4:{ i. clarify; ss.
        punfold SIM. inv SIM.
        2:{ eapply sim_fail_ub; eauto. }
        inv STEP.
        clear TERMINAL ATSTEP PARTIAL. unfold sim_seq_na_step_case in NASTEP.
        hexploit NASTEP; clear NASTEP.
        { eauto. }
        i. des. pclearbot. destruct st1, st_src2. hexploit IHbehavior; clear IHbehavior.
        3: refl. auto.
        { replace state0 with (SeqState.state (SeqState.mk _ state0 memory)). 2: ss. eapply rtc_na_step_receptive.
          { instantiate (1:= (SeqState.mk _ st_tgt m_tgt)). ss. }
          econs. eauto. refl.
        }
        { eauto. }
        i; des. esplits; eauto. eapply na_steps_behavior. 2: eauto. etrans. eauto.
        clear -STEP. inv STEP.
        - econs; eauto.
        - refl.
    }

    1:{ i. clarify; ss.
        punfold SIM. inv SIM.
        2:{ eapply sim_fail_ub; eauto. }
        clear NASTEP ATSTEP PARTIAL. unfold sim_seq_terminal_case in TERMINAL0. ss.
        hexploit TERMINAL0; clear TERMINAL0.
        { eauto. }
        i; des. destruct m_src, st_src1. destruct memory. ss. esplits.
        - eapply na_steps_behavior.
          2:{ econs 1; eauto. }
          eauto.
        - econs 1; eauto.
    }

    2:{ i. clarify; ss.
        punfold SIM. inv SIM.
        2:{ eapply sim_fail_ub; eauto. }
        unfold SeqThread.failure in FAILURE. des. inv FAILURE0.
        clear TERMINAL ATSTEP PARTIAL. unfold sim_seq_na_step_case in NASTEP.
        hexploit NASTEP; clear NASTEP.
        { eauto. }
        i. des. pclearbot. inv STEP0.
        esplits.
        - eapply na_steps_behavior. eauto.
          destruct st_src1. eapply SeqBehavior.behavior_ub. unfold SeqThread.failure.
          eexists. econs. eauto.
        - econs 3. econs.
    }



  Admitted.


  Theorem simulation_implies_refinement
          (st_src: lang_src.(Language.state)) (st_tgt: lang_tgt.(Language.state))
          (SIM: sim_seq_all _ _ (fun _ _ => True) st_src st_tgt)
          (RECEPTIVE: receptive _ st_tgt) (*maybe not needed*)
    :
      SeqBehavior.refine _ _ st_tgt st_src.
  Proof.
    unfold SeqBehavior.refine. i. eapply simulation_implies_refinement_aux. 2,3: auto.
    unfold sim_seq_all in SIM. eauto.
  Qed.
  (*   (* unfold sim_seq_all in SIM. *) *)
  (*   unfold SeqBehavior.refine. i. *)
  (*   (* specialize SIM with p m. *) *)
  (*   unfold SeqTrace.incl. i. *)
  (*   match goal with | [H: SeqBehavior.behavior _ ?a _ |- _] => remember a as th_tgt0 end. *)
  (*   depgen st_src. depgen st_tgt. depgen o. depgen p. depgen m. *)
  (*   induction H. *)

  (*   4:{ i. clarify; ss. *)
  (*       unfold sim_seq_all in SIM. *)
  (*       specialize SIM with p m. *)
  (*       dup SIM. *)
  (*       punfold SIM. inv SIM. *)
  (*       2:{ eapply sim_fail_ub; eauto. } *)
  (*       inv STEP. *)
  (*       clear TERMINAL ATSTEP. unfold sim_seq_na_step_case in NASTEP. *)
  (*       hexploit NASTEP; clear NASTEP. *)
  (*       { eauto. } *)
  (*       i. des. pclearbot. destruct st1. hexploit IHbehavior; clear IHbehavior. *)
  (*       3: refl. auto. *)
  (*       { replace state0 with (SeqState.state (SeqState.mk _ state0 memory)). 2: ss. eapply rtc_na_step_receptive. *)
  (*         { instantiate (1:= (SeqState.mk _ st_tgt m)). ss. } *)
  (*         econs. eauto. refl. *)
  (*       } *)
  (*       2:{ i; des. esplits; eauto. *)
  (*       {  *)



  (* Admitted. *)

End ADEQUACY2.









Section ADEQUACY.
  Variable lang_src lang_tgt: language.
  Variable state_step:
    Perms.t -> MachineEvent.t -> SeqState.t lang_src -> SeqState.t lang_src -> Prop.

  Definition lang_read_value (lang: language): Prop :=
    (<<READ: forall loc val ord st1 st2 val'
               (STEP: lang.(Language.step) (ProgramEvent.read loc val ord) st1 st2),
        (<<READ': exists st2',
            lang.(Language.step) (ProgramEvent.read loc val' ord) st1 st2'>>) \/
        (<<UPDATE': exists valw ordw st2',
            lang.(Language.step) (ProgramEvent.update loc val' valw ord ordw) st1 st2'>>)>>) /\
    (<<UPDATE: forall loc valr valw ordr ordw st1 st2 valr'
               (STEP: lang.(Language.step) (ProgramEvent.update loc valr valw ordr ordw) st1 st2),
        (<<READ': exists st2',
            lang.(Language.step) (ProgramEvent.read loc valr' ordr) st1 st2'>>) \/
        (<<UPDATE': exists valw' st2',
            lang.(Language.step) (ProgramEvent.update loc valr' valw' ordr ordw) st1 st2'>>)>>).

  Hypothesis lang_read_value_src: lang_read_value lang_src.

  Hypothesis state_step_subset: state_step <4= (@SeqState.na_step _).

  Hypothesis state_step_determ:
    forall p st e0 e1 st0 st1
           (STEP0: state_step p e0 st st0)
           (STEP1: state_step p e1 st st1),
      e0 = e1 /\ st0 = st1.

  Lemma refine_mon
        (st_tgt: lang_tgt.(Language.state)) (st_src: lang_src.(Language.state))
        (REFINE: SeqBehavior.refine _ _ st_tgt st_src)
        (TOP: forall p m o (WF: Oracle.wf o),
            SeqBehavior.behavior (@SeqState.na_step _) (SeqThread.mk (SeqState.mk _ st_src m) p o)
            <1=
            SeqBehavior.behavior state_step (SeqThread.mk (SeqState.mk _ st_src m) p o)):
    forall p m o (WF: Oracle.wf o),
      SeqTrace.incl
        (SeqBehavior.behavior (@SeqState.na_step _) (SeqThread.mk (SeqState.mk _ st_tgt m) p o))
        (SeqBehavior.behavior state_step (SeqThread.mk (SeqState.mk _ st_src m) p o)).
  Proof.
    ii. specialize (TOP p m o WF).
    exploit REFINE; eauto. i. des. eauto.
  Qed.


  (** lemmas on event and event step *)

  Lemma le_is_accessing
        e1 e2
        (LE: ProgramEvent.le e1 e2):
    is_accessing e1 <-> is_accessing e2.
  Proof.
    destruct e1, e2; ss; inv LE; des; subst; ss.
  Qed.

  Lemma le_is_acquire
        e1 e2
        (LE: ProgramEvent.le e1 e2):
    is_acquire e1 <-> is_acquire e2.
  Proof.
    destruct e1, e2; ss; inv LE; des; subst; ss.
  Qed.

  Lemma le_is_release
        e1 e2
        (LE: ProgramEvent.le e1 e2):
    is_release e1 <-> is_release e2.
  Proof.
    destruct e1, e2; ss; inv LE; des; subst; ss.
  Qed.

  Lemma le_is_accessing_loc
        e1 e2
        (LE: ProgramEvent.le e1 e2):
    (exists loc v1 v2,
        is_accessing e1 = Some (loc, v1) /\ is_accessing e2 = Some (loc, v2)) \/
    (is_accessing e1 = None /\ is_accessing e2 = None).
  Proof.
    destruct e1, e2; des; subst; try inv LE; ss; eauto; left; esplits; eauto.
  Qed.

  Lemma similar_is_accessing_loc
        e1 e2
        (SIMILAR: similar e1 e2):
    (exists loc v1 v2,
        is_accessing e1 = Some (loc, v1) /\ is_accessing e2 = Some (loc, v2)) \/
    (is_accessing e1 = None /\ is_accessing e2 = None).
  Proof.
    destruct e1, e2; des; subst; try inv SIMILAR; ss; eauto; left; esplits; eauto.
  Qed.

  Lemma wsimilar_is_accessing_loc
        e1 e2
        (WSIMILAR: wsimilar e1 e2):
    (exists loc v1 v2,
        is_accessing e1 = Some (loc, v1) /\ is_accessing e2 = Some (loc, v2)) \/
    (is_accessing e1 = None /\ is_accessing e2 = None).
  Proof.
    destruct e1, e2; des; subst; try inv WSIMILAR; ss; eauto; left; esplits; eauto.
  Qed.

  Lemma wsimilar_is_acquire
        e1 e2
        (WSIMILAR: wsimilar e1 e2):
    is_acquire e1 <-> is_acquire e2.
  Proof.
    destruct e1, e2; des; subst; try inv WSIMILAR; ss. des. subst. ss.
  Qed.

  Lemma le_wf_output
        e1 e2 o
        (LE: ProgramEvent.le e1 e2):
    Oracle.wf_output e1 o <-> Oracle.wf_output e2 o.
  Proof.
    unfold Oracle.wf_output. unnw.
    erewrite le_is_accessing, le_is_acquire, le_is_release; eauto.
  Qed.

  Lemma event_step_update_exists
        e (o: option Perm.t) p1 m1
        (WF_OUTPUT: o <-> is_accessing e):
    exists i,
      (<<WF: forall loc v_new,
          ((exists v_old f_old, i = Some (loc, v_old, f_old, v_new)) <->
           (is_accessing e = Some (loc, v_new)))>>) /\
      exists p2 m2, (<<STEP: SeqEvent.step_update i o p1 m1 p2 m2>>).
  Proof.
    exists (match is_accessing e with
       | Some (loc, v_new) =>
         Some (loc, m1.(SeqMemory.value_map) loc, m1.(SeqMemory.flags) loc, v_new)
       | None => None
       end).
    split.
    { split; i; des_ifs; des; ss; eauto. inv H. ss. }
    { des_ifs; destruct o; try by intuition.
      - esplits. econs; eauto. econs.
      - esplits. econs.
    }
  Qed.

  Lemma event_step_acquire_exists
        e (o: option (Perms.t * ValueMap.t)) p1 m1
        (WF_OUTPUT: o <-> is_acquire e):
    exists (i: option Flags.t),
      (<<WF: i <-> is_acquire e>>) /\
      exists p2 m2, (<<STEP: SeqEvent.step_acquire i o p1 m1 p2 m2>>).
  Proof.
    exists (if is_acquire e then Some m1.(SeqMemory.flags) else None).
    split.
    { split; i; des_ifs; des; ss; eauto. }
    { des_ifs; destruct o as [[]|]; try by intuition.
      - esplits. econs; eauto. econs.
      - esplits. econs.
    }
  Qed.

  Lemma event_step_release_exists
        e (o: option Perms.t) p1 m1
        (WF_OUTPUT: o <-> is_release e):
    exists (i: option (ValueMap.t * Flags.t)),
      (<<WF: i <-> is_release e>>) /\
      exists p2 m2, (<<STEP: SeqEvent.step_release i o p1 m1 p2 m2>>).
  Proof.
    exists (if is_release e then Some (m1.(SeqMemory.value_map), m1.(SeqMemory.flags)) else None).
    split.
    { split; i; des_ifs; des; ss; eauto. }
    { des_ifs; destruct o; try by intuition.
      - esplits. econs; eauto. econs.
      - esplits. econs.
    }
  Qed.

  Lemma event_step_exists
        e o p1 m1
        (WF_OUTPUT: Oracle.wf_output e o):
    exists i,
      (<<WF: SeqEvent.wf_input e i>>) /\
      exists p2 m2,
        (<<STEP: SeqEvent.step i o p1 m1 p2 m2>>).
  Proof.
    unfold Oracle.wf_output in *. destruct o. ss. splitsH.
    exploit (event_step_update_exists e out_access p1 m1); ss. i. des.
    exploit (event_step_acquire_exists e out_acquire p2 m2); ss. i. des.
    exploit (event_step_release_exists e out_release p0 m0); ss. i. des.
    exists (SeqEvent.mk_input i i0 i1). split.
    - unfold SeqEvent.wf_input. splits; ss.
    - esplits. econs; eauto.
  Qed.


  (** definitions and lemmas on match_trace *)

  Variant min_match (I: Type) (imatch: forall (d1 d2: Flags.t) (i_src i_tgt: I), Prop)
          (d1 d2: Flags.t) (i_src i_tgt: I): Prop :=
  | min_match_intro
      (MATCH: imatch d1 d2 i_src i_tgt)
      (MIN: forall d (MATCH: imatch d1 d i_src i_tgt), Flags.le d2 d)
  .

  Lemma min_access_match_exists
        d1 d2 i_src i_tgt
        (MATCH: SeqEvent.in_access_match d1 d2 i_src i_tgt):
    exists d_min, min_match SeqEvent.in_access_match d1 d_min i_src i_tgt.
  Proof.
    i. inv MATCH.
    { exists d1. econs; [econs 1; refl|]. i. inv MATCH. ss. }
    exists (fun loc => if Loc.eq_dec loc l then false else (d1 loc)).
    econs.
    - econs; eauto. i. condtac; ss. refl.
    - i. inv MATCH. ii. condtac; ss. eauto.
  Qed.

  Lemma min_acquire_match_exists
        d1 d2 i_src i_tgt
        (MATCH: SeqEvent.in_acquire_match d1 d2 i_src i_tgt):
    exists d_min, min_match SeqEvent.in_acquire_match d1 d_min i_src i_tgt.
  Proof.
    inv MATCH.
    { exists d1. econs; [econs 1; refl|]. i. inv MATCH. ss. }
    exists Flags.bot. econs; ss. econs; eauto.
  Qed.

  Lemma min_release_match_exists
        d1 d2 i_src i_tgt
        (MATCH: SeqEvent.in_release_match d1 d2 i_src i_tgt):
    exists d_min, min_match SeqEvent.in_release_match d1 d_min i_src i_tgt.
  Proof.
    inv MATCH.
    { exists d1. econs; [econs 1; refl|]. i. inv MATCH. ss. }
    exists (fun loc => if Const.le (v_tgt loc) (v_src loc)
               then andb (orb (f_tgt loc) (d1 loc)) (negb (f_src loc))
               else true).
    econs; ii.
    - econs; ii; des_ifs.
      unfold Flags.join. condtac; ss.
      + destruct (f_tgt loc), (d1 loc), (f_src loc); ss.
      + destruct (f_tgt loc), (d1 loc), (f_src loc); ss.
    - inv MATCH. condtac; ss.
      + specialize (DEFERRED0 loc). unfold Flags.join in *.
        destruct (f_tgt loc), (d1 loc), (f_src loc), (d loc); ss.
      + specialize (VAL0 loc). destruct (d loc); ss.
        exploit VAL0; eauto. i. congr.
  Qed.

  Lemma min_match_le_min
        I imatch d1 d2 i_src i_tgt
        (MIN: @min_match I imatch d1 d2 i_src i_tgt)
        (MON: forall d1 d2 d1' d2' i_src i_tgt
                (MATCH: imatch d1 d2 i_src i_tgt)
                (LE1: Flags.le d1' d1)
                (LE2: Flags.le d2 d2'),
            imatch d1' d2' i_src i_tgt)
        d1' d2'
        (MATCH: imatch d1' d2' i_src i_tgt)
        (LE: Flags.le d1 d1'):
    Flags.le d2 d2'.
  Proof.
    exploit MON; try exact MATCH; try exact LE; try refl. i.
    inv MIN. eapply MIN0; eauto.
  Qed.

  Lemma min_input_match_exists
        d1 d2 i_src i_tgt
        (MATCH: SeqEvent.input_match d1 d2 i_src i_tgt):
    exists d_min, (<<MIN: min_match SeqEvent.input_match d1 d_min i_src i_tgt>>).
  Proof.
    inv MATCH.
    exploit min_access_match_exists; eauto. intro MIN_ACCESS. des.
    hexploit min_match_le_min; try exact MIN_ACCESS; try exact ACCESS;
      eauto using SeqEvent.in_access_match_mon; try refl. i.
    exploit SeqEvent.in_acquire_match_mon; try exact ACQUIRE; try exact H; try refl. i.
    exploit min_acquire_match_exists; try exact x0. intro MIN_ACQUIRE. des.
    hexploit min_match_le_min; try exact MIN_ACQUIRE; try exact ACQUIRE;
      eauto using SeqEvent.in_acquire_match_mon. i.
    exploit SeqEvent.in_release_match_mon; try exact RELEASE; try exact H0; try refl. i.
    exploit min_release_match_exists; try exact x1. intro MIN_RELEASE. des.
    clear d0 d2 d3 ACCESS ACQUIRE RELEASE H x0 H0 x1.
    exists d_min1. econs.
    { econs; [apply MIN_ACCESS|apply MIN_ACQUIRE|apply MIN_RELEASE]. }
    i. inv MATCH.
    hexploit min_match_le_min; try exact MIN_ACCESS; try exact ACCESS;
      eauto using SeqEvent.in_access_match_mon; try refl. i.
    hexploit min_match_le_min; try exact MIN_ACQUIRE; try exact ACQUIRE;
      eauto using SeqEvent.in_acquire_match_mon. i.
    hexploit min_match_le_min; try exact MIN_RELEASE; try exact RELEASE;
      eauto using SeqEvent.in_release_match_mon.
  Qed.

  Inductive match_trace (imatch: forall (d1 d2: Flags.t) (i_src i_tgt: SeqEvent.input), Prop):
    forall (d_init: Flags.t) (d: Flags.t) (tr_src tr_tgt: list (ProgramEvent.t * SeqEvent.input * Oracle.output)), Prop :=
  | match_trace_nil
      d:
      match_trace imatch d d [] []
  | match_trace_snoc
      d_init d1 tr_src tr_tgt d2
      e_src i_src o_src
      e_tgt i_tgt o_tgt
      (MATCH: match_trace imatch d_init d1 tr_src tr_tgt)
      (EVENT: ProgramEvent.le e_tgt e_src)
      (INPUT: imatch d1 d2 i_src i_tgt)
      (OUTPUT: o_src = o_tgt):
      match_trace imatch d_init d2 (tr_src ++ [(e_src, i_src, o_src)]) (tr_tgt ++ [(e_tgt, i_tgt, o_tgt)])
  .

  Variant simple_match_event: forall e_src e_tgt, Prop :=
  | simple_match_event_intro
      e_src i_src (o: Oracle.output)
      e_tgt i_tgt
      (EVENT: ProgramEvent.le e_tgt e_src)
      (INPUT: oracle_similar_input (SeqEvent.get_oracle_input i_src) (SeqEvent.get_oracle_input i_tgt)):
      simple_match_event (e_src, i_src, o) (e_tgt, i_tgt, o)
  .

  Program Instance simple_match_event_PreOrder: PreOrder simple_match_event.
  Next Obligation.
    ii. destruct x as [[]]. econs; refl.
  Qed.
  Next Obligation.
    ii. inv H. inv H0. econs; etrans; eauto.
  Qed.

  Lemma match_trace_simple_match
        d_init d tr_src tr_tgt
        (TRACE: match_trace (min_match SeqEvent.input_match) d_init d tr_src tr_tgt):
    Forall2 simple_match_event tr_src tr_tgt.
  Proof.
    induction TRACE; eauto. subst.
    apply Forall2_app; ss. econs; ss. econs; eauto.
    eapply input_match_similar. eapply INPUT.
  Qed.

  Lemma simple_match_follows1
        orc0 tr1 tr2 orc
        (MATCH: Forall2 simple_match_event tr1 tr2)
        (FOLLOWS: oracle_follows_trace orc0 tr1 orc):
    oracle_follows_trace orc0 tr2 orc.
  Proof.
    revert orc FOLLOWS. induction MATCH; i; eauto. inv H.
    inv FOLLOWS. econs; i.
    - exploit SOUND; try exact STEP. i. des. split.
      + destruct e_src, e_tgt; ss; inv EVENT; des; subst; ss.
      + i. exploit x0; try by (etrans; eauto). i. des. splits; auto.
    - eapply COMPLETE; eauto; try by etrans; eauto.
      destruct e_src, e_tgt; ss; inv EVENT; des; subst; ss.
  Qed.

  Lemma simple_match_follows2
        orc0 tr1 tr2 orc
        (MATCH: Forall2 simple_match_event tr1 tr2)
        (FOLLOWS: oracle_follows_trace orc0 tr2 orc):
    oracle_follows_trace orc0 tr1 orc.
  Proof.
    revert orc FOLLOWS. induction MATCH; i; eauto. inv H.
    inv FOLLOWS. econs; i.
    - exploit SOUND; try exact STEP. i. des. split.
      + destruct e_src, e_tgt; ss; inv EVENT; des; subst; ss.
      + i. exploit x0.
        { etrans; eauto. symmetry. ss. }
        i. des. splits; auto.
    - eapply COMPLETE; eauto.
      + destruct e_src, e_tgt; ss; inv EVENT; des; subst; ss.
      + etrans; eauto. symmetry. ss.
  Qed.

  Lemma match_trace_cons
        imatch d1 d2 tr_src tr_tgt
        d0 e_src i_src o_src e_tgt i_tgt o_tgt
        (TRACE: match_trace imatch d1 d2 tr_src tr_tgt)
        (EVENT: ProgramEvent.le e_tgt e_src)
        (INPUT: imatch d0 d1 i_src i_tgt)
        (OUTPUT: o_src = o_tgt):
    match_trace imatch d0 d2 ((e_src, i_src, o_src) :: tr_src) ((e_tgt, i_tgt, o_tgt) :: tr_tgt).
  Proof.
    induction TRACE.
    { replace [(e_src, i_src, o_src)] with ([] ++ [(e_src, i_src, o_src)]) by ss.
      replace [(e_tgt, i_tgt, o_tgt)] with ([] ++ [(e_tgt, i_tgt, o_tgt)]) by ss.
      econs 2; eauto. econs.
    }
    exploit IHTRACE; eauto. i.
    replace ((e_src, i_src, o_src) :: tr_src ++ [(e_src0, i_src0, o_src0)]) with
      (((e_src, i_src, o_src) :: tr_src) ++ [(e_src0, i_src0, o_src0)]) by ss.
    replace ((e_tgt, i_tgt, o_tgt) :: tr_tgt ++ [(e_tgt0, i_tgt0, o_tgt0)]) with
      (((e_tgt, i_tgt, o_tgt) :: tr_tgt) ++ [(e_tgt0, i_tgt0, o_tgt0)]) by ss.
    econs 2; eauto.
  Qed.

  Lemma trace_le_terminal_match
        d_init tr_src v_src f_src tr_tgt v_tgt f_tgt
        (LE: SeqTrace.le d_init
                         (tr_tgt, SeqTrace.term v_tgt f_tgt)
                         (tr_src, SeqTrace.term v_src f_src)):
    exists d,
      (<<MATCH: match_trace SeqEvent.input_match d_init d tr_src tr_tgt>>) /\
      (<<FLAGS: Flags.le (Flags.join d f_tgt) (f_src)>>).
  Proof.
    remember (tr_src, SeqTrace.term v_src f_src) as r_src.
    remember (tr_tgt, SeqTrace.term v_tgt f_tgt) as r_tgt.
    revert tr_src v_src f_src tr_tgt v_tgt f_tgt Heqr_src Heqr_tgt.
    induction LE; i; subst; ss.
    { inv Heqr_src. inv Heqr_tgt. esplits; eauto. econs 1. }
    inv Heqr_src. inv Heqr_tgt.
    exploit IHLE; eauto. i. des. clear IHLE.
    esplits; eauto.
    eapply match_trace_cons; eauto.
  Qed.

  Lemma trace_le_partial_match
        P d_init tr_src tr_src_ex f_src tr_tgt f_tgt
        (TRACE: Forall2 P tr_src tr_tgt)
        (LE: SeqTrace.le d_init
                         (tr_tgt, SeqTrace.partial f_tgt)
                         (tr_src ++ tr_src_ex, SeqTrace.partial f_src)):
    exists d w,
      (<<MATCH: match_trace SeqEvent.input_match d_init d tr_src tr_tgt>>) /\
      (<<WRITING: SeqThread.writing_trace tr_src_ex w>>) /\
      (<<FLAGS: Flags.le (Flags.join d f_tgt) (Flags.join w f_src)>>).
  Proof.
    remember (tr_src ++ tr_src_ex, SeqTrace.partial f_src) as r_src.
    remember (tr_tgt, SeqTrace.partial f_tgt) as r_tgt.
    revert tr_src tr_src_ex f_src tr_tgt f_tgt Heqr_src Heqr_tgt TRACE.
    induction LE; i; subst; ss.
    { inv Heqr_src. inv Heqr_tgt. inv TRACE0. ss.
      esplits; [econs 1|..]; eauto.
    }
    inv Heqr_src. inv Heqr_tgt. inv TRACE. inv H0.
    exploit IHLE; eauto. i. des. clear IHLE.
    esplits; eauto.
    eapply match_trace_cons; eauto.
  Qed.

  Lemma trace_le_partial_step_match
        P d_init tr_src e_src i_src o tr_src_ex f_src tr_tgt e_tgt i_tgt f_tgt
        (TRACE: Forall2 P tr_src tr_tgt)
        (LE: SeqTrace.le d_init
                         (tr_tgt ++ [(e_tgt, i_tgt, o)], SeqTrace.partial f_tgt)
                         (tr_src ++ [(e_src, i_src, o)] ++ tr_src_ex, SeqTrace.partial f_src)):
    exists d1 d2,
      (<<MATCH: match_trace SeqEvent.input_match d_init d1 tr_src tr_tgt>>) /\
      (<<EVENT: ProgramEvent.le e_tgt e_src>>) /\
      (<<INPUT_MATCH: SeqEvent.input_match d1 d2 i_src i_tgt>>).
  Proof.
    remember (tr_src ++ [(e_src, i_src, o)] ++ tr_src_ex, SeqTrace.partial f_src) as r_src.
    remember (tr_tgt ++ [(e_tgt, i_tgt, o)], SeqTrace.partial f_tgt) as r_tgt.
    revert tr_src e_src i_src o tr_src_ex f_src tr_tgt e_tgt i_tgt f_tgt TRACE Heqr_src Heqr_tgt.
    induction LE; i; subst; ss.
    { inv Heqr_src. inv Heqr_tgt. destruct tr_tgt; ss. }
    inv TRACE; ss.
    { inv Heqr_src. inv Heqr_tgt. esplits; eauto. econs. }
    inv Heqr_src. inv Heqr_tgt.
    exploit IHLE; eauto. i. des. clear IHLE.
    esplits; eauto.
    eapply match_trace_cons; eauto.
  Qed.

  Lemma writing_trace_no_acquire
        tr w
        (WRITING: SeqThread.writing_trace tr w):
    forall e i o (IN: List.In (e, i, o) tr), ~ is_acquire e.
  Proof.
    induction WRITING; ss. i. inv IN; eauto. inv H. eauto.
  Qed.

  Lemma trace_le_ub_acquire_match
        P d_init tr_src e_src i_src o tr_src_ex tr_tgt e_tgt i_tgt res_tgt
        (TRACE: Forall2 P tr_src tr_tgt)
        (ACQUIRE: is_acquire e_src)
        (LE: SeqTrace.le d_init
                         (tr_tgt ++ [(e_tgt, i_tgt, o)], res_tgt)
                         (tr_src ++ [(e_src, i_src, o)] ++ tr_src_ex, SeqTrace.ub)):
    exists d1 d2,
      (<<MATCH: match_trace SeqEvent.input_match d_init d1 tr_src tr_tgt>>) /\
      (<<EVENT: ProgramEvent.le e_tgt e_src>>) /\
      (<<INPUT_MATCH: SeqEvent.input_match d1 d2 i_src i_tgt>>).
  Proof.
    remember (tr_src ++ [(e_src, i_src, o)] ++ tr_src_ex, SeqTrace.ub) as r_src.
    remember (tr_tgt ++ [(e_tgt, i_tgt, o)], res_tgt) as r_tgt.
    revert tr_src e_src i_src o tr_src_ex tr_tgt e_tgt i_tgt res_tgt TRACE ACQUIRE Heqr_src Heqr_tgt.
    induction LE; i; subst; ss.
    { inv Heqr_src.
      hexploit writing_trace_no_acquire; eauto.
      { rewrite in_app_iff. right. econs 1. eauto. }
      i. ss.
    }
    inv TRACE; ss.
    { inv Heqr_src. inv Heqr_tgt. esplits; eauto. econs. }
    inv Heqr_src. inv Heqr_tgt.
    exploit IHLE; eauto. i. des. clear IHLE.
    esplits; eauto.
    eapply match_trace_cons; eauto.
  Qed.

  Lemma writing_trace_app
        l1 l2 w
        (WRITING: SeqThread.writing_trace (l1 ++ l2) w):
    exists w',
      Flags.le w' w /\
      SeqThread.writing_trace l2 w'.
  Proof.
    revert l2 w WRITING. induction l1; ss; i.
    { esplits; eauto. refl. }
    inv WRITING. exploit IHl1; eauto. i. des.
    esplits; eauto. etrans; eauto. apply Flags.join_ge_r.
  Qed.

  Lemma trace_le_ub_match
        P d_init tr_tgt r_tgt tr_src tr
        (TRACE: Forall2 P tr_src tr_tgt)
        (LE: SeqTrace.le d_init (tr_tgt, r_tgt) (tr_src ++ tr, SeqTrace.ub)):
    exists w, SeqThread.writing_trace tr w.
  Proof.
    revert d_init LE. induction TRACE; i.
    { inv LE. eauto. }
    inv LE; eauto.
    replace (x :: l ++ tr) with ((x :: l) ++ tr) in * by ss.
    exploit writing_trace_app; eauto. i. des. eauto.
  Qed.

  Lemma trace_le_ub_step_match
        P d_init tr_tgt e i o r_tgt tr_src tr
        (TRACE: Forall2 P tr_src tr_tgt)
        (LE: SeqTrace.le d_init (tr_tgt ++ [(e, i, o)], r_tgt) (tr_src ++ tr, SeqTrace.ub)):
    (exists w, SeqThread.writing_trace tr w) \/
    (exists e_src i_src tr' d1 d2,
        (<<MATCH: match_trace SeqEvent.input_match d_init d1 tr_src tr_tgt>>) /\
        (<<TRACE: tr = (e_src, i_src, o) :: tr'>>) /\
        (<<EVENT: ProgramEvent.le e e_src>>) /\
        (<<INPUT: SeqEvent.input_match d1 d2 i_src i>>)).
  Proof.
    revert d_init LE. induction TRACE; ss; i.
    { inv LE; eauto. right. esplits; eauto. econs. }
    inv LE.
    - replace (x :: l ++ tr) with ((x :: l) ++ tr) in * by ss.
      exploit writing_trace_app; eauto. i. des. eauto.
    - exploit IHTRACE; eauto. i. des; eauto. subst.
      right. esplits; eauto.
      eapply match_trace_cons; eauto.
  Qed.

  Lemma last_eq_inv
        A l1 l2 (a1 a2: A)
        (EQ: l1 ++ [a1] = l2 ++ [a2]):
    l1 = l2 /\ a1 = a2.
  Proof.
    split.
    - erewrite <- (removelast_last l1 a1).
      erewrite <- (removelast_last l2 a2).
      congr.
    - erewrite <- (last_last l1 a1 a1).
      erewrite <- (last_last l2 a2 a1).
      congr.
  Qed.

  Lemma min_match_trace_min
        d_init d_min d tr_src tr_tgt
        (MIN_TRACE: match_trace (min_match SeqEvent.input_match) d_init d_min tr_src tr_tgt)
        (TRACE: match_trace SeqEvent.input_match d_init d tr_src tr_tgt):
    Flags.le d_min d.
  Proof.
    revert d TRACE. induction MIN_TRACE; i.
    { inv TRACE; try refl. destruct tr_src; ss. }
    inv TRACE.
    { destruct tr_src; ss. }
    apply last_eq_inv in H2, H3. des. inv H1. inv H0.
    hexploit IHMIN_TRACE; eauto. i.
    eapply min_match_le_min; eauto using SeqEvent.input_match_mon.
  Qed.

  Lemma match_trace_le_terminal
        d tr_src v_src f_src tr_tgt v_tgt f_tgt
        (MIN_TRACE: match_trace (min_match SeqEvent.input_match) Flags.bot d tr_src tr_tgt)
        (LE: SeqTrace.le Flags.bot
                         (tr_tgt, SeqTrace.term v_tgt f_tgt)
                         (tr_src, SeqTrace.term v_src f_src)):
    Flags.le (Flags.join d f_tgt) f_src.
  Proof.
    exploit trace_le_terminal_match; eauto. i. des.
    hexploit min_match_trace_min; eauto. i.
    etrans; eauto.
    apply Flags.join_mon_l; auto.
  Qed.

  Lemma match_trace_le_partial
        d
        tr_src tr_src_ex f_src
        tr_tgt f_tgt
        (MIN_TRACE: match_trace (min_match SeqEvent.input_match) Flags.bot d tr_src tr_tgt)
        (LE: SeqTrace.le Flags.bot
                         (tr_tgt, SeqTrace.partial f_tgt)
                         (tr_src ++ tr_src_ex, SeqTrace.partial f_src)):
    exists w,
      (<<WRITING: SeqThread.writing_trace tr_src_ex w>>) /\
      (<<FLAGS: Flags.le (Flags.join d f_tgt) (Flags.join w f_src)>>).
  Proof.
    exploit trace_le_partial_match; try exact LE.
    { eapply match_trace_simple_match; eauto. }
    i. des. esplits; eauto.
    etrans; eauto. apply Flags.join_mon_l.
    eapply min_match_trace_min; eauto.
  Qed.

  Lemma match_trace_le_partial_step
        d
        tr_src e_src i_src o tr_src_ex f_src
        tr_tgt e_tgt i_tgt f_tgt
        (MIN_TRACE: match_trace (min_match SeqEvent.input_match) Flags.bot d tr_src tr_tgt)
        (LE: SeqTrace.le Flags.bot
                         (tr_tgt ++ [(e_tgt, i_tgt, o)], SeqTrace.partial f_tgt)
                         (tr_src ++ [(e_src, i_src, o)] ++ tr_src_ex, SeqTrace.partial f_src)):
    exists d1 d2,
      (<<EVENT: ProgramEvent.le e_tgt e_src>>) /\
      (<<INPUT_MATCH: SeqEvent.input_match d1 d2 i_src i_tgt>>) /\
      (<<MIN: Flags.le d d1>>).
  Proof.
    exploit trace_le_partial_step_match; try exact LE.
    { eapply match_trace_simple_match; eauto. }
    i. des. esplits; eauto.
    eapply min_match_trace_min; eauto.
  Qed.

  Lemma match_trace_le_ub_acquire
        d
        tr_src e_src i_src o tr_src_ex
        tr_tgt e_tgt i_tgt f_tgt
        (MIN_TRACE: match_trace (min_match SeqEvent.input_match) Flags.bot d tr_src tr_tgt)
        (ACQUIRE: is_acquire e_src)
        (LE: SeqTrace.le Flags.bot
                         (tr_tgt ++ [(e_tgt, i_tgt, o)], SeqTrace.partial f_tgt)
                         (tr_src ++ [(e_src, i_src, o)] ++ tr_src_ex, SeqTrace.ub)):
    exists d1 d2,
      (<<EVENT: ProgramEvent.le e_tgt e_src>>) /\
      (<<INPUT_MATCH: SeqEvent.input_match d1 d2 i_src i_tgt>>) /\
      (<<MIN: Flags.le d d1>>).
  Proof.
    exploit trace_le_ub_acquire_match; try exact LE; eauto.
    { eapply match_trace_simple_match; eauto. }
    i. des. esplits; eauto.
    eapply min_match_trace_min; eauto.
  Qed.


  (** definitions and lemmas on state_steps *)

  Inductive state_steps (lang: language)
                        (step: forall (p: Perms.t) (e: MachineEvent.t) (st1 st2: SeqState.t lang), Prop):
    forall (tr: list (ProgramEvent.t * SeqEvent.input * Oracle.output))
      (st1 st2: SeqState.t lang) (p1 p2: Perms.t), Prop :=
  | state_steps_refl
      st p:
      state_steps step [] st st p p
  | state_steps_at_step
      e i o st1 st2 st3 p1 p3
      tr st4 p4
      (NASTEPS: rtc (step p1 MachineEvent.silent) st1 st2)
      (LSTEP: lang.(Language.step) e st2.(SeqState.state) st3.(SeqState.state))
      (ATOMIC: is_atomic_event e)
      (INPUT: SeqEvent.wf_input e i)
      (ESTEP: SeqEvent.step i o p1 st2.(SeqState.memory) p3 st3.(SeqState.memory))
      (STEPS: state_steps step tr st3 st4 p3 p4):
      state_steps step ((e, i, o)::tr) st1 st4 p1 p4
  .

  Lemma state_steps_last
        lang step tr (st1 st2: SeqState.t lang) p1 p2
        e i o st3 st4 p4 m4
        (STEPS: state_steps step tr st1 st2 p1 p2)
        (NASTEPS: rtc (step p2 MachineEvent.silent) st2 st3)
        (LSTEP: lang.(Language.step) e st3.(SeqState.state) st4)
        (ATOMIC: is_atomic_event e)
        (INPUT: SeqEvent.wf_input e i)
        (ESTEP: SeqEvent.step i o p2 st3.(SeqState.memory) p4 m4):
    state_steps step (tr ++ [(e, i, o)]) st1 (SeqState.mk _ st4 m4) p1 p4.
  Proof.
    dependent induction STEPS; ss.
    { econs 2; eauto.
      - instantiate (1:=(SeqState.mk _ st4 m4)). ss.
      - eauto.
      - econs.
    }
    exploit IHSTEPS; eauto. i.
    econs 2; try exact x; eauto.
  Qed.

  Lemma na_steps_behavior
        lang (step: Perms.t -> MachineEvent.t -> SeqState.t lang -> SeqState.t lang -> Prop)
        (st1 st2: SeqState.t lang) p orc tr
        (STEPS: rtc (step p MachineEvent.silent) st1 st2)
        (BEH: SeqBehavior.behavior step (SeqThread.mk st2 p orc) tr):
    SeqBehavior.behavior step (SeqThread.mk st1 p orc) tr.
  Proof.
    induction STEPS; ss.
    econs 4; try eapply IHSTEPS; eauto.
    econs. ss.
  Qed.

  Lemma steps_behavior_terminal
        lang step orc0 tr (st0 st1 st2: SeqState.t lang) p0 p1 orc
        (STEPS: state_steps step tr st0 st1 p0 p1)
        (NASTEPS: rtc (step p1 MachineEvent.silent) st1 st2)
        (TERMINAL: lang.(Language.is_terminal) st2.(SeqState.state))
        (ORACLE: oracle_follows_trace orc0 tr orc):
    SeqBehavior.behavior step
                         (SeqThread.mk st0 p0 orc)
                         (tr, SeqTrace.term st2.(SeqState.memory).(SeqMemory.value_map) st2.(SeqState.memory).(SeqMemory.flags)).
  Proof.
    revert orc ORACLE. induction STEPS; i.
    - eapply na_steps_behavior; eauto.
      destruct st2, memory. ss. econs 1; eauto.
    - eapply na_steps_behavior; eauto.
      inv ORACLE. exploit COMPLETE; try refl.
      { eapply wf_input_oracle_wf_input; eauto. }
      i. des. exploit SOUND; eauto. i. des. exploit x0; try refl. i. des.
      econs 5; try eapply IHSTEPS; try eapply FOLLOWS; eauto.
      destruct st0, st3. econs; eauto; try refl.
  Qed.

  Lemma steps_behavior_partial
        lang step orc0 tr (st0 st1 st2: SeqState.t lang) p0 p1 orc
        (STEPS: state_steps step tr st0 st1 p0 p1)
        (NASTEPS: rtc (step p1 MachineEvent.silent) st1 st2)
        (ORACLE: oracle_follows_trace orc0 tr orc):
    SeqBehavior.behavior step
                         (SeqThread.mk st0 p0 orc)
                         (tr, SeqTrace.partial st2.(SeqState.memory).(SeqMemory.flags)).
  Proof.
    revert orc ORACLE. induction STEPS; i.
    - eapply na_steps_behavior; eauto.
      destruct st2, memory. ss. econs 2; eauto.
    - eapply na_steps_behavior; eauto.
      inv ORACLE. exploit COMPLETE; try refl.
      { eapply wf_input_oracle_wf_input; eauto. }
      i. des. exploit SOUND; eauto. i. des. exploit x0; try refl. i. des.
      econs 5; try eapply IHSTEPS; try eapply FOLLOWS; eauto.
      destruct st0, st3. econs; eauto; try refl.
  Qed.

  Lemma steps_behavior_ub
        lang step orc0 tr (st0 st1 st2 st3: SeqState.t lang) p0 p1 orc
        (STEPS: state_steps step tr st0 st1 p0 p1)
        (NASTEPS: rtc (step p1 MachineEvent.silent) st1 st2)
        (FAILURE: step p1 MachineEvent.failure st2 st3)
        (ORACLE: oracle_follows_trace orc0 tr orc):
    SeqBehavior.behavior step (SeqThread.mk st0 p0 orc) (tr, SeqTrace.ub).
  Proof.
    revert orc ORACLE. induction STEPS; i.
    - eapply na_steps_behavior; eauto.
      destruct st2. econs 3; eauto. econs. econs. eauto.
    - eapply na_steps_behavior; eauto.
      inv ORACLE. exploit COMPLETE; try refl.
      { eapply wf_input_oracle_wf_input; eauto. }
      i. des. exploit SOUND; eauto. i. des. exploit x0; try refl. i. des.
      econs 5; try eapply IHSTEPS; try eapply FOLLOWS; eauto.
      destruct st0, st4. econs; eauto; try refl.
  Qed.

  Lemma event_step_oracle_input
        e ie o p1 m1 p2 m2
        (WF: SeqEvent.wf_input e ie)
        (STEP: SeqEvent.step ie o p1 m1 p2 m2):
    SeqEvent.get_oracle_input ie = oracle_input_of_event e m1.
  Proof.
    destruct ie. inv STEP; ss.
    unfold SeqEvent.wf_input, SeqEvent.get_oracle_input, oracle_input_of_event in *.
    ss. splitsH.
    repeat f_equal.
    - inv UPD; ss; des_ifs; ss.
      + specialize (H t t0). des. exploit H5; eauto. i. des. ss.
      + specialize (H t t0). des. exploit H5; eauto. i. des. inv x.
        inv MEM. ss.
      + specialize (H loc v_new). des. exploit H; eauto. i. ss.
    - inv ACQ; ss; condtac; ss; intuition.
    - inv REL; ss; condtac; ss; intuition.
  Qed.

  Lemma steps_behavior_at_step
        lang step orc0 tr (st0 st1 st2: SeqState.t lang) p0 p1 orc
        e i o st3 p3 m3
        (STEPS: state_steps step tr st0 st1 p0 p1)
        (NASTEPS: rtc (step p1 MachineEvent.silent) st1 st2)
        (ATSTEP: lang.(Language.step) e st2.(SeqState.state) st3)
        (ESTEP: SeqEvent.step i o p1 st2.(SeqState.memory) p3 m3)
        (ATOMIC: is_atomic_event e)
        (INPUT: SeqEvent.wf_input e i)
        (OUTPUT: Oracle.wf_output e o)
        (ORACLE: oracle_follows_trace (add_oracle e (SeqEvent.get_oracle_input i) o orc0) tr orc):
    SeqBehavior.behavior step (SeqThread.mk st0 p0 orc)
                         (tr ++ [(e, i, o)], SeqTrace.partial m3.(SeqMemory.flags)).
  Proof.
    revert orc ORACLE. induction STEPS; i.
    { destruct st2. ss. destruct m3. ss.
      assert (exists orc', Oracle.step e (SeqEvent.get_oracle_input i) o orc orc').
      { inv ORACLE. punfold LE2. inv LE2.
        exploit LE.
        { econs. econs 1. }
        i. des. esplits; eauto.
      }
      des.
      esplits.
      eapply na_steps_behavior; eauto. econs 5.
      - econs; try refl; eauto.
      - econs 2.
    }
    clear INPUT OUTPUT.
    inv ORACLE. exploit COMPLETE; try refl.
    { eapply wf_input_oracle_wf_input; eauto. }
    i. des. exploit SOUND; eauto. i. des. exploit x0; try refl. i. des.
    exploit IHSTEPS; eauto. i. des. esplits; eauto. ss.
    eapply na_steps_behavior; eauto.
    econs 5; try eapply IHSTEPS; try eapply FOLLOWS; eauto.
    destruct st0, st4. econs; eauto; try refl.
  Qed.

  Lemma steps_behavior_oracle_step
        lang step orc0 tr (st0 st1 st2: SeqState.t lang) p0 p1 orc
        e i o st3 p3 m3 orc1
        (STEPS: state_steps step tr st0 st1 p0 p1)
        (NASTEPS: rtc (step p1 MachineEvent.silent) st1 st2)
        (ATSTEP: lang.(Language.step) e st2.(SeqState.state) st3)
        (ESTEP: SeqEvent.step i o p1 st2.(SeqState.memory) p3 m3)
        (ATOMIC: is_atomic_event e)
        (INPUT: SeqEvent.wf_input e i)
        (OUTPUT: Oracle.wf_output e o)
        (ORACLE: oracle_follows_trace orc0 tr orc)
        (OSTEP: Oracle.step e (SeqEvent.get_oracle_input i) o orc0 orc1):
    SeqBehavior.behavior step (SeqThread.mk st0 p0 orc)
                         (tr ++ [(e, i, o)], SeqTrace.partial m3.(SeqMemory.flags)).
  Proof.
    revert orc ORACLE. induction STEPS; i.
    { destruct st2. ss. destruct m3. ss.
      assert (exists orc', Oracle.step e (SeqEvent.get_oracle_input i) o orc orc').
      { inv ORACLE. punfold LE2. inv LE2.
        exploit LE; eauto. i. des. eauto.
      }
      des.
      esplits.
      eapply na_steps_behavior; eauto. econs 5.
      - econs; try refl; eauto.
      - econs 2.
    }
    clear INPUT OUTPUT.
    inv ORACLE. exploit COMPLETE; try refl.
    { eapply wf_input_oracle_wf_input; eauto. }
    i. des. exploit SOUND; eauto. i. des. exploit x0; try refl. i. des.
    exploit IHSTEPS; eauto. i. des. esplits; eauto. ss.
    eapply na_steps_behavior; eauto.
    econs 5; try eapply IHSTEPS; try eapply FOLLOWS; eauto.
    destruct st0, st4. econs; eauto; try refl.
  Qed.

  Lemma event_step_exists_full e p1 m1:
    exists i o p2 m2,
      (<<WF_INPUT: SeqEvent.wf_input e i>>) /\
      (<<WF_OUTPUT: Oracle.wf_output e o>>) /\
      (<<ESTEP: SeqEvent.step i o p1 m1 p2 m2>>).
  Proof.
    specialize (oracle_input_of_event_wf e m1). i.
    exploit oracle_simple_output_wf; eauto. i.
    exploit event_step_exists; eauto. i. des. esplits; eauto.
  Qed.

  Lemma wf_input_wf_output
        e i o p1 m1 p2 m2
        (STEP: SeqEvent.step i o p1 m1 p2 m2)
        (WF: SeqEvent.wf_input e i):
    Oracle.wf_output e o.
  Proof.
    destruct i, o. inv STEP. ss.
    unfold SeqEvent.wf_input, Oracle.wf_output in *. ss. splitsH.
    apply wf_in_access_some in H.
    splitsH. splits.
    - inv UPD; ss.
    - inv ACQ; ss.
    - inv REL; ss.
  Qed.

  Lemma state_steps_wf_trace
        lang step tr (st1 st2: SeqState.t lang) p1 p2
        (STEPS: state_steps step tr st1 st2 p1 p2):
    wf_trace tr.
  Proof.
    induction STEPS; ss.
    econs; eauto. split; ss.
    eapply wf_input_wf_output; eauto.
  Qed.

  Lemma na_local_step_na_event
        p me pe m1 m2
        (STEP: SeqState.na_local_step p me pe m1 m2):
    ~ is_atomic_event pe.
  Proof.
    ii. inv STEP; ss.
    - destruct ord; ss.
    - destruct ord; ss.
    - unguard. des; destruct ordr, ordw; ss.
  Qed.

  Lemma similar_is_atomic
        e1 e2
        (E1: forall loc valr valw ordr ordw
               (E: e1 = ProgramEvent.update loc valr valw ordr ordw),
            Ordering.le Ordering.plain ordr /\ Ordering.le Ordering.plain ordw)
        (E2: forall loc valr valw ordr ordw
               (E: e2 = ProgramEvent.update loc valr valw ordr ordw),
            Ordering.le Ordering.plain ordr /\ Ordering.le Ordering.plain ordw)
        (SIMILAR: similar e1 e2):
    is_atomic_event e1 <-> is_atomic_event e2.
  Proof.
    destruct e1, e2; ss; des; subst; ss.
    - exploit E2; eauto. i. des.
      destruct ordr, ordw; ss.
    - exploit E1; eauto. i. des.
      destruct ord, ordw; ss.
  Qed.

  Lemma le_is_atomic
        e1 e2
        (LE: ProgramEvent.le e1 e2):
    is_atomic_event e1 <-> is_atomic_event e2.
  Proof.
    destruct e1, e2; ss; des; inv LE; ss.
  Qed.

  Lemma state_step_behavior
        p st1 st2 orc tr r
        (DETERM: deterministic _ st1.(SeqState.state))
        (STEP: state_step p MachineEvent.silent st1 st2)
        (BEH: SeqBehavior.behavior state_step (SeqThread.mk st1 p orc) (tr, r))
        (TRACE: tr <> []):
    SeqBehavior.behavior state_step (SeqThread.mk st2 p orc) (tr, r).
  Proof.
    inv BEH; ss.
    - inv STEP0. exploit state_step_determ; [exact STEP|exact STEP1|]. i. des. subst. ss.
    - inv STEP0. exploit state_step_subset; eauto. i. inv x.
      punfold DETERM. inv DETERM.
      exploit STEP_STEP; [exact LANG|exact LANG0|]. i. des.
      exploit similar_is_atomic; eauto; try by (i; subst; eapply NO_NA_UPDATE; eauto). i.
      rewrite x2 in *.
      exploit na_local_step_na_event; eauto. ss.
  Qed.

  Lemma rtc_state_step_behavior
        p st1 st2 orc tr r
        (DETERM: deterministic _ st1.(SeqState.state))
        (STEP: rtc (state_step p MachineEvent.silent) st1 st2)
        (BEH: SeqBehavior.behavior state_step (SeqThread.mk st1 p orc) (tr, r))
        (TRACE: tr <> []):
    SeqBehavior.behavior state_step (SeqThread.mk st2 p orc) (tr, r).
  Proof.
    revert DETERM BEH. induction STEP; i; ss.
    exploit state_step_behavior; eauto. i.
    apply IHSTEP; eauto.
    exploit state_step_subset; eauto. i. inv x0. s.
    punfold DETERM. inv DETERM. exploit PRESERVE; eauto. i.
    inv x; ss.
  Qed.

  Lemma state_step_behavior_ub
        p st1 st2 orc tr
        (DETERM: deterministic _ st1.(SeqState.state))
        (STEP: state_step p MachineEvent.silent st1 st2)
        (BEH: SeqBehavior.behavior state_step (SeqThread.mk st1 p orc) (tr, SeqTrace.ub)):
    SeqBehavior.behavior state_step (SeqThread.mk st2 p orc) (tr, SeqTrace.ub).
  Proof.
    inv BEH; ss.
    - inv FAILURE. inv H.
      exploit state_step_determ; [exact STEP|exact STEP0|]. i. des. ss.
    - inv STEP0.
      exploit state_step_determ; [exact STEP|exact STEP1|]. i. des. subst. ss.
    - inv STEP0. exploit state_step_subset; eauto. i. inv x.
      punfold DETERM. inv DETERM.
      exploit STEP_STEP; [exact LANG|exact LANG0|]. i. des.
      exploit similar_is_atomic; eauto; try by (i; subst; eapply NO_NA_UPDATE; eauto). i.
      rewrite x2 in *.
      exploit na_local_step_na_event; eauto. ss.
  Qed.

  Lemma rtc_state_step_behavior_ub
        p st1 st2 orc tr
        (DETERM: deterministic _ st1.(SeqState.state))
        (STEP: rtc (state_step p MachineEvent.silent) st1 st2)
        (BEH: SeqBehavior.behavior state_step (SeqThread.mk st1 p orc) (tr, SeqTrace.ub)):
    SeqBehavior.behavior state_step (SeqThread.mk st2 p orc) (tr, SeqTrace.ub).
  Proof.
    revert DETERM BEH. induction STEP; i; ss.
    exploit state_step_behavior_ub; eauto. i.
    apply IHSTEP; eauto.
    exploit state_step_subset; eauto. i. inv x0. s.
    punfold DETERM. inv DETERM. exploit PRESERVE; eauto. i.
    inv x; ss.
  Qed.

  Lemma rtc_na_step_deterministic
        lang p st1 st2
        (DETERM: deterministic _ st1.(SeqState.state))
        (STEPS: rtc (@SeqState.na_step lang p MachineEvent.silent) st1 st2):
    deterministic _ st2.(SeqState.state).
  Proof.
    induction STEPS; ss.
    apply IHSTEPS. inv H. ss.
    eapply step_deterministic; eauto.
  Qed.

  Lemma rtc_state_step_deterministic
        p st1 st2
        (DETERM: deterministic _ st1.(SeqState.state))
        (STEP: rtc (state_step p MachineEvent.silent) st1 st2):
    deterministic _ st2.(SeqState.state).
  Proof.
    induction STEP; ss.
    exploit state_step_subset; eauto. i. inv x0.
    apply IHSTEP. eapply step_deterministic; eauto.
  Qed.

  Lemma state_steps_deterministic
        tr st1 st2 p1 p2
        (DETERM: deterministic _ st1.(SeqState.state))
        (STEP: state_steps state_step tr st1 st2 p1 p2):
    deterministic _ st2.(SeqState.state).
  Proof.
    induction STEP; ss.
    apply IHSTEP. exploit rtc_state_step_deterministic; eauto. i.
    eapply step_deterministic; eauto.
  Qed.

  Lemma rtc_na_step_receptive
        lang p st1 st2
        (RECEPTIVE: receptive _ st1.(SeqState.state))
        (STEPS: rtc (@SeqState.na_step lang p MachineEvent.silent) st1 st2):
    receptive _ st2.(SeqState.state).
  Proof.
    induction STEPS; ss.
    apply IHSTEPS. inv H. ss.
    eapply step_receptive; eauto.
  Qed.

  Lemma state_steps_receptive
        lang tr st1 st2 p1 p2
        (RECEPTIVE: receptive lang st1.(SeqState.state))
        (STEP: state_steps (@SeqState.na_step _) tr st1 st2 p1 p2):
    receptive _ st2.(SeqState.state).
  Proof.
    induction STEP; ss.
    apply IHSTEP. exploit rtc_na_step_receptive; eauto. i.
    eapply step_receptive; eauto.
  Qed.

  Lemma wf_input_in_access
        e i1 i2
        loc1 v_old1 f1 v_new1
        loc2 v_old2 f2 v_new2
        (WF1: SeqEvent.wf_input e i1)
        (WF2: SeqEvent.wf_input e i2)
        (IN1: i1.(SeqEvent.in_access) = Some (loc1, v_old1, f1, v_new1))
        (IN2: i2.(SeqEvent.in_access) = Some (loc2, v_old2, f2, v_new2)):
    loc1 = loc2 /\ v_new1 = v_new2.
  Proof.
    unfold SeqEvent.wf_input in *. des.
    destruct i1, i2. ss. subst.
    specialize (UPDATE0 loc1 v_new1). des. exploit UPDATE0; eauto. i.
    specialize (UPDATE loc2 v_new2). des. exploit UPDATE; eauto. i.
    rewrite x in *. inv x0. ss.
  Qed.

  Lemma wf_input_similar
        e i1 i2
        (WF1: SeqEvent.wf_input e i1)
        (WF2: SeqEvent.wf_input e i2):
    oracle_similar_input (SeqEvent.get_oracle_input i1) (SeqEvent.get_oracle_input i2).
  Proof.
    unfold SeqEvent.wf_input in *. des. destruct i1, i2; ss.
    unfold oracle_similar_input; ss.
    etrans; eauto. repeat rewrite andb_true_iff. splits.
    - destruct (is_accessing e) as [[loc v]|].
      + specialize (UPDATE0 loc v). specialize (UPDATE loc v). des.
        exploit UPDATE2; eauto. i. des. subst.
        exploit UPDATE1; eauto. i. des. subst.
        ss. apply Loc.eqb_refl.
      + destruct in_access as [[[[]]]|].
        { specialize (UPDATE0 t t2). des. exploit UPDATE0; eauto. ss. }
        destruct in_access0 as [[[[]]]|].
        { specialize (UPDATE t t2). des. exploit UPDATE; eauto. ss. }
        ss.
    - destruct in_acquire, in_acquire0; eauto.
    - destruct in_release, in_release0; eauto.
  Qed.

  Lemma behavior_steps_partial
        lang step (th1: SeqThread.t lang) tr f
        (BEH: SeqBehavior.behavior step th1 (tr, SeqTrace.partial f)):
    exists th2,
      (<<STEPS: SeqThread.steps step tr th1 th2>>) /\
      (<<FAILURE: f = th2.(SeqThread.state).(SeqState.memory).(SeqMemory.flags)>>).
  Proof.
    remember (tr, SeqTrace.partial f) as r.
    revert tr f Heqr. induction BEH; i; inv Heqr; ss.
    - esplits; [econs 1|]; eauto.
    - exploit IHBEH; eauto. i. des.
      esplits; eauto. econs 2; eauto.
    - exploit IHBEH; eauto. i. des.
      esplits; eauto. econs 3; eauto.
  Qed.

  Lemma behavior_steps_ub
        lang step (th1: SeqThread.t lang) tr
        (BEH: SeqBehavior.behavior step th1 (tr, SeqTrace.ub)):
    exists th2 st3,
      (<<STEPS: SeqThread.steps step tr th1 th2>>) /\
      (<<FAILURE: step th2.(SeqThread.perm) MachineEvent.failure th2.(SeqThread.state) st3>>).
  Proof.
    remember (tr, SeqTrace.ub) as r.
    revert tr Heqr.
    dependent induction BEH; i; inv Heqr; ss.
    - unfold SeqThread.failure in *. des. inv FAILURE0.
      esplits; [econs 1|]; eauto.
    - exploit IHBEH; eauto. i. des.
      esplits; [econs 2; eauto|]; eauto.
    - exploit IHBEH; eauto. i. des.
      esplits; [econs 3; eauto|]; eauto.
  Qed.

  Lemma behavior_steps_at_step
        lang step (th1: SeqThread.t lang) e i o tr r
        (BEH: SeqBehavior.behavior step th1 ((e, i, o) :: tr, r)):
    exists st2 st3,
      (<<STEPS: rtc (step th1.(SeqThread.perm) MachineEvent.silent) th1.(SeqThread.state) st2>>) /\
      (<<STEP: lang.(Language.step) e st2.(SeqState.state) st3>>).
  Proof.
    remember ((e, i, o) :: tr, r) as res.
    revert e i o tr r Heqres.
    dependent induction BEH; i; inv Heqres; ss.
    - exploit IHBEH; eauto. i. des.
      inv STEP. ss.
      esplits; [econs 2; eauto|]; eauto.
    - inv STEP. ss. esplits; eauto.
  Qed.

  Lemma behavior_lang_atomic
        e st1 st2 p1 orc1 e' i o tr r
        (DETERM: deterministic _ st1.(SeqState.state))
        (LSTEP: lang_src.(Language.step) e st1.(SeqState.state) st2)
        (ATOMIC: is_atomic_event e)
        (BEH: SeqBehavior.behavior state_step (SeqThread.mk st1 p1 orc1)
                                   ((e', i, o) :: tr, r)):
    exists st2' e0 i0 orc2 p2 m2,
      (<<LANG: lang_src.(Language.step) e' st1.(SeqState.state) st2'>>) /\
      (<<SIMILAR: similar e e'>>) /\
      (<<ATOMIC: is_atomic_event e'>>) /\
      (<<EVENT: ProgramEvent.le e0 e'>>) /\
      (<<INPUT: Oracle.input_le i0 (SeqEvent.get_oracle_input i)>>) /\
      (<<ORACLE: Oracle.step e0 i0 o orc1 orc2>>) /\
      (<<MEM: SeqEvent.step i o p1 st1.(SeqState.memory) p2 m2>>) /\
      (<<INPUT: SeqEvent.wf_input e' i>>).
  Proof.
    inv BEH.
    { inv STEP. exploit state_step_subset; eauto. i. inv x. ss.
      exploit deterministic_step; [|exact LSTEP|exact LANG|]; ss. i. des.
      punfold DETERM. inv DETERM.
      exploit similar_is_atomic; eauto; try by (i; subst; eapply NO_NA_UPDATE; eauto). i.
      rewrite x2 in *.
      exploit na_local_step_na_event; eauto; ss.
    }
    inv STEP.
    exploit deterministic_step; [|exact LSTEP|exact LANG|]; ss. i. des.
    esplits; try exact LANG; eauto.
  Qed.

  Lemma at_step_behavior
        e i o p1 st1 p2 st2
        orc_init orc1 x l y ly r
        (DETERM: deterministic _ st1.(SeqState.state))
        (LSTEP: lang_src.(Language.step) e st1.(SeqState.state) st2.(SeqState.state))
        (ATOMIC: is_atomic_event e)
        (INPUT: SeqEvent.wf_input e i)
        (ESTEP: SeqEvent.step i o p1 st1.(SeqState.memory) p2 st2.(SeqState.memory))
        (ORACLE: oracle_follows_trace orc_init (y :: ly) orc1)
        (BEH: SeqBehavior.behavior state_step (SeqThread.mk st1 p1 orc1) (x :: l, r))
        (EVENT1: simple_match_event (e, i, o) y)
        (* (EVENT2: simple_match_event x y) *):
    exists orc2,
      (<<EVENT: x = (e, i, o)>>) /\
      (<<ORACLE2: oracle_follows_trace orc_init ly orc2>>) /\
      (<<BEH2: SeqBehavior.behavior state_step (SeqThread.mk st2 p2 orc2) (l, r)>>).
  Proof.
    inv BEH.
    { inv STEP. exploit state_step_subset; eauto. i. inv x0.
      punfold DETERM. inv DETERM.
      exploit STEP_STEP; [exact LSTEP|exact LANG|]. i. des.
      exploit similar_is_atomic; eauto; try by (i; subst; eapply NO_NA_UPDATE; eauto). i.
      rewrite x3 in *. inv LOCAL; ss; try destruct ord; ss.
    }
    inv STEP. ss.
    punfold DETERM. inv DETERM.
    exploit STEP_STEP; [exact LSTEP|exact LANG|]. i. des.
    destruct y as [[ey iy] oy].
    replace o with oy in * by (inv EVENT1; ss).
    replace e0 with e in *; cycle 1.
    { clear - ORACLE EVENT1 ORACLE0 x EVENT.
      inv EVENT1. clear INPUT.
      inv ORACLE. exploit SOUND; eauto. i. des.
      clear - x EVENT EVENT0 EVENT1.
      unfold eq_reading_value in *.
      destruct e1, e0, e, ey; ss; inv EVENT; inv EVENT0; des; subst; ss.
      exploit x2; eauto. i. subst. ss.
    }
    assert (ISIMILAR: oracle_similar_input (SeqEvent.get_oracle_input iy) i1).
    { clear - ORACLE EVENT1 ORACLE0 EVENT INPUT INPUT0 INPUT1. inv EVENT1.
      apply input_le_similar in INPUT0.
      exploit wf_input_similar; [exact INPUT|exact INPUT1|]. i.
      symmetry. etrans; eauto.
      symmetry. etrans; eauto.
      symmetry. ss.
    }
    replace o0 with oy in *; cycle 1.
    { clear - ORACLE EVENT1 ORACLE0 EVENT INPUT INPUT0 INPUT1 ISIMILAR. inv EVENT1.
      inv ORACLE. exploit SOUND; eauto. i. des.
      exploit x0; eauto. i. des. ss.
    }
    destruct st2. ss. exploit x0; eauto. i. subst.
    exploit SeqEvent.step_inj; [exact ESTEP|exact MEM|..]; eauto.
    { i. exploit wf_input_in_access; [exact INPUT|exact INPUT1|..]; eauto. }
    i. des. subst.
    esplits; eauto.
    inv ORACLE. exploit SOUND; try exact ORACLE0. i. des.
    apply x2. ss.
  Qed.

  Lemma steps_behavior_prefix_terminal
        tr_src tr_tgt
        st1 st2 p1 p2
        orc_init orc tr_src' v_src f_src
        (DETERM: deterministic _ st1.(SeqState.state))
        (TRACE: Forall2 simple_match_event tr_src tr_tgt)
        (STRACE: Forall2 simple_match_event tr_src' tr_tgt)
        (STEPS: state_steps state_step tr_src st1 st2 p1 p2)
        (ORACLE: oracle_follows_trace orc_init tr_tgt orc)
        (BEH: SeqBehavior.behavior state_step (SeqThread.mk st1 p1 orc)
                                   (tr_src', SeqTrace.term v_src f_src)):
    (<<TRACES: tr_src = tr_src'>>) /\
    exists st3,
      (<<NASTEPS: rtc (state_step p2 MachineEvent.silent) st2 st3>>) /\
      (<<TERMINAL: lang_src.(Language.is_terminal) st3.(SeqState.state)>>) /\
      (<<VALUE_MAP: st3.(SeqState.memory).(SeqMemory.value_map) = v_src>>) /\
      (<<FLAGS: st3.(SeqState.memory).(SeqMemory.flags) = f_src>>).
  Proof.
    revert tr_src' tr_tgt orc v_src f_src TRACE STRACE ORACLE BEH.
    induction STEPS; i.
    { clear ORACLE DETERM. inv TRACE. inv STRACE. split; ss.
      remember (SeqThread.mk st p orc) as th1.
      remember ([], SeqTrace.term v_src f_src) as tr.
      revert st v_src f_src Heqth1 Heqtr.
      induction BEH; i; inv Heqth1; try inv Heqtr.
      - esplits; eauto; ss.
      - inv STEP. exploit IHBEH; eauto. i. des. esplits.
        + econs 2; eauto.
        + ss.
        + ss.
        + ss.
    }
    exploit rtc_state_step_behavior; eauto.
    { ii. subst. inv STRACE. inv TRACE. }
    i. inv TRACE. inv STRACE.
    exploit at_step_behavior; try exact LSTEP; try exact x0; eauto.
    { eapply rtc_state_step_deterministic; eauto. }
    i. des. subst.
    exploit IHSTEPS; try exact H5; try eapply BEH2; eauto.
    { eapply step_deterministic; try eapply LSTEP; eauto.
      eapply rtc_state_step_deterministic; eauto.
    }
    i. des. subst. esplits; eauto.
  Qed.

  Lemma steps_behavior_prefix_ub
        tr_src tr_tgt
        st1 st2 p1 p2
        orc_init orc tr_src'
        (DETERM: deterministic _ st1.(SeqState.state))
        (TRACE: Forall2 simple_match_event tr_src tr_tgt)
        (STEPS: state_steps state_step tr_src st1 st2 p1 p2)
        (ORACLE: oracle_follows_trace orc_init tr_tgt orc)
        (BEH: SeqBehavior.behavior state_step (SeqThread.mk st1 p1 orc) (tr_src', SeqTrace.ub)):
    exists orc2 th tr st3,
      (<<ORACLE2: oracle_follows_trace orc_init [] orc2>>) /\
      (<<TRACES: tr_src' = tr_src ++ tr>>) /\
      (<<STEPS: SeqThread.steps state_step tr (SeqThread.mk st2 p2 orc2) th>>) /\
      (<<FAILURE: state_step th.(SeqThread.perm) MachineEvent.failure th.(SeqThread.state) st3>>).
  Proof.
    revert tr_src' tr_tgt orc TRACE ORACLE BEH.
    induction STEPS; i.
    { exploit behavior_steps_ub; eauto. i. des.
      inv TRACE. ss. esplits; eauto.
    }
    exploit rtc_state_step_behavior_ub; eauto. i. inv TRACE.
    exploit rtc_state_step_deterministic; eauto. i.
    destruct tr_src' as [|[[e' i'] o'] tr_src'].
    { inv x0; ss.
      - inv FAILURE. inv H.
        exploit state_step_subset; eauto. i. inv x.
        punfold x1. inv x1.
        exploit STEP_STEP; [exact LSTEP|exact LANG|]. i. des.
        exploit similar_is_atomic; try exact x; try by (i; subst; eapply NO_NA_UPDATE; eauto). i.
        rewrite x2 in *.
        exploit na_local_step_na_event; eauto. ss.
      - inv STEP. exploit state_step_subset; eauto. i. inv x.
        punfold x1. inv x1.
        exploit STEP_STEP; [exact LSTEP|exact LANG|]. i. des.
        exploit similar_is_atomic; try exact x; try by (i; subst; eapply NO_NA_UPDATE; eauto). i.
        rewrite x2 in *.
        exploit na_local_step_na_event; eauto. ss.
    }
    exploit at_step_behavior; try exact LSTEP; try exact x0; eauto. i. des. inv EVENT.
    exploit IHSTEPS; try exact H3; try eapply BEH2; eauto.
    { eapply step_deterministic; try eapply LSTEP; eauto. }
    i. des. subst. esplits; eauto. ss.
  Qed.

  Lemma behavior_nil_partial_inv
        lang step (th1: SeqThread.t lang) f
        (BEH: SeqBehavior.behavior step th1 ([], SeqTrace.partial f)):
    exists st2,
      (<<STEPS: rtc (step th1.(SeqThread.perm) MachineEvent.silent)
                    th1.(SeqThread.state) st2>>) /\
      (<<FLAGS: f = st2.(SeqState.memory).(SeqMemory.flags)>>).
  Proof.
    remember ([], SeqTrace.partial f) as r.
    revert f Heqr. induction BEH; ss; i; inv Heqr; eauto.
    exploit IHBEH; eauto. i. des.
    esplits; try exact FLAGS.
    inv STEP. ss. econs 2; eauto.
  Qed.

  Lemma steps_behavior_prefix_partial
        tr_src tr_tgt
        st1 st2 p1 p2
        orc_init orc tr_src' tr_src_ex f_src
        (DETERM: deterministic _ st1.(SeqState.state))
        (TRACE: Forall2 simple_match_event tr_src tr_tgt)
        (STRACE: Forall2 simple_match_event tr_src' tr_tgt)
        (STEPS: state_steps state_step tr_src st1 st2 p1 p2)
        (ORACLE: oracle_follows_trace orc_init tr_tgt orc)
        (BEH: SeqBehavior.behavior state_step (SeqThread.mk st1 p1 orc)
                                   (tr_src' ++ tr_src_ex, SeqTrace.partial f_src)):
    (<<TRACES: tr_src = tr_src'>>) /\
    (<<EX: tr_src_ex = []>>) /\
    (exists st3,
        ((<<PREFIX: rtc (state_step p2 MachineEvent.silent) st2 st3>>) \/
         (<<SUFFIX: rtc (state_step p2 MachineEvent.silent) st3 st2>>)) /\
        (<<FLAGS: f_src = st3.(SeqState.memory).(SeqMemory.flags)>>)) \/
    exists orc',
      (<<LE1: oracle_le orc' orc_init>>) /\
      (<<LE2: oracle_le orc_init orc'>>) /\
      (<<TRACES: tr_src = tr_src'>>) /\
      (<<BEH_EX: SeqBehavior.behavior state_step (SeqThread.mk st2 p2 orc')
                                      (tr_src_ex, SeqTrace.partial f_src)>>).
  Proof.
    destruct tr_src_ex as [|[[e i] o] tr_src_ex].
    { left. rewrite app_nil_r in *.
      revert tr_src' tr_tgt orc TRACE STRACE ORACLE BEH.
      induction STEPS; i.
      { inv TRACE. inv STRACE.
        exploit behavior_nil_partial_inv; eauto. s. i. des.
        esplits; try exact FLAGS; eauto.
      }
      inv TRACE. inv STRACE.
      exploit rtc_state_step_behavior; eauto; ss. i.
      exploit at_step_behavior; try exact LSTEP; try exact x1; eauto.
      { eapply rtc_state_step_deterministic; eauto. }
      i. des. subst.
      exploit IHSTEPS; try exact H5; try eapply BEH2; eauto.
      { eapply step_deterministic; try eapply LSTEP; eauto.
        eapply rtc_state_step_deterministic; eauto.
      }
      i. des; subst; splits; auto.
      - esplits; [|refl]. eauto.
      - esplits; [|refl]. eauto.
    }
    right.
    revert tr_src' tr_tgt orc TRACE STRACE ORACLE BEH.
    induction STEPS; i.
    { inv TRACE. inv STRACE. inv ORACLE. esplits; eauto. }
    exploit rtc_state_step_behavior; eauto.
    { destruct tr_src'; ss. }
    i. inv TRACE. inv STRACE.
    exploit at_step_behavior; try exact LSTEP; try exact x0; eauto.
    { eapply rtc_state_step_deterministic; eauto. }
    i. des. subst.
    exploit IHSTEPS; try exact H5; try eapply BEH2; eauto.
    { eapply step_deterministic; try eapply LSTEP; eauto.
      eapply rtc_state_step_deterministic; eauto.
    }
    i. des. subst. esplits; eauto.
  Qed.

  Lemma trace_le_cases
        d tr_tgt tr_src
        (LE: SeqTrace.le d tr_tgt tr_src):
    (<<TERM: exists tr_src' v_src f_src tr_tgt' v_tgt f_tgt,
        tr_src = (tr_src', SeqTrace.term v_src f_src) /\
        tr_tgt = (tr_tgt', SeqTrace.term v_tgt f_tgt) /\
        List.Forall2 simple_match_event tr_src' tr_tgt' /\
        ValueMap.le v_tgt v_src>>) \/
    (<<PARTIAL: exists tr_src' tr_src_ex f_src tr_tgt' f_tgt,
        tr_src = (tr_src' ++ tr_src_ex, SeqTrace.partial f_src) /\
        tr_tgt = (tr_tgt', SeqTrace.partial f_tgt) /\
        List.Forall2 simple_match_event tr_src' tr_tgt'>>) \/
    (<<UB: exists tr_src', tr_src = (tr_src', SeqTrace.ub)>>).
  Proof.
    induction LE.
    { left. esplits; eauto. }
    { right. left. esplits; eauto. refl. }
    { right. right. esplits; eauto. }
    des.
    - inv TERM. inv TERM0.
      left. esplits; eauto.
      econs 2; eauto. econs; eauto.
      eapply input_match_similar; eauto.
    - inv PARTIAL. inv PARTIAL0.
      right. left. esplits.
      + replace ((e_src, i_src, o) :: tr_src' ++ tr_src_ex) with
            (((e_src, i_src, o) :: tr_src') ++ tr_src_ex) by ss. refl.
      + ss.
      + econs 2; eauto. econs; eauto.
        eapply input_match_similar; eauto.
    - inv UB. right. right.
      esplits; eauto.
  Qed.

  Lemma steps_implies
        lang step1 step2 tr (th1 th2: SeqThread.t lang)
        (IMPLIES: step1 <4= step2)
        (STEPS: SeqThread.steps step1 tr th1 th2):
    SeqThread.steps step2 tr th1 th2.
  Proof.
    induction STEPS; try by econs 1.
    { econs 2; eauto. inv STEP. econs. eauto. }
    { econs 3; eauto. }
  Qed.

  Lemma simple_match_last_inv
        tr_src tr_tgt e_tgt
        (MATCH: Forall2 simple_match_event tr_src (tr_tgt ++ [e_tgt])):
    exists tr_src' e_src,
      tr_src = tr_src' ++ [e_src] /\
        Forall2 simple_match_event tr_src' tr_tgt /\
        simple_match_event e_src e_tgt.
  Proof.
    revert tr_src MATCH. induction tr_tgt; ss; i.
    { inv MATCH. inv H3. esplits; eauto. ss. }
    inv MATCH. exploit IHtr_tgt; eauto. i. des. subst.
    esplits; eauto. ss.
  Qed.

  Lemma rtc_step_steps_nil
        lang step (st1: SeqState.t lang) p orc st2
        (STEPS: rtc (step p MachineEvent.silent) st1 st2):
    SeqThread.steps step [] (SeqThread.mk st1 p orc) (SeqThread.mk st2 p orc).
  Proof.
    induction STEPS; try by econs.
    econs 2; eauto. econs. ss.
  Qed.

  Lemma steps_nil_rtc_step
        lang step (st1: SeqState.t lang) p1 orc1 st2 p2 orc2
        (STEPS: SeqThread.steps step [] (SeqThread.mk st1 p1 orc1) (SeqThread.mk st2 p2 orc2)):
    rtc (step p1 MachineEvent.silent) st1 st2.
  Proof.
    dependent induction STEPS; eauto.
    destruct th1. exploit IHSTEPS; eauto. i. clear IHSTEPS.
    inv STEP. econs 2; eauto.
  Qed.

  Lemma behavior_step_inv
        st1 p1 orc1
        e st2 st3
        e' i o tr r
        (DETERM: deterministic _ st1.(SeqState.state))
        (NASTEPS: rtc (state_step p1 MachineEvent.silent) st1 st2)
        (LSTEP: lang_src.(Language.step) e st2.(SeqState.state) st3)
        (ATOMIC: is_atomic_event e)
        (BEH: SeqBehavior.behavior state_step (SeqThread.mk st1 p1 orc1)
                                   ((e', i, o) :: tr, r)):
    exists th3,
      SeqThread.at_step e' i o (SeqThread.mk st2 p1 orc1) th3.
  Proof.
    induction NASTEPS.
    { inv BEH; ss; eauto.
      inv STEP. exploit state_step_subset; eauto. i.
      inv x0. exploit deterministic_step; [|exact LSTEP|exact LANG|]; ss. i. des.
      punfold DETERM. inv DETERM.
      rewrite similar_is_atomic in ATOMIC; eauto;
        try by (i; subst; eapply NO_NA_UPDATE; eauto).
      inv LOCAL; ss; try destruct ord; ss.
    }
    inv BEH; ss.
    { inv STEP. exploit state_step_determ; [exact H|exact STEP0|]. i. des. subst.
      exploit IHNASTEPS; eauto.
      exploit state_step_subset; eauto. i. inv x1. ss.
      eapply step_deterministic; eauto.
    }
    { inv STEP. exploit state_step_subset; eauto. i.
      inv x. exploit deterministic_step; [|exact LANG|exact LANG0|]; ss. i. des.
      punfold DETERM. inv DETERM.
      rewrite similar_is_atomic in ATOMIC0; eauto;
        try by (i; subst; eapply NO_NA_UPDATE; eauto).
      inv LOCAL; ss; try destruct ord; ss.
    }
  Qed.

  Lemma deterministic_steps_inv
        p1 st1 st2 e st3
        e' i o tr orc1 st4 p4 orc4
        (DETERM: deterministic _ st1.(SeqState.state))
        (NASTEPS: rtc (state_step p1 MachineEvent.silent) st1 st2)
        (LSTEP: lang_src.(Language.step) e st2.(SeqState.state) st3)
        (ATOMIC: is_atomic_event e)
        (STEPS: SeqThread.steps state_step ((e', i, o) :: tr)
                                (SeqThread.mk st1 p1 orc1) (SeqThread.mk st4 p4 orc4)):
    exists st3' p3 orc3,
      similar e e' /\
      SeqThread.at_step e' i o (SeqThread.mk st2 p1 orc1) (SeqThread.mk st3' p3 orc3).
  Proof.
    exploit steps_cons_inv; eauto. i. des.
    exploit steps_nil_rtc_step; eauto. i.
    cut (similar e e' /\ st0 = st2).
    { i. des. subst. destruct th3. eauto. }
    clear STEPS NASTEPS0 STEPS0. inv ATSTEP.
    clear - state_step_subset state_step_determ DETERM NASTEPS LSTEP ATOMIC ATOMIC0 x0 LANG.
    (* move NASTEPS at top. revert_until NASTEPS. *)
    induction NASTEPS; ss; i.
    { inv x0; ss.
      - exploit deterministic_step; [|exact LSTEP|exact LANG|]; eauto. i. des. auto.
      - exploit state_step_subset; eauto. i. inv x0. ss.
        exploit deterministic_step; [|exact LSTEP|exact LANG0|]; eauto. i. des.
        destruct e; inv LOCAL; ss; inv x0; ss; des; subst;
          try destruct ord; try destruct ord0; ss.
    }
    apply IHNASTEPS; auto.
    { eapply rtc_state_step_deterministic; eauto. }
    inv x0.
    - exploit state_step_subset; try exact H. i. inv x.
      exploit deterministic_step; [|exact LANG|exact LANG0|]; eauto. i. des.
      destruct e'; inv LOCAL; ss; inv x0; ss; des; subst;
        try destruct ord; try destruct ord0; ss.
    - exploit state_step_determ; [exact H|exact H0|..]. i. des. subst. ss.
  Qed.

  Definition wf_in_access_old (m: SeqMemory.t) (i: option (Loc.t * Const.t * Flag.t * Const.t)): Prop :=
    match i with
    | Some (loc, v_old, f_old, _) =>
      v_old = m.(SeqMemory.value_map) loc /\
      f_old = m.(SeqMemory.flags) loc
    | None => True
    end.

  Lemma event_step_wf_in_access_old
        i o p1 m1 p2 m2
        (STEP: SeqEvent.step i o p1 m1 p2 m2):
    wf_in_access_old m1 i.(SeqEvent.in_access).
  Proof.
    inv STEP; ss. inv UPD; ss. inv MEM; ss.
  Qed.

  Lemma refinement_implies_simulation_aux
        (st_src: lang_src.(Language.state)) (st_tgt: lang_tgt.(Language.state))
        (REFINE: forall p m o (WF: Oracle.wf o),
            SeqTrace.incl
              (SeqBehavior.behavior (@SeqState.na_step _) (SeqThread.mk (SeqState.mk _ st_tgt m) p o))
              (SeqBehavior.behavior state_step (SeqThread.mk (SeqState.mk _ st_src m) p o)))
        (DETERM: deterministic _ st_src)
        (RECEPTIVE: receptive _ st_tgt)
        p m p1 d
        tr_src st1_src
        tr_tgt st0_tgt st1_tgt
        (STEPS_SRC: state_steps state_step tr_src (SeqState.mk _ st_src m) st1_src p p1)
        (STEPS_TGT: state_steps (@SeqState.na_step lang_tgt) tr_tgt (SeqState.mk _ st_tgt m) st0_tgt p p1)
        (NASTEPS_TGT: rtc (SeqState.na_step p1 MachineEvent.silent) st0_tgt st1_tgt)
        (TRACES: match_trace (min_match SeqEvent.input_match) Flags.bot d tr_src tr_tgt):
      sim_seq (fun _ _ => True) p1 d st1_src st1_tgt.
  Proof.
    specialize (REFINE p m).
    revert p1 d tr_src st1_src tr_tgt st0_tgt st1_tgt STEPS_SRC STEPS_TGT NASTEPS_TGT TRACES.
    pcofix CIH. i. pfold.
    destruct (classic (sim_seq_failure_case p1 st1_src)).
    { econs 2; eauto. }
    assert (NONUB: exists orc,
               (<<WF: Oracle.wf orc>>) /\
               (forall th tr w
                  (STEPS: SeqThread.steps (@SeqState.na_step _) tr (SeqThread.mk st1_src p1 orc) th)
                  (TRACE: SeqThread.writing_trace tr w)
                  (FAILURE: SeqThread.failure (@SeqState.na_step _) th),
                 False)).
    { clear - H. unfold sim_seq_failure_case in H.
      apply not_all_ex_not in H. des. rename n into orc. exists orc.
      destruct (classic (Oracle.wf orc)); cycle 1.
      { exfalso. apply H. i. ss. }
      split; ss. i. apply H. i. esplits; eauto.
    }
    des.

    econs.
    { (* terminal *)
      ii. exploit steps_behavior_terminal; try exact STEPS_TGT; eauto.
      { eapply (oracle_of_trace_follows tr_tgt orc). }
      intro BEH_TGT.
      exploit REFINE; try exact BEH_TGT.
      { apply oracle_of_trace_wf. eapply state_steps_wf_trace; eauto. ss. }
      i. des.
      exploit trace_le_cases; eauto. i. des; try congr.
      { (* src terminal *)
        inv TERM0.
        exploit steps_behavior_prefix_terminal; try exact STEPS_SRC; try exact x; eauto.
        { eapply match_trace_simple_match; eauto. }
        { apply oracle_of_trace_follows. }
        i. des. subst.
        esplits; try exact TERMINAL; eauto.
        - eapply rtc_implies; try eapply state_step_subset. ss.
        - eapply match_trace_le_terminal; eauto.
      }
      { (* src UB *)
        subst.
        exploit steps_behavior_prefix_ub; try exact STEPS_SRC; try exact x; eauto.
        { eapply match_trace_simple_match; eauto. }
        { apply oracle_of_trace_follows. }
        i. des. subst.
        exfalso.
        inv ORACLE2. destruct th. ss.
        exploit oracle_le_steps; try exact LE1; try exact STEPS. i. des.
        exploit steps_implies; try exact x2; try apply state_step_subset. i.
        exploit trace_le_ub_match; try eapply x0.
        { eapply match_trace_simple_match; eauto. }
        i. des. eapply NONUB0; eauto.
        unfold SeqThread.failure. esplits. econs. eauto.
      }
    }

    { (* na step *)
      ii. destruct e.
      { (* silent *)
        esplits; eauto; try by econs 2.
        right. eapply CIH; eauto. etrans; eauto.
      }
      { (* syscall *)
        inv STEP_TGT. inv LOCAL; ss. destruct (p1 loc); ss.
      }
      { (* failure *)
        exploit steps_behavior_ub; eauto.
        { eapply (oracle_of_trace_follows tr_tgt orc). }
        intro BEH_TGT.
        exploit REFINE; try exact BEH_TGT.
        { apply oracle_of_trace_wf; ss. eapply state_steps_wf_trace; eauto. }
        i. des.
        exploit trace_le_cases; eauto. i. des; try congr. subst.
        exploit steps_behavior_prefix_ub; try exact STEPS_SRC; try exact x; eauto.
        { eapply match_trace_simple_match; eauto. }
        { apply oracle_of_trace_follows. }
        i. des. subst.
        exfalso.
        inv ORACLE2. destruct th. ss.
        exploit oracle_le_steps; try exact LE1; try exact STEPS. i. des.
        exploit steps_implies; try exact x2; try apply state_step_subset. i.
        exploit trace_le_ub_match; try eapply x0.
        { eapply match_trace_simple_match; eauto. }
        i. des. eapply NONUB0; eauto.
        unfold SeqThread.failure. esplits. econs. eauto.
      }
    }

    { (* at step *)
      ii.
      assert (exists (st_src1 : SeqState.t lang_src) (st_src2 : Language.state lang_src)
                (e_src : ProgramEvent.t),
                 rtc (state_step p1 MachineEvent.silent) st1_src st_src1 /\
                 Language.step lang_src e_src (SeqState.state st_src1) st_src2 /\
                 ProgramEvent.le e_tgt e_src).
      { specialize (event_step_exists_full e_tgt p1 st1_tgt.(SeqState.memory)). i. des.
        exploit steps_behavior_at_step; eauto.
        { instantiate (2:=orc). eapply oracle_of_trace_follows. }
        intro BEH_TGT. des.
        exploit REFINE; try exact BEH_TGT.
        { eapply oracle_of_trace_wf.
          - eapply state_steps_wf_trace; eauto.
          - eapply add_oracle_wf; eauto.
            eapply wf_input_oracle_wf_input. ss.
        }
        i. des.
        exploit trace_le_cases; eauto. i. des; try congr; subst.
        { (* src partial *)
          inv PARTIAL0.
          exploit simple_match_last_inv; try exact PARTIAL1. i. des. subst. clear PARTIAL1.
          destruct e_src as [[e_src i_src] o_src]. inv x3.
          rewrite <- app_assoc in x.
          exploit steps_behavior_prefix_partial; try exact STEPS_SRC; try exact x; eauto.
          { eapply match_trace_simple_match; eauto. }
          { apply oracle_of_trace_follows. }
          i. des; ss. symmetry in TRACES0. subst.
          exploit behavior_steps_at_step; eauto. s. i. des.
          esplits; try exact STEP; ss.
        }
        { (* src ub *)
          exploit steps_behavior_prefix_ub; try exact STEPS_SRC; try exact x; eauto.
          { eapply match_trace_simple_match; eauto. }
          { apply oracle_of_trace_follows. }
          i. des; ss. subst. inv ORACLE2. destruct th. ss.
          exploit add_oracle_steps_inv; try exact STEPS; eauto. i. des.
          - exploit trace_le_ub_step_match; try eapply x0.
            { eapply match_trace_simple_match; eauto. }
            i. des.
            + exfalso. eapply NONUB0.
              * eapply steps_implies; try eapply x2. eauto.
              * eauto.
              * unfold SeqThread.failure. esplits. econs.
                eapply state_step_subset; eauto.
            + subst.
              exploit steps_cons_inv; try exact x2. i. des.
              exploit steps_nil_rtc_step; try exact NASTEPS. i.
              inv ATSTEP. esplits; eauto.
          - subst.
            exploit steps_cons_inv; try exact STEPS. i. des.
            exploit steps_nil_rtc_step; eauto. i. inv ATSTEP. esplits; eauto.
        }
      }

      i. des. esplits; [eapply rtc_implies; try eapply H0|..]; eauto. i.
      exploit steps_behavior_at_step; eauto.
      { instantiate (2:=orc). eapply oracle_of_trace_follows. }
      intro BEH_TGT. des.
      exploit REFINE; try exact BEH_TGT.
      { eapply oracle_of_trace_wf.
        - eapply state_steps_wf_trace; eauto.
        - eapply add_oracle_wf; eauto.
          eapply wf_input_oracle_wf_input. ss.
      }
      i. des.
      exploit trace_le_cases; eauto. i. des; try congr; subst.
      { (* src partial *)
        inv PARTIAL0.
        exploit simple_match_last_inv; try exact PARTIAL1. i. des. subst. clear PARTIAL1.
        destruct e_src0 as [[e_src0 i_src] o_src]. inv x3.
        rewrite <- app_assoc in x.
        exploit steps_behavior_prefix_partial; try exact STEPS_SRC; try exact x; eauto.
        { eapply match_trace_simple_match; eauto. }
        { apply oracle_of_trace_follows. }
        i. des; ss. symmetry in TRACES0. subst.
        exploit state_steps_deterministic; eauto; ss. i.
        exploit rtc_state_step_deterministic; try exact H0; eauto. i.
        exploit rtc_state_step_behavior; try exact H0; eauto; ss. i.

        exploit behavior_lang_atomic; try exact x5; eauto; ss.
        { erewrite <- le_is_atomic; eauto. }
        i. des.
        exploit SeqEvent.step_inj_perms; [exact STEP_TGT0|exact MEM|..]; ss.
        { clear - INPUT INPUT2 SIMILAR H2. i.
          destruct i_src, i_tgt. ss. subst.
          unfold SeqEvent.wf_input in *. ss. splitsH. clear H1 H3 H5 H6.
          specialize (H loc2 v_new2). des. exploit H; eauto. i.
          specialize (H0 loc1 v_new1). des. exploit H0; eauto. i.
          destruct e_src, e_src0, e_tgt; ss; des; subst; inv x; inv x0; ss; inv H2; ss.
        }
        i. subst.
        rewrite <- app_assoc in x0.
        exploit match_trace_le_partial_step; try exact x0; eauto. i. des.
        exploit similar_le_eq; try exact SIMILAR; eauto. i. subst.
        exploit SeqEvent.input_match_mon; try exact INPUT_MATCH; try exact MIN; try refl. i.
        exploit min_input_match_exists; try exact x6. i. des.
        esplits; try eapply MIN0; eauto.
        right. eapply CIH; eauto.
        - eapply state_steps_last; eauto.
        - eapply state_steps_last; eauto.
        - econs; eauto.
      }

      { (* src ub *)
        exploit steps_behavior_prefix_ub; try exact STEPS_SRC; try exact x; eauto.
        { eapply match_trace_simple_match; eauto. }
        { apply oracle_of_trace_follows. }
        i. des; ss. subst. inv ORACLE2. destruct th. ss.
        exploit add_oracle_steps_inv; try exact STEPS; eauto. i. des.
        { exploit trace_le_ub_step_match; try eapply x0.
          { eapply match_trace_simple_match; eauto. }
          i. des.
          - exfalso. eapply NONUB0.
            + eapply steps_implies; try eapply x2. eauto.
            + eauto.
            + unfold SeqThread.failure. esplits. econs.
              eapply state_step_subset; eauto.
          - subst.
            hexploit min_match_trace_min; try exact MATCH; eauto. i.
            exploit SeqEvent.input_match_mon; try exact INPUT0; eauto; try refl. i.
            exploit min_input_match_exists; try exact x3. i. des.
            exploit deterministic_steps_inv; try exact x2; eauto.
            { eapply state_steps_deterministic; eauto. ss. }
            { erewrite <- le_is_atomic; eauto. }
            i. des.
            exploit similar_le_eq; try exact x3; eauto. i. subst.
            inv x1. ss.
            exploit SeqEvent.step_inj_perms; [exact STEP_TGT0|exact MEM|..]; ss.
            { clear - INPUT INPUT2 EVENT. i.
              destruct i_src, i_tgt. ss. subst.
              unfold SeqEvent.wf_input in *. ss. splitsH. clear H1 H2 H4 H5.
              specialize (H loc2 v_new2). des. exploit H; eauto. i.
              specialize (H0 loc1 v_new1). des. exploit H0; eauto. i.
              destruct e_src0, e_tgt; ss; des; subst; inv x; inv x0; ss; inv EVENT; ss.
            }
            i. subst. esplits; try eapply MIN; eauto.
            right. eapply CIH; eauto.
            + eapply state_steps_last; eauto.
            + eapply state_steps_last; eauto.
            + econs; eauto.
        }
        subst.

        exploit deterministic_steps_inv; try exact STEPS; try exact H1; eauto.
        { eapply state_steps_deterministic; eauto. ss. }
        { erewrite <- le_is_atomic; eauto. }
        i. des.
        exploit similar_le_eq; try exact x2; eauto. i. symmetry in x4. subst.
        inv x1. ss.
        exploit SeqEvent.step_inj_perms; [exact STEP_TGT0|exact MEM|..]; ss.
        { clear - INPUT INPUT2 EVENT. i.
          destruct i', i_tgt. ss. subst.
          unfold SeqEvent.wf_input in *. ss. splitsH. clear H1 H2 H4 H5.
          specialize (H loc2 v_new2). des. exploit H; eauto. i.
          specialize (H0 loc1 v_new1). des. exploit H0; eauto. i.
          destruct e_src, e_tgt; ss; des; subst; inv x; inv x0; ss; inv EVENT; ss.
        }
        i. subst.

        cut (exists d1', SeqEvent.input_match d d1' i' i_tgt).
        { i. des.
          exploit min_input_match_exists; try exact H3. i. des.
          esplits; try eapply MIN; eauto.
          right. eapply CIH; eauto.
          - eapply state_steps_last; eauto.
          - eapply state_steps_last; eauto.
          - econs; eauto.
        }

        destruct (is_acquire e_src) eqn:ACQ.
        { exploit match_trace_le_ub_acquire; try exact x0; eauto. i. des.
          exploit SeqEvent.input_match_mon; try exact INPUT_MATCH; eauto. refl.
        }

        cut (__guard__ (
                 exists e_src' e_tgt' d1' i_src' i_tgt',
                   (<<WSIMLAR: wsimilar e_tgt e_tgt'>>) /\
                   (<<LE': ProgramEvent.le e_tgt' e_src'>>) /\
                   (<<WF_SRC: SeqEvent.wf_input e_src' i_src'>>) /\
                   (<<WF_TGT: SeqEvent.wf_input e_tgt' i_tgt'>>) /\
                   (<<WF_ACCESS_SRC: wf_in_access_old m0 i_src'.(SeqEvent.in_access)>>) /\
                   (<<WF_ACCESS_TGT: wf_in_access_old st1_tgt.(SeqState.memory) i_tgt'.(SeqEvent.in_access)>>) /\
                   (<<IMATCH: SeqEvent.input_match d d1' i_src' i_tgt'>>))).
        { exploit event_step_wf_in_access_old; try exact MEM. intro WF_OLD_SRC.
          exploit event_step_wf_in_access_old; try exact STEP_TGT0. intro WF_OLD_TGT.
          clear - H2 INPUT EVENT INPUT2 WF_OLD_SRC WF_OLD_TGT ACQ.
          i. unguard. des. inv IMATCH.
          unfold SeqEvent.wf_input in *. splitsH.
          destruct i', i_tgt, i_src', i_tgt'. ss.
          exists Flags.top. econs; ss.
          - clear ACQUIRE RELEASE H1 H3 H5 H6 H8 H9 H11 H12.
            instantiate (1:=d1). inv ACCESS.
            + exploit wsimilar_is_accessing_loc; eauto. i. des.
              { rewrite x0, x1 in *.
                specialize (H loc v2). des. exploit H1; eauto. i. des. ss. }
              exploit le_is_accessing_loc; try exact EVENT; eauto. i. des; try congr.
              exploit le_is_accessing_loc; try exact LE'; eauto. i. des; try congr.
              rewrite x0, x1, x3, x5 in *. ss.
              destruct in_access as [[[[]]]|].
              { specialize (H4 t t2). des. exploit H4; eauto. ss. }
              destruct in_access0 as [[[[]]]|].
              { specialize (H7 t t2). des. exploit H7; eauto. ss. }
              econs. ss.
            + exploit wsimilar_is_accessing_loc; eauto. i. des; cycle 1.
              { rewrite x0, x1 in *.
                specialize (H l v_new_tgt). des. exploit H; eauto. ss. }
              exploit le_is_accessing_loc; try exact EVENT; eauto. i. des; try congr.
              exploit le_is_accessing_loc; try exact LE'; eauto. i. des; try congr.
              rewrite x0, x1, x3, x5 in *. ss.
              destruct in_access as [[[[]]]|]; cycle 1.
              { specialize (H4 loc0 v3). des. exploit H1; eauto. i. des. ss. }
              destruct in_access0 as [[[[]]]|]; cycle 1.
              { specialize (H7 loc v1). des. exploit H1; eauto. i. des. ss. }
              inv x2. inv x4. ss. des. subst.
              specialize (H7 loc1 v0). des. exploit H1; eauto. i. des. inv x.
              specialize (H0 loc1 v5). des. exploit H3; eauto. i. des. inv x.
              specialize (H4 loc1 v3). des. exploit H5; eauto. i. des. inv x.
              econs; eauto.
          - clear ACCESS RELEASE H H3 H0 H6 H4 H9 H7 H12.
            instantiate (1:=d2).
            exploit wsimilar_is_acquire; eauto. i.
            exploit le_is_acquire; try exact EVENT. i.
            exploit le_is_acquire; try exact LE'. i.
            inv ACQUIRE.
            + destruct in_acquire, in_acquire0, (is_acquire e_src), (is_acquire e_tgt),
              (is_acquire e_src'), (is_acquire e_tgt'); intuition.
              econs. ss.
            + destruct in_acquire, in_acquire0, (is_acquire e_src), (is_acquire e_tgt),
              (is_acquire e_src'), (is_acquire e_tgt'); intuition.
          - clear ACCESS ACQUIRE H H1 H0 H5 H4 H8 H7 H11.
            exploit le_is_release; try exact EVENT. i.
            rewrite <- H12 in x0. rewrite <- H9 in x0.
            destruct in_release, in_release0; try by intuition.
            + destruct p, p0. econs; ss.
              rewrite Flags.join_top_r. apply Flags.top_spec.
            + econs. apply Flags.top_spec.
        }

        clear CIH INPUT OUTPUT STEP_TGT0 BEH_TGT x0 x STEPS FAILURE LE1 LE2 EVENT INPUT0
              i_tgt o mem_tgt p3 i' tr' orc2 state0 perm oracle st3
              orc3 x2 e0 i0 st1 m1 LANG ATOMIC0 EVENT0 INPUT1 ORACLE MEM INPUT2.
        exploit receptive_oracle_progress; try exact STEP_TGT; try exact WF; eauto.
        { eapply rtc_na_step_receptive; eauto.
          eapply state_steps_receptive; eauto. ss.
        }
        i. des.
        exploit PROGRESS.
        { eapply (oracle_input_of_event_wf e' st1_tgt.(SeqState.memory)). }
        i. des.
        exploit event_step_exists; try exact WF0.
        instantiate (1:=st1_tgt.(SeqState.memory)).
        instantiate (1:=p1).
        i. des.
        exploit event_step_oracle_input; try exact STEP0; eauto. i. rewrite <- x0 in *.

        exploit steps_behavior_oracle_step; try exact STEPS_TGT; try exact STEP; eauto.
        { eapply oracle_of_trace_follows. }
        i. exploit REFINE; try exact x1.
        { apply oracle_of_trace_wf; ss.  eapply state_steps_wf_trace; eauto. }
        i. des.
        exploit trace_le_cases; try exact x2. i. des; try congr.
        { (* src partial *)
          inv PARTIAL0.
          exploit simple_match_last_inv; try exact PARTIAL1. i. des. subst.
          rewrite <- app_assoc in *.
          exploit steps_behavior_prefix_partial; try exact x; try exact STEPS_SRC; eauto.
          { eapply match_trace_simple_match; eauto. }
          { eapply oracle_of_trace_follows. }
          i. des; ss. subst. inv x5.
          exploit match_trace_le_partial_step; try exact x2; eauto. i. des.
          exploit SeqEvent.input_match_mon; try exact INPUT_MATCH; try exact MIN; try refl. i.
          exploit behavior_step_inv; try exact BEH_EX; eauto.
          { eapply state_steps_deterministic; eauto. ss. }
          { erewrite <- le_is_atomic; try exact ATOMIC; eauto. }
          i. des. inv x6.
          unguard. esplits; try exact x5; eauto.
          - eapply event_step_wf_in_access_old; eauto.
          - eapply event_step_wf_in_access_old; eauto.
        }
        { (* src ub *)
          subst.
          exploit steps_behavior_prefix_ub; try exact STEPS_SRC; try exact x; eauto.
          { eapply match_trace_simple_match; eauto. }
          { apply oracle_of_trace_follows. }
          i. des. subst. inv ORACLE2.
          exploit trace_le_ub_step_match; try eapply x2.
          { eapply match_trace_simple_match; eauto. }
          i. des.
          - exfalso. destruct th. ss.
            exploit oracle_le_steps; try exact STEPS; eauto. i. des.
            eapply NONUB0.
            + eapply steps_implies; try eapply x5. eauto.
            + eauto.
            + unfold SeqThread.failure. esplits. econs.
              eapply state_step_subset; eauto.
          - subst. destruct th. ss.
            exploit deterministic_steps_inv; try exact STEPS; eauto.
            { eapply state_steps_deterministic; eauto. ss. }
            { erewrite <- le_is_atomic; try exact ATOMIC; eauto. }
            i. des. inv x3.
            hexploit min_match_trace_min; try exact MATCH; eauto. i.
            exploit SeqEvent.input_match_mon; try exact INPUT; try exact H3; try refl. i.
            unguard. esplits; try exact x5; eauto.
            + eapply event_step_wf_in_access_old; eauto.
            + eapply event_step_wf_in_access_old; eauto.
        }
      }
    }

    { (* partial *)
      ii. exploit steps_behavior_partial; try exact STEPS_TGT; eauto.
      { eapply (oracle_of_trace_follows tr_tgt o). }
      intro BEH_TGT.
      exploit REFINE; try exact BEH_TGT.
      { apply oracle_of_trace_wf. eapply state_steps_wf_trace; eauto. ss. }
      i. des.
      exploit trace_le_cases; eauto. i. des; try congr.
      { (* src partial *)
        inv PARTIAL0.
        exploit steps_behavior_prefix_partial; try exact STEPS_SRC; try exact x; eauto.
        { eapply match_trace_simple_match; eauto. }
        { apply oracle_of_trace_follows. }
        i. des; subst.
        { exploit match_trace_le_partial; try exact x0; eauto. i. des.
          exploit rtc_step_steps_nil; try exact PREFIX; eauto. i.
          exploit steps_implies; try exact x2; try eapply state_step_subset. i.
          esplits; try eapply x3; eauto.
        }
        { exploit match_trace_le_partial; try exact x0; eauto. i. des.
          esplits; [econs 1|..]; eauto. s. left.
          etrans; eauto. apply Flags.join_mon_r.
          eapply na_steps_flags.
          eapply rtc_implies; try eapply state_step_subset; eauto.
        }
        { exploit match_trace_le_partial; try exact x0; eauto. i. des.
          exploit behavior_steps_partial; eauto. i. des. subst.
          exploit steps_implies; try exact STEPS; try eapply state_step_subset. i.
          destruct th2; ss.
          exploit oracle_le_steps; try exact x2; eauto. i. des.
          esplits; try exact x3; eauto.
        }
      }
      { (* src UB *)
        subst.
        exploit steps_behavior_prefix_ub; try exact STEPS_SRC; try exact x; eauto.
        { eapply match_trace_simple_match; eauto. }
        { apply oracle_of_trace_follows. }
        i. des. subst. inv ORACLE2.
        exploit trace_le_ub_match; try exact x0.
        { eapply match_trace_simple_match; eauto. }
        i. des. destruct th. ss.
        exploit steps_implies; try eapply state_step_subset; try eapply STEPS. i.
        exploit oracle_le_steps; try exact x3; try eapply LE1. i. des.
        esplits; eauto. s. right.
        unfold SeqThread.failure. esplits. econs. eauto.
      }
    }
  Qed.

  Theorem refinement_implies_simulation
          (st_src: lang_src.(Language.state)) (st_tgt: lang_tgt.(Language.state))
          (REFINE: SeqBehavior.refine _ _ st_tgt st_src)
          (DETERM: deterministic _ st_src)
          (RECEPTIVE: receptive _ st_tgt)
          (TOP: forall p m o (WF: Oracle.wf o),
              SeqBehavior.behavior (@SeqState.na_step _) (SeqThread.mk (SeqState.mk _ st_src m) p o)
              <1=
              SeqBehavior.behavior state_step (SeqThread.mk (SeqState.mk _ st_src m) p o))
    :
      sim_seq_all _ _ (fun _ _ => True) st_src st_tgt.
  Proof.
    ii. eapply refinement_implies_simulation_aux; eauto; try by econs 1.
    ii. exploit REFINE; eauto. i. des. eauto.
  Qed.
End ADEQUACY.

Require Import JoinedView.
Require Import gSimulation.
Require Import SeqLift.
Require Import SeqLiftStep.
Require Import Configuration.
Require Import Behavior.
Require Import Memory.
Require Import Cell.
Require Import Time.

Lemma memory_init_get loc to from msg
      (GET: Memory.get loc to Memory.init = Some (from, msg))
  :
    to = Time.bot /\ from = Time.bot /\ msg = Message.elt.
Proof.
  unfold Memory.get, Memory.init in *.
  erewrite Cell.init_get in GET. des_ifs.
Qed.

Theorem seq_adequacy progs_src progs_tgt
        (TIDS: Threads.tids (Threads.init progs_src) = Threads.tids (Threads.init progs_tgt))
        (SEQREFINED: forall tid,
            option_rel
              (fun langsyn_src langsyn_tgt =>
                 match langsyn_src, langsyn_tgt with
                 | existT _ lang_src prog_src, existT _ lang_tgt prog_tgt =>
                   exists sim_terminal,
                   @sim_seq_all lang_src lang_tgt sim_terminal (@Language.init _ lang_src prog_src) (@Language.init _  lang_tgt prog_tgt)
                 end)
              (IdentMap.find tid progs_src)
              (IdentMap.find tid progs_tgt))
  :
    behaviors Configuration.step (Configuration.init progs_tgt) <2=
    behaviors Configuration.step (Configuration.init progs_src).
Proof.
  Opaque sim_thread_past.
  eapply sim_adequacy.
  { eapply world_messages_le_PreOrder. }
  { eapply Configuration.init_wf. }
  { eapply JConfiguration.init_wf. }
  { eapply Configuration.init_wf. }
  3:{
    eapply sim_thread_sim.
    { eapply world_messages_le_PreOrder. }
    { eapply world_messages_le_mon. }
    { eapply sim_local_memory_bot. }
    { eapply TIDS. }
    instantiate (1:=(fun _ => initial_mapping, initial_vers)).
    i. specialize (SEQREFINED tid).
    ss. unfold Threads.init in H, H0.
    rewrite IdentMap.Facts.map_o in *. unfold option_map in *.
    des_ifs. clarify.
    eapply inj_pair2 in H1. clarify.
    eapply inj_pair2 in H0.  clarify.
    setoid_rewrite Heq in SEQREFINED.
    setoid_rewrite Heq0 in SEQREFINED. ss. des_ifs. des.
    hexploit sim_lift_gsim.
    { eapply SEQREFINED. }
    i. ss. des. esplits; eauto.
    erewrite <- configuration_initial_finalized in H. eapply H.
  }
  { ss. red. i. red. esplits.
    { refl. }
    { refl. }
    { red. ss. }
    { ss. }
  }
  { ss. econs; ss.
    { i. esplits; eauto.
      { red. ss. des_ifs. eapply memory_init_get in GET. des; clarify. }
      { eapply memory_init_get in GET. des; clarify.
        econs; eauto. econs.
      }
      { eapply memory_init_get in GET. des; clarify. }
    }
    { i. eapply memory_init_get in GET. des; clarify. left.
      esplits; eauto.
      { refl. }
      { refl. }
      { left. esplits; eauto. }
      { red. ss. des_ifs. }
      { ii. inv ITV. ss. exfalso. timetac. }
    }
  }
  { econs.
    { ii. destruct (IdentMap.find tid (Threads.init progs_tgt)) eqn:EQ; ss.
      destruct p. destruct s. econs; eauto. destruct t. econs; eauto.
      { refl. }
      unfold Threads.init in EQ.
      rewrite IdentMap.Facts.map_o in EQ. unfold option_map in *. des_ifs.
      eapply inj_pair2 in H0. clarify. ii.
      rewrite Memory.bot_get. econs.
    }
    { refl. }
    { refl. }
  }
Qed.
