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

  Lemma seq_event_input_match_to_oracle_input_le
        d d1 i_src i_tgt i0
        (MATCH: SeqEvent.input_match d d1 i_src i_tgt)
        (INPUT: Oracle.input_le i0 (SeqEvent.get_oracle_input i_tgt))
    :
    Oracle.input_le i0 (SeqEvent.get_oracle_input i_src).
  Proof.
    destruct i_src, i_tgt. inv MATCH. ss.
    destruct i0; ss.
    unfold SeqEvent.get_oracle_input, Oracle.input_le in *. ss. des. splits.
    - clear - ACCESS ACCESS0. destruct in_access, in_access0, in_access1; ss; clarify.
      + unfold Oracle.in_access_le in *. des_ifs. des. clarify; ss.
        inv ACCESS. splits; auto. etrans; eauto.
        etrans. 2: eauto. etrans. eauto. apply Flag.join_ge_l.
      + inv ACCESS.
      + inv ACCESS.
    - clear - ACQUIRE ACQUIRE0. destruct in_acquire, in_acquire0, in_acquire1; ss; clarify.
      + inv ACQUIRE.
      + inv ACQUIRE.
    - clear - RELEASE RELEASE0. destruct in_release, in_release0, in_release1; ss; clarify.
      + inv RELEASE.
      + inv RELEASE.
  Qed.

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


  Lemma simulation_implies_refinement_aux
        (st_src: lang_src.(Language.state)) (st_tgt: lang_tgt.(Language.state))
        p d m_src m_tgt
        (SIM: sim_seq (fun _ _ => True) p d (SeqState.mk _ st_src m_src) (SeqState.mk _ st_tgt m_tgt))
        o (WF: Oracle.wf o)
        (* (RECEPTIVE: receptive _ st_tgt) (*maybe not needed*) *)
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
        2: refl. auto.
        (* { replace state0 with (SeqState.state (SeqState.mk _ state0 memory)). 2: ss. eapply rtc_na_step_receptive. *)
        (*   { instantiate (1:= (SeqState.mk _ st_tgt m_tgt)). ss. } *)
        (*   econs. eauto. refl. *)
        (* } *)
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

    2:{ i. clarify; ss.
        punfold SIM. inv SIM.
        2:{ eapply sim_fail_ub; eauto. }
        inv STEP.
        clear TERMINAL NASTEP PARTIAL. unfold sim_seq_at_step_case in ATSTEP. ss.
        hexploit ATSTEP; clear ATSTEP.
        1,2: eauto.
        i; des.
        hexploit SIM; clear SIM.
        1: eauto.
        { punfold WF. inv WF. hexploit WF0; eauto. i; des. rewrite <- le_wf_output.
          2: eapply EVENT. eauto. }
        eauto.
        i; des. pclearbot.
        hexploit IHbehavior; clear IHbehavior.
        2: refl.
        { clear - WF ORACLE. punfold WF. inv WF. hexploit WF0; eauto. i; des. pclearbot. auto. }
        (* { eapply step_receptive; eauto. } *)
        eauto.
        i; des. destruct tr1, st_src1. esplits.
        - eapply na_steps_behavior. eauto. eapply SeqBehavior.behavior_at_step.
          2: eauto.
          ss. econs. eauto.
          { rewrite <- le_is_atomic. eauto. etrans; eauto. refl. }
          4,5: eauto.
          3: eauto.
          etrans; eauto. eapply seq_event_input_match_to_oracle_input_le; eauto.
        - econs 4. eauto. auto. auto.
    }

    { i. clarify; ss.
      punfold SIM. inv SIM.
      2:{ eapply sim_fail_ub; eauto. }
      clear TERMINAL NASTEP ATSTEP. unfold sim_seq_partial_case in PARTIAL. ss.
      hexploit PARTIAL; clear PARTIAL. eauto. i; des.
      2:{ destruct th. destruct state0. hexploit (SeqBehavior.behavior_ub FAILURE).
          i. esplits.
          - eapply thread_steps_app_behavior. 2: eapply H. eauto.
          - econs 3. rewrite app_nil_r. eauto.
      }
      destruct th. destruct state0. destruct memory. ss.
      esplits.
      - eapply thread_steps_app_behavior. eauto. econs 2.
      - rewrite app_nil_r. econs 2. eauto. auto.
    }

  Qed.

  Theorem simulation_implies_refinement
          (st_src: lang_src.(Language.state)) (st_tgt: lang_tgt.(Language.state))
          (SIM: sim_seq_all _ _ (fun _ _ => True) st_src st_tgt)
          (* (RECEPTIVE: receptive _ st_tgt) (*maybe not needed*) *)
    :
      SeqBehavior.refine _ _ st_tgt st_src.
  Proof.
    unfold SeqBehavior.refine. i. eapply simulation_implies_refinement_aux. 2: auto.
    unfold sim_seq_all in SIM. eauto.
  Qed.

End ADEQUACY2.
