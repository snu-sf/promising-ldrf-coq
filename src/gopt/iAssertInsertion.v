From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Loc.
From PromisingLib Require Import Language.

From PromisingLib Require Import Event.
Require Import Time.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.
Require Import Behavior.

Require Import ITreeLang.

Require Import PromiseConsistent.
Require Import ReorderPromises.
Require Import FutureCertify.
Require Import SimpleSimulation.

Require Import Invariant.

Set Implicit Arguments.


Section AssertInsertion.
  Variable
    (S:ThreadsProp)
    (J:MemoryProp)
    (program: Threads.syntax).
  Variable R_tid: Ident.t -> Type.

  Context `{LOGIC: Logic.t S J program}.


  (* simulation relations on threads *)

  Variant _insert_assertion
            (insert_assertion: forall (tid: Ident.t) (itr_src: itree MemE.t (R_tid tid)) (itr_tgt: itree MemE.t (R_tid tid)), Prop)
            (tid: Ident.t): forall (itr_src: itree MemE.t (R_tid tid)) (itr_tgt: itree MemE.t (R_tid tid)), Prop :=
  | insert_assertion_ret
      (r: (R_tid tid)):
      @_insert_assertion insert_assertion tid (Ret r) (Ret r)
  | insert_assertion_tau
      itr_src itr_tgt
      (SIM: insert_assertion tid itr_src itr_tgt)
    :
      @_insert_assertion insert_assertion tid (tau;;itr_src) (tau;;itr_tgt)
  | insert_assertion_vis
      A ktr_src ktr_tgt (e: MemE.t A)
      (SIM: forall (v: A), insert_assertion tid (ktr_src v) (ktr_tgt v))
    :
      @_insert_assertion insert_assertion tid (Vis e ktr_src) (Vis e ktr_tgt)
  | insert_assertion_assert
      (itr_src itr_tgt: itree MemE.t (R_tid tid))
      (FAIL: ~ S tid (lang (R_tid tid)) itr_src)
    :
      @_insert_assertion insert_assertion tid itr_src itr_tgt
  .
  Hint Constructors _insert_assertion.

  Lemma insert_assertion_mon: monotone3 _insert_assertion.
  Proof.
    ii. destruct IN.
    - econs 1; eauto.
    - econs 2; eauto.
    - econs 3; eauto.
    - econs 4; eauto.
  Qed.
  Hint Resolve insert_assertion_mon: paco.

  Definition insert_assertion := paco3 _insert_assertion bot3.
  Arguments insert_assertion: clear implicits.

  Inductive sim_thread (tid: Ident.t)
            (e_src: Thread.t (lang (R_tid tid))) (e_tgt: Thread.t (lang (R_tid tid))): Prop :=
  | sim_thread_intro
      (STATE: insert_assertion tid (Thread.state e_src) (Thread.state e_tgt))
      (LOCAL: (Thread.local e_src) = (Thread.local e_tgt))
      (SC: (Thread.sc e_src) = (Thread.sc e_tgt))
      (MEMORY: (Thread.memory e_src) = (Thread.memory e_tgt))
  .
  Hint Constructors sim_thread.
  Arguments sim_thread: clear implicits.

  Lemma sim_state_step
        tid st1_src
        e st1_tgt st2_tgt
        (SIM1: insert_assertion tid st1_src st1_tgt)
        (STEP: (Language.step (lang (R_tid tid))) e st1_tgt st2_tgt):
    (exists st2_src,
        <<STEP_SRC: ILang.opt_step e st1_src st2_src>> /\
        <<SIM2: insert_assertion tid st2_src st2_tgt>>) \/
    (<<NSOUND: ~ S tid (lang (R_tid tid)) st1_src>>).
  Proof.
    punfold SIM1. dependent destruction SIM1; pclearbot; ss.
    - inv STEP.
    - left. exists itr_src.
      dependent destruction STEP. split; eauto.
      econs 2. econs; eauto.
    - dependent destruction STEP.
      + left. esplits; ss. econs 2. econs; eauto.
      + left. esplits; ss. econs 2. econs; eauto.
      + left. esplits; ss. econs 2. econs; eauto.
      + left. esplits; ss. econs 2. econs; eauto.
      + left. esplits; ss. econs 2. econs; eauto.
      + left. esplits; ss. econs 2. econs; eauto.
      + left. esplits; ss. econs 2. econs; eauto.
      + left. esplits; ss. econs 2. econs; eauto.
        pcofix CIH. pfold. rewrite unfold_spin. econs. auto.
    - auto.
  Qed.

  Lemma sim_thread_promise_step
        tid e1_src
        pf e e1_tgt e2_tgt
        (SIM1: sim_thread tid e1_src e1_tgt)
        (STEP_TGT: Thread.promise_step pf e e1_tgt e2_tgt):
    exists e2_src,
      <<STEP_SRC: Thread.promise_step pf e e1_src e2_src>> /\
      <<SIM2: sim_thread tid e2_src e2_tgt>>.
  Proof.
    destruct e1_src, e1_tgt, e2_tgt. ss.
    inv SIM1. ss. subst.
    inv STEP_TGT; ss.
    esplits.
    - econs; eauto.
    - eauto.
  Qed.

  Lemma sim_thread_program_step
        tid e1_src
        e e1_tgt e2_tgt
        (SIM1: sim_thread tid e1_src e1_tgt)
        (STEP_TGT: Thread.program_step e e1_tgt e2_tgt):
    (exists e2_src,
        <<STEP_SRC: Thread.opt_program_step e e1_src e2_src>> /\
        <<SIM2: sim_thread tid e2_src e2_tgt>>) \/
    (<<NSOUND: ~ S tid (lang (R_tid tid)) (Thread.state e1_src)>>).
  Proof.
    destruct e1_src, e1_tgt, e2_tgt. ss.
    inv SIM1. ss. subst.
    dependent destruction STEP_TGT; ss.
    exploit sim_state_step; eauto. i. des; cycle 1.
    { right. esplits; eauto. }
    left. inv LOCAL; dependent destruction STEP_SRC; ss.
    - esplits.
      + econs 1.
      + econs; eauto.
    - esplits.
      + econs 2. econs; eauto.
      + econs; eauto.
    - esplits.
      + econs 2. econs; eauto.
      + econs; eauto.
    - esplits.
      + econs 2. econs; eauto.
      + econs; eauto.
    - esplits.
      + econs 2. econs; eauto.
      + econs; eauto.
    - esplits.
      + econs 2. econs; eauto.
      + econs; eauto.
    - esplits.
      + econs 2. econs; eauto.
      + econs; eauto.
    - esplits.
      + econs 2. econs; eauto.
      + econs; eauto.
  Qed.

  Lemma sim_thread_step
        tid e1_src
        pf e e1_tgt e2_tgt
        (SIM1: sim_thread tid e1_src e1_tgt)
        (STEP_TGT: Thread.step pf e e1_tgt e2_tgt):
    (exists e2_src,
        <<STEP_SRC: Thread.opt_step e e1_src e2_src>> /\
        <<SIM2: sim_thread tid e2_src e2_tgt>>) \/
    (<<NSOUND: ~ S tid (lang (R_tid tid)) (Thread.state e1_src)>>).
  Proof.
    inv STEP_TGT.
    - left.
      exploit sim_thread_promise_step; eauto. i. des.
      esplits; eauto.
      econs 2. econs 1. eauto.
    - exploit sim_thread_program_step; eauto. i. des.
      + left. esplits; eauto.
        inv STEP_SRC.
        * econs 1.
        * econs 2. econs 2. eauto.
      + right. esplits; eauto.
  Qed.

  Lemma sim_thread_rtc_tau_step
        tid e1_src e1_tgt e2_tgt
        (SIM1: sim_thread tid e1_src e1_tgt)
        (STEPS_TGT: rtc (@Thread.tau_step (lang (R_tid tid))) e1_tgt e2_tgt):
    (exists e2_src,
        <<STEPS_SRC: rtc (@Thread.tau_step (lang (R_tid tid))) e1_src e2_src>> /\
        <<SIM2: sim_thread tid e2_src e2_tgt>>) \/
    (exists e_src e_tgt,
        <<STEPS1_TGT: rtc (@Thread.tau_step (lang (R_tid tid))) e1_tgt e_tgt>> /\
        <<STEPS2_TGT: rtc (@Thread.tau_step (lang (R_tid tid))) e_tgt e2_tgt>> /\
        <<STEPS_SRC: rtc (@Thread.tau_step (lang (R_tid tid))) e1_src e_src>> /\
        <<SIM: sim_thread tid e_src e_tgt>> /\
        <<NSOUND: ~ S tid (lang (R_tid tid)) (Thread.state e_src)>>).
  Proof.
    revert e1_src SIM1.
    induction STEPS_TGT; eauto; i.
    inv H. inv TSTEP.
    exploit sim_thread_step; eauto. i. des.
    - exploit IHSTEPS_TGT; eauto. i. des.
      + left. esplits; [|eauto].
        inv STEP_SRC; eauto.
        econs 2; eauto.
        econs; [econs; eauto|ss].
      + right.
        esplits; try exact STEPS2_TGT; try exact SIM; eauto.
        * econs 2; eauto.
          econs; [econs; eauto|ss].
        * inv STEP_SRC; eauto.
          econs 2; eauto.
          econs; [econs; eauto|ss].
    - right.
      esplits; try exact SIM1; eauto.
      econs 2; eauto.
      econs; [econs; eauto| ss].
  Qed.

  Lemma sim_thread_rtc_program_step
        tid e1_src e1_tgt e2_tgt
        (SIM1: sim_thread tid e1_src e1_tgt)
        (STEPS_TGT: rtc (tau (@Thread.program_step (lang (R_tid tid)))) e1_tgt e2_tgt):
    (exists e2_src,
        <<STEPS_SRC: rtc (tau (@Thread.program_step (lang (R_tid tid)))) e1_src e2_src>> /\
        <<SIM2: sim_thread tid e2_src e2_tgt>>) \/
    (exists e_src e_tgt,
        <<STEPS1_TGT: rtc (tau (@Thread.program_step (lang (R_tid tid)))) e1_tgt e_tgt>> /\
        <<STEPS2_TGT: rtc (tau (@Thread.program_step (lang (R_tid tid)))) e_tgt e2_tgt>> /\
        <<STEPS_SRC: rtc (tau (@Thread.program_step (lang (R_tid tid)))) e1_src e_src>> /\
        <<SIM: sim_thread tid e_src e_tgt>> /\
        <<NSOUND: ~ S tid (lang (R_tid tid)) (Thread.state e_src)>>).
  Proof.
    revert e1_src SIM1.
    induction STEPS_TGT; eauto; i.
    inv H.
    exploit sim_thread_program_step; eauto. i. des.
    - exploit IHSTEPS_TGT; eauto. i. des.
      + left. esplits; [|eauto].
        inv STEP_SRC; eauto.
      + right.
        esplits; try exact STEPS2_TGT; try exact SIM; eauto.
        inv STEP_SRC; eauto.
    - right.
      esplits; try exact SIM1; eauto.
  Qed.


  (* simulation relation on configurations *)

  Inductive sim_conf (c_src c_tgt: Configuration.t): Prop :=
  | sim_conf_intro
      (SEM: sem S J c_src)
      (TIDS: Threads.tids (Configuration.threads c_src) = Threads.tids (Configuration.threads c_tgt))
      (FIND_SRC: forall tid l st_src lc_src
                        (FIND: IdentMap.find tid (Configuration.threads c_src) = Some (existT _ l st_src, lc_src)),
          l = lang (R_tid tid))
      (FIND_TGT: forall tid l st_tgt lc_tgt
                   (FIND: IdentMap.find tid (Configuration.threads c_tgt) = Some (existT _ l st_tgt, lc_tgt)),
          l = lang (R_tid tid))
      (THREADS: forall tid st_src lc_src st_tgt lc_tgt
                  (FIND_SRC: IdentMap.find tid (Configuration.threads c_src) = Some (existT _ (lang (R_tid tid)) st_src, lc_src))
                  (FIND_TGT: IdentMap.find tid (Configuration.threads c_tgt) = Some (existT _ (lang (R_tid tid)) st_tgt, lc_tgt)),
          <<STATE: insert_assertion tid st_src st_tgt>> /\
          <<LOCAL: lc_src = lc_tgt>>)
      (SC: (Configuration.sc c_src) = (Configuration.sc c_tgt))
      (MEMORY: (Configuration.memory c_src) = (Configuration.memory c_tgt))
  .
  Hint Constructors sim_conf.


  Lemma sim_conf_find
        c_src c_tgt tid
        (SIM: sim_conf c_src c_tgt):
    (exists lang_src st_src lc_src,
        IdentMap.find tid (Configuration.threads c_src) = Some (existT _ lang_src st_src, lc_src)) <->
    (exists lang_tgt st_tgt lc_tgt,
        IdentMap.find tid (Configuration.threads c_tgt) = Some (existT _ lang_tgt st_tgt, lc_tgt)).
  Proof.
    inv SIM. destruct c_src, c_tgt. ss.
    eapply Threads.tids_find; eauto.
  Qed.

  Lemma sim_conf_sim_thread
        c_src c_tgt
        tid st_src lc_src st_tgt lc_tgt
        (SIM: sim_conf c_src c_tgt)
        (FIND_SRC: IdentMap.find tid (Configuration.threads c_src) = Some (existT _ (lang (R_tid tid)) st_src, lc_src))
        (FIND_TGT: IdentMap.find tid (Configuration.threads c_tgt) = Some (existT _ (lang (R_tid tid)) st_tgt, lc_tgt)):
    sim_thread tid
               (Thread.mk (lang (R_tid tid)) st_src lc_src (Configuration.sc c_src) (Configuration.memory c_src))
               (Thread.mk (lang (R_tid tid)) st_tgt lc_tgt (Configuration.sc c_tgt) (Configuration.memory c_tgt)).
  Proof.
    inv SIM. exploit THREADS; eauto. i. des.
    econs; eauto.
  Qed.

  Lemma sim_conf_sim
        c_src c_tgt
        (SIM: sim_conf c_src c_tgt):
    sim c_src c_tgt.
  Proof.
    revert c_src c_tgt SIM.
    pcofix CIH. i. pfold. econs; ii.
    { (* terminal *)
      esplits; eauto. ii.
      exploit sim_conf_find; eauto. i. des.
      exploit x0; eauto. i. des.
      inv SIM. ss.
      exploit FIND_SRC; eauto. i. des. subst.
      exploit FIND_TGT; eauto. i. des. subst.
      exploit THREADS; eauto. i. des. subst.
      exploit TERMINAL_TGT; eauto. i. des.
      split; auto.
      inv STATE0. ss. subst.
      punfold STATE. dependent destruction STATE.
      { econs; eauto. }
      { inv SEM. exploit TH; eauto. ss. }
    }

    inv STEP_TGT.
    { (* failure step *)
      exploit sim_conf_find; eauto. i. des.
      exploit x1; eauto. i. des. clear x0 x1.
      destruct c_src as [ths1_src sc1_src mem1_src].
      destruct c_tgt as [ths1_tgt sc1 mem1].
      dup SIM. inv SIM0. ss. subst.
      exploit FIND_SRC; eauto. i. des. subst.
      exploit FIND_TGT; eauto. i. des. subst.
      clear FIND_SRC FIND_TGT THREADS.
      exploit sim_conf_sim_thread; eauto. s. intro SIM_TH.
      exploit sim_thread_rtc_tau_step; eauto. i. des.
      - exploit sim_thread_step; eauto. i. des; cycle 1.
        { destruct e2. ss. subst.
          inv STEP; inv STEP0. ss. dependent destruction STATE.
          inv SEM. dup x. eapply TH in x. inv WF_SRC.
          exploit rtc_thread_step_sem_thread; try eapply rtc_implies; try exact STEPS_SRC; eauto.
          { eapply WF; eauto. }
          { i. inv H. econs. eauto. }
          { inv SIM2. ss. subst. inv LOCAL. inv LOCAL0. ss. }
          i. des. ss.
        }
        inv STEP_SRC. destruct e2_src0. ss.
        assert (CSTEP: Configuration.step
                         MachineEvent.failure tid
                         (Configuration.mk ths1_src sc1 mem1)
                         (Configuration.mk
                            (IdentMap.add tid (existT (fun (lang: language) => (Language.state lang)) (lang (R_tid tid)) state0, local) ths1_src)
                            sc memory)).
        { econs 1; eauto. }
        esplits; [econs 2; eauto|].
        right. apply CIH. econs; ss; try by (inv SIM0; ss).
        + eapply configuration_step_sem; try exact CSTEP; eauto.
        + repeat rewrite Threads.tids_add.
          repeat rewrite IdentSet.add_mem; ss.
          * rewrite Threads.tids_o. rewrite TID. ss.
          * rewrite Threads.tids_o. rewrite x. ss.
        + i. revert FIND. rewrite IdentMap.gsspec. condtac; ss; i.
          * inv FIND. eauto.
          * inv SIM. eapply FIND_SRC; eauto.
        + i. revert FIND. rewrite IdentMap.gsspec. condtac; ss; i.
          * inv FIND. eauto.
          * inv SIM. eapply FIND_TGT; eauto.
        + i. revert FIND_SRC. rewrite IdentMap.gsspec. condtac; ss; i.
          * subst. revert FIND_TGT. rewrite IdentMap.gsspec. condtac; ss; i.
            Configuration.simplify2. inv SIM0. ss.
          * revert FIND_TGT. rewrite IdentMap.gsspec. condtac; ss; i.
            inv SIM. eauto.
      - exfalso.
        dup WF_TGT. inv WF_TGT0. inv WF. ss. clear DISJOINT.
        exploit THREADS; eauto. intro WF1_TGT. clear THREADS.
        dup WF_SRC. inv WF_SRC0. inv WF. ss. clear DISJOINT.
        exploit THREADS; eauto. intro WF1_SRC. clear THREADS.
        exploit tau_steps_pf_tau_steps_state; try exact STEPS_SRC; eauto.
        { exploit Thread.rtc_tau_step_future; try exact STEPS1_TGT; eauto. s. i. des.
          inv SIM0. rewrite LOCAL.
          inv STEP; inv STEP0. inv LOCAL0. inv LOCAL1.
          eapply rtc_tau_step_promise_consistent; eauto. }
        i. des.
        inv SEM. ss. exploit TH; eauto. i.
        exploit rtc_thread_step_sem; try eapply rtc_implies; try exact STEPS1; eauto.
        { i. inv H. econs. eauto. }
        i. des. ss. rewrite STATE in *. ss.
    }

    (* normal step *)
    exploit sim_conf_find; eauto. i. des.
    exploit x1; eauto. i. des. clear x0 x1.
    destruct c_src as [ths1_src sc1_src mem1_src].
    destruct c_tgt as [ths1_tgt sc1 mem1].
    dup SIM. inv SIM0. ss. subst.
    exploit FIND_SRC; eauto. i. subst.
    exploit FIND_TGT; eauto. i. subst.
    clear FIND_SRC FIND_TGT THREADS.
    exploit sim_conf_sim_thread; eauto. s. intro SIM_TH.
    dup WF_TGT. inv WF_TGT0. inv WF. ss. clear DISJOINT.
    exploit THREADS; eauto. intro WF1_TGT. clear THREADS.
    dup WF_SRC. inv WF_SRC0. inv WF. ss. clear DISJOINT.
    exploit THREADS; eauto. intro WF1_SRC. clear THREADS.
    exploit Thread.rtc_tau_step_future; eauto. s. i. des.
    exploit Thread.step_future; eauto. s. i. des.
    exploit sim_thread_rtc_tau_step; eauto. i. des; cycle 1.
    { exfalso.
      exploit tau_steps_pf_tau_steps_state; try exact STEPS_SRC; eauto.
      { exploit Thread.rtc_tau_step_future; try exact STEPS1_TGT; eauto. s. i. des.
        inv SIM0. rewrite LOCAL.
        eapply rtc_tau_step_promise_consistent; eauto.
        eapply step_promise_consistent; eauto.
        eapply consistent_promise_consistent; eauto. }
      i. des.
      inv SEM. ss. exploit TH; eauto. i.
      exploit rtc_thread_step_sem; try eapply rtc_implies; try exact STEPS1; eauto.
      { i. inv H. econs. eauto. }
      i. des. rewrite STATE in *. ss.
    }
    exploit sim_thread_step; eauto. i. des; cycle 1.
    { exfalso.
      exploit tau_steps_pf_tau_steps_state; try exact STEPS_SRC; eauto.
      { exploit Thread.rtc_tau_step_future; try exact STEPS1_TGT; eauto. s. i. des.
        inv SIM2. rewrite LOCAL.
        eapply rtc_tau_step_promise_consistent; eauto.
        eapply step_promise_consistent; eauto.
        eapply consistent_promise_consistent; eauto. }
      i. des.
      inv SEM. ss. exploit TH; eauto. i.
      exploit rtc_thread_step_sem; try eapply rtc_implies; try exact STEPS1; eauto.
      { i. inv H. econs. eauto. }
      i. des. rewrite STATE in *. ss.
    }

    (* certification for normal step *)
    destruct e2_src0.
    assert (CONSISTENT_SRC: Thread.consistent (Thread.mk (lang (R_tid tid)) state0 local sc memory)).
    { dup SIM0. inv SIM1. ss. subst. ii. ss.
      exploit Memory.cap_closed; eauto. intro CLOSED_CAP.
      exploit Local.cap_wf; try exact WF0; eauto. intro WF_CAP.
      hexploit Memory.max_concrete_timemap_closed; eauto. intro SC_MAX_CLOSED.
      exploit CONSISTENT; eauto. s. i. des.
      - (* failure certification *)
        left. unfold Thread.steps_failure in *. des.
        exploit (@sim_thread_rtc_tau_step tid (Thread.mk (lang (R_tid tid)) state0 lc3 sc0 mem0));
          try exact STEPS0; try by (econs; eauto).
        i. des; cycle 1.
        { exfalso.
          exploit (@FutureCertify.cap_steps_current_steps (lang (R_tid tid)) (Thread.mk (lang (R_tid tid)) state0 lc3 sc3 memory3));
            try exact STEPS_SRC0; eauto.
          { exploit Thread.rtc_tau_step_future; try exact STEPS1_TGT; eauto. s. i. des.
            inv SIM1. rewrite LOCAL.
            eapply rtc_tau_step_promise_consistent; eauto.
            inv FAILURE0; inv STEP0. inv LOCAL0. inv LOCAL1. ss. }
          i. des.
          exploit Thread.tau_opt_all; try exact STEPS_SRC; eauto. i.
          exploit rtc_implies; try eapply STEPS1; i; [|erewrite x2 in x1].
          { inv H. econs. eauto. }
          exploit steps_pf_steps_state; try exact x1; eauto. i. des.
          inv SEM. ss. exploit TH; eauto. i.
          exploit rtc_thread_step_sem; try exact STEPS2; eauto. i. des.
          rewrite STATE0 in *. ss.
        }
        exploit sim_thread_step; try exact SIM1; eauto. i. des; cycle 1.
        { exfalso.
          exploit (@FutureCertify.cap_steps_current_steps (lang (R_tid tid)) (Thread.mk (lang (R_tid tid)) state0 lc3 sc3 memory3));
            try exact STEPS_SRC0; eauto.
          { exploit Thread.rtc_tau_step_future; try exact STEPS0; eauto. s. i. des.
            inv SIM1. rewrite LOCAL.
            eapply rtc_tau_step_promise_consistent; eauto.
            inv FAILURE0; inv STEP0. inv LOCAL0. inv LOCAL1. ss. }
          i. des.
          exploit Thread.tau_opt_all; try exact STEPS_SRC; eauto. i.
          exploit rtc_implies; try eapply STEPS1; i; [|erewrite x2 in x1].
          { inv H. econs. eauto. }
          exploit steps_pf_steps_state; try exact x1; eauto. i. des.
          inv SEM. ss. exploit TH; eauto. i.
          exploit rtc_thread_step_sem; try exact STEPS2; eauto. i. des.
          rewrite STATE0 in *. ss.
        }
        inv STEP_SRC0. destruct pf0; try by (inv STEP0; inv STEP1).
        esplits; eauto.
      - (* normal certification *)
        right.
        exploit (@sim_thread_rtc_tau_step tid (Thread.mk (lang (R_tid tid)) state0 lc3 sc0 mem0));
          try exact STEPS0; try by (econs; eauto).
        i. des; cycle 1.
        { exfalso.
          exploit (@FutureCertify.cap_steps_current_steps (lang (R_tid tid)) (Thread.mk (lang (R_tid tid)) state0 lc3 sc3 memory3));
            try exact STEPS_SRC0; eauto.
          { exploit Thread.rtc_tau_step_future; try exact STEPS1_TGT; eauto. s. i. des.
            inv SIM1. rewrite LOCAL.
            eapply rtc_tau_step_promise_consistent; eauto.
            ii. rewrite PROMISES in *. rewrite Memory.bot_get in *. ss. }
          i. des.
          exploit Thread.tau_opt_all; try exact STEPS_SRC; eauto. i.
          exploit rtc_implies; try eapply STEPS1; i; [|erewrite x2 in x1].
          { inv H. econs. eauto. }
          exploit steps_pf_steps_state; try exact x1; eauto. i. des.
          inv SEM. ss. exploit TH; eauto. i.
          exploit rtc_thread_step_sem; try exact STEPS2; eauto. i. des.
          rewrite STATE0 in *. ss.
        }
        esplits; eauto.
        inv SIM1. rewrite LOCAL. ss.
    }
    assert (CSTEP: Configuration.opt_step
                     (ThreadEvent.get_machine_event e0) tid
                     (Configuration.mk ths1_src sc1 mem1)
                     (Configuration.mk
                        (IdentMap.add tid (existT (fun (lang: language) => (Language.state lang)) (lang (R_tid tid)) state0, local) ths1_src)
                        sc memory)).
    { inv STEP_SRC.
      - generalize (rtc_tail STEPS_SRC). i. des.
        + inv H0. inv TSTEP. ss. rewrite <- EVENT0.
          econs 2. econs; try exact x; try exact H; eauto.
          destruct e; ss.
        + inv H. ss.
          replace (IdentMap.add
                     tid
                     (existT (fun lang:language => (Language.state lang)) (lang (R_tid tid)) state0, local)
                     ths1_src)
            with ths1_src; eauto.
          apply IdentMap.eq_leibniz. ii.
          rewrite -> IdentMap.gsident; auto.
      - econs 2. econs 2; try exact x; try exact H; eauto.
    }
    esplits; eauto.
    right. apply CIH. econs; ss; try by (inv SIM0; ss).
    - inv CSTEP; ss.
      + repeat rewrite <- H. ss.
      + eapply configuration_step_sem; try exact STEP0; eauto.
    - repeat rewrite Threads.tids_add.
      repeat rewrite IdentSet.add_mem; ss.
      + rewrite Threads.tids_o. rewrite TID. ss.
      + rewrite Threads.tids_o. rewrite x. ss.
    - i. revert FIND. rewrite IdentMap.gsspec. condtac; ss; i.
      + inv FIND. ss.
      + inv SIM. eapply FIND_SRC; eauto.
    - i. revert FIND. rewrite IdentMap.gsspec. condtac; ss; i.
      + inv FIND. ss.
      + inv SIM. eapply FIND_TGT; eauto.
    - i. revert FIND_SRC. rewrite IdentMap.gsspec. condtac; ss; i.
      + subst. revert FIND_TGT. rewrite IdentMap.gsspec. condtac; ss; i.
        Configuration.simplify2. inv SIM0. ss.
      + revert FIND_TGT. rewrite IdentMap.gsspec. condtac; ss; i.
        inv SIM. eauto.
  Qed.


  (* assert insertion *)

  Definition syntax_tids (pgm: Threads.syntax): IdentSet.t :=
    List.fold_right (fun p s => IdentSet.add (fst p) s) IdentSet.empty (IdentMap.elements pgm).

  Lemma syntax_tids_o tid pgm:
    IdentSet.mem tid (syntax_tids pgm) = IdentMap.find tid pgm.
  Proof.
    unfold syntax_tids. rewrite IdentMap.Facts.elements_o.
    induction (IdentMap.elements pgm); ss. destruct a. s.
    rewrite IdentSet.Facts.add_b, IHl.
    unfold IdentSet.Facts.eqb, IdentMap.Facts.eqb.
    repeat match goal with
           | [|- context[if ?c then true else false]] => destruct c
           end; ss; congr.
  Qed.

  Inductive insert_assertion_program (program_tgt: Threads.syntax): Prop :=
  | insert_assertion_program_intro
      (TIDS: syntax_tids program_tgt = syntax_tids program)
      (FIND_SRC: forall tid l syn_src
                   (FIND: IdentMap.find tid program = Some (existT _ l syn_src)),
          l = lang (R_tid tid))
      (FIND_TGT: forall tid l syn_tgt
                   (FIND: IdentMap.find tid program_tgt = Some (existT _ l syn_tgt)),
          l = lang (R_tid tid))
      (THREADS: forall tid syn_src syn_tgt
                  (FIND_SRC: IdentMap.find tid program = Some (existT _ (lang (R_tid tid)) syn_src))
                  (FIND_TGT: IdentMap.find tid program_tgt = Some (existT _ (lang (R_tid tid)) syn_tgt)),
          insert_assertion tid syn_src syn_tgt)
  .

  Lemma init_sim_conf
        program_tgt
        (INSERT: insert_assertion_program program_tgt):
    sim_conf (Configuration.init program) (Configuration.init program_tgt).
  Proof.
    inv INSERT. econs; ss; i.
    - apply init_sem; ss.
    - apply IdentSet.ext. i.
      repeat rewrite Threads.tids_o.
      unfold Threads.init.
      repeat rewrite IdentMap.Facts.map_o.
      specialize (@syntax_tids_o i program). i.
      specialize (@syntax_tids_o i program_tgt). i.
      destruct (@UsualFMapPositive.UsualPositiveMap'.find
                  (@sigT _ (@Language.syntax ProgramEvent.t)) i program) eqn:SRC;
        destruct (@UsualFMapPositive.UsualPositiveMap'.find
                    (@sigT _ (@Language.syntax ProgramEvent.t)) i program_tgt) eqn:TGT; ss.
      + assert (@UsualFMapPositive.UsualPositiveMap'.find
                  (@sigT _ (@Language.syntax ProgramEvent.t)) i program = IdentMap.find i program) by ss.
        rewrite <- H1 in *. rewrite SRC in *. ss.
        assert (@UsualFMapPositive.UsualPositiveMap'.find
                  (@sigT _ (@Language.syntax ProgramEvent.t)) i program_tgt = IdentMap.find i program_tgt) by ss.
        rewrite <- H2 in *. rewrite TGT in *. ss.
        rewrite TIDS in *. congr.
      + assert (@UsualFMapPositive.UsualPositiveMap'.find
                  (@sigT _ (@Language.syntax ProgramEvent.t)) i program = IdentMap.find i program) by ss.
        rewrite <- H1 in *. rewrite SRC in *. ss.
        assert (@UsualFMapPositive.UsualPositiveMap'.find
                  (@sigT _ (@Language.syntax ProgramEvent.t)) i program_tgt = IdentMap.find i program_tgt) by ss.
        rewrite <- H2 in *. rewrite TGT in *. ss.
        rewrite TIDS in *. congr.
    - unfold Threads.init in *.
      rewrite IdentMap.Facts.map_o in *.
      destruct (@UsualFMapPositive.UsualPositiveMap'.find
                  (@sigT _ (@Language.syntax ProgramEvent.t)) tid program) eqn:SRC; ss.
      destruct s. ss. inv FIND. eapply FIND_SRC; eauto.
    - unfold Threads.init in *.
      rewrite IdentMap.Facts.map_o in *.
      destruct (@UsualFMapPositive.UsualPositiveMap'.find
                  (@sigT _ (@Language.syntax ProgramEvent.t)) tid program_tgt) eqn:SRC; ss.
      destruct s. ss. inv FIND. eapply FIND_TGT; eauto.
    - unfold Threads.init in *.
      rewrite IdentMap.Facts.map_o in *.
      destruct (@UsualFMapPositive.UsualPositiveMap'.find
                  (@sigT _ (@Language.syntax ProgramEvent.t)) tid program) eqn:SRC;
        destruct (@UsualFMapPositive.UsualPositiveMap'.find
                    (@sigT _ (@Language.syntax ProgramEvent.t)) tid program_tgt) eqn:TGT; ss.
      destruct s, s0; ss.
      inv FIND_SRC0. inv FIND_TGT0. split; ss. Configuration.simplify2.
      eapply THREADS; eauto.
  Qed.

  Theorem insert_assertion_behavior
          program_tgt
          (INSERT: insert_assertion_program program_tgt):
    behaviors Configuration.step (Configuration.init program_tgt) <1=
    behaviors Configuration.step (Configuration.init program).
  Proof.
    exploit init_sim_conf; eauto. i.
    specialize (Configuration.init_wf program). intro WF_SRC.
    specialize (Configuration.init_wf program_tgt). intro WF_TGT.
    hexploit sim_conf_sim; eauto. i.
    exploit sim_adequacy; try exact H; eauto.
  Qed.
End AssertInsertion.
