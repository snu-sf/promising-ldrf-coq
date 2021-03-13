Require Import Omega.
Require Import Bool.
Require Import RelationClasses.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Language.
From PromisingLib Require Import Loc.

Require Import Event.
Require Import Time.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.
Require Import Trace.
Require Import Behavior.
Require Import Single.
Require Import Mapping.

Set Implicit Arguments.

Module SemiReachable.
  Section REACHABLE.

    Variable (c0: Configuration.t).

    Hypothesis CONFIG_CONSISTENT: forall tid lang st lc
                                         (TID: IdentMap.find tid (Configuration.threads c0) = Some (existT _ lang st, lc)),
        Local.promise_consistent lc.
    Hypothesis CONFIG_WF: Configuration.wf c0.

    Section TID.

      Variable (tid: Ident.t).

      Inductive semi_reachable lang (th: Thread.t lang): Prop :=
      | semi_reachable_intro
          c1 st1 lc1
          (STEPS: rtc SConfiguration.all_machine_step c0 c1)
          (TID: IdentMap.find tid (Configuration.threads c1) = Some (existT _ lang st1, lc1))
          (TSTEPS: rtc (@Thread.all_step _) (Thread.mk _ st1 lc1 (Configuration.sc c1) (Configuration.memory c1)) th)
          (CONSISTENT: Local.promise_consistent (Thread.local th))
      .
      Hint Constructors semi_reachable.

      Inductive semi_reachable_state
                (lang: language) (st: @Language.state _ lang): Prop :=
      | semi_reachable_stateintro
          lc sc mem
          (REACHABLE: semi_reachable (Thread.mk _ st lc sc mem))
        :
          semi_reachable_state _ st
      .
      Hint Constructors semi_reachable_state.

      Inductive step lang: forall (pf: bool) (e: ThreadEvent.t) (th0 th1: Thread.t lang), Prop :=
      | step_intro
          pf e th0 th1
          (STEP: Thread.step pf e th0 th1)
          (REACHABLE: semi_reachable_state lang (Thread.state th1))
        :
          step pf e th0 th1
      .
      Hint Constructors step.

      Inductive opt_step lang: forall (e:ThreadEvent.t) (e1 e2:Thread.t lang), Prop :=
      | step_none
          e:
          opt_step ThreadEvent.silent e e
      | step_some
          pf e e1 e2
          (STEP: step pf e e1 e2):
          opt_step e e1 e2
      .
      Hint Constructors opt_step.

      Inductive step_allpf lang (e:ThreadEvent.t) (e1 e2:Thread.t lang): Prop :=
      | step_nopf_intro
          pf
          (STEP: step pf e e1 e2)
      .
      Hint Constructors step_allpf.

      Definition tau_step lang := tau (@step_allpf lang).

      Inductive reserve_step lang (e1 e2:Thread.t lang): Prop :=
      | reserve_step_intro
          pf loc from to
          (STEP: step pf (ThreadEvent.promise loc from to Message.reserve Memory.op_kind_add) e1 e2)
      .
      Hint Constructors reserve_step.

      Inductive cancel_step lang (e1 e2:Thread.t lang): Prop :=
      | cancel_step_intro
          pf loc from to
          (STEP: step pf (ThreadEvent.promise loc from to Message.reserve Memory.op_kind_cancel) e1 e2)
      .
      Hint Constructors cancel_step.

      Lemma step_reachable lang pf e (th0 th1: Thread.t lang)
            (STEP: Thread.step pf e th0 th1)
            (CONSISTENT: Local.promise_consistent (Thread.local th1))
            (REACHABLE: semi_reachable th0)
        :
          (<<STEP: step pf e th0 th1>>) /\
          (<<REACHABLE: semi_reachable th1>>).
      Proof.
        inv REACHABLE.
        assert (REACHABLE0: semi_reachable th1).
        { econs; eauto. etrans; eauto. econs 2; [|refl]. econs; eauto. econs; eauto. }
        splits; auto. econs; eauto. destruct th1. econs; eauto.
      Qed.

      Lemma opt_step_reachable lang e (th0 th1: Thread.t lang)
            (STEP: Thread.opt_step e th0 th1)
            (CONSISTENT: Local.promise_consistent (Thread.local th1))
            (REACHABLE: semi_reachable th0)
        :
          (<<STEP: opt_step e th0 th1>>) /\
          (<<REACHABLE: semi_reachable th1>>).
      Proof.
        inv STEP.
        - splits; auto.
        - eapply step_reachable in STEP0; eauto. des. splits; eauto.
      Qed.

      Lemma tau_steps_reachable lang (th0 th1: Thread.t lang)
            (STEPS: rtc (@Thread.tau_step _) th0 th1)
            (LOCAL: Local.wf (Thread.local th0) (Thread.memory th0))
            (MEMORY: Memory.closed (Thread.memory th0))
            (SC: Memory.closed_timemap (Thread.sc th0) (Thread.memory th0))
            (CONSISTENT: Local.promise_consistent (Thread.local th1))
            (REACHABLE: semi_reachable th0)
        :
          (<<STEP: rtc (@tau_step _) th0 th1>>) /\
          (<<REACHABLE: semi_reachable th1>>).
      Proof.
        revert LOCAL MEMORY SC CONSISTENT REACHABLE. induction STEPS; eauto. i.
        inv H. inv TSTEP. exploit Thread.step_future; eauto. i. des.
        hexploit PromiseConsistent.rtc_tau_step_promise_consistent; eauto. i.
        hexploit step_reachable; eauto. i. des.
        hexploit IHSTEPS; eauto. i. des. splits; eauto.
        econs; eauto. econs; eauto.
      Qed.

      Lemma reserve_steps_reachable lang (th0 th1: Thread.t lang)
            (STEPS: rtc (@Thread.reserve_step _) th0 th1)
            (LOCAL: Local.wf (Thread.local th0) (Thread.memory th0))
            (MEMORY: Memory.closed (Thread.memory th0))
            (SC: Memory.closed_timemap (Thread.sc th0) (Thread.memory th0))
            (CONSISTENT: Local.promise_consistent (Thread.local th1))
            (REACHABLE: semi_reachable th0)
        :
          (<<STEP: rtc (@reserve_step _) th0 th1>>) /\
          (<<REACHABLE: semi_reachable th1>>).
      Proof.
        revert LOCAL MEMORY SC CONSISTENT REACHABLE. induction STEPS; eauto. i.
        inv H. exploit Thread.step_future; eauto. i. des.
        hexploit PromiseConsistent.rtc_reserve_step_promise_consistent; eauto. i.
        hexploit step_reachable; eauto. i. des.
        hexploit IHSTEPS; eauto. i. des. splits; eauto.
      Qed.

      Lemma cancel_steps_reachable lang (th0 th1: Thread.t lang)
            (STEPS: rtc (@Thread.cancel_step _) th0 th1)
            (LOCAL: Local.wf (Thread.local th0) (Thread.memory th0))
            (MEMORY: Memory.closed (Thread.memory th0))
            (SC: Memory.closed_timemap (Thread.sc th0) (Thread.memory th0))
            (CONSISTENT: Local.promise_consistent (Thread.local th1))
            (REACHABLE: semi_reachable th0)
        :
          (<<STEP: rtc (@cancel_step _) th0 th1>>) /\
          (<<REACHABLE: semi_reachable th1>>).
      Proof.
        revert LOCAL MEMORY SC CONSISTENT REACHABLE. induction STEPS; eauto. i.
        inv H. exploit Thread.step_future; eauto. i. des.
        hexploit PromiseConsistent.rtc_cancel_step_promise_consistent; eauto. i.
        hexploit step_reachable; eauto. i. des.
        hexploit IHSTEPS; eauto. i. des. splits; eauto.
      Qed.

      Definition consistent lang (e1:Thread.t lang): Prop :=
        forall mem1 sc1
               (CAP: Memory.cap (Thread.memory e1) mem1)
               (SC_MAX: Memory.max_concrete_timemap mem1 sc1),
          (exists e2 e3,
              (<<STEPS: rtc (@tau_step lang) (Thread.mk _ (Thread.state e1) (Thread.local e1) sc1 mem1) e2>>) /\
              (<<FAILURE: step true ThreadEvent.failure e2 e3 >>)) \/
          (exists e2,
              (<<STEPS: rtc (@tau_step lang) (Thread.mk _ (Thread.state e1) (Thread.local e1) sc1 mem1) e2>>) /\
              (<<PROMISES: (Local.promises (Thread.local e2)) = Memory.bot>>))
      .

      Inductive configuration_step:
        forall (e:ThreadEvent.t) (tid:Ident.t) (c1 c2:Configuration.t), Prop :=
      | configuration_step_intro
          e tid c1 lang st1 lc1 e2 e3 st4 lc4 sc4 memory4
          (TID: IdentMap.find tid (Configuration.threads c1) = Some (existT _ lang st1, lc1))
          (CANCELS: rtc (@cancel_step _) (Thread.mk _ st1 lc1 (Configuration.sc c1) (Configuration.memory c1)) e2)
          (STEP: opt_step e e2 e3)
          (RESERVES: rtc (@reserve_step _) e3 (Thread.mk _ st4 lc4 sc4 memory4))
          (CONSISTENT: e <> ThreadEvent.failure -> consistent (Thread.mk _ st4 lc4 sc4 memory4)):
          configuration_step e tid c1 (Configuration.mk (IdentMap.add tid (existT _ _ st4, lc4) (Configuration.threads c1)) sc4 memory4)
      .
      Hint Constructors configuration_step.

      Lemma step_map_reachable lang pf e (th0 th1 fth0: Thread.t lang)
            (STEP: Thread.step pf e th0 th1)
            (THREAD: thread_map ident_map th0 fth0)
            (CONSISTENT: Local.promise_consistent (Thread.local th1))
            (REACHABLE: semi_reachable fth0)
            (LOCAL: Local.wf (Thread.local th0) (Thread.memory th0))
            (MEMORY: Memory.closed (Thread.memory th0))
            (SC: Memory.closed_timemap (Thread.sc th0) (Thread.memory th0))
            (FLOCAL: Local.wf (Thread.local fth0) (Thread.memory fth0))
            (FMEMORY: Memory.closed (Thread.memory fth0))
            (FSC: Memory.closed_timemap (Thread.sc fth0) (Thread.memory fth0))
        :
          exists fpf fe fth1,
            (<<STEP: Thread.step fpf fe fth0 fth1>>) /\
            (<<EVENT: tevent_map ident_map fe e>>) /\
            (<<THREAD: thread_map ident_map th1 fth1>>) /\
            (<<REACHABLE: semi_reachable fth1>>) /\
            (<<STEP: step pf e th0 th1>>)
      .
      Proof.
        splits; auto.
        inv THREAD. destruct th1. ss. hexploit step_map; ss.
        { eapply ident_map_le. }
        { eapply ident_map_bot. }
        { eapply ident_map_eq. }
        { instantiate (1:=fun _ => True). i. eapply ident_map_mappable_evt. }
        { econs; eauto. econs; eauto. }
        { ss. }
        { eauto. }
        { ss. }
        { ss. }
        { ss. }
        { eapply mapping_map_lt_collapsable_unwritable. eapply ident_map_lt. }
        { ss. }
        i. des. inv STEP0.
        assert (RECHABLE0: semi_reachable (Thread.mk _ state flc1 fsc1 fmem1)).
        { inv REACHABLE.
          econs; eauto. etrans; eauto. econs 2; [|refl]. econs; eauto. econs; eauto.
          ss. inv LOCAL1. hexploit promise_consistent_map.
          { eapply ident_map_le. }
          { eapply ident_map_eq. }
          { eapply TVIEW. }
          { eapply PROMISES. }
          { ss. }
          i. eapply promise_consistent_mon; eauto. refl.
        }
        esplits; eauto. econs; eauto.
        { eapply mapping_map_lt_collapsable_unwritable; eauto. eapply ident_map_lt. }
      Qed.

      Lemma tau_steps_map_reachable lang (th0 th1 fth0: Thread.t lang)
            (STEPS: rtc (@Thread.tau_step _) th0 th1)
            (THREAD: thread_map ident_map th0 fth0)
            (CONSISTENT: Local.promise_consistent (Thread.local th1))
            (REACHABLE: semi_reachable fth0)
            (LOCAL: Local.wf (Thread.local th0) (Thread.memory th0))
            (MEMORY: Memory.closed (Thread.memory th0))
            (SC: Memory.closed_timemap (Thread.sc th0) (Thread.memory th0))
            (FLOCAL: Local.wf (Thread.local fth0) (Thread.memory fth0))
            (FMEMORY: Memory.closed (Thread.memory fth0))
            (FSC: Memory.closed_timemap (Thread.sc fth0) (Thread.memory fth0))
        :
          exists fth1,
            (<<STEPS: rtc (@Thread.tau_step _) fth0 fth1>>) /\
            (<<THREAD: thread_map ident_map th1 fth1>>) /\
            (<<REACHABLE: semi_reachable fth1>>) /\
            (<<STEPS: rtc (@tau_step _) th0 th1>>)
      .
      Proof.
        revert_until STEPS. revert fth0. induction STEPS; eauto.
        { i. esplits; eauto. }
        i. inv H. inv TSTEP. exploit Thread.step_future; eauto. i. des.
        hexploit PromiseConsistent.rtc_tau_step_promise_consistent; eauto. i.
        hexploit step_map_reachable; eauto. i. des.
        exploit Thread.step_future; try apply STEP0; eauto. i. des.
        hexploit IHSTEPS; eauto. i. des. exists fth2. splits; auto.
        { eapply tevent_map_same_machine_event in EVENT0.
          rewrite <- EVENT0 in EVENT.
          econs 2; eauto. econs; eauto. econs; eauto.
        }
        { econs 2; eauto. econs; eauto. }
      Qed.

      Lemma consistent_reachable lang (th0: Thread.t lang)
            (CONSISTENT: Thread.consistent th0)
            (REACHABLE: semi_reachable th0)
            (LOCAL: Local.wf (Thread.local th0) (Thread.memory th0))
            (MEMORY: Memory.closed (Thread.memory th0))
            (SC: Memory.closed_timemap (Thread.sc th0) (Thread.memory th0))
        :
          consistent th0.
      Proof.
        ii.
        assert (THREAD: thread_map ident_map (Thread.mk _ (Thread.state th0) (Thread.local th0) sc1 mem1) th0).
        { destruct th0. ss. econs; eauto.
          - eapply ident_map_local.
          - econs.
            + i. eapply Memory.cap_inv in GET; eauto. des; eauto.
              right. exists to, from, msg, msg. splits; ss.
              * eapply ident_map_message.
              * refl.
            + i. eapply Memory.cap_le in GET; eauto; [|refl].
              left. exists fto, ffrom, fto, ffrom. splits; ss; try refl. i. econs; eauto.
          - eapply mapping_map_lt_collapsable_unwritable. eapply ident_map_lt.
          - eapply ident_map_timemap.
          - eapply Memory.max_concrete_timemap_spec; eauto.
            eapply Memory.cap_closed_timemap; eauto.
        }
        assert (FLOCAL: Local.wf (Thread.local th0) mem1).
        { eapply Local.cap_wf; eauto. }
        assert (FMEMORY: Memory.closed mem1).
        { eapply Memory.cap_closed; eauto. }
        assert (FSC: Memory.closed_timemap sc1 mem1).
        { eapply Memory.max_concrete_timemap_closed; eauto. }
        exploit CONSISTENT; eauto. i. des.
        { left. unfold Thread.steps_failure in *. des.
          exploit Thread.rtc_tau_step_future; eauto. i. des. ss.
          eapply tau_steps_map_reachable in STEPS; eauto.
          { des. exploit Thread.rtc_tau_step_future; eauto. i. des.
            eapply step_map_reachable in FAILURE0; eauto.
            { des. esplits; eauto. }
            { inv FAILURE0; inv STEP. inv LOCAL0. inv LOCAL1. ss. }
          }
          { inv FAILURE0; inv STEP. inv LOCAL0. inv LOCAL1. ss. }
        }
        { right. eapply tau_steps_map_reachable in STEPS; eauto.
          { des. esplits; eauto. }
          { eapply Local.bot_promise_consistent; eauto. }
        }
      Qed.

      Lemma configuration_step_reachable c1 c2 e
            (STEP: SConfiguration.step e tid c1 c2)
            (REACHABLE: rtc SConfiguration.all_machine_step c0 c1)
            (WF: Configuration.wf c1)
        :
          configuration_step e tid c1 c2.
      Proof.
        inv STEP.
        exploit Thread.rtc_cancel_step_future; eauto; try eapply WF; eauto. i. des. ss.
        exploit Thread.opt_step_future; eauto. i. des.
        exploit Thread.rtc_reserve_step_future; eauto. i. des. ss.
        assert ((<<CONSISTENT4: Local.promise_consistent lc4>>) /\
                (<<CONSISTENT3: Local.promise_consistent (Thread.local e3)>>)).
        { destruct (classic (e = ThreadEvent.failure)).
          - subst. inv STEP0. inv STEP; inv STEP0. inv LOCAL. inv LOCAL0. ss.
            splits; eauto.
            eapply PromiseConsistent.rtc_reserve_step_promise_consistent2 in RESERVES; eauto.
          - specialize (CONSISTENT H).
            eapply PromiseConsistent.consistent_promise_consistent in CONSISTENT; eauto.
            splits; eauto.
            eapply PromiseConsistent.rtc_reserve_step_promise_consistent; eauto.
        }
        des.
        assert (CONSISTENT2: Local.promise_consistent (Thread.local e2)).
        { inv STEP0; eauto.
          eapply PromiseConsistent.step_promise_consistent; eauto. }
        assert (CONSISTENT1: Local.promise_consistent lc1).
        { eapply PromiseConsistent.rtc_cancel_step_promise_consistent in CANCELS; eauto. }
        eapply cancel_steps_reachable in CANCELS; eauto; try eapply WF; eauto. des.
        eapply opt_step_reachable in STEP0; eauto. des.
        eapply reserve_steps_reachable in RESERVES; eauto. des.
        econs; eauto. i.
        eapply consistent_reachable; eauto.
      Qed.

    End TID.

    Section SIMCONFIG.

      Inductive sim_state_rel
                (tid: Ident.t)
                (lang_src lang_tgt: language)
                (r: Language.state lang_src -> Language.state lang_tgt -> Prop) :=
      | sim_state_rel_intro
          (STEP: forall st_src0 st_tgt0 st_tgt1 e
                        (REL: r st_src0 st_tgt0)
                        (REACHABLE: semi_reachable_state tid lang_tgt st_tgt1)
                        (STEP: Language.step lang_tgt e st_tgt0 st_tgt1),
              exists st_src1,
                (<<STEP: Language.step lang_src e st_src0 st_src1>>) /\
                (<<REL: r st_src1 st_tgt1>>))
          (TERMINAL: forall st_src st_tgt
                            (REL: r st_src st_tgt)
                            (REACHABLE: semi_reachable_state tid lang_tgt st_tgt)
                            (TERMINAL: Language.is_terminal lang_tgt st_tgt),
              Language.is_terminal lang_src st_src)
      .
      Hint Constructors sim_state_rel.

      Lemma eq_sim_state_rel tid lang
        :
          sim_state_rel tid lang lang eq.
      Proof.
        econs; i; clarify. eauto.
      Qed.

      Variable (r: forall (tid: Ident.t) (lang_src lang_tgt: language),
                   Language.state lang_src -> Language.state lang_tgt -> Prop).
      Hypothesis (REL: forall tid lang_src lang_tgt, sim_state_rel tid lang_src lang_tgt (r tid lang_src lang_tgt)).

      Inductive sim_statelocal tid:
        forall (lcst_src lcst_tgt: (sigT (@Language.state _)) * Local.t), Prop :=
      | sim_statelocal_intro
          lang_src lang_tgt st_src st_tgt lc
          (REL: r tid lang_src lang_tgt st_src st_tgt)
        :
          sim_statelocal tid (existT _ lang_src st_src, lc) (existT _ lang_tgt st_tgt, lc)
      .
      Hint Constructors sim_statelocal.

      Inductive sim_thread tid lang_src lang_tgt: forall (th_src: Thread.t lang_src) (th_tgt: Thread.t lang_tgt), Prop :=
      | sim_thread_intro
          st_src st_tgt lc sc mem
          (REL: r tid lang_src lang_tgt st_src st_tgt)
        :
          sim_thread tid (Thread.mk _ st_src lc sc mem) (Thread.mk _ st_tgt lc sc mem)
      .
      Hint Constructors sim_thread.

      Inductive sim_configuration:
        forall (c_src c_tgt: Configuration.t), Prop :=
      | sim_configuration_intro
          ths_src ths_tgt sc mem
          (THS: forall tid,
              option_rel
                (sim_statelocal tid)
                (IdentMap.find tid ths_src)
                (IdentMap.find tid ths_tgt))
        :
          sim_configuration (Configuration.mk ths_src sc mem) (Configuration.mk ths_tgt sc mem)
      .
      Hint Constructors sim_configuration.

      Lemma sim_thread_step tid lang_src lang_tgt
            (th_src0: Thread.t lang_src) (th_tgt0 th_tgt1: Thread.t lang_tgt) pf e
            (STEP: step tid pf e th_tgt0 th_tgt1)
            (SIM: sim_thread tid th_src0 th_tgt0)
        :
          exists th_src1,
            (<<STEP: Thread.step pf e th_src0 th_src1>>) /\
            (<<SIM: sim_thread tid th_src1 th_tgt1>>).
      Proof.
        inv SIM. inv STEP; ss. inv STEP0.
        { inv STEP. ss. esplits; eauto. econs 1; eauto. econs; eauto. }
        inv STEP. specialize (REL tid lang_src lang_tgt). inv REL.
        exploit STEP; eauto. i. des.
        esplits; eauto.
      Qed.

      Lemma sim_thread_opt_step tid lang_src lang_tgt
            (th_src0: Thread.t lang_src) (th_tgt0 th_tgt1: Thread.t lang_tgt) e
            (STEP: opt_step tid e th_tgt0 th_tgt1)
            (SIM: sim_thread tid th_src0 th_tgt0)
        :
          exists th_src1,
            (<<STEP: Thread.opt_step e th_src0 th_src1>>) /\
            (<<SIM: sim_thread tid th_src1 th_tgt1>>).
      Proof.
        inv STEP.
        - esplits; eauto. econs 1.
        - eapply sim_thread_step in SIM; eauto. des. esplits; eauto. econs 2; eauto.
      Qed.

      Lemma sim_thread_reserve_steps tid lang_src lang_tgt
            (th_src0: Thread.t lang_src) (th_tgt0 th_tgt1: Thread.t lang_tgt)
            (STEPS: rtc (@reserve_step tid _) th_tgt0 th_tgt1)
            (SIM: sim_thread tid th_src0 th_tgt0)
        :
          exists th_src1,
            (<<STEPS: rtc (@Thread.reserve_step _) th_src0 th_src1>>) /\
            (<<SIM: sim_thread tid th_src1 th_tgt1>>).
      Proof.
        ginduction STEPS; eauto. i. inv H.
        eapply sim_thread_step in STEP; eauto. des.
        exploit IHSTEPS; eauto. i. des.
        exists th_src2; eauto. esplits; eauto. econs; eauto. econs; eauto.
      Qed.

      Lemma sim_thread_cancel_steps tid lang_src lang_tgt
            (th_src0: Thread.t lang_src) (th_tgt0 th_tgt1: Thread.t lang_tgt)
            (STEPS: rtc (@cancel_step tid _) th_tgt0 th_tgt1)
            (SIM: sim_thread tid th_src0 th_tgt0)
        :
          exists th_src1,
            (<<STEPS: rtc (@Thread.cancel_step _) th_src0 th_src1>>) /\
            (<<SIM: sim_thread tid th_src1 th_tgt1>>).
      Proof.
        ginduction STEPS; eauto. i. inv H.
        eapply sim_thread_step in STEP; eauto. des.
        exploit IHSTEPS; eauto. i. des.
        exists th_src2; eauto. esplits; eauto. econs; eauto. econs; eauto.
      Qed.

      Lemma sim_thread_tau_steps tid lang_src lang_tgt
            (th_src0: Thread.t lang_src) (th_tgt0 th_tgt1: Thread.t lang_tgt)
            (STEPS: rtc (@tau_step tid _) th_tgt0 th_tgt1)
            (SIM: sim_thread tid th_src0 th_tgt0)
        :
          exists th_src1,
            (<<STEPS: rtc (@Thread.tau_step _) th_src0 th_src1>>) /\
            (<<SIM: sim_thread tid th_src1 th_tgt1>>).
      Proof.
        ginduction STEPS; eauto. i. inv H. inv TSTEP.
        eapply sim_thread_step in STEP; eauto. des.
        exploit IHSTEPS; eauto. i. des.
        exists th_src2; eauto. esplits; eauto. econs; eauto. econs; eauto. econs; eauto.
      Qed.

      Lemma sim_thread_consistent tid lang_src lang_tgt
            (th_src: Thread.t lang_src) (th_tgt: Thread.t lang_tgt)
            (CONSISTENT: consistent tid th_tgt)
            (SIM: sim_thread tid th_src th_tgt)
        :
          Thread.consistent th_src.
      Proof.
        inv SIM. ii; ss.
        assert (SIM: sim_thread tid (Thread.mk _ st_src lc sc1 mem1) (Thread.mk _ st_tgt lc sc1 mem1)).
        { econs; eauto. }
        exploit CONSISTENT; eauto. i; ss. des.
        - left. eapply sim_thread_tau_steps in STEPS; eauto. des.
          eapply sim_thread_step in FAILURE; eauto. des.
          unfold Thread.steps_failure. esplits; eauto.
        - right. eapply sim_thread_tau_steps in STEPS; eauto. des.
          esplits; eauto. inv SIM0. ss.
      Qed.

      Lemma sim_configuration_step c_src0 c_tgt0 c_tgt1 e tid
            (WF: Configuration.wf c_tgt0)
            (STEP: SConfiguration.step e tid c_tgt0 c_tgt1)
            (SIM: sim_configuration c_src0 c_tgt0)
            (REACHABLE: rtc SConfiguration.all_machine_step c0 c_tgt0)
        :
          exists c_src1,
            (<<STEP: SConfiguration.step e tid c_src0 c_src1>>) /\
            (<<SIM: sim_configuration c_src1 c_tgt1>>).
      Proof.
        eapply configuration_step_reachable in STEP; eauto.
        inv STEP. inv SIM. ss.
        dup THS. specialize (THS0 tid). setoid_rewrite TID in THS0.
        unfold option_rel in THS0. des_ifs. destruct p as [[lang_src st_src] lc_tgt].
        inv THS0. eapply inj_pair2 in H4. clarify. eapply inj_pair2 in H0. clarify.
        assert (SIM: sim_thread tid (Thread.mk _ st_src lc1 sc mem) (Thread.mk _ st1 lc1 sc mem)) by eauto.
        eapply sim_thread_cancel_steps in CANCELS; eauto. des.
        eapply sim_thread_opt_step in STEP0; eauto. des.
        eapply sim_thread_reserve_steps in RESERVES; eauto. des. destruct th_src2.
        esplits.
        { econs; s.
          - eauto.
          - eapply STEPS.
          - eapply STEP.
          - eapply STEPS0.
          - i. eapply sim_thread_consistent; eauto.
        }
        { inv SIM2. ss. econs; eauto. i.
          repeat erewrite IdentMap.gsspec. des_ifs.
        }
      Qed.

      Lemma steps_configuration_local_consistent c1
            (REACHABLE: rtc SConfiguration.all_machine_step c0 c1)
            tid lang st lc
            (TID: IdentMap.find tid (Configuration.threads c1) = Some (existT _ lang st, lc))
        :
          Local.promise_consistent lc.
      Proof.
        eapply Operators_Properties.clos_rt_rt1n_iff in REACHABLE.
        eapply Operators_Properties.clos_rt_rtn1_iff in REACHABLE.
        revert tid lang st lc TID. induction REACHABLE; eauto.
        i. inv H. inv STEP. assert (WF0: Configuration.wf y).
        { eapply Operators_Properties.clos_rt_rtn1_iff in REACHABLE.
          eapply Operators_Properties.clos_rt_rt1n_iff in REACHABLE.
          eapply SConfiguration.all_machine_steps_future; eauto. }
        exploit SConfiguration.step_future; eauto. i. des.
        inv STEP0. ss.
        erewrite IdentMap.gsspec in TID. des_ifs.
        { eapply inj_pair2 in H0. clarify.
          destruct (classic (e0 = ThreadEvent.failure)).
          { inv STEP; ss. inv STEP0; inv STEP. inv LOCAL. inv LOCAL0.
            eapply PromiseConsistent.rtc_reserve_step_promise_consistent2 in RESERVES; eauto.
          }
          { hexploit PromiseConsistent.consistent_promise_consistent; eauto; try apply WF2; eauto.
            ss. inv WF2. ss. eapply WF; eauto.
            erewrite IdentMap.gss. eauto.
          }
        }
        { eapply IHREACHABLE; eauto. }
      Qed.

      Lemma sim_configuration_terminal c_src c_tgt
            (TERMINAL: Configuration.is_terminal c_tgt)
            (SIM: sim_configuration c_src c_tgt)
            (REACHABLE: rtc SConfiguration.all_machine_step c0 c_tgt)
        :
          Configuration.is_terminal c_src.
      Proof.
        ii. inv SIM. ss.
        specialize (THS tid). setoid_rewrite FIND in THS.
        unfold option_rel in THS. des_ifs. destruct p as [[lang_tgt st_tgt] lc_tgt].
        inv THS. eapply inj_pair2 in H4. clarify. eapply inj_pair2 in H0. clarify.
        exploit TERMINAL; eauto. i. des.
        specialize (REL tid lang lang_tgt). inv REL.
        exploit TERMINAL0; eauto.
        econs; eauto. econs; eauto. ss.
        hexploit steps_configuration_local_consistent.
        { eapply REACHABLE. }
        { ss. eauto. }
        { eauto. }
      Qed.

      Lemma sim_configuration_behavior c_src c_tgt
            (WF: Configuration.wf c_tgt)
            (SIM: sim_configuration c_src c_tgt)
            (REACHABLE: rtc SConfiguration.all_machine_step c0 c_tgt)
        :
          behaviors SConfiguration.machine_step c_tgt <1= behaviors SConfiguration.machine_step c_src.
      Proof.
        intros beh BEH. ginduction BEH; eauto.
        - i. econs 1. eapply sim_configuration_terminal; eauto.
        - i. dup STEP. inv STEP0. exploit SConfiguration.step_future; eauto. i. des.
          eapply sim_configuration_step in STEP1; eauto. des. econs 2.
          + rewrite <- H0. econs; eauto.
          + eapply IHBEH; eauto. etrans; eauto.
        - i. dup STEP. inv STEP0. exploit SConfiguration.step_future; eauto. i. des.
          eapply sim_configuration_step in STEP1; eauto. des. econs 3.
          + rewrite <- H0. econs; eauto.
        - i. dup STEP. inv STEP0. exploit SConfiguration.step_future; eauto. i. des.
          eapply sim_configuration_step in STEP1; eauto. des. econs 4.
          + rewrite <- H0. econs; eauto.
          + eapply IHBEH; eauto. etrans; eauto.
      Qed.
    End SIMCONFIG.
  End REACHABLE.

  Theorem unreachable_code_transformation syn_src syn_tgt
          (r: forall (tid: Ident.t) (lang_src lang_tgt: language),
              Language.state lang_src -> Language.state lang_tgt -> Prop)
          (REL: forall tid lang_src lang_tgt, sim_state_rel (Configuration.init syn_tgt) tid lang_src lang_tgt (r tid lang_src lang_tgt))
          (INIT: sim_configuration r (Configuration.init syn_src) (Configuration.init syn_tgt))
    :
      behaviors SConfiguration.machine_step (Configuration.init syn_tgt)
      <1=
      behaviors SConfiguration.machine_step (Configuration.init syn_src).
  Proof.
    eapply sim_configuration_behavior; eauto.
    - i. ss. unfold Threads.init in *. rewrite IdentMap.Facts.map_o in TID.
      unfold option_map in *. des_ifs. ii. ss. erewrite Memory.bot_get in *. ss.
    - eapply Configuration.init_wf.
    - eapply Configuration.init_wf.
  Qed.
End SemiReachable.
