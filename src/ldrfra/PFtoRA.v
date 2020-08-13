Require Import Omega.
Require Import Bool.
Require Import RelationClasses.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Loc.
From PromisingLib Require Import Language.

Require Import Event.
Require Import Time.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.
Require Import Behavior.

Require Import PromiseConsistent.
Require Import Trace.
Require Import MemoryProps.
Require Import JoinedView.

Require Import LocalPF.
Require Import OrdStep.
Require Import RARace.
Require Import Stable.
Require Import PFtoRASimThread.
Require Import PFtoRAThread.

Set Implicit Arguments.


Definition option_rel3 {A B C} (P: A -> B -> C -> Prop)
           (a: option A) (b: option B) (c: option C): Prop :=
  match a, b, c with
  | Some x, Some y, Some z => P x y z
  | None, None, None => True
  | _, _, _ => False
  end.


Module PFtoRA.
  Section PFtoRA.
    Variable L: Loc.t -> bool.

    (* well-formedness *)

    Inductive wf_pf (tr: Trace.t) (c: Configuration.t): Prop :=
    | wf_pf_intro
        (WF: Configuration.wf c)
        (TRACE: forall tid lang st lc
                  (TH: IdentMap.find tid c.(Configuration.threads) = Some (existT _ lang st, lc)),
            TraceWF.wf tr lc.(Local.promises) c.(Configuration.memory))
        (PF: pf_configuration L c)
    .

    Definition wf_j := JConfiguration.wf.

    Inductive wf_ra (rels: ReleaseWrites.t) (c: Configuration.t): Prop :=
    | wf_ra_intro
        (WF: Configuration.wf c)
        (RELS: forall tid lang st lc
                 (TH: IdentMap.find tid c.(Configuration.threads) = Some (existT _ lang st, lc)),
            ReleaseWrites.wf rels lc.(Local.promises) c.(Configuration.memory))
    .

    Lemma wf_pf_thread
          tr c tid lang st lc
          (WF: wf_pf tr c)
          (FIND: IdentMap.find tid c.(Configuration.threads) = Some (existT _ lang st, lc)):
      PFtoRAThread.wf_pf tr (Thread.mk _ st lc c.(Configuration.sc) c.(Configuration.memory)).
    Proof.
      inv WF. inv WF0. inv WF.
      hexploit THREADS; eauto. i.
      hexploit TRACE; eauto. i.
      econs; eauto.
    Qed.

    Lemma wf_j_thread
          views c tid lang st lc
          (WF: wf_j views c)
          (FIND: IdentMap.find tid c.(Configuration.threads) = Some (existT _ lang st, lc)):
      PFtoRAThread.wf_j views (Thread.mk _ st lc c.(Configuration.sc) c.(Configuration.memory)).
    Proof.
      inv WF. inv WF0. inv WF.
      hexploit THREADS; eauto. i.
      hexploit REL; eauto. i.
      econs; eauto.
    Qed.

    Lemma wf_ra_thread
          rels c tid lang st lc
          (WF: wf_ra rels c)
          (FIND: IdentMap.find tid c.(Configuration.threads) = Some (existT _ lang st, lc)):
      PFtoRAThread.wf_ra rels (Thread.mk _ st lc c.(Configuration.sc) c.(Configuration.memory)).
    Proof.
      inv WF. inv WF0. inv WF.
      hexploit THREADS; eauto. i.
      hexploit RELS; eauto. i.
      econs; eauto.
    Qed.

    Lemma step_pf_future
          tr1 tr e tid c1 c2
          (WF1: wf_pf tr1 c1)
          (STEP: pf_step_trace L tr e tid c1 c2):
      <<WF2: wf_pf (tr1 ++ tr) c2>>.
    Proof.
      exploit pf_step_trace_future; eauto; try apply WF1. i. des.
      inv STEP. ss.
      exploit wf_pf_thread; eauto. i.
      exploit Trace.plus_step_steps; eauto. i.
      exploit PFtoRAThread.steps_pf_future; try exact x1; eauto. i. des.
      econs; ss. i. Configuration.simplify; try apply x2.
      exploit wf_pf_thread; try eapply TH; eauto. i. inv x3. ss.
      apply TraceWF.wf_app.
      - hexploit TraceWF.steps_disjoint_other; [eapply x0|eapply TRACE|..]; eauto.
      - hexploit TraceWF.steps_disjoint; try eapply x1; eauto; try apply x0; s.
        inv WF1. inv WF0. inv WF1. eauto.
    Qed.

    Lemma step_j_future
          e tid c1 c2 views1 views2
          (WF1: wf_j views1 c1)
          (STEP: JConfiguration.step e tid c1 c2 views1 views2):
      <<WF2: wf_j views2 c2>>.
    Proof.
      eapply JConfiguration.step_future; eauto.
    Qed.

    Lemma step_ra_future
          e tid rels1 rels2 c1 c2
          (WF1: wf_ra rels1 c1)
          (STEP: RAConfiguration.step L e tid rels1 rels2 c1 c2):
      <<WF2: wf_ra rels2 c2>>.
    Proof.
      exploit RAConfiguration.step_future; try eapply WF1; eauto. i. des.
      inv STEP. ss.
      assert (STEPS': RAThread.steps L rels1 rels2
                                     (Thread.mk _ st1 lc1 c1.(Configuration.sc) c1.(Configuration.memory))
                                     (Thread.mk _ st3 lc3 sc3 memory3)).
      { exploit RAThread.tau_steps_steps; eauto. i.
        inv STEP0; eapply RAThread.plus_step_steps; eauto. }
      exploit wf_ra_thread; eauto. i.
      hexploit RAThread.steps_rels_wf; try exact STEPS'; try apply x1. s. i.
      econs; ss. i. Configuration.simplify; ss.
      exploit wf_ra_thread; try eapply TH; eauto. i.
      inv WF1. inv WF. inv WF0.
      exploit DISJOINT; try exact n; eauto. i.
      hexploit RAThread.steps_rels_disjoint; try exact x; eauto. apply x1.
    Qed.

    Lemma steps_pf_future
          tr1 tr c1 c2
          (WF1: wf_pf tr1 c1)
          (STEPS: pf_steps_trace L c1 c2 tr):
      <<WF2: wf_pf (tr1 ++ tr) c2>>.
    Proof.
      revert tr1 WF1. induction STEPS; i.
      - rewrite List.app_nil_r. ss.
      - exploit step_pf_future; eauto. i.
        exploit IHSTEPS; eauto. i.
        rewrite List.app_assoc. ss.
    Qed.

    Lemma steps_j_future
          c1 c2 views1 views2
          (WF1: wf_j views1 c1)
          (STEPS: JConfiguration.steps c1 c2 views1 views2):
      <<WF2: wf_j views2 c2>>.
    Proof.
      eapply JConfiguration.steps_future; eauto.
    Qed.

    Lemma steps_ra_future
          rels1 rels2 c1 c2
          (WF1: wf_ra rels1 c1)
          (STEPS: RAConfiguration.steps L rels1 rels2 c1 c2):
      <<WF2: wf_ra rels2 c2>>.
    Proof.
      revert WF1. induction STEPS; i; ss.
      exploit step_ra_future; eauto.
    Qed.


    (* sim *)

    Inductive sim_thread_sl (views: Loc.t -> Time.t -> list View.t) (rels: ReleaseWrites.t)
              (sc_pf sc_j sc_ra: TimeMap.t) (mem_pf mem_j mem_ra: Memory.t):
      forall (sl_pf sl_j sl_ra: {lang: language & Language.state lang} * Local.t), Prop :=
    | sim_thread_sl_intro
        lang st_pf lc_pf st_j lc_j st_ra lc_ra
        (SIM: PFtoRAThread.sim_thread L views rels
                                      (Thread.mk lang st_pf lc_pf sc_pf mem_pf)
                                      (Thread.mk lang st_j lc_j sc_j mem_j)
                                      (Thread.mk lang st_ra lc_ra sc_ra mem_ra)):
        sim_thread_sl views rels sc_pf sc_j sc_ra mem_pf mem_j mem_ra
                      (existT _ lang st_pf, lc_pf) (existT _ lang st_j, lc_j) (existT _ lang st_ra, lc_ra)
    .

    Inductive sim_conf (tr: Trace.t) (views: Loc.t -> Time.t -> list View.t) (rels: ReleaseWrites.t):
      forall (c_pf c_j c_ra: Configuration.t), Prop :=
    | sim_conf_intro
        ths_pf sc_pf mem_pf
        ths_j sc_j mem_j
        ths_ra sc_ra mem_ra
        (SIM_TR: PFtoRAThread.sim_trace tr rels)
        (THS: forall tid,
            option_rel3
              (sim_thread_sl views rels sc_pf sc_j sc_ra mem_pf mem_j mem_ra)
              (IdentMap.find tid ths_pf)
              (IdentMap.find tid ths_j)
              (IdentMap.find tid ths_ra)):
        sim_conf tr views rels
                 (Configuration.mk ths_pf sc_pf mem_pf)
                 (Configuration.mk ths_j sc_j mem_j)
                 (Configuration.mk ths_ra sc_ra mem_ra)
    .

    Lemma init_wf_pf syn:
      wf_pf [] (Configuration.init syn).
    Proof.
      econs; eauto using Configuration.init_wf.
      - i. ss.
      - eapply configuration_init_pf.
    Qed.

    Lemma init_wf_j syn:
      wf_j (fun _ => fun _ => []) (Configuration.init syn).
    Proof.
      econs; eauto using Configuration.init_wf.
      - i. ss.
        unfold Threads.init in *.
        rewrite IdentMap.Facts.map_o in *.
        destruct (@UsualFMapPositive.UsualPositiveMap'.find
                    (@sigT _ (@Language.syntax ProgramEvent.t)) tid syn); inv TH.
        apply inj_pair2 in H1. subst. ss. ii.
        rewrite Memory.bot_get in *. ss.
      - ss. econs; ss. i.
        unfold Memory.get, Memory.init, Cell.get, Cell.init in *. ss.
        apply DOMap.singleton_find_inv in GET. des. inv GET0.
      - ss.
    Qed.

    Lemma init_wf_ra syn:
      wf_ra [] (Configuration.init syn).
    Proof.
      econs; eauto using Configuration.init_wf. i. ss.
    Qed.

    Lemma init_sim_conf syn:
      sim_conf [] (fun _ => fun _ => []) []
               (Configuration.init syn) (Configuration.init syn) (Configuration.init syn).
    Proof.
      econs; ss. i. unfold option_rel3.
      destruct (IdentMap.find tid (Threads.init syn)) as [[[lang st] lc]|] eqn:FIND; ss.
      unfold Threads.init in *.
      rewrite IdentMap.Facts.map_o in *.
      destruct (@UsualFMapPositive.UsualPositiveMap'.find
                  (@sigT _ (@Language.syntax ProgramEvent.t)) tid syn); inv FIND.
      apply inj_pair2 in H1. subst.
      econs. econs; ss.
      - econs; ss; try refl. econs; try refl. ii.
        rewrite Memory.bot_get. ss.
      - econs; ss.
        + econs; ss.
          * econs; ss. i. condtac; ss. refl.
          * ii. rewrite Memory.bot_get in *. ss.
        + econs; ss; i.
          * unfold Memory.get, Memory.init, Cell.get, Cell.init in *. ss.
            apply DOMap.singleton_find_inv in GET_SRC. des. inv GET_SRC0.
            esplits; ss. econs. condtac; ss.
          * unfold Memory.get, Memory.init, Cell.get, Cell.init in *. ss.
            apply DOMap.singleton_find_inv in GET_TGT. des. inv GET_TGT0.
            esplits; ss. econs. condtac; ss.
      - econs; ss. ii.
        unfold Memory.get, Memory.init, Cell.get, Cell.init in *. ss.
        apply DOMap.singleton_find_inv in GET. des. inv GET0.
      - econs; ss. ii.
        unfold Memory.get, Memory.init, Cell.get, Cell.init in *. ss.
        apply DOMap.singleton_find_inv in GET. des. inv GET0.
      - econs; ss. ii. des; ss.
        unfold Memory.get, Memory.init, Cell.get, Cell.init in *. ss.
        apply DOMap.singleton_find_inv in GET. des. inv GET1.
    Qed.

    Lemma sim_conf_terminal
          tr views rrels c_pf c_j c_ra
          (SIM: sim_conf tr views rrels c_pf c_j c_ra)
          (TERMINAL: Configuration.is_terminal c_pf):
      Configuration.is_terminal c_ra.
    Proof.
      ii. inv SIM. specialize (THS tid).
      unfold option_rel3 in *. ss. des_ifs.
      destruct p as [[]]. destruct p0 as [[]]. inv THS.
      apply inj_pair2 in H7. apply inj_pair2 in H4. apply inj_pair2 in H1. subst.
      inv SIM. inv SIM_JOINED. inv SIM_RA. ss.
      apply inj_pair2 in H2. apply inj_pair2 in H6. subst.
      exploit TERMINAL; eauto. i. des.
      split; ss.
      inv THREAD. econs.
      inv LOCAL0. rewrite PROMISES0.
      eapply JSim.sim_local_memory_bot; eauto.
    Qed.


    (* step *)

    Lemma sim_conf_step
          tr1 views1 rels1 c1_pf c1_j c1_ra
          tr tid e c2_pf
          (SIM1: sim_conf tr1 views1 rels1 c1_pf c1_j c1_ra)
          (WF1_PF: wf_pf tr1 c1_pf)
          (WF1_J: wf_j views1 c1_j)
          (WF1_RA: wf_ra rels1 c1_ra)
          (STEP: pf_step_trace L tr e tid c1_pf c2_pf):
      (exists c2_j views2 rels2 c2_ra,
          (<<STEP_J: JConfiguration.step e tid c1_j c2_j views1 views2>>) /\
          (<<STEP_RA: RAConfiguration.step L e tid rels1 rels2 c1_ra c2_ra>>) /\
          (<<SIM2: sim_conf (tr1 ++ tr) views2 rels2 c2_pf c2_j c2_ra>>)) \/
      (exists rels2 c2_ra,
          (<<STEP_RA: RAConfiguration.step L MachineEvent.failure tid rels1 rels2 c1_ra c2_ra>>)).
    Proof.
      dup SIM1. inv SIM0. inv STEP. ss.
      dup THS. specialize (THS0 tid). unfold option_rel3 in THS0. des_ifs.
      inv THS0. apply inj_pair2 in H1. subst.
      exploit wf_pf_thread; eauto. s. i.
      exploit wf_j_thread; eauto. s. i.
      exploit wf_ra_thread; eauto. s. i.
      exploit PFtoRAThread.sim_thread_plus_step; eauto.
      { exploit PFtoRAThread.steps_pf_future; eauto. i. des.
        exploit PFtoRAThread.step_pf_future; eauto. i. des.
        destruct (classic(e0 = ThreadEvent.failure)).
        - subst. inv STEP0; inv STEP. inv LOCAL. inv LOCAL0. ss.
        - hexploit CONSISTENT; eauto. i. inv H0. des.
          hexploit consistent_promise_consistent;
            try eapply Trace.consistent_thread_consistent; eauto; try eapply x4. }
      i. des.
      - left.
        exploit PFtoRAThread.steps_pf_future; eauto. i. des.
        exploit PFtoRAThread.step_pf_future; eauto. i. des.
        exploit PFtoRAThread.steps_j_future; eauto. i. des.
        exploit PFtoRAThread.step_j_future; eauto. i. des.
        exploit PFtoRAThread.steps_ra_future; try eapply RAThread.tau_steps_steps; eauto. i. des.
        exploit PFtoRAThread.step_ra_future; eauto. i. des.
        rewrite <- List.app_assoc in x4.
        assert (CONS: e0 <> ThreadEvent.failure ->
                      JThread.consistent e3_j views3 /\ RAThread.consistent L rels3 e3_ra).
        { i. exploit PFtoRAThread.sim_thread_consistent; try exact SIM_TR2; eauto. }
        destruct e3_j as [st3_j lc3_j sc3_j mem3_j], e3_ra as [st3_ra lc3_ra sc3_ra mem3_ra].
        esplits.
        + replace (ThreadEvent.get_machine_event e0) with (ThreadEvent.get_machine_event e_j); cycle 1.
          { inv EVENT_J; ss. }
          econs; eauto. i. eapply CONS. inv EVENT_J; ss.
        + replace (ThreadEvent.get_machine_event e0) with (ThreadEvent.get_machine_event e_ra); cycle 1.
          { inv EVENT_J; inv EVENT_RA; ss. }
          econs; eauto. i. eapply CONS. inv EVENT_J; inv EVENT_RA; ss.
        + econs; ss. i.
          repeat rewrite IdentMap.gsspec. condtac; ss.
          specialize (THS tid0). unfold option_rel3 in THS. des_ifs. inv THS. ss.
          inv SIM0. ss. econs. econs; s; eauto; try apply SIM2.
          * inv SIM_JOINED.
            apply inj_pair2 in H2. apply inj_pair2 in H6. subst.
            econs; s; eauto; try by (inv SIM2; inv SIM_JOINED; ss).
            exploit JThread.tau_steps_future; eauto; try apply x1. s. i. des.
            exploit JThread.step_future; eauto. s. i. des.
            eapply JSim.sim_local_le; try exact LOCAL.
            etrans; eauto.
          * inv SIM_RA. ss. subst.
            econs; s; eauto; try by (inv SIM2; inv SIM_RA; ss).
            inv LOCAL. econs; ss. i.
            assert (STEPS': RAThread.steps L rels1 rels3
                                           (Thread.mk _ st_ra lc_ra sc_j mem_ra)
                                           (Thread.mk _ st3_ra lc3_ra sc3_ra mem3_ra)).
            { exploit RAThread.tau_steps_steps; eauto. i.
              inv STEP_RA; eapply RAThread.plus_step_steps; eauto. }
            exploit wf_ra_thread; try exact WF1_RA; try eapply Heq4. s. i.
            eapply RAThread.steps_rels_disjoint; try exact STEPS'; ss; try apply x2; try apply x9.
            inv WF1_RA. inv WF. inv WF0. ss.
            eapply DISJOINT; [|eapply Heq1|eapply Heq4]. congr.
          * econs; try apply SIM2; try apply NORMAL_J.
          * econs; try apply SIM2; try apply NORMAL_RA.
          * econs; s; try apply SIM2; try apply STABLE_RA.
            assert (STEPS': RAThread.steps L rels1 rels3
                                           (Thread.mk _ st_ra lc_ra sc_ra mem_ra)
                                           (Thread.mk _ st3_ra lc3_ra sc3_ra mem3_ra)).
            { exploit RAThread.tau_steps_steps; eauto. i.
              inv STEP_RA; eapply RAThread.plus_step_steps; eauto. }
            exploit RAThread.steps_future; try exact STEPS'; try apply x2. s. i. des.
            exploit wf_ra_thread; try exact WF1_RA; try eapply Heq4. s. i.
            exploit Stable.future_stable_tview; try eapply STABLE_RA; try apply x9; eauto.
      - right.
        destruct e3_ra as [st3_ra lc3_ra sc3_ra mem3_ra].
        esplits.
        replace MachineEvent.failure with (ThreadEvent.get_machine_event ThreadEvent.failure) by ss.
        econs; eauto. ss.
    Qed.

    Lemma sim_conf_steps
          tr1 views1 rels1 c1_pf c1_j c1_ra
          tr c2_pf
          (SIM1: sim_conf tr1 views1 rels1 c1_pf c1_j c1_ra)
          (WF1_PF: wf_pf tr1 c1_pf)
          (WF1_J: wf_j views1 c1_j)
          (WF1_RA: wf_ra rels1 c1_ra)
          (STEPS: pf_steps_trace L c1_pf c2_pf tr):
      (exists c2_j views2 rels2 c2_ra,
          (<<STEPS_RA: RAConfiguration.steps L rels1 rels2 c1_ra c2_ra>>) /\
          (<<STEPS_J: JConfiguration.steps c1_j c2_j views1 views2>>) /\
          (<<SIM2: sim_conf (tr1 ++ tr) views2 rels2 c2_pf c2_j c2_ra>>)) \/
      (exists rels2 rels3 tid c2_ra c3_ra,
          (<<STEP_RA: RAConfiguration.steps L rels1 rels2 c1_ra c2_ra>>) /\
          (<<STEP_RA: RAConfiguration.step L MachineEvent.failure tid rels2 rels3 c2_ra c3_ra>>)).
    Proof.
      revert tr1 views1 rels1 c1_j c1_ra SIM1 WF1_PF WF1_J WF1_RA.
      induction STEPS; i.
      { left. esplits; [econs 1|econs 1|]. rewrite List.app_nil_r. eauto. }
      exploit sim_conf_step; eauto. i. des.
      - exploit step_pf_future; eauto. i. des.
        exploit step_j_future; eauto. i. des.
        exploit step_ra_future; eauto. i. des.
        exploit IHSTEPS; eauto. i. des.
        + left. esplits.
          * econs 2; eauto.
          * econs 2; eauto.
          * rewrite List.app_assoc. eauto.
        + right. esplits.
          * econs 2; eauto.
          * eauto.
      - right. esplits; eauto. econs 1.
    Qed.


    (* racefree *)

    Lemma sim_conf_racefree
          tr views rels c_pf c_j c_ra
          (SIM: sim_conf tr views rels c_pf c_j c_ra)
          (WF_PF: wf_pf tr c_pf)
          (WF_J: wf_j views c_j)
          (WF_RA: wf_ra rels c_ra)
          (RA_RACEFREE: RARace.racefree L rels c_ra):
      pf_multi_racefree_view L c_pf.
    Proof.
      ii. exploit sim_conf_steps; eauto. i. des; eauto.
      exploit steps_pf_future; eauto. i. des.
      exploit steps_j_future; eauto. i. des.
      exploit steps_ra_future; eauto. i. des.
      exploit pf_steps_trace_inv; try exact CSTEPS2; eauto; try apply x0. i. des.
      exploit sim_conf_steps; try exact STEPS; eauto. i. des; cycle 1.
      { eapply RA_RACEFREE; try eapply STEP_RA0.
        eapply RAConfiguration.steps_trans; eauto. }
      exploit steps_pf_future; try exact STEPS; eauto. i. des.
      exploit steps_j_future; try exact STEPS_J0; eauto. i. des.
      exploit steps_ra_future; try exact STEPS_RA0; eauto. i. des.
      subst. inv SIM0. specialize (THS tid). ss.
      unfold option_rel3 in THS. des_ifs. inv THS.
      apply inj_pair2 in H1. subst.
      exploit wf_pf_thread; try exact x3; eauto. s. i.
      exploit wf_j_thread; try exact x4; eauto. s. i.
      exploit wf_ra_thread; try exact x5; eauto. s. i.
      exploit PFtoRAThread.steps_pf_future; try exact THREAD_STEPS; eauto. i. des.
      hexploit step_promise_consistent; try exact THREAD_STEP; try apply x9; eauto. i.
      exploit PFtoRAThread.sim_thread_steps; try eapply SIM0; eauto. i. des; cycle 1.
      { destruct e3_ra. eapply RA_RACEFREE.
        - eapply RAConfiguration.steps_trans; eauto.
        - replace MachineEvent.failure with (ThreadEvent.get_machine_event ThreadEvent.failure) by ss.
          econs; eauto; ss.
      }
      exploit PFtoRAThread.steps_j_future; try exact STEPS_J1; eauto. i. des.
      exploit PFtoRAThread.steps_ra_future;
        try eapply RAThread.tau_steps_steps; try exact STEPS_RA1; eauto. i. des.
      exploit PFtoRAThread.sim_thread_step; try exact THREAD_STEP; eauto.
      { inv READ; ss. }
      i. des; cycle 1.
      { destruct e2_ra0. eapply RA_RACEFREE.
        - eapply RAConfiguration.steps_trans; eauto.
        - replace MachineEvent.failure with (ThreadEvent.get_machine_event ThreadEvent.failure) by ss.
          econs; eauto; ss.
      }
      inv STEP_RA; cycle 1.
      { destruct e2_ra0. eapply RA_RACEFREE.
        - eapply RAConfiguration.steps_trans; eauto.
        - replace MachineEvent.failure with (ThreadEvent.get_machine_event ThreadEvent.failure) by ss.
          econs; eauto; ss. econs 2; eauto.
      }
      inv READ; inv EVENT_J; inv EVENT_RA; ss.
      - destruct e2_ra0. eapply RA_RACEFREE.
        + eapply RAConfiguration.steps_trans; eauto.
        + replace MachineEvent.failure with (ThreadEvent.get_machine_event ThreadEvent.failure) by ss.
          econs; eauto; ss. econs 2; eauto; ss.
          * inv SIM1. inv SIM_JOINED. inv SIM_RA.
            apply inj_pair2 in H3. apply inj_pair2 in H4. subst. ss.
            eapply PFtoRASimThread.sim_local_promise_consistent; eauto.
            eapply JSim.sim_local_promise_consistent; eauto.
          * unfold RARace.ra_race. splits; ss.
            { inv SIM1. inv SIM_JOINED. inv SIM_RA.
              apply inj_pair2 in H3. apply inj_pair2 in H4. subst. ss.
              inv LOCAL0. inv TVIEW. rewrite CUR.
              eapply TimeFacts.le_lt_lt; eauto. condtac.
              - inv LOCAL. inv TVIEW. inv CUR0. apply RLX.
              - inv LOCAL. inv TVIEW. inv CUR0.
                inv NORMAL_J. inv NORMAL_TVIEW. ss. rewrite CUR0; ss. }
            { left. ii. inv WRITE.
              - eapply SIM_TR2; eauto.
                + do 2 (apply List.in_or_app; left).
                  apply List.in_or_app. right. eauto.
                + ss.
              - eapply SIM_TR2; eauto.
                + do 2 (apply List.in_or_app; left).
                  apply List.in_or_app. right. eauto.
                + ss. }
      - destruct e2_ra0. eapply RA_RACEFREE.
        + eapply RAConfiguration.steps_trans; eauto.
        + replace MachineEvent.failure with (ThreadEvent.get_machine_event ThreadEvent.failure) by ss.
          econs; eauto; ss. econs 2; eauto; ss.
          * inv SIM1. inv SIM_JOINED. inv SIM_RA.
            apply inj_pair2 in H3. apply inj_pair2 in H4. subst. ss.
            eapply PFtoRASimThread.sim_local_promise_consistent; eauto.
            eapply JSim.sim_local_promise_consistent; eauto.
          * unfold RARace.ra_race. splits; ss.
            { inv SIM1. inv SIM_JOINED. inv SIM_RA.
              apply inj_pair2 in H3. apply inj_pair2 in H4. subst. ss.
              inv LOCAL0. inv TVIEW. rewrite CUR.
              eapply TimeFacts.le_lt_lt; eauto. condtac.
              - inv LOCAL. inv TVIEW. inv CUR0. apply RLX.
              - inv LOCAL. inv TVIEW. inv CUR0.
                inv NORMAL_J. inv NORMAL_TVIEW. ss. rewrite CUR0; ss. }
            { left. ii. inv WRITE.
              - eapply SIM_TR2; eauto.
                + do 2 (apply List.in_or_app; left).
                  apply List.in_or_app. right. eauto.
                + ss.
              - eapply SIM_TR2; eauto.
                + do 2 (apply List.in_or_app; left).
                  apply List.in_or_app. right. eauto.
                + ss. }
    Qed.


    (* behaviors *)

    Lemma sim_conf_behavior
          tr views rels c_pf c_j c_ra
          (SIM: sim_conf tr views rels c_pf c_j c_ra)
          (WF_PF: wf_pf tr c_pf)
          (WF_J: wf_j views c_j)
          (WF_RA: wf_ra rels c_ra)
          (RACEFREE: RARace.racefree L rels c_ra):
      behaviors (pf_multi_step L) c_pf <1=
      behaviors (@OrdConfiguration.step L Ordering.acqrel) c_ra.
    Proof.
      i. revert tr views rels c_j c_ra SIM WF_PF WF_J WF_RA RACEFREE.
      induction PR; i.
      - econs 1. eapply sim_conf_terminal; eauto.
      - inv STEP. exploit sim_conf_step; eauto. i. des.
        + exploit RARace.racefree_step_ord_step; eauto; try apply WF_RA. i.
          econs 2; eauto.
          hexploit RARace.step_racefree; eauto. i.
          exploit step_pf_future; eauto. i. des.
          exploit step_j_future; eauto. i. des.
          exploit step_ra_future; eauto.
        + exfalso. eapply RACEFREE; eauto. econs 1.
      - inv STEP. exploit sim_conf_step; eauto. i. des.
        + exfalso. eapply RACEFREE; eauto. econs 1.
        + exfalso. eapply RACEFREE; eauto. econs 1.
      - inv STEP. exploit sim_conf_step; eauto. i. des.
        + exploit RARace.racefree_step_ord_step; eauto; try apply WF_RA. i.
          econs 4; eauto.
          hexploit RARace.step_racefree; eauto. i.
          exploit step_pf_future; eauto. i. des.
          exploit step_j_future; eauto. i. des.
          exploit step_ra_future; eauto.
        + exfalso. eapply RACEFREE; eauto. econs 1.
    Qed.
  End PFtoRA.
End PFtoRA.
