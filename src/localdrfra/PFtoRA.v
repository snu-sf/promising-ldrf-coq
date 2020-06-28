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

    Lemma step_wf_pf
          tr1 tr e tid c1 c2
          (WF1: wf_pf tr1 c1)
          (STEP: pf_step_trace L tr e tid c1 c2):
      <<WF2: wf_pf (tr1 ++ tr) c2>>.
    Proof.
      exploit pf_step_trace_future; eauto; try apply WF1. i. des.
      inv STEP. ss.
      exploit wf_pf_thread; eauto. i.
      exploit Trace.steps_step_steps; eauto. i.
      exploit PFtoRAThread.steps_pf_future; try exact x1; eauto. i. des.
      econs; ss. i. Configuration.simplify; try apply x2.
      exploit wf_pf_thread; try eapply TH; eauto. i. inv x3. ss.
      apply TraceWF.wf_app.
      - hexploit TraceWF.steps_disjoint_other; [eapply x0|eapply TRACE|..]; eauto.
      - hexploit TraceWF.steps_disjoint; try eapply x1; eauto; try apply x0; s.
        inv WF1. inv WF0. inv WF1. eauto.
    Qed.

    Lemma steps_wf_j
          e tid c1 c2 views1 views2
          (WF1: wf_j views1 c1)
          (STEP: JConfiguration.step e tid c1 c2 views1 views2):
      <<WF2: wf_j views2 c2>>.
    Proof.
      eapply JConfiguration.step_future; eauto.
    Qed.

    Lemma steps_wf_ra
          e tid rels1 rels2 c1 c2
          (WF1: wf_ra rels1 c1)
          (STEP: RAConfiguration.step L e tid rels1 rels2 c1 c2):
      <<WF2: wf_ra rels2 c2>>.
    Proof.
      exploit RAConfiguration.step_future; try eapply WF1; eauto. i. des.
      inv STEP. ss.
      assert (STEPS': RAThread.steps lang L rels1 rels2
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
                      JThread.consistent e3_j views3 /\ RAThread.consistent lang L rels3 e3_ra).
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
            assert (STEPS': RAThread.steps lang L rels1 rels3
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
            assert (STEPS': RAThread.steps lang L rels1 rels3
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
  End PFtoRA.
End PFtoRA.
