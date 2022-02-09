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

Require Import PFStep.
Require Import OrdStep.
Require Import Writes.
Require Import WStep.
Require Import Stable.
Require Import PFtoAPFSim.
Require Import APFtoRASim.
Require Import PFtoRAThread.

Set Implicit Arguments.


Module PFtoRA.
  Section PFtoRA.
    Variable L: Loc.t -> bool.

    (* well-formedness *)

    Inductive wf_pf (c: Configuration.t): Prop :=
    | wf_pf_intro
        (WF: Configuration.wf c)
        (PF: PF.pf_configuration L c)
    .

    Definition wf_j := JConfiguration.wf.

    Inductive wf_ra (rels: Writes.t) (c: Configuration.t): Prop :=
    | wf_ra_intro
        (WF: Configuration.wf c)
        (PROMISES: forall tid lang st lc
                     (TH: IdentMap.find tid (Configuration.threads c) = Some (existT _ lang st, lc)),
            OrdLocal.reserve_only L (Local.promises lc))
        (RELS: forall tid lang st lc
                 (TH: IdentMap.find tid (Configuration.threads c) = Some (existT _ lang st, lc)),
            Writes.wf L rels (Configuration.memory c))
    .

    Lemma wf_pf_thread
          c tid lang st lc
          (WF: wf_pf c)
          (FIND: IdentMap.find tid (Configuration.threads c) = Some (existT _ lang st, lc)):
      PFtoRAThread.wf_pf (Thread.mk _ st lc (Configuration.sc c) (Configuration.memory c)).
    Proof.
      inv WF. inv WF0. inv WF.
      hexploit THREADS; eauto. i.
      econs; eauto.
    Qed.

    Lemma wf_j_thread
          views c tid lang st lc
          (WF: wf_j views c)
          (FIND: IdentMap.find tid (Configuration.threads c) = Some (existT _ lang st, lc)):
      PFtoRAThread.wf_j views (Thread.mk _ st lc (Configuration.sc c) (Configuration.memory c)).
    Proof.
      inv WF. inv WF0. inv WF.
      hexploit THREADS; eauto. i.
      hexploit REL; eauto. i.
      econs; eauto.
    Qed.

    Lemma wf_ra_thread
          rels c tid lang st lc
          (WF: wf_ra rels c)
          (FIND: IdentMap.find tid (Configuration.threads c) = Some (existT _ lang st, lc)):
      PFtoRAThread.wf_ra L rels (Thread.mk _ st lc (Configuration.sc c) (Configuration.memory c)).
    Proof.
      inv WF. inv WF0. inv WF.
      econs; eauto.
    Qed.

    Lemma step_pf_future
          e tid c1 c2
          (WF1: wf_pf c1)
          (STEP: PFConfiguration.step L e tid c1 c2):
      <<WF2: wf_pf c2>>.
    Proof.
      exploit PFConfiguration.step_future; eauto; try apply WF1. i. des. ss.
    Qed.

    Lemma step_j_future
          e tid c1 c2 views1 views2
          (WF1: wf_j views1 c1)
          (STEP: JConfiguration.single_step e tid c1 c2 views1 views2):
      <<WF2: wf_j views2 c2>>.
    Proof.
      eapply JConfiguration.single_step_future; eauto.
    Qed.

    Lemma step_ra_future
          ordr ordw
          e tid rels1 rels2 c1 c2
          (WF1: wf_ra rels1 c1)
          (ORD: Ordering.le Ordering.plain ordw)
          (STEP: WConfiguration.step L ordr ordw e tid rels1 rels2 c1 c2):
      <<WF2: wf_ra rels2 c2>>.
    Proof.
      exploit WConfiguration.step_future; try eapply WF1; eauto. i. des.
      inv STEP. ss.
      assert (STEPS': WThread.steps L ordr ordw rels1 rels2
                                    (Thread.mk _ st1 lc1 (Configuration.sc c1) (Configuration.memory c1))
                                    (Thread.mk _ st4 lc4 sc4 memory4)).
      { exploit WThread.tau_steps_steps;
          try eapply WThread.cancel_steps_tau_steps; try exact CANCELS. i.
        exploit WThread.opt_step_steps; try exact STEP0. i.
        exploit WThread.tau_steps_steps;
          try eapply WThread.reserve_steps_tau_steps; try exact RESERVES. i.
        eapply WThread.steps_trans; [eauto|].
        eapply WThread.steps_trans; eauto.
      }
      exploit wf_ra_thread; eauto. i.
      hexploit WThread.steps_writes_wf; try exact STEPS'; try apply x1; ss. i.
      econs; ss. i. Configuration.simplify; ss.
      - hexploit OrdThread.rtc_cancel_step_reserve_only; try eapply x1; eauto. i. des.
        hexploit WThread.opt_step_ord_opt_step; eauto. i.
        hexploit OrdThread.opt_step_reserve_only; try exact H1; eauto. i. des.
        hexploit OrdThread.rtc_reserve_step_reserve_only; eauto.
      - exploit wf_ra_thread; try eapply TH; eauto. i. apply x2.
    Qed.

    Lemma steps_pf_future
          c1 c2
          (WF1: wf_pf c1)
          (STEPS: rtc (PFConfiguration.all_step L) c1 c2):
      <<WF2: wf_pf c2>>.
    Proof.
      exploit PFConfiguration.rtc_all_step_future; try apply WF1; eauto. i. des.
      econs; ss.
    Qed.

    Lemma steps_j_future
          c1 c2 views1 views2
          (WF1: wf_j views1 c1)
          (STEPS: JConfiguration.single_steps c1 c2 views1 views2):
      <<WF2: wf_j views2 c2>>.
    Proof.
      eapply JConfiguration.single_steps_future; eauto.
    Qed.

    Lemma steps_ra_future
          ordr ordw
          rels1 rels2 c1 c2
          (WF1: wf_ra rels1 c1)
          (ORD: Ordering.le Ordering.plain ordw)
          (STEPS: WConfiguration.steps L ordr ordw rels1 rels2 c1 c2):
      <<WF2: wf_ra rels2 c2>>.
    Proof.
      revert WF1. induction STEPS; i; ss.
      exploit step_ra_future; eauto.
    Qed.


    (* sim *)

    Inductive sim_thread_sl (views: Loc.t -> Time.t -> list View.t) (rels: Writes.t)
              (sc_pf sc_j sc_apf sc_ra: TimeMap.t) (mem_pf mem_j mem_apf mem_ra: Memory.t):
      forall (sl_pf sl_j sl_apf sl_ra: {lang: language & Language.state lang} * Local.t), Prop :=
    | sim_thread_sl_intro
        lang st_pf lc_pf st_j lc_j st_apf lc_apf st_ra lc_ra
        (SIM: PFtoRAThread.sim_thread L views rels
                                      (Thread.mk lang st_pf lc_pf sc_pf mem_pf)
                                      (Thread.mk lang st_j lc_j sc_j mem_j)
                                      (Thread.mk lang st_apf lc_apf sc_apf mem_apf)
                                      (Thread.mk lang st_ra lc_ra sc_ra mem_ra)):
        sim_thread_sl views rels sc_pf sc_j sc_apf sc_ra mem_pf mem_j mem_apf mem_ra
                      (existT _ lang st_pf, lc_pf) (existT _ lang st_j, lc_j)
                      (existT _ lang st_apf, lc_apf) (existT _ lang st_ra, lc_ra)
    .

    Definition option_rel4 {A B C D} (P: A -> B -> C -> D -> Prop):
      option A -> option B -> option C -> option D -> Prop :=
      fun a b c d =>
        match a, b, c, d with
        | Some x, Some y, Some z, Some w => P x y z w
        | None, None, None, None => True
        | _, _, _, _ => False
        end.

    Inductive sim_conf (views: Loc.t -> Time.t -> list View.t) (rels: Writes.t):
      forall (c_pf c_j c_apf c_ra: Configuration.t), Prop :=
    | sim_conf_intro
        ths_pf sc_pf mem_pf
        ths_j sc_j mem_j
        ths_apf sc_apf mem_apf
        ths_ra sc_ra mem_ra
        (THS: forall tid,
            option_rel4
              (sim_thread_sl views rels sc_pf sc_j sc_apf sc_ra mem_pf mem_j mem_apf mem_ra)
              (IdentMap.find tid ths_pf)
              (IdentMap.find tid ths_j)
              (IdentMap.find tid ths_apf)
              (IdentMap.find tid ths_ra)):
        sim_conf views rels
                 (Configuration.mk ths_pf sc_pf mem_pf)
                 (Configuration.mk ths_j sc_j mem_j)
                 (Configuration.mk ths_apf sc_apf mem_apf)
                 (Configuration.mk ths_ra sc_ra mem_ra)
    .

    Lemma init_wf_pf syn:
      wf_pf (Configuration.init syn).
    Proof.
      econs; eauto using Configuration.init_wf, PF.configuration_init_pf.
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
      econs; eauto using Configuration.init_wf; i; ss.
      - unfold Threads.init in *.
        rewrite IdentMap.Facts.map_o in *.
        destruct (@UsualFMapPositive.UsualPositiveMap'.find
                    (@sigT _ (@Language.syntax ProgramEvent.t)) tid syn); inv TH.
        apply inj_pair2 in H1. subst. ss. ii.
        rewrite Memory.bot_get in *. ss.
      - econs; i; ss.
        unfold Memory.get, Memory.init, Cell.get, Cell.init in *. ss.
        apply DOMap.singleton_find_inv in GET. des. inv GET0. ss.
    Qed.

    Lemma init_sim_conf syn:
      sim_conf (fun _ => fun _ => []) []
               (Configuration.init syn) (Configuration.init syn)
               (Configuration.init syn) (Configuration.init syn).
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
      - econs; ss. econs; ss; eauto. i.
        unfold Memory.get, Memory.init, Cell.get, Cell.init in *. ss.
        apply DOMap.singleton_find_inv in GET. des. inv GET0. ss.
      - econs; ss.
        + econs; ss. econs; ss. i. condtac; ss. refl.
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
          views rrels c_pf c_j c_apf c_ra
          (SIM: sim_conf views rrels c_pf c_j c_apf c_ra)
          (TERMINAL: Configuration.is_terminal c_pf):
      Configuration.is_terminal c_ra.
    Proof.
      ii. inv SIM. specialize (THS tid).
      unfold option_rel4 in *. ss. des_ifs.
      destruct p as [[]], p0 as [[]], p1 as [[]]. inv THS.
      apply inj_pair2 in H7, H4, H1, H10. subst.
      inv SIM. inv SIM_JOINED. inv SIM_APF. inv SIM_RA. ss.
      apply inj_pair2 in H2, H6. subst.
      exploit TERMINAL; eauto. i. des.
      split; ss.
      inv THREAD. econs.
      inv LOCAL1. rewrite PROMISES0.
      eapply JSim.sim_local_memory_bot; eauto.
    Qed.


    (* step *)

    Lemma sim_conf_step
          views1 rels1 c1_pf c1_j c1_apf c1_ra
          tid e_pf c2_pf
          (SIM1: sim_conf views1 rels1 c1_pf c1_j c1_apf c1_ra)
          (WF1_PF: wf_pf c1_pf)
          (WF1_J: wf_j views1 c1_j)
          (WF1_APF: wf_ra rels1 c1_apf)
          (WF1_RA: wf_ra rels1 c1_ra)
          (STEP: PFConfiguration.step L e_pf tid c1_pf c2_pf):
      (exists e_j c2_j e_apf c2_apf views2 e_ra rels2 c2_ra,
          (<<STEP_J: JConfiguration.single_step e_j tid c1_j c2_j views1 views2>>) /\
          (<<STEP_APF: WConfiguration.step L Ordering.na Ordering.plain
                                           e_apf tid rels1 rels2 c1_apf c2_apf>>) /\
          (<<STEP_RA: WConfiguration.step L Ordering.acqrel Ordering.acqrel
                                          e_ra tid rels1 rels2 c1_ra c2_ra>>) /\
          (<<EVENT_J: JSim.sim_event e_j e_pf>>) /\
          (<<EVENT_APF: PFtoAPFSim.sim_event e_apf e_j>>) /\
          (<<EVENT_RA: APFtoRASim.sim_event e_ra e_apf>>) /\
          (<<SIM2: sim_conf views2 rels2 c2_pf c2_j c2_apf c2_ra>>)) \/
      (<<RACE: RARaceW.ra_race_steps L Ordering.acqrel Ordering.acqrel rels1 c1_ra>>).
    Proof.
      dup SIM1. inv SIM0. inv STEP. ss.
      dup THS. specialize (THS0 tid). unfold option_rel4 in THS0. des_ifs. 
      inv THS0. apply inj_pair2 in H1. subst.
      exploit wf_pf_thread; eauto. s. i.
      exploit wf_j_thread; eauto. s. i.
      exploit wf_ra_thread; try exact WF1_APF; eauto. s. i.
      exploit wf_ra_thread; try exact WF1_RA; eauto. s. i.
      exploit PFtoRAThread.sim_thread_cancel_steps; eauto.
      { exploit PFtoRAThread.cancel_steps_pf_future; eauto. i.
        exploit PFtoRAThread.opt_step_pf_future; eauto. i.
        exploit PFtoRAThread.reserve_steps_pf_future; eauto. i.
        destruct (classic (ThreadEvent.get_machine_event e_pf = MachineEvent.failure)).
        - inv STEP0; ss. inv STEP; inv STEP0; ss.
          inv LOCAL; ss; inv LOCAL0; ss.
        - eapply opt_step_promise_consistent; eauto; try apply x4.
          eapply rtc_reserve_step_promise_consistent; eauto.
          eapply consistent_promise_consistent;
            try eapply PF.pf_consistent_consistent; eauto; try apply x6.
      }
      i. des.
      exploit PFtoRAThread.cancel_steps_pf_future; eauto. i.
      exploit PFtoRAThread.cancel_steps_j_future; eauto. i.
      exploit PFtoRAThread.cancel_steps_ra_future; try exact x2; eauto. i.
      exploit PFtoRAThread.cancel_steps_ra_future; try exact x3; eauto. i.
      exploit PFtoRAThread.sim_thread_opt_step; eauto.
      { exploit PFtoRAThread.opt_step_pf_future; eauto. i.
        exploit PFtoRAThread.reserve_steps_pf_future; eauto. i.
        destruct (classic (ThreadEvent.get_machine_event e_pf = MachineEvent.failure)).
        - inv STEP0; ss. inv STEP; inv STEP0; ss.
          inv LOCAL; ss; inv LOCAL0; ss.
        - eapply rtc_reserve_step_promise_consistent; eauto.
          eapply consistent_promise_consistent;
            try eapply PF.pf_consistent_consistent; eauto; try apply x9.
      }
      i. des; cycle 1.
      { right. unfold RARaceW.ra_race_steps.
        esplits; [econs 1|..]; eauto. s.
        eapply WThread.tau_steps_steps.
        eapply WThread.cancel_steps_tau_steps; eauto.
      }
      exploit PFtoRAThread.opt_step_pf_future; eauto. i.
      exploit PFtoRAThread.opt_step_j_future; eauto. i.
      exploit PFtoRAThread.opt_step_ra_future; try exact x6; eauto; ss. i.
      exploit PFtoRAThread.opt_step_ra_future; try exact x7; eauto; ss. i.
      exploit PFtoRAThread.sim_thread_reserve_steps; eauto.
      { exploit PFtoRAThread.reserve_steps_pf_future; eauto. s. i.
        destruct (classic (ThreadEvent.get_machine_event e_pf = MachineEvent.failure)).
        - hexploit rtc_reserve_step_promise_consistent2; eauto.
          inv STEP0; ss. inv STEP; inv STEP0; ss.
          inv LOCAL; ss; inv LOCAL0; ss.
        - hexploit consistent_promise_consistent;
            try eapply PF.pf_consistent_consistent; eauto; try apply x12.
      }
      i. des.
      exploit PFtoRAThread.reserve_steps_pf_future; eauto. i.
      exploit PFtoRAThread.reserve_steps_j_future; eauto. i.
      exploit PFtoRAThread.reserve_steps_ra_future; try exact x10; eauto. i.
      exploit PFtoRAThread.reserve_steps_ra_future; try exact x11; eauto. i.
      assert (STEPS': WThread.steps L Ordering.acqrel Ordering.acqrel
                                    rels1 rels2 (Thread.mk _ st_ra lc_ra sc_ra mem_ra) e2_ra1).
      { exploit WThread.tau_steps_steps;
          try eapply WThread.cancel_steps_tau_steps; try exact STEP_RA. i.
        exploit WThread.opt_step_steps; eauto. i.
        exploit WThread.tau_steps_steps;
          try eapply WThread.reserve_steps_tau_steps; try exact STEP_RA1. i.
        eapply WThread.steps_trans; eauto.
        eapply WThread.steps_trans; eauto.
      }

      destruct (classic (ThreadEvent.get_machine_event e_pf = MachineEvent.failure)).
      { destruct e2_j1 as [st4_j lc4_j sc4_j mem4_j],
                 e2_apf1 as [st4_apf lc4_apf sc4_apf mem4_apf],
                 e2_ra1 as [st4_ra lc4_ra sc4_ra mem4_ra].
        left. esplits.
        - econs; eauto. inv EVENT_J; ss.
        - econs; eauto. inv EVENT_J; inv EVENT_APF; ss.
        - econs; eauto. inv EVENT_J; inv EVENT_APF; inv EVENT_RA; ss.
        - ss.
        - ss.
        - ss.
        - econs; ss. i.
          repeat rewrite IdentMap.gsspec. condtac; ss.
          specialize (THS tid0). unfold option_rel4 in THS. des_ifs. inv THS. ss.
          inv SIM4. ss. econs. econs; s; eauto; try apply SIM3.
          * inv SIM_JOINED.
            apply inj_pair2 in H3, H7. subst.
            econs; s; eauto; try by (inv SIM3; inv SIM_JOINED; ss).
            exploit JThread.rtc_cancel_step_future; eauto; try apply x1. s. i. des.
            exploit JThread.opt_step_future; eauto; try apply x1. s. i. des.
            exploit JThread.rtc_reserve_step_future; eauto. s. i. des.
            eapply JSim.sim_local_le; try exact LOCAL.
            etrans; eauto. refl.
          * inv SIM_APF. ss. subst.
            econs; s; eauto; try by (inv SIM3; inv SIM_APF; ss).
          * inv SIM_RA. ss. subst.
            econs; s; eauto; try by (inv SIM3; inv SIM_RA; ss).
          * econs; try apply SIM3; try apply NORMAL_APF.
          * econs; try apply SIM3; try apply NORMAL_RA.
          * econs; s; try apply SIM3; try apply STABLE_RA.
            exploit WThread.steps_future; try exact STEPS'; try apply x3. s. i. des.
            exploit wf_ra_thread; try exact WF1_RA; try eapply Heq6. s. i.
            exploit Stable.future_stable_tview; try eapply STABLE_RA; try apply x16; eauto.
      }

      exploit PFtoRAThread.sim_thread_consistent; try eapply CONSISTENT; eauto. i. des; cycle 1.
      { right. unfold RARaceW.ra_race_steps.
        esplits; [econs 1|..]; try eapply RACE; eauto. s.
        eapply WThread.steps_trans; eauto.
        eapply WThread.tau_steps_steps; eauto.
      }
      destruct e2_j1 as [st4_j lc4_j sc4_j mem4_j],
               e2_apf1 as [st4_apf lc4_apf sc4_apf mem4_apf],
               e2_ra1 as [st4_ra lc4_ra sc4_ra mem4_ra].
      left. esplits.
      - econs; eauto.
      - econs; eauto.
      - econs; eauto.
      - ss.
      - ss.
      - ss.
      - econs; ss. i.
        repeat rewrite IdentMap.gsspec. condtac; ss.
        specialize (THS tid0). unfold option_rel4 in THS. des_ifs. inv THS. ss.
        inv SIM4. ss. econs. econs; s; eauto; try apply SIM3.
        * inv SIM_JOINED.
          apply inj_pair2 in H3, H7. subst.
          econs; s; eauto; try by (inv SIM3; inv SIM_JOINED; ss).
          exploit JThread.rtc_cancel_step_future; eauto; try apply x1. s. i. des.
          exploit JThread.opt_step_future; eauto; try apply x1. s. i. des.
          exploit JThread.rtc_reserve_step_future; eauto. s. i. des.
          eapply JSim.sim_local_le; try exact LOCAL.
          etrans; eauto. refl.
        * inv SIM_APF. ss. subst.
          econs; s; eauto; try by (inv SIM3; inv SIM_APF; ss).
        * inv SIM_RA. ss. subst.
          econs; s; eauto; try by (inv SIM3; inv SIM_RA; ss).
        * econs; try apply SIM3; try apply NORMAL_APF.
        * econs; try apply SIM3; try apply NORMAL_RA.
        * econs; s; try apply SIM3; try apply STABLE_RA.
          exploit WThread.steps_future; try exact STEPS'; try apply x3. s. i. des.
          exploit wf_ra_thread; try exact WF1_RA; try eapply Heq6. s. i.
          exploit Stable.future_stable_tview; try eapply STABLE_RA; try apply x16; eauto.
    Qed.

    Lemma sim_conf_steps
          views1 rels1 c1_pf c1_j c1_apf c1_ra
          c2_pf
          (SIM1: sim_conf views1 rels1 c1_pf c1_j c1_apf c1_ra)
          (WF1_PF: wf_pf c1_pf)
          (WF1_J: wf_j views1 c1_j)
          (WF1_APF: wf_ra rels1 c1_apf)
          (WF1_RA: wf_ra rels1 c1_ra)
          (STEPS: rtc (PFConfiguration.all_step L) c1_pf c2_pf):
      (exists c2_j c2_apf views2 rels2 c2_ra,
          (<<STEPS_J: JConfiguration.single_steps c1_j c2_j views1 views2>>) /\
          (<<STEPS_APF: WConfiguration.steps L Ordering.na Ordering.plain rels1 rels2 c1_apf c2_apf>>) /\
          (<<STEPS_RA: WConfiguration.steps L Ordering.acqrel Ordering.acqrel rels1 rels2 c1_ra c2_ra>>) /\
          (<<SIM2: sim_conf views2 rels2 c2_pf c2_j c2_apf c2_ra>>)) \/
      (<<RACE: RARaceW.ra_race_steps L Ordering.acqrel Ordering.acqrel rels1 c1_ra>>).
    Proof.
      revert views1 rels1 c1_j c1_apf c1_ra SIM1 WF1_PF WF1_J WF1_APF WF1_RA.
      induction STEPS; i.
      { left. esplits; try by econs 1. ss. }
      inv H. exploit sim_conf_step; eauto. i. des; eauto.
      exploit step_pf_future; eauto. i. des.
      exploit step_j_future; eauto. i. des.
      exploit step_ra_future; try exact STEP_APF; eauto. i. des.
      exploit step_ra_future; try exact STEP_RA; eauto. i. des.
      exploit IHSTEPS; eauto. i. des.
      - left. esplits; (try by econs 2; eauto); ss.
      - right. unfold RARaceW.ra_race_steps in *. des.
        esplits; [econs 2; eauto|..]; eauto.
    Qed.


    (* racefree *)

    Lemma sim_conf_racy_read
          views1 rels1 c1_pf c1_j c1_apf c1_ra
          loc ts e_pf tid c2_pf
          (SIM1: sim_conf views1 rels1 c1_pf c1_j c1_apf c1_ra)
          (WF1_PF: wf_pf c1_pf)
          (WF1_J: wf_j views1 c1_j)
          (WF1_APF: wf_ra rels1 c1_apf)
          (WF1_RA: wf_ra rels1 c1_ra)
          (STEP: PFRace.racy_read_step L loc ts e_pf tid c1_pf c2_pf)
          (LOC: L loc)
          (RELS: exists ord, List.In (loc, ts, ord) rels1 /\ Ordering.le ord Ordering.strong_relaxed):
      (<<RACE: RARaceW.ra_race_steps L Ordering.acqrel Ordering.acqrel rels1 c1_ra>>).
    Proof.
      inv STEP. inv SIM1. ss.
      specialize (THS tid). unfold option_rel4 in THS. des_ifs.
      inv THS. apply inj_pair2 in H1. subst.
      exploit wf_pf_thread; eauto. s. i.
      exploit wf_j_thread; eauto. s. i.
      exploit wf_ra_thread; try exact WF1_APF; eauto. s. i.
      exploit wf_ra_thread; try exact WF1_RA; eauto. s. i.
      exploit PFtoRAThread.sim_thread_cancel_steps; eauto.
      { destruct (classic (ThreadEvent.get_machine_event e_pf = MachineEvent.failure)).
        - inv STEP0; ss. inv STEP; inv STEP0; ss. inv LOCAL; ss; inv LOCAL0; ss.
        - exploit PFtoRAThread.cancel_steps_pf_future; eauto. i.
          exploit PFtoRAThread.opt_step_pf_future; eauto. i.
          exploit PFtoRAThread.reserve_steps_pf_future; eauto. i.
          eapply opt_step_promise_consistent; eauto; try eapply x4.
          eapply rtc_reserve_step_promise_consistent; eauto.
          eapply consistent_promise_consistent; try eapply PF.pf_consistent_consistent;
            try eapply CONSISTENT; try eapply x6; eauto.
      }
      i. des.
      exploit PFtoRAThread.cancel_steps_pf_future; try eapply x0; eauto. i.
      exploit PFtoRAThread.cancel_steps_j_future; try eapply x1; eauto. i.
      exploit PFtoRAThread.cancel_steps_ra_future; try eapply x2; eauto. i.
      exploit PFtoRAThread.cancel_steps_ra_future; try eapply x3; eauto. i.
      exploit PFtoRAThread.sim_thread_opt_step; eauto.
      { destruct (classic (ThreadEvent.get_machine_event e_pf = MachineEvent.failure)).
        - inv STEP0; ss. inv STEP; inv STEP0; ss. inv LOCAL; ss; inv LOCAL0; ss.
        - exploit PFtoRAThread.opt_step_pf_future; eauto. i.
          exploit PFtoRAThread.reserve_steps_pf_future; eauto. i.
          eapply rtc_reserve_step_promise_consistent; eauto.
          eapply consistent_promise_consistent; try eapply PF.pf_consistent_consistent;
            try eapply CONSISTENT; try eapply x9; eauto.
      }
      i. unfold RARaceW.ra_race_steps. des; cycle 1.
      { esplits; [econs 1|..]; eauto. s.
        eapply WThread.tau_steps_steps; eapply WThread.cancel_steps_tau_steps; eauto.
      }
      hexploit PFtoAPFSim.sim_thread_promise_consistent; try eapply SIM2; i.
      { inv SIM2. inv SIM_JOINED.
        apply inj_pair2 in H2, H3. subst. ss.
        eapply JSim.sim_local_promise_consistent; eauto.
        exploit PFtoRAThread.reserve_steps_pf_future; eauto. i.
        destruct (classic (ThreadEvent.get_machine_event e_pf = MachineEvent.failure)).
        - inv STEP0; ss. inv STEP; inv STEP0; ss. inv LOCAL0; ss; inv LOCAL1; ss.
        - exploit PFtoRAThread.opt_step_pf_future; eauto. i. des.
          exploit PFtoRAThread.reserve_steps_pf_future; eauto. i.
          hexploit consistent_promise_consistent; try eapply PF.pf_consistent_consistent;
            try eapply CONSISTENT; try eapply x10; eauto. s. i.
          hexploit rtc_reserve_step_promise_consistent; try exact H1; eauto. i.
          hexploit opt_step_promise_consistent; try eapply x8; eauto.
      }
      hexploit APFtoRASim.sim_local_promise_consistent; try eapply SIM2; eauto. i.
      inv READ; inv EVENT_J; inv EVENT_APF; inv EVENT_RA; ss.
      - inv STEP_RA0. inv STEP; ss. inv STEP1; inv STEP; ss. inv LOCAL; ss.
        esplits; [econs 1|..].
        + eauto.
        + eapply WThread.tau_steps_steps; eapply WThread.cancel_steps_tau_steps; eauto.
        + ss.
        + eauto.
        + unfold RARaceW.ra_race.
          left. esplits; eauto; ss.
          inv SIM2. inv SIM_JOINED. inv SIM_APF. inv SIM_RA. ss.
          apply inj_pair2 in H4, H5. subst. ss.
          unfold RARaceW.wr_race.
          inv LOCAL2. inv TVIEW. rewrite CUR.
          esplits; eauto.
          eapply TimeFacts.le_lt_lt; eauto. condtac.
          * inv LOCAL. inv TVIEW. inv CUR0. apply RLX.
          * inv LOCAL. inv TVIEW. inv CUR0.
            inv NORMAL_APF. inv NORMAL_TVIEW. ss.
            destruct e2_apf; ss. subst. ss.
            rewrite CUR0; ss.
      - inv STEP_RA0. inv STEP; ss. inv STEP1; inv STEP; ss. inv LOCAL; ss.
        esplits; [econs 1|..].
        + eauto.
        + eapply WThread.tau_steps_steps; eapply WThread.cancel_steps_tau_steps; eauto.
        + ss.
        + eauto.
        + unfold RARaceW.ra_race.
          left. esplits; eauto; ss.
          inv SIM2. inv SIM_JOINED. inv SIM_APF. inv SIM_RA. ss.
          apply inj_pair2 in H4, H5. subst. ss.
          unfold RARaceW.wr_race.
          inv LOCAL3. inv TVIEW. rewrite CUR.
          esplits; eauto.
          eapply TimeFacts.le_lt_lt; eauto. condtac.
          * inv LOCAL. inv TVIEW. inv CUR0. apply RLX.
          * inv LOCAL. inv TVIEW. inv CUR0.
            inv NORMAL_APF. inv NORMAL_TVIEW. ss.
            destruct e2_apf; ss. subst. ss.
            rewrite CUR0; ss.
    Qed.

    Lemma sim_conf_racefree
          views rels c_pf c_j c_apf c_ra
          (SIM: sim_conf views rels c_pf c_j c_apf c_ra)
          (WF_PF: wf_pf c_pf)
          (WF_J: wf_j views c_j)
          (WF_APF: wf_ra rels c_apf)
          (WF_RA: wf_ra rels c_ra)
          (RA_RACEFREE: RARaceW.racefree L Ordering.acqrel Ordering.acqrel rels c_ra):
      PFRace.racefree_view L c_pf.
    Proof.
      ii. exploit sim_conf_steps; eauto. i. des; cycle 1.
      { unfold RARaceW.ra_race_steps in *. des. eauto. }
      exploit steps_pf_future; eauto. i. des.
      exploit steps_j_future; eauto. i. des.
      exploit steps_ra_future; try exact WF_APF; eauto; ss. i. des.
      exploit steps_ra_future; try exact WF_RA; eauto; ss. i. des.
      inv WRITE.
      exploit sim_conf_step; try exact STEP; eauto. i. des; cycle 1.
      { unfold RARaceW.ra_race_steps in *. des.
        eapply RA_RACEFREE; cycle 1; eauto.
        eapply WConfiguration.steps_trans; eauto.
      }
      assert (WRITE_RA: exists ord, List.In (loc, ts, ord) rels0 /\ Ordering.le ord Ordering.strong_relaxed).
      { inv WRITE0; inv EVENT_J; inv EVENT_APF; inv EVENT_RA; ss.
        - inv STEP_APF. ss. inv STEP0; ss. inv STEP1.
          unfold Writes.append. ss. condtac; ss.
          esplits; [left|]; eauto.
        - inv STEP_APF. ss. inv STEP0; ss. inv STEP1.
          unfold Writes.append. ss. condtac; ss.
          esplits; [left|]; eauto.
      }
      exploit step_pf_future; try exact STEP; eauto. i. des.
      exploit step_j_future; try exact STEP_J; eauto. i. des.
      exploit step_ra_future; try exact STEP_APF; eauto. i. des.
      exploit step_ra_future; try exact STEP_RA; eauto. i. des.
      exploit sim_conf_steps; try exact CSTEPS2; eauto. i. des; cycle 1.
      { unfold RARaceW.ra_race_steps in *. des.
        eapply RA_RACEFREE; cycle 1; eauto.
        eapply WConfiguration.steps_trans; [eauto|].
        econs 2; eauto.
      }
      exploit steps_pf_future; try exact CSTEPS2; eauto. i. des.
      exploit steps_j_future; try exact STEPS_J0; eauto. i. des.
      exploit steps_ra_future; try exact STEPS_APF0; eauto. i. des.
      exploit steps_ra_future; try exact STEPS_RA0; eauto. i. des.
      assert (READ_RA: exists ord, List.In (loc, ts, ord) rels1 /\ Ordering.le ord Ordering.strong_relaxed).
      { exploit WConfiguration.steps_rels_incl; try exact STEPS_APF0. i. des. subst.
        esplits.
        - apply List.in_or_app. right. eauto.
        - ss.
      }
      exploit sim_conf_racy_read; eauto. unfold RARaceW.ra_race_steps. i. des.
      eapply RA_RACEFREE; cycle 1; eauto.
      eapply WConfiguration.steps_trans; eauto.
      eapply WConfiguration.steps_trans; eauto.
      econs 2; eauto.
    Qed.


    (* behaviors *)

    Lemma sim_conf_behavior
          views rels c_pf c_j c_apf c_ra
          (SIM: sim_conf views rels c_pf c_j c_apf c_ra)
          (WF_PF: wf_pf c_pf)
          (WF_J: wf_j views c_j)
          (WF_APF: wf_ra rels c_apf)
          (WF_RA: wf_ra rels c_ra)
          (RACEFREE: RARaceW.racefree L Ordering.acqrel Ordering.acqrel rels c_ra):
      behaviors (PFConfiguration.machine_step L) c_pf <2=
      behaviors (@OrdConfiguration.machine_step L Ordering.acqrel Ordering.acqrel) c_ra.
    Proof.
      i. revert views rels c_j c_apf c_ra SIM WF_PF WF_J WF_APF WF_RA RACEFREE.
      induction PR; i.
      - econs 1. eapply sim_conf_terminal; eauto.
      - inv STEP. exploit sim_conf_step; eauto. i. des.
        + exploit RARaceW.step_ord_step; eauto. i.
          inv EVENT_J; inv EVENT_APF; inv EVENT_RA; ss. inv H0.
          econs 2.
          { replace (MachineEvent.syscall e2) with
                (ThreadEvent.get_machine_event (ThreadEvent.syscall e2)) by ss.
            econs; eauto.
          }
          hexploit RARaceW.step_racefree; eauto. i.
          exploit step_pf_future; eauto. i. des.
          exploit step_j_future; eauto. i. des.
          exploit step_ra_future; try exact STEP_APF; eauto. i. des.
          exploit step_ra_future; try exact STEP_RA; eauto. ss.
        + exfalso. unfold RARaceW.ra_race_steps in *. des. eauto.
      - inv STEP. exploit sim_conf_step; eauto. i. des.
        + exploit RARaceW.step_ord_step; eauto. i.
          econs 3.
          replace MachineEvent.failure with (ThreadEvent.get_machine_event e_ra); [econs; eauto|].
          inv EVENT_J; inv EVENT_APF; inv EVENT_RA; ss.
        + exfalso. unfold RARaceW.ra_race_steps in *. des. eauto.
      - inv STEP. exploit sim_conf_step; eauto. i. des.
        + exploit RARaceW.step_ord_step; eauto. i.
          econs 4.
          { replace MachineEvent.silent with (ThreadEvent.get_machine_event e_ra); cycle 1.
            { inv EVENT_J; inv EVENT_APF; inv EVENT_RA; ss. }
            econs; eauto.
          }
          hexploit RARaceW.step_racefree; eauto. i.
          exploit step_pf_future; eauto. i. des.
          exploit step_j_future; eauto. i. des.
          exploit step_ra_future; try exact STEP_APF; eauto. i. des.
          exploit step_ra_future; try exact STEP_RA; eauto.
        + exfalso. unfold RARaceW.ra_race_steps in *. des. eauto.
      - econs 5.
    Qed.
  End PFtoRA.
End PFtoRA.
