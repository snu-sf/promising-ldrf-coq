Require Import RelationClasses.

From Paco Require Import paco.
From sflib Require Import sflib.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import Language.
From PromisingLib Require Import Loc.
Require Import Time.
Require Import Event.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import MemoryFacts.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.
Require Import Progress.
Require Import Behavior.
Require Import Cover.
Require Import PromiseConsistent.
Require Import Pred.
Require Import Trace.
Require Import JoinedView.

Require Import MemoryProps.
Require Import OrderedTimes.
Require Import Single.
Require SimMemory.

Require Import TimeTraced.
Require Import RecoverForget.
Require Import PFStep.
Require Import LocalPFThread.
Require Import LocalPFSim.
Require Import JoinedViewExist.

Require Import LocalPFSimTime.

Set Implicit Arguments.



Lemma PF_sim_configuration_step
      L times c_src0 c_mid0 c_tgt0 views0 prom0 extra0 proml0
      c_tgt1 tid e
      (WO: forall loc, well_ordered (times loc))
      (INCR: forall nat loc, times loc (incr_time_seq nat))
      (WFSRC: Configuration.wf c_src0)
      (PFSRC: PF.pf_configuration L c_src0)
      (WFMID: JConfiguration.wf views0 c_mid0)
      (WFTGT: Configuration.wf c_tgt0)
      (SIM: sim_configuration L times (fun _ => True) views0 prom0 extra0 proml0 c_src0 c_mid0 c_tgt0)
      (STEP: times_configuration_step_strong_all times e tid c_tgt0 c_tgt1)
  :
    (<<RACE: PFRace.racy_state L c_src0>>) \/
    (<<UB: forall beh, behaviors (PFConfiguration.machine_step L) c_src0 beh>>) \/
    (<<PROGRESS:
       exists c_src1 c_mid1 views1 prom1 extra1 proml1,
         (<<STEPSRC: exists c_src0',
             (<<STEPS: rtc (PFConfiguration.tau_machine_step L) c_src0 c_src0'>>) /\
             (<<STEP: PFConfiguration.opt_machine_step L e tid c_src0' c_src1>>)>>) /\
         (<<STEPMID: JConfiguration.step e tid c_mid0 c_mid1 views0 views1>>) /\
         (<<SIM: sim_configuration L times (fun _ => True) views1 prom1 extra1 proml1 c_src1 c_mid1 c_tgt1>>)>>).
Proof.
  destruct (classic (PFRace.racy_state L c_src0)) as [RACE|NRACE]; auto.
  right. inv STEP.
  destruct (classic (List.Forall
                       (fun the => no_read_msgs
                                     (all_promises (fun tid' => tid <> tid') prom0)
                                     (snd the)) (tr ++ tr_cert))).
  { eapply Forall_app_inv in H. des.
    eapply times_configuration_step_strong_step in STEP0.
    exploit (step_sim_configuration); eauto.
    i. des. unguard. des; clarify.
    { inv STEPSRC. left. ii. eapply PFConfiguration.multi_step_behavior; eauto.
      econs 3. econs; eauto. }
    { right. inv STEPSRC; eauto.
      { exploit PFConfiguration.multi_step_machine_step.
        { econs; eauto. }
        { eauto. }
        { eauto. } i. des.
        esplits; eauto.
      }
      { esplits; eauto. econs. }
    }
  }
  { left. ii. eapply PFConfiguration.multi_step_behavior; eauto.
    eapply promise_read_race; eauto. ii. eapply NRACE.
    eapply PFRace.multi_race_race; eauto.
  }
Qed.

Lemma PF_sim_configuration_behavior
      L times c_src0 c_mid0 c_tgt0 views0 prom0 extra0 proml0
      (WO: forall loc, well_ordered (times loc))
      (INCR: forall nat loc, times loc (incr_time_seq nat))
      (WF_SRC: Configuration.wf c_src0)
      (PFSRC: PF.pf_configuration L c_src0)
      (WF_MID: JConfiguration.wf views0 c_mid0)
      (WF_TGT: Configuration.wf c_tgt0)
      (SIM: sim_configuration L times (fun _ => True) views0 prom0 extra0 proml0 c_src0 c_mid0 c_tgt0)
      beh
      (BEH: behaviors (times_configuration_step_strong_all times) c_tgt0 beh)
  :
    (<<BEH: behaviors (PFConfiguration.machine_step L) c_src0 beh>>) \/
    (exists bhd btl c_src1,
        (<<EQ: beh = bhd ++ btl>>) /\
        (<<BHD: behaviors_partial (PFConfiguration.machine_step L) c_src0 c_src1 bhd>>) /\
        (<<RACE: PFRace.racy_state L c_src1>>) /\
        (<<BTL: behaviors SConfiguration.machine_step c_src1 btl>>)).
Proof.
  ginduction BEH; i.
  { inv SIM. left. econs 1. ii. ss.
    specialize (THSPF tid). specialize (THSJOIN tid).
    setoid_rewrite FIND in THSPF. unfold option_rel in *. des_ifs.
    dep_inv THSPF. dep_inv THSJOIN.
    eapply TERMINAL in Heq0. des. splits; auto.
    inv THREAD. inv LOCAL. inv LOCAL0. ss. subst.
    econs. exploit sim_promise_bot; eauto. eapply Memory.ext.
    i. specialize (PROMISES0 loc ts). erewrite Memory.bot_get in *.
    inv PROMISES0; ss.
  }
  { exploit PF_sim_configuration_step; try apply SIM; eauto. i. des.
    { right. exists [], (e::beh), c_src0. esplits; eauto.
      { econs. }
      { eapply sim_configuration_behavior; eauto.
        eapply SConfiguration.multi_step_equiv; eauto.
        eapply times_configuration_behavior_configuration_behavior; eauto.
        econs 2; eauto.
      }
    }
    { left. eauto. }
    { exploit PFConfiguration.rtc_tau_machine_step_future; eauto. i. des.
      exploit PFConfiguration.opt_machine_step_future; eauto. i. des.
      exploit JConfiguration.step_future; eauto. i. des.
      exploit IHBEH; try apply SIM0; eauto.
      { inv STEP. eapply times_configuration_step_strong_step in STEP1.
        eapply times_configuration_step_future; eauto. }
      i. inv STEP0. des.
      { left. eapply rtc_tau_step_behavior.
        { eapply STEPS. }
        { econs 2; eauto. }
      }
      { right. clarify.
        exists (e::bhd), btl, c_src2. splits; eauto.
        eapply rtc_tau_step_behavior_partial; eauto. econs 2; eauto.
      }
    }
  }
  { exploit PF_sim_configuration_step; try apply SIM; eauto. i. des.
    { right. exists [], beh, c_src0. esplits; eauto.
      { econs. }
      { eapply sim_configuration_behavior; eauto.
        eapply SConfiguration.multi_step_equiv; eauto.
        eapply times_configuration_behavior_configuration_behavior; eauto.
        econs 3; eauto.
      }
    }
    { left. eauto. }
    { left. inv STEP0. eapply rtc_tau_step_behavior; eauto.
      econs 3; eauto.
    }
  }
  { exploit PF_sim_configuration_step; try apply SIM; eauto. i. des.
    { right. exists [], beh, c_src0. esplits; eauto.
      { econs. }
      { eapply sim_configuration_behavior; eauto.
        eapply SConfiguration.multi_step_equiv; eauto.
        eapply times_configuration_behavior_configuration_behavior; eauto.
        econs 4; eauto.
      }
    }
    { left. eauto. }
    { exploit PFConfiguration.rtc_tau_machine_step_future; eauto. i. des.
      exploit PFConfiguration.opt_machine_step_future; eauto. i. des.
      exploit JConfiguration.step_future; eauto. i. des.
      exploit IHBEH; try apply SIM0; eauto.
      { inv STEP. eapply times_configuration_step_strong_step in STEP1.
        eapply times_configuration_step_future; eauto. }
      i. des.
      { left. eapply rtc_tau_step_behavior.
        { eapply STEPS. }
        { inv STEP0; eauto. econs 4; eauto. }
      }
      { right. clarify.
        exists bhd, btl, c_src2. splits; eauto.
        eapply rtc_tau_step_behavior_partial; eauto.
        inv STEP0; eauto. econs 3; eauto.
      }
    }
  }
Qed.

Lemma pf_configuration_sim_configuration L times c
      (PF: PF.pf_configuration L c)
      (WF: Configuration.wf c)
      (TIMES: memory_times_wf times c.(Configuration.memory))
  :
    exists views prom extra proml,
      (<<SIM: sim_configuration L times (fun _ => True) views prom extra proml c c c>>) /\
      (<<JWF: JConfiguration.wf views c>>)
.
Proof.
  hexploit joined_view_exist; eauto. intros [views JWF].
  exists views, bot3, bot4, (fun _ => []). splits; auto.
  destruct c. econs; eauto.
  { i. unfold option_rel. des_ifs. destruct p as [[lang st] [tview prom]].
    econs; eauto. econs; eauto. econs; i; ss.
    destruct (Memory.get loc ts prom) as [[from [val released|]]|] eqn:EQ; ss.
    - econs; eauto. ii. exploit PF; eauto. ss.
    - destruct (L loc) eqn:LOC; eauto.
      + econs 3; eauto.
      + econs 2; eauto. clarify.
    - destruct (L loc) eqn:LOC; eauto.
      + econs 1; eauto.
      + econs 2; eauto. clarify.
  }
  { i. unfold option_rel, language. des_ifs.
    destruct p as [[lang st] [tview prom]]. econs; eauto. econs; eauto.
    { refl. }
    { ii. destruct (Memory.get loc ts prom) as [[from [val [released|]|]]|] eqn:EQ; ss.
      - econs.
        + econs. econs; eauto.
          * eapply WF in Heq. eapply Heq in EQ. ss.
            eapply JWF in EQ. des. auto.
          * refl.
        + inv JWF. ss. eapply REL in Heq. ss.
          eapply Heq in EQ. right. ii. rewrite H in *. clarify.
      - econs; eauto. econs.
    }
  }
  { i. splits; ss. }
  { econs; ii.
    { destruct (Memory.get loc ts memory) as [[from msg]|] eqn:EQ; ss.
      - econs 2; eauto.
        + ii. inv H. ss.
        + ii. inv H. ss.
        + refl.
        + i. eapply eq_lb_time.
      - econs 1; eauto.
        + ii. inv H. ss.
        + ii. inv H. ss.
    }
    { inv EXTRA. ss. }
  }
  { refl. }
  { i. inv JWF. inv JOINMEM. eapply List.Forall_impl; [|apply CLOSED].
    ss. i. eapply closed_view_semi_closed; auto. }
  { refl. }
  { ii. econs; ss.
    { i. destruct pl0; ss. }
  }
  { i. right. splits; ss. }
Qed.


(* Time-wise LDRF-PF theorem *)
Theorem local_drf_pf_time L
        c0
        (PF: PF.pf_configuration L c0)
        (WF: Configuration.wf c0):
  forall beh
         (BEH: behaviors SConfiguration.machine_step c0 beh),
    (<<BEH: behaviors (PFConfiguration.machine_step L) c0 beh>>) \/
    (exists bhd btl c1,
        (<<EQ: beh = bhd ++ btl>>) /\
        (<<BHD: behaviors_partial (PFConfiguration.machine_step L) c0 c1 bhd>>) /\
        (<<RACE: PFRace.racy_state L c1>>) /\
        (<<BTL: behaviors SConfiguration.machine_step c1 btl>>)).
Proof.
  i. eapply SConfiguration.multi_step_equiv in BEH; eauto.
  eapply times_configuration_step_same_behaviors in BEH; eauto. des.
  hexploit (PFConsistentStrong.memory_times_wf_exists c0.(Configuration.memory)).
  i. des.
  hexploit (@pf_configuration_sim_configuration L (times \2/ times_mem)); eauto.
  { ii. eapply MWF in GET. des. splits; auto. }
  i. des.
  eapply (@PF_sim_configuration_behavior L (times \2/ times_mem)); eauto.
  { i. eapply join_well_ordered; eauto. }
  eapply le_step_behavior_improve in BEH0; eauto.
  i. eapply times_configuration_step_strong_all_mon in PR; eauto.
  i. left. auto.
Qed.
