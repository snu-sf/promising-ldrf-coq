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
Require Import LocalPF.
Require Import LocalPFThread.
Require Import LocalPFSim.
Require Import JoinedViewExist.

Set Implicit Arguments.



Lemma PF_sim_configuration_beh L times c_src c_mid c_tgt views prom extra proml
      (WO: forall loc, well_ordered (times loc))
      (INCR: forall nat loc, times loc (incr_time_seq nat))
      (RACEFRFEE: pf_multi_racefree L c_src)
      (WF_SRC: Configuration.wf c_src)
      (PFSRC: pf_configuration L c_src)
      (WF_MID: JConfiguration.wf views c_mid)
      (WF_TGT: Configuration.wf c_tgt)
      (SIM: sim_configuration L times (fun _ => True) views prom extra proml c_src c_mid c_tgt)
  :
    behaviors (times_configuration_step_strong_all times) c_tgt <1=
    behaviors (pf_multi_step L) c_src.
Proof.
  i. ginduction PR; i.
  { dep_inv SIM. econs 1. ii. ss.
    specialize (THSPF tid). specialize (THSJOIN tid).
    setoid_rewrite FIND in THSPF. unfold option_rel in *. des_ifs.
    dep_inv THSPF. dep_inv THSJOIN.
    eapply TERMINAL in Heq0. des. splits; auto.
    inv THREAD. inv LOCAL. inv LOCAL0. ss. subst.
    econs. exploit sim_promise_bot; eauto. eapply Memory.ext.
    i. specialize (PROMISES0 loc ts). erewrite Memory.bot_get in *.
    inv PROMISES0; ss. }
  { inv STEP.
    destruct (classic (List.Forall
                         (fun the => no_read_msgs
                                       (all_promises (fun tid' => tid <> tid') prom)
                                       (snd the)) (tr ++ tr_cert))).
    { eapply Forall_app_inv in H. des.
      eapply times_configuration_step_strong_step in STEP0.
      exploit (step_sim_configuration); eauto.
      i. des. unguard. des; ss. dep_inv STEPSRC.
      econs 2; eauto.
      { econs; eauto. }
      { eapply IHPR; try apply SIM0; eauto.
        { eapply multi_steps_pf_multi_racefree; eauto. econs; eauto. econs. }
        { eapply pf_step_trace_future; eauto. }
        { eapply pf_step_trace_future; eauto. }
        { eapply JConfiguration.step_future; eauto. }
        { eapply times_configuration_step_future; eauto. }
      }
    }
    { exploit promise_read_race; eauto. i. des; clarify. }
  }
  { inv STEP.
    destruct (classic (List.Forall
                         (fun the => no_read_msgs
                                       (all_promises (fun tid' => tid <> tid') prom)
                                       (snd the)) (tr ++ tr_cert))).
    { eapply Forall_app_inv in H. des.
      eapply times_configuration_step_strong_step in STEP0.
      exploit step_sim_configuration; eauto.
      i. des. unguard. des; ss.
      { dep_inv STEPSRC. econs 3; eauto. econs; eauto. }
      { dep_inv STEPSRC. econs 3; eauto. econs; eauto. }
    }
    { exploit promise_read_race; eauto. i. des; clarify. }
  }
  { inv STEP.
    destruct (classic (List.Forall
                         (fun the => no_read_msgs
                                       (all_promises (fun tid' => tid <> tid') prom)
                                       (snd the)) (tr ++ tr_cert))).
    { eapply Forall_app_inv in H. des.
      eapply times_configuration_step_strong_step in STEP0.
      exploit step_sim_configuration; eauto.
      i. des. ss. dep_inv STEPSRC.
      { econs 4; eauto.
        { econs; eauto. }
        { destruct x1; ss. des.
          eapply IHPR; try apply SIM0; eauto.
          { eapply multi_steps_pf_multi_racefree; eauto. econs; eauto. econs. }
          { eapply pf_step_trace_future; eauto. }
          { eapply pf_step_trace_future; eauto. }
          { eapply JConfiguration.step_future; eauto. }
          { eapply times_configuration_step_future; eauto. }
        }
      }
      { destruct x1; ss. des.
        eapply IHPR; try apply SIM0; eauto.
        { eapply JConfiguration.step_future; eauto. }
        { eapply times_configuration_step_future; eauto. }
      }
    }
    { exploit promise_read_race; eauto. i. des; clarify. }
  }
Qed.

Lemma local_drf_pf_multi L c
      (PF: pf_configuration L c)
      (WF: Configuration.wf c)
      (RACEFRFEE: pf_multi_racefree L c)
  :
    behaviors Configuration.step c <1=
    behaviors (pf_multi_step L) c.
Proof.
  hexploit joined_view_exist; eauto. intros [views JWF].
  i. eapply times_configuration_step_same_behaviors in PR; eauto.
  des. hexploit (PFConsistentStrong.memory_times_wf_exists c.(Configuration.memory)).
  i. des.
  eapply (@PF_sim_configuration_beh L (times \2/ times_mem)); eauto.
  { i. eapply join_well_ordered; eauto. }
  instantiate (1:=fun _ => []).
  instantiate (1:=bot4). instantiate (1:=bot3). destruct c. econs; eauto.
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
  { ii. eapply MWF in GET. des; auto. }
  { ii. eapply MWF in GET. des; auto. }
  { ii. econs; ss. i. destruct pl0; ss. }
  { i. right. splits; ss. }
  { eapply le_step_behavior_improve; [|apply BEH].
    eapply times_configuration_step_strong_all_mon; eauto. }
Qed.

Theorem local_drf_pf L c
        (PF: pf_configuration L c)
        (WF: Configuration.wf c)
        (RACEFREE: pf_racefree L c)
  :
    behaviors SConfiguration.machine_step c <1=
    behaviors (pf_machine_step L) c.
Proof.
  i. eapply SConfiguration.multi_step_equiv in PR; eauto.
  eapply pf_racefree_multi_racefree in RACEFREE; eauto.
  eapply pf_multi_step_behavior; eauto.
  eapply local_drf_pf_multi; eauto.
Qed.
