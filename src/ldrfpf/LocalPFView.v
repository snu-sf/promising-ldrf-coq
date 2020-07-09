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
Require SimMemory.

Require Import TimeTraced2.
Require Import LocalPF.
Require Import LocalPFThread.
Require Import LocalPFSimView.

Set Implicit Arguments.



Lemma PF_sim_configuration_beh L times c_src c_mid c_tgt views prom extra
      (WO: forall loc, well_ordered (times loc))
      (INCR: forall nat loc, times loc (incr_time_seq nat))
      (RACEFRFEE: pf_racefree_view L c_src)
      (WF_SRC: Configuration.wf c_src)
      (WF_MID: JConfiguration.wf views c_mid)
      (WF_TGT: Configuration.wf c_tgt)
      (SIM: sim_configuration L times (fun _ => True) views prom extra c_src c_mid c_tgt)
  :
    behaviors (times_configuration_step_all times) c_tgt <1=
    behaviors (pf_step L) c_src.
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
                                       (snd the)) (tr))).
    { destruct (classic (List.Forall
                           (fun the => no_read_msgs
                                         (all_promises (fun tid' => tid <> tid') prom)
                                         (snd the)) (tr_cert))).
      { exploit (step_sim_configuration); eauto.
        { instantiate (1:=true). ss. }
        i. des. unguard. des; ss. dep_inv STEPSRC.
        econs 2; eauto.
        { econs; eauto. }
        { eapply IHPR; try apply SIM0; eauto.
          { eapply steps_pf_racefree_view; eauto. econs; eauto. econs. }
          { eapply pf_step_trace_future; eauto. }
          { eapply JConfiguration.step_future; eauto. }
          { eapply times_configuration_step_future; eauto. }
        }
      }
      { exploit promise_read_race_certfication; eauto. i. des; clarify. }
    }
    { exploit promise_read_race; eauto. i. des; clarify. }
  }
  { inv STEP.
    destruct (classic (List.Forall
                         (fun the => no_read_msgs
                                       (all_promises (fun tid' => tid <> tid') prom)
                                       (snd the)) (tr))).
    { destruct (classic (List.Forall
                           (fun the => no_read_msgs
                                         (all_promises (fun tid' => tid <> tid') prom)
                                         (snd the)) (tr_cert))).
      { exploit step_sim_configuration; eauto.
        { instantiate (1:=true). ss. }
        i. des. unguard. des; ss.
        { dep_inv STEPSRC. econs 3; eauto. econs; eauto. }
        { dep_inv STEPSRC. econs 3; eauto. econs; eauto. }
      }
      { exploit promise_read_race_certfication; eauto. i. des; clarify. }
    }
    { exploit promise_read_race; eauto. i. des; clarify. }
  }
  { inv STEP.
    destruct (classic (List.Forall
                         (fun the => no_read_msgs
                                       (all_promises (fun tid' => tid <> tid') prom)
                                       (snd the)) (tr))).
    { destruct (classic (List.Forall
                           (fun the => no_read_msgs
                                         (all_promises (fun tid' => tid <> tid') prom)
                                         (snd the)) (tr_cert))).
      { exploit step_sim_configuration; eauto.
        { instantiate (1:=true). ss. }
        i. des. ss. dep_inv STEPSRC.
        { econs 4; eauto.
          { econs; eauto. }
          { destruct x0; ss. des.
            eapply IHPR; try apply SIM0; eauto.
            { eapply steps_pf_racefree_view; eauto. econs; eauto. econs. }
            { eapply pf_step_trace_future; eauto. }
            { eapply JConfiguration.step_future; eauto. }
            { eapply times_configuration_step_future; eauto. }
          }
        }
        { destruct x0; ss. des.
          eapply IHPR; try apply SIM0; eauto.
          { eapply JConfiguration.step_future; eauto. }
          { eapply times_configuration_step_future; eauto. }
        }
      }
      { exploit promise_read_race_certfication; eauto. i. des; clarify. }
    }
    { exploit promise_read_race; eauto. i. des; clarify. }
  }
Qed.


Theorem local_DRFPF L s
        (RACEFRFEE: pf_racefree_view L (Configuration.init s))
  :
    behaviors Configuration.step (Configuration.init s) <1=
    behaviors (pf_step L) (Configuration.init s).
Proof.
  i. eapply times_configuration_step_same_behaviors in PR; cycle 1.
  { eapply Configuration.init_wf. }
  des. eapply PF_sim_configuration_beh; eauto.
  { eapply Configuration.init_wf. }
  { eapply JConfiguration.init_wf. }
  { eapply Configuration.init_wf. }
  instantiate (1:=s). instantiate (1:=bot4). instantiate (1:=bot3). econs; eauto.
  { i. unfold Threads.init. repeat erewrite IdentMap.Facts.map_o.
    unfold option_map. des_ifs. ss. econs. econs.
    econs; ss. i. erewrite Memory.bot_get. destruct (classic (L loc)).
    { econs 1; eauto. }
    { econs 2; eauto.  }
  }
  { i. unfold Threads.init. repeat erewrite IdentMap.Facts.map_o.
    unfold option_map. des_ifs. ss. econs. econs.
    { refl. }
    { ii. erewrite Memory.bot_get. econs. }
  }
  { i. splits; ss. }
  { econs.
    { i. unfold Memory.init, Memory.get. erewrite Cell.init_get. des_ifs.
      { econs 2; eauto.
        { ii. inv H. ss. }
        { ii. inv H. ss. }
        { refl. }
        { i. apply eq_lb_time. }
      }
      { econs.
        { ii. inv H. ss. }
        { ii. inv H. ss. }
      }
    }
    { i. inv EXTRA. ss. }
  }
  { refl. }
  { i. unfold JConfiguration.init_views. des_ifs. econs; eauto.
    eapply Memory.closed_view_bot. eapply Memory.init_closed. }
  { refl. }
  { ii. unfold Memory.init, Memory.get in GET. erewrite Cell.init_get in GET.
    des_ifs. auto. }
  { i. unfold Threads.init in GET. erewrite IdentMap.Facts.map_o in GET.
    unfold option_map in GET. des_ifs. dep_clarify. ii. ss. eexists [], _. splits; auto.
    { refl. }
    { right. ss. }
  }
  { i. unfold Threads.init in GET. erewrite IdentMap.Facts.map_o in GET.
    unfold option_map in GET. des_ifs. dep_clarify. ii. ss. eexists [], _. splits; auto.
    { refl. }
    { right. ss. }
  }
Qed.


(* Lemma pf_racefree_pf_racefree_tview L c *)
(*       (WF: Configuration.wf c) *)
(*       (RACEFREE: pf_racefree_view L c) *)
(*   : *)
(*     pf_racefree L c. *)
