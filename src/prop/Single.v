Require Import Lia.
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

From PromisingLib Require Import Event.
Require Import Time.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.
Require Import Pred.
Require Import Trace.
Require Import Behavior.

Require Import ReorderCancel.
Require Import ReorderReserve.
Require Import MemoryProps.
Require Import SplitCertification.

Set Implicit Arguments.


Module SConfiguration.

  Inductive step:
    forall (e:ThreadEvent.t) (tid:Ident.t) (c1 c2:Configuration.t), Prop :=
  | step_intro
      e tid c1 lang st1 lc1 e2 e3 st4 lc4 sc4 memory4
      (TID: IdentMap.find tid (Configuration.threads c1) = Some (existT _ lang st1, lc1))
      (CANCELS: rtc (@Thread.cancel_step _) (Thread.mk _ st1 lc1 (Configuration.sc c1) (Configuration.memory c1)) e2)
      (STEP: Thread.opt_step e e2 e3)
      (RESERVES: rtc (@Thread.reserve_step _) e3 (Thread.mk _ st4 lc4 sc4 memory4))
      (CONSISTENT: ThreadEvent.get_machine_event e <> MachineEvent.failure ->
                   Thread.consistent (Thread.mk _ st4 lc4 sc4 memory4)):
      step e tid c1 (Configuration.mk (IdentMap.add tid (existT _ _ st4, lc4) (Configuration.threads c1)) sc4 memory4)
  .
  #[global] Hint Constructors step: core.

  Inductive steps:
    forall (es: list ThreadEvent.t) (tid: Ident.t) (c1 c2:Configuration.t), Prop :=
  | steps_nil
      tid c1
    :
      steps [] tid c1 c1
  | steps_cons
      ehd etl tid c1 c2 c3
      (STEP: step ehd tid c1 c2)
      (STEPS: steps etl tid c2 c3)
    :
      steps (ehd :: etl) tid c1 c3
  .
  #[global] Hint Constructors steps: core.

  Lemma steps_trans es0 es1 tid c0 c1 c2
        (STEPS0: steps es0 tid c0 c1)
        (STEPS1: steps es1 tid c1 c2)
    :
      steps (es0 ++ es1) tid c0 c2.
  Proof.
    ginduction STEPS0; eauto.
    { i. ss. econs; eauto. }
  Qed.

  Lemma steps_split es0 es1 tid c0 c2
        (STEPS: steps (es0 ++ es1) tid c0 c2)
    :
      exists c1,
        (<<STEPS0: steps es0 tid c0 c1>>) /\
        (<<STEPS1: steps es1 tid c1 c2>>).
  Proof.
    ginduction es0; eauto. i. ss. inv STEPS.
    exploit IHes0; eauto. i. des.
    esplits; eauto.
  Qed.

  Inductive reservation_only_step:
    forall (tid:Ident.t) (c1 c2:Configuration.t), Prop :=
  | reservation_only_step_intro
      tid c1 lang st1 lc1 e2 st4 lc4 sc4 memory4
      (TID: IdentMap.find tid (Configuration.threads c1) = Some (existT _ lang st1, lc1))
      (CANCELS: rtc (@Thread.cancel_step _) (Thread.mk _ st1 lc1 (Configuration.sc c1) (Configuration.memory c1)) e2)
      (RESERVES: rtc (@Thread.reserve_step _) e2 (Thread.mk _ st4 lc4 sc4 memory4))
      (CONSISTENT: Thread.consistent (Thread.mk _ st4 lc4 sc4 memory4)):
      reservation_only_step tid c1 (Configuration.mk (IdentMap.add tid (existT _ _ st4, lc4) (Configuration.threads c1)) sc4 memory4)
  .
  #[global] Hint Constructors reservation_only_step: core.

  Lemma reservation_only_step_step tid c1 c2
        (STEP: reservation_only_step tid c1 c2)
    :
      step ThreadEvent.silent tid c1 c2.
  Proof.
    inv STEP. econs; eauto. econs 1.
  Qed.

  Lemma reservation_only_step_trans tid c1 c2 c3
        (STEP1: reservation_only_step tid c1 c2)
        (STEP2: reservation_only_step tid c2 c3)
    :
      reservation_only_step tid c1 c3.
  Proof.
    inv STEP1. inv STEP2. ss.
    erewrite IdentMap.gss in TID0. dep_clarify. dep_clarify.
    assert (STEPS: rtc
                     (@Thread.reserve_step _ \2/ @Thread.cancel_step _)
                     (Thread.mk _ st1 lc1 (Configuration.sc c1) (Configuration.memory c1))
                     (Thread.mk _ st2 lc2 sc0 memory0)).
    { etrans.
      { eapply rtc_implies; try apply CANCELS; eauto. }
      etrans.
      { eapply rtc_implies; try apply RESERVES; eauto. }
      etrans.
      { eapply rtc_implies; try apply CANCELS0; eauto. }
      { eapply rtc_implies; try apply RESERVES0; eauto. }
    }
    eapply rtc_implies with (R2:=tau (@pred_step (ThreadEvent.is_reserve \1/ ThreadEvent.is_cancel) _)) in STEPS; cycle 1.
    { clear. i. des.
      { inv H. econs; eauto.
        { econs; eauto.
          { econs; eauto. }
          { ss; auto. }
        }
        { ss. }
      }
      { inv H. econs; eauto.
        { econs; eauto.
          { econs; eauto. }
          { ss; auto. }
        }
        { ss. }
      }
    }
    hexploit steps_not_reserves_reserves; try apply STEPS. i. des.
    erewrite IdentMap.add_add_eq. econs.
    { eauto. }
    { eapply rtc_implies; try apply STEPS1.
      clear. i. inv H. inv TSTEP. des; ss. inv STEP.
      unfold ThreadEvent.is_cancel in *. des_ifs. econs; eauto. }
    { eapply STEPS2. }
    { auto. }
  Qed.

  Lemma reservation_event_reservation_only_step e tid c1 c2
        (STEP: step e tid c1 c2)
        (RESERVATION: ~ ThreadEvent.is_normal e)
    :
      reservation_only_step tid c1 c2.
  Proof.
    apply NNPP in RESERVATION. inv STEP. inv STEP0; ss.
    eapply Thread.reservation_event_reserve_or_cancel_step in STEP; auto. des.
    { econs.
      { eauto. }
      { eauto. }
      { econs 2; eauto. }
      { eapply CONSISTENT. destruct e; ss. }
    }
    { econs.
      { eauto. }
      { etrans; [eauto|]. econs 2; [|refl]. eauto. }
      { eauto. }
      { eapply CONSISTENT. destruct e; ss. }
    }
  Qed.

  Inductive machine_step: forall (e:MachineEvent.t) (tid:Ident.t) (c1 c2:Configuration.t), Prop :=
  | machine_step_intro
      e tid c1 c2
      (STEP: step e tid c1 c2)
    :
      machine_step (ThreadEvent.get_machine_event e) tid c1 c2
  .
  #[global] Hint Constructors machine_step: core.

  Inductive mixed_step:
    forall (e:ThreadEvent.t) (tid:Ident.t) (c1 c2:Configuration.t), Prop :=
  | mixed_step_intro
      e tid c1 lang st1 lc1 e2 e3 st4 lc4 sc4 memory4
      (TID: IdentMap.find tid (Configuration.threads c1) = Some (existT _ lang st1, lc1))
      (CANCELS: rtc (@Thread.reserve_step _ \2/ @Thread.cancel_step _) (Thread.mk _ st1 lc1 (Configuration.sc c1) (Configuration.memory c1)) e2)
      (STEP: Thread.opt_step e e2 e3)
      (RESERVES: rtc (@Thread.reserve_step _ \2/ @Thread.cancel_step _) e3 (Thread.mk _ st4 lc4 sc4 memory4))
      (CONSISTENT: ThreadEvent.get_machine_event e <> MachineEvent.failure ->
                   Thread.consistent (Thread.mk _ st4 lc4 sc4 memory4)):
      mixed_step e tid c1 (Configuration.mk (IdentMap.add tid (existT _ _ st4, lc4) (Configuration.threads c1)) sc4 memory4)
  .
  #[global] Hint Constructors mixed_step: core.

  Inductive opt_machine_step:
    forall (e: MachineEvent.t) (tid: Ident.t) (c1 c2: Configuration.t), Prop :=
  | opt_machine_step_none
      tid c:
      opt_machine_step MachineEvent.silent tid c c
  | opt_machine_step_some
      e tid c1 c2
      (STEP: machine_step e tid c1 c2):
      opt_machine_step e tid c1 c2
  .
  #[global] Hint Constructors opt_machine_step: core.

  Definition tau_machine_step := union (machine_step MachineEvent.silent).

  Inductive all_machine_step: forall (c1 c2:Configuration.t), Prop :=
  | all_machine_step_intro
      e tid c1 c2
      (STEP: machine_step e tid c1 c2)
    :
      all_machine_step c1 c2
  .
  #[global] Hint Constructors all_machine_step: core.

  Lemma step_future
        e tid c1 c2
        (STEP: step e tid c1 c2)
        (WF1: Configuration.wf c1):
    (<<WF2: Configuration.wf c2>>) /\
    (<<SC_FUTURE: TimeMap.le (Configuration.sc c1) (Configuration.sc c2)>>) /\
    (<<MEM_FUTURE: Memory.future (Configuration.memory c1) (Configuration.memory c2)>>).
  Proof.
    inv WF1. inv WF. inv STEP; s. exploit THREADS; ss; eauto. i.
    assert (STEPS: rtc
                     (@Thread.all_step _)
                     (Thread.mk _ st1 lc1 (Configuration.sc c1) (Configuration.memory c1))
                     (Thread.mk _ st4 lc4 sc4 memory4)).
    { etrans.
      { eapply rtc_implies; try apply CANCELS. i. inv H.
        econs; eauto. econs; eauto. }
      inv STEP0.
      { eapply rtc_implies; try apply RESERVES. i. inv H.
        econs; eauto. econs; eauto. }
      { etrans.
        { econs 2; [|refl]. econs; eauto. econs; eauto. }
        { eapply rtc_implies; try apply RESERVES. i. inv H.
          econs; eauto. econs; eauto. }
      }
    }
    exploit Thread.rtc_all_step_future; eauto. s. i. des.
    splits; eauto. econs; ss. econs.
    + i. Configuration.simplify.
      * exploit THREADS; try apply TH1; eauto. i. des.
        exploit Thread.rtc_all_step_disjoint; eauto. i. des.
        symmetry. auto.
      * exploit THREADS; try apply TH2; eauto. i. des.
        exploit Thread.rtc_all_step_disjoint; eauto. i. des.
        auto.
      * eapply DISJOINT; [|eauto|eauto]. auto.
    + i. Configuration.simplify.
      exploit THREADS; try apply TH; eauto. i.
      exploit Thread.rtc_all_step_disjoint; eauto. i. des.
      auto.
  Qed.

  Lemma machine_step_future
        e tid c1 c2
        (STEP: machine_step e tid c1 c2)
        (WF1: Configuration.wf c1):
    (<<WF2: Configuration.wf c2>>) /\
    (<<SC_FUTURE: TimeMap.le (Configuration.sc c1) (Configuration.sc c2)>>) /\
    (<<MEM_FUTURE: Memory.future (Configuration.memory c1) (Configuration.memory c2)>>).
  Proof.
    inv STEP. eapply step_future; eauto.
  Qed.

  Lemma opt_machine_step_future
        e tid c1 c2
        (STEP: opt_machine_step e tid c1 c2)
        (WF1: Configuration.wf c1):
    (<<WF2: Configuration.wf c2>>) /\
    (<<SC_FUTURE: TimeMap.le (Configuration.sc c1) (Configuration.sc c2)>>) /\
    (<<MEM_FUTURE: Memory.future (Configuration.memory c1) (Configuration.memory c2)>>).
  Proof.
    inv STEP.
    - splits; auto; refl.
    - inv STEP0. eapply step_future; eauto.
  Qed.

  Lemma rtc_step_future
        c1 c2
        (STEPS: rtc tau_machine_step c1 c2)
        (WF1: Configuration.wf c1):
    (<<WF2: Configuration.wf c2>>) /\
    (<<SC_FUTURE: TimeMap.le (Configuration.sc c1) (Configuration.sc c2)>>) /\
    (<<MEM_FUTURE: Memory.future (Configuration.memory c1) (Configuration.memory c2)>>).
  Proof.
    induction STEPS; i.
    - splits; auto; refl.
    - inv H. inv USTEP.
      exploit step_future; eauto. i. des.
      exploit IHSTEPS; eauto. i. des.
      splits; eauto; etrans; eauto.
  Qed.

  Lemma all_machine_step_future
        c1 c2
        (STEP: all_machine_step c1 c2)
        (WF1: Configuration.wf c1):
    (<<WF2: Configuration.wf c2>>) /\
    (<<SC_FUTURE: TimeMap.le (Configuration.sc c1) (Configuration.sc c2)>>) /\
    (<<MEM_FUTURE: Memory.future (Configuration.memory c1) (Configuration.memory c2)>>).
  Proof.
    inv STEP. eapply machine_step_future; eauto.
  Qed.

  Lemma all_machine_steps_future
        c1 c2
        (STEP: rtc all_machine_step c1 c2)
        (WF1: Configuration.wf c1):
    (<<WF2: Configuration.wf c2>>) /\
    (<<SC_FUTURE: TimeMap.le (Configuration.sc c1) (Configuration.sc c2)>>) /\
    (<<MEM_FUTURE: Memory.future (Configuration.memory c1) (Configuration.memory c2)>>).
  Proof.
    ginduction STEP; i.
    - splits; auto. refl.
    -  exploit all_machine_step_future; eauto. i. des.
       exploit IHSTEP; eauto. i. des. esplits; eauto. etrans; eauto.
  Qed.

  Lemma silent_steps_tau_machine_steps es tid c1 c2
        (STEPS: steps es tid c1 c2)
        (SILENT: List.Forall (fun e => ThreadEvent.get_machine_event e = MachineEvent.silent) es)
    :
      rtc tau_machine_step c1 c2.
  Proof.
    ginduction es; i.
    { inv STEPS. eauto. }
    { inv STEPS. inv SILENT. exploit IHes; eauto.
      i. econs 2; eauto. econs; eauto.
      rewrite <- H1. econs; eauto. }
  Qed.

  Lemma step_mixed_step e tid c1 c2
        (STEP: step e tid c1 c2)
    :
      mixed_step e tid c1 c2.
  Proof.
    inv STEP. econs.
    { eauto. }
    { eapply rtc_implies; try apply CANCELS; eauto. }
    { eauto. }
    { eapply rtc_implies; try apply RESERVES; eauto. }
    { eauto. }
  Qed.

  Lemma mixed_step_step e tid c1 c2
        (STEP: mixed_step e tid c1 c2)
    :
      (<<STEP: step e tid c1 c2>>) \/
      ((<<STEP: reservation_only_step tid c1 c2>>) /\
       (<<RESERVATION: ~ ThreadEvent.is_normal e>>)).
  Proof.
    inv STEP.
    exploit reorder_reserves_opt_step_cancels.
    { eapply CANCELS. }
    { eauto. }
    { eapply RESERVES. }
    i. des.
    { left. econs.
      { eauto. }
      { eapply STEPS1. }
      { eapply STEP2. }
      { eapply STEPS3. }
      { eauto. }
    }
    { right. splits; auto. econs.
      { eauto. }
      { eapply STEPS1. }
      { eapply STEPS3. }
      { eapply CONSISTENT; eauto. ii.
        eapply RESERVATION. ii. destruct e; ss.
      }
    }
  Qed.

  Lemma merge_reservation_only_step_step e tid c1 c2 c3
        (STEP0: reservation_only_step tid c1 c2)
        (STEP1: step e tid c2 c3)
    :
      (<<STEP: step e tid c1 c3>>) \/
      ((<<STEP: reservation_only_step tid c1 c3>>) /\
       (<<RESERVATION: ~ ThreadEvent.is_normal e>>)).
  Proof.
    inv STEP0. inv STEP1. ss.
    erewrite IdentMap.gss in TID0. dep_clarify. dep_clarify.
    erewrite IdentMap.add_add_eq.
    exploit mixed_step_step.
    { econs.
      { eapply TID. }
      { etrans.
        { eapply rtc_implies; try apply CANCELS. eauto. }
        etrans.
        { eapply rtc_implies; try apply RESERVES. eauto. }
        { eapply rtc_implies; try apply CANCELS0. eauto. }
      }
      { eauto. }
      { eapply rtc_implies; try apply RESERVES0. eauto. }
      { eauto. }
    }
    i. des; eauto.
  Qed.

  Lemma merge_step_reservation_only_step e tid c1 c2 c3
        (STEP0: step e tid c1 c2)
        (STEP1: reservation_only_step tid c2 c3)
    :
      (<<STEP: step e tid c1 c3>>) \/
      ((<<STEP: reservation_only_step tid c1 c3>>) /\
       (<<RESERVATION: ~ ThreadEvent.is_normal e>>)).
  Proof.
    inv STEP0. inv STEP1. ss.
    erewrite IdentMap.gss in TID0. dep_clarify. dep_clarify.
    erewrite IdentMap.add_add_eq.
    exploit mixed_step_step.
    { econs.
      { eapply TID. }
      { eapply rtc_implies; try apply CANCELS. eauto. }
      { eauto. }
      { etrans.
        { eapply rtc_implies; try apply RESERVES. eauto. }
        etrans.
        { eapply rtc_implies; try apply CANCELS0. eauto. }
        { eapply rtc_implies; try apply RESERVES0. eauto. }
      }
      { eauto. }
    }
    i. des; eauto.
  Qed.

  Lemma steps_filtering es tid c1 c2
        (STEPS: steps es tid c1 c2)
    :
      (<<STEPS: steps (List.filter ThreadEvent.is_normal_dec es) tid c1 c2>>) \/
      ((<<STEP: reservation_only_step tid c1 c2>>) /\
       (<<RESERVATION: List.filter ThreadEvent.is_normal_dec es = []>>)).
  Proof.
    ginduction es; eauto. i. inv STEPS. ss. unfold proj_sumbool in *. des_ifs.
    { exploit IHes; eauto. i. des.
      { left. econs; eauto. }
      { rewrite RESERVATION in *. left. econs 2; [|econs 1].
        exploit merge_step_reservation_only_step; eauto. i. des; ss. }
    }
    { eapply reservation_event_reservation_only_step in STEP; auto.
      exploit IHes; eauto. i. des.
      { inv STEPS.
        { right. splits; eauto. }
        { left. exploit merge_reservation_only_step_step; eauto. i. des.
          { econs; eauto. }
          { exfalso.
            hexploit
              (proj1 (List.filter_In
                        (fun e => if ThreadEvent.is_normal_dec e then true else false) ehd es)).
            { rewrite <- H0. ss. auto. }
            i. des. des_ifs.
          }
        }
      }
      { rewrite RESERVATION in *. right. splits; auto.
        eapply reservation_only_step_trans; eauto. }
    }
  Qed.

  Lemma merge_reservation_only_step_steps es tid c1 c2 c3
        (STEP0: reservation_only_step tid c1 c2)
        (STEP1: steps es tid c2 c3)
    :
      (<<STEPS: steps (List.filter ThreadEvent.is_normal_dec es) tid c1 c3>>) \/
      ((<<STEP: reservation_only_step tid c1 c3>>) /\
       (<<RESERVATION: List.filter ThreadEvent.is_normal_dec es = []>>)).
  Proof.
    hexploit steps_filtering; try apply STEP1. i. des.
    { inv STEPS.
      { right. splits; auto. }
      { left. exploit merge_reservation_only_step_step; eauto. i. des.
        { econs; eauto. }
        { exfalso.
          hexploit
            (proj1 (List.filter_In
                      (fun e => ThreadEvent.is_normal_dec e) ehd es)).
          { rewrite <- H0. ss. auto. }
          i. des. unfold proj_sumbool in *. des_ifs.
        }
      }
    }
    { right. rewrite RESERVATION. splits; auto.
      eapply reservation_only_step_trans; eauto. }
  Qed.

  Lemma merge_steps_reservation_only_step es tid c1 c2 c3
        (STEP0: steps es tid c1 c2)
        (STEP1: reservation_only_step tid c2 c3)
    :
      (<<STEPS: steps (List.filter ThreadEvent.is_normal_dec es) tid c1 c3>>) \/
      ((<<STEP: reservation_only_step tid c1 c3>>) /\
       (<<RESERVATION: List.filter ThreadEvent.is_normal_dec es = []>>)).
  Proof.
    hexploit steps_filtering; try apply STEP0. i. des.
    { destruct (list_match_rev (List.filter (fun e => ThreadEvent.is_normal_dec e) es)).
      { rewrite H in *. inv STEPS. splits; auto. }
      des. rewrite H in *. eapply steps_split in STEPS. des.
      inv STEPS1. inv STEPS.
      left. exploit merge_step_reservation_only_step; eauto. i. des.
      { eapply steps_trans; eauto. }
      { exfalso.
        hexploit
          (proj1 (List.filter_In
                    (fun e => ThreadEvent.is_normal_dec e) hd_rev es)).
        { rewrite H. eapply List.in_or_app. ss. auto. }
        i. des. unfold proj_sumbool in *. des_ifs.
      }
    }
    { right. rewrite RESERVATION. splits; auto.
      eapply reservation_only_step_trans; eauto. }
  Qed.

  Lemma trace_step_machine_step tr e tid c1 c3
        (STEP: Trace.configuration_step tr e tid c1 c3)
        (WF: Configuration.wf c1)
    :
      ((<<STEPS: steps (List.filter ThreadEvent.is_normal_dec (List.map snd tr)) tid c1 c3>>) /\
       (<<NIL: List.filter ThreadEvent.is_normal_dec (List.map snd tr) <> []>>)) \/
      ((<<STEP: reservation_only_step tid c1 c3>>) /\
       (<<NIL: List.filter ThreadEvent.is_normal_dec (List.map snd tr) = []>>)).
  Proof.
    inv STEP.
    exploit Trace.steps_future; eauto.
    { eapply WF; eauto. }
    { eapply WF; eauto. }
    { eapply WF; eauto. } i. des. ss.
    clear TVIEW_FUTURE SC_FUTURE MEM_FUTURE.
    eapply Trace.steps_equivalent in STEPS.
    assert (exists e2',
               (<<STEP: Thread.step pf e0 e2 e2'>>) /\
               (<<STEPS: rtc (@Thread.reserve_step _ \2/ @Thread.cancel_step _) e2' (Thread.mk _ st3 lc3 sc3 memory3)>>)).
    { eauto. }
    clear STEP0. des.
    remember (Thread.mk _ st1 lc1 (Configuration.sc c1) (Configuration.memory c1)).
    ginduction STEPS.
    { i. subst. exploit mixed_step_step.
      { econs.
        { eauto. }
        { refl. }
        { econs 2. eapply STEP. }
        { eapply STEPS0. }
        { eauto. }
      }
      i. des.
      { ss. des_ifs.
        { left. splits; ss. econs; [|econs 1]. eauto. }
        { right. unfold proj_sumbool in *. des_ifs. splits; auto.
          eapply reservation_event_reservation_only_step; eauto.
        }
      }
      { right. ss. splits; auto. unfold proj_sumbool. des_ifs. }
    }
    i. subst. eapply rtc_implies with (R2 := @Thread.reserve_step lang \2/ @Thread.cancel_step _) in STEPS0; eauto.
    exploit consistent_split; try eassumption.
    { destruct (classic (ThreadEvent.get_machine_event e0 = MachineEvent.failure)); auto. }
    i. des. destruct th0'.
    exploit Trace.steps_future.
    { eapply Trace.steps_equivalent. eapply STEPS. }
    { eapply WF; eauto. }
    { eapply WF; eauto. }
    { eapply WF; eauto. } i. des. ss.
    eapply list_Forall_app in SILENT. des. inv FORALL1; ss. inv H2.
    exploit IHSTEPS; try apply STEP0; try apply RESERVESTEPS; eauto.

    exploit SConfiguration.mixed_step_step.
    { instantiate (1:=Configuration.mk
                        (IdentMap.add
                           tid
                           (existT _ _ st3, lc3)
                           (IdentMap.add
                              tid
                              (existT _ _ state, local)
                              (Configuration.threads c1)))
                        sc3
                        memory3).
      instantiate (1:=Configuration.mk
                        (IdentMap.add
                           tid
                           (existT _ _ state, local)
                           (Configuration.threads c1))
                        sc
                        memory).
      instantiate (1:=tid).
      instantiate (1:=e0).
      econs; ss; eauto.
      { erewrite IdentMap.gss. ss. }
      { econs 2; eauto. }
    }
    i. erewrite IdentMap.add_add_eq in *.
    erewrite List.map_app. ss.
    erewrite list_filter_app; eauto. ss. des_ifs.
    { unfold proj_sumbool in Heq. des_ifs. des; ss.
      { left. splits; ss.
        { eapply steps_trans.
          { eapply STEPS1. }
          { econs 2; eauto. }
        }
        { ii. apply List.app_eq_nil in H. des. ss. }
      }
      { rewrite NIL in *. ss.
        exploit merge_reservation_only_step_step; eauto. i. des; ss.
        left. splits; ss. econs; eauto.
      }
    }
    { erewrite List.app_nil_r in *.
      unfold proj_sumbool in Heq. des_ifs. des; ss.
      { eapply reservation_event_reservation_only_step in STEP0; eauto.
        exploit merge_steps_reservation_only_step; eauto. i.
        erewrite list_filter_idempotent in *. des; ss; eauto. }
      { exploit merge_steps_reservation_only_step; eauto. i.
        erewrite list_filter_idempotent in *. des; ss; eauto. }
      { eapply reservation_event_reservation_only_step in STEP1; eauto.
        right. splits; auto. eapply reservation_only_step_trans; eauto. }
      { right. splits; auto. eapply reservation_only_step_trans; eauto. }
    }
  Qed.

  Lemma multi_step_machine_step e tid c1 c3
        (STEP: Configuration.step e tid c1 c3)
        (WF: Configuration.wf c1)
    :
      exists c2,
        (<<STEPS: rtc tau_machine_step c1 c2>>) /\
        (<<STEP: opt_machine_step e tid c2 c3>>).
  Proof.
    eapply Trace.configuration_step_step in STEP. des.
    exploit trace_step_machine_step; eauto. i. des.
    { inv STEP0.
      rewrite List.map_app in *.
      rewrite list_filter_app in *. ss.
      eapply steps_split in STEPS. des. exists c0. splits.
      { eapply silent_steps_tau_machine_steps; eauto.
        eapply list_filter_forall with (Q:=fun e => ThreadEvent.get_machine_event e = MachineEvent.silent); eauto.
        eapply list_map_forall; eauto.
      }
      unfold proj_sumbool in *. des_ifs.
      { inv STEPS2. inv STEPS.
        econs 2. econs; eauto. }
      { inv STEPS2.
        replace (ThreadEvent.get_machine_event e0) with MachineEvent.silent; eauto.
        apply NNPP in n.
        unfold ThreadEvent.is_reservation_event, ThreadEvent.is_reserve, ThreadEvent.is_cancel in n.
        des; des_ifs.
      }
    }
    { eapply reservation_only_step_step in STEP.
      exists c1. esplits; eauto.
      replace e with (ThreadEvent.get_machine_event ThreadEvent.silent); eauto.
      ss. inv STEP0.
      rewrite List.map_app in NIL.
      rewrite list_filter_app in NIL.
      eapply List.app_eq_nil in NIL.
      ss. unfold proj_sumbool in NIL. des. des_ifs.
      apply NNPP in n.
      unfold ThreadEvent.is_reservation_event, ThreadEvent.is_reserve, ThreadEvent.is_cancel in n.
      des; des_ifs.
    }
  Qed.

  Lemma machine_step_multi_step e tid c1 c3
        (STEP: machine_step e tid c1 c3)
    :
      exists c2,
        (<<STEP: Configuration.opt_step e tid c1 c2>>) /\
        (<<STEPS: Configuration.opt_step MachineEvent.silent tid c2 c3>>).
  Proof.
    inv STEP. inv STEP0.
    eapply rtc_implies with (R2:=@Thread.tau_step _) in CANCELS; cycle 1.
    { clear. i. inv H. econs.
      { econs; eauto. }
      { ss. }
    }
    hexploit rtc_implies; [|apply RESERVES|].
    { instantiate (1:=@Thread.tau_step _).
      clear. i. inv H. econs.
      { econs; eauto. }
      { ss. }
    }
    intros AFTERSTEPS.
    destruct (ThreadEvent.get_machine_event e0) eqn:EVENT.
    { esplits; [|econs 1].
      assert (STEPS: rtc (@Thread.tau_step _)
                         (Thread.mk _ st1 lc1 (Configuration.sc c1) (Configuration.memory c1))
                         (Thread.mk _ st4 lc4 sc4 memory4)).
      { etrans.
        { eapply CANCELS. }
        inv STEP; eauto. econs 2.
        { econs; eauto. econs; eauto. }
        { eauto. }
      }
      eapply rtc_tail in STEPS. des.
      { inv STEPS0. inv TSTEP. econs 2.
        rewrite <- EVENT0. econs; eauto.
        { destruct e; ss. }
      }
      { clarify. destruct c1; ss.
        rewrite IdentMap.gsident; eauto. }
    }
    { inv STEP; ss.
      assert (BOT: (Local.promises (Thread.local e3)) = Memory.bot).
      { destruct e0; ss. inv STEP0; inv STEP. inv LOCAL. inv LOCAL0; auto. }
      destruct e3. esplits.
      { econs 2. rewrite <- EVENT. econs; eauto.
        ii. right. ss. esplits; [refl|]. ss. }
      { eapply rtc_tail in AFTERSTEPS. des; clarify.
        inv AFTERSTEPS0. inv TSTEP.
        econs 2. rewrite <- EVENT0.
        replace (IdentMap.add tid (existT _ _ st4, lc4) (Configuration.threads c1)) with (IdentMap.add tid (existT _ _ st4, lc4) (IdentMap.add tid (existT _ _ state, local) (Configuration.threads c1)))
        .
        { econs; ss.
          { eapply IdentMap.gss. }
          { eapply AFTERSTEPS. }
          { eapply STEP. }
          { ii. right.
            exploit reserve_steps_le_cancel_steps.
            { eapply RESERVES. }
            { ss. eapply CAP. }
            i. des. ss. esplits.
            { eapply rtc_implies; try apply STEPS.
              clear. i. inv H. econs.
              { econs; eauto. }
              { ss. }
            }
            { rewrite LOCAL. auto. }
          }
        }
        { eapply IdentMap.add_add_eq. }
      }
    }
    { assert (Thread.step true e0 e2 e3).
      { inv STEP; ss. inv STEP0; inv STEP; ss.
        econs 2. inv LOCAL; econs; eauto.
      }
      hexploit reorder_failure_reserves; eauto. i. des.
      esplits; [|econs 1]. econs 2. rewrite <- EVENT. econs.
      { eauto. }
      { etrans.
        { eapply CANCELS. }
        { eapply rtc_implies; try apply STEPS.
          clear. i. inv H. econs.
          { econs; eauto. }
          { ss. }
        }
      }
      { eauto. }
      { rewrite EVENT. ss. }
    }
  Qed.

  Lemma multi_step_equiv c b f
        (WF: Configuration.wf c)
    :
      behaviors Configuration.step c b f <-> behaviors machine_step c b f.
  Proof.
    split; i.
    { ginduction H; i.
      { econs 1; eauto. }
      { exploit IHbehaviors.
        { eapply Configuration.step_future; eauto. } intros BEH.
        eapply multi_step_machine_step in STEP; eauto. des.
        eapply rtc_tau_step_behavior.
        { eapply STEPS. }
        { inv STEP0. econs 2; eauto. }
      }
      { eapply multi_step_machine_step in STEP; eauto. des.
        eapply rtc_tau_step_behavior.
        { eapply STEPS. }
        { inv STEP0. econs 3; eauto. }
      }
      { exploit IHbehaviors.
        { eapply Configuration.step_future; eauto. } intros BEH.
        eapply multi_step_machine_step in STEP; eauto. des.
        eapply rtc_tau_step_behavior.
        { eapply STEPS. }
        { inv STEP0; eauto.
          econs 4; eauto.
        }
      }
      { econs 5. }
    }
    { clear WF. ginduction H; i.
      { econs 1; eauto. }
      { eapply machine_step_multi_step in STEP; eauto. des.
        inv STEP0. econs 2; eauto.
        inv STEPS; eauto. econs 4; eauto.
      }
      { eapply machine_step_multi_step in STEP; eauto. des.
        inv STEP0. econs 3; eauto.
      }
      { eapply machine_step_multi_step in STEP; eauto. des.
        inv STEP0.
        { inv STEPS; eauto. econs 4; eauto. }
        { econs 4; eauto. inv STEPS; eauto. econs 4; eauto. }
      }
      { econs 5. }
    }
  Qed.

End SConfiguration.
