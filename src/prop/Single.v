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
      (TID: IdentMap.find tid c1.(Configuration.threads) = Some (existT _ lang st1, lc1))
      (CANCELS: rtc (@Thread.cancel_step _) (Thread.mk _ st1 lc1 c1.(Configuration.sc) c1.(Configuration.memory)) e2)
      (STEP: Thread.opt_step e e2 e3)
      (RESERVES: rtc (@Thread.reserve_step _) e3 (Thread.mk _ st4 lc4 sc4 memory4))
      (CONSISTENT: e <> ThreadEvent.failure -> Thread.consistent (Thread.mk _ st4 lc4 sc4 memory4)):
      step e tid c1 (Configuration.mk (IdentMap.add tid (existT _ _ st4, lc4) c1.(Configuration.threads)) sc4 memory4)
  .
  Hint Constructors step.

  Inductive machine_step: forall (e:MachineEvent.t) (tid:Ident.t) (c1 c2:Configuration.t), Prop :=
  | machine_step_intro
      e tid c1 c2
      (STEP: step e tid c1 c2)
    :
      machine_step (ThreadEvent.get_machine_event e) tid c1 c2
  .
  Hint Constructors machine_step.

  Inductive mixed_step:
    forall (e:ThreadEvent.t) (tid:Ident.t) (c1 c2:Configuration.t), Prop :=
  | mixed_step_intro
      e tid c1 lang st1 lc1 e2 e3 st4 lc4 sc4 memory4
      (TID: IdentMap.find tid c1.(Configuration.threads) = Some (existT _ lang st1, lc1))
      (CANCELS: rtc (@Thread.reserve_step _ \2/ @Thread.cancel_step _) (Thread.mk _ st1 lc1 c1.(Configuration.sc) c1.(Configuration.memory)) e2)
      (STEP: Thread.opt_step e e2 e3)
      (RESERVES: rtc (@Thread.reserve_step _ \2/ @Thread.cancel_step _) e3 (Thread.mk _ st4 lc4 sc4 memory4))
      (CONSISTENT: e <> ThreadEvent.failure -> Thread.consistent (Thread.mk _ st4 lc4 sc4 memory4)):
      mixed_step e tid c1 (Configuration.mk (IdentMap.add tid (existT _ _ st4, lc4) c1.(Configuration.threads)) sc4 memory4)
  .
  Hint Constructors mixed_step.

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
  Hint Constructors opt_machine_step.

  Definition tau_machine_step := union (machine_step MachineEvent.silent).

  Lemma step_future
        e tid c1 c2
        (STEP: step e tid c1 c2)
        (WF1: Configuration.wf c1):
    (<<WF2: Configuration.wf c2>>) /\
    (<<SC_FUTURE: TimeMap.le c1.(Configuration.sc) c2.(Configuration.sc)>>) /\
    (<<MEM_FUTURE: Memory.future c1.(Configuration.memory) c2.(Configuration.memory)>>).
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
    (<<SC_FUTURE: TimeMap.le c1.(Configuration.sc) c2.(Configuration.sc)>>) /\
    (<<MEM_FUTURE: Memory.future c1.(Configuration.memory) c2.(Configuration.memory)>>).
  Proof.
    inv STEP. eapply step_future; eauto.
  Qed.

  Lemma opt_machine_step_future
        e tid c1 c2
        (STEP: opt_machine_step e tid c1 c2)
        (WF1: Configuration.wf c1):
    (<<WF2: Configuration.wf c2>>) /\
    (<<SC_FUTURE: TimeMap.le c1.(Configuration.sc) c2.(Configuration.sc)>>) /\
    (<<MEM_FUTURE: Memory.future c1.(Configuration.memory) c2.(Configuration.memory)>>).
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
    (<<SC_FUTURE: TimeMap.le c1.(Configuration.sc) c2.(Configuration.sc)>>) /\
    (<<MEM_FUTURE: Memory.future c1.(Configuration.memory) c2.(Configuration.memory)>>).
  Proof.
    induction STEPS; i.
    - splits; auto; refl.
    - inv H. inv USTEP.
      exploit step_future; eauto. i. des.
      exploit IHSTEPS; eauto. i. des.
      splits; eauto; etrans; eauto.
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
      exists e',
        (<<STEP: step e' tid c1 c2>>) /\
        __guard__(e' = e \/ e' = ThreadEvent.silent /\ (<<RESERVE: is_reserve e>> \/ <<CANCEL: is_cancel e>>)).
  Proof.
    inv STEP. exploit reorder_reserves_opt_step_cancels.
    { eapply CANCELS. }
    { eauto. }
    { eapply RESERVES. }
    i. des. esplits.
    { econs.
      { eauto. }
      { eapply STEPS1. }
      { eapply STEP2. }
      { eapply STEPS3. }
      { ii. eapply CONSISTENT; eauto. ii.
        subst. unguard. des; ss. }
    }
    { eauto. }
  Qed.

  Lemma multi_step_machine_step e tid c1 c3
        (STEP: Configuration.step e tid c1 c3)
        (WF: Configuration.wf c1)
    :
      exists c2,
        (<<STEPS: rtc tau_machine_step c1 c2>>) /\
        (<<STEP: machine_step e tid c2 c3>>).
  Proof.
    apply configuration_step_equivalent in STEP. inv STEP.
    exploit Thread.rtc_tau_step_future; eauto.
    { eapply WF; eauto. }
    { eapply WF; eauto. }
    { eapply WF; eauto. } i. des. ss.
    clear TVIEW_FUTURE SC_FUTURE MEM_FUTURE.
    eapply Operators_Properties.clos_rt_rt1n_iff in STEPS.
    eapply Operators_Properties.clos_rt_rtn1_iff in STEPS.
    assert (exists e2',
               (<<STEP: Thread.step pf e0 e2 e2'>>) /\
               (<<STEPS: rtc (@Thread.reserve_step _ \2/ @Thread.cancel_step _) e2' (Thread.mk _ st3 lc3 sc3 memory3)>>)).
    { eauto. }
    clear STEP0. des.
    ginduction STEPS.
    { i. exploit mixed_step_step.
      { econs.
        { eauto. }
        { refl. }
        { econs 2. eapply STEP. }
        { eapply STEPS0. }
        { eauto. }
      }
      i. des. esplits.
      { refl. }
      { replace (ThreadEvent.get_machine_event e0) with (ThreadEvent.get_machine_event e'); eauto.
        unguard. destruct e0; des; subst; ss. }
    }
    i. eapply rtc_implies with (R2 := @Thread.reserve_step lang \2/ @Thread.cancel_step _) in STEPS0; eauto.
    exploit consistent_split; try eassumption.
    { destruct (classic (e0 = ThreadEvent.failure)); auto. }
    i. des. inv H. inv TSTEP. destruct th0'.
    exploit Thread.rtc_tau_step_future.
    { eapply Operators_Properties.clos_rt_rt1n_iff.
      eapply Operators_Properties.clos_rt_rtn1_iff. eapply STEPS. }
    { eapply WF; eauto. }
    { eapply WF; eauto. }
    { eapply WF; eauto. } i. des. ss.
    exploit IHSTEPS; try apply STEP0; try apply RESERVESTEPS; eauto.
    i. des. rewrite EVENT in *.
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
    i. des. erewrite IdentMap.add_add_eq in *. esplits.
    { etrans.
      { eapply STEPS1. }
      { econs; [|refl]. econs; eauto. }
    }
    { replace (ThreadEvent.get_machine_event e0) with (ThreadEvent.get_machine_event e'); eauto.
      unguard. destruct e0; des; subst; ss. }
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
                         (Thread.mk _ st1 lc1 c1.(Configuration.sc) c1.(Configuration.memory))
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
        { eapply CONSISTENT. ii. subst. ss. }
      }
      { clarify. destruct c1; ss.
        rewrite IdentMap.gsident; eauto. }
    }
    { inv STEP; ss.
      assert (BOT: e3.(Thread.local).(Local.promises) = Memory.bot).
      { destruct e0; ss. inv STEP0; inv STEP. inv LOCAL. inv LOCAL0; auto. }
      destruct e3. esplits.
      { econs 2. rewrite <- EVENT. econs; eauto.
        { destruct e0; ss. }
        { ii. right. ss. esplits; [refl|]. ss. }
      }
      { eapply rtc_tail in AFTERSTEPS. des; clarify.
        inv AFTERSTEPS0. inv TSTEP.
        econs 2. rewrite <- EVENT0.
        replace (IdentMap.add tid (existT _ _ st4, lc4) (Configuration.threads c1)) with (IdentMap.add tid (existT _ _ st4, lc4) (IdentMap.add tid (existT _ _ state, local) (Configuration.threads c1))).
        { econs; ss.
          { eapply IdentMap.gss. }
          { eapply AFTERSTEPS. }
          { eapply STEP. }
          { destruct e1; ss. }
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
    { destruct e0; ss. inv STEP.
      exploit reorder_abort_reserves; eauto. i. des.
      esplits; [|econs 1]. econs 2. econs.
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
    }
  Qed.

  Lemma multi_step_equiv c b
        (WF: Configuration.wf c)
    :
      behaviors Configuration.step c b <-> behaviors machine_step c b.
  Proof.
    split; i.
    { ginduction H; i.
      { econs 1; eauto. }
      { exploit IHbehaviors.
        { eapply Configuration.step_future; eauto. } intros BEH.
        eapply multi_step_machine_step in STEP; eauto. des.
        eapply rtc_tau_step_behavior.
        { eapply STEPS. }
        { econs 2; eauto. }
      }
      { eapply multi_step_machine_step in STEP; eauto. des.
        eapply rtc_tau_step_behavior.
        { eapply STEPS. }
        { econs 3; eauto. }
      }
      { exploit IHbehaviors.
        { eapply Configuration.step_future; eauto. } intros BEH.
        eapply multi_step_machine_step in STEP; eauto. des.
        eapply rtc_tau_step_behavior.
        { eapply STEPS. }
        { econs 4; eauto. }
      }
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
    }
  Qed.

End SConfiguration.
