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

Require Import MemoryMerge.
Require Import ReorderCancel.
Require Import MemoryProps.
Require Import OrderedTimes.
Require Import Cover.
Require Import Mapping.
Require Import PFConsistent.
Require Import PFConsistentStrong.
Require Import FutureCertify.

Require Import PreReserve.

Set Implicit Arguments.




Lemma reserve_step_cancel_step_eq lang (th0 th1: Thread.t lang)
      (STEP: Thread.reserve_step th0 th1)
  :
    Thread.cancel_step th1 th0.
Proof.
  inv STEP. inv STEP0; inv STEP; inv LOCAL.
  assert (REMOVE: Memory.promise promises2 mem2 loc from to Message.reserve lc1.(Local.promises) mem1 Memory.op_kind_cancel).
  { inv PROMISE. econs; eauto.
    { exploit Memory.remove_exists.
      { eapply Memory.add_get0. eapply PROMISES. }
      i. des. exploit MemoryMerge.add_remove; try apply x0; eauto.
      i. subst. eauto.
    }
    { exploit Memory.remove_exists.
      { eapply Memory.add_get0. eapply MEM. }
      i. des. exploit MemoryMerge.add_remove; try apply x0; eauto.
      i. subst. eauto.
    }
  }
  destruct lc1. ss.
  econs. econs 1; eauto. econs; eauto.
Qed.

Lemma cancel_step_reserve_step_eq lang (th0 th1: Thread.t lang)
      (STEP: Thread.cancel_step th0 th1)
      (LOCAL: Local.wf th0.(Thread.local) th0.(Thread.memory))
  :
    Thread.reserve_step th1 th0.
Proof.
  inv STEP.
  hexploit step_promises_le.
  { eapply LOCAL. }
  { econs; eauto. }
  intros MLE. inv STEP0; inv STEP; inv LOCAL0. ss.
  assert (REMOVE: Memory.promise promises2 mem2 loc from to Message.reserve lc1.(Local.promises) mem1 Memory.op_kind_add).
  { inv PROMISE. dup MEM. eapply Memory.remove_get0 in MEM. des.
    exploit (@Memory.add_exists mem2 loc from to Message.reserve).
    { ii. erewrite Memory.remove_o in GET2; eauto. des_ifs.
      exploit Memory.get_disjoint.
      { eapply GET2. }
      { eapply GET. }
      i. des; ss; clarify. eapply x1; eauto.
    }
    { eapply Memory.remove_get0 in PROMISES. des.
      inv LOCAL; ss.
      eapply memory_get_ts_strong in GET. des; auto. subst.
      erewrite BOT in GET1. ss.
    }
    { econs. }
    i. des. exploit Memory.add_exists_le; eauto. i. des.
    replace mem0 with mem1 in *; cycle 1.
    { eapply Memory.ext. i.
      erewrite (@Memory.add_o mem0 mem2); eauto.
      erewrite (@Memory.remove_o mem2 mem1); eauto. des_ifs.
      ss. des; subst. eapply Memory.remove_get0; eauto. }
    replace promises0 with (Local.promises lc1) in *; cycle 1.
    { eapply Memory.ext. i.
      erewrite (@Memory.add_o promises0 promises2); eauto.
      erewrite (@Memory.remove_o promises2 lc1.(Local.promises)); eauto. des_ifs.
      ss. des; subst. eapply Memory.remove_get0; eauto. }
    econs; eauto. ss.
  }
  destruct lc1. ss.
  econs. econs 1; eauto. econs; eauto.
Qed.

Lemma reserve_or_cancel_cancellable lang (th0 th1: Thread.t lang)
      (STEPS: rtc (@Thread.reserve_step _ \2/ @Thread.cancel_step _) th0 th1)
      (LOCAL: Local.wf th0.(Thread.local) th0.(Thread.memory))
      (CLOSED: Memory.closed th0.(Thread.memory))
      (SC: Memory.closed_timemap th0.(Thread.sc) th0.(Thread.memory))
  :
    rtc (@Thread.reserve_step _ \2/ @Thread.cancel_step _) th1 th0.
Proof.
  ginduction STEPS; eauto. etrans; eauto. des.
  { dup H. inv H. exploit Thread.step_future; eauto. i. des.
    exploit IHSTEPS; eauto. i. etrans; eauto.
    econs; [|refl]. right. eapply reserve_step_cancel_step_eq; eauto. }
  { dup H. inv H. exploit Thread.step_future; eauto. i. des.
    exploit IHSTEPS; eauto. i. etrans; eauto.
    econs; [|refl]. left. eapply cancel_step_reserve_step_eq; eauto. }
Qed.

Lemma reserve_trace_reserve_steps lang (th0 th1: Thread.t lang) tr
      (STEPS: Trace.steps tr th0 th1)
      (RESERVE: List.Forall (fun lce => is_reserve (snd lce)) tr)
  :
    rtc (@Thread.reserve_step _) th0 th1.
Proof.
  ginduction STEPS; eauto. subst. i. inv RESERVE.
  exploit IHSTEPS; eauto. i. econs; eauto. ss.
  unfold is_reserve in *. des_ifs. econs; eauto.
Qed.

Lemma cancel_trace_cancel_steps lang (th0 th1: Thread.t lang) tr
      (STEPS: Trace.steps tr th0 th1)
      (RESERVE: List.Forall (fun lce => is_cancel (snd lce)) tr)
  :
    rtc (@Thread.cancel_step _) th0 th1.
Proof.
  ginduction STEPS; eauto. subst. i. inv RESERVE.
  exploit IHSTEPS; eauto. i. econs; eauto. ss.
  unfold is_cancel in *. des_ifs.
  dup STEP. inv STEP0; inv STEP1; inv LOCAL. inv PROMISE.
  econs; eauto.
Qed.

Lemma tau_steps_consistent_split lang (th0 th1: Thread.t lang)
      (STEPS: rtc (tau (@pred_step no_sc _)) th0 th1)
      (CONSISTENT: Thread.consistent th1)
      (LOCAL: Local.wf th0.(Thread.local) th0.(Thread.memory))
      (MEM: Memory.closed th0.(Thread.memory))
      (SC: Memory.closed_timemap th0.(Thread.sc) th0.(Thread.memory))
  :
    exists th0',
      (<<RESERVESTEPS: rtc (@Thread.reserve_step _ \2/ @Thread.cancel_step _) th0 th0'>>) /\
      (<<CONSISTENT: Thread.consistent th0'>>).
Proof.
  exploit Thread.rtc_tau_step_future.
  { eapply rtc_implies; try apply STEPS; eauto.
    i. inv H. inv TSTEP. econs; eauto. }
  { eauto. }
  { eauto. }
  { eauto. }
  i. des.
  exploit consistent_pf_consistent_super_strong; eauto. i. des.
  exploit (@concrete_promise_max_timemap_exists th1.(Thread.memory) th1.(Thread.local).(Local.promises)).
  { eapply CLOSED2. } i. des. destruct th1; ss.
  exploit (CONSISTENT0 memory TimeMap.bot); eauto.
  { refl. }
  i. des. ss.
  clear CANCELNORMAL SPLIT MAPLT MAPIDENT BOUND TRACE GOOD SC0 PROMCONSISTENT.
  eapply pred_steps_trace_steps2 in STEPS0; cycle 1.
  { instantiate (1:=no_sc). eapply List.Forall_impl; eauto.
    i. ss. des. splits; auto. }
  exploit steps_cancels_not_cancels.
  { etrans.
    { eapply STEPS. }
    { eapply STEPS0. }
  }
  i. des.

  exploit Thread.rtc_tau_step_future.
  { eapply rtc_implies; try apply STEPS1; eauto.
    i. inv H. econs; eauto.
    { econs; eauto. }
    { ss. }
  }
  { eauto. }
  { eauto. }
  { eauto. }
  i. ss. des.

  destruct th1, e1. ss. eapply pred_steps_trace_steps in STEPS2. des.
  exploit can_reserve_all_needed.
  { instantiate (1:=fun _ _ => True). esplits; eauto. eapply Time.incr_spec. }
  { ii. ss. }
  { eapply STEPS3. }
  { eapply List.Forall_impl; eauto. i. ss. des. splits; auto.
    destruct a. ss. destruct t0; ss. }
  { eauto. }
  { eauto. }
  { eauto. }
  i. des. esplits.
  { etrans.
    { eapply rtc_implies; cycle 1.
      { eapply STEPS1. }
      { auto. }
    }
    { eapply reserve_trace_reserve_steps in RESERVESTEPS.
      { eapply rtc_implies; cycle 1.
        { eapply RESERVESTEPS. }
        { i. left. auto. }
      }
      { eapply List.Forall_impl; eauto. i. ss. des; auto. }
    }
  }

  { unguard. des.
    { ii. left. exploit (CAP mem1).
      { eapply CAP0. }
      i. ss. des.
      eapply no_sc_any_sc_traced in CANCELSTEPS; eauto; cycle 1.
      { eapply List.Forall_impl; eauto. clear.
        i. ss. des. unfold is_cancel in *. des_ifs. }
      des. eapply Trace.silent_steps_tau_steps in STEPS4; cycle 1.
      { eapply List.Forall_impl; eauto. clear.
        i. ss. des; auto. unfold is_cancel in *. des_ifs. }
      eapply no_sc_any_sc_traced in STEPS2; eauto; cycle 1.
      { eapply List.Forall_impl; eauto. clear.
        i. ss. des. unfold is_cancel in *. des_ifs. }
      des. eapply Trace.silent_steps_tau_steps in STEPS5; cycle 1.
      { eapply List.Forall_impl; eauto. i. ss. des. auto. }
      unfold Thread.steps_failure. esplits.
      { etrans.
        { eapply STEPS4. }
        { eapply STEPS5. }
      }
      { eauto. }
    }
    { ii. right. exploit (CAP mem1).
      { eapply CAP0. }
      i. ss. des.
      eapply no_sc_any_sc_traced in CANCELSTEPS; eauto; cycle 1.
      { eapply List.Forall_impl; eauto. clear.
        i. ss. des. unfold is_cancel in *. des_ifs. }
      des. eapply Trace.silent_steps_tau_steps in STEPS4; cycle 1.
      { eapply List.Forall_impl; eauto. clear.
        i. ss. des; auto. unfold is_cancel in *. des_ifs. }
      eapply no_sc_any_sc_traced in STEPS2; eauto; cycle 1.
      { eapply List.Forall_impl; eauto. clear.
        i. ss. des. unfold is_cancel in *. des_ifs. }
      des. eapply Trace.silent_steps_tau_steps in STEPS5; cycle 1.
      { eapply List.Forall_impl; eauto. i. ss. des. auto. }
      unfold Thread.steps_failure. esplits.
      { etrans.
        { eapply STEPS4. }
        { eapply STEPS5. }
      }
      { eauto. }
    }
  }
Qed.


Lemma consistent_split lang (th0 th1' th1: Thread.t lang) pf e
      (STEP: Thread.step pf e th0 th1')
      (STEPS: rtc (@Thread.reserve_step _ \2/ @Thread.cancel_step _) th1' th1)
      (CONSISTENT: Thread.consistent th1 \/ e = ThreadEvent.failure)
      (LOCAL: Local.wf th0.(Thread.local) th0.(Thread.memory))
      (MEM: Memory.closed th0.(Thread.memory))
      (SC: Memory.closed_timemap th0.(Thread.sc) th0.(Thread.memory))
  :
    exists th0',
      (<<RESERVESTEPS: rtc (@Thread.reserve_step _ \2/ @Thread.cancel_step _) th0 th0'>>) /\
      (<<CONSISTENT: Thread.consistent th0'>>) /\
      (<<CANCELSTEPS: rtc (@Thread.reserve_step _ \2/ @Thread.cancel_step _) th0' th0>>).
Proof.
  destruct (classic (no_sc e)) as [NOSC|SCSTEP]; cycle 1.
  { exists th0. splits; eauto. ii. right. esplits; eauto. ss.
    inv STEP; inv STEP0; ss. inv LOCAL0; ss.
    { inv LOCAL1; ss. eapply PROMISES. apply NNPP in SCSTEP. destruct ordw; ss. }
    { inv LOCAL1; ss. eapply PROMISES. auto. }
  }
  destruct (ThreadEvent.get_machine_event e) eqn:EVT; cycle 1.
  { destruct e; ss. }
  { destruct e; ss. inv STEP; inv STEP0; ss. inv LOCAL0.
    esplits; eauto. left. unfold Thread.steps_failure. red. esplits; eauto.
  }
  des; clarify.
  assert (STEPS0: rtc (tau (@pred_step no_sc _)) th0 th1).
  { econs 2.
    { econs; eauto. econs; eauto. econs; eauto. }
    { eapply rtc_implies; cycle 1.
      { eapply STEPS. }
      { clear. i. ss. des.
        { inv H. econs; eauto.
          { econs; eauto.
            { econs; eauto. }
            { ss. }
          }
          { ss. }
        }
        { inv H. econs; eauto.
          { econs; eauto.
            { econs; eauto. }
            { ss. }
          }
          { ss. }
        }
      }
    }
  }
  exploit tau_steps_consistent_split; eauto. i. des.
  esplits; eauto. eapply reserve_or_cancel_cancellable; eauto.
Qed.


Module SConfiguration.

  Inductive step: forall (e:ThreadEvent.t) (tid:Ident.t) (c1 c2:Configuration.t), Prop :=
  | step_intro
      pf e tid c1 lang st1 lc1 e2 e3 st4 lc4 sc4 memory4
      (TID: IdentMap.find tid c1.(Configuration.threads) = Some (existT _ lang st1, lc1))
      (CANCELS: rtc (@Thread.cancel_step _) (Thread.mk _ st1 lc1 c1.(Configuration.sc) c1.(Configuration.memory)) e2)
      (STEP: Thread.step pf e e2 e3)
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
    forall (e:MachineEvent.t) (tid:Ident.t) (c1 c2:Configuration.t), Prop :=
  | mixed_step_intro
      pf e tid c1 lang st1 lc1 e2 e3 st4 lc4 sc4 memory4
      (TID: IdentMap.find tid c1.(Configuration.threads) = Some (existT _ lang st1, lc1))
      (CANCELS: rtc (@Thread.reserve_step _ \2/ @Thread.cancel_step _) (Thread.mk _ st1 lc1 c1.(Configuration.sc) c1.(Configuration.memory)) e2)
      (STEP: Thread.step pf e e2 e3)
      (RESERVES: rtc (@Thread.reserve_step _ \2/ @Thread.cancel_step _) e3 (Thread.mk _ st4 lc4 sc4 memory4))
      (CONSISTENT: e <> ThreadEvent.failure -> Thread.consistent (Thread.mk _ st4 lc4 sc4 memory4)):
      mixed_step (ThreadEvent.get_machine_event e) tid c1 (Configuration.mk (IdentMap.add tid (existT _ _ st4, lc4) c1.(Configuration.threads)) sc4 memory4)
  .
  Hint Constructors mixed_step.

  Inductive opt_step: forall (e: MachineEvent.t) (tid: Ident.t) (c1 c2: Configuration.t), Prop :=
  | step_none
      tid c:
      opt_step MachineEvent.silent tid c c
  | step_some
      e tid c1 c2
      (STEP: machine_step e tid c1 c2):
      opt_step e tid c1 c2
  .
  Hint Constructors opt_step.

  Definition tau_step := union (machine_step MachineEvent.silent).

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
      etrans.
      { econs 2; [|refl]. econs; eauto. econs; eauto. }
      { eapply rtc_implies; try apply RESERVES. i. inv H.
        econs; eauto. econs; eauto. }
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

  Lemma opt_step_future
        e tid c1 c2
        (STEP: opt_step e tid c1 c2)
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
        (STEPS: rtc tau_step c1 c2)
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

End SConfiguration.

Lemma single_mixed_step_single_step e tid c1 c2
      (STEP: SConfiguration.mixed_step e tid c1 c2)
      (WF: Configuration.wf c1)
  :
    SConfiguration.opt_step e tid c1 c2.
Proof.
Admitted.

Lemma step_split e tid c1 c3
      (STEP: Configuration.step e tid c1 c3)
      (WF: Configuration.wf c1)
  :
    exists c2,
      (<<STEPS: rtc SConfiguration.tau_step c1 c2>>) /\
      (<<STEP: SConfiguration.opt_step e tid c2 c3>>).
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
  { i. exploit single_mixed_step_single_step.
    { econs; eauto. }
    { eauto. }
    i. des. eauto.
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
  exploit single_mixed_step_single_step.
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
    instantiate (1:=ThreadEvent.get_machine_event e0).
    econs; ss; eauto. erewrite IdentMap.gss. ss.
  }
  { exploit SConfiguration.rtc_step_future; eauto. i. des.
    exploit SConfiguration.opt_step_future; eauto. i. des. ss. }
  i. des. erewrite IdentMap.add_add_eq in *.
  esplits; try apply x0. etrans; eauto.
  clear - STEP1. inv STEP1; eauto. econs 2; eauto. econs; eauto.
Qed.
