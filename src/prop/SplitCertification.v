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

Require Import MemoryMerge.
Require Import ReorderCancel.
Require Import ReorderReserve.
Require Import MemoryProps.
Require Import Mapping.
Require Import PFConsistent.
Require Import PFConsistentStrong.
Require Import FutureCertify.

Require Import PreReserve.

Set Implicit Arguments.



Lemma reorder_reserves_opt_step_cancels
      lang
      e th0 th1 th2 th3
      (STEPS1: rtc (@Thread.reserve_step lang \2/ @Thread.cancel_step _) th0 th1)
      (STEP2: Thread.opt_step e th1 th2)
      (STEPS3: rtc (@Thread.reserve_step lang \2/ @Thread.cancel_step _) th2 th3)
  :
    (exists th1' th2',
      (<<STEPS1: rtc (@Thread.cancel_step lang) th0 th1'>>) /\
      (<<STEP2: Thread.opt_step e th1' th2'>>) /\
      (<<STEPS3: rtc (@Thread.reserve_step lang) th2' th3>>)) \/
    (exists th1',
      (<<STEPS1: rtc (@Thread.cancel_step lang) th0 th1'>>) /\
      (<<STEPS3: rtc (@Thread.reserve_step lang) th1' th3>>) /\
      (<<RESERVATION: ~ ThreadEvent.is_normal e>>)).
Proof.
  destruct (classic (ThreadEvent.is_normal e)) as [NRESERVATION|RESERVATION]; cycle 1.
  { right.
    assert (STEPS: rtc (@Thread.reserve_step lang \2/ @Thread.cancel_step _) th0 th3).
    { etrans.
      { eapply STEPS1. }
      econs 2.
      { instantiate (1:=th2). apply NNPP in RESERVATION. inv STEP2; ss.
        eapply Thread.reservation_event_reserve_or_cancel_step; eauto. }
      { eapply STEPS3. }
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
    esplits.
    { eapply rtc_implies; try apply STEPS0.
      clear. i. inv H. inv TSTEP. des; ss. inv STEP.
      unfold ThreadEvent.is_cancel in *. des_ifs. econs; eauto. }
    { eapply STEPS2. }
    { auto. }
  }
  eapply rtc_implies with (R2:=tau (@pred_step (ThreadEvent.is_reserve \1/ ThreadEvent.is_cancel) _)) in STEPS1; cycle 1.
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
  hexploit steps_not_reserves_reserves; try apply STEPS1. i. des.
  hexploit reorder_reserves_opt_step; eauto. i. des; cycle 1.
  { exfalso. eapply NRESERVATION. unfold ThreadEvent.is_cancel in *. des_ifs. }
  hexploit (@steps_cancels_not_cancels (ThreadEvent.is_reserve \1/ ThreadEvent.is_cancel)).
  { etrans.
    { eapply rtc_implies; try apply STEPS4. i. inv H. econs; eauto.
      { econs.
        { econs; eauto. }
        { ss; auto. }
      }
      { ss. }
    }
    { eapply rtc_implies; try apply STEPS3.
      clear. i. ss. des.
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
  }
  i. des.
  hexploit reorder_opt_step_cancels.
  { eapply STEP1. }
  { eapply STEPS5. }
  i. des; cycle 1.
  { exfalso. eapply NRESERVATION. unfold ThreadEvent.is_reserve in *. des_ifs. }
  left. esplits.
  { etrans.
    { eapply rtc_implies; try apply STEPS0.
      clear. i. inv H. inv TSTEP. des; ss.
      unfold ThreadEvent.is_cancel in *. des_ifs. inv STEP. econs; eauto. }
    { eapply STEPS7. }
  }
  { eapply STEP0. }
  { eapply rtc_implies; try apply STEPS6.
    clear. i. inv H. inv TSTEP. des; ss.
    unfold ThreadEvent.is_cancel in *. des_ifs. inv STEP. econs; eauto.
  }
Qed.

Lemma reorder_reserves_opt_step_cancels2
      lang
      e th0 th1 th2 th3
      (STEPS1: rtc (@Thread.reserve_step lang \2/ @Thread.cancel_step _) th0 th1)
      (STEP2: Thread.opt_step e th1 th2)
      (STEPS3: rtc (@Thread.reserve_step lang \2/ @Thread.cancel_step _) th2 th3)
  :
    exists th1' th2' e',
      (<<STEPS1: rtc (@Thread.cancel_step lang) th0 th1'>>) /\
      (<<STEP2: Thread.opt_step e' th1' th2'>>) /\
      (<<STEPS3: rtc (@Thread.reserve_step lang) th2' th3>>) /\
      __guard__(e' = e \/ e' = ThreadEvent.silent /\ (<<RESERVATION: ~ ThreadEvent.is_normal e>>)).
Proof.
  hexploit reorder_reserves_opt_step_cancels.
  { eapply STEPS1. }
  { eapply STEP2. }
  { eapply STEPS3. }
  i. des.
  { esplits; eauto. left. auto. }
  { esplits.
    { eapply STEPS0. }
    { econs 1. }
    { eapply STEPS2. }
    right. splits; auto.
  }
Qed.

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

Lemma reserve_steps_le_cancel_steps lang (th0 th1: Thread.t lang)
      (STEPS: rtc (@Thread.reserve_step _) th0 th1)
      cap sc
      (CAP: Memory.le th1.(Thread.memory) cap)
  :
    exists th0',
      (<<STEPS: rtc (@Thread.cancel_step _) (Thread.mk _ th1.(Thread.state) th1.(Thread.local) sc cap) th0'>>) /\
      (<<LOCAL: th0'.(Thread.local) = th0.(Thread.local)>>) /\
      (<<MLE: Memory.le th0.(Thread.memory) th0'.(Thread.memory)>>).
Proof.
  ginduction STEPS.
  { i. esplits; eauto. }
  i. exploit IHSTEPS; eauto. i. des.
  inv H. inv STEP; inv STEP0; inv LOCAL0. inv PROMISE. ss.
  exploit (@Memory.remove_exists promises2 loc from to Message.reserve).
  { eapply Memory.add_get0; eauto. } i. des.
  exploit (@Memory.remove_exists th0'.(Thread.memory) loc from to Message.reserve).
  { eapply MLE. eapply Memory.add_get0; eauto. } i. des.
  destruct th0'. ss. esplits.
  { etrans; [eapply STEPS0|]. econs; [|refl]. econs.
    econs 1. econs; eauto. rewrite LOCAL. econs.
    { econs; eauto. }
    { econs. }
    { ss. }
  }
  { ss. clarify. destruct lc1; ss. f_equal.
    symmetry. eapply MemoryMerge.add_remove; eauto. }
  { ss. ii. exploit Memory.add_get1.
    { eapply MEM. }
    { eapply LHS. }
    i. eapply MLE in x2. eapply Memory.remove_get1 in x2; eauto.
    des; clarify.
    exfalso. eapply Memory.add_get0 in MEM. des. clarify.
  }
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
      (RESERVE: List.Forall (fun lce => ThreadEvent.is_reserve (snd lce)) tr)
  :
    rtc (@Thread.reserve_step _) th0 th1.
Proof.
  ginduction STEPS; eauto. subst. i. inv RESERVE.
  exploit IHSTEPS; eauto. i. econs; eauto. ss.
  unfold ThreadEvent.is_reserve in *. des_ifs. econs; eauto.
Qed.

Lemma cancel_trace_cancel_steps lang (th0 th1: Thread.t lang) tr
      (STEPS: Trace.steps tr th0 th1)
      (RESERVE: List.Forall (fun lce => ThreadEvent.is_cancel (snd lce)) tr)
  :
    rtc (@Thread.cancel_step _) th0 th1.
Proof.
  ginduction STEPS; eauto. subst. i. inv RESERVE.
  exploit IHSTEPS; eauto. i. econs; eauto. ss.
  unfold ThreadEvent.is_cancel in *. des_ifs.
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
        i. ss. des. unfold ThreadEvent.is_cancel in *. des_ifs. }
      des. eapply Trace.silent_steps_tau_steps in STEPS4; cycle 1.
      { eapply List.Forall_impl; eauto. clear.
        i. ss. des; auto. unfold ThreadEvent.is_cancel in *. des_ifs. }
      eapply no_sc_any_sc_traced in STEPS2; eauto; cycle 1.
      { eapply List.Forall_impl; eauto. clear.
        i. ss. des. unfold ThreadEvent.is_cancel in *. des_ifs. }
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
        i. ss. des. unfold ThreadEvent.is_cancel in *. des_ifs. }
      des. eapply Trace.silent_steps_tau_steps in STEPS4; cycle 1.
      { eapply List.Forall_impl; eauto. clear.
        i. ss. des; auto. unfold ThreadEvent.is_cancel in *. des_ifs. }
      eapply no_sc_any_sc_traced in STEPS2; eauto; cycle 1.
      { eapply List.Forall_impl; eauto. clear.
        i. ss. des. unfold ThreadEvent.is_cancel in *. des_ifs. }
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
