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

Require Import FutureCertify.

Set Implicit Arguments.


Module Deadlock.
  Lemma normal_step_consistent
        c1 c2
        (STEP: Configuration.normal_step c1 c2)
        (WF1: Configuration.wf c1)
        (CONSISTENT1: Configuration.consistent c1):
    Configuration.consistent c2.
  Proof.
    exploit Configuration.normal_step_future; eauto. i. des.
    inv STEP. inv STEP0; ss.
    inv WF1. inv WF. exploit THREADS; eauto. i.
    exploit Thread.rtc_tau_step_future; eauto. s. i. des.
    exploit Thread.step_future; eauto. s. i. des.
    unfold Configuration.consistent, Threads.consistent in *. s. i.
    dup TH. revert TH0.
    erewrite IdentMap.gsspec. condtac; ss; i.
    { Configuration.simplify. }
    hexploit CONSISTENT1; try exact TH0. i.
    hexploit FutureCertify.future_consistent; try exact H; s; [..|eauto]; eauto.
    - eapply Memory.future_future_weak. etrans; eauto.
    - eapply WF2; eauto.
  Qed.

  Lemma rtc_normal_step_consistent
        c1 c2
        (STEPS: rtc Configuration.normal_step c1 c2)
        (WF1: Configuration.wf c1)
        (CONSISTENT1: Configuration.consistent c1):
    Configuration.consistent c2.
  Proof.
    induction STEPS; ss.
    exploit Configuration.normal_step_future; eauto. i. des.
    eauto using normal_step_consistent.
  Qed.

  Lemma progress
        c
        (WF: Configuration.wf c)
        (CONSISTENT: Configuration.consistent c):
    (exists c', rtc Configuration.tau_step c c' /\ Configuration.no_promise c') \/
    (exists tid c1 c2,
        rtc Configuration.tau_step c c1 /\
        Configuration.step MachineEvent.failure tid c1 c2).
  Proof.
    destruct c as [ths sc mem]. ss.
    remember (Threads.tids ths) as tids eqn:TIDS.
    assert (NOTIN: forall tid lang st lc
                     (FIND: IdentMap.find tid ths = Some (existT _ lang st, lc))
                     (TID: ~ List.In tid (IdentSet.elements tids)),
               (Local.promises lc) = Memory.bot).
    { i. destruct (IdentSet.mem tid tids) eqn:MEM.
      - exfalso. apply TID. rewrite IdentSet.mem_spec in MEM.
        rewrite <- IdentSet.elements_spec1 in MEM.
        clear - MEM. induction MEM; [econs 1|econs 2]; auto.
      - rewrite TIDS in MEM. rewrite Threads.tids_o in MEM.
        destruct (IdentMap.find tid ths) eqn:IFIND; [inv MEM|]. ss. }
    assert (TIDS_MEM: forall tid, List.In tid (IdentSet.elements tids) -> IdentSet.mem tid tids = true).
    { i. rewrite IdentSet.mem_spec.
      rewrite <- IdentSet.elements_spec1.
      eapply SetoidList.In_InA; auto. }
    assert (NODUP: List.NoDup (IdentSet.elements tids)).
    { specialize (IdentSet.elements_spec2w tids). i.
      clear - H. induction H; econs; eauto. }
    revert NOTIN TIDS_MEM NODUP.
    move tids at top. revert_until tids.
    induction (IdentSet.elements tids); i.
    { left. esplits; eauto. ii. eauto. }

    destruct (IdentMap.find a ths) as [[[lang st] lc]|] eqn:FIND; cycle 1.
    { eapply IHl; eauto; i.
      - eapply NOTIN; eauto. ii. inv H; ss. congr.
      - eapply TIDS_MEM; eauto. econs 2; eauto.
      - inv NODUP. ss.
    }
    dup CONSISTENT.
    unfold Configuration.consistent, Threads.consistent in CONSISTENT0.
    hexploit CONSISTENT0; eauto. s. intro CONS_TH.
    dup WF. inv WF0. inv WF1. ss. clear DISJOINT.
    exploit THREADS; eauto. intro WF_TH. clear THREADS.
    exploit FutureCertify.future_certify_exists; eauto; ss; try refl. i. des.
    { right.
      unfold Thread.steps_failure in *. des. destruct e3.
      esplits; try refl. econs; eauto.
    }
    exploit rtc_tail; eauto. i. des; cycle 1.
    { subst. ss. eapply IHl; eauto; i.
      - destruct (Ident.eq_dec a tid).
        + subst. rewrite FIND in *. Configuration.simplify.
        + eapply NOTIN; eauto. ii. des; ss.
      - inv NODUP. ss.
    }

    destruct e2 as [st2 lc2 sc2 mem2].
    inv x1. inv TSTEP.
    assert (CSTEP: Configuration.step
                     MachineEvent.silent a
                     (Configuration.mk ths sc mem)
                     (Configuration.mk (IdentMap.add a (existT _ lang st2, lc2) ths) sc2 mem2)).
    { rewrite <- EVENT. econs; eauto.
      - destruct e; ss.
      - ii. right. esplits; eauto. }
    exploit Configuration.step_future; eauto. s. i. des.
    hexploit normal_step_consistent; [econs|..]; eauto; ss. i.
    exploit IHl; try exact WF2; eauto; i.
    { rewrite Threads.tids_add. rewrite IdentSet.add_mem; eauto. }
    { revert FIND0. rewrite IdentMap.gsspec. condtac; ss; i.
      - subst. Configuration.simplify.
      - eapply NOTIN; eauto. ii. des; ss. subst. ss. }
    { inv NODUP. ss. }
    i. des.
    - left. esplits; try exact x1.
      econs 2; eauto. econs; eauto.
    - right. esplits; try exact x1.
      econs 2; eauto. econs; eauto.
  Qed.

  Lemma deadlock_free
        pgm c
        (STEPS: rtc Configuration.normal_step (Configuration.init pgm) c):
    (exists c', rtc Configuration.tau_step c c' /\ Configuration.no_promise c') \/
    (exists tid c1 c2,
        rtc Configuration.tau_step c c1 /\
        Configuration.step MachineEvent.failure tid c1 c2).
  Proof.
    specialize (Configuration.init_wf pgm). intro WF.
    hexploit rtc_normal_step_consistent; eauto.
    { ii. ss. right. esplits; eauto. ss.
      unfold Threads.init in *. rewrite IdentMap.Facts.map_o in *.
      destruct (@UsualFMapPositive.UsualPositiveMap'.find
                  (@sigT _ (@Language.syntax ProgramEvent.t)) tid pgm); inv TH.
      ss. }
    intro CONS.
    exploit Configuration.rtc_normal_step_future; eauto. i. des.
    eapply progress; eauto.
  Qed.
End Deadlock.
