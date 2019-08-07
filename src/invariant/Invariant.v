Require Import Omega.
Require Import RelationClasses.

Require Import sflib.
From Paco Require Import paco.

Require Import Axioms.
Require Import Basic.
Require Import DataStructure.
Require Import DenseOrder.
Require Import Event.
Require Import Time.
Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.

Require Import PromiseConsistent.

Require Import PFStepCommon.
Require Import PFStep.
Require Import PFStepCap.

Set Implicit Arguments.


Definition ThreadsProp :=
  forall (tid:Ident.t)
    (lang:Language.t)
    (st:lang.(Language.state)),
    Prop.

Definition MemoryProp :=
  forall (assign: LocFun.t Const.t),
    Prop.

Section Invariant.
  Variable
    (S:ThreadsProp)
    (J:MemoryProp).

  Hypothesis
    (SILENT:
       forall tid lang st1 st2
         (ST1: S tid lang st1)
         (STEP: lang.(Language.step) ProgramEvent.silent st1 st2),
         S tid lang st2)
    (READ:
       forall tid lang st1 st2
         loc val ord
         assign
         (ST1: S tid lang st1)
         (ASSIGN1: J assign /\ LocFun.find loc assign = val)
         (STEP: lang.(Language.step) (ProgramEvent.read loc val ord) st1 st2),
         S tid lang st2)
    (WRITE:
       forall tid lang st1 st2
         loc val ord
         (ST1: S tid lang st1)
         (STEP: lang.(Language.step) (ProgramEvent.write loc val ord) st1 st2),
         <<ST2: S tid lang st2>> /\
         <<ASSIGN2: forall assign, J assign -> J (LocFun.add loc val assign)>>)
    (UPDATE:
       forall tid lang st1 st2
         loc valr valw ordr ordw
         assign
         (ST1: S tid lang st1)
         (ASSIGN1: J assign /\ LocFun.find loc assign = valr)
         (STEP: lang.(Language.step) (ProgramEvent.update loc valr valw ordr ordw) st1 st2),
         <<ST2: S tid lang st2>> /\
         <<ASSIGN2: forall assign, J assign -> J (LocFun.add loc valw assign)>>)
    (FENCE:
       forall tid lang st1 st2
         ordr ordw
         (ST1: S tid lang st1)
         (STEP: lang.(Language.step) (ProgramEvent.fence ordr ordw) st1 st2),
         S tid lang st2)
    (SYSCALL:
       forall tid lang st1 st2
         e
         (ST1: S tid lang st1)
         (STEP: lang.(Language.step) (ProgramEvent.syscall e) st1 st2),
         S tid lang st2)
    (ABORT:
       forall tid lang st1 st2
         (ST1: S tid lang st1)
         (STEP: lang.(Language.step) ProgramEvent.abort st1 st2),
         <<ST2: forall tid lang st, S tid lang st>> /\
         <<ASSIGN2: forall assign, J assign>>)
  .

  Definition sem_threads (ths:Threads.t): Prop :=
    forall tid lang st lc
      (FIND: IdentMap.find tid ths = Some (existT _ lang st, lc)),
      S tid lang st.

  Definition memory_assign (m:Memory.t) (assign:Loc.t -> Const.t) :=
    forall loc,
    exists from to released,
      Memory.get loc to m =
      Some (from, Message.full (LocFun.find loc assign) released).

  Definition sem_memory (m:Memory.t): Prop :=
    memory_assign m <1= J.

  Inductive sem (c:Configuration.t): Prop :=
  | sem_configuration_intro
      (TH: sem_threads c.(Configuration.threads))
      (MEM: sem_memory c.(Configuration.memory))
  .

  Lemma sem_memory_read_step
        lc1 mem1 loc to val released ord lc2
        (INHABITED: Memory.inhabited mem1)
        (STEP: Local.read_step lc1 mem1 loc to val released ord lc2)
        (SEM: sem_memory mem1):
    exists assign,
      J assign /\ LocFun.find loc assign = val.
  Proof.
    exists (LocFun.add loc val (LocFun.init 0)).
    splits.
    - apply SEM. ii.
      destruct (Loc.eq_dec loc loc0).
      + subst. rewrite LocFun.add_spec_eq.
        inv STEP. esplits; eauto.
      + rewrite LocFun.add_spec_neq, LocFun.init_spec.
        specialize (INHABITED loc0).
        esplits; eauto. congr.
    - apply LocFun.add_spec_eq.
  Qed.

  Lemma sem_memory_write_step_eq
        lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind
        assign
        (INHABITED: Memory.inhabited mem1)
        (STEP: Local.write_step lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind)
        (SEM: memory_assign mem2 assign)
        (LOC: LocFun.find loc assign = val):
    exists assign0,
      memory_assign mem1 assign0 /\
      assign = LocFun.add loc val assign0.
  Proof.
    exists (LocFun.add loc 0 assign). splits; cycle 1.
    - rewrite LocFun.add_add_eq. apply LocFun.ext. i.
      rewrite LocFun.add_spec. condtac; subst; ss.
    - ii. rewrite LocFun.add_spec. condtac.
      { specialize (INHABITED loc0). esplits; eauto. }
      specialize (SEM loc0). des. revert SEM.
      inv STEP. inv WRITE0. inv PROMISE.
      + erewrite Memory.add_o; eauto. condtac; ss.
        * i. des. inv SEM. congr.
        * i. esplits; eauto.
      + erewrite Memory.split_o; eauto. condtac; ss.
        { i. des. inv SEM. congr. }
        condtac; ss.
        { guardH o. des. subst. congr. }
        i. esplits; eauto.
      + erewrite Memory.lower_o; eauto. condtac; ss.
        * i. des. inv SEM. congr.
        * i. esplits; eauto.
  Qed.

  Lemma sem_memory_write_step_neq
        lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind
        assign
        (STEP: Local.write_step lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind)
        (SEM: memory_assign mem2 assign)
        (LOC: LocFun.find loc assign <> val):
    memory_assign mem1 assign.
  Proof.
    ii. specialize (SEM loc0). des. revert SEM.
    inv STEP. inv WRITE0. inv PROMISE.
    - erewrite Memory.add_o; eauto. condtac; ss.
      + i. des. inv SEM. congr.
      + i. esplits; eauto.
    - erewrite Memory.split_o; eauto. condtac; ss.
      { i. des. inv SEM. congr. }
      condtac; ss.
      { guardH o. i. des. inv SEM.
        exploit Memory.split_get0; try exact MEM; eauto. i. des.
        esplits; eauto.
      }
      i. esplits; eauto.
    - erewrite Memory.lower_o; eauto. condtac; ss.
      + i. des. inv SEM. congr.
      + i. esplits; eauto.
  Qed.

  Lemma vals_incl_sem_memory
        mem1 mem2
        (VALS: PFStepCommon.vals_incl mem1 mem2)
        (MEM2: sem_memory mem2):
    sem_memory mem1.
  Proof.
    ii. apply MEM2. ii. specialize (PR loc). des.
    exploit VALS; eauto.
  Qed.

  Lemma thread_step_sem
        tid lang e
        st1 lc1 sc1 mem1
        st2 lc2 sc2 mem2
        (TH1: S tid lang st1)
        (MEM1: sem_memory mem1)
        (INHABITED1: Memory.inhabited mem1)
        (STEP: Thread.program_step e (Thread.mk lang st1 lc1 sc1 mem1) (Thread.mk lang st2 lc2 sc2 mem2)):
    <<TH2: S tid lang st2>> /\
    <<MEM2: sem_memory mem2>>.
  Proof.
    inv STEP. inv LOCAL.
    - esplits; eauto.
    - exploit sem_memory_read_step; eauto. i. des.
      exploit READ; eauto.
    - exploit WRITE; eauto. i. des.
      esplits; eauto. ii.
      destruct (Const.eq_dec (LocFun.find loc x0) val).
      { subst. hexploit sem_memory_write_step_eq; eauto. i. des.
        rewrite H0. eauto.
      }
      { hexploit sem_memory_write_step_neq; eauto. }
    - exploit sem_memory_read_step; eauto. i. des.
      exploit UPDATE; eauto. i. des.
      esplits; eauto. ii.
      destruct (Const.eq_dec (LocFun.find loc x2) valw).
      { subst. hexploit sem_memory_write_step_eq; eauto. i. des.
        rewrite H0. eauto.
      }
      { hexploit sem_memory_write_step_neq; eauto. }
    - exploit FENCE; eauto.
    - exploit SYSCALL; eauto.
    - exploit ABORT; eauto. i. des.
      esplits; eauto.
  Qed.

  Lemma rtc_thread_step_sem
        tid lang
        th1 th2
        (TH1: S tid lang th1.(Thread.state))
        (MEM1: sem_memory th1.(Thread.memory))
        (INHABITED1: Memory.inhabited th1.(Thread.memory))
        (STEP: rtc (union (@Thread.program_step lang)) th1 th2):
    <<TH2: S tid lang th2.(Thread.state)>> /\
    <<MEM2: sem_memory th2.(Thread.memory)>>.
  Proof.
    move STEP after TH1. revert_until STEP. induction STEP; ss.
    i. inv H.
    destruct x, y. ss.
    exploit thread_step_sem; eauto. i. des.
    eapply IHSTEP; eauto.
    hexploit Thread.program_step_inhabited; try exact USTEP; eauto.
  Qed.

  Lemma thread_pf_step_sem
        tid lang caps
        st1 lc1 sc1 mem1
        st2 lc2 sc2 mem2
        (TH1: S tid lang st1)
        (MEM1: sem_memory mem1)
        (INHABITED1: Memory.inhabited mem1)
        (STEP: PFStepCap.pf_step caps (Thread.mk lang st1 lc1 sc1 mem1) (Thread.mk lang st2 lc2 sc2 mem2)):
    <<TH2: S tid lang st2>> /\
    <<MEM2: sem_memory mem2>>.
  Proof.
    inv STEP.
    exploit thread_step_sem; try exact STEP0; eauto. i. des.
    split; auto.
    hexploit PFStepCap.add_cap_vals_incl; eauto. i.
    eapply vals_incl_sem_memory; eauto.
  Qed.

  Lemma rtc_thread_pf_step_sem
        tid lang caps
        th1 th2
        (TH1: S tid lang th1.(Thread.state))
        (MEM1: sem_memory th1.(Thread.memory))
        (INHABITED1: Memory.inhabited th1.(Thread.memory))
        (STEP: rtc (PFStepCap.pf_step caps) th1 th2):
    <<TH2: S tid lang th2.(Thread.state)>> /\
    <<MEM2: sem_memory th2.(Thread.memory)>>.
  Proof.
    move STEP after TH1. revert_until STEP.
    induction STEP; ss.
    i. hexploit PFStepCap.pf_step_inhabited; eauto. i. des.
    destruct x, y. ss.
    exploit thread_pf_step_sem; eauto. i. des.
    eapply IHSTEP; eauto.
  Qed.

  Lemma future_sem_memory
        m1 m2
        (FUTURE: Memory.future m1 m2)
        (SEM: sem_memory m2):
    sem_memory m1.
  Proof.
    revert SEM. induction FUTURE; ss. i.
    hexploit IHFUTURE; eauto. i.
    ii. apply H0. ii. specialize (PR loc). des.
    inv H. exploit Memory.op_get1; eauto. i. des.
    inv MSG_LE. esplits; eauto.
  Qed.

  Lemma configuration_step_sem
        e tid c1 c2
        (WF: Configuration.wf c1)
        (SEM: sem c1)
        (STEP: Configuration.step e tid c1 c2):
    sem c2.
  Proof.
    inv SEM. econs.
    - inv STEP.
      + ss. ii. revert FIND.
        rewrite IdentMap.gsspec. condtac; ss; [|by apply TH]. subst.
        i. inv FIND. apply inj_pair2 in H1. subst.
        eapply rtc_implies in STEPS; [|by apply tau_union].
        exploit rtc_n1; eauto; i.
        { econs. econs. eauto. }
        inv STEP0; inv STEP. inv LOCAL. inv LOCAL0.
        clear STEPS COND STATE.
        inv WF. inv WF0. clear DISJOINT.
        exploit THREADS; eauto. intro WF. clear THREADS.
        exploit Thread.rtc_all_step_future; try eapply x0; eauto. s. i. des.
        exploit (@PFStep.sim_thread_exists
                   _ (Thread.mk lang0 st1 lc1 c1.(Configuration.sc) c1.(Configuration.memory))); ss.
        i. des.
        hexploit PFStep.sim_memory_inhabited; try eapply SIM; s.
        { apply WF. }
        { apply MEM0. }
        i. des.
        exploit PFStep.thread_rtc_all_step; try exact SIM; try eapply x0; eauto; ss.
        i. des.
        hexploit PFStep.sim_memory_vals_incl; try eapply SIM; eauto. s. i.
        hexploit vals_incl_sem_memory; eauto. i.
        destruct e_src, e2_src. ss. inv SIM. inv SIM2. ss. subst.
        exploit rtc_thread_step_sem; try exact STEPS_SRC; eauto. i. des. ss.
      + ss. ii. revert FIND.
        rewrite IdentMap.gsspec. condtac; ss; [|by apply TH]. subst.
        i. inv FIND. apply inj_pair2 in H1. subst.
        eapply rtc_implies in STEPS; [|by apply tau_union].
        exploit rtc_n1; eauto; i.
        { econs. econs. eauto. }
        clear STEP0 STEPS COND.
        inv WF. inv WF0. clear DISJOINT.
        exploit THREADS; eauto. intro WF. clear THREADS.
        exploit Thread.rtc_all_step_future; try eapply x0; eauto. s. i. des.
        exploit (@PFStep.sim_thread_exists
                   _ (Thread.mk lang0 st1 lc1 c1.(Configuration.sc) c1.(Configuration.memory))); ss.
        i. des.
        hexploit PFStep.sim_memory_inhabited; try eapply SIM; s.
        { apply WF. }
        { apply MEM0. }
        i. des.
        exploit PFStep.thread_rtc_all_step; try exact SIM; try eapply x0; eauto; ss.
        { hexploit consistent_promise_consistent; try exact CONSISTENT; ss. }
        i. des.
        hexploit PFStep.sim_memory_vals_incl; try eapply SIM; eauto. s. i.
        hexploit vals_incl_sem_memory; eauto. i.
        destruct e_src, e2_src. ss. inv SIM. inv SIM2. ss. subst.
        exploit rtc_thread_step_sem; try exact STEPS_SRC; eauto. i. des. ss.
    - inv STEP.
      + admit.
      + ss. inv WF. inv WF0. clear DISJOINT.
        exploit THREADS; eauto. intro WF. clear THREADS.
        eapply rtc_implies in STEPS; [|by apply tau_union].
        exploit rtc_n1; eauto.
        { econs. econs. eauto. }
        intro STEPS_TGT. clear STEP0 STEPS.
        exploit Thread.rtc_all_step_future; try exact STEPS_TGT; eauto. s. i. des.
        exploit Memory.cap_exists; try exact CLOSED2.
        instantiate (1 := lc3.(Local.promises)). i. des.
        exploit Memory.cap_closed; eauto. intro CLOSED_CAP.
        exploit Local.cap_wf; eauto. intro WF_CAP.
        exploit Memory.max_full_timemap_exists; try eapply CLOSED_CAP. i. des.
        exploit CONSISTENT; try exact CAP; try exact x0; eauto. s. i. des.
        * admit.
        * exploit (@PFStep.sim_thread_exists
                     _ (Thread.mk lang st1 lc1 c1.(Configuration.sc) c1.(Configuration.memory))); ss.
          i. des.
          hexploit PFStep.sim_memory_inhabited; try eapply SIM; s.
          { apply WF. }
          { apply MEM0. }
          intro INHABITED_SRC. des.
          exploit PFStep.thread_rtc_all_step; try exact SIM; eauto; ss.
          { hexploit consistent_promise_consistent; eauto. }
          i. des.
          exploit PFStepCap.sim_thread_exists; try exact SIM2; eauto. s. i. des.
          hexploit PFStepCap.sim_memory_inhabited; try eapply SIM0; s.
          { apply WF_CAP. }
          { apply CLOSED_CAP. }
          intro INHABITED_SRC_CAP. des.
          exploit PFStepCap.thread_rtc_all_step; try eapply rtc_implies; try exact STEPS; eauto; s.
          { apply Memory.max_full_timemap_closed; auto. }
          { i. inv PR. econs. eauto. }
          { ii. rewrite PROMISES in *. rewrite Memory.bot_get in *. ss. }
          i. des.
          exploit Thread.rtc_tau_step_future; try exact STEPS; eauto; s.
          { eapply Memory.max_full_timemap_closed; eauto. }
          i. des.
          hexploit PFStep.sim_memory_vals_incl; try eapply SIM; eauto. i.
          apply vals_incl_sem_memory in H; ss.
          exploit rtc_thread_step_sem; try exact STEPS_SRC; eauto.
          { inv SIM. ss. rewrite STATE. eauto. }
          i. des.
          apply vals_incl_sem_memory in VALS; ss.
          exploit rtc_thread_pf_step_sem; try exact STEPS_SRC0; eauto. i. des.
          hexploit PFStepCap.sim_memory_bot; try eapply SIM1; eauto. i.
          eapply future_sem_memory; eauto.
          eapply future_sem_memory; eauto.
          rewrite H0 in *. ss.
  Admitted.

  Inductive Configuration_step_evt (c1 c2:Configuration.t): Prop :=
  | Configuration_step_evt_intro
      e tid
      (STEP: Configuration.step e tid c1 c2)
  .

  Lemma init_sem
        program
        (TH: forall tid lang syn
               (FIND: IdentMap.find tid program = Some (existT _ lang syn)),
            S tid lang (lang.(Language.init) syn))
        (MEM: J (LocFun.init 0)):
    sem (Configuration.init program).
  Proof.
    econs.
    - ii. unfold Configuration.init in FIND. ss.
      unfold Threads.init in FIND. rewrite IdentMap.Facts.map_o in FIND.
      destruct ((UsualFMapPositive.UsualPositiveMap'.find tid program)) eqn:X; inv FIND.
      apply inj_pair2 in H1. subst. destruct s. ss.
      eapply TH; eauto.
    - ii. cut (x0 = LocFun.init 0); [by i; subst|].
      apply LocFun.ext. i. rewrite LocFun.init_spec.
      specialize (PR i). des. ss.
      unfold Memory.get, Memory.init in PR. unfold Cell.get, Cell.init in PR. ss.
      apply DOMap.singleton_find_inv in PR. des. inv PR0. auto.
  Qed.

  Lemma sound
        program c
        (TH: forall tid lang syn
               (FIND: IdentMap.find tid program = Some (existT _ lang syn)),
            S tid lang (lang.(Language.init) syn))
        (MEM: J (LocFun.init 0))
        (STEPS: rtc Configuration_step_evt (Configuration.init program) c):
    sem c.
  Proof.
    cut (forall c1 c2
           (WF: Configuration.wf c1)
           (SEM: sem c1)
           (STEPS: rtc Configuration_step_evt c1 c2),
            sem c2).
    { i. eapply H; eauto.
      - apply Configuration.init_wf.
      - apply init_sem; auto.
    }
    i. revert WF SEM. induction STEPS0; ss. i.
    inv H. exploit Configuration.step_future; eauto. i. des.
    apply IHSTEPS0; ss. eapply configuration_step_sem; try exact STEP; eauto.
  Qed.
End Invariant.
