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
Require Import ReorderPromises.
Require Import ConcreteStep.
Require Import LowerMemory.

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
        (CLOSED: Memory.closed mem1)
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
        inv CLOSED. specialize (INHABITED loc0).
        esplits; eauto. congr.
    - apply LocFun.add_spec_eq.
  Qed.

  Lemma sem_memory_write_step_eq
        lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind
        assign
        (CLOSED: Memory.closed mem1)
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
      { inv CLOSED. specialize (INHABITED loc). esplits; eauto. }
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
        (CLOSED: Memory.closed mem1)
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

  Lemma thread_step_sem
        tid lang e
        st1 lc1 sc1 mem1
        st2 lc2 sc2 mem2
        (TH1: S tid lang st1)
        (MEM1: sem_memory mem1)
        (WF1: Local.wf lc1 mem1)
        (SC1: Memory.closed_timemap sc1 mem1)
        (CLOSED1: Memory.closed mem1)
        (STEP: Thread.step true e (Thread.mk lang st1 lc1 sc1 mem1) (Thread.mk lang st2 lc2 sc2 mem2)):
    <<TH2: S tid lang st2>> /\
    <<MEM2: sem_memory mem2>>.
  Proof.
    inv STEP.
    { inv STEP0. symmetry in PF. apply promise_pf_inv in PF. des. subst.
      splits; ss. inv LOCAL. inv PROMISE.
      ii. apply MEM1. ii. specialize (PR loc0). des.
      revert PR. erewrite Memory.lower_o; eauto. condtac; eauto.
      ss. i. des. subst. inv PR. exploit Memory.lower_get0; eauto. i. des.
      inv MSG_LE. eauto.
    }
    inv STEP0. inv LOCAL.
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
  Qed.

  Lemma rtc_thread_step_sem
        tid lang
        th1 th2
        (TH1: S tid lang th1.(Thread.state))
        (MEM1: sem_memory th1.(Thread.memory))
        (WF1: Local.wf th1.(Thread.local) th1.(Thread.memory))
        (SC1: Memory.closed_timemap th1.(Thread.sc) th1.(Thread.memory))
        (CLOSED1: Memory.closed th1.(Thread.memory))
        (HALF_WF1: Memory.half_wf th1.(Thread.memory))
        (STEP: rtc (union (Thread.step true)) th1 th2):
    <<TH2: S tid lang th2.(Thread.state)>> /\
    <<MEM2: sem_memory th2.(Thread.memory)>>.
  Proof.
    move STEP after TH1. revert_until STEP. induction STEP; ss.
    i. inv H.
    exploit Thread.step_future; eauto. i. des.
    destruct x, y. ss.
    exploit thread_step_sem; eauto. i. des.
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

  Lemma concrete_none_sem_memory
        m1 m2
        (CLOSED: Memory.closed m1)
        (CONCRETE: Memory.concrete_none m1 m2)
        (SEM: sem_memory m1):
    sem_memory m2.
  Proof.
    ii. apply SEM. ii. specialize (PR loc). des.
    inv CONCRETE. exploit COMPLETE; eauto. i; des.
    - esplits; eauto.
    - exploit SOUND; eauto. i. des; try congr.
      rewrite PR in x3. inv x3. eauto.
  Qed.

  Lemma concrete_exact_sem_memory_inv
        m1 m2
        (CONCRETE: Memory.concrete_exact m1 m2)
        (SEM: sem_memory m2):
    sem_memory m1.
  Proof.
    ii. apply SEM. ii. specialize (PR loc). des.
    inv CONCRETE. exploit SOUND; eauto. i. des; try congr.
    esplits; eauto.
  Qed.

  Lemma lower_memory_sem_memory
        m1 m2
        (LOWER: LowerMemory.lower_memory m1 m2)
        (SEM: sem_memory m1):
    sem_memory m2.
  Proof.
    ii. apply SEM. ii. specialize (PR loc). des.
    inv LOWER. exploit COMPLETE; eauto. i. des.
    exploit MSG; eauto. i. inv x1. eauto.
  Qed.

  Lemma configuration_step_sem
        e tid c1 c2
        (WF: Configuration.wf c1)
        (SEM: sem c1)
        (STEP: Configuration.step e tid c1 c2):
    sem c2.
  Proof.
    inv SEM. econs.
    - inv STEP. ss. ii. revert FIND.
      rewrite IdentMap.gsspec. condtac; ss; [|by apply TH]. subst.
      i. inv FIND. apply inj_pair2 in H1. subst.
      eapply rtc_implies in STEPS; [|by apply tau_union].
      exploit rtc_n1; eauto; i.
      { econs. econs. eauto. }
      exploit Thread.rtc_all_step_future; eauto; ss; try by inv WF.
      { inv WF. eapply WF0. eauto. }
      i. des.
      exploit steps_pf_steps; eauto; ss; try by inv WF.
      { unfold Configuration.consistent in CONSISTENT. ss.
        unfold Threads.consistent in CONSISTENT.
        hexploit CONSISTENT; try eapply IdentMap.gss. i.
        hexploit consistent_promise_consistent; eauto. }
      { inv WF. eapply WF0. eauto. }
      i. des.
      exploit rtc_implies; [|exact STEPS1|i].
      { apply union_mon. apply Thread.allpf. }
      exploit Thread.rtc_all_step_future; eauto; ss; try by inv WF.
      { inv WF. eapply WF0. eauto. }
      i. des.
      exploit Thread.rtc_step_nonpf_future; eauto. s. i. des.
      subst. eapply rtc_thread_step_sem; try exact STEPS1; eauto; ss; try by inv WF.
      inv WF. eapply WF3. eauto.
    - inv STEP. ss.
      assert (WF_LOCAL: Local.wf lc1 (c1.(Configuration.memory))).
      { inv WF. inv WF0. eauto. }
      exploit Thread.rtc_tau_step_future; eauto; try by inv WF. s. i. des.
      exploit Thread.step_future; eauto. s. i. des.
      exploit Memory.no_half_concrete_exact_future_exists; try exact CLOSED0; eauto.
      { apply WF0. }
      i. des.
      unfold Configuration.consistent in CONSISTENT. ss.
      unfold Threads.consistent in CONSISTENT.
      hexploit CONSISTENT; try eapply IdentMap.gss. i.
      exploit H; try exact NOHALF; try refl; eauto; s.
      { inv WF0. econs; eauto. eapply TView.future_closed; eauto. }
      i. des.
      exploit Memory.no_half_concrete_none_future_exists.
      { apply WF_LOCAL. }
      { apply WF. }
      { apply WF. }
      i. des.
      assert (WF_LOCAL': Local.wf lc1 mem0).
      { inv WF_LOCAL. econs; eauto. eapply TView.future_closed; eauto. }
      exploit concrete_none_thread_rtc_tau_step;
        try exact STEPS; try exact CONCRETE0; eauto; try by inv WF. s. i. des.
      exploit concrete_none_thread_step; try exact STEP0; try exact CONCRETE2; eauto.
      { exploit Thread.rtc_tau_step_future; try exact STEPS'; eauto; s.
        { inv WF. eapply Memory.concrete_none_closed_timemap; eauto. }
        i. des. ss. }
      s. i. des.
      exploit Thread.rtc_tau_step_future; try exact STEPS'; eauto; s.
      { inv WF. eapply Memory.future_closed_timemap; eauto. }
      i. des.
      exploit Thread.step_future; try exact STEP'; eauto. s. i. des.
      hexploit Thread.rtc_tau_step_no_half; try exact STEPS'; eauto. s. i. des.
      hexploit Thread.step_no_half; try exact STEP'; eauto. s. i. des.
      exploit LowerMemory.no_half_concrete_none_concrete_exact_lower_memory;
        try exact CONCRETE; try exact CONCRETE1; try exact NOHALF; try apply WF3; eauto. i.
      exploit (@LowerMemory.thread_rtc_tau_step lang (Thread.mk lang st3 lc3 sc3 mem2'0));
        try exact STEPS0; try refl; eauto; s.
      { inv WF0. econs; eauto. eapply TView.future_closed; eauto. }
      { eapply Memory.future_closed_timemap; try exact SC0; eauto. }
      i. des.
      eapply rtc_implies in STEPS'; [|by apply tau_union].
      exploit rtc_n1; eauto; i.
      { econs. econs. eauto. }
      eapply rtc_implies in STEPS_SRC; [|by apply tau_union].
      rewrite STEPS_SRC in x1.
      inv LC2. rewrite PROMISES in PROMISES0.
      exploit steps_pf_steps; try exact x1; eauto; ss; try by inv WF.
      { ii. rewrite PROMISES0, Memory.bot_get in *. congr. }
      { inv WF. eapply Memory.future_closed_timemap; eauto. }
      i. des.
      exploit rtc_union_step_nonpf_bot; eauto. i. subst.
      exploit rtc_thread_step_sem; try exact STEPS1; eauto; ss; try by inv WF.
      { eapply concrete_none_sem_memory; try exact CONCRETE0; eauto. by inv WF. }
      { inv WF. eapply Memory.future_closed_timemap; eauto. }
      i. des.
      exploit Thread.rtc_all_step_future; try exact STEPS0; eauto. s. i. des.
      eapply concrete_exact_sem_memory_inv; try exact CONCRETE2; eauto.
      eapply lower_memory_sem_memory; try exact x0; eauto.
      eapply future_sem_memory; eauto.
  Qed.

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
           (CONS: Configuration.consistent c1)
           (SEM: sem c1)
           (STEPS: rtc Configuration_step_evt c1 c2),
            sem c2).
    { i. eapply H; eauto.
      - apply Configuration.init_wf.
      - apply Configuration.init_consistent.
      - apply init_sem; auto.
    }
    i. revert WF SEM. induction STEPS0; ss. i.
    inv H. exploit Configuration.step_future; eauto. i. des.
    apply IHSTEPS0; ss. eapply configuration_step_sem; try exact STEP; eauto.
  Qed.
End Invariant.
