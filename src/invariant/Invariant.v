Require Import Omega.
Require Import RelationClasses.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Loc.
From PromisingLib Require Import Language.

Require Import Event.
Require Import Time.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.

Require Import PromiseConsistent.
Require Import ReorderPromises.
Require Import FutureCertify.

Set Implicit Arguments.


Definition ThreadsProp :=
  forall (tid:Ident.t)
    (lang:language)
    (st:lang.(Language.state)),
    Prop.

Definition MemoryProp :=
  forall (assign: LocFun.t Const.t),
    Prop.


Module Logic.
  Section Logic.
    Variable
      (S: ThreadsProp)
      (J: MemoryProp)
      (program: Threads.syntax).

    Structure t: Type := mk {
      INIT:
        <<ST_INIT:
          forall tid lang syn
            (FIND: IdentMap.find tid program = Some (existT _ lang syn)),
            S tid lang (lang.(Language.init) syn)>> /\
        <<ASSIGN_INIT: J (LocFun.init 0)>>;
      SILENT:
        forall tid lang st1 st2
          (ST1: S tid lang st1)
          (STEP: lang.(Language.step) ProgramEvent.silent st1 st2),
          S tid lang st2;
      READ:
        forall tid lang st1 st2
          loc val ord
          assign
          (ST1: S tid lang st1)
          (ASSIGN1: J assign /\ LocFun.find loc assign = val)
          (STEP: lang.(Language.step) (ProgramEvent.read loc val ord) st1 st2),
          S tid lang st2;
      WRITE:
        forall tid lang st1 st2
          loc val ord
          (ST1: S tid lang st1)
          (STEP: lang.(Language.step) (ProgramEvent.write loc val ord) st1 st2),
          <<ST2: S tid lang st2>> /\
          <<ASSIGN2: forall assign, J assign -> J (LocFun.add loc val assign)>>;
      UPDATE:
        forall tid lang st1 st2
          loc valr valw ordr ordw
          assign
          (ST1: S tid lang st1)
          (ASSIGN1: J assign /\ LocFun.find loc assign = valr)
          (STEP: lang.(Language.step) (ProgramEvent.update loc valr valw ordr ordw) st1 st2),
          <<ST2: S tid lang st2>> /\
          <<ASSIGN2: forall assign, J assign -> J (LocFun.add loc valw assign)>>;
      FENCE:
        forall tid lang st1 st2
          ordr ordw
          (ST1: S tid lang st1)
          (STEP: lang.(Language.step) (ProgramEvent.fence ordr ordw) st1 st2),
          S tid lang st2;
      SYSCALL:
        forall tid lang st1 st2
          e
          (ST1: S tid lang st1)
          (STEP: lang.(Language.step) (ProgramEvent.syscall e) st1 st2),
          S tid lang st2;
      FAILURE:
        forall tid lang st1 st2
          (ST1: S tid lang st1)
          (STEP: lang.(Language.step) ProgramEvent.failure st1 st2),
          <<ST2: forall tid lang st, S tid lang st>> /\
          <<ASSIGN2: forall assign, J assign>>;
    }.
  End Logic.
End Logic.


Section Invariant.
  Variable
    (S:ThreadsProp)
    (J:MemoryProp)
    (program: IdentMap.t {lang:language & lang.(Language.syntax)}).

  Context `{LOGIC: Logic.t S J program}.

  Definition sem_threads (ths:Threads.t): Prop :=
    forall tid lang st lc
      (FIND: IdentMap.find tid ths = Some (existT _ lang st, lc)),
      S tid lang st.

  Definition memory_assign (m:Memory.t) (assign:Loc.t -> Const.t) :=
    forall loc,
    exists from to released,
      Memory.get loc to m =
      Some (from, Message.concrete (LocFun.find loc assign) released).

  Definition sem_memory (m:Memory.t): Prop :=
    memory_assign m <1= J.

  Inductive sem (c:Configuration.t): Prop :=
  | sem_configuration_intro
      (TH: sem_threads c.(Configuration.threads))
      (MEM: sem_memory c.(Configuration.memory))
  .


  (* sem_memory_step *)

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
      + rewrite LocFun.add_spec_neq, LocFun.init_spec; eauto.
        inv CLOSED. specialize (INHABITED loc0).
        esplits; eauto.
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
      inv STEP. inv WRITE. inv PROMISE; ss.
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
    inv STEP. inv WRITE. inv PROMISE; ss.
    - erewrite Memory.add_o; eauto. condtac; ss.
      + i. des. inv SEM. congr.
      + i. esplits; eauto.
    - erewrite Memory.split_o; eauto. condtac; ss.
      { i. des. inv SEM. congr. }
      condtac; ss.
      { guardH o. i. des. inv SEM. ss.
        exploit Memory.split_get0; try exact MEM; eauto. i. des.
        clarify. esplits; eauto.
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
        (CLOSED1: Memory.closed mem1)
        (STEP: Thread.step true e (Thread.mk lang st1 lc1 sc1 mem1) (Thread.mk lang st2 lc2 sc2 mem2)):
    <<TH2: S tid lang st2>> /\
    <<MEM2: sem_memory mem2>>.
  Proof.
    inv STEP.
    { inv STEP0. symmetry in PF.
      destruct kind; ss.
      - destruct msg1; ss. destruct msg; ss. destruct released0; ss.
        splits; ss. inv LOCAL. inv PROMISE. des. inv RESERVE.
        ii. apply MEM1. ii. specialize (PR loc0). des.
        revert PR. erewrite Memory.lower_o; eauto. condtac; eauto.
        ss. i. des. inv PR. exploit Memory.lower_get0; eauto. i. des.
        inv MSG_LE. eauto.
      - inv LOCAL. inv PROMISE. splits; ss. ii.
        apply MEM1. ii. specialize (PR loc0). des.
        revert PR. erewrite Memory.remove_o; eauto. condtac; ss; eauto.
    }
    inv LOGIC. inv STEP0. inv LOCAL.
    - esplits; eauto.
    - exploit sem_memory_read_step; eauto. i. des.
      exploit READ; eauto.
    - exploit WRITE; eauto. i. des.
      esplits; eauto. ii.
      destruct (Const.eq_dec (LocFun.find loc x0) val).
      { subst. hexploit sem_memory_write_step_eq; try apply CLOSED1; eauto. i. des.
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
    - exploit FAILURE; eauto. i. des. eauto.
  Qed.

  Lemma rtc_thread_step_sem
        tid lang
        th1 th2
        (TH1: S tid lang th1.(Thread.state))
        (MEM1: sem_memory th1.(Thread.memory))
        (WF1: Local.wf th1.(Thread.local) th1.(Thread.memory))
        (SC1: Memory.closed_timemap th1.(Thread.sc) th1.(Thread.memory))
        (CLOSED1: Memory.closed th1.(Thread.memory))
        (STEPS: rtc (union (Thread.step true)) th1 th2):
    <<TH2: S tid lang th2.(Thread.state)>> /\
    <<MEM2: sem_memory th2.(Thread.memory)>>.
  Proof.
    move STEPS after TH1. revert_until STEPS. induction STEPS; ss.
    i. inv H.
    exploit Thread.step_future; eauto. i. des.
    destruct x, y. ss.
    exploit thread_step_sem; eauto. i. des.
    eapply IHSTEPS; eauto.
  Qed.

  Lemma rtc_thread_step_sem_thread
        tid lang
        th1 th2
        (TH1: S tid lang th1.(Thread.state))
        (MEM1: sem_memory th1.(Thread.memory))
        (WF1: Local.wf th1.(Thread.local) th1.(Thread.memory))
        (SC1: Memory.closed_timemap th1.(Thread.sc) th1.(Thread.memory))
        (CLOSED1: Memory.closed th1.(Thread.memory))
        (STEPS: rtc (@Thread.all_step lang) th1 th2)
        (CONS: Local.promise_consistent th2.(Thread.local)):
    <<TH2: S tid lang th2.(Thread.state)>>.
  Proof.
    exploit steps_pf_steps; eauto. i. des.
    exploit Thread.rtc_all_step_future; try eapply rtc_implies; try exact STEPS1; eauto.
    { i. inv H. econs. econs. eauto. }
    i. des.
    exploit Thread.rtc_step_nonpf_future; eauto. i. des.
    rewrite <- STATE.
    exploit rtc_thread_step_sem; eauto. i. des. ss.
  Qed.


  (* future_sem_memory *)

  Lemma future_sem_memory
        m1 m2
        (FUTURE: Memory.future m1 m2)
        (SEM: sem_memory m2):
    sem_memory m1.
  Proof.
    ii. apply SEM. ii. specialize (PR loc). des.
    exploit Memory.future_get1; eauto. i. des.
    inv MSG_LE. esplits; eauto.
  Qed.

  Lemma future_weak_sem_memory
        m1 m2
        (FUTURE: Memory.future_weak m1 m2)
        (SEM: sem_memory m2):
    sem_memory m1.
  Proof.
    ii. apply SEM. ii. specialize (PR loc). des.
    exploit Memory.future_weak_get1; eauto. i. des.
    inv MSG_LE. esplits; eauto.
  Qed.


  (* configuration *)

  Lemma consistent_sem
        tid lang
        pf e th1 th2 th3
        (TH1: S tid lang th1.(Thread.state))
        (MEM1: sem_memory th1.(Thread.memory))
        (WF1: Local.wf th1.(Thread.local) th1.(Thread.memory))
        (SC1: Memory.closed_timemap th1.(Thread.sc) th1.(Thread.memory))
        (CLOSED1: Memory.closed th1.(Thread.memory))
        (STEPS: rtc (@Thread.tau_step lang) th1 th2)
        (STEP: Thread.step pf e th2 th3)
        (CONSISTENT: Thread.consistent th3):
    <<TH3: S tid lang th3.(Thread.state)>> /\
    <<MEM3: sem_memory th3.(Thread.memory)>>.
  Proof.
    exploit Thread.rtc_tau_step_future; eauto. s. i. des.
    exploit Thread.step_future; eauto. s. i. des.
    split.
    { hexploit consistent_promise_consistent; eauto. intro CONS.
      eapply rtc_thread_step_sem_thread; eauto.
      eapply rtc_n1; try eapply rtc_implies; try exact STEPS.
      - i. inv H. econs. eauto.
      - econs. econs. eauto.
    }
    hexploit FutureCertify.future_certify_exists; try exact CONSISTENT; eauto. i.
    destruct th3 as [st3 lc3 sc3 mem3]. ss.
    exploit H; try refl; ss. i. des.
    - unfold Thread.steps_failure in *. des.
      eapply rtc_implies in STEPS; [|apply tau_union].
      eapply rtc_implies in STEPS0; [|apply tau_union].
      exploit rtc_n1; try exact STEPS; i.
      { econs. econs. eauto. }
      rewrite STEPS0 in x0.
      exploit steps_failure_pf_steps_failure; try exact x0; eauto. i. des.
      exploit rtc_thread_step_sem; try exact STEPS'; eauto. i. des.
      inv FAILURE'; inv STEP0. ss.
      inv LOGIC. exploit FAILURE; try exact STATE0; eauto. i. des.
      ii. ss.
    - exploit Thread.rtc_tau_step_future; try exact STEPS0; eauto. s. i. des.
      eapply rtc_implies in STEPS; [|apply tau_union].
      eapply rtc_implies in STEPS0; [|apply tau_union].
      exploit rtc_n1; try exact STEPS; i.
      { econs. econs. eauto. }
      rewrite STEPS0 in x0.
      exploit steps_pf_steps; try exact x0; eauto.
      { ii. rewrite PROMISES in *. rewrite Memory.bot_get in *. ss. }
      i. des.
      exploit rtc_union_step_nonpf_bot; try exact STEPS2; eauto. i. subst.
      exploit rtc_thread_step_sem; try exact STEPS1; eauto. i. des.
      eapply future_sem_memory; eauto.
  Qed.

  Lemma configuration_step_sem
        e tid c1 c2
        (WF: Configuration.wf c1)
        (SEM: sem c1)
        (STEP: Configuration.step e tid c1 c2):
    sem c2.
  Proof.
    inv STEP.
    - inv SEM. exploit TH; eauto. i.
      inv WF. inv WF0. exploit THREADS; eauto. i.
      clear DISJOINT THREADS TID.
      exploit steps_failure_pf_steps_failure; try eapply rtc_implies; try exact STEPS; eauto.
      { i. inv H. econs. eauto. }
      i. des.
      exploit rtc_thread_step_sem; try exact STEPS'; eauto. i. des.
      inv FAILURE'; inv STEP.
      inv LOGIC. exploit FAILURE; try exact STATE0; eauto. i. des.
      econs; ii; eauto.
    - inv SEM. exploit TH; eauto. i.
      inv WF. inv WF0. exploit THREADS; eauto. i.
      exploit consistent_sem; try exact STEPS; eauto. s. i. des.
      econs; eauto. ss. ii. revert FIND.
      rewrite IdentMap.gsspec. condtac; ss; [|by apply TH].
      i. subst. inv FIND. apply inj_pair2 in H1. subst. ss.
  Qed.

  Inductive Configuration_step_evt (c1 c2:Configuration.t): Prop :=
  | Configuration_step_evt_intro
      e tid
      (STEP: Configuration.step e tid c1 c2)
  .

  Lemma init_sem: sem (Configuration.init program).
  Proof.
    inv LOGIC. des. econs.
    - ii. unfold Configuration.init in FIND. ss.
      unfold Threads.init in FIND. rewrite IdentMap.Facts.map_o in FIND.
      destruct (@UsualFMapPositive.UsualPositiveMap'.find
                  (@sigT _ (@Language.syntax ProgramEvent.t)) tid program) eqn:X; inv FIND.
      apply inj_pair2 in H1. subst. destruct s. ss.
      eapply ST_INIT; eauto.
    - ii. cut (x0 = LocFun.init 0); [by i; subst|].
      apply LocFun.ext. i. rewrite LocFun.init_spec.
      specialize (PR i). des. ss.
      unfold Memory.get, Memory.init in PR. unfold Cell.get, Cell.init in PR. ss.
      apply DOMap.singleton_find_inv in PR. des. inv PR0. auto.
  Qed.

  Lemma sound
        c
        (STEPS: rtc Configuration.all_step (Configuration.init program) c):
    sem c.
  Proof.
    cut (forall c1 c2
           (WF: Configuration.wf c1)
           (SEM: sem c1)
           (STEPS: rtc Configuration.all_step c1 c2),
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
