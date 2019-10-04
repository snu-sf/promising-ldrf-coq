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

Require Import Syntax.
Require Import Semantics.

Require Import PromiseConsistent.

Require Import FulfillStep.

Require Import Promotion.
Require Import SimCommon.

Set Implicit Arguments.


Inductive opt_lang_step: forall (e:ProgramEvent.t) (st1 st2:State.t), Prop :=
| opt_lang_step_none
    st:
    opt_lang_step ProgramEvent.silent st st
| opt_lang_step_some
    e st1 st2
    (STEP: lang.(Language.step) e st1 st2):
    opt_lang_step e st1 st2
.

Inductive opt_promise_step: forall (e:ThreadEvent.t) (e1 e2:Thread.t lang), Prop :=
| opt_promise_step_none
    e1:
    opt_promise_step ThreadEvent.silent e1 e1
| opt_promise_step_some
    pf e e1 e2
    (STEP: Thread.promise_step pf e e1 e2):
    opt_promise_step e e1 e2
.

Inductive opt_program_step: forall (e:ThreadEvent.t) (e1 e2:Thread.t lang), Prop :=
| opt_program_step_none
    e1:
    opt_program_step ThreadEvent.silent e1 e1
| opt_program_step_some
    e e1 e2
    (STEP: Thread.program_step e e1 e2):
    opt_program_step e e1 e2
.


Inductive sim_thread_other (l: Loc.t) (e_src e_tgt: Thread.t lang): Prop :=
| sim_thread_other_intro
    (LOCFREE: loc_free_stmts l e_src.(Thread.state).(State.stmts))
    (STATE: e_src.(Thread.state) = e_tgt.(Thread.state))
    (LOCAL: sim_local l e_src.(Thread.local) e_tgt.(Thread.local))
    (SC: sim_timemap l e_src.(Thread.sc) e_tgt.(Thread.sc))
    (MEMORY: sim_memory l e_src.(Thread.memory) e_tgt.(Thread.memory))
    (PROMISES: forall to, Memory.get l to e_src.(Thread.local).(Local.promises) = None)
    (FULFILLABLE: fulfillable l e_src.(Thread.local).(Local.tview) e_src.(Thread.memory)
                              e_src.(Thread.local).(Local.promises))
.
Hint Constructors sim_thread_other.


Lemma promise_eq_promises
      l
      promises1 mem1 loc from to msg promises2 mem2 kind
      (PROMISE: Memory.promise promises1 mem1 loc from to msg promises2 mem2 kind)
      (LOC: loc <> l):
  forall to, Memory.get l to promises1 = Memory.get l to promises2.
Proof.
  i. inv PROMISE.
  - erewrite (@Memory.add_o promises2); eauto. condtac; ss. des. subst. ss.
  - erewrite (@Memory.split_o promises2); eauto. repeat condtac; ss.
    { des. subst. ss. }
    { des; subst; ss. }
  - erewrite (@Memory.lower_o promises2); eauto. condtac; ss. des. subst. ss.
  - erewrite (@Memory.remove_o promises2); eauto. condtac; ss. des. subst. ss.
Qed.

Lemma promise_eq_mem
      l
      promises1 mem1 loc from to msg promises2 mem2 kind
      (PROMISE: Memory.promise promises1 mem1 loc from to msg promises2 mem2 kind)
      (LOC: loc <> l):
  forall to, Memory.get l to mem1 = Memory.get l to mem2.
Proof.
  i. inv PROMISE.
  - erewrite (@Memory.add_o mem2); eauto. condtac; ss. des. subst. ss.
  - erewrite (@Memory.split_o mem2); eauto. repeat condtac; ss.
    { des. subst. ss. }
    { des; subst; ss. }
  - erewrite (@Memory.lower_o mem2); eauto. condtac; ss. des. subst. ss.
  - erewrite (@Memory.remove_o mem2); eauto. condtac; ss. des. subst. ss.
Qed.


Lemma promise_step
      l
      lc1_src mem1_src
      lc1_tgt mem1_tgt loc from to msg_tgt lc2_tgt mem2_tgt kind_tgt
      (LC1: sim_local l lc1_src lc1_tgt)
      (MEM1: sim_memory l mem1_src mem1_tgt)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
      (CLOSED1_SRC: Memory.closed mem1_src)
      (FULFILLABLE1: fulfillable l lc1_src.(Local.tview) mem1_src lc1_src.(Local.promises))
      (LOC: loc <> l)
      (STEP_TGT: Local.promise_step lc1_tgt mem1_tgt loc from to msg_tgt lc2_tgt mem2_tgt kind_tgt):
  exists msg_src lc2_src mem2_src kind_src,
    <<STEP_SRC: Local.promise_step lc1_src mem1_src loc from to msg_src lc2_src mem2_src kind_src>> /\
    <<LC2: sim_local l lc2_src lc2_tgt>> /\
    <<MEM2: sim_memory l mem2_src mem2_tgt>> /\
    <<FULFILLABLE2: fulfillable l lc2_src.(Local.tview) mem2_src lc2_src.(Local.promises)>>.
Proof.
  inv STEP_TGT.
  exploit sim_memory_promise; try exact PROMISE; try apply LC1;
    try apply WF1_SRC; try apply WF1_TGT; eauto.
  i. des.
  esplits.
  - econs; eauto.
    eapply get_message_src_closed; eauto; try apply WF1_SRC. i.
    exploit Memory.promise_op; try exact PROMISE_SRC. i.
    eapply Memory.op_closed_view; eauto.
  - inv LC1. econs; eauto.
  - ss.
  - ss.
Qed.

Lemma sim_thread_other_promise_step
      l e1_src
      pf e_tgt e1_tgt e2_tgt
      (SIM1: sim_thread_other l e1_src e1_tgt)
      (WF1_SRC: Local.wf e1_src.(Thread.local) e1_src.(Thread.memory))
      (WF1_TGT: Local.wf e1_tgt.(Thread.local) e1_tgt.(Thread.memory))
      (CLOSED1_SRC: Memory.closed e1_src.(Thread.memory))
      (STEP_TGT: Thread.promise_step pf e_tgt e1_tgt e2_tgt):
  exists e_src e2_src,
    <<STEP_SRC: opt_promise_step e_src e1_src e2_src>> /\
    <<SIM2: sim_thread_other l e2_src e2_tgt>> /\
    <<MEMLOC: forall to, Memory.get l to e1_src.(Thread.memory) = Memory.get l to e2_src.(Thread.memory)>>.
Proof.
  inversion STEP_TGT. subst.
  destruct (Loc.eq_dec loc l).
  { subst. inv LOCAL; ss.
    esplits; [econs 1| |]; eauto.
    inv SIM1. ss.
    exploit sim_memory_promise_loc; try exact PROMISE; try apply LOCAL; eauto. i. des.
    econs; ss; eauto.
    econs; ss; eauto; try apply LOCAL.
  }
  exploit promise_step; try exact LOCAL; try apply SIM1;
    try apply WF1_SRC; try apply WF1_TGT; eauto.
  i. des.
  destruct e1_src. ss.
  esplits.
  - econs 2. econs; eauto.
  - inv SIM1. ss. econs; eauto; ss.
    i. inv STEP_SRC.
    erewrite <- promise_eq_promises; try exact PROMISE; eauto.
  - i. s. inv STEP_SRC.
    erewrite promise_eq_mem; try exact PROMISE; eauto.
Qed.

Lemma fold_andb_impl
      l (a b: bool)
      (FOLD: List.fold_left andb l a)
      (IMPL: a -> b):
  List.fold_left andb l b.
Proof.
  revert a b IMPL FOLD.
  induction l; i; ss; eauto.
  eapply IHl; try exact FOLD. i.
  destruct a0, b, a; ss.
  apply IMPL. ss.
Qed.

Lemma step_loc_free
      l e st1 st2
      (LOCFREE: loc_free_stmts l st1.(State.stmts))
      (STEP: State.step e st1 st2):
  loc_free_stmts l st2.(State.stmts).
Proof.
Admitted.

Lemma sim_thread_other_step
      l e1_src
      pf e_tgt e1_tgt e3_tgt
      (SIM1: sim_thread_other l e1_src e1_tgt)
      (WF1_SRC: Local.wf e1_src.(Thread.local) e1_src.(Thread.memory))
      (WF1_TGT: Local.wf e1_tgt.(Thread.local) e1_tgt.(Thread.memory))
      (CLOSED1_SRC: Memory.closed e1_src.(Thread.memory))
      (STEP_TGT: Thread.step pf e_tgt e1_tgt e3_tgt):
  exists e_src e1_src e2_src e3_src,
    <<STEPS_SRC: rtc (@Thread.tau_step lang) e1_src e2_src>> /\
    <<STEP_SRC: Thread.opt_step e_src e2_src e3_src>> /\
    <<SIM2: sim_thread_other l e3_src e3_tgt>> /\
    <<EVENT: ThreadEvent.get_machine_event e_src = ThreadEvent.get_machine_event e_tgt>> /\
    <<MEMLOC: forall to, Memory.get l to e1_src.(Thread.memory) = Memory.get l to e3_src.(Thread.memory)>>.
Proof.
  inv STEP_TGT.
  { (* promise step *)
    exploit sim_thread_other_promise_step; eauto;
      try apply WF1_SRC; try apply WF1_TGT.
    i. des.
    esplits; [| | |M|]; eauto.
    - inv STEP_SRC.
      + econs 1; eauto.
      + econs 2; eauto. econs 1; eauto.
    - inv STEP. ss. inv STEP_SRC; ss. inv STEP. ss.
  }
  (* program step *)
  inv STEP; ss. inv LOCAL; ss.
  - inv SIM1. ss. subst. esplits.
    + refl.
    + econs 2. econs 2. econs 1; eauto. s. eapply STATE.
    + econs; s; eauto.
      eapply step_loc_free; eauto.
    + ss.
    + ss.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.
