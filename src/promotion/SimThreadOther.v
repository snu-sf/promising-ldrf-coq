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


Module SimThreadOther.
  Import SimCommon.

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

  Lemma sim_thread_promise_step
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
      exploit promise_loc; try exact PROMISE; try apply LOCAL; eauto. i. des.
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

  Lemma Forall_app
        A
        (P: A -> Prop)
        (l1 l2: list A)
        (FORALL1: List.Forall P l1)
        (FORALL2: List.Forall P l2):
    List.Forall P (l1 ++ l2).
  Proof.
    induction l1; ss.
    inv FORALL1. eauto.
  Qed.

  Lemma Forall_app_inv
        A
        (P: A -> Prop)
        (l1 l2: list A)
        (FORALL: List.Forall P (l1 ++ l2)):
    <<FORALL1: List.Forall P l1>> /\
               <<FORALL2: List.Forall P l2>>.
  Proof.
    induction l1; split; ss.
    - inv FORALL. exploit IHl1; eauto. i. des. eauto.
    - inv FORALL. exploit IHl1; eauto. i. des. ss.
  Qed.

  Lemma step_loc_free
        l e st1 st2
        (LOCFREE: loc_free_stmts l st1.(State.stmts))
        (STEP: State.step e st1 st2):
    loc_free_stmts l st2.(State.stmts).
  Proof.
    inv STEP; ss.
    - inv LOCFREE. ss.
    - inv LOCFREE. condtac.
      + inv H1. eapply Forall_app; eauto.
      + inv H1. eapply Forall_app; eauto.
    - inv LOCFREE. inv H1.
      eapply Forall_app; eauto.
  Qed.

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
      exploit sim_thread_promise_step; eauto;
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
      + econs 2. econs 2.
        econs; eauto. s. eapply STATE.
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
End SimThreadOther.
