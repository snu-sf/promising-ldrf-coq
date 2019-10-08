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
      <<STEP_SRC: Thread.opt_promise_step e_src e1_src e2_src>> /\
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

  Lemma sim_thread_other_step
        l e1_src
        pf e_tgt e1_tgt e2_tgt
        (SIM1: sim_thread_other l e1_src e1_tgt)
        (WF1_SRC: Local.wf e1_src.(Thread.local) e1_src.(Thread.memory))
        (WF1_TGT: Local.wf e1_tgt.(Thread.local) e1_tgt.(Thread.memory))
        (SC1_SRC: Memory.closed_timemap e1_src.(Thread.sc) e1_src.(Thread.memory))
        (SC1_TGT: Memory.closed_timemap e1_tgt.(Thread.sc) e1_tgt.(Thread.memory))
        (CLOSED1_SRC: Memory.closed e1_src.(Thread.memory))
        (CLOSED1_TGT: Memory.closed e1_tgt.(Thread.memory))
        (STEP_TGT: Thread.step pf e_tgt e1_tgt e2_tgt):
    exists e_src e1_src e2_src,
      <<STEP_SRC: Thread.opt_step e_src e1_src e2_src>> /\
      <<EVENT: ThreadEvent.get_machine_event e_src = ThreadEvent.get_machine_event e_tgt>> /\
      <<SIM2: sim_thread_other l e2_src e2_tgt>> /\
      <<MEMLOC: forall to, Memory.get l to e1_src.(Thread.memory) = Memory.get l to e2_src.(Thread.memory)>>.
  Proof.
    inv STEP_TGT.
    { (* promise step *)
      exploit sim_thread_promise_step; eauto;
        try apply WF1_SRC; try apply WF1_TGT.
      i. des.
      esplits; [|M| |]; eauto.
      - inv STEP_SRC.
        + econs 1.
        + econs 2. econs 1; eauto.
      - inv STEP. ss. inv STEP_SRC; ss. inv STEP. ss.
    }
    (* program step *)
    inv STEP; ss.
    hexploit loc_free_step_is_accessing_loc; eauto; i.
    { inv SIM1. ss. subst. eauto. }
    exploit program_step; try exact LOCAL; try eapply SIM1; eauto. i. des.
    esplits.
    - econs 2. econs 2. econs; try exact STEP_SRC.
      rewrite EVENT2. eauto.
    - ss.
    - econs; eauto.
      + s. eapply step_loc_free; eauto.
        inv SIM1. ss. subst. ss.
      + s. i. inv SIM1.
        erewrite <- program_step_eq_promises; eauto.
        erewrite ThreadEvent.eq_program_event_eq_loc; eauto.
    - s. i.
      eapply program_step_eq_mem; eauto.
      erewrite ThreadEvent.eq_program_event_eq_loc; eauto.
  Qed.
End SimThreadOther.
