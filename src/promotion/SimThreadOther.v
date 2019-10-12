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

  Inductive sim_thread (l: Loc.t) (e_src e_tgt: Thread.t lang): Prop :=
  | sim_thread_intro
      (LOCFREE: loc_free_stmts l e_src.(Thread.state).(State.stmts))
      (STATE: e_src.(Thread.state) = e_tgt.(Thread.state))
      (LOCAL: sim_local l e_src.(Thread.local) e_tgt.(Thread.local))
      (SC: sim_timemap l e_src.(Thread.sc) e_tgt.(Thread.sc))
      (MEMORY: sim_memory l e_src.(Thread.memory) e_tgt.(Thread.memory))
      (PROMISES: forall to, Memory.get l to e_src.(Thread.local).(Local.promises) = None)
      (FULFILLABLE: fulfillable l e_src.(Thread.local).(Local.tview) e_src.(Thread.memory)
                                  e_src.(Thread.local).(Local.promises))
  .
  Hint Constructors sim_thread.

  Lemma sim_thread_promise_step
        l e1_src
        pf e_tgt e1_tgt e2_tgt
        (SIM1: sim_thread l e1_src e1_tgt)
        (WF1_SRC: Local.wf e1_src.(Thread.local) e1_src.(Thread.memory))
        (WF1_TGT: Local.wf e1_tgt.(Thread.local) e1_tgt.(Thread.memory))
        (CLOSED1_SRC: Memory.closed e1_src.(Thread.memory))
        (STEP_TGT: Thread.promise_step pf e_tgt e1_tgt e2_tgt):
    exists e_src e2_src,
      <<STEP_SRC: Thread.opt_promise_step e_src e1_src e2_src>> /\
      <<SIM2: sim_thread l e2_src e2_tgt>> /\
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

  Lemma sim_thread_program_step
        l e1_src
        e_tgt e1_tgt e2_tgt
        (SIM1: sim_thread l e1_src e1_tgt)
        (WF1_SRC: Local.wf e1_src.(Thread.local) e1_src.(Thread.memory))
        (WF1_TGT: Local.wf e1_tgt.(Thread.local) e1_tgt.(Thread.memory))
        (SC1_SRC: Memory.closed_timemap e1_src.(Thread.sc) e1_src.(Thread.memory))
        (SC1_TGT: Memory.closed_timemap e1_tgt.(Thread.sc) e1_tgt.(Thread.memory))
        (CLOSED1_SRC: Memory.closed e1_src.(Thread.memory))
        (CLOSED1_TGT: Memory.closed e1_tgt.(Thread.memory))
        (STEP_TGT: Thread.program_step e_tgt e1_tgt e2_tgt):
    exists e_src e2_src,
      <<STEP_SRC: Thread.opt_program_step e_src e1_src e2_src>> /\
      <<EVENT: ThreadEvent.get_machine_event e_src = ThreadEvent.get_machine_event e_tgt>> /\
      <<SIM2: sim_thread l e2_src e2_tgt>> /\
      <<MEMLOC: forall to, Memory.get l to e1_src.(Thread.memory) = Memory.get l to e2_src.(Thread.memory)>>.
  Proof.
    inv STEP_TGT; ss.
    hexploit loc_free_step_is_accessing_loc; eauto; i.
    { inv SIM1. ss. subst. eauto. }
    exploit program_step; try exact LOCAL; try eapply SIM1; eauto. i. des.
    destruct e1_src. ss.
    esplits.
    - econs 2. econs; try exact STEP_SRC.
      inv SIM1. inv STATE0. ss.
      rewrite H0. rewrite EVENT2. eauto.
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

  Lemma sim_thread_step
        l e1_src
        pf e_tgt e1_tgt e2_tgt
        (SIM1: sim_thread l e1_src e1_tgt)
        (WF1_SRC: Local.wf e1_src.(Thread.local) e1_src.(Thread.memory))
        (WF1_TGT: Local.wf e1_tgt.(Thread.local) e1_tgt.(Thread.memory))
        (SC1_SRC: Memory.closed_timemap e1_src.(Thread.sc) e1_src.(Thread.memory))
        (SC1_TGT: Memory.closed_timemap e1_tgt.(Thread.sc) e1_tgt.(Thread.memory))
        (CLOSED1_SRC: Memory.closed e1_src.(Thread.memory))
        (CLOSED1_TGT: Memory.closed e1_tgt.(Thread.memory))
        (STEP_TGT: Thread.step pf e_tgt e1_tgt e2_tgt):
    exists e_src e2_src,
      <<STEP_SRC: Thread.opt_step e_src e1_src e2_src>> /\
      <<EVENT: ThreadEvent.get_machine_event e_src = ThreadEvent.get_machine_event e_tgt>> /\
      <<SIM2: sim_thread l e2_src e2_tgt>> /\
      <<MEMLOC: forall to, Memory.get l to e1_src.(Thread.memory) = Memory.get l to e2_src.(Thread.memory)>>.
  Proof.
    inv STEP_TGT.
    - exploit sim_thread_promise_step; eauto. i. des.
      esplits.
      + inv STEP_SRC.
        * econs 1.
        * econs 2. econs 1; eauto.
      + inv STEP. ss. inv STEP_SRC; ss. inv STEP. ss.
      + ss.
      + ss.
    - exploit sim_thread_program_step; eauto. i. des.
      esplits.
      + inv STEP_SRC.
        * econs 1.
        * econs 2. econs 2; eauto.
      + ss.
      + ss.
      + ss.
  Qed.

  Lemma sim_thread_opt_step
        l e1_src
        e_tgt e1_tgt e2_tgt
        (SIM1: sim_thread l e1_src e1_tgt)
        (WF1_SRC: Local.wf e1_src.(Thread.local) e1_src.(Thread.memory))
        (WF1_TGT: Local.wf e1_tgt.(Thread.local) e1_tgt.(Thread.memory))
        (SC1_SRC: Memory.closed_timemap e1_src.(Thread.sc) e1_src.(Thread.memory))
        (SC1_TGT: Memory.closed_timemap e1_tgt.(Thread.sc) e1_tgt.(Thread.memory))
        (CLOSED1_SRC: Memory.closed e1_src.(Thread.memory))
        (CLOSED1_TGT: Memory.closed e1_tgt.(Thread.memory))
        (STEP_TGT: Thread.opt_step e_tgt e1_tgt e2_tgt):
    exists e_src e2_src,
      <<STEP_SRC: Thread.opt_step e_src e1_src e2_src>> /\
      <<EVENT: ThreadEvent.get_machine_event e_src = ThreadEvent.get_machine_event e_tgt>> /\
      <<SIM2: sim_thread l e2_src e2_tgt>> /\
      <<MEMLOC: forall to, Memory.get l to e1_src.(Thread.memory) = Memory.get l to e2_src.(Thread.memory)>>.
  Proof.
    inv STEP_TGT.
    - esplits; eauto. econs 1.
    - exploit sim_thread_step; eauto.
  Qed.

  Lemma sim_thread_rtc_tau_step
        l e1_src
        e1_tgt e2_tgt
        (SIM1: sim_thread l e1_src e1_tgt)
        (WF1_SRC: Local.wf e1_src.(Thread.local) e1_src.(Thread.memory))
        (WF1_TGT: Local.wf e1_tgt.(Thread.local) e1_tgt.(Thread.memory))
        (SC1_SRC: Memory.closed_timemap e1_src.(Thread.sc) e1_src.(Thread.memory))
        (SC1_TGT: Memory.closed_timemap e1_tgt.(Thread.sc) e1_tgt.(Thread.memory))
        (CLOSED1_SRC: Memory.closed e1_src.(Thread.memory))
        (CLOSED1_TGT: Memory.closed e1_tgt.(Thread.memory))
        (STEPS_TGT: rtc (@Thread.tau_step lang) e1_tgt e2_tgt):
    exists e2_src,
      <<STEPS_SRC: rtc (@Thread.tau_step lang) e1_src e2_src>> /\
      <<SIM2: sim_thread l e2_src e2_tgt>> /\
      <<MEMLOC: forall to, Memory.get l to e1_src.(Thread.memory) = Memory.get l to e2_src.(Thread.memory)>>.
  Proof.
    revert e1_src SIM1 WF1_SRC SC1_SRC CLOSED1_SRC.
    induction STEPS_TGT; i.
    - esplits; eauto.
    - inv H. inv TSTEP.
      exploit sim_thread_step; eauto. i. des.
      exploit Thread.step_future; try exact STEP; eauto. i. des.
      exploit Thread.opt_step_future; try exact STEP_SRC; eauto. i. des.
      exploit IHSTEPS_TGT; eauto. i. des.
      inv STEP_SRC.
      + esplits; eauto.
      + esplits; [M|..]; eauto.
        * econs; [|eauto].
          econs; [econs; eauto|]. rewrite <- EVENT. ss.
        * i. rewrite MEMLOC. ss.
  Qed.

  Lemma sim_thread_plus_step
        l e1_src
        e_tgt e1_tgt e2_tgt e3_tgt
        (SIM1: sim_thread l e1_src e1_tgt)
        (WF1_SRC: Local.wf e1_src.(Thread.local) e1_src.(Thread.memory))
        (WF1_TGT: Local.wf e1_tgt.(Thread.local) e1_tgt.(Thread.memory))
        (SC1_SRC: Memory.closed_timemap e1_src.(Thread.sc) e1_src.(Thread.memory))
        (SC1_TGT: Memory.closed_timemap e1_tgt.(Thread.sc) e1_tgt.(Thread.memory))
        (CLOSED1_SRC: Memory.closed e1_src.(Thread.memory))
        (CLOSED1_TGT: Memory.closed e1_tgt.(Thread.memory))
        (STEPS_TGT: rtc (@Thread.tau_step lang) e1_tgt e2_tgt)
        (STEP_TGT: Thread.opt_step e_tgt e2_tgt e3_tgt):
    exists e_src e2_src e3_src,
      <<STEPS_SRC: rtc (@Thread.tau_step lang) e1_src e2_src>> /\
      <<STEP_SRC: Thread.opt_step e_src e2_src e3_src>> /\
      <<EVENT: ThreadEvent.get_machine_event e_src = ThreadEvent.get_machine_event e_tgt>> /\
      <<SIM3: sim_thread l e3_src e3_tgt>> /\
      <<MEMLOC: forall to, Memory.get l to e1_src.(Thread.memory) = Memory.get l to e3_src.(Thread.memory)>>.
  Proof.
    exploit sim_thread_rtc_tau_step; eauto. i. des.
    exploit Thread.rtc_tau_step_future; try exact STEPS_SRC; eauto. i. des.
    exploit Thread.rtc_tau_step_future; try exact STEPS_TGT; eauto. i. des.
    exploit sim_thread_opt_step; eauto. i. des.
    esplits; eauto.
    i. rewrite MEMLOC. ss.
  Qed.


  (* certification *)

  Lemma sim_thread_cap
        l e_src e_tgt
        sc_src sc_tgt
        cap_src cap_tgt
        (SIM: sim_thread l e_src e_tgt)
        (WF_SRC: Local.wf e_src.(Thread.local) e_src.(Thread.memory))
        (WF_TGT: Local.wf e_tgt.(Thread.local) e_tgt.(Thread.memory))
        (CLOSED_SRC: Memory.closed e_src.(Thread.memory))
        (CLOSED_TGT: Memory.closed e_tgt.(Thread.memory))
        (SC_SRC: Memory.max_full_timemap cap_src sc_src)
        (SC_TGT: Memory.max_full_timemap cap_tgt sc_tgt)
        (CAP_SRC: Memory.cap e_src.(Thread.local).(Local.promises) e_src.(Thread.memory) cap_src)
        (CAP_TGT: Memory.cap e_tgt.(Thread.local).(Local.promises) e_tgt.(Thread.memory) cap_tgt):
    sim_thread l
               (Thread.mk lang e_src.(Thread.state) e_src.(Thread.local) sc_src cap_src)
               (Thread.mk lang e_tgt.(Thread.state) e_tgt.(Thread.local) sc_tgt cap_tgt).
  Proof.
    inv SIM. inv LOCAL.
    exploit sim_memory_cap; [apply PROMISES1|exact MEMORY|..]; eauto. i. des.
    hexploit sim_memory_max_full_timemap; try exact x0; eauto. i. des.
    econs; eauto.
    s. eapply cap_fulfillable; eauto. apply WF_SRC.
  Qed.

  Lemma sim_thread_consistent
        l e_src e_tgt
        (SIM: sim_thread l e_src e_tgt)
        (WF_SRC: Local.wf e_src.(Thread.local) e_src.(Thread.memory))
        (WF_TGT: Local.wf e_tgt.(Thread.local) e_tgt.(Thread.memory))
        (SC_SRC: Memory.closed_timemap e_src.(Thread.sc) e_src.(Thread.memory))
        (SC_TGT: Memory.closed_timemap e_tgt.(Thread.sc) e_tgt.(Thread.memory))
        (CLOSED_SRC: Memory.closed e_src.(Thread.memory))
        (CLOSED_TGT: Memory.closed e_tgt.(Thread.memory))
        (CONSISTENT_TGT: Thread.consistent e_tgt):
    <<CONSISTENT_SRC: Thread.consistent e_src>>.
  Proof.
    exploit Memory.cap_exists; try exact CLOSED_TGT. i. des.
    exploit Memory.cap_closed; eauto. i.
    exploit Memory.max_full_timemap_exists; try apply x0. i. des.
    ii.
    exploit sim_thread_cap; try exact SIM; try exact CAP0; try exact CAP; eauto. i.
    exploit Local.cap_wf; try exact WF_SRC; eauto. intro WF_CAP_SRC.
    exploit Local.cap_wf; try exact WF_TGT; eauto. intro WF_CAP_TGT.
    hexploit Memory.max_full_timemap_closed; try exact SC_MAX. intro SC_MAX_SRC.
    hexploit Memory.max_full_timemap_closed; try exact x1. intro SC_MAX_TGT.
    exploit Memory.cap_closed; try exact CLOSED_SRC; eauto. intro CLOSED_CAP_SRC.
    exploit Memory.cap_closed; try exact CLOSED_TGT; eauto. intro CLOSED_CAP_TGT.
    exploit CONSISTENT_TGT; eauto. i. des.
    - left. unfold Thread.steps_failure in *. des.
      exploit sim_thread_plus_step; eauto.
      { econs 2; eauto. }
      s. i. des.
      destruct e_src0; ss. inv STEP_SRC.
      destruct pf; try by (inv STEP; inv STEP0).
      esplits; eauto.
    - right.
      exploit sim_thread_rtc_tau_step; try exact STEPS; eauto. i. des.
      esplits; eauto.
      inv SIM2. apply Memory.ext. i.
      rewrite Memory.bot_get.
      destruct (Loc.eq_dec loc l); subst; ss.
      destruct (Memory.get loc ts (Local.promises (Thread.local e2_src))) as [[]|] eqn:GETP; ss.
      inv LOCAL. inv PROMISES1.
      exploit SOUND; eauto. i. des.
      rewrite PROMISES, Memory.bot_get in GET_TGT. ss.
  Qed.
End SimThreadOther.
