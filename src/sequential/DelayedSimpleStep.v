Require Import RelationClasses.
Require Import Program.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import Loc.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Language.

Require Import Event.
Require Import Time.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import MemoryFacts.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.

Require Import PromiseConsistent.
Require Import Cover.
Require Import MemorySplit.
Require Import MemoryMerge.
Require Import FulfillStep.
Require Import Pred.
Require Import Trace.
Require Import MemoryProps.
Require Import LowerMemory.
Require Import FulfillStep.
Require Import ReorderStepPromise.
Require Import Pred.
Require Import Trace.

Require Import SeqLib.
Require Import gSimAux.
Require Import DelayedSimple.

Set Implicit Arguments.
Set Nested Proofs Allowed.


Section DStep.
  Variable lang: language.

  (** delayed steps *)

  Variant dstep (e: ThreadEvent.t) (e1 e4: Thread.t lang): Prop :=
  | dstep_intro
      e2 e3 pf
      (PROMISES: rtc (tau (@pred_step is_promise _)) e1 e2)
      (LOWERS: rtc (tau lower_step) e2 e3)
      (STEP_RELEASE: Thread.step pf e e3 e4)
      (EVENT_RELEASE: release_event e)
  .

  Variant dsteps: forall (e: MachineEvent.t) (e1 e2: Thread.t lang), Prop :=
  | dsteps_promises
      e1 e2 e3
      (DSTEPS: rtc (tau dstep) e1 e2)
      (PROMISES: rtc (tau (@pred_step is_promise _)) e2 e3):
    dsteps MachineEvent.silent e1 e3
  | dsteps_step
      e te e1 e2 e3
      (DSTEPS: rtc (tau dstep) e1 e2)
      (DSTEP: dstep te e2 e3)
      (EVENT: e = ThreadEvent.get_machine_event te):
    dsteps e e1 e3
  .

  Definition delayed_consistent (e1: Thread.t lang): Prop :=
    forall mem1 (CAP: Memory.cap e1.(Thread.memory) mem1),
    exists e e2,
      (<<DSTEPS: dsteps
                   e (Thread.mk _ (Thread.state e1) (Thread.local e1) (Thread.sc e1) mem1) e2>>) /\
      ((<<FAILURE: e = MachineEvent.failure>>) \/
       (<<SILENT: e = MachineEvent.silent>>) /\
       (<<PROMISES: Local.promises (Thread.local e2) = Memory.bot>>)).

  Lemma dstep_rtc_all_step
        e e1 e2
        (STEP: dstep e e1 e2):
    rtc (@Thread.all_step lang) e1 e2.
  Proof.
    inv STEP.
    etrans.
    { eapply rtc_implies; try eapply PROMISES.
      i. inv H. inv TSTEP. econs. eauto.
    }
    etrans.
    { eapply rtc_implies; try eapply LOWERS.
      i. inv H. inv TSTEP. econs. econs. econs 2. eauto.
    }
    econs 2; eauto. econs. econs. eauto.
  Qed.

  Lemma dstep_rtc_tau_step
        e e1 e2
        (STEP: dstep e e1 e2)
        (SILENT: ThreadEvent.get_machine_event e = MachineEvent.silent):
    rtc (@Thread.tau_step lang) e1 e2.
  Proof.
    inv STEP.
    etrans.
    { eapply rtc_implies; try eapply PROMISES.
      i. inv H. inv TSTEP. econs; eauto.
    }
    etrans.
    { eapply rtc_implies; try eapply LOWERS.
      i. inv H. inv TSTEP. econs; eauto. econs. econs 2. eauto.
    }
    econs 2; eauto. econs; eauto. econs. eauto.
  Qed.

  Lemma rtc_dstep_rtc_tau_step
        e1 e2
        (STEP: rtc (tau dstep) e1 e2):
    rtc (@Thread.tau_step lang) e1 e2.
  Proof.
    induction STEP; eauto. inv H.
    exploit dstep_rtc_tau_step; eauto. i.
    etrans; eauto.
  Qed.

  Lemma dsteps_rtc_all_step
        e e1 e2
        (STEP: dsteps e e1 e2):
    rtc (@Thread.all_step lang) e1 e2.
  Proof.
    inv STEP.
    - exploit rtc_dstep_rtc_tau_step; eauto. i.
      etrans.
      + eapply rtc_implies; try eapply x0.
        i. inv H. econs. eauto.
      + eapply rtc_implies; try eapply PROMISES.
        i. inv H. inv TSTEP. econs. eauto.
    - exploit rtc_dstep_rtc_tau_step; eauto. i.
      exploit dstep_rtc_all_step; eauto. i.
      etrans; [|eauto].
      eapply rtc_implies; try eapply x0.
      i. inv H. econs. eauto.
  Qed.

  (* Lemma dstep_future *)
  (*       e e1 e2 *)
  (*       (WF1: Local.wf (Thread.local e1) (Thread.memory e1)) *)
  (*       (SC1: Memory.closed_timemap (Thread.sc e1) (Thread.memory e1)) *)
  (*       (MEM1: Memory.closed (Thread.memory e1)) *)
  (*       (STEP: dstep e e1 e2): *)
  (*   (<<WF2: Local.wf (Thread.local e2) (Thread.memory e2)>>) /\ *)
  (*   (<<SC2: Memory.closed_timemap (Thread.sc e2) (Thread.memory e2)>>) /\ *)
  (*   (<<MEM2: Memory.closed (Thread.memory e2)>>) /\ *)
  (*   (<<TVIEW_FUTURE: TView.le (Local.tview (Thread.local e1)) (Local.tview (Thread.local e2))>>) /\ *)
  (*   (<<SC_FUTURE: TimeMap.le (Thread.sc e1) (Thread.sc e2)>>) /\ *)
  (*   (<<MEM_FUTURE: Memory.future (Thread.memory e1) (Thread.memory e2)>>). *)
  (* Proof. *)
  (*   inv STEP. *)
  (*   exploit Thread.rtc_tau_step_future; try eapply rtc_implies; try eapply PROMISES; eauto. *)
  (*   { i. inv H. inv TSTEP. inv STEP. econs; eauto. econs. eauto. } *)
  (*   i. des. *)
  (*   exploit Thread.rtc_tau_step_future; try eapply rtc_implies; try eapply LOWERS; eauto. *)
  (*   { i. inv H. inv TSTEP. econs; eauto. econs. econs 2; eauto. } *)
  (*   i. des. *)
  (*   exploit Thread.step_future; try exact STEP_RELEASE; eauto. i. des. *)
  (*   splits; eauto; repeat (etrans; eauto). *)
  (* Qed. *)

  (* Lemma rtc_dstep_future *)
  (*       e1 e2 *)
  (*       (WF1: Local.wf (Thread.local e1) (Thread.memory e1)) *)
  (*       (SC1: Memory.closed_timemap (Thread.sc e1) (Thread.memory e1)) *)
  (*       (MEM1: Memory.closed (Thread.memory e1)) *)
  (*       (STEP: rtc (tau dstep) e1 e2): *)
  (*   (<<WF2: Local.wf (Thread.local e2) (Thread.memory e2)>>) /\ *)
  (*   (<<SC2: Memory.closed_timemap (Thread.sc e2) (Thread.memory e2)>>) /\ *)
  (*   (<<MEM2: Memory.closed (Thread.memory e2)>>) /\ *)
  (*   (<<TVIEW_FUTURE: TView.le (Local.tview (Thread.local e1)) (Local.tview (Thread.local e2))>>) /\ *)
  (*   (<<SC_FUTURE: TimeMap.le (Thread.sc e1) (Thread.sc e2)>>) /\ *)
  (*   (<<MEM_FUTURE: Memory.future (Thread.memory e1) (Thread.memory e2)>>). *)
  (* Proof. *)
  (*   induction STEP. *)
  (*   { splits; auto; refl. } *)
  (*   inv H. exploit dstep_future; try exact TSTEP; eauto. i. des. *)
  (*   exploit IHSTEP; eauto. i. des. *)
  (*   splits; auto; etrans; eauto. *)
  (* Qed. *)

  (* Lemma dsteps_future *)
  (*       e e1 e2 *)
  (*       (WF1: Local.wf (Thread.local e1) (Thread.memory e1)) *)
  (*       (SC1: Memory.closed_timemap (Thread.sc e1) (Thread.memory e1)) *)
  (*       (MEM1: Memory.closed (Thread.memory e1)) *)
  (*       (STEP: dsteps e e1 e2): *)
  (*   (<<WF2: Local.wf (Thread.local e2) (Thread.memory e2)>>) /\ *)
  (*   (<<SC2: Memory.closed_timemap (Thread.sc e2) (Thread.memory e2)>>) /\ *)
  (*   (<<MEM2: Memory.closed (Thread.memory e2)>>) /\ *)
  (*   (<<TVIEW_FUTURE: TView.le (Local.tview (Thread.local e1)) (Local.tview (Thread.local e2))>>) /\ *)
  (*   (<<SC_FUTURE: TimeMap.le (Thread.sc e1) (Thread.sc e2)>>) /\ *)
  (*   (<<MEM_FUTURE: Memory.future (Thread.memory e1) (Thread.memory e2)>>). *)
  (* Proof. *)
  (*   inv STEP. *)
  (*   - exploit rtc_dstep_future; try exact DSTEPS; eauto. i. des. *)
  (*     exploit Thread.rtc_tau_step_future; try eapply rtc_implies; try eapply PROMISES; eauto. *)
  (*     { i. inv H. inv TSTEP. inv STEP. econs; eauto. econs. eauto. } *)
  (*     i. des. splits; auto; etrans; eauto. *)
  (*   - exploit rtc_dstep_future; try exact DSTEPS; eauto. i. des. *)
  (*     exploit dstep_future; try exact DSTEP; eauto. i. des. *)
  (*     splits; auto; etrans; eauto. *)
  (* Qed. *)


  (** non release steps *)

  Variant nr_step (e: ThreadEvent.t) (e1 e2: Thread.t lang): Prop :=
  | nr_step_intro
      pf
      (STEP: Thread.step pf e e1 e2)
      (RELEASE: ~ release_event e)
  .

  Variant nrp_step (e: ThreadEvent.t) (e1 e3: Thread.t lang): Prop :=
  | nrp_step_intro
      e2 pf
      (STEPS: rtc (tau nr_step) e1 e2)
      (STEP: Thread.step pf e e2 e3)
      (RELEASE: release_event e)
  .

  Variant nrp_steps: forall (e: MachineEvent.t) (e1 e2: Thread.t lang), Prop :=
  | nrp_steps_non_release
      e1 e2 e3
      (STEPS: rtc (tau nrp_step) e1 e2)
      (NSTEPS: rtc (tau nr_step) e2 e3):
    nrp_steps MachineEvent.silent e1 e3
  | nrp_steps_release
      e e1 e2 e3
      (STEPS: rtc (tau nrp_step) e1 e2)
      (STEP: nrp_step e e2 e3):
    nrp_steps (ThreadEvent.get_machine_event e) e1 e3
  .

  Lemma nrp_step_rtc_all_step
        e e1 e2
        (STEP: nrp_step e e1 e2):
    rtc (@Thread.all_step lang) e1 e2.
  Proof.
    inv STEP. etrans.
    - eapply rtc_implies; try eapply STEPS.
      i. inv H. inv TSTEP. econs. econs. eauto.
    - econs 2; eauto. econs. econs. eauto.
  Qed.

  Lemma nrp_step_rtc_tau_step
        e e1 e2
        (STEP: nrp_step e e1 e2)
        (SILENT: ThreadEvent.get_machine_event e = MachineEvent.silent):
    rtc (@Thread.tau_step lang) e1 e2.
  Proof.
    inv STEP. etrans.
    - eapply rtc_implies; try eapply STEPS.
      i. inv H. inv TSTEP. econs; eauto. econs. eauto.
    - econs 2; eauto. econs; eauto. econs. eauto.
  Qed.

  Lemma rtc_nrp_step_rtc_tau_step
        e1 e2
        (STEP: rtc (tau nrp_step) e1 e2):
    rtc (@Thread.tau_step lang) e1 e2.
  Proof.
    induction STEP; eauto. inv H.
    exploit nrp_step_rtc_tau_step; eauto. i.
    etrans; eauto.
  Qed.

  Lemma nrp_steps_rtc_all_step
        e e1 e2
        (STEP: nrp_steps e e1 e2):
    rtc (@Thread.all_step lang) e1 e2.
  Proof.
    inv STEP.
    - etrans.
      + eapply rtc_implies; try eapply rtc_nrp_step_rtc_tau_step; eauto.
        i. inv H. econs. eauto.
      + eapply rtc_implies; try eapply NSTEPS.
        i. inv H. inv TSTEP. econs. econs. eauto.
    - etrans.
      + eapply rtc_implies; try eapply rtc_nrp_step_rtc_tau_step; eauto.
        i. inv H. econs. eauto.
      + eapply nrp_step_rtc_all_step; eauto.
  Qed.

  (* Lemma nrp_step_future *)
  (*       e e1 e2 *)
  (*       (WF1: Local.wf (Thread.local e1) (Thread.memory e1)) *)
  (*       (SC1: Memory.closed_timemap (Thread.sc e1) (Thread.memory e1)) *)
  (*       (MEM1: Memory.closed (Thread.memory e1)) *)
  (*       (STEP: nrp_step e e1 e2): *)
  (*   (<<WF2: Local.wf (Thread.local e2) (Thread.memory e2)>>) /\ *)
  (*   (<<SC2: Memory.closed_timemap (Thread.sc e2) (Thread.memory e2)>>) /\ *)
  (*   (<<MEM2: Memory.closed (Thread.memory e2)>>) /\ *)
  (*   (<<TVIEW_FUTURE: TView.le (Local.tview (Thread.local e1)) (Local.tview (Thread.local e2))>>) /\ *)
  (*   (<<SC_FUTURE: TimeMap.le (Thread.sc e1) (Thread.sc e2)>>) /\ *)
  (*   (<<MEM_FUTURE: Memory.future (Thread.memory e1) (Thread.memory e2)>>). *)
  (* Proof. *)
  (*   inv STEP. *)
  (*   exploit Thread.rtc_tau_step_future; try eapply rtc_implies; try eapply STEPS; eauto. *)
  (*   { i. inv H. inv TSTEP. econs; eauto. econs. eauto. } *)
  (*   i. des. *)
  (*   exploit Thread.step_future; try exact STEP0; eauto. i. des. *)
  (*   splits; auto; etrans; eauto. *)
  (* Qed. *)

  (* Lemma rtc_nrp_step_future *)
  (*       e1 e2 *)
  (*       (WF1: Local.wf (Thread.local e1) (Thread.memory e1)) *)
  (*       (SC1: Memory.closed_timemap (Thread.sc e1) (Thread.memory e1)) *)
  (*       (MEM1: Memory.closed (Thread.memory e1)) *)
  (*       (STEP: rtc (tau nrp_step) e1 e2): *)
  (*   (<<WF2: Local.wf (Thread.local e2) (Thread.memory e2)>>) /\ *)
  (*   (<<SC2: Memory.closed_timemap (Thread.sc e2) (Thread.memory e2)>>) /\ *)
  (*   (<<MEM2: Memory.closed (Thread.memory e2)>>) /\ *)
  (*   (<<TVIEW_FUTURE: TView.le (Local.tview (Thread.local e1)) (Local.tview (Thread.local e2))>>) /\ *)
  (*   (<<SC_FUTURE: TimeMap.le (Thread.sc e1) (Thread.sc e2)>>) /\ *)
  (*   (<<MEM_FUTURE: Memory.future (Thread.memory e1) (Thread.memory e2)>>). *)
  (* Proof. *)
  (*   induction STEP. *)
  (*   { splits; auto; refl. } *)
  (*   inv H. exploit nrp_step_future; try exact TSTEP; eauto. i. des. *)
  (*   exploit IHSTEP; eauto. i. des. *)
  (*   splits; auto; etrans; eauto. *)
  (* Qed. *)

  (* Lemma nrp_steps_future *)
  (*       e e1 e2 *)
  (*       (WF1: Local.wf (Thread.local e1) (Thread.memory e1)) *)
  (*       (SC1: Memory.closed_timemap (Thread.sc e1) (Thread.memory e1)) *)
  (*       (MEM1: Memory.closed (Thread.memory e1)) *)
  (*       (STEP: nrp_steps e e1 e2): *)
  (*   (<<WF2: Local.wf (Thread.local e2) (Thread.memory e2)>>) /\ *)
  (*   (<<SC2: Memory.closed_timemap (Thread.sc e2) (Thread.memory e2)>>) /\ *)
  (*   (<<MEM2: Memory.closed (Thread.memory e2)>>) /\ *)
  (*   (<<TVIEW_FUTURE: TView.le (Local.tview (Thread.local e1)) (Local.tview (Thread.local e2))>>) /\ *)
  (*   (<<SC_FUTURE: TimeMap.le (Thread.sc e1) (Thread.sc e2)>>) /\ *)
  (*   (<<MEM_FUTURE: Memory.future (Thread.memory e1) (Thread.memory e2)>>). *)
  (* Proof. *)
  (*   inv STEP. *)
  (*   - exploit rtc_nrp_step_future; eauto. i. des. *)
  (*     exploit Thread.rtc_tau_step_future; try eapply rtc_implies; try exact NSTEPS; eauto. *)
  (*     { i. inv H. inv TSTEP. econs; eauto. econs. eauto. } *)
  (*     i. des. splits; auto; etrans; eauto. *)
  (*   - exploit rtc_nrp_step_future; eauto. i. des. *)
  (*     exploit nrp_step_future; try exact STEP0; eauto. i. des. *)
  (*     splits; auto; etrans; eauto. *)
  (* Qed. *)

  Lemma non_release_silent
        e
        (RELEASE: ~ release_event e):
    ThreadEvent.get_machine_event e = MachineEvent.silent.
  Proof.
    destruct e; ss.
  Qed.

  Lemma lower_event_release
        e_src e_tgt
        (LOWER: lower_event e_src e_tgt):
    release_event e_src <-> release_event e_tgt.
  Proof.
    inv LOWER; ss.
  Qed.

  Lemma lower_event_machine_event
        e_src e_tgt
        (LOWER: lower_event e_src e_tgt):
    ThreadEvent.get_machine_event e_src = ThreadEvent.get_machine_event e_tgt.
  Proof.
    inv LOWER; ss.
  Qed.

  Lemma plus_step_nrp_steps
        pf e e1 e2 e3
        (STEPS: rtc (@Thread.tau_step _) e1 e2)
        (STEP: Thread.step pf e e2 e3):
    nrp_steps (ThreadEvent.get_machine_event e) e1 e3.
  Proof.
    induction STEPS; i.
    { destruct (classic (release_event e)).
      - econs 2; try refl. econs; try refl; eauto.
      - rewrite non_release_silent; eauto.
        econs 1; try refl. econs 2; try refl.
        econs; try eapply non_release_silent; eauto.
        econs; eauto.
    }
    exploit IHSTEPS; eauto. i. clear IHSTEPS.
    clear - H x0.
    inv H. inv TSTEP.
    destruct (classic (release_event e0)).
    { inv x0.
      { econs 1; try exact NSTEPS.
        econs 2; try exact STEPS.
        econs; try exact EVENT.
        econs; try refl; eauto.
      }
      { econs 2; try exact STEP0.
        econs 2; try exact STEPS.
        econs; try exact EVENT.
        econs; try refl; eauto.
      }
    }
    { inv x0.
      { inv STEPS.
        { econs 1; [refl|].
          econs 2; try exact NSTEPS.
          econs; try exact EVENT.
          econs; eauto.
        }
        { econs 1; try exact NSTEPS.
          econs 2; try exact H2.
          inv H0. econs; try exact EVENT0.
          inv TSTEP. econs; try exact STEP0; ss.
          econs 2; try exact STEPS.
          econs; try exact EVENT. econs; eauto.
        }
      }
      { inv STEPS.
        { econs 2; [refl|].
          inv STEP0. econs; try exact STEP1; ss.
          econs 2; try exact STEPS.
          econs; try exact EVENT.
          econs; eauto.
        }
        { econs 2; try exact STEP0.
          econs 2; try exact H2.
          inv H0. econs; try exact EVENT0.
          inv TSTEP. econs; try exact STEP1; ss.
          econs 2; try exact STEPS.
          econs; try exact EVENT.
          econs; eauto.
        }
      }
    }
  Qed.


  (** steps to delayed steps *)

  Variant delayed_thread (e_src e_lower: Thread.t lang): Prop :=
  | delayed_thread_intro
      (SC: Thread.sc e_src = Thread.sc e_lower)
      (MEM: Thread.memory e_src = Thread.memory e_lower)
      (DELAYED: delayed (Thread.state e_src) (Thread.state e_lower)
                        (Thread.local e_src) (Thread.local e_lower)
                        (Thread.sc e_lower) (Thread.memory e_lower))
  .

  Lemma delayed_thread_refl
        e
        (WF: Local.wf (Thread.local e) (Thread.memory e))
        (SC: Memory.closed_timemap (Thread.sc e) (Thread.memory e))
        (MEM: Memory.closed (Thread.memory e)):
    delayed_thread e e.
  Proof.
    econs; eauto. eapply delayed_refl; eauto.
  Qed.

  Lemma delayed_wf_src
        e_src e_lower
        (DELAYED: delayed_thread e_src e_lower):
    (<<WF: Local.wf (Thread.local e_src) (Thread.memory e_src)>>) /\
    (<<SC: Memory.closed_timemap (Thread.sc e_src) (Thread.memory e_src)>>) /\
    (<<MEM: Memory.closed (Thread.memory e_src)>>).
  Proof.
    inv DELAYED. unfold delayed in *. des.
    rewrite SC, MEM in *. auto.
  Qed.

  Variant lower_delayed_thread (e_src e_tgt: Thread.t lang): Prop :=
  | lower_delayed_thread_intro
      e_lower
      (LOWER: lower_thread e_lower e_tgt)
      (DELAYED: delayed_thread e_src e_lower)
  .

  Lemma ld_wf_src
        e_src e_tgt
        (LD: lower_delayed_thread e_src e_tgt):
    (<<WF: Local.wf (Thread.local e_src) (Thread.memory e_src)>>) /\
    (<<SC: Memory.closed_timemap (Thread.sc e_src) (Thread.memory e_src)>>) /\
    (<<MEM: Memory.closed (Thread.memory e_src)>>).
  Proof.
    inv LD. eapply delayed_wf_src; eauto.
  Qed.

  Lemma delayed_rtc_nr_step_aux
        (st0 st1 st2: Language.state lang) lc0 lc1 lc2
        mem1 sc1 mem2 sc2
        (STEP: rtc (tau nr_step) (Thread.mk _ st1 lc1 sc1 mem1) (Thread.mk _ st2 lc2 sc2 mem2))
        (CONS: Local.promise_consistent lc2)
        (DELAYED: delayed st0 st1 lc0 lc1 sc1 mem1)
    :
      exists lc0',
        (<<PROMISES: rtc (tau (@pred_step is_promise _)) (Thread.mk _ st0 lc0 sc1 mem1) (Thread.mk _ st0 lc0' sc2 mem2)>>) /\
        (<<DELAYED: delayed st0 st2 lc0' lc2 sc2 mem2>>).
  Proof.
    remember (Thread.mk _ st1 lc1 sc1 mem1) as e1.
    remember (Thread.mk _ st2 lc2 sc2 mem2) as e2.
    revert lc0 st1 lc1 sc1 mem1 Heqe1 st2 lc2 sc2 mem2 Heqe2 CONS DELAYED.
    induction STEP; i; subst.
    { inv Heqe2. esplits; eauto. }
    destruct y as [st lc sc mem].
    inv H. inv TSTEP.
    exploit delayed_step; try exact STEP0; try exact DELAYED; eauto.
    { exploit Thread.step_future; try exact STEP0; try apply DELAYED. s. i. des.
      hexploit rtc_all_step_promise_consistent;
        try eapply rtc_implies; try eapply STEP; eauto; ss.
      i. inv H. inv TSTEP. econs. econs. eauto.
    }
    i. des.
    exploit IHSTEP; try exact DELAYED0; eauto. i. des.
    esplits; [etrans; eauto|].
    unfold delayed in *. des. splits; eauto.
  Qed.

  Lemma delayed_rtc_nr_step
        e1_src e1_lower e2_lower
        (DELAYED: delayed_thread e1_src e1_lower)
        (STEP: rtc (tau nr_step) e1_lower e2_lower)
        (CONS: Local.promise_consistent (Thread.local e2_lower)):
      exists e2_src,
        (<<PROMISES: rtc (tau (@pred_step is_promise _)) e1_src e2_src>>) /\
        (<<DELAYED: delayed_thread e2_src e2_lower>>).
  Proof.
    destruct e1_src as [st1_src lc1_src sc1_src mem1_src],
             e1_lower as [st1_lower lc1_lower sc1_lower mem1_lower],
             e2_lower as [st2_lower lc2_lower sc2_lower mem2_lower].
    inv DELAYED. ss. subst.
    exploit delayed_rtc_nr_step_aux; try exact DELAYED0; eauto. i. des.
    esplits; eauto.
    econs; ss; eauto.
  Qed.

  Lemma delayed_nrp_step
        e1_src e1_lower e_lower e2_lower
        (DELAYED: delayed_thread e1_src e1_lower)
        (STEP: nrp_step e_lower e1_lower e2_lower)
        (CONS: Local.promise_consistent (Thread.local e2_lower)):
    exists e_src e2_src,
      (<<STEP_SRC: dstep e_src e1_src e2_src>>) /\
      (<<EVENT: lower_event e_src e_lower>>) /\
      (<<LOWER: lower_thread e2_src e2_lower>>).
  Proof.
    inv DELAYED. inv STEP.
    destruct e1_src as [st1_src lc1_src sc1_src mem1_src],
             e1_lower as [st1_lower lc1_lower sc1_lower mem1_lower],
             e2 as [st2_lower lc2_lower sc2_lower mem2_lower].
    ss. subst.
    exploit delayed_rtc_nr_step_aux; try exact DELAYED0; eauto.
    { exploit Thread.rtc_all_step_future;
        try eapply rtc_implies; try exact STEPS; try apply DELAYED0.
      { i. inv H. inv TSTEP. econs. econs. eauto. }
      s. i. des.
      hexploit step_promise_consistent; try exact STEP0; eauto.
    }
    i. des.
    unfold delayed in DELAYED. des.
    hexploit Thread.rtc_all_step_future;
      try eapply rtc_implies; try exact STEPS0; ss; try apply DELAYED0.
    { i. inv H. inv TSTEP. econs. econs. econs 2; eauto. }
    i. des.
    destruct e2_lower as [st3_lower lc3_lower sc3_lower mem3_lower]. ss.
    exploit lower_memory_thread_step; try exact STEP0;
      try exact LOCAL; try exact MEM0; eauto. i. des.
    esplits.
    - econs; eauto. erewrite lower_event_release; eauto.
    - ss.
    - econs; eauto.
  Qed.

  Lemma lower_rtc_nr_step
        e1_lower e1_tgt e2_tgt
        (LOWER1: lower_thread e1_lower e1_tgt)
        (WF1_LOWER: Local.wf (Thread.local e1_lower) (Thread.memory e1_lower))
        (SC1_LOWER: Memory.closed_timemap (Thread.sc e1_lower) (Thread.memory e1_lower))
        (CLOSED1_LOWER: Memory.closed (Thread.memory e1_lower))
        (WF1_TGT: Local.wf (Thread.local e1_tgt) (Thread.memory e1_tgt))
        (SC1_TGT: Memory.closed_timemap (Thread.sc e1_tgt) (Thread.memory e1_tgt))
        (CLOSED1_TGT: Memory.closed (Thread.memory e1_tgt))
        (STEP_TGT: rtc (tau nr_step) e1_tgt e2_tgt):
      exists e2_lower,
        (<<STEP_LOWER: rtc (tau nr_step) e1_lower e2_lower>>) /\
        (<<LOWER2: lower_thread e2_lower e2_tgt>>).
  Proof.
    revert e1_lower LOWER1 WF1_LOWER SC1_LOWER CLOSED1_LOWER.
    induction STEP_TGT; i; eauto.
    inv H. inv TSTEP.
    exploit lower_thread_step; try exact LD1; eauto. i. des.
    exploit Thread.step_future; try exact STEP; eauto. i. des.
    exploit Thread.step_future; try exact STEP0; eauto. i. des.
    exploit IHSTEP_TGT; try exact LOWER; eauto. i. des.
    esplits; try exact LOWER2.
    econs 2; eauto. econs.
    - econs; [eauto|]. erewrite lower_event_release; eauto.
    - erewrite lower_event_machine_event; eauto.
  Qed.

  Lemma lower_nrp_step
        e1_lower e_tgt e1_tgt e2_tgt
        (LOWER1: lower_thread e1_lower e1_tgt)
        (WF1_LOWER: Local.wf (Thread.local e1_lower) (Thread.memory e1_lower))
        (SC1_LOWER: Memory.closed_timemap (Thread.sc e1_lower) (Thread.memory e1_lower))
        (CLOSED1_LOWER: Memory.closed (Thread.memory e1_lower))
        (WF1_TGT: Local.wf (Thread.local e1_tgt) (Thread.memory e1_tgt))
        (SC1_TGT: Memory.closed_timemap (Thread.sc e1_tgt) (Thread.memory e1_tgt))
        (CLOSED1_TGT: Memory.closed (Thread.memory e1_tgt))
        (STEP_TGT: nrp_step e_tgt e1_tgt e2_tgt):
      exists e_src e2_lower,
        (<<STEP_LOWER: nrp_step e_src e1_lower e2_lower>>) /\
        (<<EVENT: lower_event e_src e_tgt>>) /\
        (<<LOWER2: lower_thread e2_lower e2_tgt>>).
  Proof.
    inv STEP_TGT.
    exploit lower_rtc_nr_step; try exact LOWER1; eauto. i. des.
    exploit Thread.rtc_tau_step_future; try eapply rtc_implies; try exact STEPS; eauto.
    { i. inv H. inv TSTEP. econs; eauto. econs. eauto. }
    i. des.
    exploit Thread.rtc_tau_step_future; try eapply rtc_implies; try exact STEP_LOWER; eauto.
    { i. inv H. inv TSTEP. econs; eauto. econs. eauto. }
    i. des.
    exploit lower_thread_step; try exact STEP; eauto. i. des.
    esplits; eauto. econs; eauto.
    erewrite lower_event_release; eauto.
  Qed.

  Lemma ld_rtc_nr_step
        e1_src e1_tgt e2_tgt
        (LD1: lower_delayed_thread e1_src e1_tgt)
        (WF1_TGT: Local.wf (Thread.local e1_tgt) (Thread.memory e1_tgt))
        (SC1_TGT: Memory.closed_timemap (Thread.sc e1_tgt) (Thread.memory e1_tgt))
        (CLOSED1_TGT: Memory.closed (Thread.memory e1_tgt))
        (STEP: rtc (tau nr_step) e1_tgt e2_tgt)
        (CONS: Local.promise_consistent (Thread.local e2_tgt)):
      exists e2_src,
        (<<PROMISES: rtc (tau (@pred_step is_promise _)) e1_src e2_src>>) /\
        (<<LD2: lower_delayed_thread e2_src e2_tgt>>).
  Proof.
    inv LD1.
    exploit lower_rtc_nr_step; try exact LOWER; try apply DELAYED; eauto. i. des.
    hexploit lower_thread_consistent; try apply LOWER2; eauto. i.
    exploit delayed_rtc_nr_step; try exact DELAYED; eauto. i. des.
    esplits; eauto. econs; eauto.
  Qed.

  Lemma ld_nrp_step
        e1_src e1_tgt e_tgt e2_tgt
        (LD1: lower_delayed_thread e1_src e1_tgt)
        (WF1_TGT: Local.wf (Thread.local e1_tgt) (Thread.memory e1_tgt))
        (SC1_TGT: Memory.closed_timemap (Thread.sc e1_tgt) (Thread.memory e1_tgt))
        (CLOSED1_TGT: Memory.closed (Thread.memory e1_tgt))
        (STEP: nrp_step e_tgt e1_tgt e2_tgt)
        (CONS: Local.promise_consistent (Thread.local e2_tgt)):
      exists e_src e2_src,
        (<<PROMISES: dstep e_src e1_src e2_src>>) /\
        (<<EVENT: lower_event e_src e_tgt>>) /\
        (<<LD2: lower_delayed_thread e2_src e2_tgt>>).
  Proof.
    inv LD1.
    exploit lower_nrp_step; try exact LOWER; try apply DELAYED; eauto. i. des.
    hexploit lower_thread_consistent; try apply LOWER2; eauto. i.
    exploit delayed_nrp_step; try exact DELAYED; eauto. i. des.
    exploit delayed_wf_src; eauto. i. des.
    exploit Thread.rtc_all_step_future;
      try eapply dstep_rtc_all_step; try exact STEP_SRC; eauto. i. des.
    esplits; eauto.
    - etrans; eauto.
    - econs; try apply delayed_thread_refl; eauto. etrans; eauto.
  Qed.

  Lemma ld_rtc_nrp_step
        e1_src e1_tgt e2_tgt
        (LD1: lower_delayed_thread e1_src e1_tgt)
        (WF1_TGT: Local.wf (Thread.local e1_tgt) (Thread.memory e1_tgt))
        (SC1_TGT: Memory.closed_timemap (Thread.sc e1_tgt) (Thread.memory e1_tgt))
        (CLOSED1_TGT: Memory.closed (Thread.memory e1_tgt))
        (STEP: rtc (tau nrp_step) e1_tgt e2_tgt)
        (CONS: Local.promise_consistent (Thread.local e2_tgt)):
      exists e2_src,
        (<<PROMISES: rtc (tau dstep) e1_src e2_src>>) /\
        (<<LD2: lower_delayed_thread e2_src e2_tgt>>).
  Proof.
    revert e1_src LD1.
    induction STEP; i; eauto. inv H.
    exploit Thread.rtc_all_step_future;
      try eapply nrp_step_rtc_all_step; try exact TSTEP; eauto. i. des.
    exploit ld_nrp_step; try exact LD1; eauto.
    { eapply rtc_tau_step_promise_consistent;
        try eapply rtc_nrp_step_rtc_tau_step; try exact STEP; eauto.
    }
    i. des.
    exploit IHSTEP; eauto. i. des.
    esplits; [|eauto].
    econs 2; eauto. econs; eauto.
    erewrite lower_event_machine_event; eauto.
  Qed.

  Lemma ld_nrp_steps_dsteps
        e1_src e1_tgt e_tgt e2_tgt
        (LD1: lower_delayed_thread e1_src e1_tgt)
        (WF1_TGT: Local.wf (Thread.local e1_tgt) (Thread.memory e1_tgt))
        (SC1_TGT: Memory.closed_timemap (Thread.sc e1_tgt) (Thread.memory e1_tgt))
        (CLOSED1_TGT: Memory.closed (Thread.memory e1_tgt))
        (STEP: nrp_steps e_tgt e1_tgt e2_tgt)
        (CONS: Local.promise_consistent (Thread.local e2_tgt)):
    exists e_src e2_src,
      (<<STEP_SRC: dsteps e_src e1_src e2_src>>) /\
      (<<EVENT: e_src = e_tgt>>) /\
      (<<LD2: lower_delayed_thread e2_src e2_tgt>>).
  Proof.
    inv STEP.
    { exploit Thread.rtc_tau_step_future;
        try eapply rtc_nrp_step_rtc_tau_step; try exact STEPS; eauto. i. des.
      exploit ld_rtc_nrp_step; eauto.
      { eapply rtc_tau_step_promise_consistent;
          try eapply rtc_implies; try exact NSTEPS; eauto.
        i. inv H. inv TSTEP. econs; eauto. econs. eauto.
      }
      i. des.
      exploit ld_rtc_nr_step; try exact LD2; eauto. i. des.
      esplits; eauto. econs 1; eauto.
    }
    { exploit Thread.rtc_tau_step_future;
        try eapply rtc_nrp_step_rtc_tau_step; try exact STEPS; eauto. i. des.
      exploit ld_rtc_nrp_step; eauto.
      { eapply rtc_all_step_promise_consistent;
          try eapply nrp_step_rtc_all_step; try exact STEP0; eauto.
      }
      i. des.
      exploit ld_nrp_step; try exact LD2; eauto. i. des.
      esplits; eauto. econs 2; eauto.
      exploit lower_event_machine_event; eauto.
    }
  Qed.

  Lemma ld_future
        e_src e_tgt
        sc_src mem_src sc_tgt mem_tgt
        (LD: lower_delayed_thread e_src e_tgt)
        (SC: TimeMap.le sc_src sc_tgt)
        (MEM: lower_memory mem_src mem_tgt)
        (SC_FUTURE_SRC: TimeMap.le (Thread.sc e_src) sc_src)
        (SC_FUTURE_TGT: TimeMap.le (Thread.sc e_tgt) sc_tgt)
        (MEM_FUTURE_SRC: Memory.future (Thread.memory e_src) mem_src)
        (MEM_FUTURE_TGT: Memory.future (Thread.memory e_tgt) mem_tgt)
        (WF_SRC: Local.wf (Thread.local e_src) mem_src)
        (SC_SRC: Memory.closed_timemap sc_src mem_src)
        (MEM_SRC: Memory.closed mem_src):
    (<<LD_FUTURE: lower_delayed_thread
                    (Thread.mk _ (Thread.state e_src) (Thread.local e_src) sc_src mem_src)
                    (Thread.mk _ (Thread.state e_tgt) (Thread.local e_tgt) sc_tgt mem_tgt)>>).
  Proof.
    inv LD. econs.
    - instantiate (1 := (Thread.mk _ (Thread.state e_lower) (Thread.local e_lower) sc_src mem_src)).
      inv LOWER. econs; ss.
    - inv DELAYED. econs; ss.
      eapply delayed_future; try exact DELAYED0; ss.
      rewrite <- MEM0.
      apply Memory.future_future_weak; eauto.
  Qed.
End DStep.


Module DConfiguration.
  Variant step: forall (e: MachineEvent.t) (tid: Ident.t) (c1 c2: Configuration.t), Prop :=
  | step_intro
      e tid c1 lang st1 lc1 st2 lc2 sc2 mem2
      (TID: IdentMap.find tid (Configuration.threads c1) = Some (existT _ lang st1, lc1))
      (DSTEPS: dsteps e (Thread.mk _ st1 lc1 (Configuration.sc c1) (Configuration.memory c1))
                      (Thread.mk _ st2 lc2 sc2 mem2))
      (CONSISTENT: e <> MachineEvent.failure ->
                   delayed_consistent (Thread.mk _ st2 lc2 sc2 mem2)):
      step e tid c1
           (Configuration.mk (IdentMap.add tid (existT _ _ st2, lc2) (Configuration.threads c1)) sc2 mem2)
  .
End DConfiguration.
