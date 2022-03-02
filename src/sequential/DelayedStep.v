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
Require Import Behavior.

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
Require Import Delayed.

Set Implicit Arguments.


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
       (exists e3,
           (<<SILENT: e = MachineEvent.silent>>) /\
           (<<STEPS: rtc (tau lower_step) e2 e3>>) /\
           (<<PROMISES: Local.promises (Thread.local e3) = Memory.bot>>))).

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

  Lemma dsteps_rtc_tau_step
        e e1 e2
        (STEP: dsteps e e1 e2)
        (SILENT: e = MachineEvent.silent):
    rtc (@Thread.tau_step lang) e1 e2.
  Proof.
    inv STEP.
    - exploit rtc_dstep_rtc_tau_step; eauto. i.
      etrans; eauto.
      eapply rtc_implies; try eapply PROMISES.
      i. inv H0. inv TSTEP. econs; eauto.
    - exploit rtc_dstep_rtc_tau_step; eauto. i.
      exploit dstep_rtc_tau_step; eauto. i.
      etrans; eauto.
  Qed.

  Lemma dsteps_plus_step
        e e1 e3
        (STEP: dsteps e e1 e3):
    e = MachineEvent.silent /\ e1 = e3 \/
    exists e2 pf te,
      (<<STEPS: rtc (@Thread.tau_step lang) e1 e2>>) /\
      (<<STEP: Thread.step pf te e2 e3>>) /\
      (<<EVENT: ThreadEvent.get_machine_event te = e>>).
  Proof.
    inv STEP.
    { exploit rtc_dstep_rtc_tau_step; eauto. i.
      exploit rtc_implies; try eapply PROMISES.
      { i. instantiate (1 := @Thread.tau_step lang).
        inv H. inv TSTEP. econs; eauto.
      }
      i. rewrite x1 in x0. clear e2 DSTEPS PROMISES x1.
      exploit rtc_tail; try exact x0. i. des; eauto.
      right. inv x2. inv TSTEP.
      esplits; eauto.
    }
    { exploit rtc_dstep_rtc_tau_step; eauto. i.
      inv DSTEP.
      exploit rtc_implies; try eapply PROMISES; i.
      { i. instantiate (1 := @Thread.tau_step lang).
        inv H. inv TSTEP. econs; eauto.
      }
      exploit rtc_implies; try eapply LOWERS; i.
      { i. instantiate (1 := @Thread.tau_step lang).
        inv H. inv TSTEP. econs; eauto. econs. econs 2. eauto.
      }
      rewrite x2 in x1. rewrite x1 in x0.
      clear x1 x2 DSTEPS PROMISES LOWERS.
      right. esplits; eauto.
    }
  Qed.


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

  Lemma rtc_tau_step_nrp_steps
        e1 e2
        (STEPS: rtc (@Thread.tau_step _) e1 e2):
    nrp_steps MachineEvent.silent e1 e2.
  Proof.
    induction STEPS.
    { econs; refl. }
    clear - H IHSTEPS.
    inv H. inv TSTEP.
    destruct (classic (release_event e)).
    { inv IHSTEPS.
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
    { inv IHSTEPS.
      { inv STEPS.
        { econs 1; [refl|].
          econs 2; try exact NSTEPS.
          econs; try exact EVENT.
          econs; eauto.
        }
        { econs 1; try exact NSTEPS.
          econs 2; try exact H1.
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

  Lemma lower_delayed_thread_refl
        e
        (WF: Local.wf (Thread.local e) (Thread.memory e))
        (SC: Memory.closed_timemap (Thread.sc e) (Thread.memory e))
        (MEM: Memory.closed (Thread.memory e)):
    lower_delayed_thread e e.
  Proof.
    econs; try refl.
    eapply delayed_thread_refl; eauto.
  Qed.

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

  Lemma ld_rtc_tau_step_dsteps
        e1_src e1_tgt e2_tgt
        (LD1: lower_delayed_thread e1_src e1_tgt)
        (WF1_TGT: Local.wf (Thread.local e1_tgt) (Thread.memory e1_tgt))
        (SC1_TGT: Memory.closed_timemap (Thread.sc e1_tgt) (Thread.memory e1_tgt))
        (CLOSED1_TGT: Memory.closed (Thread.memory e1_tgt))
        (STEPS: rtc (@Thread.tau_step _) e1_tgt e2_tgt)
        (CONS: Local.promise_consistent (Thread.local e2_tgt)):
    exists e2_src,
      (<<STEP_SRC: dsteps MachineEvent.silent e1_src e2_src>>) /\
      (<<LD2: lower_delayed_thread e2_src e2_tgt>>).
  Proof.
    exploit rtc_tau_step_nrp_steps; eauto. i.
    exploit ld_nrp_steps_dsteps; eauto. i. des. subst. eauto.
  Qed.

  Lemma ld_plus_step_dsteps
        e1_src e1_tgt pf e_tgt e2_tgt e3_tgt
        (LD1: lower_delayed_thread e1_src e1_tgt)
        (WF1_TGT: Local.wf (Thread.local e1_tgt) (Thread.memory e1_tgt))
        (SC1_TGT: Memory.closed_timemap (Thread.sc e1_tgt) (Thread.memory e1_tgt))
        (CLOSED1_TGT: Memory.closed (Thread.memory e1_tgt))
        (STEPS: rtc (@Thread.tau_step _) e1_tgt e2_tgt)
        (STEP: Thread.step pf e_tgt e2_tgt e3_tgt)
        (CONS: Local.promise_consistent (Thread.local e3_tgt)):
    exists e_src e3_src,
      (<<STEP_SRC: dsteps e_src e1_src e3_src>>) /\
      (<<EVENT: e_src = ThreadEvent.get_machine_event e_tgt>>) /\
      (<<LD2: lower_delayed_thread e3_src e3_tgt>>).
  Proof.
    exploit plus_step_nrp_steps; eauto. i.
    exploit ld_nrp_steps_dsteps; eauto.
  Qed.

  Lemma ld_future
        e_src e_tgt
        sc_src mem_src sc_tgt mem_tgt
        (LD: lower_delayed_thread e_src e_tgt)
        (SC: TimeMap.le sc_src sc_tgt)
        (MEM: lower_memory mem_src mem_tgt)
        (MEM_FUTURE_SRC: Memory.future (Thread.memory e_src) mem_src)
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

  Lemma ld_cap
        e_src e_tgt
        cap_src cap_tgt
        (LD: lower_delayed_thread e_src e_tgt)
        (MEM_TGT: Memory.closed (Thread.memory e_tgt))
        (CAP_SRC: Memory.cap (Thread.memory e_src) cap_src)
        (CAP_TGT: Memory.cap (Thread.memory e_tgt) cap_tgt):
    (<<LD_CAP: lower_delayed_thread
                 (Thread.mk _ (Thread.state e_src) (Thread.local e_src) (Thread.sc e_src) cap_src)
                 (Thread.mk _ (Thread.state e_tgt) (Thread.local e_tgt) (Thread.sc e_tgt) cap_tgt)>>).
  Proof.
    inv LD.
    destruct e_src as [st_src lc_src sc_src mem_src],
             e_lower as [st_lower lc_lower sc_lower mem_lower],
             e_tgt as [st_tgt lc_tgt sc_tgt mem_tgt].
    inv LOWER. inv DELAYED. ss. subst.
    exploit lower_memory_cap; try exact MEMORY; eauto; try apply DELAYED0. i.
    econs.
    - instantiate (1 := Thread.mk _ st_tgt lc_lower sc_lower cap_src).
      econs; ss.
    - econs; ss.
      eapply delayed_future; eauto.
      + eapply Local.cap_wf; eauto. apply DELAYED0.
      + eapply Memory.cap_closed_timemap; eauto. apply DELAYED0.
      + eapply Memory.cap_closed; eauto. apply DELAYED0.
      + eapply Memory.cap_future_weak; eauto. apply DELAYED0.
  Qed.

  Lemma ld_consistent
        e_src e_tgt
        (LD: lower_delayed_thread e_src e_tgt)
        (WF_TGT: Local.wf (Thread.local e_tgt) (Thread.memory e_tgt))
        (SC_TGT: Memory.closed_timemap (Thread.sc e_tgt) (Thread.memory e_tgt))
        (CLOSED_TGT: Memory.closed (Thread.memory e_tgt))
        (CONSISTENT_TGT: Thread.consistent e_tgt):
    (<<CONSISTENT_SRC: delayed_consistent e_src>>).
  Proof.
    ii. exploit Memory.cap_exists; try apply CLOSED_TGT. i. des.
    exploit ld_cap; try exact LD; eauto. i. des.
    exploit CONSISTENT_TGT; eauto. unfold Thread.steps_failure. i. des.
    { exploit ld_plus_step_dsteps; try exact x0; eauto; ss.
      { eapply Local.cap_wf; eauto. }
      { eapply Memory.cap_closed_timemap; eauto. }
      { eapply Memory.cap_closed; eauto. }
      { inv STEP_FAILURE; inv STEP; ss. inv LOCAL; ss; inv LOCAL0; ss. }
      i. des.
      rewrite EVENT_FAILURE in *. subst.
      esplits; eauto.
    }
    { exploit ld_rtc_tau_step_dsteps; try exact x0; eauto; ss.
      { eapply Local.cap_wf; eauto. }
      { eapply Memory.cap_closed_timemap; eauto. }
      { eapply Memory.cap_closed; eauto. }
      { ii. rewrite PROMISES in *. rewrite Memory.bot_get in *. ss. }
      i. des.
      esplits; eauto. right.
      inv LD2. inv DELAYED.
      unfold delayed in *. des.
      destruct e2_src, e_lower. ss. subst.
      esplits; eauto. ss.
      inv LOCAL. ss. inv LOWER. ss. inv LOCAL. ss.
      rewrite <- H in *. ss.
    }
  Qed.

  Lemma delayed_consistent_consistent
        e
        (CONSISTENT: delayed_consistent e):
    (<<CONSISTENT: Thread.consistent e>>).
  Proof.
    ii. exploit CONSISTENT; eauto. i. des.
    { left.
      exploit dsteps_plus_step; eauto. i. des; subst; ss.
      replace pf with true in *; cycle 1.
      { inv STEP; inv STEP0; ss. }
      unfold Thread.steps_failure. esplits; eauto.
    }
    { right.
      exploit dsteps_rtc_tau_step; eauto. i.
      esplits; try exact PROMISES.
      etrans; eauto.
      eapply rtc_implies; try exact STEPS.
      i. inv H. inv TSTEP. econs; eauto. econs. econs 2. eauto.
    }
  Qed.

  Lemma ld_terminal
        e_src e_tgt
        (LD: lower_delayed_thread e_src e_tgt)
        (TERMINAL: Language.is_terminal _ (Thread.state e_tgt)):
    exists e1_src,
      (<<STEP: rtc (tau lower_step) e_src e1_src>>) /\
      (<<TERMINAL_SRC: Language.is_terminal _ (Thread.state e1_src)>>) /\
      (<<PROMISES: Local.promises (Thread.local e1_src) = Local.promises (Thread.local e_tgt)>>) /\
      (<<SC_LOWER: TimeMap.le (Thread.sc e1_src) (Thread.sc e_tgt)>>) /\
      (<<MEM_LOWER: lower_memory (Thread.memory e1_src) (Thread.memory e_tgt)>>).
  Proof.
    inv LD.
    destruct e_src as [st_src lc_src sc_src mem_src],
             e_lower as [st_lower lc_lower sc_lower mem_lower],
             e_tgt as [st_tgt lc_tgt sc_tgt mem_tgt].
    inv LOWER. inv DELAYED. ss. subst.
    unfold delayed in *. des.
    esplits; try exact STEPS; ss.
    - inv LOCAL. ss. inv LOCAL2. ss.
    - etrans; eauto.
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

  Variant terminal_step: forall (tid: Ident.t) (c1 c2: Configuration.t), Prop :=
  | terminal_step_intro
      tid c1 lang st1 lc1 st2 lc2 sc2 mem2
      (TID: IdentMap.find tid (Configuration.threads c1) = Some (existT _ lang st1, lc1))
      (STEPS: rtc (tau lower_step)
                  (Thread.mk _ st1 lc1 (Configuration.sc c1) (Configuration.memory c1))
                  (Thread.mk _ st2 lc2 sc2 mem2))
      (TERMINAL: Language.is_terminal _ st2)
      (PROMISES: Local.promises lc2 = Memory.bot):
      terminal_step tid c1
                    (Configuration.mk
                       (IdentMap.add tid (existT _ _ st2, lc2) (Configuration.threads c1))
                       sc2 mem2)
  .

  Inductive terminal_steps: forall (tids: list Ident.t) (c1 c2: Configuration.t), Prop :=
  | terminal_steps_nil
      c:
      terminal_steps [] c c
  | terminal_steps_cons
      tid c1 c2 tids c3
      (NOTIN: ~ List.In tid tids)
      (STEP: terminal_step tid c1 c2)
      (STEPS: terminal_steps tids c2 c3):
      terminal_steps (tid :: tids) c1 c3
  .

  Lemma step_step
        e tid c1 c2
        (STEP: step e tid c1 c2):
    Configuration.opt_step e tid c1 c2.
  Proof.
    inv STEP.
    exploit dsteps_plus_step; eauto. i. des.
    - inv x1. destruct c1 as [threads sc mem]. ss.
      rewrite IdentMap.gsident; eauto.
    - subst. econs 2. econs; eauto. i.
      hexploit CONSISTENT; eauto. i.
      eapply delayed_consistent_consistent; eauto.
  Qed.

  Lemma terminal_step_step
        tid c1 c2
        (STEP: terminal_step tid c1 c2):
    Configuration.opt_step MachineEvent.silent tid c1 c2.
  Proof.
    inv STEP.
    exploit rtc_tail; eauto. i. des.
    - inv x1. inv TSTEP. destruct a2. ss.
      rewrite <- EVENT.
      econs 2. econs; [eauto|..].
      + eapply rtc_implies; try eapply x0.
        i. inv H. inv TSTEP. econs; try exact EVENT0. econs. econs 2. eauto.
      + econs 2. eauto.
      + ii. ss. right. esplits; eauto.
    - inv x0. destruct c1 as [threads sc mem]. ss.
      rewrite IdentMap.gsident; eauto.
  Qed.

  Variant ld_sl (sc_src sc_tgt: TimeMap.t) (mem_src mem_tgt: Memory.t):
    forall (sl_src sl_tgt: {lang: language & Language.state lang} * Local.t), Prop :=
  | ld_sl_intro
      lang st_src lc_src st_tgt lc_tgt
      (LD: lower_delayed_thread (Thread.mk lang st_src lc_src sc_src mem_src)
                                (Thread.mk lang st_tgt lc_tgt sc_tgt mem_tgt)):
    ld_sl sc_src sc_tgt mem_src mem_tgt
          (existT _ lang st_src, lc_src)
          (existT _ lang st_tgt, lc_tgt)
  .

  Variant ld_conf: forall (c_src c_tgt: Configuration.t), Prop :=
  | ld_conf_intro
      ths_src sc_src mem_src
      ths_tgt sc_tgt mem_tgt
      (THS: forall tid,
          option_rel
            (ld_sl sc_src sc_tgt mem_src mem_tgt)
            (IdentMap.find tid ths_src)
            (IdentMap.find tid ths_tgt)):
    ld_conf (Configuration.mk ths_src sc_src mem_src)
            (Configuration.mk ths_tgt sc_tgt mem_tgt)
  .

  Lemma ld_conf_refl
        c
        (WF: Configuration.wf c):
    ld_conf c c.
  Proof.
    destruct c. econs. i.
    destruct (IdentMap.find tid threads) as [[[lang st] lc]|] eqn:FIND; ss.
    inv WF. ss.
    inv WF0. exploit THREADS; eauto. i.
    econs. eapply lower_delayed_thread_refl; eauto.
  Qed.

  Lemma ld_conf_step_aux
        c1_src c1_tgt
        e tid c2_tgt
        (LD: ld_conf c1_src c1_tgt)
        (WF1_SRC: Configuration.wf c1_src)
        (WF1_TGT: Configuration.wf c1_tgt)
        (STEP: Configuration.step e tid c1_tgt c2_tgt):
    exists c2_src lang st2_src lc2_src st2_tgt lc2_tgt,
      (<<STEP_SRC: step e tid c1_src c2_src>>) /\
      (<<FIND_SRC: IdentMap.find tid (Configuration.threads c2_src) =
                   Some (existT _ lang st2_src, lc2_src)>>) /\
      (<<FIND_TGT: IdentMap.find tid (Configuration.threads c2_tgt) =
                   Some (existT _ lang st2_tgt, lc2_tgt)>>) /\
      (<<LD_THREAD: lower_delayed_thread
                      (Thread.mk _ st2_src lc2_src (Configuration.sc c2_src) (Configuration.memory c2_src))
                      (Thread.mk _ st2_tgt lc2_tgt (Configuration.sc c2_tgt) (Configuration.memory c2_tgt))>>).
  Proof.
    destruct c1_src as [ths1_src sc1_src mem1_src],
             c1_tgt as [ths1_tgt sc1_tgt mem1_tgt].
    inv LD. inv STEP. ss.
    specialize (THS tid). rewrite TID in THS.
    destruct (IdentMap.find tid ths1_src) as [[[lang_src st1_src] lc1_src]|] eqn:FIND_SRC; ss.
    inv THS. Configuration.simplify.
    inv WF1_SRC. ss.
    inv WF. exploit THREADS; eauto. intro WF1_SRC.
    clear DISJOINT THREADS.
    inv WF1_TGT. ss.
    inv WF. exploit THREADS; eauto. intro WF1_TGT.
    clear DISJOINT THREADS.
    exploit ld_plus_step_dsteps; try exact LD; eauto.
    { destruct (classic (ThreadEvent.get_machine_event e0 = MachineEvent.failure)).
      { inv STEP0; inv STEP; ss. inv LOCAL; ss; inv LOCAL0; ss. }
      { exploit Thread.rtc_tau_step_future; try exact STEPS; eauto. s. i. des.
        exploit Thread.step_future; try exact STEP0; eauto. s. i. des.
        hexploit consistent_promise_consistent; try eapply EVENT; eauto.
      }
    }
    i. des. subst.
    destruct e3_src as [st3_src lc3_src sc3_src mem3_src].
    esplits.
    - econs; eauto. i.
      exploit Thread.rtc_tau_step_future; try exact STEPS; eauto. s. i. des.
      exploit Thread.step_future; try exact STEP0; eauto. s. i. des.
      eapply ld_consistent; eauto.
    - ss. rewrite IdentMap.gss. eauto.
    - rewrite IdentMap.gss. eauto.
    - ss.
  Qed.

  Lemma ld_lower
        lang e_src e_tgt
        (LD: @lower_delayed_thread lang e_src e_tgt):
    (<<SC_LOWER: TimeMap.le (Thread.sc e_src) (Thread.sc e_tgt)>>) /\
    (<<MEM_LOWER: lower_memory (Thread.memory e_src) (Thread.memory e_tgt)>>).
  Proof.
    inv LD.
    destruct e_src, e_tgt, e_lower. ss.
    inv LOWER. inv DELAYED. ss. subst.
    splits; auto.
  Qed.

  Lemma ld_conf_step
        c1_src c1_tgt
        e tid c2_tgt
        (LD1: ld_conf c1_src c1_tgt)
        (WF1_SRC: Configuration.wf c1_src)
        (WF1_TGT: Configuration.wf c1_tgt)
        (STEP: Configuration.step e tid c1_tgt c2_tgt):
    exists c2_src,
      (<<STEP_SRC: step e tid c1_src c2_src>>) /\
      (<<LD2: ld_conf c2_src c2_tgt>>).
  Proof.
    exploit ld_conf_step_aux; eauto. i. des.
    esplits; eauto.
    exploit Configuration.opt_step_future;
      try eapply step_step; try exact STEP_SRC; eauto. i. des.
    inv STEP. ss. inv STEP_SRC. ss.
    econs. i. do 2 rewrite IdentMap.gsspec.
    condtac; ss.
    { subst. Configuration.simplify. }
    { clear FIND_SRC FIND_TGT.
      clear TID STEPS STEP0 EVENT TID0 DSTEPS CONSISTENT COND.
      clear pf st1 lc1 e2 st0 lc0.
      destruct c1_src as [ths1_src sc1_src mem1_src],
               c1_tgt as [ths1_tgt sc1_tgt mem1_tgt].
      inv LD1. ss.
      specialize (THS tid0).
      destruct (IdentMap.find tid0 ths1_src) as [[[lang_src st_src] lc_src]|] eqn:FIND_SRC; ss.
      destruct (IdentMap.find tid0 ths1_tgt) as [[[lang_tgt st_tgt] lc_tgt]|] eqn:FIND_TGT; ss.
      inv THS. Configuration.simplify. econs.
      exploit ld_lower; try exact LD_THREAD. s. i. des.
      hexploit ld_future; try exact LD; try exact SC_LOWER; try exact MEM_LOWER; s; eauto.
      - inv WF2. inv WF. ss.
        eapply THREADS.
        rewrite IdentMap.gso; eauto.
      - inv WF2. ss.
      - inv WF2. ss.
    }
  Qed.

  Lemma ld_conf_terminal
        c_src c_tgt
        (LD: ld_conf c_src c_tgt)
        (WF_SRC: Configuration.wf c_src)
        (TERMINAL: Configuration.is_terminal c_tgt):
    exists c1_src,
      (<<STEP: terminal_steps
                 (IdentSet.elements (Threads.tids (Configuration.threads c_src)))
                 c_src c1_src>>) /\
      (<<TERMINAL: Configuration.is_terminal c1_src>>).
  Proof.
    destruct c_src as [ths_src sc_src mem_src],
             c_tgt as [ths_tgt sc_tgt mem_tgt]. ss.
    remember (Threads.tids ths_src) as tids eqn:TIDS_SRC.
    assert (NOTIN: forall tid lang_src st_src lc_src
                     (FIND: IdentMap.find tid ths_src = Some (existT _ lang_src st_src, lc_src))
                     (TID: ~ List.In tid (IdentSet.elements tids)),
               Language.is_terminal _ st_src /\ Local.is_terminal lc_src).
    { i. destruct (IdentSet.mem tid tids) eqn:MEM.
      - exfalso. apply TID. rewrite IdentSet.mem_spec in MEM.
        rewrite <- IdentSet.elements_spec1 in MEM.
        clear - MEM. induction MEM; [econs 1|econs 2]; auto.
      - rewrite TIDS_SRC in MEM. rewrite Threads.tids_o in MEM.
        destruct (IdentMap.find tid ths_src) eqn:IFIND; [inv MEM|]. ss.
    }
    assert (IN: forall tid (TID: List.In tid (IdentSet.elements tids)),
               exists lang st_src lc_src st_tgt lc_tgt,
                 (<<FIND_SRC: IdentMap.find tid ths_src = Some (existT _ lang st_src, lc_src)>>) /\
                 (<<FIND_TGT: IdentMap.find tid ths_tgt = Some (existT _ lang st_tgt, lc_tgt)>>) /\
                 (<<LD_THREAD: lower_delayed_thread
                                 (Thread.mk _ st_src lc_src sc_src mem_src)
                                 (Thread.mk _ st_tgt lc_tgt sc_tgt mem_tgt)>>)).
    { i. destruct (IdentSet.mem tid tids) eqn:MEM.
      - subst. dup MEM. rewrite Threads.tids_o in MEM0.
        inv LD. specialize (THS tid).
        destruct (IdentMap.find tid ths_src) as [[[lang_src st_src] lc_src]|] eqn:FIND_SRC; ss.
        destruct (IdentMap.find tid ths_tgt) as [[[lang_tgt st_tgt] lc_tgt]|] eqn:FIND_TGT; ss.
        inv THS. Configuration.simplify.
        esplits; eauto.
      - exfalso. subst.
        assert (SetoidList.InA eq tid (IdentSet.elements (Threads.tids ths_src))).
        { clear - TID. induction (IdentSet.elements (Threads.tids ths_src)); eauto. }
        rewrite IdentSet.elements_spec1 in H.
        rewrite <- IdentSet.mem_spec in H. congr.
    }
    assert (TIDS_MEM: forall tid, List.In tid (IdentSet.elements tids) -> IdentSet.mem tid tids = true).
    { i. rewrite IdentSet.mem_spec.
      rewrite <- IdentSet.elements_spec1.
      eapply SetoidList.In_InA; auto.
    }
    assert (NODUP: List.NoDup (IdentSet.elements tids)).
    { specialize (IdentSet.elements_spec2w tids). i.
      clear - H. induction H; econs; eauto.
    }
    clear LD.
    revert NOTIN IN TIDS_MEM NODUP.
    revert ths_src sc_src mem_src WF_SRC TIDS_SRC.
    induction (IdentSet.elements tids); i.
    { esplits; [econs 1|]. ii. eauto. }
    exploit (IN a); try by econs 1. i. des.
    exploit TERMINAL; eauto. i. des. inv THREAD.
    exploit ld_terminal; try exact LD_THREAD; eauto. s. i. des.
    rewrite PROMISES in *.
    destruct e1_src as [st1 lc1 sc1 mem1]. ss.
    assert (STEP_SRC: terminal_step
                        a
                        (Configuration.mk ths_src sc_src mem_src)
                        (Configuration.mk
                           (IdentMap.add a (existT _ _ st1, lc1) ths_src) sc1 mem1)).
    { econs; eauto. }
    exploit Configuration.opt_step_future;
      try eapply terminal_step_step; try eapply STEP_SRC; eauto. s. i. des.
    exploit IHl; try exact WF2; ss; eauto; i.
    { rewrite Threads.tids_add. rewrite IdentSet.add_mem; eauto. }
    { rewrite IdentMap.gsspec in FIND. revert FIND. condtac; ss; i.
      - subst. Configuration.simplify.
      - eapply NOTIN; eauto. ii. des; ss. subst. ss.
    }
    { exploit IN; eauto. i. des. inv NODUP.
      rewrite IdentMap.gso; try by (ii; subst; ss).
      esplits; eauto.
      exploit ld_future; try exact LD_THREAD0; [..|eauto]; ss; try apply WF2.
      inv WF2. inv WF. ss.
      eapply (THREADS tid).
      rewrite IdentMap.gso; eauto. ii. subst. ss.
    }
    { inv NODUP. ss. }
    des. esplits; [|eauto].
    econs; eauto. inv NODUP. ss.
  Qed.

  Inductive delayed_behaviors:
    forall (conf:Configuration.t) (b:list Event.t) (f: bool), Prop :=
  | delayed_behaviors_nil
      c1 c2
      (STEP: terminal_steps
               (IdentSet.elements (Threads.tids (Configuration.threads c1)))
               c1 c2)
      (TERMINAL: Configuration.is_terminal c2):
      delayed_behaviors c1 nil true
  | delayed_behaviors_syscall
      e1 e2 tid c1 c2 beh f
      (STEP: step (MachineEvent.syscall e2) tid c1 c2)
      (NEXT: delayed_behaviors c2 beh f)
      (EVENT: Event.le e1 e2):
      delayed_behaviors c1 (e1::beh) f
  | delayed_behaviors_failure
      tid c1 c2 beh f
      (STEP: step MachineEvent.failure tid c1 c2):
      delayed_behaviors c1 beh f
  | delayed_behaviors_tau
      tid c1 c2 beh f
      (STEP: step MachineEvent.silent tid c1 c2)
      (NEXT: delayed_behaviors c2 beh f):
      delayed_behaviors c1 beh f
  | delayed_behaviors_partial_term
      c:
      delayed_behaviors c [] false
  .

  Lemma ld_conf_behavior
        c_src c_tgt
        (LD: ld_conf c_src c_tgt)
        (WF_SRC: Configuration.wf c_src)
        (WF_tgt: Configuration.wf c_tgt):
    behaviors Configuration.step c_tgt <2= delayed_behaviors c_src.
  Proof.
    i. revert c_src LD WF_SRC. induction PR; i.
    - exploit ld_conf_terminal; eauto. i. des.
      econs 1; eauto.
    - exploit ld_conf_step; eauto. i. des.
      exploit Configuration.opt_step_future;
        try eapply step_step; try exact STEP_SRC; eauto. i. des.
      exploit Configuration.step_future; try exact STEP; eauto. i. des.
      econs 2; eauto.
    - exploit ld_conf_step; eauto. i. des.
      econs 3; eauto.
    - exploit ld_conf_step; eauto. i. des.
      exploit Configuration.opt_step_future;
        try eapply step_step; try exact STEP_SRC; eauto. i. des.
      exploit Configuration.step_future; try exact STEP; eauto. i. des.
      econs 4; eauto.
    - econs 5.
  Qed.

  Lemma delayed_refinement
        c
        (WF: Configuration.wf c):
    behaviors Configuration.step c <2= delayed_behaviors c.
  Proof.
    exploit ld_conf_refl; eauto. i.
    eapply ld_conf_behavior; eauto.
  Qed.
End DConfiguration.



Lemma dstep_rtc_all_step lang e th0 th1
      (STEP: dstep e th0 th1)
  :
    rtc (@Thread.all_step lang) th0 th1.
Proof.
  inv STEP. etrans.
  { eapply rtc_implies; [|eapply PROMISES].
    i. inv H. inv TSTEP. econs; eauto.
  }
  etrans.
  { eapply rtc_implies; [|eapply LOWERS].
    i. inv H. inv TSTEP. econs; eauto. econs; eauto. econs 2; eauto.
  }
  econs 2; [|refl]. econs; eauto. econs; eauto.
Qed.

Lemma rtc_tau_dstep_rtc_all_step lang th0 th1
      (STEPS: rtc (tau (@dstep lang)) th0 th1)
  :
    rtc (@Thread.all_step lang) th0 th1.
Proof.
  induction STEPS.
  { refl. }
  etrans; [|eauto]. inv H.
  eapply dstep_rtc_all_step; eauto.
Qed.

Lemma dsteps_rtc_all_step lang e th0 th1
      (STEPS: dsteps e th0 th1)
  :
    rtc (@Thread.all_step lang) th0 th1.
Proof.
  inv STEPS.
  { etrans.
    { eapply rtc_tau_dstep_rtc_all_step; eauto. }
    { eapply rtc_implies; [|eapply PROMISES].
      i. inv H. inv TSTEP. econs; eauto.
    }
  }
  { etrans.
    { eapply rtc_tau_dstep_rtc_all_step; eauto. }
    { eapply dstep_rtc_all_step; eauto. }
  }
Qed.

Lemma delayed_consistent_promise_consistent lang (th: Thread.t lang)
      (CONSISTENT: delayed_consistent th)
      (MEM: Memory.closed th.(Thread.memory))
      (LOCAL: Local.wf th.(Thread.local) th.(Thread.memory))
      (SC: Memory.closed_timemap th.(Thread.sc) th.(Thread.memory))
  :
    Local.promise_consistent th.(Thread.local).
Proof.
  hexploit Memory.cap_exists; eauto. i. des.
  hexploit Local.cap_wf; eauto. i.
  hexploit Memory.cap_closed_timemap; eauto. i.
  hexploit Memory.cap_closed; eauto. i.
  exploit CONSISTENT; eauto. i. des.
  { pose proof (dsteps_rtc_all_step DSTEPS) as STEPS.
    eapply rtc_all_step_promise_consistent in STEPS; eauto; ss.
    inv DSTEPS; ss. inv DSTEP. inv STEP_RELEASE; inv STEP; ss.
    inv LOCAL0; ss; inv LOCAL1; ss.
  }
  { pose proof (dsteps_rtc_all_step DSTEPS) as STEPS.
    eapply rtc_all_step_promise_consistent in STEPS; eauto; ss.
    eapply Local.bot_promise_consistent in PROMISES; eauto.
  }
Qed.

Lemma DConfiguration_step_future c0 c1 e tid
      (STEP: DConfiguration.step e tid c0 c1)
      (WF: Configuration.wf c0)
  :
  (<<WF2: Configuration.wf c1>>) /\
  (<<SC_FUTURE: TimeMap.le (Configuration.sc c0) (Configuration.sc c1)>>) /\
  (<<MEM_FUTURE: Memory.future (Configuration.memory c0) (Configuration.memory c1)>>).
Proof.
Admitted.
