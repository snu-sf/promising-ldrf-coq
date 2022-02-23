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
Require Import Delayed.

Set Implicit Arguments.
Set Nested Proofs Allowed.


Section DStep.
  Variable lang: language.

  Variant delayed_step (e: ThreadEvent.t) (e1 e4: Thread.t lang): Prop :=
  | delayed_step_intro
      e2 e3 pf
      (PROMISES: rtc (tau (@pred_step is_promise _)) e1 e2)
      (LOWERS: rtc (tau lower_step) e2 e3)
      (STEP_RELEASE: Thread.step pf e e3 e4)
      (EVENT_RELEASE: release_event e)
  .

  Variant delayed_steps: forall (e: MachineEvent.t) (e1 e2: Thread.t lang), Prop :=
  | delayed_steps_promises
      e1 e2 e3
      (DSTEPS: rtc (tau delayed_step) e1 e2)
      (PROMISES: rtc (tau (@pred_step is_promise _)) e2 e3):
    delayed_steps MachineEvent.silent e1 e3
  | delayed_steps_step
      e te e1 e2 e3
      (DSTEPS: rtc (tau (@pred_step is_promise _)) e1 e2)
      (DSTEP: delayed_step te e2 e3)
      (EVENT: e = ThreadEvent.get_machine_event te):
    delayed_steps e e1 e3
  .

  Definition delayed_consistent (e1: Thread.t lang): Prop :=
    forall mem1 (CAP: Memory.cap e1.(Thread.memory) mem1),
    exists e e2,
      (<<DSTEPS: delayed_steps
                   e (Thread.mk _ (Thread.state e1) (Thread.local e1) (Thread.sc e1) mem1) e2>>) /\
      ((<<FAILURE: e = MachineEvent.failure>>) \/
       (<<SILENT: e = MachineEvent.silent>>) /\
         (<<PROMISES: Local.promises (Thread.local e2) = Memory.bot>>)).

  Variant non_release_step (e: ThreadEvent.t) (e1 e2: Thread.t lang): Prop :=
  | non_release_step_intro
      pf
      (STEP: Thread.step pf e e1 e2)
      (RELEASE: ~ release_event e)
  .

  Variant non_release_plus_step (e: ThreadEvent.t) (e1 e3: Thread.t lang): Prop :=
  | non_release_plus_step_intro
      e2 pf
      (STEPS: rtc (tau non_release_step) e1 e2)
      (STEP: Thread.step pf e e2 e3)
      (RELEASE: release_event e)
  .

  Variant steps: forall (e: MachineEvent.t) (e1 e2: Thread.t lang), Prop :=
  | steps_non_release
      e1 e2 e3
      (STEPS: rtc (tau non_release_plus_step) e1 e2)
      (NSTEPS: rtc (tau non_release_step) e2 e3):
    steps MachineEvent.silent e1 e3
  | steps_release
      e e1 e2 e3
      (STEPS: rtc (tau non_release_plus_step) e1 e2)
      (STEP: non_release_plus_step e e2 e3):
    steps (ThreadEvent.get_machine_event e) e1 e3
  .

  Lemma non_release_silent
        e
        (RELEASE: ~ release_event e):
    ThreadEvent.get_machine_event e = MachineEvent.silent.
  Proof.
    destruct e; ss.
  Qed.

  Lemma plus_step_steps
        pf e e1 e2 e3
        (STEPS: rtc (@Thread.tau_step _) e1 e2)
        (STEP: Thread.step pf e e2 e3):
    steps (ThreadEvent.get_machine_event e) e1 e3.
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

  Variant delayed_thread fin (e_src e_tgt: Thread.t lang): Prop :=
    | delayed_thread_intro
        lc_lower
        (LOWER_LC: lower_local lc_lower (Thread.local e_tgt))
        (LOWER_SC: TimeMap.le (Thread.sc e_src) (Thread.sc e_tgt))
        (LOWER_MEM: lower_memory (Thread.memory e_src) (Thread.memory e_tgt))
        (DELAYED: delayed (Thread.state e_src) (Thread.state e_tgt)
                          (Thread.local e_src) lc_lower
                          (Thread.sc e_src) (Thread.memory e_src) fin)
  .

  Definition committed_thread (e1 e2: Thread.t lang) :=
    committed (Thread.memory e1) (Local.promises (Thread.local e1))
              (Thread.memory e2) (Local.promises (Thread.local e2)).

  Lemma non_release_step_delayed
        e1_src
        fin e_tgt e1_tgt e2_tgt
        (DELAYED: delayed_thread fin e1_src e1_tgt)
        (STEP: non_release_step e_tgt e1_tgt e2_tgt)
        (CONS: Local.promise_consistent (Thread.local e2_tgt)):
    exists e2_src,
      (<<PROMISES: rtc (tau (@pred_step is_promise _)) e1_src e2_src>>) /\
        (<<DELAYED: delayed_thread (fin \4/ committed_thread e1_src e2_src) e2_src e2_tgt>>).
  Proof.
  Admitted.
End DStep.

Module DConfiguration.
  Variant step: forall (e: MachineEvent.t) (tid: Ident.t) (c1 c2: Configuration.t), Prop :=
  | step_intro
      e tid c1 lang st1 lc1 st2 lc2 sc2 mem2
      (TID: IdentMap.find tid (Configuration.threads c1) = Some (existT _ lang st1, lc1))
      (DSTEPS: delayed_steps e (Thread.mk _ st1 lc1 (Configuration.sc c1) (Configuration.memory c1))
                             (Thread.mk _ st2 lc2 sc2 mem2))
      (CONSISTENT: e <> MachineEvent.failure ->
                   delayed_consistent (Thread.mk _ st2 lc2 sc2 mem2)):
      step e tid c1
           (Configuration.mk (IdentMap.add tid (existT _ _ st2, lc2) (Configuration.threads c1)) sc2 mem2)
  .
End DConfiguration.
