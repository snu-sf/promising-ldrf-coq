Require Import Omega.
Require Import Bool.
Require Import RelationClasses.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Language.

Require Import Event.
Require Import Time.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.

Require Import AMemory.
Require Import ATView.
Require Import ALocal.

Set Implicit Arguments.


Module AThread.
  Section AThread.
    Variable (lang:language).

    Inductive promise_step (pf:bool): forall (e:ThreadEvent.t) (e1 e2:Thread.t lang), Prop :=
    | promise_step_intro
        st lc1 sc1 mem1
        loc from to msg kind
        lc2 mem2
        (LOCAL: ALocal.promise_step lc1 mem1 loc from to msg lc2 mem2 kind)
        (PF: pf = orb (andb (Memory.op_kind_is_lower_concrete kind) (Message.is_released_none msg))
                      (Memory.op_kind_is_cancel kind)):
        promise_step pf (ThreadEvent.promise loc from to msg kind) (Thread.mk lang st lc1 sc1 mem1) (Thread.mk lang st lc2 sc1 mem2)
    .

    (* NOTE: Syscalls act like a SC fence. *)
    Inductive program_step (e:ThreadEvent.t): forall (e1 e2:Thread.t lang), Prop :=
    | program_step_intro
        st1 lc1 sc1 mem1
        st2 lc2 sc2 mem2
        (STATE: lang.(Language.step) (ThreadEvent.get_program_event e) st1 st2)
        (LOCAL: ALocal.program_step e lc1 sc1 mem1 lc2 sc2 mem2):
        program_step e (Thread.mk lang st1 lc1 sc1 mem1) (Thread.mk lang st2 lc2 sc2 mem2)
    .
    Hint Constructors program_step.

    Inductive step: forall (pf:bool) (e:ThreadEvent.t) (e1 e2:Thread.t lang), Prop :=
    | step_promise
        pf e e1 e2
        (STEP: promise_step pf e e1 e2):
        step pf e e1 e2
    | step_program
        e e1 e2
        (STEP: program_step e e1 e2):
        step true e e1 e2
    .
    Hint Constructors step.

    Inductive step_allpf (e:ThreadEvent.t) (e1 e2:Thread.t lang): Prop :=
    | step_nopf_intro
        pf
        (STEP: step pf e e1 e2)
    .
    Hint Constructors step_allpf.

    Lemma allpf pf: step pf <3= step_allpf.
    Proof.
      i. econs. eauto.
    Qed.

    Definition pf_tau_step := tau (step true).
    Hint Unfold pf_tau_step.

    Definition tau_step := tau step_allpf.
    Hint Unfold tau_step.

    Definition all_step := union step_allpf.
    Hint Unfold all_step.

    Inductive opt_step: forall (e:ThreadEvent.t) (e1 e2:Thread.t lang), Prop :=
    | step_none
        e:
        opt_step ThreadEvent.silent e e
    | step_some
        pf e e1 e2
        (STEP: step pf e e1 e2):
        opt_step e e1 e2
    .
    Hint Constructors opt_step.

    Definition steps_failure (e1: Thread.t lang): Prop :=
      exists e2 e3,
        <<STEPS: rtc tau_step e1 e2>> /\
        <<FAILURE: step true ThreadEvent.failure e2 e3>>.
    Hint Unfold steps_failure.

    Definition consistent (e:Thread.t lang): Prop :=
      forall mem1 sc1
        (CAP: Memory.cap e.(Thread.memory) mem1)
        (SC_MAX: Memory.max_concrete_timemap mem1 sc1),
        <<FAILURE: steps_failure (Thread.mk lang e.(Thread.state) e.(Thread.local) sc1 mem1)>> \/
        exists e2,
          <<STEPS: rtc tau_step (Thread.mk lang e.(Thread.state) e.(Thread.local) sc1 mem1) e2>> /\
          <<PROMISES: e2.(Thread.local).(Local.promises) = Memory.bot>>.


    (* step_future *)

    Lemma promise_step_future
          pf e e1 e2
          (STEP: promise_step pf e e1 e2)
          (WF1: Local.wf e1.(Thread.local) e1.(Thread.memory))
          (SC1: Memory.closed_timemap e1.(Thread.sc) e1.(Thread.memory))
          (CLOSED1: Memory.closed e1.(Thread.memory)):
      <<WF2: Local.wf e2.(Thread.local) e2.(Thread.memory)>> /\
      <<SC2: Memory.closed_timemap e2.(Thread.sc) e2.(Thread.memory)>> /\
      <<CLOSED2: Memory.closed e2.(Thread.memory)>> /\
      <<TVIEW_FUTURE: TView.le e1.(Thread.local).(Local.tview) e2.(Thread.local).(Local.tview)>> /\
      <<SC_FUTURE: TimeMap.le e1.(Thread.sc) e2.(Thread.sc)>> /\
      <<MEM_FUTURE: Memory.future e1.(Thread.memory) e2.(Thread.memory)>>.
    Proof.
      inv STEP. ss.
      exploit ALocal.promise_step_future; eauto. i. des.
      splits; eauto. refl.
    Qed.

    Lemma program_step_future
          e e1 e2
          (STEP: program_step e e1 e2)
          (WF1: Local.wf e1.(Thread.local) e1.(Thread.memory))
          (SC1: Memory.closed_timemap e1.(Thread.sc) e1.(Thread.memory))
          (CLOSED1: Memory.closed e1.(Thread.memory)):
      <<WF2: Local.wf e2.(Thread.local) e2.(Thread.memory)>> /\
      <<SC2: Memory.closed_timemap e2.(Thread.sc) e2.(Thread.memory)>> /\
      <<CLOSED2: Memory.closed e2.(Thread.memory)>> /\
      <<TVIEW_FUTURE: TView.le e1.(Thread.local).(Local.tview) e2.(Thread.local).(Local.tview)>> /\
      <<SC_FUTURE: TimeMap.le e1.(Thread.sc) e2.(Thread.sc)>> /\
      <<MEM_FUTURE: Memory.future e1.(Thread.memory) e2.(Thread.memory)>>.
    Proof.
      inv STEP. ss. eapply ALocal.program_step_future; eauto.
    Qed.

    Lemma step_future
          pf e e1 e2
          (STEP: step pf e e1 e2)
          (WF1: Local.wf e1.(Thread.local) e1.(Thread.memory))
          (SC1: Memory.closed_timemap e1.(Thread.sc) e1.(Thread.memory))
          (CLOSED1: Memory.closed e1.(Thread.memory)):
      <<WF2: Local.wf e2.(Thread.local) e2.(Thread.memory)>> /\
      <<SC2: Memory.closed_timemap e2.(Thread.sc) e2.(Thread.memory)>> /\
      <<CLOSED2: Memory.closed e2.(Thread.memory)>> /\
      <<TVIEW_FUTURE: TView.le e1.(Thread.local).(Local.tview) e2.(Thread.local).(Local.tview)>> /\
      <<SC_FUTURE: TimeMap.le e1.(Thread.sc) e2.(Thread.sc)>> /\
      <<MEM_FUTURE: Memory.future e1.(Thread.memory) e2.(Thread.memory)>>.
    Proof.
      inv STEP.
      - eapply promise_step_future; eauto.
      - eapply program_step_future; eauto.
    Qed.

    Lemma opt_step_future
          e e1 e2
          (STEP: opt_step e e1 e2)
          (WF1: Local.wf e1.(Thread.local) e1.(Thread.memory))
          (SC1: Memory.closed_timemap e1.(Thread.sc) e1.(Thread.memory))
          (CLOSED1: Memory.closed e1.(Thread.memory)):
      <<WF2: Local.wf e2.(Thread.local) e2.(Thread.memory)>> /\
      <<SC2: Memory.closed_timemap e2.(Thread.sc) e2.(Thread.memory)>> /\
      <<CLOSED2: Memory.closed e2.(Thread.memory)>> /\
      <<TVIEW_FUTURE: TView.le e1.(Thread.local).(Local.tview) e2.(Thread.local).(Local.tview)>> /\
      <<SC_FUTURE: TimeMap.le e1.(Thread.sc) e2.(Thread.sc)>> /\
      <<MEM_FUTURE: Memory.future e1.(Thread.memory) e2.(Thread.memory)>>.
    Proof.
      inv STEP.
      - esplits; eauto; refl.
      - eapply step_future; eauto.
    Qed.

    Lemma rtc_all_step_future
          e1 e2
          (STEP: rtc all_step e1 e2)
          (WF1: Local.wf e1.(Thread.local) e1.(Thread.memory))
          (SC1: Memory.closed_timemap e1.(Thread.sc) e1.(Thread.memory))
          (CLOSED1: Memory.closed e1.(Thread.memory)):
      <<WF2: Local.wf e2.(Thread.local) e2.(Thread.memory)>> /\
      <<SC2: Memory.closed_timemap e2.(Thread.sc) e2.(Thread.memory)>> /\
      <<CLOSED2: Memory.closed e2.(Thread.memory)>> /\
      <<TVIEW_FUTURE: TView.le e1.(Thread.local).(Local.tview) e2.(Thread.local).(Local.tview)>> /\
      <<SC_FUTURE: TimeMap.le e1.(Thread.sc) e2.(Thread.sc)>> /\
      <<MEM_FUTURE: Memory.future e1.(Thread.memory) e2.(Thread.memory)>>.
    Proof.
      revert WF1. induction STEP.
      - i. splits; ss; refl.
      - i. inv H. inv USTEP.
        exploit step_future; eauto. i. des.
        exploit IHSTEP; eauto. i. des.
        splits; ss; etrans; eauto.
    Qed.

    Lemma rtc_tau_step_future
          e1 e2
          (STEP: rtc tau_step e1 e2)
          (WF1: Local.wf e1.(Thread.local) e1.(Thread.memory))
          (SC1: Memory.closed_timemap e1.(Thread.sc) e1.(Thread.memory))
          (CLOSED1: Memory.closed e1.(Thread.memory)):
      <<WF2: Local.wf e2.(Thread.local) e2.(Thread.memory)>> /\
      <<SC2: Memory.closed_timemap e2.(Thread.sc) e2.(Thread.memory)>> /\
      <<CLOSED2: Memory.closed e2.(Thread.memory)>> /\
      <<TVIEW_FUTURE: TView.le e1.(Thread.local).(Local.tview) e2.(Thread.local).(Local.tview)>> /\
      <<SC_FUTURE: TimeMap.le e1.(Thread.sc) e2.(Thread.sc)>> /\
      <<MEM_FUTURE: Memory.future e1.(Thread.memory) e2.(Thread.memory)>>.
    Proof.
      apply rtc_all_step_future; auto.
      eapply rtc_implies; [|eauto].
      apply tau_union.
    Qed.

    Lemma promise_step_inhabited
          pf e e1 e2
          (STEP: promise_step pf e e1 e2)
          (INHABITED1: Memory.inhabited e1.(Thread.memory)):
      <<INHABITED2: Memory.inhabited e2.(Thread.memory)>>.
    Proof.
      inv STEP. ss.
      eapply ALocal.promise_step_inhabited; eauto.
    Qed.

    Lemma program_step_inhabited
          e e1 e2
          (STEP: program_step e e1 e2)
          (INHABITED1: Memory.inhabited e1.(Thread.memory)):
      <<INHABITED2: Memory.inhabited e2.(Thread.memory)>>.
    Proof.
      inv STEP. ss.
      eapply ALocal.program_step_inhabited; eauto.
    Qed.

    Lemma step_inhabited
          pf e e1 e2
          (STEP: step pf e e1 e2)
          (INHABITED1: Memory.inhabited e1.(Thread.memory)):
      <<INHABITED2: Memory.inhabited e2.(Thread.memory)>>.
    Proof.
      inv STEP.
      - eapply promise_step_inhabited; eauto.
      - eapply program_step_inhabited; eauto.
    Qed.


    (* step_disjoint *)

    Lemma promise_step_disjoint
          pf e e1 e2 lc
          (STEP: promise_step pf e e1 e2)
          (WF1: Local.wf e1.(Thread.local) e1.(Thread.memory))
          (SC1: Memory.closed_timemap e1.(Thread.sc) e1.(Thread.memory))
          (CLOSED1: Memory.closed e1.(Thread.memory))
          (DISJOINT1: Local.disjoint e1.(Thread.local) lc)
          (WF: Local.wf lc e1.(Thread.memory)):
      <<DISJOINT2: Local.disjoint e2.(Thread.local) lc>> /\
      <<WF: Local.wf lc e2.(Thread.memory)>>.
    Proof.
      inv STEP.
      exploit ALocal.promise_step_future; eauto. i. des.
      exploit ALocal.promise_step_disjoint; eauto.
    Qed.

    Lemma program_step_disjoint
          e e1 e2 lc
          (STEP: program_step e e1 e2)
          (WF1: Local.wf e1.(Thread.local) e1.(Thread.memory))
          (SC1: Memory.closed_timemap e1.(Thread.sc) e1.(Thread.memory))
          (CLOSED1: Memory.closed e1.(Thread.memory))
          (DISJOINT1: Local.disjoint e1.(Thread.local) lc)
          (WF: Local.wf lc e1.(Thread.memory)):
      <<DISJOINT2: Local.disjoint e2.(Thread.local) lc>> /\
      <<WF: Local.wf lc e2.(Thread.memory)>>.
    Proof.
      inv STEP. ss. eapply ALocal.program_step_disjoint; eauto.
    Qed.

    Lemma step_disjoint
          pf e e1 e2 lc
          (STEP: step pf e e1 e2)
          (WF1: Local.wf e1.(Thread.local) e1.(Thread.memory))
          (SC1: Memory.closed_timemap e1.(Thread.sc) e1.(Thread.memory))
          (CLOSED1: Memory.closed e1.(Thread.memory))
          (DISJOINT1: Local.disjoint e1.(Thread.local) lc)
          (WF: Local.wf lc e1.(Thread.memory)):
      <<DISJOINT2: Local.disjoint e2.(Thread.local) lc>> /\
      <<WF: Local.wf lc e2.(Thread.memory)>>.
    Proof.
      inv STEP.
      - eapply promise_step_disjoint; eauto.
      - eapply program_step_disjoint; eauto.
    Qed.

    Lemma opt_step_disjoint
          e e1 e2 lc
          (STEP: opt_step e e1 e2)
          (WF1: Local.wf e1.(Thread.local) e1.(Thread.memory))
          (SC1: Memory.closed_timemap e1.(Thread.sc) e1.(Thread.memory))
          (CLOSED1: Memory.closed e1.(Thread.memory))
          (DISJOINT1: Local.disjoint e1.(Thread.local) lc)
          (WF: Local.wf lc e1.(Thread.memory)):
      <<DISJOINT2: Local.disjoint e2.(Thread.local) lc>> /\
      <<WF: Local.wf lc e2.(Thread.memory)>>.
    Proof.
      inv STEP.
      - esplits; eauto.
      - eapply step_disjoint; eauto.
    Qed.

    Lemma rtc_all_step_disjoint
          e1 e2 lc
          (STEP: rtc all_step e1 e2)
          (WF1: Local.wf e1.(Thread.local) e1.(Thread.memory))
          (SC1: Memory.closed_timemap e1.(Thread.sc) e1.(Thread.memory))
          (CLOSED1: Memory.closed e1.(Thread.memory))
          (DISJOINT1: Local.disjoint e1.(Thread.local) lc)
          (WF: Local.wf lc e1.(Thread.memory)):
      <<DISJOINT2: Local.disjoint e2.(Thread.local) lc>> /\
      <<WF: Local.wf lc e2.(Thread.memory)>>.
    Proof.
      revert WF1 DISJOINT1 WF. induction STEP; eauto. i.
      inv H. inv USTEP.
      exploit step_future; eauto. i. des.
      exploit step_disjoint; eauto. i. des.
      exploit IHSTEP; eauto.
    Qed.

    Lemma rtc_tau_step_disjoint
          e1 e2 lc
          (STEP: rtc tau_step e1 e2)
          (WF1: Local.wf e1.(Thread.local) e1.(Thread.memory))
          (SC1: Memory.closed_timemap e1.(Thread.sc) e1.(Thread.memory))
          (CLOSED1: Memory.closed e1.(Thread.memory))
          (DISJOINT1: Local.disjoint e1.(Thread.local) lc)
          (WF: Local.wf lc e1.(Thread.memory)):
      <<DISJOINT2: Local.disjoint e2.(Thread.local) lc>> /\
      <<WF: Local.wf lc e2.(Thread.memory)>>.
    Proof.
      eapply rtc_all_step_disjoint; cycle 1; eauto.
      eapply rtc_implies; [|eauto].
      apply tau_union.
    Qed.

    Lemma bot_program_step_bot
          e e1 e2
          (STEP: program_step e e1 e2)
          (PROMISES: e1.(Thread.local).(Local.promises) = Memory.bot):
      e2.(Thread.local).(Local.promises) = Memory.bot.
    Proof.
      inv STEP. eapply ALocal.bot_program_step_bot; eauto.
    Qed.
  End AThread.
End AThread.
