Require Import Omega.
Require Import Bool.
Require Import RelationClasses.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
Require Import Event.
Require Import Time.
From PromisingLib Require Import Language.

Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.

Set Implicit Arguments.


Inductive tau T (step: forall (e:ThreadEvent.t) (e1 e2:T), Prop) (e1 e2:T): Prop :=
| tau_intro
    e
    (TSTEP: step e e1 e2)
    (EVENT: ThreadEvent.get_machine_event e = MachineEvent.silent)
.
Hint Constructors tau.

Inductive union E T (step: forall (e:E) (e1 e2:T), Prop) (e1 e2:T): Prop :=
| union_intro
    e
    (USTEP: step e e1 e2)
.
Hint Constructors union.

Lemma tau_mon T (step1 step2: forall (e:ThreadEvent.t) (e1 e2:T), Prop)
      (STEP: step1 <3= step2):
  tau step1 <2= tau step2.
Proof.
  i. inv PR. econs; eauto.
Qed.

Lemma union_mon E T (step1 step2: forall (e:E) (e1 e2:T), Prop)
      (STEP: step1 <3= step2):
  union step1 <2= union step2.
Proof.
  i. inv PR. econs; eauto.
Qed.

Lemma tau_union: tau <4= (@union ThreadEvent.t).
Proof.
  ii. inv PR. econs. eauto.
Qed.


Module Thread.
  Section Thread.
    Variable (lang:language).

    Structure t := mk {
      state: lang.(Language.state);
      local: Local.t;
      sc: TimeMap.t;
      memory: Memory.t;
    }.

    Inductive promise_step (pf:bool): forall (e:ThreadEvent.t) (e1 e2:t), Prop :=
    | promise_step_intro
        st lc1 sc1 mem1
        loc from to msg kind
        lc2 mem2
        (LOCAL: Local.promise_step lc1 mem1 loc from to msg lc2 mem2 kind)
        (PF: pf = orb (Message.is_reserve msg)
                      (orb (Memory.op_kind_is_lower_full kind) (Memory.op_kind_is_cancel kind))):
        promise_step pf (ThreadEvent.promise loc from to msg kind) (mk st lc1 sc1 mem1) (mk st lc2 sc1 mem2)
    .

    (* NOTE: Syscalls act like a SC fence. *)
    Inductive program_step (e:ThreadEvent.t): forall (e1 e2:t), Prop :=
    | program_step_intro
        st1 lc1 sc1 mem1
        st2 lc2 sc2 mem2
        (STATE: lang.(Language.step) (ThreadEvent.get_program_event e) st1 st2)
        (LOCAL: Local.program_step e lc1 sc1 mem1 lc2 sc2 mem2):
        program_step e (mk st1 lc1 sc1 mem1) (mk st2 lc2 sc2 mem2)
    .
    Hint Constructors program_step.

    Inductive step: forall (pf:bool) (e:ThreadEvent.t) (e1 e2:t), Prop :=
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

    Inductive step_allpf (e:ThreadEvent.t) (e1 e2:t): Prop :=
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

    Inductive opt_step: forall (e:ThreadEvent.t) (e1 e2:t), Prop :=
    | step_none
        e:
        opt_step ThreadEvent.silent e e
    | step_some
        pf e e1 e2
        (STEP: step pf e e1 e2):
        opt_step e e1 e2
    .
    Hint Constructors opt_step.

    Definition steps_failure (e1: t): Prop :=
      exists e2 e3,
        <<STEPS: rtc tau_step e1 e2>> /\
        <<FAILURE: step true ThreadEvent.failure e2 e3>>.
    Hint Unfold steps_failure.

    Definition consistent (e:t): Prop :=
      forall mem1 sc1
        (CAP: Memory.cap e.(local).(Local.promises) e.(memory) mem1)
        (SC_MAX: Memory.max_full_timemap mem1 sc1),
        <<FAILURE: steps_failure (mk e.(state) e.(local) sc1 mem1)>> \/
        exists e2,
          <<STEPS: rtc tau_step (mk e.(state) e.(local) sc1 mem1) e2>> /\
          <<PROMISES: e2.(local).(Local.promises) = Memory.bot>>.


    (* step_future *)

    Lemma promise_step_future
          pf e e1 e2
          (STEP: promise_step pf e e1 e2)
          (WF1: Local.wf e1.(local) e1.(memory))
          (SC1: Memory.closed_timemap e1.(sc) e1.(memory))
          (CLOSED1: Memory.closed e1.(memory)):
      <<WF2: Local.wf e2.(local) e2.(memory)>> /\
      <<SC2: Memory.closed_timemap e2.(sc) e2.(memory)>> /\
      <<CLOSED2: Memory.closed e2.(memory)>> /\
      <<TVIEW_FUTURE: TView.le e1.(Thread.local).(Local.tview) e2.(Thread.local).(Local.tview)>> /\
      <<SC_FUTURE: TimeMap.le e1.(sc) e2.(sc)>> /\
      <<MEM_FUTURE: Memory.future e1.(memory) e2.(memory)>>.
    Proof.
      inv STEP. ss.
      exploit Local.promise_step_future; eauto. i. des.
      splits; eauto. refl.
    Qed.

    Lemma program_step_future
          e e1 e2
          (STEP: program_step e e1 e2)
          (WF1: Local.wf e1.(local) e1.(memory))
          (SC1: Memory.closed_timemap e1.(sc) e1.(memory))
          (CLOSED1: Memory.closed e1.(memory)):
      <<WF2: Local.wf e2.(local) e2.(memory)>> /\
      <<SC2: Memory.closed_timemap e2.(sc) e2.(memory)>> /\
      <<CLOSED2: Memory.closed e2.(memory)>> /\
      <<TVIEW_FUTURE: TView.le e1.(Thread.local).(Local.tview) e2.(Thread.local).(Local.tview)>> /\
      <<SC_FUTURE: TimeMap.le e1.(sc) e2.(sc)>> /\
      <<MEM_FUTURE: Memory.future e1.(memory) e2.(memory)>>.
    Proof.
      inv STEP. ss. eapply Local.program_step_future; eauto.
    Qed.

    Lemma step_future
          pf e e1 e2
          (STEP: step pf e e1 e2)
          (WF1: Local.wf e1.(local) e1.(memory))
          (SC1: Memory.closed_timemap e1.(sc) e1.(memory))
          (CLOSED1: Memory.closed e1.(memory)):
      <<WF2: Local.wf e2.(local) e2.(memory)>> /\
      <<SC2: Memory.closed_timemap e2.(sc) e2.(memory)>> /\
      <<CLOSED2: Memory.closed e2.(memory)>> /\
      <<TVIEW_FUTURE: TView.le e1.(Thread.local).(Local.tview) e2.(Thread.local).(Local.tview)>> /\
      <<SC_FUTURE: TimeMap.le e1.(sc) e2.(sc)>> /\
      <<MEM_FUTURE: Memory.future e1.(memory) e2.(memory)>>.
    Proof.
      inv STEP.
      - eapply promise_step_future; eauto.
      - eapply program_step_future; eauto.
    Qed.

    (* TODO: unused *)
    Lemma step_nonpf_future
          e e1 e2
          (STEP: step false e e1 e2)
          (WF1: Local.wf e1.(local) e1.(memory))
          (SC1: Memory.closed_timemap e1.(sc) e1.(memory))
          (CLOSED1: Memory.closed e1.(memory)):
      <<WF2: Local.wf e2.(local) e2.(memory)>> /\
      <<SC2: Memory.closed_timemap e2.(sc) e2.(memory)>> /\
      <<CLOSED2: Memory.closed e2.(memory)>> /\
      <<TVIEW_FUTURE: TView.le e1.(local).(Local.tview) e2.(local).(Local.tview)>> /\
      <<SC_FUTURE: TimeMap.le e1.(sc) e2.(sc)>> /\
      <<MEM_FUTURE: Memory.future e1.(memory) e2.(memory)>> /\
      <<STATE: e1.(state) = e2.(state)>>.
    Proof.
      inv STEP. inv STEP0. ss.
      exploit Local.promise_step_future; eauto. i. des.
      esplits; ss. refl.
    Qed.

    Lemma opt_step_future
          e e1 e2
          (STEP: opt_step e e1 e2)
          (WF1: Local.wf e1.(local) e1.(memory))
          (SC1: Memory.closed_timemap e1.(sc) e1.(memory))
          (CLOSED1: Memory.closed e1.(memory)):
      <<WF2: Local.wf e2.(local) e2.(memory)>> /\
      <<SC2: Memory.closed_timemap e2.(sc) e2.(memory)>> /\
      <<CLOSED2: Memory.closed e2.(memory)>> /\
      <<TVIEW_FUTURE: TView.le e1.(Thread.local).(Local.tview) e2.(Thread.local).(Local.tview)>> /\
      <<SC_FUTURE: TimeMap.le e1.(sc) e2.(sc)>> /\
      <<MEM_FUTURE: Memory.future e1.(memory) e2.(memory)>>.
    Proof.
      inv STEP.
      - esplits; eauto; refl.
      - eapply step_future; eauto.
    Qed.

    Lemma rtc_all_step_future
          e1 e2
          (STEP: rtc all_step e1 e2)
          (WF1: Local.wf e1.(local) e1.(memory))
          (SC1: Memory.closed_timemap e1.(sc) e1.(memory))
          (CLOSED1: Memory.closed e1.(memory)):
      <<WF2: Local.wf e2.(local) e2.(memory)>> /\
      <<SC2: Memory.closed_timemap e2.(sc) e2.(memory)>> /\
      <<CLOSED2: Memory.closed e2.(memory)>> /\
      <<TVIEW_FUTURE: TView.le e1.(Thread.local).(Local.tview) e2.(Thread.local).(Local.tview)>> /\
      <<SC_FUTURE: TimeMap.le e1.(sc) e2.(sc)>> /\
      <<MEM_FUTURE: Memory.future e1.(memory) e2.(memory)>>.
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
          (WF1: Local.wf e1.(local) e1.(memory))
          (SC1: Memory.closed_timemap e1.(sc) e1.(memory))
          (CLOSED1: Memory.closed e1.(memory)):
      <<WF2: Local.wf e2.(local) e2.(memory)>> /\
      <<SC2: Memory.closed_timemap e2.(sc) e2.(memory)>> /\
      <<CLOSED2: Memory.closed e2.(memory)>> /\
      <<TVIEW_FUTURE: TView.le e1.(Thread.local).(Local.tview) e2.(Thread.local).(Local.tview)>> /\
      <<SC_FUTURE: TimeMap.le e1.(sc) e2.(sc)>> /\
      <<MEM_FUTURE: Memory.future e1.(memory) e2.(memory)>>.
    Proof.
      apply rtc_all_step_future; auto.
      eapply rtc_implies; [|eauto].
      apply tau_union.
    Qed.

    (* TODO: unused *)
    Lemma rtc_step_nonpf_future
          e1 e2
          (STEP: rtc (union (step false)) e1 e2)
          (WF1: Local.wf e1.(local) e1.(memory))
          (SC1: Memory.closed_timemap e1.(sc) e1.(memory))
          (CLOSED1: Memory.closed e1.(memory)):
      <<WF2: Local.wf e2.(local) e2.(memory)>> /\
      <<SC2: Memory.closed_timemap e2.(sc) e2.(memory)>> /\
      <<CLOSED2: Memory.closed e2.(memory)>> /\
      <<TVIEW_FUTURE: TView.le e1.(local).(Local.tview) e2.(local).(Local.tview)>> /\
      <<SC_FUTURE: TimeMap.le e1.(sc) e2.(sc)>> /\
      <<MEM_FUTURE: Memory.future e1.(memory) e2.(memory)>> /\
      <<STATE: e1.(state) = e2.(state)>>.
    Proof.
      revert WF1. induction STEP.
      - i. splits; ss; refl.
      - inv H. i. exploit step_nonpf_future; eauto. i. des.
        exploit IHSTEP; eauto. i. des.
        splits; ss; etrans; eauto.
    Qed.

    Lemma promise_step_inhabited
          pf e e1 e2
          (STEP: promise_step pf e e1 e2)
          (INHABITED1: Memory.inhabited e1.(memory)):
      <<INHABITED2: Memory.inhabited e2.(memory)>>.
    Proof.
      inv STEP. ss.
      eapply Local.promise_step_inhabited; eauto.
    Qed.

    Lemma program_step_inhabited
          e e1 e2
          (STEP: program_step e e1 e2)
          (INHABITED1: Memory.inhabited e1.(memory)):
      <<INHABITED2: Memory.inhabited e2.(memory)>>.
    Proof.
      inv STEP. ss.
      eapply Local.program_step_inhabited; eauto.
    Qed.

    Lemma step_inhabited
          pf e e1 e2
          (STEP: step pf e e1 e2)
          (INHABITED1: Memory.inhabited e1.(memory)):
      <<INHABITED2: Memory.inhabited e2.(memory)>>.
    Proof.
      inv STEP.
      - eapply promise_step_inhabited; eauto.
      - eapply program_step_inhabited; eauto.
    Qed.


    (* step_disjoint *)

    Lemma promise_step_disjoint
          pf e e1 e2 lc
          (STEP: promise_step pf e e1 e2)
          (WF1: Local.wf e1.(local) e1.(memory))
          (SC1: Memory.closed_timemap e1.(sc) e1.(memory))
          (CLOSED1: Memory.closed e1.(memory))
          (DISJOINT1: Local.disjoint e1.(local) lc)
          (WF: Local.wf lc e1.(memory)):
      <<DISJOINT2: Local.disjoint e2.(local) lc>> /\
      <<WF: Local.wf lc e2.(memory)>>.
    Proof.
      inv STEP.
      exploit Local.promise_step_future; eauto. i. des.
      exploit Local.promise_step_disjoint; eauto.
    Qed.

    Lemma program_step_disjoint
          e e1 e2 lc
          (STEP: program_step e e1 e2)
          (WF1: Local.wf e1.(local) e1.(memory))
          (SC1: Memory.closed_timemap e1.(sc) e1.(memory))
          (CLOSED1: Memory.closed e1.(memory))
          (DISJOINT1: Local.disjoint e1.(local) lc)
          (WF: Local.wf lc e1.(memory)):
      <<DISJOINT2: Local.disjoint e2.(local) lc>> /\
      <<WF: Local.wf lc e2.(memory)>>.
    Proof.
      inv STEP. ss. eapply Local.program_step_disjoint; eauto.
    Qed.

    Lemma step_disjoint
          pf e e1 e2 lc
          (STEP: step pf e e1 e2)
          (WF1: Local.wf e1.(local) e1.(memory))
          (SC1: Memory.closed_timemap e1.(sc) e1.(memory))
          (CLOSED1: Memory.closed e1.(memory))
          (DISJOINT1: Local.disjoint e1.(local) lc)
          (WF: Local.wf lc e1.(memory)):
      <<DISJOINT2: Local.disjoint e2.(local) lc>> /\
      <<WF: Local.wf lc e2.(memory)>>.
    Proof.
      inv STEP.
      - eapply promise_step_disjoint; eauto.
      - eapply program_step_disjoint; eauto.
    Qed.

    Lemma opt_step_disjoint
          e e1 e2 lc
          (STEP: opt_step e e1 e2)
          (WF1: Local.wf e1.(local) e1.(memory))
          (SC1: Memory.closed_timemap e1.(sc) e1.(memory))
          (CLOSED1: Memory.closed e1.(memory))
          (DISJOINT1: Local.disjoint e1.(local) lc)
          (WF: Local.wf lc e1.(memory)):
      <<DISJOINT2: Local.disjoint e2.(local) lc>> /\
      <<WF: Local.wf lc e2.(memory)>>.
    Proof.
      inv STEP.
      - esplits; eauto.
      - eapply step_disjoint; eauto.
    Qed.

    Lemma rtc_all_step_disjoint
          e1 e2 lc
          (STEP: rtc all_step e1 e2)
          (WF1: Local.wf e1.(local) e1.(memory))
          (SC1: Memory.closed_timemap e1.(sc) e1.(memory))
          (CLOSED1: Memory.closed e1.(memory))
          (DISJOINT1: Local.disjoint e1.(local) lc)
          (WF: Local.wf lc e1.(memory)):
      <<DISJOINT2: Local.disjoint e2.(local) lc>> /\
      <<WF: Local.wf lc e2.(memory)>>.
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
          (WF1: Local.wf e1.(local) e1.(memory))
          (SC1: Memory.closed_timemap e1.(sc) e1.(memory))
          (CLOSED1: Memory.closed e1.(memory))
          (DISJOINT1: Local.disjoint e1.(local) lc)
          (WF: Local.wf lc e1.(memory)):
      <<DISJOINT2: Local.disjoint e2.(local) lc>> /\
      <<WF: Local.wf lc e2.(memory)>>.
    Proof.
      eapply rtc_all_step_disjoint; cycle 1; eauto.
      eapply rtc_implies; [|eauto].
      apply tau_union.
    Qed.


    (* step_no_reserve_except *)

    Definition no_reserve_except (e: t) :=
      Memory.no_reserve_except e.(local).(Local.promises) e.(memory).

    Lemma step_no_reserve_except
          pf e e1 e2
          (STEP: step pf e e1 e2)
          (WF1: Local.wf e1.(local) e1.(memory))
          (NORESERVE1: no_reserve_except e1):
      no_reserve_except e2.
    Proof.
      inv STEP; inv STEP0.
      - eapply Local.promise_step_no_reserve_except; eauto. apply WF1.
      - eapply Local.program_step_no_reserve_except; eauto. apply WF1.
    Qed.

    Lemma rtc_tau_step_no_reserve_except
          e1 e2
          (STEP: rtc tau_step e1 e2)
          (WF1: Local.wf e1.(local) e1.(memory))
          (SC1: Memory.closed_timemap e1.(sc) e1.(memory))
          (CLOSED1: Memory.closed e1.(memory))
          (NORESERVE1: no_reserve_except e1):
      no_reserve_except e2.
    Proof.
      induction STEP; ss; i.
      inv H. inv TSTEP. exploit step_future; eauto. i. des.
      eapply IHSTEP; eauto.
      eapply step_no_reserve_except; eauto.
    Qed.

    Lemma step_bot_no_reserve
          pf e e1 e2
          (STEP: step pf e e1 e2)
          (WF1: Local.wf e1.(local) e1.(memory))
          (SC1: Memory.closed_timemap e1.(sc) e1.(memory))
          (CLOSED1: Memory.closed e1.(memory))
          (NORESERVE1: Memory.no_reserve e1.(memory))
          (PROMISES2: e2.(local).(Local.promises) = Memory.bot):
      Memory.no_reserve e2.(memory).
    Proof.
      exploit step_future; eauto. i. des.
      hexploit step_no_reserve_except; eauto; i.
      { eapply Memory.no_reserve_no_reserve_except; eauto. }
      unfold no_reserve_except in *. rewrite PROMISES2 in *.
      eapply Memory.no_reserve_except_bot_no_reserve; eauto.
      apply CLOSED2.
    Qed.

    Lemma rtc_tau_step_bot_no_reserve
          e1 e2
          (STEP: rtc tau_step e1 e2)
          (WF1: Local.wf e1.(local) e1.(memory))
          (SC1: Memory.closed_timemap e1.(sc) e1.(memory))
          (CLOSED1: Memory.closed e1.(memory))
          (NORESERVE1: Memory.no_reserve e1.(memory))
          (PROMISES2: e2.(local).(Local.promises) = Memory.bot):
      Memory.no_reserve e2.(memory).
    Proof.
      exploit rtc_tau_step_future; eauto. i. des.
      hexploit rtc_tau_step_no_reserve_except; eauto; i.
      { eapply Memory.no_reserve_no_reserve_except; eauto. }
      unfold no_reserve_except in *. rewrite PROMISES2 in *.
      eapply Memory.no_reserve_except_bot_no_reserve; eauto.
      apply CLOSED2.
    Qed.


    Lemma bot_program_step_bot
          e e1 e2
          (STEP: program_step e e1 e2)
          (PROMISES: e1.(local).(Local.promises) = Memory.bot):
      e2.(local).(Local.promises) = Memory.bot.
    Proof.
      inv STEP. eapply Local.bot_program_step_bot; eauto.
    Qed.
  End Thread.
End Thread.
