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
      state: (Language.state lang);
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
        (PF: pf = orb (andb (Memory.op_kind_is_lower kind) (Message.is_released_none msg))
                      (Memory.op_kind_is_cancel kind)):
        promise_step pf (ThreadEvent.promise loc from to msg kind) (mk st lc1 sc1 mem1) (mk st lc2 sc1 mem2)
    .

    (* NOTE: Syscalls act like a SC fence. *)
    Inductive program_step (e:ThreadEvent.t): forall (e1 e2:t), Prop :=
    | program_step_intro
        st1 lc1 sc1 mem1
        st2 lc2 sc2 mem2
        (STATE: (Language.step lang) (ThreadEvent.get_program_event e) st1 st2)
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

    Inductive opt_promise_step: forall (e:ThreadEvent.t) (e1 e2:t), Prop :=
    | opt_promise_step_none
        e1:
        opt_promise_step ThreadEvent.silent e1 e1
    | opt_promise_step_some
        pf e e1 e2
        (STEP: promise_step pf e e1 e2):
        opt_promise_step e e1 e2
    .

    Inductive opt_program_step: forall (e:ThreadEvent.t) (e1 e2:t), Prop :=
    | opt_program_step_none
        e1:
        opt_program_step ThreadEvent.silent e1 e1
    | opt_program_step_some
        e e1 e2
        (STEP: program_step e e1 e2):
        opt_program_step e e1 e2
    .

    Lemma tau_opt_tau
          e1 e2 e3 e
          (STEPS: rtc tau_step e1 e2)
          (STEP: opt_step e e2 e3)
          (EVENT: ThreadEvent.get_machine_event e = MachineEvent.silent):
      rtc tau_step e1 e3.
    Proof.
      induction STEPS.
      - inv STEP; eauto.
      - exploit IHSTEPS; eauto.
    Qed.

    Lemma tau_opt_all
          e1 e2 e3 e
          (STEPS: rtc tau_step e1 e2)
          (STEP: opt_step e e2 e3):
      rtc all_step e1 e3.
    Proof.
      induction STEPS.
      - inv STEP; eauto.
      - exploit IHSTEPS; eauto. i.
        econs 2; eauto.
        inv H. inv TSTEP. econs. econs. eauto.
    Qed.


    Definition steps_failure (e1: t): Prop :=
      exists e e2 e3,
        <<STEPS: rtc tau_step e1 e2>> /\
        <<STEP_FAILURE: step true e e2 e3>> /\
        <<EVENT_FAILURE: ThreadEvent.get_machine_event e = MachineEvent.failure>>.
    Hint Unfold steps_failure.


    (* consistency *)

    Definition consistent (e:t): Prop :=
      forall mem1 sc1
        (CAP: Memory.cap (memory e) mem1)
        (SC_MAX: Memory.max_concrete_timemap mem1 sc1),
        <<FAILURE: steps_failure (mk (state e) (local e) sc1 mem1)>> \/
        exists e2,
          <<STEPS: rtc tau_step (mk (state e) (local e) sc1 mem1) e2>> /\
          <<PROMISES: (Local.promises (local e2)) = Memory.bot>>.


    (* step_future *)

    Lemma promise_step_future
          pf e e1 e2
          (STEP: promise_step pf e e1 e2)
          (WF1: Local.wf (local e1) (memory e1))
          (SC1: Memory.closed_timemap (sc e1) (memory e1))
          (CLOSED1: Memory.closed (memory e1)):
      <<WF2: Local.wf (local e2) (memory e2)>> /\
      <<SC2: Memory.closed_timemap (sc e2) (memory e2)>> /\
      <<CLOSED2: Memory.closed (memory e2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (local e1)) (Local.tview (local e2))>> /\
      <<SC_FUTURE: TimeMap.le (sc e1) (sc e2)>> /\
      <<MEM_FUTURE: Memory.future (memory e1) (memory e2)>>.
    Proof.
      inv STEP. ss.
      exploit Local.promise_step_future; eauto. i. des.
      splits; eauto. refl.
    Qed.

    Lemma program_step_future
          e e1 e2
          (STEP: program_step e e1 e2)
          (WF1: Local.wf (local e1) (memory e1))
          (SC1: Memory.closed_timemap (sc e1) (memory e1))
          (CLOSED1: Memory.closed (memory e1)):
      <<WF2: Local.wf (local e2) (memory e2)>> /\
      <<SC2: Memory.closed_timemap (sc e2) (memory e2)>> /\
      <<CLOSED2: Memory.closed (memory e2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (local e1)) (Local.tview (local e2))>> /\
      <<SC_FUTURE: TimeMap.le (sc e1) (sc e2)>> /\
      <<MEM_FUTURE: Memory.future (memory e1) (memory e2)>>.
    Proof.
      inv STEP. ss. eapply Local.program_step_future; eauto.
    Qed.

    Lemma step_future
          pf e e1 e2
          (STEP: step pf e e1 e2)
          (WF1: Local.wf (local e1) (memory e1))
          (SC1: Memory.closed_timemap (sc e1) (memory e1))
          (CLOSED1: Memory.closed (memory e1)):
      <<WF2: Local.wf (local e2) (memory e2)>> /\
      <<SC2: Memory.closed_timemap (sc e2) (memory e2)>> /\
      <<CLOSED2: Memory.closed (memory e2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (local e1)) (Local.tview (local e2))>> /\
      <<SC_FUTURE: TimeMap.le (sc e1) (sc e2)>> /\
      <<MEM_FUTURE: Memory.future (memory e1) (memory e2)>>.
    Proof.
      inv STEP.
      - eapply promise_step_future; eauto.
      - eapply program_step_future; eauto.
    Qed.

    Lemma opt_step_future
          e e1 e2
          (STEP: opt_step e e1 e2)
          (WF1: Local.wf (local e1) (memory e1))
          (SC1: Memory.closed_timemap (sc e1) (memory e1))
          (CLOSED1: Memory.closed (memory e1)):
      <<WF2: Local.wf (local e2) (memory e2)>> /\
      <<SC2: Memory.closed_timemap (sc e2) (memory e2)>> /\
      <<CLOSED2: Memory.closed (memory e2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (local e1)) (Local.tview (local e2))>> /\
      <<SC_FUTURE: TimeMap.le (sc e1) (sc e2)>> /\
      <<MEM_FUTURE: Memory.future (memory e1) (memory e2)>>.
    Proof.
      inv STEP.
      - esplits; eauto; refl.
      - eapply step_future; eauto.
    Qed.

    Lemma rtc_all_step_future
          e1 e2
          (STEP: rtc all_step e1 e2)
          (WF1: Local.wf (local e1) (memory e1))
          (SC1: Memory.closed_timemap (sc e1) (memory e1))
          (CLOSED1: Memory.closed (memory e1)):
      <<WF2: Local.wf (local e2) (memory e2)>> /\
      <<SC2: Memory.closed_timemap (sc e2) (memory e2)>> /\
      <<CLOSED2: Memory.closed (memory e2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (local e1)) (Local.tview (local e2))>> /\
      <<SC_FUTURE: TimeMap.le (sc e1) (sc e2)>> /\
      <<MEM_FUTURE: Memory.future (memory e1) (memory e2)>>.
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
          (WF1: Local.wf (local e1) (memory e1))
          (SC1: Memory.closed_timemap (sc e1) (memory e1))
          (CLOSED1: Memory.closed (memory e1)):
      <<WF2: Local.wf (local e2) (memory e2)>> /\
      <<SC2: Memory.closed_timemap (sc e2) (memory e2)>> /\
      <<CLOSED2: Memory.closed (memory e2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (local e1)) (Local.tview (local e2))>> /\
      <<SC_FUTURE: TimeMap.le (sc e1) (sc e2)>> /\
      <<MEM_FUTURE: Memory.future (memory e1) (memory e2)>>.
    Proof.
      apply rtc_all_step_future; auto.
      eapply rtc_implies; [|eauto].
      apply tau_union.
    Qed.

    Lemma step_nonpf_future
          e e1 e2
          (STEP: step false e e1 e2)
          (WF1: Local.wf (local e1) (memory e1))
          (SC1: Memory.closed_timemap (sc e1) (memory e1))
          (CLOSED1: Memory.closed (memory e1)):
      <<WF2: Local.wf (local e2) (memory e2)>> /\
      <<SC2: Memory.closed_timemap (sc e2) (memory e2)>> /\
      <<CLOSED2: Memory.closed (memory e2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (local e1)) (Local.tview (local e2))>> /\
      <<SC_FUTURE: TimeMap.le (sc e1) (sc e2)>> /\
      <<MEM_FUTURE: Memory.future (memory e1) (memory e2)>> /\
      <<STATE: (state e1) = (state e2)>>.
    Proof.
      inv STEP. inv STEP0. ss.
      exploit Local.promise_step_future; eauto. i. des.
      esplits; ss. refl.
    Qed.

    Lemma rtc_step_nonpf_future
          e1 e2
          (STEP: rtc (union (step false)) e1 e2)
          (WF1: Local.wf (local e1) (memory e1))
          (SC1: Memory.closed_timemap (sc e1) (memory e1))
          (CLOSED1: Memory.closed (memory e1)):
      <<WF2: Local.wf (local e2) (memory e2)>> /\
      <<SC2: Memory.closed_timemap (sc e2) (memory e2)>> /\
      <<CLOSED2: Memory.closed (memory e2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (local e1)) (Local.tview (local e2))>> /\
      <<SC_FUTURE: TimeMap.le (sc e1) (sc e2)>> /\
      <<MEM_FUTURE: Memory.future (memory e1) (memory e2)>> /\
      <<STATE: (state e1) = (state e2)>>.
    Proof.
      revert WF1. induction STEP.
      - i. splits; ss; refl.
      - inv H. i. exploit step_nonpf_future; eauto. i. des.
        exploit IHSTEP; eauto. i. des.
        splits; ss; etrans; eauto.
    Qed.


    (* step_inhabited *)

    Lemma promise_step_inhabited
          pf e e1 e2
          (STEP: promise_step pf e e1 e2)
          (INHABITED1: Memory.inhabited (memory e1)):
      <<INHABITED2: Memory.inhabited (memory e2)>>.
    Proof.
      inv STEP. ss.
      eapply Local.promise_step_inhabited; eauto.
    Qed.

    Lemma program_step_inhabited
          e e1 e2
          (STEP: program_step e e1 e2)
          (INHABITED1: Memory.inhabited (memory e1)):
      <<INHABITED2: Memory.inhabited (memory e2)>>.
    Proof.
      inv STEP. ss.
      eapply Local.program_step_inhabited; eauto.
    Qed.

    Lemma step_inhabited
          pf e e1 e2
          (STEP: step pf e e1 e2)
          (INHABITED1: Memory.inhabited (memory e1)):
      <<INHABITED2: Memory.inhabited (memory e2)>>.
    Proof.
      inv STEP.
      - eapply promise_step_inhabited; eauto.
      - eapply program_step_inhabited; eauto.
    Qed.


    (* step_disjoint *)

    Lemma promise_step_disjoint
          pf e e1 e2 lc
          (STEP: promise_step pf e e1 e2)
          (WF1: Local.wf (local e1) (memory e1))
          (SC1: Memory.closed_timemap (sc e1) (memory e1))
          (CLOSED1: Memory.closed (memory e1))
          (DISJOINT1: Local.disjoint (local e1) lc)
          (WF: Local.wf lc (memory e1)):
      <<DISJOINT2: Local.disjoint (local e2) lc>> /\
      <<WF: Local.wf lc (memory e2)>>.
    Proof.
      inv STEP.
      exploit Local.promise_step_future; eauto. i. des.
      exploit Local.promise_step_disjoint; eauto.
    Qed.

    Lemma program_step_disjoint
          e e1 e2 lc
          (STEP: program_step e e1 e2)
          (WF1: Local.wf (local e1) (memory e1))
          (SC1: Memory.closed_timemap (sc e1) (memory e1))
          (CLOSED1: Memory.closed (memory e1))
          (DISJOINT1: Local.disjoint (local e1) lc)
          (WF: Local.wf lc (memory e1)):
      <<DISJOINT2: Local.disjoint (local e2) lc>> /\
      <<WF: Local.wf lc (memory e2)>>.
    Proof.
      inv STEP. ss. eapply Local.program_step_disjoint; eauto.
    Qed.

    Lemma step_disjoint
          pf e e1 e2 lc
          (STEP: step pf e e1 e2)
          (WF1: Local.wf (local e1) (memory e1))
          (SC1: Memory.closed_timemap (sc e1) (memory e1))
          (CLOSED1: Memory.closed (memory e1))
          (DISJOINT1: Local.disjoint (local e1) lc)
          (WF: Local.wf lc (memory e1)):
      <<DISJOINT2: Local.disjoint (local e2) lc>> /\
      <<WF: Local.wf lc (memory e2)>>.
    Proof.
      inv STEP.
      - eapply promise_step_disjoint; eauto.
      - eapply program_step_disjoint; eauto.
    Qed.

    Lemma opt_step_disjoint
          e e1 e2 lc
          (STEP: opt_step e e1 e2)
          (WF1: Local.wf (local e1) (memory e1))
          (SC1: Memory.closed_timemap (sc e1) (memory e1))
          (CLOSED1: Memory.closed (memory e1))
          (DISJOINT1: Local.disjoint (local e1) lc)
          (WF: Local.wf lc (memory e1)):
      <<DISJOINT2: Local.disjoint (local e2) lc>> /\
      <<WF: Local.wf lc (memory e2)>>.
    Proof.
      inv STEP.
      - esplits; eauto.
      - eapply step_disjoint; eauto.
    Qed.

    Lemma rtc_all_step_disjoint
          e1 e2 lc
          (STEP: rtc all_step e1 e2)
          (WF1: Local.wf (local e1) (memory e1))
          (SC1: Memory.closed_timemap (sc e1) (memory e1))
          (CLOSED1: Memory.closed (memory e1))
          (DISJOINT1: Local.disjoint (local e1) lc)
          (WF: Local.wf lc (memory e1)):
      <<DISJOINT2: Local.disjoint (local e2) lc>> /\
      <<WF: Local.wf lc (memory e2)>>.
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
          (WF1: Local.wf (local e1) (memory e1))
          (SC1: Memory.closed_timemap (sc e1) (memory e1))
          (CLOSED1: Memory.closed (memory e1))
          (DISJOINT1: Local.disjoint (local e1) lc)
          (WF: Local.wf lc (memory e1)):
      <<DISJOINT2: Local.disjoint (local e2) lc>> /\
      <<WF: Local.wf lc (memory e2)>>.
    Proof.
      eapply rtc_all_step_disjoint; cycle 1; eauto.
      eapply rtc_implies; [|eauto].
      apply tau_union.
    Qed.

    Lemma program_step_promises_bot
          e e1 e2
          (STEP: program_step e e1 e2)
          (PROMISES: (Local.promises (local e1)) = Memory.bot):
      (Local.promises (local e2)) = Memory.bot.
    Proof.
      inv STEP. eapply Local.program_step_promises_bot; eauto.
    Qed.


    (* step_prev_None *)

    (* Lemma step_prev_None *)
    (*       pf e e1 e2 *)
    (*       (STEP: step pf e e1 e2): *)
    (*   <<PREV: Memory.prev_None e1.(memory) e2.(memory)>>. *)
    (* Proof. *)
    (*   inv STEP; inv STEP0; inv LOCAL; ss; *)
    (*     try by ii; eapply GET_PREV; eauto. *)
    (*   - eapply Memory.promise_prev_None; eauto. *)
    (*   - inv LOCAL0. inv WRITE. ss. *)
    (*     eapply Memory.promise_prev_None; eauto. *)
    (*   - inv LOCAL1. inv LOCAL2. inv WRITE. ss. *)
    (*     eapply Memory.promise_prev_None; eauto. *)
    (* Qed. *)

    (* Lemma opt_step_prev_None *)
    (*       e e1 e2 *)
    (*       (STEP: opt_step e e1 e2): *)
    (*   <<PREV: Memory.prev_None e1.(memory) e2.(memory)>>. *)
    (* Proof. *)
    (*   inv STEP; eauto using step_prev_None. *)
    (*   ii. eapply GET_PREV; eauto. *)
    (* Qed. *)

    (* Lemma rtc_tau_step_prev_None *)
    (*       e1 e2 *)
    (*       (STEPS: rtc tau_step e1 e2): *)
    (*   <<PREV: Memory.prev_None e1.(memory) e2.(memory)>>. *)
    (* Proof. *)
    (*   induction STEPS. *)
    (*   - ii. eapply GET_PREV; eauto. *)
    (*   - inv H. inv TSTEP. *)
    (*     inv STEP; inv STEP0; inv LOCAL; ss; ii. *)
    (*     + exploit Memory.promise_get_from; eauto. i. des. *)
    (*       hexploit Memory.promise_prev_None; eauto. i. *)
    (*       eapply IHSTEPS; eauto. *)
    (*     + inv LOCAL0. inv WRITE. *)
    (*       exploit Memory.promise_get_from; eauto. i. des. *)
    (*       hexploit Memory.promise_prev_None; eauto. i. *)
    (*       eapply IHSTEPS; eauto. *)
    (*     + inv LOCAL1. inv LOCAL2. inv WRITE. ss. *)
    (*       exploit Memory.promise_get_from; try exact GET; eauto. i. des. *)
    (*       hexploit Memory.promise_prev_None; eauto. i. *)
    (*       eapply IHSTEPS; eauto. *)
    (* Qed. *)

    (* Lemma rtc_all_step_prev_None *)
    (*       e1 e2 *)
    (*       (STEPS: rtc all_step e1 e2): *)
    (*   <<PREV: Memory.prev_None e1.(memory) e2.(memory)>>. *)
    (* Proof. *)
    (*   induction STEPS. *)
    (*   - ii. eapply GET_PREV; eauto. *)
    (*   - inv H. inv USTEP. *)
    (*     inv STEP; inv STEP0; inv LOCAL; ss; ii. *)
    (*     + exploit Memory.promise_get_from; eauto. i. des. *)
    (*       hexploit Memory.promise_prev_None; eauto. i. *)
    (*       eapply IHSTEPS; eauto. *)
    (*     + inv LOCAL0. inv WRITE. *)
    (*       exploit Memory.promise_get_from; eauto. i. des. *)
    (*       hexploit Memory.promise_prev_None; eauto. i. *)
    (*       eapply IHSTEPS; eauto. *)
    (*     + inv LOCAL1. inv LOCAL2. inv WRITE. ss. *)
    (*       exploit Memory.promise_get_from; try exact GET; eauto. i. des. *)
    (*       hexploit Memory.promise_prev_None; eauto. i. *)
    (*       eapply IHSTEPS; eauto. *)
    (* Qed. *)

    Inductive reserve_step (e1 e2:t): Prop :=
    | reserve_step_intro
        pf loc from to
        (STEP: step pf (ThreadEvent.promise loc from to Message.reserve Memory.op_kind_add) e1 e2)
    .
    Hint Constructors reserve_step.

    Inductive cancel_step (e1 e2:t): Prop :=
    | cancel_step_intro
        pf loc from to
        (STEP: step pf (ThreadEvent.promise loc from to Message.reserve Memory.op_kind_cancel) e1 e2)
    .
    Hint Constructors cancel_step.

    Lemma reserve_step_tau_step e1 e2
          (RESERVE: reserve_step e1 e2)
      :
        tau_step e1 e2.
    Proof.
      inv RESERVE. econs; eauto.
    Qed.

    Lemma cancel_step_tau_step e1 e2
          (CANCEL: cancel_step e1 e2)
      :
        tau_step e1 e2.
    Proof.
      inv CANCEL. econs; eauto.
    Qed.

    Lemma reservation_event_reserve_or_cancel_step
          (e1 e2: t) pf e
          (RESERVATION: ThreadEvent.is_reservation_event e)
          (STEP: step pf e e1 e2):
        reserve_step e1 e2 \/ cancel_step e1 e2.
    Proof.
      dup STEP. inv STEP.
      - inv STEP1. inv LOCAL. ss. des_ifs. inv PROMISE; ss; eauto.
      - inv STEP1. inv LOCAL; ss.
    Qed.

    Lemma rtc_reserve_step_future
          e1 e2
          (STEP: rtc reserve_step e1 e2)
          (WF1: Local.wf (local e1) (memory e1))
          (SC1: Memory.closed_timemap (sc e1) (memory e1))
          (CLOSED1: Memory.closed (memory e1)):
      <<WF2: Local.wf (local e2) (memory e2)>> /\
      <<SC2: Memory.closed_timemap (sc e2) (memory e2)>> /\
      <<CLOSED2: Memory.closed (memory e2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (local e1)) (Local.tview (local e2))>> /\
      <<SC_FUTURE: TimeMap.le (sc e1) (sc e2)>> /\
      <<MEM_FUTURE: Memory.future (memory e1) (memory e2)>>.
    Proof.
      apply rtc_all_step_future; auto.
      eapply rtc_implies; [|eauto].
      i. inv H. eauto.
    Qed.

    Lemma rtc_cancel_step_future
          e1 e2
          (STEP: rtc cancel_step e1 e2)
          (WF1: Local.wf (local e1) (memory e1))
          (SC1: Memory.closed_timemap (sc e1) (memory e1))
          (CLOSED1: Memory.closed (memory e1)):
      <<WF2: Local.wf (local e2) (memory e2)>> /\
      <<SC2: Memory.closed_timemap (sc e2) (memory e2)>> /\
      <<CLOSED2: Memory.closed (memory e2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (local e1)) (Local.tview (local e2))>> /\
      <<SC_FUTURE: TimeMap.le (sc e1) (sc e2)>> /\
      <<MEM_FUTURE: Memory.future (memory e1) (memory e2)>>.
    Proof.
      apply rtc_all_step_future; auto.
      eapply rtc_implies; [|eauto].
      i. inv H. eauto.
    Qed.
  End Thread.
End Thread.
