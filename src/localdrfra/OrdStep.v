Require Import Omega.
Require Import Bool.
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

Set Implicit Arguments.


Module OrdLocal.
  Section OrdLocal.
    Variable L: Loc.t -> bool.
    Variable ordc: Ordering.t.

    Inductive read_step (lc1:Local.t) (mem1:Memory.t) (loc:Loc.t) (to:Time.t) (val:Const.t) (released:option View.t) (ord:Ordering.t) (lc2:Local.t): Prop :=
    | read_step_intro
        ord'
        (ORD: ord' = if L loc then Ordering.join ord ordc else ord)
        (STEP: Local.read_step lc1 mem1 loc to val released ord' lc2)
    .
    Hint Constructors read_step.

    Inductive write_step (lc1:Local.t) (sc1:TimeMap.t) (mem1:Memory.t)
              (loc:Loc.t) (from to:Time.t)
              (val:Const.t) (releasedm released:option View.t) (ord:Ordering.t)
              (lc2:Local.t) (sc2:TimeMap.t) (mem2:Memory.t) (kind:Memory.op_kind): Prop :=
    | write_step_intro
        ord'
        (ORD: ord' = if L loc then Ordering.join ord ordc else ord)
        (STEP: Local.write_step lc1 sc1 mem1 loc from to val releasedm released ord' lc2 sc2 mem2 kind)
    .
    Hint Constructors write_step.

    Inductive program_step: forall (e:ThreadEvent.t) lc1 sc1 mem1 lc2 sc2 mem2, Prop :=
    | step_silent
        lc1 sc1 mem1:
        program_step ThreadEvent.silent lc1 sc1 mem1 lc1 sc1 mem1
    | step_read
        lc1 sc1 mem1
        loc ts val released ord lc2
        (LOCAL: read_step lc1 mem1 loc ts val released ord lc2):
        program_step (ThreadEvent.read loc ts val released ord) lc1 sc1 mem1 lc2 sc1 mem1
    | step_write
        lc1 sc1 mem1
        loc from to val released ord lc2 sc2 mem2 kind
        (LOCAL: write_step lc1 sc1 mem1 loc from to val None released ord lc2 sc2 mem2 kind):
        program_step (ThreadEvent.write loc from to val released ord) lc1 sc1 mem1 lc2 sc2 mem2
    | step_update
        lc1 sc1 mem1
        loc ordr ordw
        tsr valr releasedr releasedw lc2
        tsw valw lc3 sc3 mem3 kind
        (LOCAL1: read_step lc1 mem1 loc tsr valr releasedr ordr lc2)
        (LOCAL2: write_step lc2 sc1 mem1 loc tsr tsw valw releasedr releasedw ordw lc3 sc3 mem3 kind):
        program_step (ThreadEvent.update loc tsr tsw valr valw releasedr releasedw ordr ordw)
                     lc1 sc1 mem1 lc3 sc3 mem3
    | step_fence
        lc1 sc1 mem1
        ordr ordw lc2 sc2
        (LOCAL: Local.fence_step lc1 sc1 ordr ordw lc2 sc2):
        program_step (ThreadEvent.fence ordr ordw) lc1 sc1 mem1 lc2 sc2 mem1
    | step_syscall
        lc1 sc1 mem1
        e lc2 sc2
        (LOCAL: Local.fence_step lc1 sc1 Ordering.seqcst Ordering.seqcst lc2 sc2):
        program_step (ThreadEvent.syscall e) lc1 sc1 mem1 lc2 sc2 mem1
    | step_failure
        lc1 sc1 mem1
        (LOCAL: Local.failure_step lc1):
        program_step ThreadEvent.failure lc1 sc1 mem1 lc1 sc1 mem1
    .
    Hint Constructors program_step.


    (* step_future *)

    Lemma write_step_non_cancel
          lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind
          (STEP: write_step lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind):
      negb (Memory.op_kind_is_cancel kind).
    Proof.
      inv STEP. eapply Local.write_step_non_cancel; eauto.
    Qed.

    Lemma write_step_strong_relaxed
          lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind
          (STEP: write_step lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind)
          (ORD: Ordering.le Ordering.strong_relaxed ord):
      negb (Memory.op_kind_is_lower kind).
    Proof.
      inv STEP. eapply Local.write_step_strong_relaxed; eauto.
      etrans; eauto. des_ifs; try refl.
      eapply Ordering.join_l.
    Qed.

    Lemma program_step_future
          e lc1 sc1 mem1 lc2 sc2 mem2
          (STEP: program_step e lc1 sc1 mem1 lc2 sc2 mem2)
          (WF1: Local.wf lc1 mem1)
          (SC1: Memory.closed_timemap sc1 mem1)
          (CLOSED1: Memory.closed mem1):
      <<WF2: Local.wf lc2 mem2>> /\
      <<SC2: Memory.closed_timemap sc2 mem2>> /\
      <<CLOSED2: Memory.closed mem2>> /\
      <<TVIEW_FUTURE: TView.le lc1.(Local.tview) lc2.(Local.tview)>> /\
      <<SC_FUTURE: TimeMap.le sc1 sc2>> /\
      <<MEM_FUTURE: Memory.future mem1 mem2>>.
    Proof.
      inv STEP.
      - esplits; eauto; try refl.
      - inv LOCAL.
        exploit Local.read_step_future; eauto. i. des.
        esplits; eauto; try refl.
      - inv LOCAL.
        exploit Local.write_step_future; eauto; try by econs. i. des.
        esplits; eauto; try refl.
      - inv LOCAL1. inv LOCAL2.
        exploit Local.read_step_future; eauto. i. des.
        exploit Local.write_step_future; eauto; try by econs. i. des.
        esplits; eauto. etrans; eauto.
      - exploit Local.fence_step_future; eauto. i. des. esplits; eauto; try refl.
      - exploit Local.fence_step_future; eauto. i. des. esplits; eauto; try refl.
      - esplits; eauto; try refl.
    Qed.

    Lemma program_step_inhabited
          e lc1 sc1 mem1 lc2 sc2 mem2
          (STEP: program_step e lc1 sc1 mem1 lc2 sc2 mem2)
          (INHABITED1: Memory.inhabited mem1):
      <<INHABITED2: Memory.inhabited mem2>>.
    Proof.
      inv STEP; eauto.
      - inv LOCAL. inv STEP. inv WRITE.
        inv PROMISE; eauto using Memory.add_inhabited, Memory.split_inhabited, Memory.lower_inhabited, Memory.cancel_inhabited.
      - inv LOCAL2. inv STEP. inv WRITE.
        inv PROMISE; eauto using Memory.add_inhabited, Memory.split_inhabited, Memory.lower_inhabited, Memory.cancel_inhabited.
    Qed.


    (* step_disjoint *)

    Lemma program_step_disjoint
          e lc1 sc1 mem1 lc2 sc2 mem2 lc
          (STEP: program_step e lc1 sc1 mem1 lc2 sc2 mem2)
          (WF1: Local.wf lc1 mem1)
          (SC1: Memory.closed_timemap sc1 mem1)
          (CLOSED1: Memory.closed mem1)
          (DISJOINT1: Local.disjoint lc1 lc)
          (WF: Local.wf lc mem1):
      <<DISJOINT2: Local.disjoint lc2 lc>> /\
      <<WF: Local.wf lc mem2>>.
    Proof.
      inv STEP.
      - esplits; eauto.
      - inv LOCAL. exploit Local.read_step_disjoint; eauto.
      - inv LOCAL. exploit Local.write_step_disjoint; eauto.
      - inv LOCAL1. inv LOCAL2.
        exploit Local.read_step_future; eauto. i. des.
        exploit Local.read_step_disjoint; eauto. i. des.
        exploit Local.write_step_disjoint; eauto.
      - exploit Local.fence_step_disjoint; eauto.
      - exploit Local.fence_step_disjoint; eauto.
      - esplits; eauto.
    Qed.

    Lemma program_step_promises_bot
          e lc1 sc1 mem1 lc2 sc2 mem2
          (STEP: program_step e lc1 sc1 mem1 lc2 sc2 mem2)
          (PROMISES: lc1.(Local.promises) = Memory.bot):
      lc2.(Local.promises) = Memory.bot.
    Proof.
      inv STEP; try inv LOCAL; ss; try inv STEP; ss.
      - eapply Memory.write_promises_bot; eauto.
      - inv LOCAL1. inv LOCAL2. inv STEP. inv STEP0.
        eapply Memory.write_promises_bot; eauto.
    Qed.
  End OrdLocal.
End OrdLocal.


Module OrdThread.
  Section OrdThread.
    Variable lang: language.
    Variable L: Loc.t -> bool.
    Variable ordc: Ordering.t.

    Inductive program_step (e:ThreadEvent.t): forall (e1 e2:Thread.t lang), Prop :=
    | program_step_intro
        st1 lc1 sc1 mem1
        st2 lc2 sc2 mem2
        (STATE: lang.(Language.step) (ThreadEvent.get_program_event e) st1 st2)
        (LOCAL: OrdLocal.program_step L ordc e lc1 sc1 mem1 lc2 sc2 mem2):
        program_step e (Thread.mk lang st1 lc1 sc1 mem1) (Thread.mk lang st2 lc2 sc2 mem2)
    .
    Hint Constructors program_step.

    Inductive step: forall (pf:bool) (e:ThreadEvent.t) (e1 e2:Thread.t lang), Prop :=
    | step_promise
        pf e e1 e2
        (STEP: Thread.promise_step pf e e1 e2):
        step pf e e1 e2
    | step_program
        e e1 e2
        (STEP: program_step e e1 e2):
        step true e e1 e2
    .
    Hint Constructors step.

    Inductive step_allpf (e: ThreadEvent.t) (e1 e2: Thread.t lang): Prop :=
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

    Definition steps_failure (e1: Thread.t lang): Prop :=
      exists e2 e3,
        <<STEPS: rtc tau_step e1 e2>> /\
        <<FAILURE: step true ThreadEvent.failure e2 e3>>.
    Hint Unfold steps_failure.

    Definition consistent (e: Thread.t lang): Prop :=
      forall mem1 sc1
        (CAP: Memory.cap e.(Thread.memory) mem1)
        (SC_MAX: Memory.max_concrete_timemap mem1 sc1),
        <<FAILURE: steps_failure (Thread.mk lang e.(Thread.state) e.(Thread.local) sc1 mem1)>> \/
        exists e2,
          <<STEPS: rtc tau_step (Thread.mk lang e.(Thread.state) e.(Thread.local) sc1 mem1) e2>> /\
          <<PROMISES: e2.(Thread.local).(Local.promises) = Memory.bot>>.


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
      inv STEP. ss. eapply OrdLocal.program_step_future; eauto.
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
      - eapply Thread.promise_step_future; eauto.
      - eapply program_step_future; eauto.
    Qed.
  End OrdThread.
End OrdThread.


Module OrdConfiguration.
  Section OrdConfiguration.
    Variable L: Loc.t -> bool.
    Variable ordc: Ordering.t.

    Inductive step: forall (e: MachineEvent.t) (tid: Ident.t) (c1 c2: Configuration.t), Prop :=
    | step_intro
        pf e tid c1 lang st1 lc1 e2 st3 lc3 sc3 memory3
        (TID: IdentMap.find tid c1.(Configuration.threads) = Some (existT _ lang st1, lc1))
        (STEPS: rtc (@OrdThread.tau_step _ L ordc)
                    (Thread.mk _ st1 lc1 c1.(Configuration.sc) c1.(Configuration.memory)) e2)
        (STEP: OrdThread.step L ordc pf e e2 (Thread.mk _ st3 lc3 sc3 memory3))
        (CONSISTENT: e <> ThreadEvent.failure ->
                     OrdThread.consistent L ordc (Thread.mk lang st3 lc3 sc3 memory3)):
        step (ThreadEvent.get_machine_event e) tid
             c1 (Configuration.mk (IdentMap.add tid (existT _ _ st3, lc3) c1.(Configuration.threads)) sc3 memory3)
    .
  End OrdConfiguration.
End OrdConfiguration.
