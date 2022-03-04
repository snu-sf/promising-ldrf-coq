Require Import Lia.
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

Require Import PromiseConsistent.
Require Import Mapping.

Require Import PFStep.
Require Import OrdStep.

Set Implicit Arguments.




(** L-SC machine **)
Module SCLocal.
  Section SCLocal.
    Variable L: Loc.t -> bool.

    Definition non_maximal (lc: Local.t) (mem: Memory.t) (loc: Loc.t): Prop :=
      exists to from msg,
        (<<GET: Memory.get loc to mem = Some (from, msg)>>) /\
        (<<NRESERVE: msg <> Message.reserve>>) /\
        (<<TS: Time.lt ((TView.cur (Local.tview lc)).(View.rlx) loc) to>>)
    .

    Inductive read_step (lc1:Local.t) (mem1:Memory.t) (loc:Loc.t) (to:Time.t) (val:Const.t) (released:option View.t) (ord:Ordering.t) (lc2:Local.t): Prop :=
    | read_step_intro
        ord'
        (ORD: ord' = if L loc then Ordering.join ord Ordering.acqrel else ord)
        (STEP: Local.read_step lc1 mem1 loc to val released ord' lc2)
        (MAXIMAL: forall (LOC: L loc)
                         from' to' val' released'
                         (GET: Memory.get loc to' mem1 = Some (from', Message.concrete val' released')),
            Time.le to' to)
    .
    Hint Constructors read_step.

    Inductive write_step (lc1:Local.t) (sc1:TimeMap.t) (mem1:Memory.t)
              (loc:Loc.t) (from to:Time.t)
              (val:Const.t) (releasedm released:option View.t) (ord:Ordering.t)
              (lc2:Local.t) (sc2:TimeMap.t) (mem2:Memory.t) (kind:Memory.op_kind): Prop :=
    | write_step_intro
        ord'
        (ORD: ord' = if L loc then Ordering.join ord Ordering.acqrel else ord)
        (STEP: Local.write_step lc1 sc1 mem1 loc from to val releasedm released ord' lc2 sc2 mem2 kind)
        (MAXIMAL: forall (LOC: L loc)
                         from' to' val' released'
                         (GET: Memory.get loc to' mem1 = Some (from', Message.concrete val' released')),
            Time.lt to' to)
    .
    Hint Constructors write_step.

    Inductive write_na_step (lc1:Local.t) (sc1:TimeMap.t) (mem1:Memory.t)
                            (loc:Loc.t) (from to:Time.t) (val:Const.t) (ord:Ordering.t)
                            (lc2:Local.t) (sc2:TimeMap.t) (mem2:Memory.t):
      forall (msgs: list (Time.t * Time.t * Message.t))
        (kinds: list Memory.op_kind) (kind:Memory.op_kind), Prop :=
    | write_na_step_na
        msgs kinds kind
        (LOC: L loc = false)
        (STEP: Local.write_na_step lc1 sc1 mem1 loc from to val ord lc2 sc2 mem2 msgs kinds kind):
      write_na_step lc1 sc1 mem1 loc from to val ord lc2 sc2 mem2 msgs kinds kind
    | write_na_step_at
        released kind
        (LOC: L loc = true)
        (STEP: Local.write_step lc1 sc1 mem1 loc from to val None released Ordering.acqrel lc2 sc2 mem2 kind):
      write_na_step lc1 sc1 mem1 loc from to val ord lc2 sc2 mem2 [] [] kind
    .
    Hint Constructors write_na_step.

    Inductive program_step:
      forall (e:ThreadEvent.t) (lc1:Local.t) (sc1:TimeMap.t) (mem1:Memory.t) (lc2:Local.t) (sc2:TimeMap.t) (mem2:Memory.t), Prop :=
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
    | step_write_na
        lc1 sc1 mem1
        loc from to val ord lc2 sc2 mem2 msgs kinds kind
        (LOCAL: write_na_step lc1 sc1 mem1 loc from to val ord lc2 sc2 mem2 msgs kinds kind):
        program_step (ThreadEvent.write_na loc msgs from to val ord) lc1 sc1 mem1 lc2 sc2 mem2
    | step_racy_read
        lc1 sc1 mem1
        loc to val ord
        (LOCAL: OrdLocal.racy_read_step L Ordering.acqrel lc1 mem1 loc to val ord):
        program_step (ThreadEvent.racy_read loc to val ord) lc1 sc1 mem1 lc1 sc1 mem1
    | step_racy_write
        lc1 sc1 mem1
        loc to val ord
        (LOCAL: OrdLocal.racy_write_step L Ordering.acqrel lc1 mem1 loc to ord):
        program_step (ThreadEvent.racy_write loc to val ord) lc1 sc1 mem1 lc1 sc1 mem1
    | step_racy_update
        lc1 sc1 mem1
        loc to valr valw ordr ordw
        (LOCAL: Local.racy_update_step lc1 mem1 loc to ordr ordw):
        program_step (ThreadEvent.racy_update loc to valr valw ordr ordw) lc1 sc1 mem1 lc1 sc1 mem1
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
      <<TVIEW_FUTURE: TView.le (Local.tview lc1) (Local.tview lc2)>> /\
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
      - inv LOCAL.
        { exploit Local.write_na_step_future; eauto. }
        { exploit Local.write_step_future; eauto. i. des. esplits; eauto. }
      - esplits; eauto; try refl.
      - esplits; eauto; try refl.
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
      - inv LOCAL.
        { inv STEP. eapply Memory.write_na_inhabited; eauto. }
        { inv STEP. eapply Memory.write_inhabited; eauto. }
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
      - inv LOCAL.
        { exploit Local.write_na_step_disjoint; eauto. }
        { exploit Local.write_step_disjoint; eauto. }
      - esplits; eauto.
      - esplits; eauto.
      - esplits; eauto.
    Qed.

    Lemma program_step_promises_bot
          e lc1 sc1 mem1 lc2 sc2 mem2
          (STEP: program_step e lc1 sc1 mem1 lc2 sc2 mem2)
          (PROMISES: (Local.promises lc1) = Memory.bot):
      (Local.promises lc2) = Memory.bot.
    Proof.
      inv STEP; try inv LOCAL; ss; try inv STEP; ss.
      - eapply Memory.write_promises_bot; eauto.
      - inv LOCAL1. inv LOCAL2. inv STEP. inv STEP0.
        eapply Memory.write_promises_bot; eauto.
      - eapply Memory.write_na_promises_bot; eauto.
      - eapply Memory.write_promises_bot; eauto.
    Qed.
  End SCLocal.
End SCLocal.


Module SCThread.
  Section SCThread.
    Variable lang: language.
    Variable L: Loc.t -> bool.

    Inductive program_step (e:ThreadEvent.t): forall (e1 e2:Thread.t lang), Prop :=
    | program_step_intro
        st1 lc1 sc1 mem1
        st2 lc2 sc2 mem2
        (STATE: (Language.step lang) (ThreadEvent.get_program_event e) st1 st2)
        (LOCAL: SCLocal.program_step L e lc1 sc1 mem1 lc2 sc2 mem2):
        program_step e (Thread.mk lang st1 lc1 sc1 mem1) (Thread.mk lang st2 lc2 sc2 mem2)
    .
    Hint Constructors program_step.

    Inductive step: forall (pf:bool) (e:ThreadEvent.t) (e1 e2:Thread.t lang), Prop :=
    | step_promise
        pf e e1 e2
        (STEP: Thread.promise_step pf e e1 e2)
        (PF: PF.pf_event L e):
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

    Inductive opt_step: forall (e: ThreadEvent.t) (e1 e2: Thread.t lang), Prop :=
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
      exists e e2 e3,
        <<STEPS: rtc tau_step e1 e2>> /\
        <<STEP_FAILURE: step true e e2 e3>> /\
        <<EVENT_FAILURE: ThreadEvent.get_machine_event e = MachineEvent.failure>>.
    Hint Unfold steps_failure.

    Definition consistent (e: Thread.t lang): Prop :=
      forall mem1
        (CAP: Memory.cap (Thread.memory e) mem1),
        <<FAILURE: steps_failure (Thread.mk lang (Thread.state e) (Thread.local e) (Thread.sc e) mem1)>> \/
        exists e2,
          <<STEPS: rtc tau_step (Thread.mk lang (Thread.state e) (Thread.local e) (Thread.sc e) mem1) e2>> /\
          <<PROMISES: (Local.promises (Thread.local e2)) = Memory.bot>>.


    (* future *)

    Lemma program_step_future
          e e1 e2
          (STEP: program_step e e1 e2)
          (WF1: Local.wf (Thread.local e1) (Thread.memory e1))
          (SC1: Memory.closed_timemap (Thread.sc e1) (Thread.memory e1))
          (CLOSED1: Memory.closed (Thread.memory e1)):
      <<WF2: Local.wf (Thread.local e2) (Thread.memory e2)>> /\
      <<SC2: Memory.closed_timemap (Thread.sc e2) (Thread.memory e2)>> /\
      <<CLOSED2: Memory.closed (Thread.memory e2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (Thread.local e1)) (Local.tview (Thread.local e2))>> /\
      <<SC_FUTURE: TimeMap.le (Thread.sc e1) (Thread.sc e2)>> /\
      <<MEM_FUTURE: Memory.future (Thread.memory e1) (Thread.memory e2)>>.
    Proof.
      inv STEP. ss. eapply SCLocal.program_step_future; eauto.
    Qed.

    Lemma step_future
          pf e e1 e2
          (STEP: step pf e e1 e2)
          (WF1: Local.wf (Thread.local e1) (Thread.memory e1))
          (SC1: Memory.closed_timemap (Thread.sc e1) (Thread.memory e1))
          (CLOSED1: Memory.closed (Thread.memory e1)):
      <<WF2: Local.wf (Thread.local e2) (Thread.memory e2)>> /\
      <<SC2: Memory.closed_timemap (Thread.sc e2) (Thread.memory e2)>> /\
      <<CLOSED2: Memory.closed (Thread.memory e2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (Thread.local e1)) (Local.tview (Thread.local e2))>> /\
      <<SC_FUTURE: TimeMap.le (Thread.sc e1) (Thread.sc e2)>> /\
      <<MEM_FUTURE: Memory.future (Thread.memory e1) (Thread.memory e2)>>.
    Proof.
      inv STEP.
      - eapply Thread.promise_step_future; eauto.
      - eapply program_step_future; eauto.
    Qed.

    Lemma rtc_all_step_future
          e1 e2
          (STEPS: rtc all_step e1 e2)
          (WF1: Local.wf (Thread.local e1) (Thread.memory e1))
          (SC1: Memory.closed_timemap (Thread.sc e1) (Thread.memory e1))
          (CLOSED1: Memory.closed (Thread.memory e1)):
      <<WF2: Local.wf (Thread.local e2) (Thread.memory e2)>> /\
      <<SC2: Memory.closed_timemap (Thread.sc e2) (Thread.memory e2)>> /\
      <<CLOSED2: Memory.closed (Thread.memory e2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (Thread.local e1)) (Local.tview (Thread.local e2))>> /\
      <<SC_FUTURE: TimeMap.le (Thread.sc e1) (Thread.sc e2)>> /\
      <<MEM_FUTURE: Memory.future (Thread.memory e1) (Thread.memory e2)>>.
    Proof.
      revert WF1 SC1 CLOSED1. induction STEPS; i.
      - esplits; eauto; refl.
      - inv H. inv USTEP. exploit step_future; eauto. i. des.
        exploit IHSTEPS; eauto. i. des.
        esplits; eauto; etrans; eauto.
    Qed.

    Lemma rtc_tau_step_future
          e1 e2
          (STEPS: rtc tau_step e1 e2)
          (WF1: Local.wf (Thread.local e1) (Thread.memory e1))
          (SC1: Memory.closed_timemap (Thread.sc e1) (Thread.memory e1))
          (CLOSED1: Memory.closed (Thread.memory e1)):
      <<WF2: Local.wf (Thread.local e2) (Thread.memory e2)>> /\
      <<SC2: Memory.closed_timemap (Thread.sc e2) (Thread.memory e2)>> /\
      <<CLOSED2: Memory.closed (Thread.memory e2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (Thread.local e1)) (Local.tview (Thread.local e2))>> /\
      <<SC_FUTURE: TimeMap.le (Thread.sc e1) (Thread.sc e2)>> /\
      <<MEM_FUTURE: Memory.future (Thread.memory e1) (Thread.memory e2)>>.
    Proof.
      eapply rtc_all_step_future; eauto.
      eapply rtc_implies; try exact STEPS.
      apply tau_union.
    Qed.

    Lemma opt_step_future
          e e1 e2
          (STEP: opt_step e e1 e2)
          (WF1: Local.wf (Thread.local e1) (Thread.memory e1))
          (SC1: Memory.closed_timemap (Thread.sc e1) (Thread.memory e1))
          (CLOSED1: Memory.closed (Thread.memory e1)):
      <<WF2: Local.wf (Thread.local e2) (Thread.memory e2)>> /\
      <<SC2: Memory.closed_timemap (Thread.sc e2) (Thread.memory e2)>> /\
      <<CLOSED2: Memory.closed (Thread.memory e2)>> /\
      <<TVIEW_FUTURE: TView.le (Local.tview (Thread.local e1)) (Local.tview (Thread.local e2))>> /\
      <<SC_FUTURE: TimeMap.le (Thread.sc e1) (Thread.sc e2)>> /\
      <<MEM_FUTURE: Memory.future (Thread.memory e1) (Thread.memory e2)>>.
    Proof.
      inv STEP.
      - esplits; eauto; try refl.
      - eapply step_future; eauto.
    Qed.

    (* disjoint *)

    Lemma step_disjoint
          pf e e1 e2 lc
          (STEP: step pf e e1 e2)
          (WF1: Local.wf (Thread.local e1) (Thread.memory e1))
          (SC1: Memory.closed_timemap (Thread.sc e1) (Thread.memory e1))
          (CLOSED1: Memory.closed (Thread.memory e1))
          (DISJOINT1: Local.disjoint (Thread.local e1) lc)
          (WF: Local.wf lc (Thread.memory e1)):
      <<DISJOINT2: Local.disjoint (Thread.local e2) lc>> /\
      <<WF: Local.wf lc (Thread.memory e2)>>.
    Proof.
      inv STEP.
      - eapply Thread.promise_step_disjoint; eauto.
      - inv STEP0. eapply SCLocal.program_step_disjoint; eauto.
    Qed.

    Lemma rtc_all_step_disjoint
          e1 e2 lc
          (STEPS: rtc all_step e1 e2)
          (WF1: Local.wf (Thread.local e1) (Thread.memory e1))
          (SC1: Memory.closed_timemap (Thread.sc e1) (Thread.memory e1))
          (CLOSED1: Memory.closed (Thread.memory e1))
          (DISJOINT1: Local.disjoint (Thread.local e1) lc)
          (WF: Local.wf lc (Thread.memory e1)):
      <<DISJOINT2: Local.disjoint (Thread.local e2) lc>> /\
      <<WF: Local.wf lc (Thread.memory e2)>>.
    Proof.
      revert WF1 SC1 CLOSED1 DISJOINT1 WF.
      induction STEPS; i; eauto.
      inv H. inv USTEP.
      exploit step_future; eauto. i. des.
      exploit step_disjoint; eauto. i. des.
      eauto.
    Qed.

    Lemma rtc_tau_step_disjoint
          e1 e2 lc
          (STEPS: rtc tau_step e1 e2)
          (WF1: Local.wf (Thread.local e1) (Thread.memory e1))
          (SC1: Memory.closed_timemap (Thread.sc e1) (Thread.memory e1))
          (CLOSED1: Memory.closed (Thread.memory e1))
          (DISJOINT1: Local.disjoint (Thread.local e1) lc)
          (WF: Local.wf lc (Thread.memory e1)):
      <<DISJOINT2: Local.disjoint (Thread.local e2) lc>> /\
      <<WF: Local.wf lc (Thread.memory e2)>>.
    Proof.
      eapply rtc_all_step_disjoint; try exact DISJOINT1; eauto.
      eapply rtc_implies; try exact STEPS.
      apply tau_union.
    Qed.


    (* promise_consistent *)

    Lemma step_promise_consistent
          pf e e1 e2
          (STEP: step pf e e1 e2)
          (WF1: Local.wf (Thread.local e1) (Thread.memory e1))
          (SC1: Memory.closed_timemap (Thread.sc e1) (Thread.memory e1))
          (CLOSED1: Memory.closed (Thread.memory e1))
          (CONS: Local.promise_consistent (Thread.local e2)):
      Local.promise_consistent (Thread.local e1).
    Proof.
      inv STEP; ss.
      - inv STEP0. s.
        eapply promise_step_promise_consistent; eauto.
      - inv STEP0. inv LOCAL; ss.
        + inv LOCAL0. eapply read_step_promise_consistent; eauto.
        + inv LOCAL0. eapply write_step_promise_consistent; eauto.
        + inv LOCAL1. inv LOCAL2.
          exploit Local.read_step_future; eauto. i. des.
          eapply read_step_promise_consistent; eauto.
          eapply write_step_promise_consistent; eauto.
        + eapply fence_step_promise_consistent; eauto.
        + eapply fence_step_promise_consistent; eauto.
        + inv LOCAL0.
          { eapply write_na_step_promise_consistent; eauto. }
          { eapply write_step_promise_consistent; eauto. }
    Qed.

    Lemma rtc_all_step_promise_consistent
          e1 e2
          (STEPS: rtc all_step e1 e2)
          (WF1: Local.wf (Thread.local e1) (Thread.memory e1))
          (SC1: Memory.closed_timemap (Thread.sc e1) (Thread.memory e1))
          (CLOSED1: Memory.closed (Thread.memory e1))
          (CONS: Local.promise_consistent (Thread.local e2)):
      Local.promise_consistent (Thread.local e1).
    Proof.
      revert WF1 SC1 CLOSED1 CONS. induction STEPS; ss. i.
      inv H. inv USTEP. exploit step_future; eauto. i. des.
      eapply step_promise_consistent; eauto.
    Qed.

    Lemma rtc_tau_step_promise_consistent
          e1 e2
          (STEPS: rtc tau_step e1 e2)
          (WF1: Local.wf (Thread.local e1) (Thread.memory e1))
          (SC1: Memory.closed_timemap (Thread.sc e1) (Thread.memory e1))
          (CLOSED1: Memory.closed (Thread.memory e1))
          (CONS: Local.promise_consistent (Thread.local e2)):
      Local.promise_consistent (Thread.local e1).
    Proof.
      eapply rtc_all_step_promise_consistent; try exact CONS; eauto.
      eapply rtc_implies; try exact STEPS.
      apply tau_union.
    Qed.

  End SCThread.
End SCThread.


Module SCConfiguration.
  Section SCConfiguration.
    Variable L: Loc.t -> bool.

    Inductive step: forall (e: ThreadEvent.t) (tid: Ident.t) (c1 c2: Configuration.t), Prop :=
    | step_intro
        e tid c1 lang st1 lc1 e2 e3 st4 lc4 sc4 memory4
        (TID: IdentMap.find tid (Configuration.threads c1) = Some (existT _ lang st1, lc1))
        (CANCELS: rtc (@Thread.cancel_step _) (Thread.mk _ st1 lc1 (Configuration.sc c1) (Configuration.memory c1)) e2)
        (STEP: SCThread.opt_step L e e2 e3)
        (RESERVES: rtc (@Thread.reserve_step _) e3 (Thread.mk _ st4 lc4 sc4 memory4))
        (CONSISTENT: ThreadEvent.get_machine_event e <> MachineEvent.failure ->
                     SCThread.consistent L (Thread.mk _ st4 lc4 sc4 memory4)):
        step e tid c1 (Configuration.mk (IdentMap.add tid (existT _ _ st4, lc4) (Configuration.threads c1)) sc4 memory4)
    .
    Hint Constructors step.

    Inductive all_step (c1 c2: Configuration.t): Prop :=
    | all_step_intro
        e tid
        (STEP: step e tid c1 c2)
    .
    Hint Constructors all_step.

    Inductive machine_step: forall (e: MachineEvent.t) (tid: Ident.t) (c1 c2: Configuration.t), Prop :=
    | machine_step_instro
        e tid c1 c2
        (STEP: step e tid c1 c2):
        machine_step (ThreadEvent.get_machine_event e) tid c1 c2
    .
    Hint Constructors machine_step.

    Lemma step_future
          e tid c1 c2
          (STEP: step e tid c1 c2)
          (WF1: Configuration.wf c1):
      (<<WF2: Configuration.wf c2>>) /\
      (<<SC_FUTURE: TimeMap.le (Configuration.sc c1) (Configuration.sc c2)>>) /\
      (<<MEM_FUTURE: Memory.future (Configuration.memory c1) (Configuration.memory c2)>>).
    Proof.
      inv WF1. inv WF. inv STEP; s. exploit THREADS; ss; eauto. i.
      assert (STEPS: rtc
                       (@SCThread.all_step _ L)
                       (Thread.mk _ st1 lc1 (Configuration.sc c1) (Configuration.memory c1))
                       (Thread.mk _ st4 lc4 sc4 memory4)).
      { etrans.
        { eapply rtc_implies; try apply CANCELS. i.
          inv H. inv STEP; [|inv STEP1; inv LOCAL].
          econs; eauto. econs; eauto. econs 1; eauto. ii. clarify. }
        etrans.
        { instantiate (1:=e3). inv STEP0; eauto.
          econs; [|refl]; eauto. econs; eauto. econs; eauto. }
        { eapply rtc_implies; try apply RESERVES. i.
          inv H. inv STEP; [|inv STEP1; inv LOCAL].
          econs; eauto. econs; eauto. econs 1; eauto. ii. clarify. }
      }
      exploit SCThread.rtc_all_step_future; eauto. s. i. des.
      splits; eauto. econs; ss. econs.
      + i. Configuration.simplify.
        * exploit THREADS; try apply TH1; eauto. i. des.
          exploit SCThread.rtc_all_step_disjoint; eauto. i. des.
          symmetry. auto.
        * exploit THREADS; try apply TH2; eauto. i. des.
          exploit SCThread.rtc_all_step_disjoint; eauto. i. des.
          auto.
        * eapply DISJOINT; [|eauto|eauto]. auto.
      + i. Configuration.simplify.
        exploit THREADS; try apply TH; eauto. i.
        exploit SCThread.rtc_all_step_disjoint; eauto. i. des.
        auto.
    Qed.

    Lemma all_steps_future
          c1 c2
          (STEPS: rtc all_step c1 c2)
          (WF1: Configuration.wf c1):
      (<<WF2: Configuration.wf c2>>) /\
      (<<SC_FUTURE: TimeMap.le (Configuration.sc c1) (Configuration.sc c2)>>) /\
      (<<MEM_FUTURE: Memory.future (Configuration.memory c1) (Configuration.memory c2)>>).
    Proof.
      ginduction STEPS; eauto.
      - i. esplits; eauto; try refl.
      - i. inv H. exploit step_future; eauto. i. des.
        exploit IHSTEPS; eauto. i. des. esplits; eauto. etrans; eauto.
    Qed.
  End SCConfiguration.
End SCConfiguration.


Definition is_accessing (e:ProgramEvent.t): option Loc.t :=
  match e with
  | ProgramEvent.read loc _ _ => Some loc
  | ProgramEvent.write loc _ _ => Some loc
  | ProgramEvent.update loc _ _ _ _ => Some loc
  | _ => None
  end.


(** L-SC race **)
Module SCRace.
  Section SCRace.
    Variable L: Loc.t -> bool.

    Definition race lang (th: Thread.t lang): Prop :=
      exists e st' loc,
        (<<STEP: Language.step _ e (Thread.state th) st'>>) /\
        (<<ACCESS: is_accessing e = (Some loc)>>) /\
        (<<LOC: L loc>>) /\
        (<<MAXIMAL: SCLocal.non_maximal (Thread.local th) (Thread.memory th) loc>>).

    Definition race_steps (c: Configuration.t) (tid: Ident.t): Prop :=
      exists lang st1 lc1 e2,
        (<<TID: IdentMap.find tid (Configuration.threads c) = Some (existT _ lang st1, lc1)>>) /\
        (<<THREAD_STEPS: rtc (SCThread.all_step L)
                             (Thread.mk _ st1 lc1 (Configuration.sc c) (Configuration.memory c)) e2>>) /\
        (<<CONS: Local.promise_consistent (Thread.local e2)>>) /\
        (<<SCRACE: race e2>>).

    Definition racefree (c: Configuration.t): Prop :=
      forall tid c2
             (STEPS: rtc (SCConfiguration.all_step L) c c2),
        ~ race_steps c2 tid.

    Definition racefree_syn (syn: Threads.syntax): Prop :=
      racefree (Configuration.init syn).

    Lemma step_racefree
          e tid c1 c2
          (RACEFREE: racefree c1)
          (STEP: SCConfiguration.step L e tid c1 c2):
      racefree c2.
    Proof.
      ii. eapply RACEFREE; cycle 1; eauto.
      econs 2; eauto. econs; eauto.
    Qed.
  End SCRace.
End SCRace.
