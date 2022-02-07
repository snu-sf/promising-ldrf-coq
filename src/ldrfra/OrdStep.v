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

Require Import PromiseConsistent.
Require Import Mapping.

Require Import PFStep.

Set Implicit Arguments.


Module OrdLocal.
  Section OrdLocal.
    Variable L: Loc.t -> bool.
    Variable ordcr: Ordering.t.
    Variable ordcw: Ordering.t.

    Inductive read_step (lc1:Local.t) (mem1:Memory.t) (loc:Loc.t) (to:Time.t) (val:Const.t) (released:option View.t) (ord:Ordering.t) (lc2:Local.t): Prop :=
    | read_step_intro
        ord'
        (ORD: ord' = if L loc then Ordering.join ord ordcr else ord)
        (STEP: Local.read_step lc1 mem1 loc to val released ord' lc2)
    .
    Hint Constructors read_step.

    Inductive write_step (lc1:Local.t) (sc1:TimeMap.t) (mem1:Memory.t)
              (loc:Loc.t) (from to:Time.t)
              (val:Const.t) (releasedm released:option View.t) (ord:Ordering.t)
              (lc2:Local.t) (sc2:TimeMap.t) (mem2:Memory.t) (kind:Memory.op_kind): Prop :=
    | write_step_intro
        ord'
        (ORD: ord' = if L loc then Ordering.join ord ordcw else ord)
        (STEP: Local.write_step lc1 sc1 mem1 loc from to val releasedm released ord' lc2 sc2 mem2 kind)
    .
    Hint Constructors write_step.

    Inductive write_na_step (lc1:Local.t) (sc1:TimeMap.t) (mem1:Memory.t)
                            (loc:Loc.t) (from to:Time.t) (val:Const.t) (ord:Ordering.t)
                            (lc2:Local.t) (sc2:TimeMap.t) (mem2:Memory.t):
      forall (msgs: list (Time.t * Time.t * Message.t))
        (kinds: list Memory.op_kind) (kind:Memory.op_kind), Prop :=
    | write_na_step_na
        ord' msgs kinds kind
        (ORD: ord' = if L loc then Ordering.join ord ordcw else ord)
        (STEP: Local.write_na_step lc1 sc1 mem1 loc from to val ord' lc2 sc2 mem2 msgs kinds kind):
      write_na_step lc1 sc1 mem1 loc from to val ord lc2 sc2 mem2 msgs kinds kind
    | write_na_step_at
        released ord' kind
        (LOC: L loc)
        (NA: Ordering.le ord Ordering.na)
        (ORD: ord' = Ordering.join ord ordcw)
        (STEP: Local.write_step lc1 sc1 mem1 loc from to val None released ord' lc2 sc2 mem2 kind):
      write_na_step lc1 sc1 mem1 loc from to val ord lc2 sc2 mem2 [] [] kind
    .
    Hint Constructors write_na_step.

    Inductive racy_read_step (lc1:Local.t) (mem1:Memory.t) (loc:Loc.t) (val:Const.t) (ord:Ordering.t): Prop :=
    | racy_read_step_intro
        ord'
        (ORD: ord' = if L loc then Ordering.join ord ordcr else ord)
        (STEP: Local.racy_read_step lc1 mem1 loc val ord')
    .
    Hint Constructors racy_read_step.

    Inductive racy_write_step (lc1:Local.t) (mem1:Memory.t) (loc:Loc.t) (ord:Ordering.t): Prop :=
    | racy_write_step_intro
        ord'
        (ORD: ord' = if L loc then Ordering.join ord ordcw else ord)
        (STEP: Local.racy_write_step lc1 mem1 loc ord')
    .
    Hint Constructors racy_write_step.

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
        loc val ord
        (LOCAL: racy_read_step lc1 mem1 loc val ord):
      program_step (ThreadEvent.racy_read loc val ord) lc1 sc1 mem1 lc1 sc1 mem1
    | step_racy_write
        lc1 sc1 mem1
        loc val ord
        (LOCAL: racy_write_step lc1 mem1 loc ord):
      program_step (ThreadEvent.racy_write loc val ord) lc1 sc1 mem1 lc1 sc1 mem1
    | step_racy_update
        lc1 sc1 mem1
        loc valr valw ordr ordw
        (LOCAL: Local.racy_update_step lc1 mem1 loc ordr ordw):
      program_step (ThreadEvent.racy_update loc valr valw ordr ordw) lc1 sc1 mem1 lc1 sc1 mem1
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
        + exploit Local.write_na_step_future; eauto.
        + exploit Local.write_step_future; eauto. i. des. splits; ss.
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
      - inv LOCAL. inv STEP. eapply Memory.write_inhabited; eauto.
      - inv LOCAL2. inv STEP. eapply Memory.write_inhabited; eauto.
      - inv LOCAL.
        + inv STEP. eapply Memory.write_na_inhabited; eauto.
        + inv STEP. eapply Memory.write_inhabited; eauto.
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
        + exploit Local.write_na_step_disjoint; eauto.
        + exploit Local.write_step_disjoint; eauto.
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


    (* reserve only *)

    Definition reserve_only (promises: Memory.t): Prop :=
      forall loc from to msg
        (LOC: L loc)
        (GET: Memory.get loc to promises = Some (from, msg)),
        msg = Message.reserve.

    Lemma promise_reserve_only
          promises1 mem1 loc from to msg promises2 mem2 kind
          (PROMISES1: reserve_only promises1)
          (LOC: L loc -> msg = Message.reserve)
          (PROMISE: Memory.promise promises1 mem1 loc from to msg promises2 mem2 kind):
      reserve_only promises2.
    Proof.
      ii. revert GET. inv PROMISE; ss.
      - erewrite Memory.add_o; eauto. condtac; ss; eauto.
        i. des. clarify. eauto.
      - erewrite Memory.split_o; eauto. repeat condtac; ss; eauto.
        + i. des. clarify. eauto.
        + guardH o. i. des. clarify.
          exploit Memory.split_get0; try exact PROMISES. i. des.
          exploit PROMISES1; eauto.
      - erewrite Memory.lower_o; eauto. condtac; ss; eauto.
        i. des. clarify. eauto.
      - erewrite Memory.remove_o; eauto. condtac; ss; eauto.
    Qed.

    Lemma write_reserve_only
          promises1 mem1 loc from to msg promises2 mem2 kind
          (PROMISES1: reserve_only promises1)
          (WRITE: Memory.write promises1 mem1 loc from to msg promises2 mem2 kind):
      reserve_only promises2.
    Proof.
      ii. revert GET. inv WRITE.
      erewrite Memory.remove_o; eauto. condtac; ss. guardH o.
      inv PROMISE; ss.
      - erewrite Memory.add_o; eauto. condtac; ss; eauto.
      - erewrite Memory.split_o; eauto. repeat condtac; ss; eauto.
        guardH o0. i. des. inv GET.
        exploit Memory.split_get0; try exact PROMISES. i. des.
        exploit PROMISES1; try exact GET0; ss.
      - erewrite Memory.lower_o; eauto. condtac; ss; eauto.
      - erewrite Memory.remove_o; eauto. condtac; ss; eauto.
    Qed.

    Lemma write_na_reserve_only
          ts promises1 mem1 loc from to msg promises2 mem2 msgs kinds kind
          (PROMISES1: reserve_only promises1)
          (WRITE: Memory.write_na ts promises1 mem1 loc from to msg promises2 mem2 msgs kinds kind):
      reserve_only promises2.
    Proof.
      induction WRITE; eauto using write_reserve_only.
    Qed.

    Lemma program_step_reserve_only
          e lc1 sc1 mem1 lc2 sc2 mem2
          (PROMISES1: reserve_only (Local.promises lc1))
          (STEP: program_step e lc1 sc1 mem1 lc2 sc2 mem2):
      <<PROMISES2: reserve_only (Local.promises lc2)>>.
    Proof.
      inv STEP; try inv LOCAL; try inv STEP; ss.
      - eapply write_reserve_only; eauto.
      - inv LOCAL1. inv STEP. inv LOCAL2. inv STEP. ss.
        eapply write_reserve_only; eauto.
      - eapply write_na_reserve_only; eauto.
      - eapply write_reserve_only; eauto.
    Qed.

    Lemma reserve_only_write_add
          promises1 mem1 loc from to msg promises2 mem2 kind
          (RESERVE_ONLY: reserve_only promises1)
          (LOC: L loc)
          (WRITE: Memory.write promises1 mem1 loc from to msg promises2 mem2 kind):
      kind = Memory.op_kind_add.
    Proof.
      inv WRITE. inv PROMISE; ss; exfalso.
      - exploit Memory.split_get0; try exact PROMISES. i. des. eauto.
      - exploit Memory.lower_get0; try exact PROMISES. i. des.
        exploit RESERVE_ONLY; eauto. i. subst. inv MSG_LE. ss.
      - exploit Memory.remove_get0; try exact PROMISES. i. des.
        exploit Memory.remove_get0; try exact REMOVE. i. des. congr.
    Qed.

    Lemma ordc_na
          ordc ord loc
          (ORDC: Ordering.le ordc Ordering.na):
      (if L loc then Ordering.join ord ordc else ord) = ord.
    Proof.
      condtac; ss.
      destruct ordc, ord; ss.
    Qed.

    Lemma write_step_le
          lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind
          ordc'
          (STEP: write_step lc1 sc1 mem1 loc from to val releasedm released
                            (if L loc then Ordering.join ord ordc' else ord) lc2 sc2 mem2 kind)
          (ORDC: Ordering.le ordc' ordcw):
      write_step lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind.
    Proof.
      econs; eauto.
      inv STEP. condtac; ss.
      replace (Ordering.join ord ordcw) with
          (Ordering.join (Ordering.join ord ordc') ordcw); ss.
      destruct ord, ordcw, ordc'; ss.
    Qed.

    Lemma racy_write_step_le
          lc1 mem1 loc ord
          ordc'
          (STEP: racy_write_step lc1 mem1 loc (if L loc then Ordering.join ord ordc' else ord))
          (ORDC: Ordering.le ordc' ordcw):
      racy_write_step lc1 mem1 loc ord.
    Proof.
      inv STEP. econs; eauto. condtac; ss.
      replace (Ordering.join ord ordcw) with
          (Ordering.join (Ordering.join ord ordc') ordcw); ss.
      destruct ord, ordcw, ordc'; ss.
    Qed.
  End OrdLocal.
End OrdLocal.


Module OrdThread.
  Section OrdThread.
    Variable lang: language.
    Variable L: Loc.t -> bool.
    Variable ordcr: Ordering.t.
    Variable ordcw: Ordering.t.

    Inductive program_step (e:ThreadEvent.t): forall (e1 e2:Thread.t lang), Prop :=
    | program_step_intro
        st1 lc1 sc1 mem1
        st2 lc2 sc2 mem2
        (STATE: (Language.step lang) (ThreadEvent.get_program_event e) st1 st2)
        (LOCAL: OrdLocal.program_step L ordcr ordcw e lc1 sc1 mem1 lc2 sc2 mem2):
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
      exists e2 e3,
        <<STEPS: rtc tau_step e1 e2>> /\
        <<FAILURE: step true ThreadEvent.failure e2 e3>>.
    Hint Unfold steps_failure.

    Definition consistent (e: Thread.t lang): Prop :=
      forall mem1 sc1
        (CAP: Memory.cap (Thread.memory e) mem1)
        (SC_MAX: Memory.max_concrete_timemap mem1 sc1),
        <<FAILURE: steps_failure (Thread.mk lang (Thread.state e) (Thread.local e) sc1 mem1)>> \/
        exists e2,
          <<STEPS: rtc tau_step (Thread.mk lang (Thread.state e) (Thread.local e) sc1 mem1) e2>> /\
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
      inv STEP. ss. eapply OrdLocal.program_step_future; eauto.
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
      - inv STEP0. eapply OrdLocal.program_step_disjoint; eauto.
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
          * eapply write_na_step_promise_consistent; eauto.
          * eapply write_step_promise_consistent; eauto.
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

    Lemma cap_step_current_step
          pf e e0 e1 fe0
          (THREAD: thread_map ident_map e0 fe0)
          (STEP: step pf e e0 e1)
          (LOCAL: Local.wf (Thread.local e0) (Thread.memory e0))
          (FLOCAL: Local.wf (Thread.local fe0) (Thread.memory fe0))
          (MEMORY: Memory.closed (Thread.memory e0))
          (FMEMORY: Memory.closed (Thread.memory fe0))
          (SC: Memory.closed_timemap (Thread.sc e0) (Thread.memory e0))
          (FSC: Memory.closed_timemap (Thread.sc fe0) (Thread.memory fe0))
      :
        exists fe fe1,
          (<<THREAD: thread_map ident_map e1 fe1>>) /\
          (<<STEP: step pf fe fe0 fe1>>) /\
          (<<EVENT: tevent_map ident_map fe e>>).
    Proof.
      assert (MAPLT: mapping_map_lt_iff ident_map).
      { eapply ident_map_lt_iff. }
      assert (MAPLE: mapping_map_le ident_map).
      { eapply ident_map_le. }
      assert (MAPEQ: mapping_map_eq ident_map).
      { eapply ident_map_eq. }

      inv THREAD. ss. inv STEP.
      { inv STEP0. inv LOCAL1.
        exploit promise_map; try apply PROMISE; eauto; ss.
        { eapply FLOCAL. }
        { eapply LOCAL0. }
        { eapply mapping_map_lt_iff_non_collapsable; eauto. }
        { eapply ident_map_message. }
        i. des. inv LOCAL0.
        eexists _, (Thread.mk _ st (Local.mk (Local.tview flc) fprom1) fsc fmem1).
        esplits; eauto.
        { econs; eauto.
          { econs; eauto. }
          { eapply mapping_map_lt_iff_collapsable_unwritable; eauto. }
        }
        { econs 1. econs.
          { econs; eauto. eapply closed_message_map; eauto.
            eapply ident_map_message. }
          { inv KIND; ss. }
          { unfold PF.pf_event in *. i. inv PROMISE1. eauto. }
        }
        { econs; eauto; ss. eapply ident_map_message. }
      }
      { inv STEP0. inv LOCAL1.
        { esplits; eauto.
          { econs; eauto. }
          { econs 2; eauto. econs; eauto. econs 1; eauto. }
          { econs; eauto. }
        }
        { inv LOCAL2. exploit read_step_map; eauto.
          { eapply ident_map_bot. }
          { eapply FLOCAL. } i. des.
          exists (ThreadEvent.read loc fto val freleased ord). esplits.
          { econs; eauto. eapply mapping_map_lt_iff_collapsable_unwritable; eauto. }
          { econs 2; eauto. econs; eauto. econs 2; eauto. econs; eauto. }
          { econs; eauto. }
        }
        { inv LOCAL2. hexploit write_step_map; try eassumption; eauto.
          { eapply ident_map_bot. }
          { eapply FLOCAL. }
          { eapply FLOCAL. }
          { econs 2. }
          { refl. }
          { refl. }
          { eapply mapping_map_lt_iff_non_collapsable; eauto. }
          i. des.
          exists (ThreadEvent.write loc from to val freleasedw ord). esplits.
          { econs; eauto. eapply mapping_map_lt_iff_collapsable_unwritable; eauto. }
          { econs 2; eauto. econs; eauto. econs 3; eauto. econs; eauto. }
          { econs; eauto; ss. }
        }
        { inv LOCAL2. inv LOCAL3. exploit read_step_map; eauto.
          { eapply ident_map_bot. }
          { eapply FLOCAL. } i. des.
          hexploit Local.read_step_future; try apply STEP; eauto. i. des.
          hexploit Local.read_step_future; try apply READ; eauto. i. des.
          hexploit write_step_map; try eapply STEP0; try eassumption; eauto.
          { eapply ident_map_bot. }
          { eapply WF0. }
          { eapply WF0. }
          { eapply mapping_map_lt_iff_collapsable_unwritable; eauto. }
          { refl. }
          { eapply mapping_map_lt_iff_non_collapsable; eauto. }
          i. des.
          exists (ThreadEvent.update loc fto tsw valr valw freleased freleasedw ordr ordw). esplits.
          { econs; eauto. eapply mapping_map_lt_iff_collapsable_unwritable; eauto. }
          { econs 2; eauto. econs; eauto. econs 4; eauto.
            { econs; eauto. }
            { econs; eauto. }
          }
          { econs; eauto; ss. }
        }
        { inv LOCAL2. exploit fence_step_map; try apply FENCE; eauto.
          { eapply ident_map_bot. }
          { eapply FLOCAL. } i. des.
          exists (ThreadEvent.fence ordr ordw). esplits.
          { econs; eauto. }
          { econs 2; eauto. econs; eauto. econs 5; eauto. }
          { econs; eauto; ss. }
        }
        { inv LOCAL2. exploit fence_step_map; eauto.
          { eapply ident_map_bot. }
          { eapply FLOCAL. } i. des.
          exists (ThreadEvent.syscall e0). esplits.
          { econs; eauto. }
          { econs 2; eauto. econs; eauto. econs 6; eauto. }
          { econs; eauto; ss. }
        }
        { inv LOCAL2. exploit failure_step_map; eauto. i.
          exists (ThreadEvent.failure). esplits.
          { econs; eauto. }
          { econs 2; eauto. econs; eauto. econs 7; eauto. }
          { econs; eauto; ss. }
        }
        { inv LOCAL2.
          { hexploit write_na_step_map; try eassumption; eauto.
            { eapply ident_map_bot. }
            { eapply FLOCAL. }
            { eapply FLOCAL. }
            { refl. }
            { refl. }
            { eapply mapping_map_lt_iff_non_collapsable; eauto. }
            { instantiate (1 := List.map fst msgs). clear.
              induction msgs; ss.
              econs; eauto. destruct a as [[]]. ss.
            }
            { rewrite List.Forall_forall. i.
              eapply mapping_map_lt_iff_non_collapsable; eauto.
            }
            i. des.
            exists (ThreadEvent.write_na loc fmsgs from to val ord). esplits.
            { econs; eauto. eapply mapping_map_lt_iff_collapsable_unwritable; eauto. }
            { econs 2; eauto. econs; eauto. econs 8; eauto. econs; eauto. }
            { econs; eauto; ss. }
          }
          { hexploit write_step_map; try eassumption; eauto.
            { eapply ident_map_bot. }
            { eapply FLOCAL. }
            { eapply FLOCAL. }
            { econs 2. }
            { refl. }
            { refl. }
            { eapply mapping_map_lt_iff_non_collapsable; eauto. }
            i. des.
            exists (ThreadEvent.write_na loc [] from to val ord). esplits.
            { econs; eauto. eapply mapping_map_lt_iff_collapsable_unwritable; eauto. }
            { econs 2; eauto. econs; eauto. econs 8; eauto. econs 2; eauto. }
            { econs; eauto; ss. }
          }
        }
        { inv LOCAL2. exploit racy_read_step_map; eauto.
          { apply ident_map_lt. }
          i. exists (ThreadEvent.racy_read loc val ord). esplits.
          { econs; eauto. }
          { econs 2; eauto. econs; eauto. econs 9; eauto. econs; eauto. }
          { econs; eauto; ss. }
        }
        { inv LOCAL2. exploit racy_write_step_map; eauto.
          { apply ident_map_lt. }
          i. exists (ThreadEvent.racy_write loc val ord). esplits.
          { econs; eauto. }
          { econs 2; eauto. econs; eauto. econs 10; eauto. econs; eauto. }
          { econs; eauto; ss. }
        }
        { exploit racy_update_step_map; eauto.
          { apply ident_map_lt. }
          i. exists (ThreadEvent.racy_update loc valr valw ordr ordw). esplits.
          { econs; eauto. }
          { econs 2; eauto. econs; eauto. econs 11; eauto. }
          { econs; eauto; ss. }
        }
      }
    Qed.


    (* reserve only *)

    Lemma step_reserve_only
          pf e e1 e2
          (PROMISES1: OrdLocal.reserve_only L (Local.promises (Thread.local e1)))
          (STEP: step pf e e1 e2):
      <<PROMISES2: OrdLocal.reserve_only L (Local.promises (Thread.local e2))>>.
    Proof.
      inv STEP; inv STEP0; eauto using OrdLocal.program_step_reserve_only.
      ii. revert GET. inv LOCAL. inv PROMISE; ss.
      - erewrite Memory.add_o; eauto. condtac; ss; eauto.
        i. des. inv GET. exploit PF; eauto.
      - erewrite Memory.split_o; eauto. repeat condtac; ss; eauto.
        + i. des. inv GET. exploit PF; eauto.
        + guardH o. i. des. inv GET.
          exploit Memory.split_get0; try exact PROMISES. i. des.
          exploit PF; try exact GET0; eauto.
      - erewrite Memory.lower_o; eauto. condtac; ss; eauto.
        i. des. inv GET. exploit PF; eauto.
      - erewrite Memory.remove_o; eauto. condtac; ss; eauto.
    Qed.

    Lemma reserve_step_reserve_only
          e1 e2
          (PROMISES1: OrdLocal.reserve_only L (Local.promises (Thread.local e1)))
          (STEP: @Thread.reserve_step lang e1 e2):
      <<PROMISES2: OrdLocal.reserve_only L (Local.promises (Thread.local e2))>>.
    Proof.
      inv STEP. inv STEP0; inv STEP; inv LOCAL. ss.
      eapply OrdLocal.promise_reserve_only; eauto.
      Qed.

    Lemma cancel_step_reserve_only
          e1 e2
          (PROMISES1: OrdLocal.reserve_only L (Local.promises (Thread.local e1)))
          (STEP: @Thread.cancel_step lang e1 e2):
      <<PROMISES2: OrdLocal.reserve_only L (Local.promises (Thread.local e2))>>.
    Proof.
      inv STEP. inv STEP0; inv STEP; inv LOCAL. ss.
      eapply OrdLocal.promise_reserve_only; eauto.
      Qed.
  End OrdThread.
End OrdThread.


Module OrdConfiguration.
  Section OrdConfiguration.
    Variable L: Loc.t -> bool.
    Variable ordcr: Ordering.t.
    Variable ordcw: Ordering.t.

    Inductive step: forall (e: ThreadEvent.t) (tid: Ident.t) (c1 c2: Configuration.t), Prop :=
    | step_intro
        e tid c1 lang st1 lc1 e2 e3 st4 lc4 sc4 memory4
        (TID: IdentMap.find tid (Configuration.threads c1) = Some (existT _ lang st1, lc1))
        (CANCELS: rtc (@Thread.cancel_step _) (Thread.mk _ st1 lc1 (Configuration.sc c1) (Configuration.memory c1)) e2)
        (STEP: OrdThread.opt_step L ordcr ordcw e e2 e3)
        (RESERVES: rtc (@Thread.reserve_step _) e3 (Thread.mk _ st4 lc4 sc4 memory4))
        (CONSISTENT: ThreadEvent.get_machine_event e <> MachineEvent.failure ->
                     OrdThread.consistent L ordcr ordcw (Thread.mk _ st4 lc4 sc4 memory4)):
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
  End OrdConfiguration.
End OrdConfiguration.
