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

Require Import LocalPF.

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
        (CAP: Memory.cap e.(Thread.memory) mem1)
        (SC_MAX: Memory.max_concrete_timemap mem1 sc1),
        <<FAILURE: steps_failure (Thread.mk lang e.(Thread.state) e.(Thread.local) sc1 mem1)>> \/
        exists e2,
          <<STEPS: rtc tau_step (Thread.mk lang e.(Thread.state) e.(Thread.local) sc1 mem1) e2>> /\
          <<PROMISES: e2.(Thread.local).(Local.promises) = Memory.bot>>.


    (* future *)

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

    Lemma rtc_all_step_future
          e1 e2
          (STEPS: rtc all_step e1 e2)
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
      revert WF1 SC1 CLOSED1. induction STEPS; i.
      - esplits; eauto; refl.
      - inv H. inv USTEP. exploit step_future; eauto. i. des.
        exploit IHSTEPS; eauto. i. des.
        esplits; eauto; etrans; eauto.
    Qed.

    Lemma rtc_tau_step_future
          e1 e2
          (STEPS: rtc tau_step e1 e2)
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
      eapply rtc_all_step_future; eauto.
      eapply rtc_implies; try exact STEPS.
      apply tau_union.
    Qed.


    (* disjoint *)

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
      - eapply Thread.promise_step_disjoint; eauto.
      - inv STEP0. eapply OrdLocal.program_step_disjoint; eauto.
    Qed.

    Lemma rtc_all_step_disjoint
          e1 e2 lc
          (STEPS: rtc all_step e1 e2)
          (WF1: Local.wf e1.(Thread.local) e1.(Thread.memory))
          (SC1: Memory.closed_timemap e1.(Thread.sc) e1.(Thread.memory))
          (CLOSED1: Memory.closed e1.(Thread.memory))
          (DISJOINT1: Local.disjoint e1.(Thread.local) lc)
          (WF: Local.wf lc e1.(Thread.memory)):
      <<DISJOINT2: Local.disjoint e2.(Thread.local) lc>> /\
      <<WF: Local.wf lc e2.(Thread.memory)>>.
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
          (WF1: Local.wf e1.(Thread.local) e1.(Thread.memory))
          (SC1: Memory.closed_timemap e1.(Thread.sc) e1.(Thread.memory))
          (CLOSED1: Memory.closed e1.(Thread.memory))
          (DISJOINT1: Local.disjoint e1.(Thread.local) lc)
          (WF: Local.wf lc e1.(Thread.memory)):
      <<DISJOINT2: Local.disjoint e2.(Thread.local) lc>> /\
      <<WF: Local.wf lc e2.(Thread.memory)>>.
    Proof.
      eapply rtc_all_step_disjoint; try exact DISJOINT1; eauto.
      eapply rtc_implies; try exact STEPS.
      apply tau_union.
    Qed.


    (* promise_consistent *)

    Lemma step_promise_consistent
          pf e e1 e2
          (STEP: step pf e e1 e2)
          (WF1: Local.wf e1.(Thread.local) e1.(Thread.memory))
          (SC1: Memory.closed_timemap e1.(Thread.sc) e1.(Thread.memory))
          (CLOSED1: Memory.closed e1.(Thread.memory))
          (CONS: Local.promise_consistent e2.(Thread.local)):
      Local.promise_consistent e1.(Thread.local).
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
    Qed.

    Lemma rtc_all_step_promise_consistent
          e1 e2
          (STEPS: rtc all_step e1 e2)
          (WF1: Local.wf e1.(Thread.local) e1.(Thread.memory))
          (SC1: Memory.closed_timemap e1.(Thread.sc) e1.(Thread.memory))
          (CLOSED1: Memory.closed e1.(Thread.memory))
          (CONS: Local.promise_consistent e2.(Thread.local)):
      Local.promise_consistent e1.(Thread.local).
    Proof.
      revert WF1 SC1 CLOSED1 CONS. induction STEPS; ss. i.
      inv H. inv USTEP. exploit step_future; eauto. i. des.
      eapply step_promise_consistent; eauto.
    Qed.

    Lemma rtc_tau_step_promise_consistent
          e1 e2
          (STEPS: rtc tau_step e1 e2)
          (WF1: Local.wf e1.(Thread.local) e1.(Thread.memory))
          (SC1: Memory.closed_timemap e1.(Thread.sc) e1.(Thread.memory))
          (CLOSED1: Memory.closed e1.(Thread.memory))
          (CONS: Local.promise_consistent e2.(Thread.local)):
      Local.promise_consistent e1.(Thread.local).
    Proof.
      eapply rtc_all_step_promise_consistent; try exact CONS; eauto.
      eapply rtc_implies; try exact STEPS.
      apply tau_union.
    Qed.

    Lemma cap_step_current_step
          pf e e0 e1 fe0
          (THREAD: thread_map ident_map e0 fe0)
          (STEP: step pf e e0 e1)
          (LOCAL: Local.wf e0.(Thread.local) e0.(Thread.memory))
          (FLOCAL: Local.wf fe0.(Thread.local) fe0.(Thread.memory))
          (MEMORY: Memory.closed e0.(Thread.memory))
          (FMEMORY: Memory.closed fe0.(Thread.memory))
          (SC: Memory.closed_timemap e0.(Thread.sc) e0.(Thread.memory))
          (FSC: Memory.closed_timemap fe0.(Thread.sc) fe0.(Thread.memory))
      :
        exists fe fe1,
          (<<THREAD: thread_map ident_map e1 fe1>>) /\
          (<<STEP: step pf fe fe0 fe1>>) /\
          (<<EVENT: tevent_map ident_map fe e>>).
    Proof.
      assert (MAPLT: mapping_map_lt ident_map).
      { eapply ident_map_lt. }
      assert (MAPLE: mapping_map_le ident_map).
      { eapply ident_map_le. }
      assert (MAPEQ: mapping_map_eq ident_map).
      { eapply ident_map_eq. }

      inv THREAD. ss. inv STEP.
      { inv STEP0. inv LOCAL1.
        exploit promise_map; try apply PROMISE; eauto; ss.
        { eapply FLOCAL. }
        { eapply LOCAL0. }
        { eapply mapping_map_lt_non_collapsable; eauto. }
        { eapply ident_map_message. }
        i. des. inv LOCAL0.
        eexists _, (Thread.mk _ st (Local.mk (Local.tview flc) fprom1) fsc fmem1).
        esplits; eauto.
        { econs; eauto.
          { econs; eauto. }
          { eapply mapping_map_lt_collapsable_unwritable; eauto. }
        }
        { econs 1. econs.
          { econs; eauto. eapply closed_message_map; eauto.
            eapply ident_map_message. }
          { inv KIND; ss. inv MSG; ss. }
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
          { econs; eauto. eapply mapping_map_lt_collapsable_unwritable; eauto. }
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
          { eapply mapping_map_lt_non_collapsable; eauto. }
          i. des.
          exists (ThreadEvent.write loc from to val freleasedw ord). esplits.
          { econs; eauto. eapply mapping_map_lt_collapsable_unwritable; eauto. }
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
          { eapply mapping_map_lt_collapsable_unwritable; eauto. }
          { refl. }
          { eapply mapping_map_lt_non_collapsable; eauto. }
          i. des.
          exists (ThreadEvent.update loc fto tsw valr valw freleased freleasedw ordr ordw). esplits.
          { econs; eauto. eapply mapping_map_lt_collapsable_unwritable; eauto. }
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
      }
    Qed.
  End OrdThread.
End OrdThread.


Module OrdConfiguration.
  Section OrdConfiguration.
    Variable L: Loc.t -> bool.
    Variable ordc: Ordering.t.

    Inductive step: forall (e: ThreadEvent.t) (tid: Ident.t) (c1 c2: Configuration.t), Prop :=
    | step_intro
        e tid c1 lang st1 lc1 e2 e3 st4 lc4 sc4 memory4
        (TID: IdentMap.find tid c1.(Configuration.threads) = Some (existT _ lang st1, lc1))
        (CANCELS: rtc (@Thread.cancel_step _) (Thread.mk _ st1 lc1 c1.(Configuration.sc) c1.(Configuration.memory)) e2)
        (STEP: OrdThread.opt_step L ordc e e2 e3)
        (RESERVES: rtc (@Thread.reserve_step _) e3 (Thread.mk _ st4 lc4 sc4 memory4))
        (CONSISTENT: e <> ThreadEvent.failure ->
                     OrdThread.consistent L ordc (Thread.mk _ st4 lc4 sc4 memory4)):
        step e tid c1 (Configuration.mk (IdentMap.add tid (existT _ _ st4, lc4) c1.(Configuration.threads)) sc4 memory4)
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
