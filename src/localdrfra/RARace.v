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

Require Import OrdStep.


Module ReleaseWrites.
  Section ReleaseWrites.
    Variable L: Loc.t -> bool.

    Definition t: Type := list (Loc.t * Time.t).

    Definition append (e: ThreadEvent.t) (rels: t): t :=
      match ThreadEvent.is_writing e with
      | Some (loc, from, to, val, released, ord) =>
        if L loc
        then if Ordering.le Ordering.acqrel ord then (loc, to) :: rels else rels
        else rels
      | None => rels
      end.

    Definition wf (rels: t) (promises mem: Memory.t): Prop :=
      forall loc to (IN: List.In (loc, to) rels),
        Memory.get loc to promises = None /\
        exists from val released,
          Memory.get loc to mem = Some (from, Message.concrete val released).

    Lemma append_app e rels1 rels2:
      append e rels1 ++ rels2 = append e (rels1 ++ rels2).
    Proof.
      unfold append. des_ifs.
    Qed.

    Lemma in_append_or
          loc to e rels
          (IN: List.In (loc, to) (append e rels)):
      (exists from val released ord,
          ThreadEvent.is_writing e = Some (loc, from, to, val, released, ord) /\
          L loc /\ Ordering.le Ordering.acqrel ord) \/
      List.In (loc, to) rels.
    Proof.
      revert IN. unfold append. des_ifs; eauto. i.
      inv IN; eauto. inv H. left. esplits; eauto.
    Qed.
  End ReleaseWrites.
End ReleaseWrites.


Module RAThread.
  Section RAThread.
    Variable lang: language.
    Variable L: Loc.t -> bool.

    Definition ra_race (rels: ReleaseWrites.t) (tview: TView.t) (loc: Loc.t) (to: Time.t) (ordr: Ordering.t): Prop :=
      (<<LOC: L loc>>) /\
      (<<HIGHER: Time.lt (tview.(TView.cur).(View.rlx) loc) to>>) /\
      ((<<ORDW: ~ List.In (loc, to) rels>>) \/
       (<<ORDR: Ordering.le ordr Ordering.strong_relaxed>>)).

    Inductive step rels1: forall (rels2: ReleaseWrites.t) (e: ThreadEvent.t) (e1 e2: Thread.t lang), Prop :=
    | step_normal
        pf e e1 e2
        (STEP: @OrdThread.step lang L Ordering.acqrel pf e e1 e2):
        step rels1 (ReleaseWrites.append L e rels1) e e1 e2
    | step_race
        pf e e1 e2
        loc to val released ord
        (STEP: @OrdThread.step lang L Ordering.acqrel pf e e1 e2)
        (CONS: Local.promise_consistent e1.(Thread.local))
        (EVENT: ThreadEvent.is_reading e = Some (loc, to, val, released, ord))
        (RACE: ra_race rels1 e1.(Thread.local).(Local.tview) loc to ord):
        step rels1 (ReleaseWrites.append L e rels1) ThreadEvent.failure e1 e2
    .

    Inductive steps rels1: forall (rels2: ReleaseWrites.t) (e1 e2: Thread.t lang), Prop :=
    | steps_refl
        e:
        steps rels1 rels1 e e
    | steps_step
        rels2 rels3 e e1 e2 e3
        (STEP: step rels1 rels2 e e1 e2)
        (STEPS: steps rels2 rels3 e2 e3):
        steps rels1 rels3 e1 e3
    .
    Hint Constructors steps.

    Inductive tau_steps rels1: forall (rels2: ReleaseWrites.t) (e1 e2: Thread.t lang), Prop :=
    | tau_steps_refl
        e:
        tau_steps rels1 rels1 e e
    | tau_steps_step
        rels2 rels3 e e1 e2 e3
        (STEP: step rels1 rels2 e e1 e2)
        (SILENT: ThreadEvent.get_machine_event e = MachineEvent.silent)
        (STEPS: tau_steps rels2 rels3 e2 e3):
        tau_steps rels1 rels3 e1 e3
    .
    Hint Constructors tau_steps.

    Definition steps_failure (rels1: ReleaseWrites.t) (e1: Thread.t lang): Prop :=
      exists rels2 rels3 e2 e3,
        (<<STEPS: tau_steps rels1 rels2 e1 e2>>) /\
        (<<FAILURE: step rels2 rels3 ThreadEvent.failure e2 e3>>).
    Hint Unfold steps_failure.

    Definition consistent (rels: ReleaseWrites.t) (e: Thread.t lang): Prop :=
      forall mem1 sc1
        (CAP: Memory.cap e.(Thread.memory) mem1)
        (SC_MAX: Memory.max_concrete_timemap mem1 sc1),
        (<<FAILURE: steps_failure rels (Thread.mk lang e.(Thread.state) e.(Thread.local) sc1 mem1)>>) \/
        exists rels2 e2,
          <<STEPS: tau_steps rels rels2 (Thread.mk lang e.(Thread.state) e.(Thread.local) sc1 mem1) e2>> /\
          <<PROMISES: e2.(Thread.local).(Local.promises) = Memory.bot>>.


    Lemma tau_steps_ord_tau_steps
          rels1 rels2 e1 e2
          (STEPS: tau_steps rels1 rels2 e1 e2):
      rtc (@OrdThread.tau_step lang L Ordering.acqrel) e1 e2.
    Proof.
      induction STEPS; eauto.
      inv STEP; ss.
      econs 2; eauto. econs; eauto. econs. eauto.
    Qed.

    Lemma tau_steps_steps
          rels1 rels2 e1 e2
          (STEPS: tau_steps rels1 rels2 e1 e2):
      steps rels1 rels2 e1 e2.
    Proof.
      induction STEPS; eauto.
    Qed.

    Lemma steps_app
          rels1 rels2 rels3 e1 e2 e3
          (STEPS1: steps rels1 rels2 e1 e2)
          (STEPS2: steps rels2 rels3 e2 e3):
      steps rels1 rels3 e1 e3.
    Proof.
      revert rels3 e3 STEPS2.
      induction STEPS1; i; eauto.
    Qed.

    Lemma tau_steps_app
          rels1 rels2 rels3 e1 e2 e3
          (STEPS1: tau_steps rels1 rels2 e1 e2)
          (STEPS2: tau_steps rels2 rels3 e2 e3):
      tau_steps rels1 rels3 e1 e3.
    Proof.
      revert rels3 e3 STEPS2.
      induction STEPS1; i; eauto.
    Qed.

    Lemma tau_steps_rtc_tau_step
          rels1 rels2 e1 e2
          (STEPS: tau_steps rels1 rels2 e1 e2):
      rtc (@OrdThread.tau_step lang L Ordering.acqrel) e1 e2.
    Proof.
      induction STEPS; eauto.
      econs 2; eauto. inv STEP; ss.
      econs; eauto. econs. eauto.
    Qed.

    Lemma plus_step_steps
          rels1 rels2 e1 pf e e2 e3
          (STEPS: steps rels1 rels2 e1 e2)
          (STEP: OrdThread.step L Ordering.acqrel pf e e2 e3):
      steps rels1 (ReleaseWrites.append L e rels2) e1 e3.
    Proof.
      induction STEPS; eauto.
      econs; eauto. econs; eauto.
    Qed.

    Lemma step_future
          rels1 rels2 e e1 e2
          (STEP: step rels1 rels2 e e1 e2)
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
      inv STEP; eauto using OrdThread.step_future.
    Qed.

    Lemma steps_future
          rels1 rels2 e1 e2
          (STEPS: steps rels1 rels2 e1 e2)
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
      - splits; ss; refl.
      - exploit step_future; eauto. i. des.
        exploit IHSTEPS; eauto. i. des.
        splits; ss; etrans; eauto.
    Qed.

    Lemma step_disjoint
          rels1 rels2 e e1 e2 lc
          (STEP: step rels1 rels2 e e1 e2)
          (WF1: Local.wf e1.(Thread.local) e1.(Thread.memory))
          (SC1: Memory.closed_timemap e1.(Thread.sc) e1.(Thread.memory))
          (CLOSED1: Memory.closed e1.(Thread.memory))
          (DISJOINT1: Local.disjoint e1.(Thread.local) lc)
          (WF: Local.wf lc e1.(Thread.memory)):
      <<DISJOINT2: Local.disjoint e2.(Thread.local) lc>> /\
      <<WF: Local.wf lc e2.(Thread.memory)>>.
    Proof.
      inv STEP; eauto using OrdThread.step_disjoint.
    Qed.

    (* ReleaseWrites.wf *)

    Lemma promise_rels_wf
          rels promises1 mem1 loc from to msg promises2 mem2 kind
          (RELS1: ReleaseWrites.wf rels promises1 mem1)
          (PROMISE: Memory.promise promises1 mem1 loc from to msg promises2 mem2 kind):
      ReleaseWrites.wf rels promises2 mem2.
    Proof.
      ii. exploit RELS1; eauto. i. des. inv PROMISE; ss.
      - exploit Memory.add_get1; try exact x0; eauto. i. esplits; eauto.
        erewrite Memory.add_o; eauto. condtac; ss. des. subst.
        exploit Memory.add_get0; try exact MEM. i. des. congr.
      - exploit Memory.split_get1; try exact x0; eauto. i. des. subst. esplits; eauto.
        erewrite Memory.split_o; eauto. repeat condtac; ss.
        + des. subst. exploit Memory.split_get0; try exact MEM. i. des. congr.
        + guardH o. des. subst.
          exploit Memory.split_get0; try exact PROMISES. i. des. congr.
      - exploit Memory.lower_get1; try exact x0; eauto. i. des. subst. inv MSG_LE.
        esplits; eauto.
        erewrite Memory.lower_o; eauto. condtac; ss. des. subst.
        exploit Memory.lower_get0; try exact PROMISES. i. des. congr.
      - erewrite (@Memory.remove_o promises2); eauto.
        erewrite (@Memory.remove_o mem2); eauto. condtac; ss; eauto.
        des. subst. exploit Memory.remove_get0; try exact PROMISES. i. des. congr.
    Qed.

    Lemma step_rels_wf
          rels1 rels2 e e1 e2
          (RELS1: ReleaseWrites.wf rels1 e1.(Thread.local).(Local.promises) e1.(Thread.memory))
          (STEP: step rels1 rels2 e e1 e2):
      ReleaseWrites.wf rels2 e2.(Thread.local).(Local.promises) e2.(Thread.memory).
    Proof.
      inv STEP; cycle 1.
      { unfold ReleaseWrites.append.
        inv STEP0; inv STEP; inv LOCAL; ss.
        - inv LOCAL0. inv STEP. ss.
        - inv LOCAL1. inv STEP. inv LOCAL2. inv STEP. inv WRITE. ss.
          hexploit promise_rels_wf; eauto. i.
          cut (ReleaseWrites.wf rels1 promises2 mem2).
          { i. repeat condtac; ss. ii. inv IN; eauto. inv H1.
            exploit Memory.promise_get0; eauto; try by (inv PROMISE; ss). i. des.
            exploit Memory.remove_get0; eauto. i. des.
            esplits; eauto. }
          ii. exploit H; eauto. i. des. esplits; eauto.
          erewrite Memory.remove_o; eauto. condtac; ss.
      }
      unfold ReleaseWrites.append.
      inv STEP0; inv STEP; inv LOCAL; ss.
      - eauto using promise_rels_wf.
      - inv LOCAL0. inv STEP. ss.
      - inv LOCAL0. inv STEP. inv WRITE. ss.
        hexploit promise_rels_wf; eauto. i.
        cut (ReleaseWrites.wf rels1 promises2 mem2).
        { i. repeat condtac; ss. ii. inv IN; eauto. inv H1.
          exploit Memory.promise_get0; eauto; try by (inv PROMISE; ss). i. des.
          exploit Memory.remove_get0; eauto. i. des.
          esplits; eauto. }
        ii. exploit H; eauto. i. des. esplits; eauto.
        erewrite Memory.remove_o; eauto. condtac; ss.
      - inv LOCAL1. inv STEP. inv LOCAL2. inv STEP. inv WRITE. ss.
        hexploit promise_rels_wf; eauto. i.
        cut (ReleaseWrites.wf rels1 promises2 mem2).
        { i. repeat condtac; ss. ii. inv IN; eauto. inv H1.
          exploit Memory.promise_get0; eauto; try by (inv PROMISE; ss). i. des.
          exploit Memory.remove_get0; eauto. i. des.
          esplits; eauto. }
        ii. exploit H; eauto. i. des. esplits; eauto.
        erewrite Memory.remove_o; eauto. condtac; ss.
      - inv LOCAL0. ss.
      - inv LOCAL0. ss.
    Qed.

    Lemma steps_rels_wf
          rels1 rels2 e1 e2
          (RELS1: ReleaseWrites.wf rels1 e1.(Thread.local).(Local.promises) e1.(Thread.memory))
          (STEPS: steps rels1 rels2 e1 e2):
      ReleaseWrites.wf rels2 e2.(Thread.local).(Local.promises) e2.(Thread.memory).
    Proof.
      induction STEPS; eauto.
      apply IHSTEPS. eapply step_rels_wf; eauto.
    Qed.

    Lemma promise_rels_disjoint
          promises1 mem1 loc from to msg promises2 mem2 kind
          promises
          (PROMISE: Memory.promise promises1 mem1 loc from to msg promises2 mem2 kind)
          (DISJOINT: Memory.disjoint promises1 promises)
          (LE: Memory.le promises mem1):
      Memory.get loc to promises = None.
    Proof.
      destruct (Memory.get loc to promises) as [[]|] eqn:GETP; ss.
      exploit LE; eauto. i.
      inv PROMISE; ss.
      - exploit Memory.add_get0; try exact MEM. i. des. congr.
      - exploit Memory.split_get0; try exact MEM. i. des. congr.
      - exploit Memory.lower_get0; try exact PROMISES. i. des.
        inv DISJOINT. exploit DISJOINT0; eauto. i. des. exfalso.
        exploit Memory.get_ts; try exact GETP. i. des; try congr.
        exploit Memory.get_ts; try exact GET. i. des; try congr.
        apply (x0 to); econs; try refl; ss.
      - exploit Memory.remove_get0; try exact PROMISES. i. des.
        inv DISJOINT. exploit DISJOINT0; eauto. i. des. exfalso.
        exploit Memory.get_ts; try exact GETP. i. des; try congr.
        exploit Memory.get_ts; try exact GET. i. des; try congr.
        apply (x0 to); econs; try refl; ss.
    Qed.

    Lemma step_rels_disjoint
          rels1 rels2 e e1 e2 promises
          (RELS1: ReleaseWrites.wf rels1 e1.(Thread.local).(Local.promises) e1.(Thread.memory))
          (STEP: step rels1 rels2 e e1 e2)
          (DISJOINT: Memory.disjoint e1.(Thread.local).(Local.promises) promises)
          (LE: Memory.le promises e1.(Thread.memory))
          (RELS: ReleaseWrites.wf rels1 promises e1.(Thread.memory)):
      ReleaseWrites.wf rels2 promises e2.(Thread.memory).
    Proof.
      hexploit step_rels_wf; eauto. ii.
      exploit H; eauto. i. des. esplits; eauto.
      inv STEP; cycle 1.
      { unfold ReleaseWrites.append in *.
        inv STEP0; inv STEP; inv LOCAL; ss.
        - inv LOCAL0. exploit RELS; eauto. i. des. ss.
        - inv LOCAL1. inv STEP. inv LOCAL2. inv STEP. inv WRITE. ss.
          revert IN. repeat condtac; ss; i; des; try by (exploit RELS; eauto; i; des; ss).
          inv IN. eapply promise_rels_disjoint; eauto.
      }
      unfold ReleaseWrites.append in *.
      inv STEP0; inv STEP; inv LOCAL; ss.
      - exploit RELS; eauto. i. des. ss.
      - exploit RELS; eauto. i. des. ss.
      - exploit RELS; eauto. i. des. ss.
      - inv LOCAL0. inv STEP. inv WRITE. ss. revert IN.
        repeat condtac; ss; i; des; try by (exploit RELS; eauto; i; des; ss).
        inv IN. eapply promise_rels_disjoint; eauto.
      - inv LOCAL1. inv STEP. inv LOCAL2. inv STEP. inv WRITE. ss. revert IN.
        repeat condtac; ss; i; des; try by (exploit RELS; eauto; i; des; ss).
        inv IN. eapply promise_rels_disjoint; eauto.
      - exploit RELS; eauto. i. des. ss.
      - exploit RELS; eauto. i. des. ss.
      - exploit RELS; eauto. i. des. ss.
    Qed.

    Lemma steps_rels_disjoint
          rels1 rels2 e1 e2 lc
          (RELS1: ReleaseWrites.wf rels1 e1.(Thread.local).(Local.promises) e1.(Thread.memory))
          (STEPS: steps rels1 rels2 e1 e2)
          (WF1: Local.wf e1.(Thread.local) e1.(Thread.memory))
          (SC1: Memory.closed_timemap e1.(Thread.sc) e1.(Thread.memory))
          (CLOSED1: Memory.closed e1.(Thread.memory))
          (DISJOINT: Local.disjoint e1.(Thread.local) lc)
          (WF: Local.wf lc e1.(Thread.memory))
          (RELS: ReleaseWrites.wf rels1 lc.(Local.promises) e1.(Thread.memory)):
      ReleaseWrites.wf rels2 lc.(Local.promises) e2.(Thread.memory).
    Proof.
      induction STEPS; ss.
      hexploit step_rels_disjoint; eauto; try apply DISJOINT; try apply WF. i.
      hexploit step_rels_wf; eauto. i.
      inv STEP.
      - exploit OrdThread.step_future; eauto. i. des.
        exploit OrdThread.step_disjoint; eauto. i. des.
        eapply IHSTEPS; eauto.
      - exploit OrdThread.step_future; eauto. i. des.
        exploit OrdThread.step_disjoint; eauto. i. des.
        eapply IHSTEPS; eauto.
    Qed.
  End RAThread.
End RAThread.


Module RAConfiguration.
  Section RAConfiguration.
    Variable L: Loc.t -> bool.

    Inductive step:
      forall (e: MachineEvent.t) (tid: Ident.t) (rels1 rels2: ReleaseWrites.t) (c1 c2: Configuration.t), Prop :=
    | step_intro
        rels1 rels2 rels3
        e tid c1 lang st1 lc1 e2 st3 lc3 sc3 memory3
        (TID: IdentMap.find tid c1.(Configuration.threads) = Some (existT _ lang st1, lc1))
        (STEPS: RAThread.tau_steps lang L rels1 rels2
                                   (Thread.mk _ st1 lc1 c1.(Configuration.sc) c1.(Configuration.memory)) e2)
        (STEP: RAThread.step lang L rels2 rels3 e e2 (Thread.mk _ st3 lc3 sc3 memory3))
        (CONSISTENT: e <> ThreadEvent.failure ->
                     RAThread.consistent lang L rels3 (Thread.mk _ st3 lc3 sc3 memory3)):
        step (ThreadEvent.get_machine_event e) tid rels1 rels3
             c1 (Configuration.mk (IdentMap.add tid (existT _ _ st3, lc3) c1.(Configuration.threads)) sc3 memory3)
    .

    Inductive steps rels1: forall (rels2: ReleaseWrites.t) (c1 c2: Configuration.t), Prop :=
    | steps_refl
        c:
        steps rels1 rels1 c c
    | steps_step
        rels2 rels3 e tid c1 c2 c3
        (STEP: step e tid rels1 rels2 c1 c2)
        (STEPS: steps rels2 rels3 c2 c3):
        steps rels1 rels3 c1 c3
    .
    Hint Constructors steps.

    Lemma step_future
          e tid rels1 rels2 c1 c2
          (WF1: Configuration.wf c1)
          (STEP: step e tid rels1 rels2 c1 c2):
      <<WF2: Configuration.wf c2>>.
    Proof.
      inv WF1. inv WF. inv STEP; s.
      exploit THREADS; eauto. i.
      exploit OrdThread.rtc_tau_step_future;
        try eapply RAThread.tau_steps_ord_tau_steps; try exact STEPS; eauto.
      s. i. des.
      exploit RAThread.step_future; try exact STEP0; eauto. s. i. des.
      econs; ss. econs.
      - i. Configuration.simplify.
        + exploit THREADS; try apply TH1; eauto. i.
          exploit OrdThread.rtc_tau_step_disjoint;
            try eapply RAThread.tau_steps_ord_tau_steps; try exact STEPS; eauto. i. des.
          exploit RAThread.step_disjoint; try exact STEP0; eauto. s. i. des. symmetry. ss.
        + exploit THREADS; try apply TH2; eauto. i.
          exploit OrdThread.rtc_tau_step_disjoint;
            try eapply RAThread.tau_steps_ord_tau_steps; try exact STEPS; eauto. i. des.
          exploit RAThread.step_disjoint; try exact STEP0; eauto. s. i. des. ss.
        + eapply DISJOINT; cycle 1; eauto.
      - i. Configuration.simplify.
        exploit THREADS; try apply TH; eauto. i.
        exploit OrdThread.rtc_tau_step_disjoint;
          try eapply RAThread.tau_steps_ord_tau_steps; try exact STEPS; eauto. i. des.
        exploit RAThread.step_disjoint; try exact STEP0; eauto. s. i. des. ss.
    Qed.
  End RAConfiguration.
End RAConfiguration.


Module RARace.
  Section RARace.
    Variable L: Loc.t -> bool.

    Definition racefree (rels: ReleaseWrites.t) (c: Configuration.t): Prop :=
      forall e tid rels2 rels3 c2 c3
        (STEPS: RAConfiguration.steps L rels rels2 c c2)
        (STEP: RAConfiguration.step L e tid rels2 rels3 c2 c3),
        False.

    Definition racefree_syn (syn: Threads.syntax): Prop :=
      racefree [] (Configuration.init syn).
  End RARace.
End RARace.
