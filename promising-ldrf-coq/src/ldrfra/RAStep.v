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
Require Import MemoryFacts.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.

Require Import Mapping.

Require Import PFStep.
Require Import OrdStep.

Set Implicit Arguments.


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
  End ReleaseWrites.
End ReleaseWrites.


Module RAThread.
  Section RAThread.
    Variable lang: language.
    Variable L: Loc.t -> bool.

    Inductive step rels1: forall (rels2: ReleaseWrites.t) (e: ThreadEvent.t) (e1 e2: Thread.t lang), Prop :=
    | step_intro
        pf e e1 e2
        (STEP: @OrdThread.step lang L Ordering.acqrel pf e e1 e2):
        step rels1 (ReleaseWrites.append L e rels1) e e1 e2
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

    Inductive opt_step rels1: forall (rels2: ReleaseWrites.t) (e: ThreadEvent.t) (e1 e2: Thread.t lang), Prop :=
    | step_none
        e:
        opt_step rels1 rels1 ThreadEvent.silent e e
    | step_some
        rels2 e e1 e2
        (STEP: step rels1 rels2 e e1 e2):
        opt_step rels1 rels2 e e1 e2
    .
    Hint Constructors opt_step.


    Lemma step_ord_step
          rels1 rels2 e e1 e2
          (STEP: step rels1 rels2 e e1 e2):
      exists pf, OrdThread.step L Ordering.acqrel pf e e1 e2.
    Proof.
      inv STEP. eauto.
    Qed.

    Lemma steps_ord_steps
          rels1 rels2 e1 e2
          (STEPS: steps rels1 rels2 e1 e2):
      rtc (OrdThread.all_step L Ordering.acqrel) e1 e2.
    Proof.
      induction STEPS; eauto.
      exploit step_ord_step; eauto. i. des.
      econs 2; eauto. econs. econs. eauto.
    Qed.

    Lemma tau_steps_ord_tau_steps
          rels1 rels2 e1 e2
          (STEPS: tau_steps rels1 rels2 e1 e2):
      rtc (@OrdThread.tau_step lang L Ordering.acqrel) e1 e2.
    Proof.
      induction STEPS; eauto.
      inv STEP; ss.
      econs 2; eauto. econs; eauto. econs. eauto.
    Qed.

    Lemma ord_tau_steps_tau_steps
          e1 e2
          (STEPS: rtc (@OrdThread.tau_step lang L Ordering.acqrel) e1 e2):
      forall rels1, exists rels2,
          tau_steps rels1 rels2 e1 e2.
    Proof.
      induction STEPS; eauto. inv H. inv TSTEP. i.
      specialize (IHSTEPS (ReleaseWrites.append L e rels1)). des.
      esplits. econs 2; eauto. econs; eauto.
    Qed.

    Lemma tau_steps_steps
          rels1 rels2 e1 e2
          (STEPS: tau_steps rels1 rels2 e1 e2):
      steps rels1 rels2 e1 e2.
    Proof.
      induction STEPS; eauto.
    Qed.

    Lemma reserve_steps_tau_steps
          rels e1 e2
          (STEPS: rtc (@Thread.reserve_step _) e1 e2):
      tau_steps rels rels e1 e2.
    Proof.
      induction STEPS; eauto.
      inv H. inv STEP; [|inv STEP0; inv LOCAL].
      econs 2; eauto.
      - replace rels with
            (ReleaseWrites.append
               L (ThreadEvent.promise loc from to Message.reserve Memory.op_kind_add) rels)
            at 2 by ss.
        econs. econs 1; eauto.
        ii. inv PROMISE.
      - ss.
    Qed.

    Lemma cancel_steps_tau_steps
          rels e1 e2
          (STEPS: rtc (@Thread.cancel_step _) e1 e2):
      tau_steps rels rels e1 e2.
    Proof.
      induction STEPS; eauto.
      inv H. inv STEP; [|inv STEP0; inv LOCAL].
      econs 2; eauto.
      - replace rels with
            (ReleaseWrites.append
               L (ThreadEvent.promise loc from to Message.reserve Memory.op_kind_cancel) rels)
            at 2 by ss.
        econs. econs 1; eauto.
        ii. inv PROMISE; ss.
      - ss.
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

    Lemma opt_step_steps
          rels1 rels2 e e1 e2
          (STEP: opt_step rels1 rels2 e e1 e2):
      steps rels1 rels2 e1 e2.
    Proof.
      inv STEP; eauto.
    Qed.

    Lemma steps_trans
          rels1 rels2 rels3 e1 e2 e3
          (STEPS1: steps rels1 rels2 e1 e2)
          (STEPS2: steps rels2 rels3 e2 e3):
      steps rels1 rels3 e1 e3.
    Proof.
      revert rels3 e3 STEPS2.
      induction STEPS1; i; eauto.
    Qed.

    Lemma tau_steps_trans
          rels1 rels2 rels3 e1 e2 e3
          (STEPS1: tau_steps rels1 rels2 e1 e2)
          (STEPS2: tau_steps rels2 rels3 e2 e3):
      tau_steps rels1 rels3 e1 e3.
    Proof.
      revert rels3 e3 STEPS2.
      induction STEPS1; i; eauto.
    Qed.

    Lemma step_future
          rels1 rels2 e e1 e2
          (STEP: step rels1 rels2 e e1 e2)
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
      inv STEP; eauto using OrdThread.step_future.
    Qed.

    Lemma opt_step_future
          rels1 rels2 e e1 e2
          (STEP: opt_step rels1 rels2 e e1 e2)
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
      - esplits; eauto; refl.
      - inv STEP0; eauto using OrdThread.step_future.
    Qed.

    Lemma steps_future
          rels1 rels2 e1 e2
          (STEPS: steps rels1 rels2 e1 e2)
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
      - splits; ss; refl.
      - exploit step_future; eauto. i. des.
        exploit IHSTEPS; eauto. i. des.
        splits; ss; etrans; eauto.
    Qed.

    Lemma step_disjoint
          rels1 rels2 e e1 e2 lc
          (STEP: step rels1 rels2 e e1 e2)
          (WF1: Local.wf (Thread.local e1) (Thread.memory e1))
          (SC1: Memory.closed_timemap (Thread.sc e1) (Thread.memory e1))
          (CLOSED1: Memory.closed (Thread.memory e1))
          (DISJOINT1: Local.disjoint (Thread.local e1) lc)
          (WF: Local.wf lc (Thread.memory e1)):
      <<DISJOINT2: Local.disjoint (Thread.local e2) lc>> /\
      <<WF: Local.wf lc (Thread.memory e2)>>.
    Proof.
      inv STEP; eauto using OrdThread.step_disjoint.
    Qed.

    Lemma opt_step_disjoint
          rels1 rels2 e e1 e2 lc
          (STEP: opt_step rels1 rels2 e e1 e2)
          (WF1: Local.wf (Thread.local e1) (Thread.memory e1))
          (SC1: Memory.closed_timemap (Thread.sc e1) (Thread.memory e1))
          (CLOSED1: Memory.closed (Thread.memory e1))
          (DISJOINT1: Local.disjoint (Thread.local e1) lc)
          (WF: Local.wf lc (Thread.memory e1)):
      <<DISJOINT2: Local.disjoint (Thread.local e2) lc>> /\
      <<WF: Local.wf lc (Thread.memory e2)>>.
    Proof.
      inv STEP; eauto.
      inv STEP0; eauto using OrdThread.step_disjoint.
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
          (RELS1: ReleaseWrites.wf rels1 (Local.promises (Thread.local e1)) (Thread.memory e1))
          (STEP: step rels1 rels2 e e1 e2):
      ReleaseWrites.wf rels2 (Local.promises (Thread.local e2)) (Thread.memory e2).
    Proof.
      inv STEP. unfold ReleaseWrites.append.
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
          (RELS1: ReleaseWrites.wf rels1 (Local.promises (Thread.local e1)) (Thread.memory e1))
          (STEPS: steps rels1 rels2 e1 e2):
      ReleaseWrites.wf rels2 (Local.promises (Thread.local e2)) (Thread.memory e2).
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
          (RELS1: ReleaseWrites.wf rels1 (Local.promises (Thread.local e1)) (Thread.memory e1))
          (STEP: step rels1 rels2 e e1 e2)
          (DISJOINT: Memory.disjoint (Local.promises (Thread.local e1)) promises)
          (LE: Memory.le promises (Thread.memory e1))
          (RELS: ReleaseWrites.wf rels1 promises (Thread.memory e1)):
      ReleaseWrites.wf rels2 promises (Thread.memory e2).
    Proof.
      hexploit step_rels_wf; eauto. ii.
      exploit H; eauto. i. des. esplits; eauto.
      inv STEP. unfold ReleaseWrites.append in *.
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
          (RELS1: ReleaseWrites.wf rels1 (Local.promises (Thread.local e1)) (Thread.memory e1))
          (STEPS: steps rels1 rels2 e1 e2)
          (WF1: Local.wf (Thread.local e1) (Thread.memory e1))
          (SC1: Memory.closed_timemap (Thread.sc e1) (Thread.memory e1))
          (CLOSED1: Memory.closed (Thread.memory e1))
          (DISJOINT: Local.disjoint (Thread.local e1) lc)
          (WF: Local.wf lc (Thread.memory e1))
          (RELS: ReleaseWrites.wf rels1 (Local.promises lc) (Thread.memory e1)):
      ReleaseWrites.wf rels2 (Local.promises lc) (Thread.memory e2).
    Proof.
      induction STEPS; ss.
      hexploit step_rels_disjoint; eauto; try apply DISJOINT; try apply WF. i.
      hexploit step_rels_wf; eauto. i.
      inv STEP.
      exploit OrdThread.step_future; eauto. i. des.
      exploit OrdThread.step_disjoint; eauto. i. des.
      eapply IHSTEPS; eauto.
    Qed.


    Lemma cap_tau_steps_current_tau_steps
          rels0 rels1 e0 e1 fe0
          (THREAD: thread_map ident_map e0 fe0)
          (STEPS: tau_steps rels0 rels1 e0 e1)
          (LOCAL: Local.wf (Thread.local e0) (Thread.memory e0))
          (FLOCAL: Local.wf (Thread.local fe0) (Thread.memory fe0))
          (MEMORY: Memory.closed (Thread.memory e0))
          (FMEMORY: Memory.closed (Thread.memory fe0))
          (SC: Memory.closed_timemap (Thread.sc e0) (Thread.memory e0))
          (FSC: Memory.closed_timemap (Thread.sc fe0) (Thread.memory fe0)):
        exists fe1,
          (<<THREAD: thread_map ident_map e1 fe1>>) /\
          (<<STEPS: tau_steps rels0 rels1 fe0 fe1>>).
    Proof.
      ginduction STEPS; eauto. i.
      inv STEP; ss.
      exploit OrdThread.cap_step_current_step; eauto. i. des.
      exploit OrdThread.step_future; try apply STEP; eauto. i. des.
      exploit OrdThread.step_future; try apply STEP0; eauto. i. des.
      exploit IHSTEPS; eauto. i. des. exists fe2. splits; eauto.
      replace (ReleaseWrites.append L e rels1) with (ReleaseWrites.append L fe rels1) in STEPS0; cycle 1.
      { unfold ReleaseWrites.append. destruct e; inv EVENT; ss.
        - inv FROM. inv TO. refl.
        - inv FROM. inv TO. refl. }
      econs; [econs 1; eauto|..]; eauto.
      destruct e; inv EVENT; ss.
    Qed.

    Lemma cap_plus_step_current_plus_step
          rels1 rels2 rels3 e e1 e2 e3 sc1 mem1
          (LOCAL: Local.wf (Thread.local e1) (Thread.memory e1))
          (MEMORY: Memory.closed (Thread.memory e1))
          (SC: Memory.closed_timemap (Thread.sc e1) (Thread.memory e1))
          (CAP: Memory.cap (Thread.memory e1) mem1)
          (SC_MAX: Memory.max_concrete_timemap mem1 sc1)
          (STEPS: tau_steps rels1 rels2 (Thread.mk lang (Thread.state e1) (Thread.local e1) sc1 mem1) e2)
          (STEP: RAThread.step rels2 rels3 e e2 e3):
        exists rels3' e' e2' e3',
          (<<STEPS: tau_steps rels1 rels2 e1 e2'>>) /\
          (<<STEP: RAThread.step rels2 rels3' e' e2' e3'>>) /\
          (<<LOCAL: local_map ident_map (Thread.local e2) (Thread.local e2')>>) /\
          (<<EVENT: tevent_map ident_map e' e>>).
    Proof.
      exploit cap_tau_steps_current_tau_steps; try apply STEPS; eauto; ss.
      { destruct e1. ss. econs; eauto.
        { eapply ident_map_local. }
        { econs.
          { i. eapply Memory.cap_inv in GET; eauto. des; auto.
            right. exists to, from, msg, msg; splits; ss.
            { eapply ident_map_message. }
            { refl. }
          }
          { i. eapply CAP in GET. left. esplits; ss.
            { refl. }
            { refl. }
            { i. econs; eauto. }
          }
        }
        { eapply mapping_map_lt_collapsable_unwritable. eapply ident_map_lt. }
        { eapply ident_map_timemap. }
        { eapply Memory.max_concrete_timemap_spec; eauto.
          eapply Memory.cap_closed_timemap; eauto. }
      }
      { eapply Local.cap_wf; eauto. }
      { eapply Memory.cap_closed; eauto. }
      { eapply Memory.max_concrete_timemap_closed; eauto. }
      i. des.
      exploit steps_future; try eapply tau_steps_steps; try apply STEPS; ss.
      { eapply Local.cap_wf; eauto. }
      { eapply Memory.max_concrete_timemap_closed; eauto. }
      { eapply Memory.cap_closed; eauto. }
      i. des.
      exploit steps_future; try eapply tau_steps_steps; try apply STEPS0; ss. i. des.
      inv STEP.
      exploit OrdThread.cap_step_current_step; eauto. i. des.
      esplits; eauto.
      - econs; eauto.
      - inv THREAD. ss.
    Qed.


    (* promises get *)

    Lemma promise_get_None
          promises1 mem1 loc' from' to' msg' promises2 mem2 kind
          loc from to msg
          (PROMISE: Memory.promise promises1 mem1 loc' from' to' msg' promises2 mem2 kind)
          (PROMISES1: Memory.get loc to promises1 = None)
          (MEM1: Memory.get loc to mem1 = Some (from, msg)):
      (<<PROMISES2: Memory.get loc to promises2 = None>>) /\
      (<<MEM2: Memory.get loc to mem2 = Some (from, msg)>>) /\
      (<<LOCTS: __guard__ (loc' <> loc \/ to' <> to)>>).
    Proof.
      unguard. inv PROMISE.
      - exploit Memory.add_get0; try exact PROMISES. i. des.
        exploit Memory.add_get0; try exact MEM. i. des.
        erewrite Memory.add_o; eauto.
        erewrite (@Memory.add_o mem2); eauto.
        condtac; ss.
        + des. subst. congr.
        + splits; ss. des; eauto.
      - exploit Memory.split_get0; try exact PROMISES. i. des.
        exploit Memory.split_get0; try exact MEM. i. des.
        erewrite Memory.split_o; eauto.
        erewrite (@Memory.split_o mem2); eauto.
        repeat condtac; ss.
        + des. subst. congr.
        + des; subst; congr.
        + splits; ss. des; eauto.
      - exploit Memory.lower_get0; try exact PROMISES. i. des.
        exploit Memory.lower_get0; try exact MEM. i. des.
        erewrite Memory.lower_o; eauto.
        erewrite (@Memory.lower_o mem2); eauto.
        condtac; ss.
        + des. subst. congr.
        + splits; ss. des; eauto.
      - exploit Memory.remove_get0; try exact PROMISES. i. des.
        exploit Memory.remove_get0; try exact MEM. i. des.
        erewrite Memory.remove_o; eauto.
        erewrite (@Memory.remove_o mem2); eauto.
        condtac; ss.
        + des. subst. congr.
        + splits; ss. des; eauto.
    Qed.

    Lemma write_get_None
          promises1 mem1 loc' from' to' val released promises2 mem2 kind
          loc from to msg
          (WRITE: Memory.write promises1 mem1 loc' from' to' val released promises2 mem2 kind)
          (PROMISES1: Memory.get loc to promises1 = None)
          (MEM1: Memory.get loc to mem1 = Some (from, msg)):
      (<<PROMISES2: Memory.get loc to promises2 = None>>) /\
      (<<MEM2: Memory.get loc to mem2 = Some (from, msg)>>) /\
      (<<LOCTS: __guard__ (loc' <> loc \/ to' <> to)>>).
    Proof.
      inv WRITE.
      exploit promise_get_None; eauto. i. des. split; ss.
      erewrite Memory.remove_o; eauto. condtac; ss.
    Qed.

    Lemma step_get_None
          e rels1 rels2 e1 e2
          loc from to msg
          (STEP: step rels1 rels2 e e1 e2)
          (PROMISES1: Memory.get loc to (Local.promises (Thread.local e1)) = None)
          (MEM1: Memory.get loc to (Thread.memory e1) = Some (from, msg)):
      (<<PROMISES2: Memory.get loc to (Local.promises (Thread.local e2)) = None>>) /\
      (<<MEM2: Memory.get loc to (Thread.memory e2) = Some (from, msg)>>) /\
      (<<EVENT: forall from' val released ord, ThreadEvent.is_writing e <> Some (loc, from', to, val, released, ord)>>).
    Proof.
      inv STEP. inv STEP0; inv STEP; inv LOCAL; ss.
      - exploit promise_get_None; eauto. i. des. splits; ss.
      - inv LOCAL0. inv STEP. ss.
      - inv LOCAL0. inv STEP.
        exploit write_get_None; eauto. i. des. splits; ss.
        ii. inv H. unguard. des; ss.
      - inv LOCAL1. inv STEP. inv LOCAL2. inv STEP.
        exploit write_get_None; eauto. i. des. splits; ss.
        ii. inv H. unguard. des; ss.
      - inv LOCAL0. ss.
      - inv LOCAL0. ss.
    Qed.

    Lemma opt_step_get_None
          e rels1 rels2 e1 e2
          loc from to msg
          (STEP: opt_step rels1 rels2 e e1 e2)
          (PROMISES1: Memory.get loc to (Local.promises (Thread.local e1)) = None)
          (MEM1: Memory.get loc to (Thread.memory e1) = Some (from, msg)):
      (<<PROMISES2: Memory.get loc to (Local.promises (Thread.local e2)) = None>>) /\
      (<<MEM2: Memory.get loc to (Thread.memory e2) = Some (from, msg)>>) /\
      (<<EVENT: forall from' val released ord, ThreadEvent.is_writing e <> Some (loc, from', to, val, released, ord)>>).
    Proof.
      inv STEP.
      - splits; eauto. ss.
      - exploit step_get_None; eauto.
    Qed.

    Lemma reserve_step_get_None
          e1 e2
          loc from to msg
          (STEP: @Thread.reserve_step lang e1 e2)
          (PROMISES1: Memory.get loc to (Local.promises (Thread.local e1)) = None)
          (MEM1: Memory.get loc to (Thread.memory e1) = Some (from, msg)):
      (<<PROMISES2: Memory.get loc to (Local.promises (Thread.local e2)) = None>>) /\
      (<<MEM2: Memory.get loc to (Thread.memory e2) = Some (from, msg)>>).
    Proof.
      inv STEP. inv STEP0; inv STEP; inv LOCAL; ss.
      exploit promise_get_None; eauto. i. des. ss.
    Qed.

    Lemma cancel_step_get_None
          e1 e2
          loc from to msg
          (STEP: @Thread.cancel_step lang e1 e2)
          (PROMISES1: Memory.get loc to (Local.promises (Thread.local e1)) = None)
          (MEM1: Memory.get loc to (Thread.memory e1) = Some (from, msg)):
      (<<PROMISES2: Memory.get loc to (Local.promises (Thread.local e2)) = None>>) /\
      (<<MEM2: Memory.get loc to (Thread.memory e2) = Some (from, msg)>>).
    Proof.
      inv STEP. inv STEP0; inv STEP; inv LOCAL; ss.
      exploit promise_get_None; eauto. i. des. ss.
    Qed.

    Lemma reserve_steps_get_None
          e1 e2
          loc from to msg
          (STEP: rtc (@Thread.reserve_step lang) e1 e2)
          (PROMISES1: Memory.get loc to (Local.promises (Thread.local e1)) = None)
          (MEM1: Memory.get loc to (Thread.memory e1) = Some (from, msg)):
      (<<PROMISES2: Memory.get loc to (Local.promises (Thread.local e2)) = None>>) /\
      (<<MEM2: Memory.get loc to (Thread.memory e2) = Some (from, msg)>>).
    Proof.
      induction STEP; ss.
      exploit reserve_step_get_None; eauto. i. des. eauto.
    Qed.

    Lemma cancel_steps_get_None
          e1 e2
          loc from to msg
          (STEP: rtc (@Thread.cancel_step lang) e1 e2)
          (PROMISES1: Memory.get loc to (Local.promises (Thread.local e1)) = None)
          (MEM1: Memory.get loc to (Thread.memory e1) = Some (from, msg)):
      (<<PROMISES2: Memory.get loc to (Local.promises (Thread.local e2)) = None>>) /\
      (<<MEM2: Memory.get loc to (Thread.memory e2) = Some (from, msg)>>).
    Proof.
      induction STEP; ss.
      exploit cancel_step_get_None; eauto. i. des. eauto.
    Qed.


    (* reserve_only *)

    Definition reserve_only (promises: Memory.t): Prop :=
      forall loc from to msg
        (LOC: L loc)
        (GET: Memory.get loc to promises = Some (from, msg)),
        msg = Message.reserve.

    Lemma step_reserve_only
          rels1 rels2 e e1 e2
          (PROMISES1: reserve_only (Local.promises (Thread.local e1)))
          (STEP: step rels1 rels2 e e1 e2):
      <<PROMISES2: reserve_only (Local.promises (Thread.local e2))>>.
    Proof.
      inv STEP. inv STEP0; inv STEP; inv LOCAL; ss; try by (inv LOCAL0; ss).
      - destruct (L loc) eqn:LOC.
        + ii. destruct msg.
          { exploit PF; ss. }
          revert GET. inv PROMISE; ss.
          * erewrite Memory.add_o; eauto. condtac; ss; eauto.
            i. des. subst. inv GET. ss.
          * erewrite Memory.split_o; eauto. repeat (condtac; ss; eauto).
            { i. des. subst. inv GET. ss. }
            { guardH o. i. des. subst. inv GET. ss. }
          * erewrite Memory.lower_o; eauto. condtac; ss; eauto.
            i. des. subst. inv GET. ss.
          * erewrite Memory.remove_o; eauto. condtac; ss; eauto.
        + ii. revert GET. inv PROMISE; ss.
          * erewrite Memory.add_o; eauto. condtac; ss; eauto.
            i. des. subst. congr.
          * erewrite Memory.split_o; eauto. repeat (condtac; ss; eauto).
            { i. des. subst. congr. }
            { guardH o. i. des. subst. congr. }
          * erewrite Memory.lower_o; eauto. condtac; ss; eauto.
            i. des. subst. congr.
          * erewrite Memory.remove_o; eauto. condtac; ss; eauto.
      - inv LOCAL0. inv STEP. ss.
      - inv LOCAL0. inv STEP. inv WRITE. ss.
        ii. revert GET. erewrite Memory.remove_o; eauto. condtac; ss.
        guardH o. inv PROMISE; ss.
        + erewrite Memory.add_o; eauto. condtac; ss; eauto.
        + erewrite Memory.split_o; eauto. condtac; ss. condtac; ss; eauto.
          guardH o0. i. des. inv GET.
          exploit Memory.split_get0; try exact PROMISES. i. des.
          exploit PROMISES1; try exact GET0; eauto.
        + erewrite Memory.lower_o; eauto. condtac; ss; eauto.
      - inv LOCAL1. inv STEP. inv LOCAL2. inv STEP. inv WRITE. ss.
        ii. revert GET0. erewrite Memory.remove_o; eauto. condtac; ss.
        guardH o. inv PROMISE; ss.
        + erewrite Memory.add_o; eauto. condtac; ss; eauto.
        + erewrite Memory.split_o; eauto. condtac; ss. condtac; ss; eauto.
          guardH o0. i. des. inv GET0.
          exploit Memory.split_get0; try exact PROMISES. i. des.
          exploit PROMISES1; try exact GET0; eauto.
        + erewrite Memory.lower_o; eauto. condtac; ss; eauto.
    Qed.

    Lemma opt_step_reserve_only
          rels1 rels2 e e1 e2
          (PROMISES1: reserve_only (Local.promises (Thread.local e1)))
          (STEP: opt_step rels1 rels2 e e1 e2):
      <<PROMISES2: reserve_only (Local.promises (Thread.local e2))>>.
    Proof.
      inv STEP; ss.
      eapply step_reserve_only; eauto.
    Qed.

    Lemma reserve_step_reserve_only
          e1 e2
          (PROMISES1: reserve_only (Local.promises (Thread.local e1)))
          (STEP: @Thread.reserve_step lang e1 e2):
      <<PROMISES2: reserve_only (Local.promises (Thread.local e2))>>.
    Proof.
      inv STEP. inv STEP0; inv STEP; inv LOCAL. inv PROMISE. ss. ii.
      revert GET. erewrite Memory.add_o; eauto. condtac; ss; eauto.
      i. des. inv GET. ss.
    Qed.

    Lemma cancel_step_reserve_only
          e1 e2
          (PROMISES1: reserve_only (Local.promises (Thread.local e1)))
          (STEP: @Thread.cancel_step lang e1 e2):
      <<PROMISES2: reserve_only (Local.promises (Thread.local e2))>>.
    Proof.
      inv STEP. inv STEP0; inv STEP; inv LOCAL. inv PROMISE. ss. ii.
      revert GET. erewrite Memory.remove_o; eauto. condtac; ss; eauto.
    Qed.

    Lemma reserve_steps_reserve_only
          e1 e2
          (PROMISES1: reserve_only (Local.promises (Thread.local e1)))
          (STEPS: rtc (@Thread.reserve_step lang) e1 e2):
      <<PROMISES2: reserve_only (Local.promises (Thread.local e2))>>.
    Proof.
      induction STEPS; ss.
      hexploit reserve_step_reserve_only; eauto.
    Qed.

    Lemma cancel_steps_reserve_only
          e1 e2
          (PROMISES1: reserve_only (Local.promises (Thread.local e1)))
          (STEPS: rtc (@Thread.cancel_step lang) e1 e2):
      <<PROMISES2: reserve_only (Local.promises (Thread.local e2))>>.
    Proof.
      induction STEPS; ss.
      hexploit cancel_step_reserve_only; eauto.
    Qed.

    Lemma step_rels_incl
          rels1 rels2 e e1 e2
          (STEP: step rels1 rels2 e e1 e2):
      rels2 = rels1 \/ exists a, rels2 = a :: rels1.
    Proof.
      inv STEP. unfold ReleaseWrites.append. des_ifs; eauto.
    Qed.

    Lemma step_non_concrete
          rels1 rels2 e e1 e2 loc to
          (STEP: step rels1 rels2 e e1 e2)
          (LOC: L loc)
          (EVENT: forall from val released ord,
              ThreadEvent.is_writing e <> Some (loc, from, to, val, released, ord))
          (GET1: forall from val released,
              Memory.get loc to (Thread.memory e1) <> Some (from, Message.concrete val released)):
      <<GET2: forall from val released,
        Memory.get loc to (Thread.memory e2) <> Some (from, Message.concrete val released)>>.
    Proof.
      i. inv STEP. inv STEP0; inv STEP; inv LOCAL; ss; eauto.
      - inv PROMISE.
        + erewrite Memory.add_o; eauto. condtac; ss; eauto.
          des. subst. ii. clarify. exploit PF; ss.
        + erewrite Memory.split_o; eauto. repeat condtac; ss; eauto.
          * des. subst. exploit PF; eauto.
          * guardH o. des. subst. exploit PF; eauto.
        + erewrite Memory.lower_o; eauto. condtac; ss; eauto.
          des. subst. ii. clarify. exploit PF; ss.
        + erewrite Memory.remove_o; eauto. condtac; ss; eauto.
      - inv LOCAL0. inv STEP. inv WRITE. inv PROMISE; ss.
        + erewrite Memory.add_o; eauto. condtac; ss; eauto.
          des. subst. exploit EVENT; eauto.
        + erewrite Memory.split_o; eauto. repeat condtac; ss; eauto.
          * des. subst. exploit EVENT; eauto.
          * des. subst. exploit EVENT; eauto.
          * guardH o. des. subst.
            exploit Memory.split_get0; try exact MEM. i. des.
            exploit GET1; eauto.
        + erewrite Memory.lower_o; eauto. condtac; ss; eauto.
          des. subst. exploit EVENT; eauto.
      - inv LOCAL1. inv STEP.
        inv LOCAL2. inv STEP. inv WRITE. inv PROMISE; ss.
        + erewrite Memory.add_o; eauto. condtac; ss; eauto.
          des. subst. exploit EVENT; eauto.
        + erewrite Memory.split_o; eauto. repeat condtac; ss; eauto.
          * des. subst. exploit EVENT; eauto.
          * des. subst. exploit EVENT; eauto.
          * guardH o. des. subst.
            exploit Memory.split_get0; try exact MEM. i. des.
            exploit GET1; eauto.
        + erewrite Memory.lower_o; eauto. condtac; ss; eauto.
          des. subst. exploit EVENT; eauto.
    Qed.

    Lemma opt_step_non_concrete
          rels1 rels2 e e1 e2 loc to
          (STEP: opt_step rels1 rels2 e e1 e2)
          (LOC: L loc)
          (EVENT: forall from val released ord,
              ThreadEvent.is_writing e <> Some (loc, from, to, val, released, ord))
          (GET1: forall from val released,
              Memory.get loc to (Thread.memory e1) <> Some (from, Message.concrete val released)):
      <<GET2: forall from val released,
        Memory.get loc to (Thread.memory e2) <> Some (from, Message.concrete val released)>>.
    Proof.
      inv STEP; eauto.
      eapply step_non_concrete; eauto.
    Qed.

    Lemma reserve_steps_non_concrete
          e1 e2 loc to
          (STEPS: rtc (@Thread.reserve_step lang) e1 e2)
          (LOC: L loc)
          (GET1: forall from val released,
              Memory.get loc to (Thread.memory e1) <> Some (from, Message.concrete val released)):
      <<GET2: forall from val released,
        Memory.get loc to (Thread.memory e2) <> Some (from, Message.concrete val released)>>.
    Proof.
      induction STEPS; eauto. i.
      eapply IHSTEPS; eauto. i.
      inv H. inv STEP; inv STEP0; inv LOCAL. inv PROMISE; ss.
      erewrite Memory.add_o; eauto. condtac; ss; eauto.
    Qed.

    Lemma cancel_steps_non_concrete
          e1 e2 loc to
          (STEPS: rtc (@Thread.cancel_step lang) e1 e2)
          (LOC: L loc)
          (GET1: forall from val released,
              Memory.get loc to (Thread.memory e1) <> Some (from, Message.concrete val released)):
      <<GET2: forall from val released,
        Memory.get loc to (Thread.memory e2) <> Some (from, Message.concrete val released)>>.
    Proof.
      induction STEPS; eauto. i.
      eapply IHSTEPS; eauto. i.
      inv H. inv STEP; inv STEP0; inv LOCAL. inv PROMISE; ss.
      erewrite Memory.remove_o; eauto. condtac; ss; eauto.
    Qed.
  End RAThread.
End RAThread.


Module RAConfiguration.
  Section RAConfiguration.
    Variable L: Loc.t -> bool.

    Inductive step:
      forall (e: ThreadEvent.t) (tid: Ident.t) (rels1 rels2: ReleaseWrites.t) (c1 c2: Configuration.t), Prop :=
    | step_intro
        rels1 rels2
        e tid c1 lang st1 lc1 e2 e3 st4 lc4 sc4 memory4
        (TID: IdentMap.find tid (Configuration.threads c1) = Some (existT _ lang st1, lc1))
        (CANCELS: rtc (@Thread.cancel_step _) (Thread.mk _ st1 lc1 (Configuration.sc c1) (Configuration.memory c1)) e2)
        (STEP: RAThread.opt_step L rels1 rels2 e e2 e3)
        (RESERVES: rtc (@Thread.reserve_step _) e3 (Thread.mk _ st4 lc4 sc4 memory4))
        (CONSISTENT: e <> ThreadEvent.failure ->
                     OrdThread.consistent L Ordering.acqrel (Thread.mk _ st4 lc4 sc4 memory4)):
        step e tid rels1 rels2
             c1 (Configuration.mk (IdentMap.add tid (existT _ _ st4, lc4) (Configuration.threads c1)) sc4 memory4)
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

    Lemma steps_trans
          rels1 rels2 rels3 c1 c2 c3
          (STEPS1: steps rels1 rels2 c1 c2)
          (STEPS2: steps rels2 rels3 c2 c3):
      steps rels1 rels3 c1 c3.
    Proof.
      revert c3 STEPS2. induction STEPS1; i; eauto.
    Qed.

    Lemma step_ord_step
          e tid rels1 rels2 c1 c2
          (STEP: step e tid rels1 rels2 c1 c2):
      OrdConfiguration.step L Ordering.acqrel e tid c1 c2.
    Proof.
      inv STEP. econs; eauto. inv STEP0; [econs 1|].
      inv STEP. econs 2. eauto.
    Qed.

    Lemma steps_ord_steps
          rels1 rels2 c1 c2
          (STEPS: steps rels1 rels2 c1 c2):
      rtc (@OrdConfiguration.all_step L Ordering.acqrel) c1 c2.
    Proof.
      induction STEPS; eauto.
      exploit step_ord_step; eauto. i. econs 2; eauto.
      econs. eauto.
    Qed.

    Lemma step_future
          e tid rels1 rels2 c1 c2
          (WF1: Configuration.wf c1)
          (STEP: step e tid rels1 rels2 c1 c2):
      <<WF2: Configuration.wf c2>>.
    Proof.
      inv WF1. inv WF. inv STEP; s.
      exploit THREADS; eauto. i.
      exploit Thread.rtc_cancel_step_future; try exact CANCELS; eauto. s. i. des.
      exploit RAThread.opt_step_future; try exact STEP0; eauto. i. des.
      exploit Thread.rtc_reserve_step_future; try exact RESERVES; eauto. s. i. des.
      econs; ss. econs.
      - i. Configuration.simplify.
        + exploit THREADS; try apply TH1; eauto. i.
          exploit Thread.rtc_tau_step_disjoint; try eapply rtc_implies;
            try eapply Thread.cancel_step_tau_step; try exact CANCELS; eauto. i. des.
          exploit RAThread.opt_step_disjoint; try exact STEP0; eauto. i. des.
          exploit Thread.rtc_tau_step_disjoint; try eapply rtc_implies;
            try eapply Thread.reserve_step_tau_step; try exact RESERVES; eauto. s. i. des.
          symmetry. ss.
        + exploit THREADS; try apply TH1; eauto. i.
          exploit Thread.rtc_tau_step_disjoint; try eapply rtc_implies;
            try eapply Thread.cancel_step_tau_step; try exact CANCELS; eauto. i. des.
          exploit RAThread.opt_step_disjoint; try exact STEP0; eauto. i. des.
          exploit Thread.rtc_tau_step_disjoint; try eapply rtc_implies;
            try eapply Thread.reserve_step_tau_step; try exact RESERVES; eauto. s. i. des.
          ss.
        + eapply DISJOINT; cycle 1; eauto.
      - i. Configuration.simplify.
        exploit THREADS; try apply TH; eauto. i. exploit THREADS; try apply TH1; eauto. i.
        exploit Thread.rtc_tau_step_disjoint; try eapply rtc_implies;
          try eapply Thread.cancel_step_tau_step; try exact CANCELS; eauto. i. des.
        exploit RAThread.opt_step_disjoint; try exact STEP0; eauto. i. des.
        exploit Thread.rtc_tau_step_disjoint; try eapply rtc_implies;
          try eapply Thread.reserve_step_tau_step; try exact RESERVES; eauto. s. i. des.
        ss.
    Qed.

    Lemma step_future2
          e tid rels1 rels2 c1 c2
          (WF1: Configuration.wf c1)
          (STEP: step e tid rels1 rels2 c1 c2):
      (<<WF2: Configuration.wf c2>>) /\
      (<<SC_FUTURE: TimeMap.le (Configuration.sc c1) (Configuration.sc c2)>>) /\
      (<<MEM_FUTURE: Memory.future (Configuration.memory c1) (Configuration.memory c2)>>).
    Proof.
      exploit step_future; eauto. i. des. split; ss.
      inv STEP. s.
      inv WF1. inv WF. exploit THREADS; eauto. i. clear DISJOINT THREADS.
      exploit Thread.rtc_cancel_step_future; eauto. s. i. des.
      exploit RAThread.opt_step_future; eauto. i. des.
      exploit Thread.rtc_reserve_step_future; eauto. s. i. des.
      splits; (etrans; [etrans|]; eauto).
    Qed.

    Lemma steps_future
          rels1 rels2 c1 c2
          (WF1: Configuration.wf c1)
          (STEPS: steps rels1 rels2 c1 c2):
      <<WF2: Configuration.wf c2>>.
    Proof.
      induction STEPS; ss.
      exploit step_future; eauto.
    Qed.

    Lemma steps_future2
          rels1 rels2 c1 c2
          (WF1: Configuration.wf c1)
          (STEPS: steps rels1 rels2 c1 c2):
      (<<WF2: Configuration.wf c2>>) /\
      (<<SC_FUTURE: TimeMap.le (Configuration.sc c1) (Configuration.sc c2)>>) /\
      (<<MEM_FUTURE: Memory.future (Configuration.memory c1) (Configuration.memory c2)>>).
    Proof.
      induction STEPS.
      - splits; ss; try refl.
      - exploit step_future2; eauto. i. des.
        exploit IHSTEPS; eauto. i. des.
        splits; ss; etrans; eauto.
    Qed.

    Lemma write_get_None
          e tid rels1 rels2 c1 c2
          loc from to val released ord
          (WF1: Configuration.wf c1)
          (STEP: step e tid rels1 rels2 c1 c2)
          (WRITE: ThreadEvent.is_writing e = Some (loc, from, to, val, released, ord)):
      (<<PROMISES: forall tid lang st lc
                     (FIND: IdentMap.find tid (Configuration.threads c2) = Some (existT _ lang st, lc)),
          Memory.get loc to (Local.promises lc) = None>>) /\
      (<<MEM: Memory.get loc to (Configuration.memory c2) = Some (from, Message.concrete val released)>>).
    Proof.
      inv STEP. inv STEP0; ss.
      split; cycle 1.
      { inv STEP. inv STEP0; inv STEP; inv LOCAL; ss.
        - inv LOCAL0. inv STEP. exploit Memory.write_get2; eauto. i. des.
          exploit RAThread.reserve_steps_get_None; eauto. i. des. inv WRITE. ss.
        - inv LOCAL1. inv STEP. inv LOCAL2. inv STEP.
          exploit Memory.write_get2; eauto. i. des.
          exploit RAThread.reserve_steps_get_None; eauto. i. des. inv WRITE. ss.
      }
      ii. revert FIND. rewrite IdentMap.gsspec. condtac; ss.
      { i. inv FIND.
        inv STEP. inv STEP0; inv STEP; inv LOCAL; ss.
        - inv LOCAL0. inv STEP. exploit Memory.write_get2; eauto. i. des.
          exploit RAThread.reserve_steps_get_None; eauto. i. des. inv WRITE. ss.
        - inv LOCAL1. inv STEP. inv LOCAL2. inv STEP.
          exploit Memory.write_get2; eauto. i. des.
          exploit RAThread.reserve_steps_get_None; eauto. i. des. inv WRITE. ss.
      }

      i. inv WF1. inv WF. hexploit DISJOINT; eauto. i.
      exploit THREADS; try eapply TID. i.
      exploit THREADS; try eapply FIND. i.
      exploit Thread.rtc_tau_step_disjoint; try eapply rtc_implies;
        try eapply Thread.cancel_step_tau_step; try exact CANCELS; eauto. i. des.
      exploit Thread.rtc_tau_step_future; try eapply rtc_implies;
        try eapply Thread.cancel_step_tau_step; try exact CANCELS; eauto. s. i. des.
      exploit RAThread.step_future; try exact STEP; eauto. i. des.
      inv STEP. inv STEP0; inv STEP; inv LOCAL; inv WRITE; ss.
      - inv LOCAL0. inv STEP. inv WRITE.
        exploit Memory.promise_disjoint; try eapply WF; try eapply DISJOINT2; eauto. i. des.
        exploit Memory.promise_get0; eauto; try by (inv PROMISE; ss). i. des.
        destruct (Memory.get loc to (Local.promises lc)) as [[]|] eqn:GETP; ss.
        exfalso.
        exploit MemoryFacts.promise_time_lt; eauto; try by (inv PROMISE; ss). i.
        inv DISJOINT0. hexploit DISJOINT1; eauto. i. des.
        exploit Memory.get_ts; try exact GETP. i. des.
        { subst. ss. }
        apply (H0 to); econs; ss; refl.
      - inv LOCAL1. inv STEP. inv LOCAL2. inv STEP. inv WRITE.
        exploit Memory.promise_disjoint; try eapply WF; try eapply DISJOINT2; eauto. i. des.
        exploit Memory.promise_get0; eauto; try by (inv PROMISE; ss). i. des.
        destruct (Memory.get loc to (Local.promises lc)) as [[]|] eqn:GETP; ss.
        exfalso.
        exploit MemoryFacts.promise_time_lt; eauto; try by (inv PROMISE; ss). i.
        inv DISJOINT0. hexploit DISJOINT1; eauto. i. des.
        exploit Memory.get_ts; try exact GETP. i. des.
        { subst. ss. }
        apply (H0 to); econs; ss; refl.
    Qed.

    Lemma step_get_None
          e tid rels1 rels2 c1 c2
          loc from to msg
          (STEP: step e tid rels1 rels2 c1 c2)
          (PROMISES1: forall tid lang st lc
                       (FIND: IdentMap.find tid (Configuration.threads c1) = Some (existT _ lang st, lc)),
              Memory.get loc to (Local.promises lc) = None)
          (MEM1: Memory.get loc to (Configuration.memory c1) = Some (from, msg)):
      (<<PROMISES2: forall tid lang st lc
                     (FIND: IdentMap.find tid (Configuration.threads c2) = Some (existT _ lang st, lc)),
          Memory.get loc to (Local.promises lc) = None>>) /\
      (<<MEM2: Memory.get loc to (Configuration.memory c2) = Some (from, msg)>>) /\
      (<<EVENT: forall from' val released ord, ThreadEvent.is_writing e <> Some (loc, from', to, val, released, ord)>>).
    Proof.
      inv STEP. ss.
      exploit PROMISES1; eauto. i.
      exploit RAThread.cancel_steps_get_None; eauto. i. des.
      exploit RAThread.opt_step_get_None; eauto. i. des.
      exploit RAThread.reserve_steps_get_None; eauto. i. des.
      splits; eauto. i.
      revert FIND. rewrite IdentMap.gsspec. condtac; eauto. i. inv FIND. ss.
    Qed.

    Lemma steps_rels
          rels1 rels2 c1 c2
          loc from to msg
          (STEPS: steps rels1 rels2 c1 c2)
          (PROMISES1: forall tid lang st lc
                       (FIND: IdentMap.find tid (Configuration.threads c1) = Some (existT _ lang st, lc)),
              Memory.get loc to (Local.promises lc) = None)
          (MEM1: Memory.get loc to (Configuration.memory c1) = Some (from, msg))
          (RELS1: ~ List.In (loc, to) rels1):
      ~ List.In (loc, to) rels2.
    Proof.
      induction STEPS; ss.
      exploit step_get_None; eauto. i. des.
      eapply IHSTEPS; eauto.
      ii. inv STEP. ss. inv STEP0; ss. inv STEP.
      unfold ReleaseWrites.append in H. des_ifs. inv H; ss. inv H0.
      eapply EVENT; eauto.
    Qed.

    Lemma write_rels
          e tid rels1 rels2 c1 c2
          loc from to val released ord
          (WF1: Configuration.wf c1)
          (RELS1: forall tid lang st lc
                    (TH: IdentMap.find tid (Configuration.threads c1) = Some (existT _ lang st, lc)),
              ReleaseWrites.wf rels1 (Local.promises lc) (Configuration.memory c1))
          (STEP: step e tid rels1 rels2 c1 c2)
          (WRITE: ThreadEvent.is_writing e = Some (loc, from, to, val, released, ord)):
      ~ List.In (loc, to) rels1.
    Proof.
      ii. inv STEP. inv STEP0; ss.
      hexploit RELS1; eauto. i.
      hexploit (@RAThread.steps_rels_wf lang L); try eapply RAThread.tau_steps_steps;
        try eapply RAThread.cancel_steps_tau_steps; eauto; ss; eauto. i.
      inv STEP. inv STEP0; inv STEP; inv LOCAL; ss.
      - inv LOCAL0. inv STEP. inv WRITE0.
        exploit RAThread.promise_rels_wf; eauto. i. des.
        exploit Memory.promise_get0; eauto; try by (inv PROMISE; ss). i. des.
        congr.
      - inv LOCAL1. inv STEP. inv LOCAL2. inv STEP. inv WRITE0. ss.
        exploit RAThread.promise_rels_wf; eauto. i. des.
        exploit Memory.promise_get0; eauto; try by (inv PROMISE; ss). i. des.
        congr.
    Qed.


    (* reserve_only *)

    Definition reserve_only (c: Configuration.t): Prop :=
      forall tid lang st lc
        (FIND: IdentMap.find tid (Configuration.threads c) = Some (existT _ lang st, lc)),
        RAThread.reserve_only L (Local.promises lc).

    Lemma init_reserve_only s:
      reserve_only (Configuration.init s).
    Proof.
      ii. unfold Configuration.init, Threads.init in *. ss.
      rewrite IdentMap.Facts.map_o in *.
      destruct (@UsualFMapPositive.UsualPositiveMap'.find
                  (@sigT _ (@Language.syntax ProgramEvent.t)) tid s); inv FIND.
      ss. rewrite Memory.bot_get in *. ss.
    Qed.

    Lemma step_reserve_only
          tid e rels1 rels2 c1 c2
          (RESERVE: reserve_only c1)
          (STEP: step tid e rels1 rels2 c1 c2):
      reserve_only c2.
    Proof.
      inv STEP. ii. ss.
      revert FIND. rewrite IdentMap.gsspec. condtac; ss; i; cycle 1.
      { eapply RESERVE; eauto. }
      inv FIND. apply inj_pair2 in H1. subst.
      unfold reserve_only in RESERVE.
      hexploit RESERVE; eauto. i.
      hexploit RAThread.cancel_steps_reserve_only; try exact CANCELS; eauto. i. des.
      hexploit RAThread.opt_step_reserve_only; try exact STEP0; eauto. i.
      hexploit RAThread.reserve_steps_reserve_only; try exact RESERVES; eauto.
    Qed.

    Lemma steps_reserve_only
          rels1 rels2 c1 c2
          (RESERVE: reserve_only c1)
          (STEPS: steps rels1 rels2 c1 c2):
      reserve_only c2.
    Proof.
      induction STEPS; ss.
      hexploit step_reserve_only; eauto.
    Qed.

    Lemma step_rels_incl
          e tid rels1 rels2 c1 c2
          (STEP: step e tid rels1 rels2 c1 c2):
      rels2 = rels1 \/ exists a, rels2 = a :: rels1.
    Proof.
      inv STEP. inv STEP0; eauto. inv STEP.
      unfold ReleaseWrites.append. des_ifs; eauto.
    Qed.

    Lemma steps_rels_incl
          rels1 rels2 c1 c2
          (STEPS: steps rels1 rels2 c1 c2):
      exists rels, rels2 = rels ++ rels1.
    Proof.
      induction STEPS.
      - exists []. ss.
      - des. exploit step_rels_incl; eauto. i. des; subst.
        + exists rels. ss.
        + exists (rels ++ [a]). rewrite <- List.app_assoc. ss.
    Qed.

    Lemma step_non_concrete
          e tid rels1 rels2 c1 c2 loc to
          (STEP: step e tid rels1 rels2 c1 c2)
          (LOC: L loc)
          (EVENT: forall from val released ord,
              ThreadEvent.is_writing e <> Some (loc, from, to, val, released, ord))
          (GET1: forall from val released,
              Memory.get loc to (Configuration.memory c1) <> Some (from, Message.concrete val released)):
      <<GET2: forall from val released,
        Memory.get loc to (Configuration.memory c2) <> Some (from, Message.concrete val released)>>.
    Proof.
      inv STEP. ss.
      hexploit RAThread.cancel_steps_non_concrete; eauto. i. des.
      hexploit RAThread.opt_step_non_concrete; eauto. i. des.
      hexploit RAThread.reserve_steps_non_concrete; eauto.
    Qed.
  End RAConfiguration.
End RAConfiguration.


Module RARaceW.
  Section RARace.
    Variable L: Loc.t -> bool.

    Definition ra_race (rels: ReleaseWrites.t) (tview: TView.t) (loc: Loc.t) (to: Time.t) (ordr: Ordering.t): Prop :=
      (<<LOC: L loc>>) /\
      (<<HIGHER: Time.lt ((View.rlx (TView.cur tview)) loc) to>>) /\
      ((<<ORDW: ~ List.In (loc, to) rels>>) \/
       (<<ORDR: Ordering.le ordr Ordering.strong_relaxed>>)).

    Definition ra_race_steps (rels: ReleaseWrites.t) (c: Configuration.t): Prop :=
      exists tid rels2 rels3 rels4
        c2 lang st2 lc2 e loc to val released ord e3 e4,
        (<<STEPS: RAConfiguration.steps L rels rels2 c c2>>) /\
        (<<TID: IdentMap.find tid (Configuration.threads c2) = Some (existT _ lang st2, lc2)>>) /\
        (<<THREAD_STEPS: RAThread.steps L rels2 rels3
                                        (Thread.mk _ st2 lc2 (Configuration.sc c2) (Configuration.memory c2)) e3>>) /\
        (<<CONS: Local.promise_consistent (Thread.local e3)>>) /\
        (<<THREAD_STEP: RAThread.step L rels3 rels4 e e3 e4>>) /\
        (<<READ: ThreadEvent.is_reading e = Some (loc, to, val, released, ord)>>) /\
        (<<RARACE: ra_race rels3 (Local.tview (Thread.local e3)) loc to ord>>).

    Definition racefree (rels: ReleaseWrites.t) (c: Configuration.t): Prop :=
      forall tid rels2 rels3 rels4
        c2 lang st2 lc2 e loc to val released ord e3 e4
        (STEPS: RAConfiguration.steps L rels rels2 c c2)
        (TID: IdentMap.find tid (Configuration.threads c2) = Some (existT _ lang st2, lc2))
        (THREAD_STEPS: RAThread.steps L rels2 rels3
                                      (Thread.mk _ st2 lc2 (Configuration.sc c2) (Configuration.memory c2)) e3)
        (CONS: Local.promise_consistent (Thread.local e3))
        (THREAD_STEP: RAThread.step L rels3 rels4 e e3 e4)
        (READ: ThreadEvent.is_reading e = Some (loc, to, val, released, ord))
        (RARACE: ra_race rels3 (Local.tview (Thread.local e3)) loc to ord),
        False.

    Definition racefree_syn (syn: Threads.syntax): Prop :=
      racefree [] (Configuration.init syn).

    Lemma step_racefree
          e tid rels1 rels2 c1 c2
          (RACEFREE: racefree rels1 c1)
          (STEP: RAConfiguration.step L e tid rels1 rels2 c1 c2):
      racefree rels2 c2.
    Proof.
      ii. eapply RACEFREE; eauto. econs 2; eauto.
    Qed.

    Lemma step_ord_step
          e tid rels1 rels2 c1 c2
          (STEP: RAConfiguration.step L e tid rels1 rels2 c1 c2):
      OrdConfiguration.step L Ordering.acqrel e tid c1 c2.
    Proof.
      inv STEP. econs; eauto. inv STEP0.
      - econs 1.
      - inv STEP. econs 2. eauto.
    Qed.
  End RARace.
End RARaceW.
