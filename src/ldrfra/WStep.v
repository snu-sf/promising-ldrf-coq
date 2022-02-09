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
Require Import Writes.

Set Implicit Arguments.


Module WThread.
  Section WThread.
    Variable lang: language.
    Variable L: Loc.t -> bool.
    Variable ordcr: Ordering.t.
    Variable ordcw: Ordering.t.

    Inductive step rels1: forall (rels2: Writes.t) (e: ThreadEvent.t) (e1 e2: Thread.t lang), Prop :=
    | step_intro
        pf e e1 e2
        (STEP: @OrdThread.step lang L ordcr ordcw pf e e1 e2):
        step rels1 (Writes.append L e rels1) e e1 e2
    .

    Inductive steps rels1: forall (rels2: Writes.t) (e1 e2: Thread.t lang), Prop :=
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

    Inductive tau_steps rels1: forall (rels2: Writes.t) (e1 e2: Thread.t lang), Prop :=
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

    Inductive opt_step rels1: forall (rels2: Writes.t) (e: ThreadEvent.t) (e1 e2: Thread.t lang), Prop :=
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
      exists pf, OrdThread.step L ordcr ordcw pf e e1 e2.
    Proof.
      inv STEP. eauto.
    Qed.

    Lemma opt_step_ord_opt_step
          rels1 rels2 e e1 e2
          (STEP: opt_step rels1 rels2 e e1 e2):
      OrdThread.opt_step L ordcr ordcw e e1 e2.
    Proof.
      inv STEP; [econs 1|].
      exploit step_ord_step; eauto. i. des.
      econs 2. eauto.
    Qed.

    Lemma steps_ord_steps
          rels1 rels2 e1 e2
          (STEPS: steps rels1 rels2 e1 e2):
      rtc (OrdThread.all_step L ordcr ordcw) e1 e2.
    Proof.
      induction STEPS; eauto.
      exploit step_ord_step; eauto. i. des.
      econs 2; eauto. econs. econs. eauto.
    Qed.

    Lemma tau_steps_ord_tau_steps
          rels1 rels2 e1 e2
          (STEPS: tau_steps rels1 rels2 e1 e2):
      rtc (@OrdThread.tau_step lang L ordcr ordcw) e1 e2.
    Proof.
      induction STEPS; eauto.
      inv STEP; ss.
      econs 2; eauto. econs; eauto. econs. eauto.
    Qed.

    Lemma ord_tau_steps_tau_steps
          e1 e2
          (STEPS: rtc (@OrdThread.tau_step lang L ordcr ordcw) e1 e2):
      forall rels1, exists rels2,
          tau_steps rels1 rels2 e1 e2.
    Proof.
      induction STEPS; eauto. inv H. inv TSTEP. i.
      specialize (IHSTEPS (Writes.append L e rels1)). des.
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
            (Writes.append
               L (ThreadEvent.promise loc from to Message.reserve Memory.op_kind_add) rels)
            at 2 by ss.
        econs. econs 1; eauto.
        ii. inv PROMISE. ss.
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
            (Writes.append
               L (ThreadEvent.promise loc from to Message.reserve Memory.op_kind_cancel) rels)
            at 2 by ss.
        econs. econs 1; eauto.
        ii. inv PROMISE; ss.
      - ss.
    Qed.

    Lemma tau_steps_rtc_tau_step
          rels1 rels2 e1 e2
          (STEPS: tau_steps rels1 rels2 e1 e2):
      rtc (@OrdThread.tau_step lang L ordcr ordcw) e1 e2.
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


    (* Writes.wf *)

    Lemma step_writes_wf
          rels1 rels2 e e1 e2
          (ORDCW: Ordering.le Ordering.plain ordcw)
          (RELS1: Writes.wf L rels1 (Thread.memory e1))
          (STEP: step rels1 rels2 e e1 e2):
      Writes.wf L rels2 (Thread.memory e2).
    Proof.
      inv STEP. eapply Writes.step_wf; eauto.
    Qed.

    Lemma steps_writes_wf
          rels1 rels2 e1 e2
          (ORDCW: Ordering.le Ordering.plain ordcw)
          (RELS1: Writes.wf L rels1 (Thread.memory e1))
          (STEPS: steps rels1 rels2 e1 e2):
      Writes.wf L rels2 (Thread.memory e2).
    Proof.
      induction STEPS; eauto.
      apply IHSTEPS. eapply step_writes_wf; eauto.
    Qed.

    (* Lemma step_rels_disjoint *)
    (*       rels1 rels2 e e1 e2 promises *)
    (*       (RELS1: Writes.wf L rels1 (Local.promises (Thread.local e1)) (Thread.memory e1)) *)
    (*       (STEP: step rels1 rels2 e e1 e2) *)
    (*       (DISJOINT: Memory.disjoint (Local.promises (Thread.local e1)) promises) *)
    (*       (LE: Memory.le promises (Thread.memory e1)) *)
    (*       (RELS: Writes.wf L rels1 promises (Thread.memory e1)): *)
    (*   Writes.wf L rels2 promises (Thread.memory e2). *)
    (* Proof. *)
    (*   inv STEP. eauto using Writes.step_disjoint. *)
    (* Qed. *)

    (* Lemma steps_rels_disjoint *)
    (*       rels1 rels2 e1 e2 lc *)
    (*       (RELS1: Writes.wf L rels1 (Local.promises (Thread.local e1)) (Thread.memory e1)) *)
    (*       (STEPS: steps rels1 rels2 e1 e2) *)
    (*       (WF1: Local.wf (Thread.local e1) (Thread.memory e1)) *)
    (*       (SC1: Memory.closed_timemap (Thread.sc e1) (Thread.memory e1)) *)
    (*       (CLOSED1: Memory.closed (Thread.memory e1)) *)
    (*       (DISJOINT: Local.disjoint (Thread.local e1) lc) *)
    (*       (WF: Local.wf lc (Thread.memory e1)) *)
    (*       (RELS: Writes.wf L rels1 (Local.promises lc) (Thread.memory e1)): *)
    (*   Writes.wf L rels2 (Local.promises lc) (Thread.memory e2). *)
    (* Proof. *)
    (*   induction STEPS; ss. *)
    (*   hexploit step_rels_disjoint; eauto; try apply DISJOINT; try apply WF. i. *)
    (*   hexploit step_writes_wf; eauto. i. *)
    (*   inv STEP. *)
    (*   exploit OrdThread.step_future; eauto. i. des. *)
    (*   exploit OrdThread.step_disjoint; eauto. i. des. *)
    (*   eapply IHSTEPS; eauto. *)
    (* Qed. *)


    Lemma cap_tau_steps_current_tau_steps_aux
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
      replace (Writes.append L e rels1) with (Writes.append L fe rels1) in STEPS0; cycle 1.
      { unfold Writes.append. destruct e; inv EVENT; ss.
        - inv FROM. inv TO. refl.
        - inv FROM. inv TO. refl.
        - inv FROM. inv TO. refl.
      }
      econs; [econs 1; eauto|..]; eauto.
      destruct e; inv EVENT; ss.
    Qed.

    Lemma cap_tau_steps_current_tau_steps
          rels1 rels2 e1 e2 mem1
          (LOCAL: Local.wf (Thread.local e1) (Thread.memory e1))
          (MEMORY: Memory.closed (Thread.memory e1))
          (SC: Memory.closed_timemap (Thread.sc e1) (Thread.memory e1))
          (CAP: Memory.cap (Thread.memory e1) mem1)
          (STEPS: tau_steps rels1 rels2 (Thread.mk lang (Thread.state e1) (Thread.local e1) (Thread.sc e1) mem1) e2):
        exists e2',
          (<<STEPS: tau_steps rels1 rels2 e1 e2'>>) /\
          (<<THREAD: thread_map ident_map e2 e2'>>).
    Proof.
      exploit cap_tau_steps_current_tau_steps_aux; try apply STEPS; eauto; ss.
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
        { eapply mapping_map_lt_iff_collapsable_unwritable. eapply ident_map_lt_iff. }
        { eapply ident_map_timemap. }
        { refl. }
      }
      { eapply Local.cap_wf; eauto. }
      { eapply Memory.cap_closed; eauto. }
      { eapply Memory.cap_closed_timemap; eauto. }
      i. des. esplits; eauto.
    Qed.

    Lemma cap_plus_step_current_plus_step
          rels1 rels2 rels3 e e1 e2 e3 mem1
          (LOCAL: Local.wf (Thread.local e1) (Thread.memory e1))
          (MEMORY: Memory.closed (Thread.memory e1))
          (SC: Memory.closed_timemap (Thread.sc e1) (Thread.memory e1))
          (CAP: Memory.cap (Thread.memory e1) mem1)
          (STEPS: tau_steps rels1 rels2 (Thread.mk lang (Thread.state e1) (Thread.local e1) (Thread.sc e1) mem1) e2)
          (STEP: WThread.step rels2 rels3 e e2 e3):
        exists rels3' e' e2' e3',
          (<<STEPS: tau_steps rels1 rels2 e1 e2'>>) /\
          (<<STEP: WThread.step rels2 rels3' e' e2' e3'>>) /\
          (<<LOCAL: local_map ident_map (Thread.local e2) (Thread.local e2')>>) /\
          (<<EVENT: tevent_map ident_map e' e>>).
    Proof.
      exploit cap_tau_steps_current_tau_steps_aux; try apply STEPS; eauto; ss.
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
        { eapply mapping_map_lt_iff_collapsable_unwritable. eapply ident_map_lt_iff. }
        { eapply ident_map_timemap. }
        { refl. }
      }
      { eapply Local.cap_wf; eauto. }
      { eapply Memory.cap_closed; eauto. }
      { eapply Memory.cap_closed_timemap; eauto. }
      i. des.
      exploit steps_future; try eapply tau_steps_steps; try apply STEPS; ss.
      { eapply Local.cap_wf; eauto. }
      { eapply Memory.cap_closed_timemap; eauto. }
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
          promises1 mem1 loc' from' to' msg' promises2 mem2 kind
          loc from to msg
          (WRITE: Memory.write promises1 mem1 loc' from' to' msg' promises2 mem2 kind)
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

    Lemma write_na_get_None
          ts promises1 mem1 loc' from' to' val' promises2 mem2 msgs kinds kind
          loc from to msg
          (WRITE: Memory.write_na ts promises1 mem1 loc' from' to' val' promises2 mem2 msgs kinds kind)
          (PROMISES1: Memory.get loc to promises1 = None)
          (MEM1: Memory.get loc to mem1 = Some (from, msg)):
      (<<PROMISES2: Memory.get loc to promises2 = None>>) /\
      (<<MEM2: Memory.get loc to mem2 = Some (from, msg)>>) /\
      (<<LOCTS: __guard__ (loc' <> loc \/ to' <> to)>>).
    Proof.
      induction WRITE; eauto using write_get_None.
      exploit write_get_None; eauto. i. des.
      apply IHWRITE; auto.
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
      - inv LOCAL0. inv STEP. ss.
        exploit write_get_None; eauto. i. des. splits; ss.
        ii. inv H. unguard. des; ss.
      - inv LOCAL1. inv STEP. inv LOCAL2. inv STEP. ss.
        exploit write_get_None; eauto. i. des. splits; ss.
        ii. inv H. unguard. des; ss.
      - inv LOCAL0. ss.
      - inv LOCAL0. ss.
      - inv LOCAL0.
        + inv STEP. ss.
          exploit write_na_get_None; eauto. i. des. splits; ss.
          ii. inv H. unguard. des; ss.
        + inv STEP. ss.
        exploit write_get_None; eauto. i. des. splits; ss.
        ii. inv H. unguard. des; ss.
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

    Lemma step_reserve_only
          rels1 rels2 e e1 e2
          (PROMISES1: OrdLocal.reserve_only L (Local.promises (Thread.local e1)))
          (STEP: step rels1 rels2 e e1 e2):
      <<PROMISES2: OrdLocal.reserve_only L (Local.promises (Thread.local e2))>>.
    Proof.
      inv STEP. eauto using OrdThread.step_reserve_only.
    Qed.

    Lemma opt_step_reserve_only
          rels1 rels2 e e1 e2
          (PROMISES1: OrdLocal.reserve_only L (Local.promises (Thread.local e1)))
          (STEP: opt_step rels1 rels2 e e1 e2):
      <<PROMISES2: OrdLocal.reserve_only L (Local.promises (Thread.local e2))>>.
    Proof.
      inv STEP; ss.
      eapply step_reserve_only; eauto.
    Qed.

    Lemma reserve_step_reserve_only
          e1 e2
          (PROMISES1: OrdLocal.reserve_only L (Local.promises (Thread.local e1)))
          (STEP: @Thread.reserve_step lang e1 e2):
      <<PROMISES2: OrdLocal.reserve_only L (Local.promises (Thread.local e2))>>.
    Proof.
      inv STEP. inv STEP0; inv STEP; inv LOCAL. inv PROMISE. ss. ii.
      revert GET. erewrite Memory.add_o; eauto. condtac; ss; eauto.
      i. des. inv GET. ss.
    Qed.

    Lemma cancel_step_reserve_only
          e1 e2
          (PROMISES1: OrdLocal.reserve_only L (Local.promises (Thread.local e1)))
          (STEP: @Thread.cancel_step lang e1 e2):
      <<PROMISES2: OrdLocal.reserve_only L (Local.promises (Thread.local e2))>>.
    Proof.
      inv STEP. inv STEP0; inv STEP; inv LOCAL. inv PROMISE. ss. ii.
      revert GET. erewrite Memory.remove_o; eauto. condtac; ss; eauto.
    Qed.

    Lemma reserve_steps_reserve_only
          e1 e2
          (PROMISES1: OrdLocal.reserve_only L (Local.promises (Thread.local e1)))
          (STEPS: rtc (@Thread.reserve_step lang) e1 e2):
      <<PROMISES2: OrdLocal.reserve_only L (Local.promises (Thread.local e2))>>.
    Proof.
      induction STEPS; ss.
      hexploit reserve_step_reserve_only; eauto.
    Qed.

    Lemma cancel_steps_reserve_only
          e1 e2
          (PROMISES1: OrdLocal.reserve_only L (Local.promises (Thread.local e1)))
          (STEPS: rtc (@Thread.cancel_step lang) e1 e2):
      <<PROMISES2: OrdLocal.reserve_only L (Local.promises (Thread.local e2))>>.
    Proof.
      induction STEPS; ss.
      hexploit cancel_step_reserve_only; eauto.
    Qed.

    Lemma step_rels_incl
          rels1 rels2 e e1 e2
          (STEP: step rels1 rels2 e e1 e2):
      rels2 = rels1 \/ exists a, rels2 = a :: rels1.
    Proof.
      inv STEP. unfold Writes.append. des_ifs; eauto.
    Qed.

    (* Lemma step_non_concrete *)
    (*       rels1 rels2 e e1 e2 loc to *)
    (*       (STEP: step rels1 rels2 e e1 e2) *)
    (*       (LOC: L loc) *)
    (*       (EVENT: forall from val released ord, *)
    (*           ThreadEvent.is_writing e <> Some (loc, from, to, val, released, ord)) *)
    (*       (GET1: forall from msg (GET: Memory.get loc to (Thread.memory e1) = Some (from, msg)), *)
    (*           msg = Message.reserve): *)
    (*   <<GET2: forall from msg (GET: Memory.get loc to (Thread.memory e2) = Some (from, msg)), *)
    (*       msg = Message.reserve>>. *)
    (* Proof. *)
    (*   i. inv STEP. inv STEP0; inv STEP; inv LOCAL; ss; eauto. *)
    (*   - inv PROMISE. *)
    (*     + erewrite Memory.add_o; eauto. condtac; ss; eauto. *)
    (*       des. subst. ii. clarify. exploit PF; eauto. *)
    (*     + erewrite Memory.split_o; eauto. repeat condtac; ss; eauto. *)
    (*       * des. subst. ii. clarify. exploit PF; eauto. *)
    (*       * guardH o. des. subst. ii. clarify. *)
    (*         exploit PF; eauto. i. subst. ss. *)
    (*     + erewrite Memory.lower_o; eauto. condtac; ss; eauto. *)
    (*       des. subst. ii. clarify. exploit PF; ss. *)
    (*     + erewrite Memory.remove_o; eauto. condtac; ss; eauto. *)
    (*   - inv LOCAL0. inv STEP. inv WRITE. inv PROMISE; ss. *)
    (*     + erewrite Memory.add_o; eauto. condtac; ss; eauto. *)
    (*       des. subst. exploit EVENT; eauto. ss. *)
    (*     + erewrite Memory.split_o; eauto. repeat condtac; ss; eauto. *)
    (*       * des. subst. exploit EVENT; eauto. ss. *)
    (*       * des. subst. exploit EVENT; eauto. ss. *)
    (*       * guardH o. des. subst. *)
    (*         exploit Memory.split_get0; try exact MEM. i. des. *)
    (*         exploit GET1; eauto. ss. *)
    (*     + erewrite Memory.lower_o; eauto. condtac; ss; eauto. *)
    (*       des. subst. exploit EVENT; eauto. ss. *)
    (*   - inv LOCAL1. inv STEP. *)
    (*     inv LOCAL2. inv STEP. inv WRITE. inv PROMISE; ss. *)
    (*     + erewrite Memory.add_o; eauto. condtac; ss; eauto. *)
    (*       des. subst. exploit EVENT; eauto. ss. *)
    (*     + erewrite Memory.split_o; eauto. repeat condtac; ss; eauto. *)
    (*       * des. subst. exploit EVENT; eauto. ss. *)
    (*       * des. subst. exploit EVENT; eauto. ss. *)
    (*       * guardH o. des. subst. *)
    (*         exploit Memory.split_get0; try exact MEM. i. des. *)
    (*         exploit GET1; eauto. ss. *)
    (*     + erewrite Memory.lower_o; eauto. condtac; ss; eauto. *)
    (*       des. subst. exploit EVENT; eauto. ss. *)
    (* Qed. *)

    (* Lemma opt_step_non_concrete *)
    (*       rels1 rels2 e e1 e2 loc to *)
    (*       (STEP: opt_step rels1 rels2 e e1 e2) *)
    (*       (LOC: L loc) *)
    (*       (EVENT: forall from val released ord, *)
    (*           ThreadEvent.is_writing e <> Some (loc, from, to, val, released, ord)) *)
    (*       (GET1: forall from msg (GET: Memory.get loc to (Thread.memory e1) = Some (from, msg)), *)
    (*           msg = Message.reserve): *)
    (*   <<GET2: forall from msg (GET: Memory.get loc to (Thread.memory e2) = Some (from, msg)), *)
    (*       msg = Message.reserve>>. *)
    (* Proof. *)
    (*   inv STEP; eauto. *)
    (*   eapply step_non_concrete; eauto. *)
    (* Qed. *)

    (* Lemma reserve_steps_non_concrete *)
    (*       e1 e2 loc to *)
    (*       (STEPS: rtc (@Thread.reserve_step lang) e1 e2) *)
    (*       (LOC: L loc) *)
    (*       (GET1: forall from msg (GET: Memory.get loc to (Thread.memory e1) = Some (from, msg)), *)
    (*           msg = Message.reserve): *)
    (*   <<GET2: forall from msg (GET: Memory.get loc to (Thread.memory e2) = Some (from, msg)), *)
    (*       msg = Message.reserve>>. *)
    (* Proof. *)
    (*   induction STEPS; eauto. i. *)
    (*   eapply IHSTEPS; eauto. i. *)
    (*   inv H. inv STEP; inv STEP0; inv LOCAL. inv PROMISE; ss. *)
    (*   revert GET. erewrite Memory.add_o; eauto. condtac; ss; eauto. *)
    (*   i. des. clarify. *)
    (* Qed. *)

    (* Lemma cancel_steps_non_concrete *)
    (*       e1 e2 loc to *)
    (*       (STEPS: rtc (@Thread.cancel_step lang) e1 e2) *)
    (*       (LOC: L loc) *)
    (*       (GET1: forall from msg (GET: Memory.get loc to (Thread.memory e1) = Some (from, msg)), *)
    (*           msg = Message.reserve): *)
    (*   <<GET2: forall from msg (GET: Memory.get loc to (Thread.memory e2) = Some (from, msg)), *)
    (*       msg = Message.reserve>>. *)
    (* Proof. *)
    (*   induction STEPS; eauto. i. *)
    (*   eapply IHSTEPS; eauto. i. *)
    (*   inv H. inv STEP; inv STEP0; inv LOCAL. inv PROMISE; ss. *)
    (*   revert GET. erewrite Memory.remove_o; eauto. condtac; ss; eauto. *)
    (* Qed. *)
  End WThread.
End WThread.


Module WConfiguration.
  Section WConfiguration.
    Variable L: Loc.t -> bool.
    Variable ordcr ordcw: Ordering.t.

    Inductive step:
      forall (e: ThreadEvent.t) (tid: Ident.t) (rels1 rels2: Writes.t) (c1 c2: Configuration.t), Prop :=
    | step_intro
        rels1 rels2
        e tid c1 lang st1 lc1 e2 e3 st4 lc4 sc4 memory4
        (TID: IdentMap.find tid (Configuration.threads c1) = Some (existT _ lang st1, lc1))
        (CANCELS: rtc (@Thread.cancel_step _) (Thread.mk _ st1 lc1 (Configuration.sc c1) (Configuration.memory c1)) e2)
        (STEP: WThread.opt_step L ordcr ordcw rels1 rels2 e e2 e3)
        (RESERVES: rtc (@Thread.reserve_step _) e3 (Thread.mk _ st4 lc4 sc4 memory4))
        (CONSISTENT: ThreadEvent.get_machine_event e <> MachineEvent.failure ->
                     OrdThread.consistent L ordcr ordcw (Thread.mk _ st4 lc4 sc4 memory4)):
        step e tid rels1 rels2
             c1 (Configuration.mk (IdentMap.add tid (existT _ _ st4, lc4) (Configuration.threads c1)) sc4 memory4)
    .

    Inductive steps rels1: forall (rels2: Writes.t) (c1 c2: Configuration.t), Prop :=
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
      OrdConfiguration.step L ordcr ordcw e tid c1 c2.
    Proof.
      inv STEP. econs; eauto. inv STEP0; [econs 1|].
      inv STEP. econs 2. eauto.
    Qed.

    Lemma steps_ord_steps
          rels1 rels2 c1 c2
          (STEPS: steps rels1 rels2 c1 c2):
      rtc (@OrdConfiguration.all_step L ordcr ordcw) c1 c2.
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
      exploit WThread.opt_step_future; try exact STEP0; eauto. i. des.
      exploit Thread.rtc_reserve_step_future; try exact RESERVES; eauto. s. i. des.
      econs; ss. econs.
      - i. Configuration.simplify.
        + exploit THREADS; try apply TH1; eauto. i.
          exploit Thread.rtc_tau_step_disjoint; try eapply rtc_implies;
            try eapply Thread.cancel_step_tau_step; try exact CANCELS; eauto. i. des.
          exploit WThread.opt_step_disjoint; try exact STEP0; eauto. i. des.
          exploit Thread.rtc_tau_step_disjoint; try eapply rtc_implies;
            try eapply Thread.reserve_step_tau_step; try exact RESERVES; eauto. s. i. des.
          symmetry. ss.
        + exploit THREADS; try apply TH1; eauto. i.
          exploit Thread.rtc_tau_step_disjoint; try eapply rtc_implies;
            try eapply Thread.cancel_step_tau_step; try exact CANCELS; eauto. i. des.
          exploit WThread.opt_step_disjoint; try exact STEP0; eauto. i. des.
          exploit Thread.rtc_tau_step_disjoint; try eapply rtc_implies;
            try eapply Thread.reserve_step_tau_step; try exact RESERVES; eauto. s. i. des.
          ss.
        + eapply DISJOINT; cycle 1; eauto.
      - i. Configuration.simplify.
        exploit THREADS; try apply TH; eauto. i. exploit THREADS; try apply TH1; eauto. i.
        exploit Thread.rtc_tau_step_disjoint; try eapply rtc_implies;
          try eapply Thread.cancel_step_tau_step; try exact CANCELS; eauto. i. des.
        exploit WThread.opt_step_disjoint; try exact STEP0; eauto. i. des.
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
      exploit WThread.opt_step_future; eauto. i. des.
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

    (* Lemma write_get_None *)
    (*       e tid rels1 rels2 c1 c2 *)
    (*       loc from to val released ord *)
    (*       (WF1: Configuration.wf c1) *)
    (*       (STEP: step e tid rels1 rels2 c1 c2) *)
    (*       (WRITE: ThreadEvent.is_writing e = Some (loc, from, to, val, released, ord)): *)
    (*   (<<PROMISES: forall tid lang st lc *)
    (*                  (FIND: IdentMap.find tid (Configuration.threads c2) = Some (existT _ lang st, lc)), *)
    (*       Memory.get loc to (Local.promises lc) = None>>) /\ *)
    (*   (<<MEM: Memory.get loc to (Configuration.memory c2) = Some (from, Message.concrete val released)>>). *)
    (* Proof. *)
    (*   inv STEP. inv STEP0; ss. *)
    (*   split; cycle 1. *)
    (*   { inv STEP. inv STEP0; inv STEP; inv LOCAL; ss. *)
    (*     - inv LOCAL0. inv STEP. exploit Memory.write_get2; eauto. i. des. *)
    (*       exploit WThread.reserve_steps_get_None; eauto. i. des. inv WRITE. ss. *)
    (*     - inv LOCAL1. inv STEP. inv LOCAL2. inv STEP. *)
    (*       exploit Memory.write_get2; eauto. i. des. *)
    (*       exploit WThread.reserve_steps_get_None; eauto. i. des. inv WRITE. ss. *)
    (*   } *)
    (*   ii. revert FIND. rewrite IdentMap.gsspec. condtac; ss. *)
    (*   { i. inv FIND. *)
    (*     inv STEP. inv STEP0; inv STEP; inv LOCAL; ss. *)
    (*     - inv LOCAL0. inv STEP. exploit Memory.write_get2; eauto. i. des. *)
    (*       exploit WThread.reserve_steps_get_None; eauto. i. des. inv WRITE. ss. *)
    (*     - inv LOCAL1. inv STEP. inv LOCAL2. inv STEP. *)
    (*       exploit Memory.write_get2; eauto. i. des. *)
    (*       exploit WThread.reserve_steps_get_None; eauto. i. des. inv WRITE. ss. *)
    (*   } *)

    (*   i. inv WF1. inv WF. hexploit DISJOINT; eauto. i. *)
    (*   exploit THREADS; try eapply TID. i. *)
    (*   exploit THREADS; try eapply FIND. i. *)
    (*   exploit Thread.rtc_tau_step_disjoint; try eapply rtc_implies; *)
    (*     try eapply Thread.cancel_step_tau_step; try exact CANCELS; eauto. i. des. *)
    (*   exploit Thread.rtc_tau_step_future; try eapply rtc_implies; *)
    (*     try eapply Thread.cancel_step_tau_step; try exact CANCELS; eauto. s. i. des. *)
    (*   exploit WThread.step_future; try exact STEP; eauto. i. des. *)
    (*   inv STEP. inv STEP0; inv STEP; inv LOCAL; inv WRITE; ss. *)
    (*   - inv LOCAL0. inv STEP. inv WRITE. *)
    (*     exploit Memory.promise_disjoint; try eapply WF; try eapply DISJOINT2; eauto. i. des. *)
    (*     exploit Memory.promise_get0; eauto; try by (inv PROMISE; ss). i. des. *)
    (*     destruct (Memory.get loc to (Local.promises lc)) as [[]|] eqn:GETP; ss. *)
    (*     exfalso. *)
    (*     exploit MemoryFacts.promise_time_lt; eauto; try by (inv PROMISE; ss). i. *)
    (*     inv DISJOINT0. hexploit DISJOINT1; eauto. i. des. *)
    (*     exploit Memory.get_ts; try exact GETP. i. des. *)
    (*     { subst. ss. } *)
    (*     apply (H0 to); econs; ss; refl. *)
    (*   - inv LOCAL1. inv STEP. inv LOCAL2. inv STEP. inv WRITE. *)
    (*     exploit Memory.promise_disjoint; try eapply WF; try eapply DISJOINT2; eauto. i. des. *)
    (*     exploit Memory.promise_get0; eauto; try by (inv PROMISE; ss). i. des. *)
    (*     destruct (Memory.get loc to (Local.promises lc)) as [[]|] eqn:GETP; ss. *)
    (*     exfalso. *)
    (*     exploit MemoryFacts.promise_time_lt; eauto; try by (inv PROMISE; ss). i. *)
    (*     inv DISJOINT0. hexploit DISJOINT1; eauto. i. des. *)
    (*     exploit Memory.get_ts; try exact GETP. i. des. *)
    (*     { subst. ss. } *)
    (*     apply (H0 to); econs; ss; refl. *)
    (* Qed. *)

    (* Lemma step_get_None *)
    (*       e tid rels1 rels2 c1 c2 *)
    (*       loc from to msg *)
    (*       (STEP: step e tid rels1 rels2 c1 c2) *)
    (*       (PROMISES1: forall tid lang st lc *)
    (*                    (FIND: IdentMap.find tid (Configuration.threads c1) = Some (existT _ lang st, lc)), *)
    (*           Memory.get loc to (Local.promises lc) = None) *)
    (*       (MEM1: Memory.get loc to (Configuration.memory c1) = Some (from, msg)): *)
    (*   (<<PROMISES2: forall tid lang st lc *)
    (*                  (FIND: IdentMap.find tid (Configuration.threads c2) = Some (existT _ lang st, lc)), *)
    (*       Memory.get loc to (Local.promises lc) = None>>) /\ *)
    (*   (<<MEM2: Memory.get loc to (Configuration.memory c2) = Some (from, msg)>>) /\ *)
    (*   (<<EVENT: forall from' val released ord, ThreadEvent.is_writing e <> Some (loc, from', to, val, released, ord)>>). *)
    (* Proof. *)
    (*   inv STEP. ss. *)
    (*   exploit PROMISES1; eauto. i. *)
    (*   exploit WThread.cancel_steps_get_None; eauto. i. des. *)
    (*   exploit WThread.opt_step_get_None; eauto. i. des. *)
    (*   exploit WThread.reserve_steps_get_None; eauto. i. des. *)
    (*   splits; eauto. i. *)
    (*   revert FIND. rewrite IdentMap.gsspec. condtac; eauto. i. inv FIND. ss. *)
    (* Qed. *)

    (* Lemma steps_rels *)
    (*       rels1 rels2 c1 c2 *)
    (*       loc from to msg *)
    (*       (STEPS: steps rels1 rels2 c1 c2) *)
    (*       (PROMISES1: forall tid lang st lc *)
    (*                    (FIND: IdentMap.find tid (Configuration.threads c1) = Some (existT _ lang st, lc)), *)
    (*           Memory.get loc to (Local.promises lc) = None) *)
    (*       (MEM1: Memory.get loc to (Configuration.memory c1) = Some (from, msg)) *)
    (*       (RELS1: ~ List.In (loc, to) rels1): *)
    (*   ~ List.In (loc, to) rels2. *)
    (* Proof. *)
    (*   induction STEPS; ss. *)
    (*   exploit step_get_None; eauto. i. des. *)
    (*   eapply IHSTEPS; eauto. *)
    (*   ii. inv STEP. ss. inv STEP0; ss. inv STEP. *)
    (*   unfold Writes.append in H. des_ifs. inv H; ss. inv H0. *)
    (*   eapply EVENT; eauto. *)
    (* Qed. *)

    (* Lemma write_rels *)
    (*       e tid rels1 rels2 c1 c2 *)
    (*       loc from to val released ord *)
    (*       (WF1: Configuration.wf c1) *)
    (*       (RELS1: forall tid lang st lc *)
    (*                 (TH: IdentMap.find tid (Configuration.threads c1) = Some (existT _ lang st, lc)), *)
    (*           Writes.wf L rels1 (Local.promises lc) (Configuration.memory c1)) *)
    (*       (STEP: step e tid rels1 rels2 c1 c2) *)
    (*       (WRITE: ThreadEvent.is_writing e = Some (loc, from, to, val, released, ord)): *)
    (*   ~ List.In (loc, to) rels1. *)
    (* Proof. *)
    (*   ii. inv STEP. inv STEP0; ss. *)
    (*   hexploit RELS1; eauto. i. *)
    (*   hexploit (@WThread.steps_writes_wf lang L ordcr ordcw); *)
    (*     try eapply WThread.tau_steps_steps; *)
    (*     try eapply WThread.cancel_steps_tau_steps; eauto; ss; eauto. i. *)
    (*   inv STEP. inv STEP0; inv STEP; inv LOCAL; ss. *)
    (*   - inv LOCAL0. inv STEP. inv WRITE0. *)
    (*     exploit WThread.promise_writes_wf; eauto. i. des. *)
    (*     exploit Memory.promise_get0; eauto; try by (inv PROMISE; ss). i. des. *)
    (*     congr. *)
    (*   - inv LOCAL1. inv STEP. inv LOCAL2. inv STEP. inv WRITE0. ss. *)
    (*     exploit WThread.promise_writes_wf; eauto. i. des. *)
    (*     exploit Memory.promise_get0; eauto; try by (inv PROMISE; ss). i. des. *)
    (*     congr. *)
    (* Qed. *)


    (* reserve_only *)

    (* Definition reserve_only (c: Configuration.t): Prop := *)
    (*   forall tid lang st lc *)
    (*     (FIND: IdentMap.find tid (Configuration.threads c) = Some (existT _ lang st, lc)), *)
    (*     WThread.reserve_only L (Local.promises lc). *)

    (* Lemma init_reserve_only s: *)
    (*   reserve_only (Configuration.init s). *)
    (* Proof. *)
    (*   ii. unfold Configuration.init, Threads.init in *. ss. *)
    (*   rewrite IdentMap.Facts.map_o in *. *)
    (*   destruct (@UsualFMapPositive.UsualPositiveMap'.find *)
    (*               (@sigT _ (@Language.syntax ProgramEvent.t)) tid s); inv FIND. *)
    (*   ss. rewrite Memory.bot_get in *. ss. *)
    (* Qed. *)

    (* Lemma step_reserve_only *)
    (*       tid e rels1 rels2 c1 c2 *)
    (*       (RESERVE: reserve_only c1) *)
    (*       (STEP: step tid e rels1 rels2 c1 c2): *)
    (*   reserve_only c2. *)
    (* Proof. *)
    (*   inv STEP. ii. ss. *)
    (*   revert FIND. rewrite IdentMap.gsspec. condtac; ss; i; cycle 1. *)
    (*   { eapply RESERVE; eauto. } *)
    (*   inv FIND. apply inj_pair2 in H1. subst. *)
    (*   unfold reserve_only in RESERVE. *)
    (*   hexploit RESERVE; eauto. i. *)
    (*   hexploit WThread.cancel_steps_reserve_only; try exact CANCELS; eauto. i. des. *)
    (*   hexploit WThread.opt_step_reserve_only; try exact STEP0; eauto. i. *)
    (*   hexploit WThread.reserve_steps_reserve_only; try exact RESERVES; eauto. *)
    (* Qed. *)

    (* Lemma steps_reserve_only *)
    (*       rels1 rels2 c1 c2 *)
    (*       (RESERVE: reserve_only c1) *)
    (*       (STEPS: steps rels1 rels2 c1 c2): *)
    (*   reserve_only c2. *)
    (* Proof. *)
    (*   induction STEPS; ss. *)
    (*   hexploit step_reserve_only; eauto. *)
    (* Qed. *)

    Lemma step_rels_incl
          e tid rels1 rels2 c1 c2
          (STEP: step e tid rels1 rels2 c1 c2):
      rels2 = rels1 \/ exists a, rels2 = a :: rels1.
    Proof.
      inv STEP. inv STEP0; eauto. inv STEP.
      unfold Writes.append. des_ifs; eauto.
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

    (* Lemma step_non_concrete *)
    (*       e tid rels1 rels2 c1 c2 loc to *)
    (*       (STEP: step e tid rels1 rels2 c1 c2) *)
    (*       (LOC: L loc) *)
    (*       (EVENT: forall from val released ord, *)
    (*           ThreadEvent.is_writing e <> Some (loc, from, to, val, released, ord)) *)
    (*       (GET1: forall from msg (GET: Memory.get loc to (Configuration.memory c1) = Some (from, msg)), *)
    (*           msg = Message.reserve): *)
    (*   <<GET2: forall from msg (GET: Memory.get loc to (Configuration.memory c2) = Some (from, msg)), *)
    (*       msg = Message.reserve>>. *)
    (* Proof. *)
    (*   inv STEP. ss. *)
    (*   hexploit WThread.cancel_steps_non_concrete; eauto. i. des. *)
    (*   hexploit WThread.opt_step_non_concrete; eauto. i. des. *)
    (*   hexploit WThread.reserve_steps_non_concrete; eauto. *)
    (* Qed. *)
  End WConfiguration.
End WConfiguration.


Module RARaceW.
  Section RARaceW.
    Variable L: Loc.t -> bool.
    Variable ordcr ordcw: Ordering.t.

    Definition wr_race (rels: Writes.t) (tview: TView.t) (loc: Loc.t) (ord: Ordering.t): Prop :=
      exists to ordw,
        (<<LOC: L loc>>) /\
        (<<HIGHER: Time.lt ((View.rlx (TView.cur tview)) loc) to>>) /\
        (<<IN: List.In (loc, to, ordw) rels>>) /\
        ((<<ORDW: Ordering.le ordw Ordering.strong_relaxed>>) \/
         (<<ORDR: Ordering.le ord Ordering.strong_relaxed>>)).

    Definition ww_race (rels: Writes.t) (tview: TView.t) (loc: Loc.t) (ord: Ordering.t): Prop :=
      exists to ordw,
        (<<LOC: L loc>>) /\
        (<<HIGHER: Time.lt ((View.rlx (TView.cur tview)) loc) to>>) /\
        (<<IN: List.In (loc, to, ordw) rels>>) /\
        ((<<ORDW1: Ordering.le ordw Ordering.na>>) \/
         (<<ORDW2: Ordering.le ord Ordering.na>>)).

    Definition ra_race (rels: Writes.t) (tview: TView.t) (e: ProgramEvent.t): Prop :=
      (exists loc val ord,
          (<<READ: ProgramEvent.is_reading e = Some (loc, val, ord)>>) /\
          (<<WRRACE: wr_race rels tview loc ord>>)) \/
      (exists loc val ord,
          (<<WRITE: ProgramEvent.is_writing e = Some (loc, val, ord)>>) /\
          (<<WWRACE: ww_race rels tview loc ord>>)).

    Definition ra_race_steps (rels: Writes.t) (c: Configuration.t): Prop :=
      exists tid rels2 rels3 c2 lang st2 lc2 e e3 st4,
        (<<STEPS: WConfiguration.steps L ordcr ordcw rels rels2 c c2>>) /\
        (<<TID: IdentMap.find tid (Configuration.threads c2) = Some (existT _ lang st2, lc2)>>) /\
        (<<THREAD_STEPS: WThread.steps L ordcr ordcw rels2 rels3
                                       (Thread.mk _ st2 lc2 (Configuration.sc c2) (Configuration.memory c2)) e3>>) /\
        (<<CONS: Local.promise_consistent (Thread.local e3)>>) /\
        (<<THREAD_STEP: lang.(Language.step) e e3.(Thread.state) st4>>) /\
        (<<RARACE: ra_race rels3 (Local.tview (Thread.local e3)) e>>).

    Definition racefree (rels: Writes.t) (c: Configuration.t): Prop :=
      forall tid rels2 rels3 c2 lang st2 lc2 e e3 st4
        (STEPS: WConfiguration.steps L ordcr ordcw rels rels2 c c2)
        (TID: IdentMap.find tid (Configuration.threads c2) = Some (existT _ lang st2, lc2))
        (THREAD_STEPS: WThread.steps L ordcr ordcw rels2 rels3
                                       (Thread.mk _ st2 lc2 (Configuration.sc c2) (Configuration.memory c2)) e3)
        (CONS: Local.promise_consistent (Thread.local e3))
        (THREAD_STEP: lang.(Language.step) e e3.(Thread.state) st4)
        (RARACE: ra_race rels3 (Local.tview (Thread.local e3)) e),
        False.

    Definition racefree_syn (syn: Threads.syntax): Prop :=
      racefree [] (Configuration.init syn).

    Lemma step_racefree
          e tid rels1 rels2 c1 c2
          (RACEFREE: racefree rels1 c1)
          (STEP: WConfiguration.step L ordcr ordcw e tid rels1 rels2 c1 c2):
      racefree rels2 c2.
    Proof.
      ii. eapply RACEFREE; eauto. econs 2; eauto.
    Qed.

    Lemma step_ord_step
          e tid rels1 rels2 c1 c2
          (STEP: WConfiguration.step L ordcr ordcw e tid rels1 rels2 c1 c2):
      OrdConfiguration.step L ordcr ordcw e tid c1 c2.
    Proof.
      inv STEP. econs; eauto. inv STEP0.
      - econs 1.
      - inv STEP. econs 2. eauto.
    Qed.
  End RARaceW.
End RARaceW.
