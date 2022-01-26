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

Require Import OrdStep.

Set Implicit Arguments.


Module Writes.
  Section Writes.
    Variable L: Loc.t -> bool.

    Definition t: Type := list (Loc.t * Time.t * Ordering.t).

    Definition append (e: ThreadEvent.t) (rels: t): t :=
      match ThreadEvent.is_writing e with
      | Some (loc, from, to, val, released, ord) =>
        if L loc
        then if Ordering.le Ordering.acqrel ord then (loc, to, ord) :: rels else rels
        else rels
      | None => rels
      end.

    Definition wf (rels: t) (promises mem: Memory.t): Prop :=
      forall loc to ord (IN: List.In (loc, to, ord) rels),
        Memory.get loc to promises = None /\
        exists from val released,
          Memory.get loc to mem = Some (from, Message.concrete val released).

    Lemma append_app e rels1 rels2:
      append e rels1 ++ rels2 = append e (rels1 ++ rels2).
    Proof.
      unfold append. des_ifs.
    Qed.

    Lemma promise_wf
          rels promises1 mem1 loc from to msg promises2 mem2 kind
          (RELS1: wf rels promises1 mem1)
          (PROMISE: Memory.promise promises1 mem1 loc from to msg promises2 mem2 kind):
      wf rels promises2 mem2.
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
      - exploit Memory.lower_get1; try exact x0; eauto. i. des. inv MSG_LE.
        dup GET2. revert GET2. erewrite Memory.lower_o; eauto. condtac; ss.
        + i. des. inv GET2.
          exploit Memory.lower_get0; try exact PROMISES. i. des. congr.
        + guardH o. i. rewrite GET2 in *. inv x0. esplits; eauto.
          erewrite Memory.lower_o; eauto. condtac; ss.
      - erewrite (@Memory.remove_o promises2); eauto.
        erewrite (@Memory.remove_o mem2); eauto. condtac; ss; eauto.
        des. subst. exploit Memory.remove_get0; try exact PROMISES. i. des. congr.
    Qed.

    Lemma write_wf
          rels promises1 mem1 loc from to msg promises2 mem2 kind
          (RELS1: wf rels promises1 mem1)
          (WRITE: Memory.write promises1 mem1 loc from to msg promises2 mem2 kind):
      wf rels promises2 mem2.
    Proof.
      inv WRITE. hexploit promise_wf; eauto. i.
      ii. exploit H; eauto. i. des. esplits; eauto.
      erewrite Memory.remove_o; eauto. condtac; ss.
    Qed.

    Lemma write_wf_incr
          rels promises1 mem1 loc from to msg promises2 mem2 kind ord
          (RELS1: wf rels promises1 mem1)
          (WRITE: Memory.write promises1 mem1 loc from to msg promises2 mem2 kind)
          (MSG: exists val released, msg = Message.concrete val (Some released)):
      wf ((loc, to, ord)::rels) promises2 mem2.
    Proof.
      des. hexploit write_wf; eauto. ii.
      inv IN; eauto. inv H0.
      exploit Memory.write_not_cancel; eauto. i.
      inv WRITE. exploit Memory.promise_get0; eauto. i. des.
      exploit Memory.remove_get0; eauto. i. des.
      esplits; eauto.
    Qed.

    Lemma write_na_wf
          rels ts promises1 mem1 loc from to msg promises2 mem2 msgs kinds kind
          (RELS1: wf rels promises1 mem1)
          (WRITE: Memory.write_na ts promises1 mem1 loc from to msg promises2 mem2 msgs kinds kind):
      wf rels promises2 mem2.
    Proof.
      induction WRITE; eauto using write_wf.
    Qed.

    Lemma step_wf
          ordcr ordcw rels lang pf e e1 e2
          (RELS1: wf rels (Local.promises (Thread.local e1)) (Thread.memory e1))
          (STEP: @OrdThread.step lang L ordcr ordcw pf e e1 e2):
      wf (append e rels) (Local.promises (Thread.local e2)) (Thread.memory e2).
    Proof.
      unfold append.
      inv STEP; inv STEP0; inv LOCAL; try inv LOCAL0; ss.
      - eapply promise_wf; eauto.
      - inv STEP. ss.
      - inv STEP. hexploit write_wf; eauto. i.
        repeat condtac; eauto.
        revert WRITE. unfold TView.write_released.
        condtac; try by destruct ord, ordcw; ss. i.
        hexploit write_wf_incr; try exact WRITE; eauto.
      - inv LOCAL1. inv STEP. inv LOCAL2. inv STEP. ss.
        hexploit write_wf; eauto. i.
        repeat condtac; eauto.
        revert WRITE. unfold TView.write_released.
        condtac; try by destruct ordw, ordcw; ss. i.
        hexploit write_wf_incr; try exact WRITE; eauto.
      - inv STEP. hexploit write_na_wf; eauto. i.
        repeat condtac; eauto.
        destruct ord, ordcw; ss.
    Qed.

    Lemma promise_disjoint
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

    Lemma write_disjoint
          promises1 mem1 loc from to msg promises2 mem2 kind
          promises
          (WRITE: Memory.write promises1 mem1 loc from to msg promises2 mem2 kind)
          (DISJOINT: Memory.disjoint promises1 promises)
          (LE: Memory.le promises mem1):
      Memory.get loc to promises = None.
    Proof.
      inv WRITE. eauto using promise_disjoint.
    Qed.

    Lemma write_na_disjoint
          ts promises1 mem1 loc from to msg promises2 mem2 msgs kinds kind
          promises
          (WRITE: Memory.write_na ts promises1 mem1 loc from to msg promises2 mem2 msgs kinds kind)
          (DISJOINT: Memory.disjoint promises1 promises)
          (LE: Memory.le promises mem1):
      Memory.get loc to promises = None.
    Proof.
      induction WRITE; eauto using write_disjoint.
      exploit Memory.write_disjoint; try exact WRITE_EX; eauto. i. des. eauto.
    Qed.

    Lemma step_disjoint
          ordrc ordwc rels lang pf e e1 e2 promises
          (RELS1: wf rels (Local.promises (Thread.local e1)) (Thread.memory e1))
          (STEP: @OrdThread.step lang L ordrc ordwc pf e e1 e2)
          (DISJOINT: Memory.disjoint (Local.promises (Thread.local e1)) promises)
          (LE: Memory.le promises (Thread.memory e1))
          (RELS: wf rels promises (Thread.memory e1)):
      wf (append e rels) promises (Thread.memory e2).
    Proof.
      hexploit step_wf; eauto. ii.
      exploit H; eauto. i. des. esplits; eauto.
      unfold append in *.
      inv STEP; inv STEP0; inv LOCAL; ss.
      - exploit RELS; eauto. i. des. ss.
      - exploit RELS; eauto. i. des. ss.
      - exploit RELS; eauto. i. des. ss.
      - inv LOCAL0. inv STEP. ss. revert IN.
        repeat condtac; ss; i; des; try by (exploit RELS; eauto; i; des; ss).
        inv IN. eapply write_disjoint; eauto.
      - inv LOCAL1. inv STEP. inv LOCAL2. inv STEP. ss. revert IN.
        repeat condtac; ss; i; des; try by (exploit RELS; eauto; i; des; ss).
        inv IN. eapply write_disjoint; eauto.
      - exploit RELS; eauto. i. des. ss.
      - exploit RELS; eauto. i. des. ss.
      - exploit RELS; eauto. i. des. ss.
      - inv LOCAL0. inv STEP. ss. revert IN.
        repeat condtac; ss; i; des; try by (exploit RELS; eauto; i; des; ss).
        inv IN. eapply write_na_disjoint; eauto.
      - exploit RELS; eauto. i. des. ss.
      - exploit RELS; eauto. i. des. ss.
      - exploit RELS; eauto. i. des. ss.
    Qed.
  End Writes.
End Writes.
