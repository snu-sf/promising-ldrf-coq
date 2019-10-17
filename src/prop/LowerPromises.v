Require Import Omega.
Require Import RelationClasses.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Loc.

Require Import Event.
Require Import Time.
From PromisingLib Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import MemoryFacts.
Require Import TView.
Require Import Local.
Require Import Thread.

Set Implicit Arguments.


Module LowerPromises.
  Inductive message_rel: forall (msg1 msg2: Message.t), Prop :=
  | message_rel_full
      val released:
      message_rel (Message.full val released) (Message.full val None)
  | message_rel_reserve:
      message_rel Message.reserve Message.reserve
  .
  Hint Constructors message_rel.

  Inductive promises_rel (promises1 promises2: Memory.t): Prop :=
  | promises_rel_intro
      (SOUND: forall loc from to msg1
                (GET1: Memory.get loc to promises1 = Some (from, msg1)),
          exists msg2,
            <<GET2: Memory.get loc to promises2 = Some (from, msg2)>>)
      (COMPLETE: forall loc from to msg2
                   (GET2: Memory.get loc to promises2 = Some (from, msg2)),
          exists msg1,
            <<GET1: Memory.get loc to promises1 = Some (from, msg1)>> /\
            <<MSG: message_rel msg1 msg2>>)
  .

  Inductive promises_rel_aux (dom: list (Loc.t * Time.t)) (promises1 promises2: Memory.t): Prop :=
  | promises_rel_aux_intro
      (SOUND: forall loc from to msg1
                (GET1: Memory.get loc to promises1 = Some (from, msg1)),
          exists msg2,
            <<GET2: Memory.get loc to promises2 = Some (from, msg2)>>)
      (COMPLETE1: forall loc from to msg2
                    (IN: List.In (loc, to) dom)
                    (GET2: Memory.get loc to promises2 = Some (from, msg2)),
          <<GET1: Memory.get loc to promises1 = Some (from, msg2)>>)
      (COMPLETE2: forall loc from to msg2
                    (IN: ~ List.In (loc, to) dom)
                    (GET2: Memory.get loc to promises2 = Some (from, msg2)),
          exists msg1,
            <<GET1: Memory.get loc to promises1 = Some (from, msg1)>> /\
            <<MSG: message_rel msg1 msg2>>)
  .

  Lemma promises_rel_aux_exists
        promises
        (FINITE: Memory.finite promises):
    exists dom, promises_rel_aux dom promises promises.
  Proof.
  Admitted.

  Lemma promises_rel_aux_promises_rel
        promises1 promises2
        (REL: promises_rel_aux [] promises1 promises2):
    promises_rel promises1 promises2.
  Proof.
  Admitted.

  Lemma promises_rel_promises
        promises1 promises2
        (REL: promises_rel promises1 promises2):
    Memory.nonsynch promises2.
  Proof.
    inv REL. ii.
    exploit COMPLETE; eauto. i. des. inv MSG; ss.
  Qed.


  Lemma steps_promises_rel
        lang e1
        (WF1: Local.wf e1.(Thread.local) e1.(Thread.memory))
        (CLOSED1: Memory.closed e1.(Thread.memory)):
    exists e2,
      <<STEPS: rtc (union (@Thread.opt_promise_step lang)) e1 e2>> /\
      <<REL: promises_rel e1.(Thread.local).(Local.promises) e2.(Thread.local).(Local.promises)>>.
  Proof.
    exploit promises_rel_aux_exists; try eapply WF1. i. des.
    revert e1 WF1 CLOSED1 x0.
    induction dom; i.
    { esplits; eauto. apply promises_rel_aux_promises_rel; ss. }
  Admitted.

  Lemma rtc_opt_promise_step_future
        lang e1 e2
        (STEPS: rtc (union (@Thread.opt_promise_step lang)) e1 e2):
    <<STEPS: rtc (@Thread.tau_step lang) e1 e2>> /\
    <<STATE: e1.(Thread.state) = e2.(Thread.state)>> /\
    <<TVIEW: e1.(Thread.local).(Local.tview) = e2.(Thread.local).(Local.tview)>>.
  Proof.
    induction STEPS; try by (splits; eauto). des.
    inv H. inv USTEP; eauto. splits.
    - econs 2; [|eauto].
      econs; [econs; econs; eauto|].
      inv STEP. ss.
    - rewrite <- STATE. inv STEP. ss.
    - rewrite <- TVIEW. inv STEP. inv LOCAL. ss.
  Qed.
End LowerPromises.
