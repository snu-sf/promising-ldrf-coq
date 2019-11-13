Require Import Omega.
Require Import RelationClasses.

From Paco Require Import paco.
From sflib Require Import sflib.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
Require Import Time.
Require Import Event.
From PromisingLib Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import Cover.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.
Require Import Progress.
Require Import PromiseConsistent.
From PromisingLib Require Import Loc.

Require Import AMemory.
Require Import ALocal.
Require Import AThread.

Lemma promise_apromise
  :
    Memory.promise <9= AMemory.promise.
Proof.
  i. inv PR; econs; eauto.
Qed.

Lemma write_awrite
  :
    Memory.write <10= AMemory.write.
Proof.
  i. inv PR; econs; eauto.
  eapply promise_apromise; eauto.
Qed.

Lemma thread_step_athread_step
  :
    Thread.step_allpf <4= AThread.step_allpf.
Proof.
  i. inv PR. inv STEP.
  - inv STEP0. inv LOCAL. econs; eauto. econs; eauto.
    econs; eauto. econs; eauto. eapply promise_apromise; eauto.
  - inv STEP0. inv LOCAL.
    + econs; eauto. econs 2; eauto. econs; eauto.
    + econs; eauto. econs 2; eauto. econs; eauto.
    + inv LOCAL0. econs; eauto. econs 2; eauto. econs; eauto.
      econs; eauto. econs; eauto. eapply write_awrite; eauto.
    + inv LOCAL2. econs; eauto. econs 2; eauto. econs; eauto.
      econs; eauto. econs; eauto. eapply write_awrite; eauto.
    + econs; eauto. econs 2; eauto. econs; eauto.
    + econs; eauto. econs 2; eauto. econs; eauto.
    + econs; eauto. econs 2; eauto. econs; eauto.
Qed.
