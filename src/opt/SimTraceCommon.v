From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import Language.

Require Import Event.
Require Import Time.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.

Set Implicit Arguments.


Definition lang_steps_failure [lang] (st1: Language.state lang): Prop :=
  exists st2 st3,
    <<STEPS: rtc ((Language.step lang) ProgramEvent.silent) st1 st2>> /\
    <<FAILURE: (Language.step lang) ProgramEvent.failure st2 st3>>.

Lemma rtc_lang_tau_step_rtc_thread_tau_step lang
      st1 st2 lc sc mem
      (STEP: rtc ((Language.step lang) ProgramEvent.silent) st1 st2):
  rtc (@Thread.tau_step lang) (Thread.mk lang st1 lc sc mem) (Thread.mk lang st2 lc sc mem).
Proof.
  induction STEP.
  - econs 1.
  - econs 2; eauto. econs.
    + econs. econs 2. econs; [|econs 1]; eauto.
    + ss.
Qed.
