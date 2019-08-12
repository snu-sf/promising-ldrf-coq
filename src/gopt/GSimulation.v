From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import Loc.
From PromisingLib Require Import Language.

Require Import Event.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Thread.
Require Import Configuration.
Require Import Behavior.

Set Implicit Arguments.


Section Simulation.
  Definition SIM := forall (c1_src c1_tgt: Configuration.t), Prop.

  Inductive _sim (sim: SIM) (c1_src c1_tgt:Configuration.t): Prop :=
  | _sim_intro
      (TERMINAL:
         forall (TERMINAL_TGT: Threads.is_terminal c1_tgt.(Configuration.threads)),
           <<TERMINAL_SRC: Threads.is_terminal c1_src.(Configuration.threads)>>)
      (STEP:
         forall e tid c3_tgt
           (STEP_TGT: Configuration.step e tid c1_tgt c3_tgt),
           <<ABORT: Configuration.steps_abort c1_src>> \/
         exists c2_src c3_src,
           <<STEPS_SRC: rtc Configuration.tau_step c1_src c2_src>> /\
           <<STEP_SRC: Configuration.opt_step e tid c2_src c3_src>> /\
           <<SIM: sim c3_src c3_tgt>>)
  .

  Lemma _sim_mon: monotone2 _sim.
  Proof.
    ii. inv IN. econs; eauto. i.
    exploit STEP; eauto. i. des; eauto.
    right. esplits; eauto.
  Qed.
  Hint Resolve _sim_mon: paco.

  Definition sim: SIM := paco2 _sim bot2.
End Simulation.
Hint Resolve _sim_mon: paco.


Lemma sim_adequacy
      c_src c_tgt
      (SIM: sim c_src c_tgt):
  behaviors Configuration.step c_tgt <1= behaviors Configuration.step c_src.
Proof.
  i. revert c_src SIM.
  induction PR; i.
  - punfold SIM0. inv SIM0. hexploit TERMINAL0; eauto. i. des.
    econs 1. eauto.
  - punfold SIM0. inv SIM0. exploit STEP0; eauto. i. des.
    + inv ABORT. des.
      eapply rtc_tau_step_behavior; eauto.
      econs 3; eauto.
    + inv SIM0; ss.
      eapply rtc_tau_step_behavior; eauto.
      inv STEP_SRC. econs 2; eauto.
  - punfold SIM0. inv SIM0. exploit STEP0; eauto. i. des.
    + inv ABORT. des.
      eapply rtc_tau_step_behavior; eauto.
      econs 3; eauto.
    + inv SIM0; ss.
      eapply rtc_tau_step_behavior; eauto.
      inv STEP_SRC; eauto. econs 3; eauto.
  - punfold SIM0. inv SIM0. exploit STEP0; eauto. i. des.
    + inv ABORT. des.
      eapply rtc_tau_step_behavior; eauto.
      econs 3; eauto.
    + inv SIM0; ss.
      eapply rtc_tau_step_behavior; eauto.
      inv STEP_SRC; eauto. econs 4; eauto.
Qed.
