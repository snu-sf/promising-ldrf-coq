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
Require Import MemoryFacts.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.
Require Import Progress.
Require Import Behavior.

Require Import AMemory.
Require Import ALocal.
Require Import AThread.
Require Import Race.

Require Import APF.
Require Import APFSingle.
Require Import ADRF_PF.

Lemma sim_apf_pf_racefree c
      (RACEFREE: APFSingle.pf_racefree c)
  :
    APF.pf_racefree c.
Proof.
  ii. ginduction STEPS; i.
  - eapply RACEFREE; eauto.
  - inv H. inv USTEP. exploit pftstep_single_sim; eauto. i. des.
    eapply IHSTEPS; auto. ii. eapply RACEFREE; cycle 1; eauto. etrans.
    + eapply rtc_implies; try apply STEPS0. i. inv PR. econs; eauto.
    + econs; eauto.
Qed.

Lemma drf_pf s
      (RACEFREE: APFSingle.pf_racefree (Configuration.init s))
  :
    behaviors Configuration.step (Configuration.init s) <1=
    behaviors pftstep_single (Configuration.init s).
Proof.
  ii. eapply pftstep_equiv.
  eapply ADRF_PF.drf_pf; eauto.
  eapply sim_apf_pf_racefree; eauto.
Qed.
