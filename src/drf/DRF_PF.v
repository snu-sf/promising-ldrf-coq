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
Require Import PF.
Require Import ADRF_PF.
Require Import APFPF.

Lemma sim_apf_pf_race c_src c_tgt
      (SIM: sim_apf_pf c_src c_tgt)
  :
    pf_race c_src <-> pf_race c_tgt.
Proof.
  inv SIM. split; i.
  - inv H. ss. econs; [eapply TID1|eapply TID2|..]; eauto.
  - inv H. ss. econs; [eapply TID1|eapply TID2|..]; eauto.
Qed.

Lemma sim_apf_pf_racefree c_src c_tgt
      (SIM: sim_apf_pf c_src c_tgt)
      (RACEFREE: PFConfiguration.pf_racefree c_src)
  :
    APFConfiguration.pf_racefree c_tgt.
Proof.
  ii. ginduction STEPS.
  - i. erewrite <- sim_apf_pf_race in RACE; eauto.
  - i. inv H. inv USTEP. exploit sim_apf_pf_step; eauto.
    i. des. eapply IHSTEPS; eauto.
    eapply PFConfiguration.pf_racefree_step; eauto.
Qed.

Lemma drf_pf s
      (RACEFREE: PFConfiguration.pf_racefree (Configuration.init s))
  :
    behaviors Configuration.step (Configuration.init s) <1=
    behaviors PFConfiguration.step (Configuration.init s).
Proof.
  ii. eapply ADRF_PF.drf_pf in PR.
  - eapply apf_pf_equiv; eauto.
  - eapply sim_apf_pf_racefree; eauto.
    eapply sim_apf_pf_init; eauto.
Qed.
