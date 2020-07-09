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
Require Import Behavior.

Require Import JoinedView.

Require Import LocalPFView.

Require Import OrdStep.
Require Import Stable.
Require Import RARace.
Require Import PFtoRASimThread.
Require Import PFtoRA.

Set Implicit Arguments.


Theorem local_drf_ra
        L s
        (RACEFREE: RARace.racefree_syn L s):
  behaviors Configuration.step (Configuration.init s) <1=
  behaviors (@OrdConfiguration.step L Ordering.acqrel) (Configuration.init s).
Proof.
  i.
  specialize (PFtoRA.init_sim_conf L s). intro SIM.
  specialize (PFtoRA.init_wf_pf s). intro WF_PF.
  specialize (PFtoRA.init_wf_j s). intro WF_J.
  specialize (PFtoRA.init_wf_ra s). intro WF_RA.
  ii. exploit (@local_DRFPF L); eauto.
  { eapply PFtoRA.sim_conf_racefree; eauto. }
  eapply PFtoRA.sim_conf_behavior; eauto.
Qed.
