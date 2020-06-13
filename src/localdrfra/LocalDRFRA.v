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

(* TODO: rename *)
Require Import LocalDRF_PF.

Require Import OrdStep.
Require Import Stable.
Require Import RARace.
Require Import PFtoRASimThread.

Set Implicit Arguments.


Theorem local_drf_ra
        L s
        (RACEFREE: RARace.racefree L s):
  behaviors Configuration.step (Configuration.init s) <1=
  behaviors (@OrdConfiguration.step L Ordering.acqrel) (Configuration.init s).
Proof.
  ii. exploit (@local_DRF_PF L); eauto.
  { ii.
    admit.
  }

  (* ii. clear PR. *)
  (* remember (Configuration.init s) as c_tgt in x1. *)
  (* remember (Configuration.init s) as c_src. *)
  (* assert (exists rels, RATrace.configuration_steps L rels (Configuration.init s) c_src) by admit. des. *)
  (* clear Heqc_src Heqc_tgt. *)
  (* revert c_src rels H. induction x1. *)
  (* - admit. *)
  (* - i. *)
  (* Require Import Program. *)
  (* dependent induction x1. *)
  (* - admit. *)
  (* -  *)
Admitted.
