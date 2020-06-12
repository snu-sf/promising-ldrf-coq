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

Require Import OrdStep.
Require Import Stable.
Require Import RARace.
Require Import RASimThread.

Set Implicit Arguments.


Theorem local_drf_ra
        L s
        (RACEFREE: RARace.racefree L s):
  behaviors Configuration.step (Configuration.init s) <1=
  behaviors (@OrdConfiguration.step L Ordering.acqrel) (Configuration.init s).
Proof.
Admitted.
