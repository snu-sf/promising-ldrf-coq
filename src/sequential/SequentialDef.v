Require Import Bool.
Require Import RelationClasses.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Language.
From PromisingLib Require Import Loc.

Require Import Event.

Set Implicit Arguments.

Module Perm.
  Variant t :=
  | none
  | full
  .
End Perm.

Definition Perms := Loc.t -> Perm.t.
Definition flag := bool.

Definition SMemory := Loc.t -> Const.t * flag.

Definition Oracle: Type. Admitted.

Module State.
Section LANG.
  Variable lang: language.

  Record t :=
    mk {
        state: lang.(Language.state);
        memory: SMemory;
        perm: Perms;
        oracle: Oracle;
      }.

  Variant na_step: t -> t -> Prop :=
  | na_step_silent
      st0 st1
      (STEP: lang.(Language.step) ProgramEvent.silent st0 st1)
      m p o
    :
      na_step (mk st0 m p o) (mk st1 m p o)
  | na_step_silent
      st0 st1
      (STEP: lang.(Language.step) ProgramEvent.silent st0 st1)
      m p o
    :
      na_step (mk st0 m p o) (mk st1 m p o)
  .

ProgramEvent.t



Definition update_mem :=

Module Memory.
  Definition t := Loc.t -> Cell.t.


Memory.t

Variant mem_permission

ProgramEvent.t
