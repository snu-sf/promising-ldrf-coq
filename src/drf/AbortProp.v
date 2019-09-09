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

Require Import PF.
Require Import Race.
Require Import Behavior.
Require Import SimMemory.
Require Import yjtac.
Require Import Program.
Require Import Cell.
Require Import Time.
Require Import PredStep.

Set Implicit Arguments.


Inductive added_memory (tm: TimeMap.t): Memory.t -> Memory.t -> Prop :=
| added_memory_intro
    m0 loc to from msg m1
    (TLE: Time.le (tm loc) to) 
    (ADD: Memory.add m0 loc to from msg m1)
  :
    added_memory tm m0 m1
.

(* Lemma thread_consistent_no_sc_no_acq *)

Lemma progressable_in_added_rtc
      lang st lc sc0 sc1 m0 m1 tm
      (CONSISTENT: Thread.consistent (Thread.mk lang st lc sc0 m0))
      (FUTURE: Memory.future m0 m1)
  :
    exists m2 e2,
      (<<ADDED: rtc (added_memory tm) m1 m2>>) /\
      (<<STEPS: rtc (Thread.tau_step (lang:=lang))
                    (Thread.mk _ st lc sc1 m1) e2>>) /\
      (<<PROMISES: Local.promises (Thread.local e2) = Memory.bot>>).
Proof.
Admitted.
