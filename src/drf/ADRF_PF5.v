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
Require Import APromiseConsistent.
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
Require Import ReorderPromises2.

Require Import Pred.
Require Import DRF_PF0.
Require Import DRF_PF1.
Require Import DRF_PF3.
Require Import DRF_PF4.
Require Import Mapping.

Require Import PFConsistent.

Set Implicit Arguments.

Definition tgt_consistent_drf
           lang (e0:Thread.t lang) max
           (


           (space: Loc.t -> Time.t -> Prop)





                                                         Prop :=


  let L := (fun loc => Memory.latest_reserve loc e0.(Thread.local).(Local.promises) e0.(Thread.memory)) in
  forall mem1 max sc
         (FORGET: forget_memory (latest_other_reserves e0.(Thread.local).(Local.promises) e0.(Thread.memory)) mem1 e0.(Thread.memory))
         (MAX: my_max_timemap e0.(Thread.local).(Local.promises) e0.(Thread.memory) max),
  exists e1,
    (<<STEPS0: rtc (tau (@pred_step ((promise_free /1\ no_acq_update_on ((fun loc to => L loc) /2\ Memory.max_full_ts e0.(Thread.memory))) /1\ no_sc /1\ write_in (later_times max \2/ fun loc to => covered loc to e0.(Thread.local).(Local.promises))) lang)) (Thread.mk _ e0.(Thread.state) e0.(Thread.local) sc mem1) e1>>) /\
    (__guard__((<<FAILURE: Local.failure_step e1.(Thread.local)>>) \/
               (<<PROMISES: e1.(Thread.local).(Local.promises) = Memory.bot>>))).
