Require Import Omega.
Require Import Bool.
Require Import RelationClasses.
Require Import Program.

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

Require Import Single.
Require Import JoinedView.

Require Import LocalDRFPFView.

Require Import OrdStep.
Require Import Stable.
Require Import WStep.
Require Import PFtoRA.

Set Implicit Arguments.


Module RARace.
Section RARACE.
  Variable L: Loc.t -> bool.

  Definition race (c1: Configuration.t): Prop :=
    exists c2 c3
           tid_w e_w loc from to val released ordw
           tid_r lang st3 lc3 e4 e5
           pf e_r released' ordr,
      (<<WRITE_STEP: OrdConfiguration.step L Ordering.acqrel Ordering.acqrel e_w tid_w c1 c2>>) /\
      (<<WRITE_EVENT: ThreadEvent.is_writing e_w = Some (loc, from, to, val, released, ordw)>>) /\
      (<<STEPS2: rtc (@OrdConfiguration.all_step L Ordering.acqrel Ordering.acqrel) c2 c3>>) /\
      (<<FIND: IdentMap.find tid_r (Configuration.threads c3) = Some (existT _ lang st3, lc3)>>) /\
      (<<THREAD_STEPS: rtc (@OrdThread.all_step _ L Ordering.acqrel Ordering.acqrel)
                           (Thread.mk _ st3 lc3 (Configuration.sc c3) (Configuration.memory c3))
                           e4>>) /\
      (<<CONS: Local.promise_consistent (Thread.local e4)>>) /\
      (<<READ_STEP: OrdThread.step L Ordering.acqrel Ordering.acqrel pf e_r e4 e5>>) /\
      (<<READ_EVENT: ThreadEvent.is_reading e_r = Some (loc, to, val, released', ordr)>>) /\
      (<<LOC: L loc>>) /\
      (<<HIGHER: Time.lt ((Local.tview (Thread.local e4)).(TView.cur).(View.rlx) loc) to>>) /\
      (<<ORDERING: __guard__(Ordering.le ordw Ordering.strong_relaxed \/
                             Ordering.le ordr Ordering.strong_relaxed)>>).

  Definition racefree (c: Configuration.t): Prop :=
    forall c1
           (STEPS1: rtc (@OrdConfiguration.all_step L Ordering.acqrel Ordering.acqrel) c c1),
      ~ race c1.

  Definition racefree_syn (s: Threads.syntax): Prop :=
    racefree (Configuration.init s).

End RARACE.
End RARace.
