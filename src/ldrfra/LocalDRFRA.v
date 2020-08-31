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

Require Import Single.
Require Import JoinedView.

Require Import LocalPFView.

Require Import OrdStep.
Require Import Stable.
Require Import RARace.
Require Import PFtoRASimThread.
Require Import PFtoRA.

Set Implicit Arguments.


Section LocalDRFRA.
  Variable L: Loc.t -> bool.

  Definition ra_racefree (c: Configuration.t): Prop :=
    forall c1 c2 c3
      tid_w e_w loc from to val released ordw
      tid_r lang st3 lc3 e4 e5
      pf e_r releasedr ordr
      (STEPS1: rtc (@OrdConfiguration.all_step L Ordering.acqrel) c c1)
      (WRITE_STEP: OrdConfiguration.step L Ordering.acqrel e_w tid_w c1 c2)
      (WRITE_EVENT: ThreadEvent.is_writing e_w = Some (loc, from, to, val, released, ordw))
      (STEPS2: rtc (@OrdConfiguration.all_step L Ordering.acqrel) c2 c3)
      (FIND: IdentMap.find tid_r c3.(Configuration.threads) = Some (existT _ lang st3, lc3))
      (THREAD_STEPS: rtc (@OrdThread.all_step _ L Ordering.acqrel)
                         (Thread.mk _ st3 lc3 c3.(Configuration.sc) c3.(Configuration.memory))
                         e4)
      (CONS: Local.promise_consistent e4.(Thread.local))
      (READ_STEP: OrdThread.step L Ordering.acqrel pf e_r e4 e5)
      (READ_EVENT: ThreadEvent.is_reading e_r = Some (loc, to, val, releasedr, ordr))
      (LOC: L loc)
      (HIGHER: Time.lt (e4.(Thread.local).(Local.tview).(TView.cur).(View.rlx) loc) to)
      (ORDERING: Ordering.le ordw Ordering.strong_relaxed \/
                 Ordering.le ordr Ordering.strong_relaxed),
      False.

  Definition ra_racefree_syn (s: Threads.syntax): Prop :=
    ra_racefree (Configuration.init s).

  Lemma racefree_implies
        s
        (RACEFREE: ra_racefree_syn s):
    RARace.racefree_syn L s.
  Proof.
  Admitted.

  Theorem local_drf_ra
          s
          (RACEFREE: ra_racefree_syn s):
    behaviors SConfiguration.machine_step (Configuration.init s) <1=
    behaviors (@OrdConfiguration.machine_step L Ordering.acqrel) (Configuration.init s).
  Proof.
    hexploit racefree_implies; eauto. i.
    specialize (PFtoRA.init_sim_conf L s). intro SIM.
    specialize (PFtoRA.init_wf_pf L s). intro WF_PF.
    specialize (PFtoRA.init_wf_j s). intro WF_J.
    specialize (PFtoRA.init_wf_ra s). intro WF_RA.
    ii. exploit (@local_DRFPF_view L); eauto.
    { eapply PFtoRA.sim_conf_racefree; eauto. }
    eapply PFtoRA.sim_conf_behavior; eauto.
  Qed.
End LocalDRFRA.
