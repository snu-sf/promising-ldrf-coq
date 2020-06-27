Require Import RelationClasses.

From Paco Require Import paco.
From sflib Require Import sflib.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import Language.
From PromisingLib Require Import Loc.
Require Import Time.
Require Import Event.
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
Require Import Cover.
Require Import Pred.
Require Import Trace.

Require Import MemoryProps.

Set Implicit Arguments.




Section LOCALDRF.

  Variable L: Loc.t -> bool.

  Definition pf_event (e: ThreadEvent.t): Prop :=
    forall loc from to msg kind (PROMISE: e = ThreadEvent.promise loc from to msg kind) (LOC: L loc),
      msg = Message.reserve.

  Definition pf_step (e: MachineEvent.t) (tid: Ident.t)
             (c0 c1: Configuration.t): Prop :=
    exists tr,
      (<<STEP: @Trace.configuration_step tr e tid c0 c1>>) /\
      (<<PF: List.Forall (compose pf_event snd) tr>>).

  Inductive configuration_steps_trace:
    forall (c0 c1: Configuration.t) (tr: Trace.t), Prop :=
  | configuration_steps_trace_nil
      c0
    :
      configuration_steps_trace c0 c0 []
  | configuration_steps_trace_cons
      c0 c1 c2 trs tr e tid
      (STEPS: configuration_steps_trace c1 c2 trs)
      (STEP: @Trace.configuration_step tr e tid c0 c1)
      (PF: List.Forall (compose pf_event snd) tr)
    :
      configuration_steps_trace c0 c2 (tr ++ trs)
  .

  Lemma configuration_steps_trace_n1 c0 c1 c2 tr trs e tid
        (STEPS: configuration_steps_trace c0 c1 trs)
        (STEP: @Trace.configuration_step tr e tid c1 c2)
        (PF: List.Forall (compose pf_event snd) tr)
    :
      configuration_steps_trace c0 c2 (trs ++ tr).
  Proof.
    ginduction STEPS.
    { i. exploit configuration_steps_trace_cons.
      { econs 1. }
      { eapply STEP. }
      { auto. }
      { i. ss. erewrite List.app_nil_r in *. auto. }
    }
    { i. exploit IHSTEPS; eauto. i. erewrite <- List.app_assoc. econs; eauto. }
  Qed.

  Lemma configuration_steps_trace_trans c0 c1 c2 trs0 trs1
        (STEPS0: configuration_steps_trace c0 c1 trs0)
        (STEPS1: configuration_steps_trace c1 c2 trs1)
    :
      configuration_steps_trace c0 c2 (trs0 ++ trs1).
  Proof.
    ginduction STEPS0.
    { i. erewrite List.app_nil_l. eauto. }
    { i. exploit IHSTEPS0; eauto. i. erewrite <- List.app_assoc. econs; eauto. }
  Qed.

  Inductive silent_configuration_steps_trace:
    forall (c0 c1: Configuration.t) (tr: Trace.t), Prop :=
  | silent_configuration_steps_trace_nil
      c0
    :
      silent_configuration_steps_trace c0 c0 []
  | silent_configuration_steps_trace_cons
      c0 c1 c2 trs tr tid
      (STEPS: silent_configuration_steps_trace c1 c2 trs)
      (STEP: @Trace.configuration_step tr MachineEvent.silent tid c0 c1)
      (PF: List.Forall (compose pf_event snd) tr)
    :
      silent_configuration_steps_trace c0 c2 (tr ++ trs)
  .

  Lemma silent_configuration_steps_trace_configuration_steps_trace
    :
      silent_configuration_steps_trace <3= configuration_steps_trace.
  Proof.
    intros. induction PR.
    { econs. }
    { econs; eauto. }
  Qed.

  Lemma silent_configuration_steps_trace_behaviors c0 c1 tr
        (STEP: silent_configuration_steps_trace c0 c1 tr)
    :
      behaviors pf_step c1 <1= behaviors pf_step c0.
  Proof.
    ginduction STEP; auto.
    i. eapply IHSTEP in PR. econs 4; eauto.
    econs. esplits; eauto.
  Qed.

  Inductive racy_read (loc: Loc.t) (ts: Time.t):
    forall (lc: Local.t) (e: ThreadEvent.t), Prop :=
  | racy_read_read
      lc
      valr releasedr ordr
      (VIEW:
         if Ordering.le Ordering.relaxed ordr
         then Time.lt (lc.(Local.tview).(TView.cur).(View.rlx) loc) ts
         else Time.lt (lc.(Local.tview).(TView.cur).(View.pln) loc) ts)
    :
      racy_read loc ts lc (ThreadEvent.read loc ts valr releasedr ordr)
  | racy_read_update
      lc
      to valr valw releasedr releasedw ordr ordw
      (VIEW:
         if Ordering.le Ordering.relaxed ordr
         then Time.lt (lc.(Local.tview).(TView.cur).(View.rlx) loc) ts
         else Time.lt (lc.(Local.tview).(TView.cur).(View.pln) loc) ts)
    :
      racy_read loc ts lc (ThreadEvent.update loc ts to valr valw releasedr releasedw ordr ordw)
  .

  Inductive racy_write (loc: Loc.t) (ts: Time.t):
    forall (lc: Local.t) (e: ThreadEvent.t), Prop :=
  | racy_write_write
      lc
      from valw releasedw ordw
      (ORD: Ordering.le ordw Ordering.relaxed)
    :
      racy_write loc ts lc (ThreadEvent.write loc from ts valw releasedw ordw)
  | racy_write_update
      lc
      from valr valw releasedr releasedw ordr ordw
      (ORD: Ordering.le ordw Ordering.relaxed)
    :
      racy_write loc ts lc (ThreadEvent.update loc from ts valr valw releasedr releasedw ordr ordw)
  .

  Definition racefree (c0: Configuration.t): Prop :=
    forall c1 trs
           loc ts lc0 lc1 e0 e1
           (CSTEPS: configuration_steps_trace c0 c1 trs)
           (TRACE0: List.In (lc0, e0) trs)
           (TRACE1: List.In (lc1, e1) trs)
           (WRITE: racy_write loc ts lc0 e0)
           (READ: racy_read loc ts lc1 e1),
      False.

  Lemma step_racefree c0 c1 tr e tid
        (RACEFREE: racefree c0)
        (STEP: @Trace.configuration_step tr e tid c0 c1)
        (PF: List.Forall (compose pf_event snd) tr)
    :
      racefree c1.
  Proof.
    ii. eapply RACEFREE.
    { econs 2; eauto. }
    { eapply List.in_or_app. right. eapply TRACE0. }
    { eapply List.in_or_app. right. eapply TRACE1. }
    { eauto. }
    { eauto. }
  Qed.

  Lemma steps_racefree c0 c1 trs
        (RACEFREE: racefree c0)
        (STEP: configuration_steps_trace c0 c1 trs)
    :
      racefree c1.
  Proof.
    ii. eapply RACEFREE.
    { eapply configuration_steps_trace_trans; eauto. }
    { eapply List.in_or_app. right. eapply TRACE0. }
    { eapply List.in_or_app. right. eapply TRACE1. }
    { eauto. }
    { eauto. }
  Qed.

  Lemma racefree_write_read c0 c1 c2 trs0 trs1
        loc ts lc0 lc1 e0 e1
        (RACEFREE: racefree c0)
        (STEPS0: configuration_steps_trace c0 c1 trs0)
        (STEPS1: configuration_steps_trace c1 c2 trs1)
        (TRACE0: List.In (lc0, e0) trs0)
        (TRACE1: List.In (lc1, e1) trs1)
        (WRITE: racy_write loc ts lc0 e0)
        (READ: racy_read loc ts lc1 e1)
    :
      False.
  Proof.
    eapply RACEFREE.
    { eapply configuration_steps_trace_trans; eauto. }
    { eapply List.in_or_app. left. eapply TRACE0. }
    { eapply List.in_or_app. right. eapply TRACE1. }
    { eauto. }
    { eauto. }
  Qed.

  Theorem local_DRF_PF s
          (RACEFRFEE: racefree (Configuration.init s))
    :
      behaviors Configuration.step (Configuration.init s) <1=
      behaviors pf_step (Configuration.init s).
  Admitted.

End LOCALDRF.
