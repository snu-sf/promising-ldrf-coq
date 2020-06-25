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
    exists lang tr,
      (<<STEP: @Trace.configuration_step lang tr e tid c0 c1>>) /\
      (<<PF: List.Forall (compose pf_event snd) tr>>).

  Inductive configuration_steps_trace:
    forall (c0 c1: Configuration.t) (tr: list (Ident.t * sigT Trace.t)), Prop :=
  | configuration_steps_trace_nil
      c0
    :
      configuration_steps_trace c0 c0 []
  | configuration_steps_trace_cons
      c0 c1 c2 trs lang tr e tid
      (STEPS: configuration_steps_trace c1 c2 trs)
      (STEP: @Trace.configuration_step lang tr e tid c0 c1)
      (PF: List.Forall (compose pf_event snd) tr)
    :
      configuration_steps_trace c0 c2 ((tid, existT _ _ tr) :: trs)
  .

  Lemma configuration_steps_trace_n1 c0 c1 c2 lang tr trs e tid
        (STEPS: configuration_steps_trace c0 c1 trs)
        (STEP: @Trace.configuration_step lang tr e tid c1 c2)
        (PF: List.Forall (compose pf_event snd) tr)
    :
      configuration_steps_trace c0 c2 (trs ++ [(tid, existT _ _ tr)]).
  Proof.
    ginduction STEPS.
    { i. eapply configuration_steps_trace_cons with (trs:=[]); eauto. econs. }
    { i. exploit IHSTEPS; eauto. i. erewrite <- List.app_comm_cons. econs; eauto. }
  Qed.

  Lemma configuration_steps_trace_trans c0 c1 c2 trs0 trs1
        (STEPS0: configuration_steps_trace c0 c1 trs0)
        (STEPS1: configuration_steps_trace c1 c2 trs1)
    :
      configuration_steps_trace c0 c2 (trs0 ++ trs1).
  Proof.
    ginduction STEPS0.
    { i. erewrite List.app_nil_l. eauto. }
    { i. exploit IHSTEPS0; eauto. i. econs; eauto. }
  Qed.

  Inductive silent_configuration_steps_trace:
    forall (c0 c1: Configuration.t) (tr: list (Ident.t * sigT Trace.t)), Prop :=
  | silent_configuration_steps_trace_nil
      c0
    :
      silent_configuration_steps_trace c0 c0 []
  | silent_configuration_steps_trace_cons
      c0 c1 c2 trs lang tr tid
      (STEPS: silent_configuration_steps_trace c1 c2 trs)
      (STEP: @Trace.configuration_step lang tr MachineEvent.silent tid c0 c1)
      (PF: List.Forall (compose pf_event snd) tr)
    :
      silent_configuration_steps_trace c0 c2 ((tid, existT _ _ tr) :: trs)
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
    forall lang (th: Thread.t lang) (e: ThreadEvent.t), Prop :=
  | racy_read_read
      lang (th: Thread.t lang)
      valr releasedr ordr
      (VIEW:
         if Ordering.le Ordering.relaxed ordr
         then Time.lt (th.(Thread.local).(Local.tview).(TView.cur).(View.rlx) loc) ts
         else Time.lt (th.(Thread.local).(Local.tview).(TView.cur).(View.pln) loc) ts)
    :
      racy_read loc ts th (ThreadEvent.read loc ts valr releasedr ordr)
  | racy_read_update
      lang (th: Thread.t lang)
      to valr valw releasedr releasedw ordr ordw
      (VIEW:
         if Ordering.le Ordering.relaxed ordr
         then Time.lt (th.(Thread.local).(Local.tview).(TView.cur).(View.rlx) loc) ts
         else Time.lt (th.(Thread.local).(Local.tview).(TView.cur).(View.pln) loc) ts)
    :
      racy_read loc ts th (ThreadEvent.update loc ts to valr valw releasedr releasedw ordr ordw)
  .

  Inductive racy_write (loc: Loc.t) (ts: Time.t):
    forall lang (th: Thread.t lang) (e: ThreadEvent.t), Prop :=
  | racy_write_write
      lang (th: Thread.t lang)
      from valw releasedw ordw
      (ORD: Ordering.le ordw Ordering.relaxed)
    :
      racy_write loc ts th (ThreadEvent.write loc from ts valw releasedw ordw)
  | racy_write_update
      lang (th: Thread.t lang)
      from valr valw releasedr releasedw ordr ordw
      (ORD: Ordering.le ordw Ordering.relaxed)
    :
      racy_write loc ts th (ThreadEvent.update loc from ts valr valw releasedr releasedw ordr ordw)
  .

  Definition racefree (c0: Configuration.t): Prop :=
    forall c1 trs
           loc ts
           tid0 tid1 lang0 lang1 tr0 tr1 th0 th1 e0 e1
           (CSTEPS: configuration_steps_trace c0 c1 trs)
           (TRACE0: List.In (tid0, existT _ lang0 tr0) trs)
           (TRACE1: List.In (tid1, existT _ lang1 tr1) trs)
           (EVENT0: List.In (th0, e0) tr0)
           (EVENT1: List.In (th1, e1) tr1)
           (WRITE: racy_write loc ts th0 e0)
           (READ: racy_read loc ts th1 e1),
      False.

  Lemma step_racefree c0 c1 lang tr e tid
        (RACEFREE: racefree c0)
        (STEP: @Trace.configuration_step lang tr e tid c0 c1)
        (PF: List.Forall (compose pf_event snd) tr)
    :
      racefree c1.
  Proof.
    ii. eapply RACEFREE.
    { econs 2; eauto. }
    { ss. right. eapply TRACE0. }
    { ss. right. eapply TRACE1. }
    { eauto. }
    { eauto. }
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
    { eauto. }
    { eauto. }
  Qed.

  Lemma racefree_write_read c0 c1 c2 trs0 trs1
        loc ts tid0 tid1 lang0 lang1 tr0 tr1 th0 th1 e0 e1
        (RACEFREE: racefree c0)
        (STEPS0: configuration_steps_trace c0 c1 trs0)
        (STEPS1: configuration_steps_trace c1 c2 trs1)
        (TRACE0: List.In (tid0, existT _ lang0 tr0) trs0)
        (TRACE1: List.In (tid1, existT _ lang1 tr1) trs1)
        (EVENT0: List.In (th0, e0) tr0)
        (EVENT1: List.In (th1, e1) tr1)
        (WRITE: racy_write loc ts th0 e0)
        (READ: racy_read loc ts th1 e1)
    :
      False.
  Proof.
    eapply RACEFREE.
    { eapply configuration_steps_trace_trans; eauto. }
    { eapply List.in_or_app. left. eapply TRACE0. }
    { eapply List.in_or_app. right. eapply TRACE1. }
    { eauto. }
    { eauto. }
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
