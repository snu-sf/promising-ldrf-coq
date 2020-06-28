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

  Definition pf_consistent lang (th: Thread.t lang): Prop :=
    exists tr_cert,
      (<<CONSISTENT: Trace.consistent th tr_cert>>) /\
      (<<PFCERT: List.Forall (compose pf_event snd) tr_cert>>).

  Inductive pf_step_trace: forall (tr: Trace.t) (e:MachineEvent.t) (tid:Ident.t) (c1 c2:Configuration.t), Prop :=
  | pf_step_trace_intro
      lang tr e tr' pf tid c1 st1 lc1 e2 st3 lc3 sc3 memory3
      (TID: IdentMap.find tid c1.(Configuration.threads) = Some (existT _ lang st1, lc1))
      (STEPS: Trace.steps tr' (Thread.mk _ st1 lc1 c1.(Configuration.sc) c1.(Configuration.memory)) e2)
      (SILENT: List.Forall (fun the => ThreadEvent.get_machine_event (snd the) = MachineEvent.silent) tr')
      (STEP: Thread.step pf e e2 (Thread.mk _ st3 lc3 sc3 memory3))
      (TR: tr = tr'++[(e2.(Thread.local), e)])
      (CONSISTENT: forall (EVENT: e <> ThreadEvent.failure),
          pf_consistent (Thread.mk _ st3 lc3 sc3 memory3))
      (PF: List.Forall (compose pf_event snd) tr)
    :
      pf_step_trace tr (ThreadEvent.get_machine_event e) tid c1 (Configuration.mk (IdentMap.add tid (existT _ _ st3, lc3) c1.(Configuration.threads)) sc3 memory3)
  .

  Inductive pf_opt_step_trace: forall (tr: Trace.t) (e:MachineEvent.t) (tid:Ident.t) (c1 c2:Configuration.t), Prop :=
  | pf_opt_step_trace_some
      tr e tid c1 c2
      (STEP: pf_step_trace tr e tid c1 c2)
    :
      pf_opt_step_trace tr e tid c1 c2
  | pf_opt_step_trace_none
      tid c1
    :
      pf_opt_step_trace [] MachineEvent.silent tid c1 c1
  .

  Lemma pf_step_trace_step tr e tid c1 c2
        (STEP: pf_step_trace tr e tid c1 c2)
    :
      Configuration.step e tid c1 c2.
  Proof.
    inv STEP. destruct (classic (e0 = ThreadEvent.failure)).
    { subst. econs 1; try apply STEP0; eauto.
      eapply Trace.silent_steps_tau_steps; eauto. }
    { econs 2; try apply STEP0; eauto.
      { eapply Trace.silent_steps_tau_steps; eauto. }
      { exploit CONSISTENT; eauto. i. unfold pf_consistent in *. des.
        eapply Trace.consistent_thread_consistent; eauto. }
    }
  Qed.

  Lemma pf_step_trace_future
        (tr: Trace.t) e tid c1 c2
        (STEP: pf_step_trace tr e tid c1 c2)
        (WF1: Configuration.wf c1):
    (<<WF2: Configuration.wf c2>>) /\
    (<<SC_FUTURE: TimeMap.le c1.(Configuration.sc) c2.(Configuration.sc)>>) /\
    (<<MEM_FUTURE: Memory.future c1.(Configuration.memory) c2.(Configuration.memory)>>).
  Proof.
    eapply pf_step_trace_step in STEP.
    eapply Configuration.step_future; eauto.
  Qed.

  Lemma pf_opt_step_trace_future
        (tr: Trace.t) e tid c1 c2
        (STEP: pf_opt_step_trace tr e tid c1 c2)
        (WF1: Configuration.wf c1):
    (<<WF2: Configuration.wf c2>>) /\
    (<<SC_FUTURE: TimeMap.le c1.(Configuration.sc) c2.(Configuration.sc)>>) /\
    (<<MEM_FUTURE: Memory.future c1.(Configuration.memory) c2.(Configuration.memory)>>).
  Proof.
    inv STEP.
    { eapply pf_step_trace_future; eauto. }
    { splits; auto. refl. }
  Qed.

  Inductive pf_steps_trace:
    forall (c0 c1: Configuration.t) (tr: Trace.t), Prop :=
  | pf_steps_trace_nil
      c0
    :
      pf_steps_trace c0 c0 []
  | pf_steps_trace_cons
      c0 c1 c2 trs tr e tid
      (STEPS: pf_steps_trace c1 c2 trs)
      (STEP: pf_step_trace tr e tid c0 c1)
    :
      pf_steps_trace c0 c2 (tr ++ trs)
  .

  Lemma pf_steps_trace_n1 c0 c1 c2 tr trs e tid
        (STEPS: pf_steps_trace c0 c1 trs)
        (STEP: pf_step_trace tr e tid c1 c2)
    :
      pf_steps_trace c0 c2 (trs ++ tr).
  Proof.
    ginduction STEPS.
    { i. exploit pf_steps_trace_cons.
      { econs 1. }
      { eapply STEP. }
      { i. ss. erewrite List.app_nil_r in *. auto. }
    }
    { i. exploit IHSTEPS; eauto. i. erewrite <- List.app_assoc. econs; eauto. }
  Qed.

  Lemma pf_steps_trace_trans c0 c1 c2 trs0 trs1
        (STEPS0: pf_steps_trace c0 c1 trs0)
        (STEPS1: pf_steps_trace c1 c2 trs1)
    :
      pf_steps_trace c0 c2 (trs0 ++ trs1).
  Proof.
    ginduction STEPS0.
    { i. erewrite List.app_nil_l. eauto. }
    { i. exploit IHSTEPS0; eauto. i. erewrite <- List.app_assoc. econs; eauto. }
  Qed.

  Inductive silent_pf_steps_trace:
    forall (c0 c1: Configuration.t) (tr: Trace.t), Prop :=
  | silent_pf_steps_trace_nil
      c0
    :
      silent_pf_steps_trace c0 c0 []
  | silent_pf_steps_trace_cons
      c0 c1 c2 trs tr tid
      (STEPS: silent_pf_steps_trace c1 c2 trs)
      (STEP: pf_step_trace tr MachineEvent.silent tid c0 c1)
    :
      silent_pf_steps_trace c0 c2 (tr ++ trs)
  .

  Lemma silent_pf_steps_trace_pf_steps_trace
    :
      silent_pf_steps_trace <3= pf_steps_trace.
  Proof.
    intros. induction PR.
    { econs. }
    { econs; eauto. }
  Qed.


  Inductive pf_step (e:MachineEvent.t) (tid:Ident.t) (c1 c2:Configuration.t): Prop :=
  | pf_step_intro
      tr
      (STEP: pf_step_trace tr e tid c1 c2)
  .

  Lemma pf_step_future
        e tid c1 c2
        (STEP: pf_step e tid c1 c2)
        (WF1: Configuration.wf c1):
    (<<WF2: Configuration.wf c2>>) /\
    (<<SC_FUTURE: TimeMap.le c1.(Configuration.sc) c2.(Configuration.sc)>>) /\
    (<<MEM_FUTURE: Memory.future c1.(Configuration.memory) c2.(Configuration.memory)>>).
  Proof.
    inv STEP. eapply pf_step_trace_future; eauto.
  Qed.

  Lemma silent_pf_steps_trace_behaviors c0 c1 tr
        (STEP: silent_pf_steps_trace c0 c1 tr)
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
         Time.lt (if Ordering.le Ordering.relaxed ordr
                  then (lc.(Local.tview).(TView.cur).(View.rlx) loc)
                  else (lc.(Local.tview).(TView.cur).(View.pln) loc)) ts)
    :
      racy_read loc ts lc (ThreadEvent.read loc ts valr releasedr ordr)
  | racy_read_update
      lc
      to valr valw releasedr releasedw ordr ordw
      (VIEW:
         Time.lt (if Ordering.le Ordering.relaxed ordr
                  then (lc.(Local.tview).(TView.cur).(View.rlx) loc)
                  else (lc.(Local.tview).(TView.cur).(View.pln) loc)) ts)
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
           (CSTEPS: pf_steps_trace c0 c1 trs)
           (TRACE0: List.In (lc0, e0) trs)
           (TRACE1: List.In (lc1, e1) trs)
           (WRITE: racy_write loc ts lc0 e0)
           (READ: racy_read loc ts lc1 e1),
      False.

  Lemma step_racefree c0 c1 tr e tid
        (RACEFREE: racefree c0)
        (STEP: pf_step_trace tr e tid c0 c1)
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
        (STEP: pf_steps_trace c0 c1 trs)
    :
      racefree c1.
  Proof.
    ii. eapply RACEFREE.
    { eapply pf_steps_trace_trans; eauto. }
    { eapply List.in_or_app. right. eapply TRACE0. }
    { eapply List.in_or_app. right. eapply TRACE1. }
    { eauto. }
    { eauto. }
  Qed.

  Lemma racefree_write_read c0 c1 c2 trs0 trs1
        loc ts lc0 lc1 e0 e1
        (RACEFREE: racefree c0)
        (STEPS0: pf_steps_trace c0 c1 trs0)
        (STEPS1: pf_steps_trace c1 c2 trs1)
        (TRACE0: List.In (lc0, e0) trs0)
        (TRACE1: List.In (lc1, e1) trs1)
        (WRITE: racy_write loc ts lc0 e0)
        (READ: racy_read loc ts lc1 e1)
    :
      False.
  Proof.
    eapply RACEFREE.
    { eapply pf_steps_trace_trans; eauto. }
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
