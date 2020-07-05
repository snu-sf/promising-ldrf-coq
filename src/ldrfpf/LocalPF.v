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

Require Import PromiseConsistent.
Require Import MemoryProps.

Set Implicit Arguments.



Section LOCALPF.

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

  Lemma pf_steps_trace_future
        c1 c2 tr
        (STEPS: pf_steps_trace c1 c2 tr)
        (WF1: Configuration.wf c1):
    (<<WF2: Configuration.wf c2>>) /\
    (<<SC_FUTURE: TimeMap.le c1.(Configuration.sc) c2.(Configuration.sc)>>) /\
    (<<MEM_FUTURE: Memory.future c1.(Configuration.memory) c2.(Configuration.memory)>>).
  Proof.
    revert WF1. induction STEPS; i.
    - splits; ss; refl.
    - exploit pf_step_trace_future; eauto. i. des.
      exploit IHSTEPS; eauto. i. des.
      splits; ss; etrans; eauto.
  Qed.

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

  Lemma pf_step_trace_pf_steps_trace tr e tid c1 c2
        (STEP: pf_step_trace tr e tid c1 c2)
    :
      pf_steps_trace c1 c2 tr.
  Proof.
    exploit pf_steps_trace_cons.
    { econs 1. }
    { eauto. }
    i. rewrite List.app_nil_r in x0. auto.
  Qed.

  Lemma pf_opt_step_trace_pf_steps_trace tr e tid c1 c2
        (STEP: pf_opt_step_trace tr e tid c1 c2)
    :
      pf_steps_trace c1 c2 tr.
  Proof.
    inv STEP.
    { eapply pf_step_trace_pf_steps_trace; eauto. }
    { econs 1. }
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

  Inductive pf_steps_trace_rev: forall (c1 c2: Configuration.t) (tr: Trace.t), Prop :=
  | pf_steps_trace_rev_nil
      c:
      pf_steps_trace_rev c c []
  | pf_steps_trace_rev_cons
      c1 c2 c3 tr1 tr2 e tid
      (STEPS: pf_steps_trace_rev c1 c2 tr1)
      (STEP: pf_step_trace tr2 e tid c2 c3):
      pf_steps_trace_rev c1 c3 (tr1 ++ tr2)
  .
  Hint Constructors pf_steps_trace_rev.

  Lemma pf_steps_trace_rev_1n
        c1 c2 c3 tr1 tr2 e tid
        (STEP: pf_step_trace tr1 e tid c1 c2)
        (STEPS: pf_steps_trace_rev c2 c3 tr2):
    pf_steps_trace_rev c1 c3 (tr1 ++ tr2).
  Proof.
    revert tr1 e tid c1 STEP. induction STEPS; i.
    - replace (tr1 ++ []) with ([] ++ tr1) by (rewrite List.app_nil_r; ss).
      econs 2; [econs 1|]. eauto.
    - exploit IHSTEPS; eauto. i.
      rewrite List.app_assoc.
      econs 2; eauto.
  Qed.

  Lemma pf_steps_trace_equiv c1 c2 tr:
    pf_steps_trace c1 c2 tr <-> pf_steps_trace_rev c1 c2 tr.
  Proof.
    split; i.
    - induction H; eauto.
      eapply pf_steps_trace_rev_1n; eauto.
    - induction H; [econs 1|].
      eapply pf_steps_trace_n1; eauto.
  Qed.

  Lemma pf_steps_trace_inv
        c1 c2 tr lc e
        (STEPS: pf_steps_trace c1 c2 tr)
        (WF: Configuration.wf c1)
        (TRACE: List.In (lc, e) tr):
    exists c tr1 tid lang st1 lc1,
      (<<STEPS: pf_steps_trace c1 c tr1>>) /\
      (<<FIND: IdentMap.find tid c.(Configuration.threads) = Some (existT _ lang st1, lc1)>>) /\
      exists tr2 pf e2 e3,
        (<<THREAD_STEPS: Trace.steps tr2 (Thread.mk _ st1 lc1 c.(Configuration.sc) c.(Configuration.memory)) e2>>) /\
        (<<SILENT: List.Forall (fun the => ThreadEvent.get_machine_event (snd the) = MachineEvent.silent) tr2>>) /\
        (<<PF: List.Forall (compose pf_event snd) tr2>>) /\
        (<<LC: e2.(Thread.local) = lc>>) /\
        (<<THREAD_STEP: Thread.step pf e e2 e3>>) /\
        (<<CONS: Local.promise_consistent e3.(Thread.local)>>).
  Proof.
    rewrite pf_steps_trace_equiv in STEPS.
    induction STEPS; ss.
    apply List.in_app_or in TRACE. des; eauto.
    clear IHSTEPS. inv STEP.
    exists c2, tr1, tid, lang, st1, lc1.
    rewrite <- pf_steps_trace_equiv in STEPS.
    splits; ss.
    apply List.in_app_or in TRACE. des; cycle 1.
    { inv TRACE; ss. inv H. esplits; eauto.
      - apply Forall_app_inv in PF. des. ss.
      - destruct (classic (e = ThreadEvent.failure)).
        + subst. inv STEP0; inv STEP. inv LOCAL. inv LOCAL0. ss.
        + exploit CONSISTENT; eauto. i. inv x. des.
          exploit pf_steps_trace_future; eauto. i. des.
          inv WF2. inv WF0. exploit THREADS; eauto. i.
          exploit Trace.steps_future; try exact STEPS0; eauto. s. i. des.
          exploit Thread.step_future; try exact STEP0; eauto. s. i. des.
          hexploit consistent_promise_consistent;
            try eapply Trace.consistent_thread_consistent; try exact CONSISTENT0; eauto.
    }
    exploit pf_steps_trace_future; eauto. i. des.
    inv WF2. inv WF0. exploit THREADS; eauto. i. clear DISJOINT THREADS.
    exploit Trace.steps_inv; try exact STEPS0; eauto.
    { destruct (classic (e1 = ThreadEvent.failure)).
      - subst. inv STEP0; inv STEP. inv LOCAL. inv LOCAL0. ss.
      - exploit CONSISTENT; ss. i. inv x0. des.
        exploit Trace.steps_future; eauto. s. i. des.
        exploit Thread.step_future; eauto. s. i. des.
        eapply step_promise_consistent; eauto.
        eapply consistent_promise_consistent; eauto.
        eapply Trace.consistent_thread_consistent; eauto.
    }
    i. des. esplits; eauto; subst.
    - apply Forall_app_inv in SILENT. des. ss.
    - apply Forall_app_inv in PF. des.
      apply Forall_app_inv in FORALL1. des. ss.
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

  Inductive reading_event (loc: Loc.t) (ts: Time.t):
    forall (e: ThreadEvent.t), Prop :=
  | reading_event_read
      valr releasedr ordr
    :
      reading_event loc ts (ThreadEvent.read loc ts valr releasedr ordr)
  | reading_event_update
      to valr valw releasedr releasedw ordr ordw
    :
      reading_event loc ts (ThreadEvent.update loc ts to valr valw releasedr releasedw ordr ordw)
  .

  Inductive writing_event (loc: Loc.t) (ts: Time.t):
    forall (e: ThreadEvent.t), Prop :=
  | writing_event_write
      from valw releasedw ordw
      (ORD: Ordering.le ordw Ordering.relaxed)
    :
      writing_event loc ts (ThreadEvent.write loc from ts valw releasedw ordw)
  | writing_event_update
      from valr valw releasedr releasedw ordr ordw
      (ORD: Ordering.le ordw Ordering.relaxed)
    :
      writing_event loc ts (ThreadEvent.update loc from ts valr valw releasedr releasedw ordr ordw)
  .

  Definition pf_racefree_imm (c0: Configuration.t): Prop :=
    forall tid0 c1 trs0 tid1 c2 trs1
           loc ts lc1 te0 te1 e0 e1
           (LOC: L loc)
           (TID: tid0 <> tid1)
           (CSTEP0: pf_step_trace trs0 e0 tid0 c0 c1)
           (WRITE: writing_event loc ts te0)
           (TRACE0: final_event_trace te0 trs0)
           (CSTEP1: pf_step_trace trs1 e1 tid1 c1 c2)
           (READ: reading_event loc ts te1)
           (TRACE1: List.In (lc1, te1) trs1),
      False.

  Definition pf_racefree (c0: Configuration.t): Prop :=
    forall c1 trs
           (CSTEPS: pf_steps_trace c0 c1 trs),
      pf_racefree_imm c1.

  Lemma step_pf_racefree c0 c1 tr e tid
        (RACEFREE: pf_racefree c0)
        (STEP: pf_step_trace tr e tid c0 c1)
    :
      pf_racefree c1.
  Proof.
    unfold pf_racefree in *. i.
    eapply RACEFREE. econs 2; eauto.
  Qed.

  Lemma steps_pf_racefree c0 c1 trs
        (RACEFREE: pf_racefree c0)
        (STEPS: pf_steps_trace c0 c1 trs)
    :
      pf_racefree c1.
  Proof.
    induction STEPS; auto. eapply IHSTEPS.
    eapply step_pf_racefree; eauto.
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

  Definition pf_racefree_view (c0: Configuration.t): Prop :=
    forall c1 trs1 c2 trs2
      loc ts lc0 lc1 e0 e1
      (CSTEPS1: pf_steps_trace c0 c1 trs1)
      (LOC: L loc)
      (TRACE1: List.In (lc0, e0) trs1)
      (WRITE: racy_write loc ts lc0 e0)
      (CSTEPS2: pf_steps_trace c1 c2 trs2)
      (TRACE2: List.In (lc1, e1) trs2)
      (READ: racy_read loc ts lc1 e1),
      False.

  Lemma step_pf_racefree_view c0 c1 tr e tid
        (RACEFREE: pf_racefree_view c0)
        (STEP: pf_step_trace tr e tid c0 c1)
    :
      pf_racefree_view c1.
  Proof.
    ii. eapply RACEFREE.
    { econs 2.
      { eapply CSTEPS1. }
      { eauto. }
    }
    { eauto. }
    { eapply List.in_or_app. right. eapply TRACE1. }
    { eauto. }
    { eauto. }
    { eauto. }
    { eauto. }
  Qed.

  Lemma steps_pf_racefree_view c0 c1 trs
        (RACEFREE: pf_racefree_view c0)
        (STEPS: pf_steps_trace c0 c1 trs)
    :
      pf_racefree_view c1.
  Proof.
    induction STEPS; auto. eapply IHSTEPS.
    eapply step_pf_racefree_view; eauto.
  Qed.

  Lemma pf_racefree_pf_racefree_tview c
        (WF: Configuration.wf c)
        (RACEFREE: pf_racefree_view c)
    :
      pf_racefree c.
  Proof.
  Admitted.

End LOCALPF.