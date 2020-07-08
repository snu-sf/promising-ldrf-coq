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
Require Import PromiseConsistent.
Require Import Progress.
Require Import Behavior.

Set Implicit Arguments.



Module Trace.

  Definition t := list (Local.t * ThreadEvent.t).

  Inductive steps lang: forall (tr: t) (th0 th1: Thread.t lang), Prop :=
  | steps_refl
      th0
    :
      steps [] th0 th0
  | steps_step
      tr tr' th0 th1 th2 pf e
      (STEP: Thread.step pf e th0 th1)
      (STEPS: steps tr th1 th2)
      (TR: tr' = (th0.(Thread.local), e) :: tr)
    :
      steps tr' th0 th2
  .
  Hint Constructors steps.

  Inductive steps_n1 lang: t -> (Thread.t lang) -> (Thread.t lang) -> Prop :=
  | steps_n1_refl
      th0
    :
      steps_n1 [] th0 th0
  | steps_n1_step
      th0 th1 th2 hds pf tle
      (HD: steps_n1 hds th0 th1)
      (TL: Thread.step pf tle th1 th2)
    :
      steps_n1 (hds++[(th1.(Thread.local), tle)]) th0 th2
  .
  Hint Constructors steps_n1.

  Lemma steps_n1_one lang (th0 th1: Thread.t lang) e pf
        (STEP: Thread.step pf e th0 th1)
    :
      steps_n1 [(th0.(Thread.local), e)] th0 th1.
  Proof.
    erewrite <- List.app_nil_l at 1. econs; eauto.
  Qed.

  Lemma steps_n1_trans lang (th0 th1 th2: Thread.t lang) tr0 tr1
        (STEPS0: steps_n1 tr0 th0 th1)
        (STEPS1: steps_n1 tr1 th1 th2)
    :
      steps_n1 (tr0 ++ tr1) th0 th2.
  Proof.
    ginduction STEPS1; i; ss.
    - erewrite List.app_nil_r. auto.
    - rewrite List.app_assoc. econs; eauto.
  Qed.

  Lemma steps_one lang (th0 th1: Thread.t lang) e pf
        (STEP: Thread.step pf e th0 th1)
    :
      steps [(th0.(Thread.local), e)] th0 th1.
  Proof.
    econs 2; eauto.
  Qed.

  Lemma steps_trans lang (th0 th1 th2: Thread.t lang) tr0 tr1
        (STEPS0: steps tr0 th0 th1)
        (STEPS1: steps tr1 th1 th2)
    :
      steps (tr0 ++ tr1) th0 th2.
  Proof.
    ginduction STEPS0; i; ss. subst. econs; eauto.
  Qed.

  Lemma steps_equivalent lang (th0 th1: Thread.t lang) tr
    :
        steps tr th0 th1 <-> steps_n1 tr th0 th1.
  Proof.
    split; intros STEP.
    - ginduction STEP.
      + econs.
      + exploit steps_n1_trans.
        * eapply steps_n1_one; eauto.
        * eauto.
        * ss. clarify.
    - ginduction STEP.
      + econs.
      + eapply steps_trans; eauto.
  Qed.

  Lemma steps_separate lang (th0 th2: Thread.t lang) tr0 tr1
        (STEPS: steps (tr0++tr1) th0 th2)
    :
      exists th1,
        (<<STEPS0: steps tr0 th0 th1>>) /\
        (<<STEPS1: steps tr1 th1 th2>>).
  Proof.
    ginduction tr0; i; ss.
    - exists th0. splits; ss.
    - inv STEPS. inv TR. eapply IHtr0 in STEPS0. des.
      exists th1. splits; ss.
      econs; eauto.
  Qed.

  Lemma steps_in lang P (th0 th1: Thread.t lang) tr e th
        (STEPS: steps tr th0 th1)
        (IN: List.In (th, e) tr)
        (PRED: List.Forall P tr)
    :
      exists th' th'' pf tr0 tr1,
        (<<STEPS0: steps tr0 th0 th'>>) /\
        (<<STEP: Thread.step pf e th' th''>>) /\
        (<<STEPS1: steps tr1 th'' th1>>) /\
        (<<TRACES: tr = tr0 ++ [(th, e)] ++ tr1>>) /\
        (<<SAT: P (th, e)>>).
  Proof.
    ginduction STEPS; i; ss. inv PRED; ss. des; clarify.
    - exists th0, th1. esplits; eauto.
    - exploit IHSTEPS; eauto. i. des. subst.
      exists th', th''. esplits; eauto.
  Qed.

  Lemma steps_disjoint
        lang tr (e1 e2: Thread.t lang) lc
        (STEPS: steps tr e1 e2)
        (WF1: Local.wf e1.(Thread.local) e1.(Thread.memory))
        (SC1: Memory.closed_timemap e1.(Thread.sc) e1.(Thread.memory))
        (CLOSED1: Memory.closed e1.(Thread.memory))
        (DISJOINT1: Local.disjoint e1.(Thread.local) lc)
        (WF: Local.wf lc e1.(Thread.memory)):
    (<<DISJOINT2: Local.disjoint e2.(Thread.local) lc>>) /\
    (<<WF: Local.wf lc e2.(Thread.memory)>>).
  Proof.
    induction STEPS; eauto. subst.
    exploit Thread.step_disjoint; eauto. i. des.
    exploit Thread.step_future; eauto. i. des.
    eapply IHSTEPS; eauto.
  Qed.


  Lemma steps_future
        lang tr e1 e2
        (STEPS: @steps lang tr e1 e2)
        (WF1: Local.wf e1.(Thread.local) e1.(Thread.memory))
        (SC1: Memory.closed_timemap e1.(Thread.sc) e1.(Thread.memory))
        (CLOSED1: Memory.closed e1.(Thread.memory)):
    (<<WF2: Local.wf e2.(Thread.local) e2.(Thread.memory)>>) /\
    (<<SC2: Memory.closed_timemap e2.(Thread.sc) e2.(Thread.memory)>>) /\
    (<<CLOSED2: Memory.closed e2.(Thread.memory)>>) /\
    (<<TVIEW_FUTURE: TView.le e1.(Thread.local).(Local.tview) e2.(Thread.local).(Local.tview)>>) /\
    (<<SC_FUTURE: TimeMap.le e1.(Thread.sc) e2.(Thread.sc)>>) /\
    (<<MEM_FUTURE: Memory.future e1.(Thread.memory) e2.(Thread.memory)>>)
  .
  Proof.
    ginduction STEPS.
    - i. splits; auto.
      + refl.
      + refl.
    - i. exploit Thread.step_future; eauto. i. des.
      exploit IHSTEPS; eauto. i. des. splits; auto.
      + etrans; eauto.
      + etrans; eauto.
      + etrans; eauto.
  Qed.

  Lemma steps_promise_consistent
        lang (th1 th2: Thread.t lang) tr
        (STEPS: steps tr th1 th2)
        (CONS: Local.promise_consistent th2.(Thread.local))
        (WF1: Local.wf th1.(Thread.local) th1.(Thread.memory))
        (SC1: Memory.closed_timemap th1.(Thread.sc) th1.(Thread.memory))
        (MEM1: Memory.closed th1.(Thread.memory)):
    Local.promise_consistent th1.(Thread.local).
  Proof.
    ginduction STEPS; auto. i. subst.
    exploit Thread.step_future; eauto. i. des.
    eapply step_promise_consistent; eauto.
  Qed.

  Lemma silent_steps_tau_steps lang tr (th0 th1: Thread.t lang)
        (STEPS: steps tr th0 th1)
        (SILENT: List.Forall (fun the => ThreadEvent.get_machine_event (snd the) = MachineEvent.silent) tr)
    :
      rtc (Thread.tau_step (lang:=lang)) th0 th1.
  Proof.
    ginduction STEPS; auto. i. inv SILENT; clarify. econs 2.
    - econs; eauto. econs; eauto.
    - eauto.
  Qed.

  Lemma tau_steps_silent_steps lang (th0 th1: Thread.t lang)
        (STEPS: rtc (Thread.tau_step (lang:=lang)) th0 th1)
    :
      exists tr,
        (<<STEPS: steps tr th0 th1>>) /\
        (<<SILENT: List.Forall (fun the => ThreadEvent.get_machine_event (snd the) = MachineEvent.silent) tr>>).
  Proof.
    ginduction STEPS; eauto. inv H. inv TSTEP. des.
    exists ((x.(Thread.local), e)::tr). splits; eauto.
  Qed.

  Lemma steps_app lang tr0 tr1 (th0 th1 th2: Thread.t lang)
        (STEPS0: steps tr0 th0 th1)
        (STEPS1: steps tr1 th1 th2)
    :
      steps (tr0 ++ tr1) th0 th2.
  Proof.
    ginduction STEPS0; eauto. i. subst. econs; eauto.
  Qed.

  Definition consistent lang (e:Thread.t lang) (tr: t): Prop :=
    forall mem1 sc1
           (CAP: Memory.cap e.(Thread.memory) mem1)
           (SC_MAX: Memory.max_concrete_timemap mem1 sc1),
    exists e2,
      (<<STEPS: steps tr (Thread.mk _ e.(Thread.state) e.(Thread.local) sc1 mem1) e2>>) /\
      (<<SILENT: List.Forall (fun lce => ThreadEvent.get_machine_event (snd lce) = MachineEvent.silent) tr>>) /\
      ((<<FAILURE: exists e3, Thread.step true ThreadEvent.failure e2 e3 >>) \/
       (<<PROMISES: e2.(Thread.local).(Local.promises) = Memory.bot>>)).

  Lemma consistent_thread_consistent lang (e: Thread.t lang) tr
        (CONSISTENT: consistent e tr)
    :
      Thread.consistent e.
  Proof.
    ii. exploit CONSISTENT; eauto. i. des.
    { left. unfold Thread.steps_failure. esplits.
      { eapply silent_steps_tau_steps in STEPS; eauto. }
      { eauto. }
    }
    { right. esplits.
      { eapply silent_steps_tau_steps in STEPS; eauto. }
      { eauto. }
    }
  Qed.

  Lemma thread_consistent_consistent lang (e: Thread.t lang)
        (CONSISTENT: Thread.consistent e)
        (CLOSED: Memory.closed e.(Thread.memory))
    :
      exists tr,
        (<<CONSISTENT: consistent e tr>>).
  Proof.
    exploit Memory.cap_exists; eauto. i. des.
    exploit Memory.max_concrete_timemap_exists; eauto.
    { eapply Memory.cap_closed; eauto. } i. des.
    exploit CONSISTENT; eauto. i. des.
    { unfold Thread.steps_failure in *. des.
      eapply tau_steps_silent_steps in STEPS. des.
      exists tr. ii.
      exploit (@Memory.cap_inj e.(Thread.memory) mem2 mem1); eauto. i. subst.
      exploit (@Memory.max_concrete_timemap_inj mem1 tm sc1); eauto. i. subst.
      esplits; eauto.
    }
    { eapply tau_steps_silent_steps in STEPS. des.
      exists tr. ii.
      exploit (@Memory.cap_inj e.(Thread.memory) mem2 mem1); eauto. i. subst.
      exploit (@Memory.max_concrete_timemap_inj mem1 tm sc1); eauto. i. subst.
      esplits; eauto.
    }
  Qed.

  Lemma plus_step_steps
        lang tr e1 e2 e3 pf e
        (STEPS: @steps lang tr e1 e2)
        (STEP: Thread.step pf e e2 e3):
    steps (tr ++ [(e2.(Thread.local), e)]) e1 e3.
  Proof.
    rewrite steps_equivalent in *. eauto.
  Qed.

  Lemma steps_inv
        lang tr e1 e2 lc e
        (STEPS: @steps lang tr e1 e2)
        (WF1: Local.wf e1.(Thread.local) e1.(Thread.memory))
        (SC1: Memory.closed_timemap e1.(Thread.sc) e1.(Thread.memory))
        (MEM1: Memory.closed e1.(Thread.memory))
        (EVENT: List.In (lc, e) tr)
        (CONS: Local.promise_consistent e2.(Thread.local)):
    exists tr' tr'' e2' pf e3,
      (<<STEPS: steps tr' e1 e2'>>) /\
      (<<TRACE: tr = tr' ++ tr''>>) /\
      (<<LC: e2'.(Thread.local) = lc>>) /\
      (<<STEP: Thread.step pf e e2' e3>>) /\
      (<<CONS: Local.promise_consistent e3.(Thread.local)>>).
  Proof.
    rewrite steps_equivalent in STEPS.
    induction STEPS; ss.
    apply List.in_app_or in EVENT. des.
    - exploit IHSTEPS; eauto.
      { rewrite <- steps_equivalent in STEPS.
        exploit steps_future; eauto. i. des.
        eapply step_promise_consistent; eauto. }
      i. des. subst. esplits; eauto.
      rewrite <- List.app_assoc. refl.
    - inv EVENT; ss. inv H.
      rewrite <- steps_equivalent in STEPS.
      esplits; eauto.
  Qed.
End Trace.

Module ThreadTrace.

  Definition t (lang: language) := list (Thread.t lang * ThreadEvent.t).

  Inductive steps lang: forall (tr: t lang) (th0 th1: Thread.t lang), Prop :=
  | steps_refl
      th0
    :
      steps [] th0 th0
  | steps_step
      tr tr' th0 th1 th2 pf e
      (STEP: Thread.step pf e th0 th1)
      (STEPS: steps tr th1 th2)
      (TR: tr' = (th0, e) :: tr)
    :
      steps tr' th0 th2
  .
  Hint Constructors steps.

  Lemma steps_trans lang (th0 th1 th2: Thread.t lang) tr0 tr1
        (STEPS0: steps tr0 th0 th1)
        (STEPS1: steps tr1 th1 th2)
    :
      steps (tr0 ++ tr1) th0 th2.
  Proof.
    ginduction STEPS0; i; ss. subst. econs; eauto.
  Qed.

  Lemma steps_separate lang (th0 th2: Thread.t lang) tr0 tr1
        (STEPS: steps (tr0++tr1) th0 th2)
    :
      exists th1,
        (<<STEPS0: steps tr0 th0 th1>>) /\
        (<<STEPS1: steps tr1 th1 th2>>).
  Proof.
    ginduction tr0; i; ss.
    - exists th0. splits; ss.
    - inv STEPS. inv TR. eapply IHtr0 in STEPS0. des.
      exists th1. splits; ss.
      econs; eauto.
  Qed.

  Lemma steps_future
        lang tr e1 e2
        (STEPS: @steps lang tr e1 e2)
        (WF1: Local.wf e1.(Thread.local) e1.(Thread.memory))
        (SC1: Memory.closed_timemap e1.(Thread.sc) e1.(Thread.memory))
        (CLOSED1: Memory.closed e1.(Thread.memory)):
    (<<WF2: Local.wf e2.(Thread.local) e2.(Thread.memory)>>) /\
    (<<SC2: Memory.closed_timemap e2.(Thread.sc) e2.(Thread.memory)>>) /\
    (<<CLOSED2: Memory.closed e2.(Thread.memory)>>) /\
    (<<TVIEW_FUTURE: TView.le e1.(Thread.local).(Local.tview) e2.(Thread.local).(Local.tview)>>) /\
    (<<SC_FUTURE: TimeMap.le e1.(Thread.sc) e2.(Thread.sc)>>) /\
    (<<MEM_FUTURE: Memory.future e1.(Thread.memory) e2.(Thread.memory)>>)
  .
  Proof.
    ginduction STEPS.
    - i. splits; auto.
      + refl.
      + refl.
    - i. exploit Thread.step_future; eauto. i. des.
      exploit IHSTEPS; eauto. i. des. splits; auto.
      + etrans; eauto.
      + etrans; eauto.
      + etrans; eauto.
  Qed.

  Lemma trace_steps_thread_trace_steps lang (th0 th1: Thread.t lang) tr
        (STEPS: Trace.steps tr th0 th1)
    :
      exists ttr,
        (<<STEPS: steps ttr th0 th1>>) /\
        (<<MATCH: List.Forall2
                    (fun the lce =>
                       (fst the).(Thread.local) = (fst lce) /\
                       (snd the) = (snd lce)) ttr tr>>).
  Proof.
    ginduction STEPS; eauto. i. subst. des. esplits.
    { econs; eauto. }
    { econs; eauto. }
  Qed.

  Lemma thread_trace_steps_trace_steps lang (th0 th1: Thread.t lang) ttr
        (STEPS: steps ttr th0 th1)
    :
      exists tr,
        (<<STEPS: Trace.steps tr th0 th1>>) /\
        (<<MATCH: List.Forall2
                    (fun the lce =>
                       (fst the).(Thread.local) = (fst lce) /\
                       (snd the) = (snd lce)) ttr tr>>).
  Proof.
    ginduction STEPS; eauto. i. subst. des. esplits.
    { econs; eauto. }
    { econs; eauto. }
  Qed.

End ThreadTrace.


Definition is_reserving (te: ThreadEvent.t): Prop :=
  match te with
  | ThreadEvent.promise _ _ _ Message.reserve Memory.op_kind_add => True
  | _ => False
  end.

Inductive final_event_trace (e: ThreadEvent.t)
  :
    forall (tr: Trace.t), Prop :=
| final_event_trace_base
    lc str
    (RESERVING: List.Forall (fun lce => is_reserving (snd lce)) str)
  :
    final_event_trace e ((lc, e) :: str)
| final_event_trace_cons
    hd tl
    (FINAL: final_event_trace e tl)
  :
    final_event_trace e (hd :: tl)
.
