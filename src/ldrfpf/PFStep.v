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
Require Import PFConsistent.
Require Import MemoryProps.
Require Import Single.

Set Implicit Arguments.



Module PF.
Section LOCALPF.
  Variable L: Loc.t -> bool.

  Definition pf_event (e: ThreadEvent.t): Prop :=
    forall loc from to msg kind
      (PROMISE: e = ThreadEvent.promise loc from to msg kind)
      (LOC: L loc),
      msg = Message.reserve.

  Definition pf_consistent lang (th: Thread.t lang): Prop :=
    exists tr_cert,
      (<<CONSISTENT: Trace.consistent th tr_cert>>) /\
      (<<PFCERT: List.Forall (compose pf_event snd) tr_cert>>).

  Definition pf_promises (prom: Memory.t): Prop :=
    forall loc to from msg
           (LOC: L loc)
           (GET: Memory.get loc to prom = Some (from, msg)),
      msg = Message.reserve.

  Definition pf_configuration (c: Configuration.t) :=
    forall tid lang st lc
           (TID: IdentMap.find tid (Configuration.threads c) = Some (existT _ lang st, lc)),
      pf_promises (Local.promises lc).

  Lemma pf_consistent_consistent lang (th: Thread.t lang)
        (CONSISTENT: pf_consistent th)
    :
      Thread.consistent th.
  Proof.
    ii. unfold pf_consistent in *. des.
    exploit CONSISTENT0; eauto. i. des.
    { eapply Trace.silent_steps_tau_steps in STEPS; eauto.
      left. unfold Thread.steps_failure. esplits; eauto. }
    { eapply Trace.silent_steps_tau_steps in STEPS; eauto. }
  Qed.

  Lemma pf_promises_promise prom0 mem0 loc from to msg prom1 mem1 kind
        (PROMISE: Memory.promise prom0 mem0 loc from to msg prom1 mem1 kind)
        (PF: L loc -> msg = Message.reserve)
        (PROMISES: pf_promises prom0)
    :
      pf_promises prom1.
  Proof.
    inv PROMISE.
    - ii. erewrite Memory.add_o in GET; eauto. des_ifs.
      + ss. des; clarify. auto.
      + eapply PROMISES; eauto.
    - ii. erewrite Memory.split_o in GET; eauto. des_ifs.
      + ss. des; clarify. auto.
      + ss. des; clarify. exploit PF; ss.
      + eapply PROMISES; eauto.
    - ii. erewrite Memory.lower_o in GET; eauto. des_ifs.
      + ss. des; clarify. auto.
      + eapply PROMISES; eauto.
    - ii. erewrite Memory.remove_o in GET; eauto. des_ifs.
      eapply PROMISES; eauto.
  Qed.

  Lemma pf_promises_write prom0 mem0 loc from to msg prom1 mem1 kind
        (WRITE: Memory.write prom0 mem0 loc from to msg prom1 mem1 kind)
        (PROMISES: pf_promises prom0)
    :
      pf_promises prom1.
  Proof.
    inv WRITE. ii. erewrite Memory.remove_o in GET; eauto. des_ifs.
    inv PROMISE.
    - erewrite Memory.add_o in GET; eauto. des_ifs.
      + ss. des; clarify.
      + eapply PROMISES; eauto.
    - erewrite Memory.split_o in GET; eauto. des_ifs.
      + ss. des; clarify.
      + ss. des; clarify.
        eapply Memory.split_get0 in PROMISES0. des.
        eapply PROMISES in GET0; eauto.
      + eapply PROMISES; eauto.
    - erewrite Memory.lower_o in GET; eauto. des_ifs.
      + ss. des; clarify.
      + eapply PROMISES; eauto.
    - erewrite Memory.remove_o in GET; eauto. des_ifs. eauto.
  Qed.

  Lemma pf_promises_write_na
        ts prom0 mem0 loc from to msg prom1 mem1 msgs kinds kind
        (WRITE: Memory.write_na ts prom0 mem0 loc from to msg prom1 mem1 msgs kinds kind)
        (PROMISES: pf_promises prom0)
    :
      pf_promises prom1.
  Proof.
    induction WRITE; eauto using pf_promises_write.
  Qed.

  Lemma pf_promises_step lang (th0 th1: Thread.t lang) pf e
        (STEP: Thread.step pf e th0 th1)
        (PF: pf_event e)
        (PROMISES: pf_promises (Local.promises (Thread.local th0)))
    :
      pf_promises (Local.promises (Thread.local th1)).
  Proof.
    inv STEP.
    - inv STEP0; ss. inv LOCAL.
      eapply pf_promises_promise; eauto.
    - inv STEP0. inv LOCAL; ss.
      + inv LOCAL0; ss.
      + inv LOCAL0; ss.
        eapply pf_promises_write; eauto.
      + inv LOCAL1. inv LOCAL2; ss.
        eapply pf_promises_write; eauto.
      + inv LOCAL0; ss.
      + inv LOCAL0; ss.
      + inv LOCAL0; ss.
        eapply pf_promises_write_na; eauto.
  Qed.

  Lemma pf_promises_opt_step lang (th0 th1: Thread.t lang) e
        (STEP: Thread.opt_step e th0 th1)
        (PF: pf_event e)
        (PROMISES: pf_promises (Local.promises (Thread.local th0)))
    :
      pf_promises (Local.promises (Thread.local th1)).
  Proof.
    inv STEP; auto.
    eapply pf_promises_step; eauto.
  Qed.

  Lemma pf_promises_reserve_steps lang (th0 th1: Thread.t lang)
        (STEPS: rtc (@Thread.reserve_step _) th0 th1)
        (PROMISES: pf_promises (Local.promises (Thread.local th0)))
    :
      pf_promises (Local.promises (Thread.local th1)).
  Proof.
    ginduction STEPS; eauto. i. eapply IHSTEPS.
    inv H. eapply pf_promises_step; eauto. ii. clarify.
  Qed.

  Lemma pf_promises_cancel_steps lang (th0 th1: Thread.t lang)
        (STEPS: rtc (@Thread.cancel_step _) th0 th1)
        (PROMISES: pf_promises (Local.promises (Thread.local th0)))
    :
      pf_promises (Local.promises (Thread.local th1)).
  Proof.
    ginduction STEPS; eauto. i. eapply IHSTEPS.
    inv H. eapply pf_promises_step; eauto. ii. clarify.
  Qed.

  Lemma configuration_init_pf syn: pf_configuration (Configuration.init syn).
  Proof.
    ii. ss. unfold Threads.init in *.
    erewrite IdentMap.Facts.map_o in TID.
    unfold option_map in *. des_ifs. dep_clarify.
    erewrite Memory.bot_get in GET. ss.
  Qed.

  Lemma pf_promises_step_event lang (th0 th1: Thread.t lang) e
        (STEP: Thread.step true e th0 th1)
        (PROMISES: pf_promises (Local.promises (Thread.local th0)))
    :
      pf_event e.
  Proof.
    ii. subst.
    inv STEP; inv STEP0; inv LOCAL. inv PROMISE; ss.
    eapply Memory.lower_get0 in PROMISES0. des.
    eapply PROMISES in GET; eauto. clarify. inv MSG_LE. ss.
  Qed.

  Lemma pf_promises_steps_trace lang (th0 th1: Thread.t lang)
        (STEPS: rtc (tau (Thread.step true)) th0 th1)
        (PROMISES: pf_promises (Local.promises (Thread.local th0)))
    :
      exists tr,
        (<<STEPS: Trace.steps tr th0 th1>>) /\
        (<<PF: List.Forall (compose pf_event snd) tr>>) /\
        (<<SILENT: List.Forall (fun lce => ThreadEvent.get_machine_event (snd lce) = MachineEvent.silent) tr>>).
  Proof.
    ginduction STEPS; eauto; i.
    { exists []. splits; eauto. }
    i. inv H. hexploit pf_promises_step_event; eauto. intros PF.
    hexploit pf_promises_step; eauto. intros PROMISES0.
    exploit IHSTEPS; eauto. i. des. esplits; eauto.
  Qed.

  Lemma pf_promises_trace_steps lang (th0 th1: Thread.t lang) tr
        (STEPS: Trace.steps tr th0 th1)
        (PF: List.Forall (compose pf_event snd) tr)
        (PROMISES: pf_promises (Local.promises (Thread.local th0)))
    :
      pf_promises (Local.promises (Thread.local th1)).
  Proof.
    ginduction STEPS; eauto. i. subst.
    inv PF. eapply IHSTEPS; eauto.
    eapply pf_promises_step; eauto.
  Qed.

  Lemma pf_promises_consistent_consistent lang (th: Thread.t lang)
        (CONSISTENT: Thread.consistent th)
        (WF: Local.wf (Thread.local th) (Thread.memory th))
        (SC: Memory.closed_timemap (Thread.sc th) (Thread.memory th))
        (MEM: Memory.closed (Thread.memory th))
        (PROMISES: pf_promises (Local.promises (Thread.local th)))
    :
      pf_consistent th.
  Proof.
    eapply consistent_pf_consistent in CONSISTENT; eauto.
    exploit Memory.cap_exists; eauto. i. des.
    exploit Memory.max_concrete_timemap_exists.
    { eapply Memory.cap_closed; eauto. } i. des.
    exploit CONSISTENT; eauto. i. des.
    { eapply pf_promises_steps_trace in STEPS; eauto. des.
      exists tr. splits; auto. ii.
      exploit (@Memory.cap_inj (Thread.memory th) mem2 mem1); eauto. i. subst.
      esplits; eauto.
    }
    { eapply pf_promises_steps_trace in STEPS; eauto. des.
      exists tr. splits; auto. ii.
      exploit (@Memory.cap_inj (Thread.memory th) mem2 mem1); eauto. i. subst.
      esplits; eauto.
    }
  Qed.
End LOCALPF.
End PF.

(** L-PF machine **)
Module PFConfiguration.
Section LOCALPF.
  Variable L: Loc.t -> bool.

  Inductive step:
    forall (e:ThreadEvent.t) (tid:Ident.t) (c1 c2:Configuration.t), Prop :=
  | step_intro
      e tid c1 lang st1 lc1 e2 e3 st4 lc4 sc4 memory4
      (TID: IdentMap.find tid (Configuration.threads c1) = Some (existT _ lang st1, lc1))
      (CANCELS: rtc (@Thread.cancel_step _) (Thread.mk _ st1 lc1 (Configuration.sc c1) (Configuration.memory c1)) e2)
      (STEP: Thread.opt_step e e2 e3)
      (RESERVES: rtc (@Thread.reserve_step _) e3 (Thread.mk _ st4 lc4 sc4 memory4))
      (CONSISTENT: ThreadEvent.get_machine_event e <> MachineEvent.failure ->
                   PF.pf_consistent L (Thread.mk _ st4 lc4 sc4 memory4))
      (PF: PF.pf_event L e)
    :
      step e tid c1 (Configuration.mk (IdentMap.add tid (existT _ _ st4, lc4) (Configuration.threads c1)) sc4 memory4)
  .
  Hint Constructors step.

  Inductive machine_step: forall (e:MachineEvent.t) (tid:Ident.t) (c1 c2:Configuration.t), Prop :=
  | machine_step_intro
      e tid c1 c2
      (STEP: step e tid c1 c2)
    :
      machine_step (ThreadEvent.get_machine_event e) tid c1 c2
  .
  Hint Constructors machine_step.

  Inductive all_step (c1 c2: Configuration.t): Prop :=
  | all_step_intro
      e tid
      (STEP: step e tid c1 c2)
  .
  Hint Constructors all_step.

  Inductive opt_machine_step:
    forall (e: MachineEvent.t) (tid: Ident.t) (c1 c2: Configuration.t), Prop :=
  | opt_machine_step_none
      tid c:
      opt_machine_step MachineEvent.silent tid c c
  | opt_machine_step_some
      e tid c1 c2
      (STEP: machine_step e tid c1 c2):
      opt_machine_step e tid c1 c2
  .
  Hint Constructors opt_machine_step.

  Definition tau_machine_step := union (machine_step MachineEvent.silent).

  Inductive steps:
    forall (es: list ThreadEvent.t) (tid: Ident.t) (c1 c2:Configuration.t), Prop :=
  | steps_nil
      tid c1
    :
      steps [] tid c1 c1
  | steps_cons
      ehd etl tid c1 c2 c3
      (STEP: step ehd tid c1 c2)
      (STEPS: steps etl tid c2 c3)
    :
      steps (ehd :: etl) tid c1 c3
  .
  Hint Constructors steps.

  Lemma steps_rtc_all_step es tid c1 c2
        (STEPS: steps es tid c1 c2)
    :
      rtc all_step c1 c2.
  Proof.
    induction STEPS; eauto.
  Qed.

  Lemma steps_split es0 es1 tid c0 c2
        (STEPS: steps (es0 ++ es1) tid c0 c2)
    :
      exists c1,
        (<<STEPS0: steps es0 tid c0 c1>>) /\
        (<<STEPS1: steps es1 tid c1 c2>>).
  Proof.
    ginduction es0; eauto. i. ss. inv STEPS.
    exploit IHes0; eauto. i. des.
    esplits; eauto.
  Qed.

  Lemma silent_steps_tau_machine_steps es tid c1 c2
        (STEPS: steps es tid c1 c2)
        (SILENT: List.Forall (fun e => ThreadEvent.get_machine_event e = MachineEvent.silent) es)
    :
      rtc (machine_step MachineEvent.silent tid) c1 c2.
  Proof.
    ginduction es; i.
    { inv STEPS. eauto. }
    { inv STEPS. inv SILENT. exploit IHes; eauto.
      i. econs 2; eauto. rewrite <- H1. econs; eauto. }
  Qed.

  Lemma pf_configuration_step tid c1 c2 e
        (STEP: step e tid c1 c2)
        (PF: PF.pf_configuration L c1)
    :
      PF.pf_configuration L c2.
  Proof.
    inv STEP. unfold PF.pf_configuration in *. i. ss.
    erewrite IdentMap.gsspec in TID0. des_ifs; eauto.
    dep_clarify. eapply PF in TID.
    eapply PF.pf_promises_cancel_steps in CANCELS; eauto.
    eapply PF.pf_promises_opt_step in STEP0; eauto.
    eapply PF.pf_promises_reserve_steps in RESERVES; eauto.
  Qed.

  Lemma event_configuration_step_step c1 c2 e tid
        (STEP: SConfiguration.step e tid c1 c2)
        (WF: Configuration.wf c1)
        (PF: PF.pf_configuration L c1)
        (EVENT: PF.pf_event L e)
    :
      step e tid c1 c2.
  Proof.
    inv STEP. econs; eauto. i.
    exploit Thread.rtc_cancel_step_future; eauto; try eapply WF; eauto. ss. i. des.
    exploit Thread.opt_step_future; eauto. ss. i. des.
    exploit Thread.rtc_reserve_step_future; eauto; try eapply WF; eauto. ss. i. des.
    hexploit PF.pf_promises_cancel_steps; eauto. i. ss.
    hexploit PF.pf_promises_opt_step; eauto. i. ss.
    hexploit PF.pf_promises_reserve_steps; eauto. i. ss.
    eapply PF.pf_promises_consistent_consistent; eauto.
  Qed.

  Lemma reservation_only_step_step tid c1 c2
        (STEP: SConfiguration.reservation_only_step tid c1 c2)
        (WF: Configuration.wf c1)
        (PF: PF.pf_configuration L c1)
    :
      step ThreadEvent.silent tid c1 c2.
  Proof.
    eapply SConfiguration.reservation_only_step_step in STEP.
    eapply event_configuration_step_step; eauto. ss.
  Qed.

  Lemma step_event_configuration_step c1 c2 e tid
        (STEP: step e tid c1 c2)
        (WF: Configuration.wf c1)
    :
      (<<STEP: SConfiguration.step e tid c1 c2>>) /\
      (<<EVENT: PF.pf_event L e>>)
  .
  Proof.
    inv STEP. splits; auto. econs; eauto.
    i. eapply PF.pf_consistent_consistent; eauto.
  Qed.

  Lemma step_future
        e tid c1 c2
        (STEP: step e tid c1 c2)
        (WF1: Configuration.wf c1)
        (PF: PF.pf_configuration L c1):
    (<<WF2: Configuration.wf c2>>) /\
    (<<SC_FUTURE: TimeMap.le (Configuration.sc c1) (Configuration.sc c2)>>) /\
    (<<MEM_FUTURE: Memory.future (Configuration.memory c1) (Configuration.memory c2)>>) /\
    (<<PF: PF.pf_configuration L c2>>).
  Proof.
    exploit step_event_configuration_step; eauto. i. des.
    exploit SConfiguration.step_future; eauto. i. des.
    splits; auto. eapply pf_configuration_step; eauto.
  Qed.

  Lemma machine_step_future
        e tid c1 c2
        (STEP: machine_step e tid c1 c2)
        (WF1: Configuration.wf c1)
        (PF: PF.pf_configuration L c1):
    (<<WF2: Configuration.wf c2>>) /\
    (<<SC_FUTURE: TimeMap.le (Configuration.sc c1) (Configuration.sc c2)>>) /\
    (<<MEM_FUTURE: Memory.future (Configuration.memory c1) (Configuration.memory c2)>>) /\
    (<<PF: PF.pf_configuration L c2>>).
  Proof.
    inv STEP. eapply step_future; eauto.
  Qed.

  Lemma opt_machine_step_future
        e tid c1 c2
        (STEP: opt_machine_step e tid c1 c2)
        (WF1: Configuration.wf c1)
        (PF: PF.pf_configuration L c1):
    (<<WF2: Configuration.wf c2>>) /\
    (<<SC_FUTURE: TimeMap.le (Configuration.sc c1) (Configuration.sc c2)>>) /\
    (<<MEM_FUTURE: Memory.future (Configuration.memory c1) (Configuration.memory c2)>>) /\
    (<<PF: PF.pf_configuration L c2>>).
  Proof.
    inv STEP; eauto.
    - splits; eauto. refl.
    - eapply machine_step_future; eauto.
  Qed.

  Lemma all_step_future
        c1 c2
        (STEP: all_step c1 c2)
        (WF1: Configuration.wf c1)
        (PF: PF.pf_configuration L c1):
    (<<WF2: Configuration.wf c2>>) /\
    (<<SC_FUTURE: TimeMap.le (Configuration.sc c1) (Configuration.sc c2)>>) /\
    (<<MEM_FUTURE: Memory.future (Configuration.memory c1) (Configuration.memory c2)>>) /\
    (<<PF: PF.pf_configuration L c2>>).
  Proof.
    inv STEP. eapply step_future; eauto.
  Qed.

  Lemma tau_machine_step_future
        c1 c2
        (STEP: tau_machine_step c1 c2)
        (WF1: Configuration.wf c1)
        (PF: PF.pf_configuration L c1):
    (<<WF2: Configuration.wf c2>>) /\
    (<<SC_FUTURE: TimeMap.le (Configuration.sc c1) (Configuration.sc c2)>>) /\
    (<<MEM_FUTURE: Memory.future (Configuration.memory c1) (Configuration.memory c2)>>) /\
    (<<PF: PF.pf_configuration L c2>>).
  Proof.
    inv STEP. eapply machine_step_future; eauto.
  Qed.

  Lemma rtc_tau_machine_step_future
        c1 c2
        (STEPS: rtc tau_machine_step c1 c2)
        (WF1: Configuration.wf c1)
        (PF: PF.pf_configuration L c1):
    (<<WF2: Configuration.wf c2>>) /\
    (<<SC_FUTURE: TimeMap.le (Configuration.sc c1) (Configuration.sc c2)>>) /\
    (<<MEM_FUTURE: Memory.future (Configuration.memory c1) (Configuration.memory c2)>>) /\
    (<<PF: PF.pf_configuration L c2>>).
  Proof.
    ginduction STEPS; eauto.
    - i. splits; eauto. refl.
    - i. exploit tau_machine_step_future; eauto. i. des.
      exploit IHSTEPS; eauto. i. des. esplits; eauto. etrans; eauto.
  Qed.

  Lemma rtc_all_step_future
        c1 c2
        (STEPS: rtc all_step c1 c2)
        (WF1: Configuration.wf c1)
        (PF: PF.pf_configuration L c1):
    (<<WF2: Configuration.wf c2>>) /\
    (<<SC_FUTURE: TimeMap.le (Configuration.sc c1) (Configuration.sc c2)>>) /\
    (<<MEM_FUTURE: Memory.future (Configuration.memory c1) (Configuration.memory c2)>>) /\
    (<<PF: PF.pf_configuration L c2>>).
Proof.
    ginduction STEPS; eauto.
    - i. splits; eauto. refl.
    - i. exploit all_step_future; eauto. i. des.
      exploit IHSTEPS; eauto. i. des. esplits; eauto. etrans; eauto.
  Qed.

  Lemma steps_future
        es tid c1 c2
        (STEPS: steps es tid c1 c2)
        (WF1: Configuration.wf c1)
        (PF: PF.pf_configuration L c1):
    (<<WF2: Configuration.wf c2>>) /\
    (<<SC_FUTURE: TimeMap.le (Configuration.sc c1) (Configuration.sc c2)>>) /\
    (<<MEM_FUTURE: Memory.future (Configuration.memory c1) (Configuration.memory c2)>>) /\
    (<<PF: PF.pf_configuration L c2>>).
  Proof.
    ginduction STEPS; eauto.
    - i. splits; eauto. refl.
    - i. exploit step_future; eauto. i. des.
      exploit IHSTEPS; eauto. i. des. esplits; eauto. etrans; eauto.
  Qed.

  Inductive step_trace: forall (tr: Trace.t) (e:MachineEvent.t) (tid:Ident.t) (c1 c2:Configuration.t), Prop :=
  | step_trace_intro
      lang tr e tr' pf tid c1 st1 lc1 e2 st3 lc3 sc3 memory3
      (TID: IdentMap.find tid (Configuration.threads c1) = Some (existT _ lang st1, lc1))
      (STEPS: Trace.steps tr' (Thread.mk _ st1 lc1 (Configuration.sc c1) (Configuration.memory c1)) e2)
      (SILENT: List.Forall (fun the => ThreadEvent.get_machine_event (snd the) = MachineEvent.silent) tr')
      (STEP: Thread.step pf e e2 (Thread.mk _ st3 lc3 sc3 memory3))
      (TR: tr = tr'++[((Thread.local e2), e)])
      (CONSISTENT: forall (EVENT: ThreadEvent.get_machine_event e <> MachineEvent.failure),
          PF.pf_consistent L (Thread.mk _ st3 lc3 sc3 memory3))
      (PF: List.Forall (compose (PF.pf_event L) snd) tr)
    :
      step_trace tr (ThreadEvent.get_machine_event e) tid c1 (Configuration.mk (IdentMap.add tid (existT _ _ st3, lc3) (Configuration.threads c1)) sc3 memory3)
  .

  Lemma trace_step_step_trace c1 c2 tr e tid
        (STEP: Trace.configuration_step tr e tid c1 c2)
        (WF: Configuration.wf c1)
        (PF: PF.pf_configuration L c1)
        (TRACE: List.Forall (compose (PF.pf_event L) snd) tr)
    :
      step_trace tr e tid c1 c2.
  Proof.
    inv STEP. econs; eauto. i.
    eapply Forall_app_inv in TRACE. des. inv FORALL2.
    exploit Trace.steps_future; eauto; try eapply WF; eauto. ss. i. des.
    exploit Thread.step_future; eauto. ss. i. des.
    hexploit PF.pf_promises_trace_steps; eauto. i. ss.
    hexploit PF.pf_promises_step; eauto. i. ss.
    eapply PF.pf_promises_consistent_consistent; eauto.
  Qed.

  Lemma step_trace_trace_step c1 c2 tr e tid
        (STEP: step_trace tr e tid c1 c2)
        (WF: Configuration.wf c1)
    :
      (<<STEP: Trace.configuration_step tr e tid c1 c2>>) /\
      (<<TRACE: List.Forall (compose (PF.pf_event L) snd) tr>>).
  Proof.
    inv STEP. splits; auto. econs; eauto. i.
    eapply PF.pf_consistent_consistent; eauto.
  Qed.

  Inductive opt_step_trace: forall (tr: Trace.t) (e:MachineEvent.t) (tid:Ident.t) (c1 c2:Configuration.t), Prop :=
  | opt_step_trace_some
      tr e tid c1 c2
      (STEP: step_trace tr e tid c1 c2)
    :
      opt_step_trace tr e tid c1 c2
  | opt_step_trace_none
      tid c1
    :
      opt_step_trace [] MachineEvent.silent tid c1 c1
  .

  Lemma step_trace_step tr e tid c1 c2
        (STEP: step_trace tr e tid c1 c2)
    :
      Configuration.step e tid c1 c2.
  Proof.
    inv STEP. econs; try apply STEP0; eauto.
    - eapply Trace.silent_steps_tau_steps; eauto.
    - i. exploit CONSISTENT; eauto.
      i. unfold PF.pf_consistent in *. des.
      eapply Trace.consistent_thread_consistent; eauto.
  Qed.

  Inductive steps_trace:
    forall (c0 c1: Configuration.t) (tr: Trace.t), Prop :=
  | steps_trace_nil
      c0
    :
      steps_trace c0 c0 []
  | steps_trace_cons
      c0 c1 c2 trs tr e tid
      (STEPS: steps_trace c1 c2 trs)
      (STEP: step_trace tr e tid c0 c1)
    :
      steps_trace c0 c2 (tr ++ trs)
  .

  (* Lemma step_trace_steps tr e tid c1 c3 *)
  (*       (STEP: step_trace tr e tid c1 c3) *)
  (*       (WF: Configuration.wf c1) *)
  (*       (PF: PF.pf_configuration L c1) *)
  (*   : *)
  (*     ((<<STEPS: steps (List.filter ThreadEvent.is_normal_dec (List.map snd tr)) tid c1 c3>>) /\ *)
  (*      (<<NIL: List.filter ThreadEvent.is_normal_dec (List.map snd tr) <> []>>)) \/ *)
  (*     ((<<STEP: SConfiguration.reservation_only_step tid c1 c3>>) /\ *)
  (*      (<<NIL: List.filter ThreadEvent.is_normal_dec (List.map snd tr) = []>>)). *)
  (* Proof. *)
  (*   eapply step_trace_trace_step in STEP; eauto. des. *)
  (*   eapply SConfiguration.trace_step_machine_step in STEP0; eauto. des; eauto. *)
  (*   left. splits; auto. clear e. *)
  (*   remember (List.filter (fun e => ThreadEvent.is_normal_dec e) (List.map snd tr)). *)
  (*   assert (EVENTS: List.Forall (PF.pf_event L) l). *)
  (*   { subst. clear - TRACE. induction tr; ss. inv TRACE. des_ifs; eauto. } *)
  (*   clear tr Heql NIL TRACE. ginduction STEPS; eauto. *)
  (*   i. inv EVENTS. *)
  (*   eapply event_configuration_step_step in STEP; eauto. *)
  (*   exploit step_future; eauto. i. des. *)
  (*   hexploit pf_configuration_step; eauto. *)
  (* Qed. *)

  (* Lemma step_trace_future *)
  (*       (tr: Trace.t) e tid c1 c2 *)
  (*       (STEP: step_trace tr e tid c1 c2) *)
  (*       (WF1: Configuration.wf c1) *)
  (*       (PF: PF.pf_configuration L c1): *)
  (*   (<<WF2: Configuration.wf c2>>) /\ *)
  (*   (<<SC_FUTURE: TimeMap.le (Configuration.sc c1) (Configuration.sc c2)>>) /\ *)
  (*   (<<MEM_FUTURE: Memory.future (Configuration.memory c1) (Configuration.memory c2)>>) /\ *)
  (*   (<<PF: PF.pf_configuration L c2>>). *)
  (* Proof. *)
  (*   eapply step_trace_steps in STEP; eauto. des. *)
  (*   { eapply steps_future; eauto. } *)
  (*   { eapply reservation_only_step_step in STEP0; eauto. *)
  (*     eapply step_future; eauto. } *)
  (* Qed. *)

  (* Lemma opt_step_trace_future *)
  (*       (tr: Trace.t) e tid c1 c2 *)
  (*       (STEP: opt_step_trace tr e tid c1 c2) *)
  (*       (WF1: Configuration.wf c1) *)
  (*       (PF: PF.pf_configuration L c1): *)
  (*   (<<WF2: Configuration.wf c2>>) /\ *)
  (*   (<<SC_FUTURE: TimeMap.le (Configuration.sc c1) (Configuration.sc c2)>>) /\ *)
  (*   (<<MEM_FUTURE: Memory.future (Configuration.memory c1) (Configuration.memory c2)>>) /\ *)
  (*   (<<PF: PF.pf_configuration L c2>>). *)
  (* Proof. *)
  (*   inv STEP. *)
  (*   { eapply step_trace_future; eauto. } *)
  (*   { splits; auto. refl. } *)
  (* Qed. *)

  (* Lemma steps_trace_future *)
  (*       c1 c2 tr *)
  (*       (STEPS: steps_trace c1 c2 tr) *)
  (*       (WF1: Configuration.wf c1) *)
  (*       (PF: PF.pf_configuration L c1): *)
  (*   (<<WF2: Configuration.wf c2>>) /\ *)
  (*   (<<SC_FUTURE: TimeMap.le (Configuration.sc c1) (Configuration.sc c2)>>) /\ *)
  (*   (<<MEM_FUTURE: Memory.future (Configuration.memory c1) (Configuration.memory c2)>>) /\ *)
  (*   (<<PF: PF.pf_configuration L c2>>). *)
  (* Proof. *)
  (*   revert WF1. induction STEPS; i. *)
  (*   - splits; ss; refl. *)
  (*   - exploit step_trace_future; eauto. i. des. *)
  (*     exploit IHSTEPS; eauto. i. des. *)
  (*     splits; ss; etrans; eauto. *)
  (* Qed. *)

  Lemma steps_trace_n1 c0 c1 c2 tr trs e tid
        (STEPS: steps_trace c0 c1 trs)
        (STEP: step_trace tr e tid c1 c2)
    :
      steps_trace c0 c2 (trs ++ tr).
  Proof.
    ginduction STEPS.
    { i. exploit steps_trace_cons.
      { econs 1. }
      { eapply STEP. }
      { i. ss. erewrite List.app_nil_r in *. auto. }
    }
    { i. exploit IHSTEPS; eauto. i. erewrite <- List.app_assoc. econs; eauto. }
  Qed.

  Lemma steps_trace_trans c0 c1 c2 trs0 trs1
        (STEPS0: steps_trace c0 c1 trs0)
        (STEPS1: steps_trace c1 c2 trs1)
    :
      steps_trace c0 c2 (trs0 ++ trs1).
  Proof.
    ginduction STEPS0.
    { i. erewrite List.app_nil_l. eauto. }
    { i. exploit IHSTEPS0; eauto. i. erewrite <- List.app_assoc. econs; eauto. }
  Qed.

  Lemma step_trace_steps_trace tr e tid c1 c2
        (STEP: step_trace tr e tid c1 c2)
    :
      steps_trace c1 c2 tr.
  Proof.
    exploit steps_trace_cons.
    { econs 1. }
    { eauto. }
    i. rewrite List.app_nil_r in x0. auto.
  Qed.

  Lemma opt_step_trace_steps_trace tr e tid c1 c2
        (STEP: opt_step_trace tr e tid c1 c2)
    :
      steps_trace c1 c2 tr.
  Proof.
    inv STEP.
    { eapply step_trace_steps_trace; eauto. }
    { econs 1. }
  Qed.

  Inductive silent_steps_trace:
    forall (c0 c1: Configuration.t) (tr: Trace.t), Prop :=
  | silent_steps_trace_nil
      c0
    :
      silent_steps_trace c0 c0 []
  | silent_steps_trace_cons
      c0 c1 c2 trs tr tid
      (STEPS: silent_steps_trace c1 c2 trs)
      (STEP: step_trace tr MachineEvent.silent tid c0 c1)
    :
      silent_steps_trace c0 c2 (tr ++ trs)
  .

  Lemma silent_steps_trace_steps_trace
    :
      silent_steps_trace <3= steps_trace.
  Proof.
    intros. induction PR.
    { econs. }
    { econs; eauto. }
  Qed.

  Inductive steps_trace_rev: forall (c1 c2: Configuration.t) (tr: Trace.t), Prop :=
  | steps_trace_rev_nil
      c:
      steps_trace_rev c c []
  | steps_trace_rev_cons
      c1 c2 c3 tr1 tr2 e tid
      (STEPS: steps_trace_rev c1 c2 tr1)
      (STEP: step_trace tr2 e tid c2 c3):
      steps_trace_rev c1 c3 (tr1 ++ tr2)
  .
  Hint Constructors steps_trace_rev.

  Lemma steps_trace_rev_1n
        c1 c2 c3 tr1 tr2 e tid
        (STEP: step_trace tr1 e tid c1 c2)
        (STEPS: steps_trace_rev c2 c3 tr2):
    steps_trace_rev c1 c3 (tr1 ++ tr2).
  Proof.
    revert tr1 e tid c1 STEP. induction STEPS; i.
    - replace (tr1 ++ []) with ([] ++ tr1) by (rewrite List.app_nil_r; ss).
      econs 2; [econs 1|]. eauto.
    - exploit IHSTEPS; eauto. i.
      rewrite List.app_assoc.
      econs 2; eauto.
  Qed.

  Lemma steps_trace_equiv c1 c2 tr:
    steps_trace c1 c2 tr <-> steps_trace_rev c1 c2 tr.
  Proof.
    split; i.
    - induction H; eauto.
      eapply steps_trace_rev_1n; eauto.
    - induction H; [econs 1|].
      eapply steps_trace_n1; eauto.
  Qed.

  (* Lemma steps_trace_inv *)
  (*       c1 c2 tr lc e *)
  (*       (STEPS: steps_trace c1 c2 tr) *)
  (*       (WF: Configuration.wf c1) *)
  (*       (PF: PF.pf_configuration L c1) *)
  (*       (TRACE: List.In (lc, e) tr): *)
  (*   exists c tr1 tid lang st1 lc1, *)
  (*     (<<STEPS: steps_trace c1 c tr1>>) /\ *)
  (*     (<<FIND: IdentMap.find tid (Configuration.threads c) = Some (existT _ lang st1, lc1)>>) /\ *)
  (*     exists tr2 pf e2 e3, *)
  (*       (<<THREAD_STEPS: Trace.steps tr2 (Thread.mk _ st1 lc1 (Configuration.sc c) (Configuration.memory c)) e2>>) /\ *)
  (*       (<<SILENT: List.Forall (fun the => ThreadEvent.get_machine_event (snd the) = MachineEvent.silent) tr2>>) /\ *)
  (*       (<<PF: List.Forall (compose (PF.pf_event L) snd) tr2>>) /\ *)
  (*       (<<LC: (Thread.local e2) = lc>>) /\ *)
  (*       (<<THREAD_STEP: Thread.step pf e e2 e3>>) /\ *)
  (*       (<<CONS: Local.promise_consistent (Thread.local e3)>>). *)
  (* Proof. *)
  (*   rewrite steps_trace_equiv in STEPS. *)
  (*   induction STEPS; ss. *)
  (*   apply List.in_app_or in TRACE. des; eauto. *)
  (*   clear IHSTEPS. inv STEP. *)
  (*   exists c2, tr1, tid, lang, st1, lc1. *)
  (*   rewrite <- steps_trace_equiv in STEPS. *)
  (*   splits; ss. *)
  (*   apply List.in_app_or in TRACE. des; cycle 1. *)
  (*   { inv TRACE; ss. inv H. esplits; eauto. *)
  (*     - apply Forall_app_inv in PF0. des. ss. *)
  (*     - destruct (classic (ThreadEvent.get_machine_event e = MachineEvent.failure)). *)
  (*       + destruct e; ss; inv STEP0; inv STEP; inv LOCAL; inv LOCAL0; ss. *)
  (*       + exploit CONSISTENT; eauto. i. inv x. des. *)
  (*         exploit steps_trace_future; eauto. i. des. *)
  (*         inv WF2. inv WF0. exploit THREADS; eauto. i. *)
  (*         exploit Trace.steps_future; try exact STEPS0; eauto. s. i. des. *)
  (*         exploit Thread.step_future; try exact STEP0; eauto. s. i. des. *)
  (*         hexploit consistent_promise_consistent; *)
  (*           try eapply Trace.consistent_thread_consistent; try exact CONSISTENT0; eauto. *)
  (*   } *)
  (*   exploit steps_trace_future; eauto. i. des. *)
  (*   inv WF2. inv WF0. exploit THREADS; eauto. i. clear DISJOINT THREADS. *)
  (*   exploit Trace.steps_inv; try exact STEPS0; eauto. *)
  (*   { destruct (classic (e1 = ThreadEvent.failure)). *)
  (*     - subst. inv STEP0; inv STEP. inv LOCAL. inv LOCAL0. ss. *)
  (*     - exploit CONSISTENT; ss. i. inv x0. des. *)
  (*       exploit Trace.steps_future; eauto. s. i. des. *)
  (*       exploit Thread.step_future; eauto. s. i. des. *)
  (*       eapply step_promise_consistent; eauto. *)
  (*       eapply consistent_promise_consistent; eauto. *)
  (*       eapply Trace.consistent_thread_consistent; eauto. *)
  (*   } *)
  (*   i. des. esplits; eauto; subst. *)
  (*   - apply Forall_app_inv in SILENT. des. ss. *)
  (*   - apply Forall_app_inv in PF0. des. *)
  (*     apply Forall_app_inv in FORALL1. des. ss. *)
  (* Qed. *)

  Inductive multi_step (e:MachineEvent.t) (tid:Ident.t) (c1 c2:Configuration.t): Prop :=
  | multi_step_intro
      tr
      (STEP: step_trace tr e tid c1 c2)
  .

  (* Lemma multi_step_machine_step e tid c1 c3 *)
  (*       (STEP: multi_step e tid c1 c3) *)
  (*       (WF: Configuration.wf c1) *)
  (*       (PF: PF.pf_configuration L c1) *)
  (*   : *)
  (*     exists c2, *)
  (*       (<<STEPS: rtc tau_machine_step c1 c2>>) /\ *)
  (*       (<<STEP: opt_machine_step e tid c2 c3>>). *)
  (* Proof. *)
  (*   inv STEP. exploit step_trace_steps; eauto. i. des. *)
  (*   { inv STEP0. *)
  (*     rewrite List.map_app in *. *)
  (*     rewrite list_filter_app in *. ss. *)
  (*     eapply steps_split in STEPS. des. exists c0. splits. *)
  (*     { eapply rtc_implies with (R1:=(machine_step MachineEvent.silent tid)). *)
  (*       { clear. i. econs; eauto. } *)
  (*       eapply silent_steps_tau_machine_steps; eauto. *)
  (*       eapply list_filter_forall with (Q:=fun e => ThreadEvent.get_machine_event e = MachineEvent.silent); eauto. *)
  (*       eapply list_map_forall; eauto. *)
  (*     } *)
  (*     unfold proj_sumbool in *. des_ifs. *)
  (*     { inv STEPS2. inv STEPS. *)
  (*       econs 2. econs; eauto. } *)
  (*     { inv STEPS2. *)
  (*       replace (ThreadEvent.get_machine_event e0) with MachineEvent.silent; eauto. *)
  (*       apply NNPP in n. *)
  (*       unfold ThreadEvent.is_reservation_event, ThreadEvent.is_reserve, ThreadEvent.is_cancel in n. *)
  (*       des; des_ifs. *)
  (*     } *)
  (*   } *)
  (*   { eapply SConfiguration.reservation_only_step_step in STEP. *)
  (*     eapply event_configuration_step_step in STEP; eauto; ss. *)
  (*     exists c1. esplits; eauto. *)
  (*     replace e with (ThreadEvent.get_machine_event ThreadEvent.silent); eauto. *)
  (*     ss. inv STEP0. *)
  (*     rewrite List.map_app in NIL. *)
  (*     rewrite list_filter_app in NIL. *)
  (*     eapply List.app_eq_nil in NIL. *)
  (*     ss. unfold proj_sumbool in NIL. des. des_ifs. *)
  (*     apply NNPP in n. *)
  (*     unfold ThreadEvent.is_reservation_event, ThreadEvent.is_reserve, ThreadEvent.is_cancel in n. *)
  (*     des; des_ifs. *)
  (*   } *)
  (* Qed. *)

  (* Lemma multi_step_future *)
  (*       e tid c1 c2 *)
  (*       (STEP: multi_step e tid c1 c2) *)
  (*       (WF1: Configuration.wf c1) *)
  (*       (PF: PF.pf_configuration L c1): *)
  (*   (<<WF2: Configuration.wf c2>>) /\ *)
  (*   (<<SC_FUTURE: TimeMap.le (Configuration.sc c1) (Configuration.sc c2)>>) /\ *)
  (*   (<<MEM_FUTURE: Memory.future (Configuration.memory c1) (Configuration.memory c2)>>) /\ *)
  (*   (<<PF: PF.pf_configuration L c2>>). *)
  (* Proof. *)
  (*   inv STEP. eapply step_trace_future; eauto. *)
  (* Qed. *)

  Lemma silent_multi_steps_trace_behaviors c0 c1 tr
        (STEP: silent_steps_trace c0 c1 tr)
    :
      behaviors multi_step c1 <2= behaviors multi_step c0.
  Proof.
    ginduction STEP; auto.
    i. eapply IHSTEP in PR. econs 4; eauto.
    econs. esplits; eauto.
  Qed.

  (* Lemma multi_step_behavior c *)
  (*       (WF: Configuration.wf c) *)
  (*       (PF: PF.pf_configuration L c) *)
  (*   : *)
  (*     behaviors multi_step c <2= behaviors machine_step c. *)
  (* Proof. *)
  (*   i. induction PR. *)
  (*   - econs 1; eauto. *)
  (*   - exploit multi_step_future; eauto. i. des. *)
  (*     eapply multi_step_machine_step in STEP; eauto. des. *)
  (*     eapply rtc_tau_step_behavior; eauto. *)
  (*     inv STEP0; eauto. econs 2; eauto. *)
  (*   - exploit multi_step_future; eauto. i. des. *)
  (*     eapply multi_step_machine_step in STEP; eauto. des. *)
  (*     eapply rtc_tau_step_behavior; eauto. *)
  (*     inv STEP0; eauto. econs 3; eauto. *)
  (*   - exploit multi_step_future; eauto. i. des. *)
  (*     eapply multi_step_machine_step in STEP; eauto. des. *)
  (*     eapply rtc_tau_step_behavior; eauto. *)
  (*     inv STEP0; eauto. econs 4; eauto. *)
  (* Qed. *)

End LOCALPF.
End PFConfiguration.


(** L-PF race **)
Module PFRace.
Section LOCALPFRACE.
  Variable L: Loc.t -> bool.

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

  Definition racy_execution (c0: Configuration.t): Prop :=
    forall tid0 c1 tid1 c2 c3
           loc ts e0 e1
           (LOC: L loc)
           (TID: tid0 <> tid1)
           (CSTEP0: PFConfiguration.step L e0 tid0 c0 c1)
           (WRITE: writing_event loc ts e0)
           (STEPS: rtc (PFConfiguration.machine_step L MachineEvent.silent tid1) c1 c2)
           (CSTEP1: PFConfiguration.step L e1 tid1 c2 c3)
           (READ: reading_event loc ts e1),
      False.

  Definition racefree (c0: Configuration.t): Prop :=
    forall c1
           (CSTEPS: rtc (PFConfiguration.all_step L) c0 c1),
      racy_execution c1.

  Definition racefree_syn (syn: Threads.syntax): Prop :=
    racefree (Configuration.init syn).

  Inductive racy_state (c0: Configuration.t): Prop :=
  | race_intro
      c1 c2
      tid0 tid1 e0 e1
      lang st0 lc0 th1 th2
      tr pf loc ts
      (STEPS: rtc (PFConfiguration.machine_step L MachineEvent.silent tid0) c0 c1)
      (WRITE_STEP: PFConfiguration.step L e0 tid0 c1 c2)
      (WRITE: writing_event loc ts e0)
      (FIND: IdentMap.find tid1 (Configuration.threads c2) = Some (existT _ lang st0, lc0))
      (THREAD_STEPS: Trace.steps tr (Thread.mk _ st0 lc0 (Configuration.sc c2) (Configuration.memory c2)) th1)
      (PF: List.Forall (compose (PF.pf_event L) snd) tr)
      (CONS: Local.promise_consistent (Thread.local th1))
      (READ_STEP: Thread.step pf e1 th1 th2)
      (READ: reading_event loc ts e1)
      (LOC: L loc)
  .

  Lemma step_racefree c0 c1 e tid
        (RACEFREE: racefree c0)
        (STEP: PFConfiguration.step L e tid c0 c1)
    :
      racefree c1.
  Proof.
    unfold racefree in *. i.
    eapply RACEFREE. econs 2; eauto. econs; eauto.
  Qed.

  Lemma rtc_tau_machine_step_racefree c0 c1
        (RACEFREE: racefree c0)
        (STEP: rtc (PFConfiguration.tau_machine_step L) c0 c1)
    :
      racefree c1.
  Proof.
    ginduction STEP; eauto.
    i. eapply IHSTEP. inv H. inv USTEP.
    eapply step_racefree; eauto.
  Qed.

  Lemma steps_racefree es tid c0 c1
        (RACEFREE: racefree c0)
        (STEPS: PFConfiguration.steps L es tid c0 c1)
    :
      racefree c1.
  Proof.
    ginduction STEPS; eauto.
    i. eapply IHSTEPS.
    eapply step_racefree; eauto.
  Qed.

  Inductive multi_race (c0: Configuration.t): Prop :=
  | multi_race_intro
      c1
      tid0 tid1 e0 e1
      lang st0 lc0 th1 th2
      e trs tr pf loc ts
      (STEPS: PFConfiguration.step_trace L trs e tid0 c0 c1)
      (TRACE: final_event_trace e0 trs)
      (WRITE: writing_event loc ts e0)
      (FIND: IdentMap.find tid1 (Configuration.threads c1) = Some (existT _ lang st0, lc0))
      (THREAD_STEPS: Trace.steps tr (Thread.mk _ st0 lc0 (Configuration.sc c1) (Configuration.memory c1)) th1)
      (PF: List.Forall (compose (PF.pf_event L) snd) tr)
      (CONS: Local.promise_consistent (Thread.local th1))
      (READ_STEP: Thread.step pf e1 th1 th2)
      (READ: reading_event loc ts e1)
      (LOC: L loc)
  .

  Definition multi_racefree_imm (c0: Configuration.t): Prop :=
    forall tid0 c1 trs0 tid1 c2 trs1
           loc ts lc1 te0 te1 e0 e1
           (LOC: L loc)
           (TID: tid0 <> tid1)
           (CSTEP0: PFConfiguration.step_trace L trs0 e0 tid0 c0 c1)
           (WRITE: writing_event loc ts te0)
           (TRACE0: final_event_trace te0 trs0)
           (CSTEP1: PFConfiguration.step_trace L trs1 e1 tid1 c1 c2)
           (READ: reading_event loc ts te1)
           (TRACE1: List.In (lc1, te1) trs1),
      False.

  Definition multi_racefree (c0: Configuration.t): Prop :=
    forall c1 trs
           (CSTEPS: PFConfiguration.steps_trace L c0 c1 trs),
      multi_racefree_imm c1.

  Lemma multi_step_multi_racefree c0 c1 tr e tid
        (RACEFREE: multi_racefree c0)
        (STEP: PFConfiguration.step_trace L tr e tid c0 c1)
    :
      multi_racefree c1.
  Proof.
    unfold multi_racefree in *. i.
    eapply RACEFREE. econs 2; eauto.
  Qed.

  Lemma multi_steps_multi_racefree c0 c1 trs
        (RACEFREE: multi_racefree c0)
        (STEPS: PFConfiguration.steps_trace L c0 c1 trs)
    :
      multi_racefree c1.
  Proof.
    induction STEPS; auto. eapply IHSTEPS.
    eapply multi_step_multi_racefree; eauto.
  Qed.

  (* Lemma racefree_multi_racefree_imm c *)
  (*       (RACEFREE: racefree c) *)
  (*       (WF: Configuration.wf c) *)
  (*       (PF: PF.pf_configuration L c) *)
  (*   : *)
  (*     multi_racefree_imm c. *)
  (* Proof. *)
  (*   ii. exploit PFConfiguration.step_trace_future; try apply CSTEP0; eauto.  i. des. *)
  (*   exploit final_event_trace_filter; eauto. *)
  (*   { unfold ThreadEvent.is_normal, ThreadEvent.is_reservation_event. *)
  (*     inv WRITE; ss; ii; des; ss. } i. des. *)
  (*   eapply PFConfiguration.step_trace_steps in CSTEP0; eauto. *)
  (*   rewrite FILTER in *. des; cycle 1. *)
  (*   { eapply List.app_eq_nil in NIL. des; ss. } *)
  (*   eapply PFConfiguration.steps_split in STEPS. des. inv STEPS1. inv STEPS. *)
  (*   eapply List.in_split in TRACE1. des; subst. *)
  (*   dup CSTEP1. eapply PFConfiguration.step_trace_steps in CSTEP1; eauto. *)
  (*   rewrite List.map_app in *. *)
  (*   rewrite list_filter_app in *. ss. unfold proj_sumbool in *. *)
  (*   des_ifs; cycle 1. *)
  (*   { clear - READ n. apply NNPP in n. *)
  (*     unfold ThreadEvent.is_normal, ThreadEvent.is_reservation_event in *. *)
  (*     inv READ; ss; ii; des; ss. } *)
  (*   des; cycle 1. *)
  (*   { eapply List.app_eq_nil in NIL0. des; ss. } *)
  (*   eapply PFConfiguration.steps_split in STEPS. des. inv STEPS2. *)
  (*   eapply RACEFREE; try eassumption. *)
  (*   { eapply PFConfiguration.steps_rtc_all_step; eauto. } *)
  (*   { eapply PFConfiguration.silent_steps_tau_machine_steps; eauto. *)
  (*     clear - CSTEP0. inv CSTEP0. *)
  (*     destruct (list_match_rev l2); des; subst. *)
  (*     { eapply List.app_inj_tail in TR. des; clarify. *)
  (*       eapply List.Forall_forall. ii. *)
  (*       eapply List.filter_In in H. des. *)
  (*       eapply List.in_map_iff in H. des; subst. *)
  (*       eapply List.Forall_forall in SILENT; eauto. } *)
  (*     { rewrite List.app_comm_cons in TR. *)
  (*       rewrite List.app_assoc in TR. *)
  (*       eapply List.app_inj_tail in TR. des; clarify. *)
  (*       eapply Forall_app_inv in SILENT. des. *)
  (*       eapply List.Forall_forall. ii. *)
  (*       eapply List.filter_In in H. des. *)
  (*       eapply List.in_map_iff in H. des; subst. *)
  (*       eapply List.Forall_forall in FORALL1; eauto. } *)
  (*   } *)
  (* Qed. *)

  (* Lemma racefree_multi_racefree c *)
  (*       (RACEFREE: racefree c) *)
  (*       (WF: Configuration.wf c) *)
  (*       (PF: PF.pf_configuration L c) *)
  (*   : *)
  (*     multi_racefree c. *)
  (* Proof. *)
  (*   unfold multi_racefree. i. *)
  (*   ginduction CSTEPS; eauto. *)
  (*   { i. eapply racefree_multi_racefree_imm; eauto. } *)
  (*   { i. exploit PFConfiguration.step_trace_future; eauto. *)
  (*     i. des. eapply IHCSTEPS; eauto. *)
  (*     eapply PFConfiguration.step_trace_steps in STEP; eauto. des. *)
  (*     { eapply steps_racefree; eauto. } *)
  (*     { eapply PFConfiguration.reservation_only_step_step in STEP0; eauto. *)
  (*       eapply step_racefree; eauto. } *)
  (*   } *)
  (* Qed. *)

  (* Lemma multi_race_race c *)
  (*       (RACE: multi_race c) *)
  (*       (WF: Configuration.wf c) *)
  (*       (PF: PF.pf_configuration L c) *)
  (*   : *)
  (*     racy_state c. *)
  (* Proof. *)
  (*   inv RACE. *)
  (*   exploit PFConfiguration.step_trace_future; try apply STEPS; eauto. i. des. *)
  (*   exploit final_event_trace_filter; eauto. *)
  (*   { ii. inv WRITE; eauto. } i. des. *)
  (*   dup STEPS. eapply PFConfiguration.step_trace_steps in STEPS; eauto. *)
  (*   rewrite FILTER in *. des; cycle 1. *)
  (*   { eapply List.app_eq_nil in NIL. des; ss. } *)
  (*   eapply PFConfiguration.steps_split in STEPS1. des. inv STEPS3. inv STEPS. *)
  (*   econs; cycle 1; eauto. *)
  (*   eapply PFConfiguration.silent_steps_tau_machine_steps; eauto. *)
  (*   assert (exists trs_hd trs_tl, *)
  (*              (<<TRS: trs = trs_hd ++ [trs_tl]>>) /\ *)
  (*              (<<SILENT: List.Forall (fun the => ThreadEvent.get_machine_event (snd the) = MachineEvent.silent) trs_hd>>)). *)
  (*   { inv STEPS0. eauto. } clear STEPS0. des. subst. *)
  (*   erewrite List.map_app in FILTER. erewrite list_filter_app in FILTER. *)
  (*   assert (exists tl, *)
  (*              tr_hd ++ tl = List.filter (fun e => ThreadEvent.is_normal_dec e) (List.map snd trs_hd)). *)
  (*   { ss. des_ifs. *)
  (*     - exists []. rewrite List.app_nil_r. *)
  (*       eapply List.app_inj_tail in FILTER. des. auto. *)
  (*     - exists [e0]. rewrite <- FILTER. rewrite List.app_nil_r. auto. *)
  (*   } *)
  (*   des. exploit Forall_app_inv; cycle 1. *)
  (*   { i. des. eapply FORALL1. } *)
  (*   { rewrite H. eapply List.Forall_forall. i. *)
  (*     eapply List.filter_In in H0. des. *)
  (*     eapply List.in_map_iff in H0. des. subst. *)
  (*     eapply List.Forall_forall in SILENT; eauto. *)
  (*   } *)
  (* Qed. *)

  Inductive racy_read (loc: Loc.t) (ts: Time.t):
    forall (lc: Local.t) (e: ThreadEvent.t), Prop :=
  | racy_read_read
      lc
      valr releasedr ordr
      (VIEW:
         Time.lt (if Ordering.le Ordering.relaxed ordr
                  then ((TView.cur (Local.tview lc)).(View.rlx) loc)
                  else ((TView.cur (Local.tview lc)).(View.pln) loc)) ts)
    :
      racy_read loc ts lc (ThreadEvent.read loc ts valr releasedr ordr)
  | racy_read_update
      lc
      to valr valw releasedr releasedw ordr ordw
      (VIEW:
         Time.lt (if Ordering.le Ordering.relaxed ordr
                  then ((TView.cur (Local.tview lc)).(View.rlx) loc)
                  else ((TView.cur (Local.tview lc)).(View.pln) loc)) ts)
    :
      racy_read loc ts lc (ThreadEvent.update loc ts to valr valw releasedr releasedw ordr ordw)
  .

  Definition multi_racefree_view (c0: Configuration.t): Prop :=
    forall c1 trs1 c2 trs2
      loc ts lc0 lc1 e0 e1
      (CSTEPS1: PFConfiguration.steps_trace L c0 c1 trs1)
      (LOC: L loc)
      (TRACE1: List.In (lc0, e0) trs1)
      (WRITE: writing_event loc ts e0)
      (CSTEPS2: PFConfiguration.steps_trace L c1 c2 trs2)
      (TRACE2: List.In (lc1, e1) trs2)
      (READ: racy_read loc ts lc1 e1),
      False.

  Lemma multi_step_multi_racefree_view c0 c1 tr e tid
        (RACEFREE: multi_racefree_view c0)
        (STEP: PFConfiguration.step_trace L tr e tid c0 c1)
    :
      multi_racefree_view c1.
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

  Lemma multi_steps_multi_racefree_view c0 c1 trs
        (RACEFREE: multi_racefree_view c0)
        (STEPS: PFConfiguration.steps_trace L c0 c1 trs)
    :
      multi_racefree_view c1.
  Proof.
    induction STEPS; auto. eapply IHSTEPS.
    eapply multi_step_multi_racefree_view; eauto.
  Qed.

  Inductive racy_read_step:
    forall (loc: Loc.t) (ts: Time.t)
           (e:ThreadEvent.t) (tid:Ident.t) (c1 c2:Configuration.t), Prop :=
  | racy_read_step_intro
      loc ts e tid c1 lang st1 lc1 e2 e3 st4 lc4 sc4 memory4
      (TID: IdentMap.find tid (Configuration.threads c1) = Some (existT _ lang st1, lc1))
      (CANCELS: rtc (@Thread.cancel_step _) (Thread.mk _ st1 lc1 (Configuration.sc c1) (Configuration.memory c1)) e2)
      (STEP: Thread.opt_step e e2 e3)
      (RESERVES: rtc (@Thread.reserve_step _) e3 (Thread.mk _ st4 lc4 sc4 memory4))
      (CONSISTENT: e <> ThreadEvent.failure -> PF.pf_consistent L (Thread.mk _ st4 lc4 sc4 memory4))
      (PF: PF.pf_event L e)
      (READ: racy_read loc ts (Thread.local e2) e)
    :
      racy_read_step loc ts e tid c1 (Configuration.mk (IdentMap.add tid (existT _ _ st4, lc4) (Configuration.threads c1)) sc4 memory4)
  .
  Hint Constructors racy_read_step.

  Inductive racy_write_step:
    forall (loc: Loc.t) (ts: Time.t)
           (e:ThreadEvent.t) (tid:Ident.t) (c1 c2:Configuration.t), Prop :=
  | racy_write_step_intro
      loc ts e tid c1 c2
      (STEP: PFConfiguration.step L e tid c1 c2)
      (WRITE: writing_event loc ts e)
    :
      racy_write_step loc ts e tid c1 c2
  .

  Definition racefree_view (c0: Configuration.t): Prop :=
    forall c1 c2 c3 c4 loc ts e0 e1 tid0 tid1
      (LOC: L loc)
      (CSTEPS1: rtc (PFConfiguration.all_step L) c0 c1)
      (WRITE: racy_write_step loc ts e0 tid0 c1 c2)
      (CSTEPS2: rtc (PFConfiguration.all_step L) c2 c3)
      (READ: racy_read_step loc ts e1 tid1 c3 c4),
      False.

  Definition racefree_view_syn (syn: Threads.syntax): Prop :=
    racefree_view (Configuration.init syn).

  Lemma step_racefree_view c0 c1 e tid
        (RACEFREE: racefree_view c0)
        (STEP: PFConfiguration.step L e tid c0 c1)
    :
      racefree_view c1.
  Proof.
    ii. eapply RACEFREE; cycle 2; eauto.
    econs; eauto. econs; eauto.
  Qed.

  Lemma steps_racefree_view c0 c1
        (RACEFREE: racefree_view c0)
        (STEPS: rtc (PFConfiguration.all_step L) c0 c1)
    :
      racefree_view c1.
  Proof.
    ii. eapply RACEFREE; cycle 2; eauto. etrans; eauto.
  Qed.

End LOCALPFRACE.
End PFRace.
