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

Require Import Pred.
Require Import Trace.
Require Import OrderedTimes.
Require Import PFConsistentStrong.

Set Implicit Arguments.



Inductive times_configuration_step_strong (times: Loc.t -> Time.t -> Prop)
  : forall (tr tr_cert: Trace.t)
           (e:MachineEvent.t) (tid:Ident.t) (c1 c2:Configuration.t), Prop :=
| times_configuration_step_strong_intro
    lang tr e tr' pf tid c1 st1 lc1 e2 st3 lc3 sc3 memory3 tr_cert
    (TID: IdentMap.find tid (Configuration.threads c1) = Some (existT _ lang st1, lc1))
    (STEPS: Trace.steps tr' (Thread.mk _ st1 lc1 (Configuration.sc c1) (Configuration.memory c1)) e2)
    (SILENT: List.Forall (fun the => ThreadEvent.get_machine_event (snd the) = MachineEvent.silent) tr')
    (STEP: Thread.step pf e e2 (Thread.mk _ st3 lc3 sc3 memory3))
    (TR: tr = tr'++[((Thread.local e2), e)])
    (CONSISTENT: forall (EVENT: ThreadEvent.get_machine_event e <> MachineEvent.failure),
        pf_consistent_super_strong (Thread.mk _ st3 lc3 sc3 memory3) tr_cert times)
    (CERTBOT: ThreadEvent.get_machine_event e = MachineEvent.failure \/ (exists se, e = ThreadEvent.syscall se) -> tr_cert = [])
    (CERTBOTNIL: (Local.promises lc3) = Memory.bot -> tr_cert = [])
    (TIMES: List.Forall (fun thte => wf_time_evt times (snd thte)) tr)
  :
    times_configuration_step_strong
      times tr tr_cert
      (ThreadEvent.get_machine_event e) tid c1 (Configuration.mk (IdentMap.add tid (existT _ _ st3, lc3) (Configuration.threads c1)) sc3 memory3)
.

Inductive times_configuration_step (times: Loc.t -> Time.t -> Prop)
  : forall (tr tr_cert: Trace.t)
           (e:MachineEvent.t) (tid:Ident.t) (c1 c2:Configuration.t), Prop :=
| times_configuration_step_intro
    lang tr e tr' pf tid c1 st1 lc1 e2 st3 lc3 sc3 memory3 tr_cert
    (TID: IdentMap.find tid (Configuration.threads c1) = Some (existT _ lang st1, lc1))
    (STEPS: Trace.steps tr' (Thread.mk _ st1 lc1 (Configuration.sc c1) (Configuration.memory c1)) e2)
    (SILENT: List.Forall (fun the => ThreadEvent.get_machine_event (snd the) = MachineEvent.silent) tr')
    (STEP: Thread.step pf e e2 (Thread.mk _ st3 lc3 sc3 memory3))
    (TR: tr = tr'++[((Thread.local e2), e)])
    (CONSISTENT: forall (EVENT: ThreadEvent.get_machine_event e <> MachineEvent.failure),
        pf_consistent_super_strong (Thread.mk _ st3 lc3 sc3 memory3) tr_cert times)
    (CERTBOT: ThreadEvent.get_machine_event e = MachineEvent.failure \/ (exists se, e = ThreadEvent.syscall se) -> tr_cert = [])
    (TIMES: List.Forall (fun thte => wf_time_evt times (snd thte)) tr)
  :
    times_configuration_step
      times tr tr_cert
      (ThreadEvent.get_machine_event e) tid c1 (Configuration.mk (IdentMap.add tid (existT _ _ st3, lc3) (Configuration.threads c1)) sc3 memory3)
.

Lemma times_configuration_step_strong_step
  :
    times_configuration_step_strong <7= times_configuration_step.
Proof.
  i. inv PR. econs; eauto.
Qed.

Inductive times_configuration_step_strong_all (times: Loc.t -> Time.t -> Prop)
          (e:MachineEvent.t) (tid:Ident.t) (c1 c2:Configuration.t): Prop :=
| times_configuration_step_strong_all_intro
    tr tr_cert
    (STEP: @times_configuration_step_strong times tr tr_cert e tid c1 c2)
.

Lemma times_configuration_step_configuration_step times tr tr_cert e tid c1 c2
      (STEP: @times_configuration_step times tr tr_cert e tid c1 c2)
      (WF: Configuration.wf c1)
  :
    Configuration.step e tid c1 c2.
Proof.
  inv STEP. eapply Trace.silent_steps_tau_steps in STEPS; eauto.
  destruct (classic (ThreadEvent.get_machine_event e0 = MachineEvent.failure)).
  { econs; eauto. ss. }
  { inv WF. exploit Thread.rtc_tau_step_future; ss; eauto.
    { eapply WF0; eauto. } i. des.
    exploit Thread.step_future; ss; eauto. ss. i. des.
    econs; eauto. i. eapply pf_consistent_super_strong_consistent; eauto.
  }
Qed.

Lemma times_configuration_step_future
      times tr tr_cert e tid c1 c2
      (STEP: @times_configuration_step times tr tr_cert e tid c1 c2)
      (WF1: Configuration.wf c1):
  (<<WF2: Configuration.wf c2>>) /\
  (<<SC_FUTURE: TimeMap.le (Configuration.sc c1) (Configuration.sc c2)>>) /\
  (<<MEM_FUTURE: Memory.future (Configuration.memory c1) (Configuration.memory c2)>>).
Proof.
  eapply times_configuration_step_configuration_step in STEP; eauto.
  eapply Configuration.step_future; eauto.
Qed.

Inductive times_configuration_opt_step (times: Loc.t -> Time.t -> Prop)
  : forall (tr tr_cert: Trace.t)
           (e:MachineEvent.t) (tid:Ident.t) (c1 c2:Configuration.t), Prop :=
| times_configuration_opt_step_some
    tr tr_cert e tid c1 c2
    (STEP: @times_configuration_step times tr tr_cert e tid c1 c2)
  :
    times_configuration_opt_step times tr tr_cert e tid c1 c2
| times_configuration_opt_step_none
    tid c
  :
    @times_configuration_opt_step times [] [] MachineEvent.silent tid c c
.

Lemma times_configuration_opt_step_future
      times tr tr_cert e tid c1 c2
      (STEP: @times_configuration_opt_step times tr tr_cert e tid c1 c2)
      (WF1: Configuration.wf c1):
  (<<WF2: Configuration.wf c2>>) /\
  (<<SC_FUTURE: TimeMap.le (Configuration.sc c1) (Configuration.sc c2)>>) /\
  (<<MEM_FUTURE: Memory.future (Configuration.memory c1) (Configuration.memory c2)>>).
Proof.
  inv STEP.
  { eapply times_configuration_step_future; eauto. }
  { splits; auto. refl. }
Qed.

Lemma times_configuration_step_strong_mon times0 times1
      (LE: times0 <2= times1)
  :
    times_configuration_step_strong times0 <6= times_configuration_step_strong times1.
Proof.
  i. inv PR. econs; eauto.
  { i. hexploit CONSISTENT; eauto. i. des. esplits; eauto.
    eapply pf_consistent_super_strong_mon; eauto. }
  { eapply List.Forall_impl; eauto. i. eapply wf_time_evt_mon; eauto. }
Qed.

Lemma times_configuration_step_mon times0 times1
      (LE: times0 <2= times1)
  :
    times_configuration_step times0 <6= times_configuration_step times1.
Proof.
  i. inv PR. econs; eauto.
  { i. hexploit CONSISTENT; eauto. i. des. esplits; eauto.
    eapply pf_consistent_super_strong_mon; eauto. }
  { eapply List.Forall_impl; eauto. i. eapply wf_time_evt_mon; eauto. }
Qed.

Lemma times_configuration_step_strong_all_mon times0 times1
      (LE: times0 <2= times1)
  :
    times_configuration_step_strong_all times0 <4= times_configuration_step_strong_all times1.
Proof.
  i. inv PR. econs. eapply times_configuration_step_strong_mon; eauto.
Qed.

Lemma times_configuration_step_exists c0 c1 tid e
      (STEP: Configuration.step e tid c0 c1)
      (WF: Configuration.wf c0)
  :
    exists times tr tr_cert,
      ((<<STEP: @times_configuration_step_strong times tr tr_cert e tid c0 c1>>) \/
       exists c1',
         (<<STEP: @times_configuration_step_strong times tr tr_cert MachineEvent.failure tid c0 c1'>>))
      /\
      (<<WO: forall loc, well_ordered (times loc)>>).
Proof.
  inv STEP.
  destruct (classic (Thread.steps_failure (Thread.mk _ st1 lc1 c0.(Configuration.sc) c0.(Configuration.memory)))) as [FAILURE|NFAILURE].
  { clear STEPS STEP0 EVENT. red in FAILURE. des. destruct e3.
    eapply Trace.tau_steps_silent_steps in STEPS. des.
    hexploit (trace_times_list_exists tr). i. des.
    hexploit step_times_list_exists; eauto. i. des.
    replace MachineEvent.failure with (ThreadEvent.get_machine_event e); auto.
    eexists (fun loc ts => List.In ts (times loc ++ times0 loc)), (tr++_), []. splits.
    { right. esplits. econs; eauto; ss. eapply Forall_app.
      { eapply List.Forall_impl; eauto. i. ss. eapply wf_time_evt_mon; eauto.
        i. ss. eapply List.in_or_app; eauto. }
      { econs; ss. eapply wf_time_evt_mon; eauto.
        i. ss. eapply List.in_or_app; eauto. }
    }
    { i. eapply finite_well_ordered. }
  }
  assert (NORMAL: ThreadEvent.get_machine_event e0 <> MachineEvent.failure).
  { ii. eapply NFAILURE. red. esplits; eauto.
    replace pf with true in *; eauto. inv STEP0; inv STEP; ss.
  }
  dup STEPS. eapply Trace.tau_steps_silent_steps in STEPS. des.
  hexploit (trace_times_list_exists tr). i. des.
  hexploit step_times_list_exists; eauto. i. des.
  hexploit EVENT; ss.
  dup WF. inv WF. exploit Trace.steps_future; eauto.
  { ss. eapply WF1; eauto. } i. des. ss.
  hexploit Thread.step_future; eauto. i. des. ss.
  destruct (classic ((Local.promises lc3) = Memory.bot)) as [EQBOT|NEQBOT].
  { eexists (fun loc ts => List.In ts (times loc ++ times0 loc)), (tr++_), []. splits.
    { left. econs; eauto.
      { i. esplits. eapply promises_bot_certify_nil; eauto. }
      { eapply Forall_app.
        { eapply List.Forall_impl; eauto. i. eapply wf_time_evt_mon; try apply H0.
          i. ss. eapply List.in_or_app; eauto. }
        { econs; ss. eapply wf_time_evt_mon; try apply WFTIME0.
          i. ss. eapply List.in_or_app; eauto. }
      }
    }
    { i. eapply finite_well_ordered. }
  }
  destruct (ThreadEvent.get_machine_event e0) eqn:EQ; ss; cycle 1.
  { inv STEP0; inv STEP; ss. inv LOCAL; ss.
    inv LOCAL0; ss. exfalso. eapply NEQBOT; eauto. }
  eapply consistent_pf_consistent_super_strong in H; eauto. des.
  { red in FAILURE. des. exfalso. eapply NFAILURE. red. esplits.
    { etrans.
      { eapply STEPS0. }
      econs 2.
      { econs; [|eapply EQ]. econs; eauto. }
      { eauto. }
    }
    { eauto. }
    { eauto. }
  }
  eexists (certimes \2/ (fun loc ts => List.In ts (times loc ++ times0 loc))), (tr++_), tr0. splits.
  { left. rewrite <- EQ. econs; eauto.
    { i. esplits. eapply pf_consistent_super_strong_mon; eauto. }
    { rewrite EQ. i. des; ss; clarify. }
    { ii. ss. }
    { eapply Forall_app.
      { eapply List.Forall_impl; eauto. i. eapply wf_time_evt_mon; try apply H.
        i. ss. right. eapply List.in_or_app; eauto. }
      { econs; ss. eapply wf_time_evt_mon; try apply WFTIME0.
        i. ss. right. eapply List.in_or_app; eauto. }
    }
  }
  { i. eapply join_well_ordered; eauto. eapply finite_well_ordered. }
Qed.

Lemma times_configuration_behavior_configuration_behavior times c
      (WF: Configuration.wf c)
  :
    behaviors (times_configuration_step_strong_all times) c <2=
    behaviors (Configuration.step) c.
Proof.
  i. ginduction PR; eauto.
  { i. econs 1. eauto. }
  { i. inv STEP. eapply times_configuration_step_strong_step in STEP0.
    eapply times_configuration_step_configuration_step in STEP0; eauto.
    econs 2; eauto. eapply IHPR; eauto.
    eapply Configuration.step_future; eauto.
  }
  { i. inv STEP. eapply times_configuration_step_strong_step in STEP0.
    eapply times_configuration_step_configuration_step in STEP0; eauto.
    econs 3; eauto.
  }
  { i. inv STEP. eapply times_configuration_step_strong_step in STEP0.
    eapply times_configuration_step_configuration_step in STEP0; eauto.
    econs 4; eauto. eapply IHPR; eauto.
    eapply Configuration.step_future; eauto.
  }
  { i. econs 5; eauto. }
Qed.

Lemma times_configuration_step_same_behaviors c f beh
      (WF: Configuration.wf c)
      (BEH: behaviors Configuration.step c f beh)
  :
    exists times,
      (<<BEH: behaviors (times_configuration_step_strong_all times) c f beh>>) /\
      (<<WO: forall loc, well_ordered (times loc)>>) /\
      (<<INCR: forall nat loc, times loc (incr_time_seq nat)>>) /\
      (<<BOT: forall loc, times loc Time.bot>>)
.
Proof.
  ginduction BEH.
  { i. exists (fun loc => incr_times \1/ eq Time.bot). splits.
    { econs 1; eauto. }
    { i. eapply join_well_ordered; eauto.
      { eapply incr_times_well_ordered. }
      { eapply singleton_well_ordered. }
    }
    { i. left. eexists. eauto. }
    { auto. }
  }
  { i. exploit IHBEH.
    { eapply Configuration.step_future; eauto. } i. des.
    exploit times_configuration_step_exists; eauto. i. des.
    { exists (times \2/ times0). splits.
      { econs 2; eauto.
        { econs. eapply times_configuration_step_strong_mon; eauto. }
        { eapply le_step_behavior_improve; try apply BEH0.
          eapply times_configuration_step_strong_all_mon; auto. }
      }
      { i. eapply join_well_ordered; eauto. }
      { auto. }
      { auto. }
    }
    { exists (times \2/ times0). splits.
      { econs 3; eauto.
        { econs. eapply times_configuration_step_strong_mon; eauto. }
      }
      { i. eapply join_well_ordered; eauto. }
      { auto. }
      { auto. }
    }
  }
  { i. exploit times_configuration_step_exists; eauto. i. des.
    { exists (times \2/ (fun loc => incr_times) \2/ (fun _ => eq Time.bot)). splits; eauto.
      { econs 3; eauto. econs; eauto.
        eapply times_configuration_step_strong_mon; eauto. }
      { i. eapply join_well_ordered; eauto.
        { eapply join_well_ordered; eauto. eapply incr_times_well_ordered. }
        { eapply singleton_well_ordered. }
      }
      { i. left. right. eexists. eauto. }
    }
    { exists (times \2/ (fun loc => incr_times) \2/ (fun _ => eq Time.bot)). splits; eauto.
      { econs 3; eauto.
        { econs. eapply times_configuration_step_strong_mon; eauto. }
      }
      { i. eapply join_well_ordered; eauto.
        { eapply join_well_ordered; eauto. eapply incr_times_well_ordered. }
        { eapply singleton_well_ordered. }
      }
      { i. left. right. eexists. eauto. }
    }
  }
  { i. exploit IHBEH.
    { eapply Configuration.step_future; eauto. } i. des.
    exploit times_configuration_step_exists; eauto. i. des.
    { exists (times \2/ times0). splits.
      { econs 4; eauto.
        { econs. eapply times_configuration_step_strong_mon; eauto. }
        { eapply le_step_behavior_improve; try apply BEH0.
          eapply times_configuration_step_strong_all_mon; auto. }
      }
      { i. eapply join_well_ordered; eauto. }
      { auto. }
      { auto. }
    }
    { exists (times \2/ times0). splits.
      { econs 3; eauto.
        { econs. eapply times_configuration_step_strong_mon; eauto. }
      }
      { i. eapply join_well_ordered; eauto. }
      { auto. }
      { auto. }
    }
  }
  { i. esplits.
    { econs 5. }
    { instantiate (1:=((fun loc => incr_times) \2/ (fun _ => eq Time.bot))).
      i. eapply join_well_ordered; eauto.
      { eapply incr_times_well_ordered. }
      { eapply singleton_well_ordered. }
    }
    { i. left. eexists. eauto. }
    { i. right. auto. }
  }
Qed.
