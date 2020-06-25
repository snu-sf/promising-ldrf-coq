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


Inductive times_configuration_step (times: Loc.t -> Time.t -> Prop)
  : forall lang (tr tr_cert: Trace.t lang)
           (e:MachineEvent.t) (tid:Ident.t) (c1 c2:Configuration.t), Prop :=
| times_configuration_step_intro
    lang tr e tr' pf tid c1 st1 lc1 e2 st3 lc3 sc3 memory3 tr_cert
    (TID: IdentMap.find tid c1.(Configuration.threads) = Some (existT _ lang st1, lc1))
    (STEPS: Trace.steps tr' (Thread.mk _ st1 lc1 c1.(Configuration.sc) c1.(Configuration.memory)) e2)
    (SILENT: List.Forall (fun the => ThreadEvent.get_machine_event (snd the) = MachineEvent.silent) tr')
    (STEP: Thread.step pf e e2 (Thread.mk _ st3 lc3 sc3 memory3))
    (TR: tr = tr'++[(e2, e)])
    (CONSISTENT: forall (EVENT: e <> ThreadEvent.failure),
        pf_consistent_super_strong (Thread.mk _ st3 lc3 sc3 memory3) tr_cert times)
    (CERTNIL: e = ThreadEvent.failure -> tr_cert = [])
    (TIMES: List.Forall (fun thte => wf_time_evt times (snd thte)) tr)
  :
    times_configuration_step
      times tr tr_cert
      (ThreadEvent.get_machine_event e) tid c1 (Configuration.mk (IdentMap.add tid (existT _ _ st3, lc3) c1.(Configuration.threads)) sc3 memory3)
.

Inductive times_configuration_step_all (times: Loc.t -> Time.t -> Prop)
          (e:MachineEvent.t) (tid:Ident.t) (c1 c2:Configuration.t): Prop :=
| times_configuration_step_all_intro
    lang tr tr_cert
    (STEP: @times_configuration_step times lang tr tr_cert e tid c1 c2)
.

Lemma times_configuration_step_traced_step times lang tr tr_cert e tid c1 c2
      (STEP: @times_configuration_step times lang tr tr_cert e tid c1 c2)
      (WF: Configuration.wf c1)
  :
    exists lang (tr: Trace.t lang),
      (<<STEP: Trace.configuration_step tr e tid c1 c2>>).
Proof.
  inv STEP. apply inj_pair2 in H1. apply inj_pair2 in H2. subst.
  esplits. econs; eauto.
  i. hexploit CONSISTENT; eauto. i. des.
  dup WF. inv WF. exploit Trace.steps_future; eauto.
  { ss. eapply WF1; eauto. } i. des. ss.
  hexploit Trace.steps_future; eauto.
  { eapply WF0; eauto. } i. des. ss.
  hexploit Thread.step_future; eauto. i. des. ss.
  eapply pf_consistent_super_strong_consistent; eauto.
Qed.

Lemma times_configuration_step_future
      times lang tr tr_cert e tid c1 c2
      (STEP: @times_configuration_step times lang tr tr_cert e tid c1 c2)
      (WF1: Configuration.wf c1):
  (<<WF2: Configuration.wf c2>>) /\
  (<<SC_FUTURE: TimeMap.le c1.(Configuration.sc) c2.(Configuration.sc)>>) /\
  (<<MEM_FUTURE: Memory.future c1.(Configuration.memory) c2.(Configuration.memory)>>).
Proof.
  eapply times_configuration_step_traced_step in STEP; eauto. des.
  eapply Trace.configuration_step_future; eauto.
Qed.

Inductive times_configuration_opt_step (times: Loc.t -> Time.t -> Prop)
  : forall lang (tr tr_cert: Trace.t lang)
           (e:MachineEvent.t) (tid:Ident.t) (c1 c2:Configuration.t), Prop :=
| times_configuration_opt_step_some
    lang tr tr_cert e tid c1 c2
    (STEP: @times_configuration_step times lang tr tr_cert e tid c1 c2)
  :
    times_configuration_opt_step times tr tr_cert e tid c1 c2
| times_configuration_opt_step_none
    lang tid c
  :
    @times_configuration_opt_step times lang [] [] MachineEvent.silent tid c c
.

Lemma times_configuration_opt_step_future
      times lang tr tr_cert e tid c1 c2
      (STEP: @times_configuration_opt_step times lang tr tr_cert e tid c1 c2)
      (WF1: Configuration.wf c1):
  (<<WF2: Configuration.wf c2>>) /\
  (<<SC_FUTURE: TimeMap.le c1.(Configuration.sc) c2.(Configuration.sc)>>) /\
  (<<MEM_FUTURE: Memory.future c1.(Configuration.memory) c2.(Configuration.memory)>>).
Proof.
  inv STEP.
  { apply inj_pair2 in H1. apply inj_pair2 in H2. subst.
    eapply times_configuration_step_future; eauto. }
  { apply inj_pair2 in H1. apply inj_pair2 in H2. subst. splits; auto. refl. }
Qed.

Lemma times_configuration_step_mon times0 times1
      (LE: times0 <2= times1)
  :
    times_configuration_step times0 <7= times_configuration_step times1.
Proof.
  i. inv PR. eapply inj_pair2 in H1. eapply inj_pair2 in H2. subst. econs; eauto.
  { i. hexploit CONSISTENT; eauto. i. des. esplits; eauto.
    eapply pf_consistent_super_strong_mon; eauto. }
  { eapply List.Forall_impl; eauto. i. eapply wf_time_evt_mon; eauto. }
Qed.

Lemma times_configuration_step_all_mon times0 times1
      (LE: times0 <2= times1)
  :
    times_configuration_step_all times0 <4= times_configuration_step_all times1.
Proof.
  i. inv PR. econs. eapply times_configuration_step_mon; eauto.
Qed.

Lemma times_configuration_step_exists c0 c1 tid e
      (STEP: Configuration.step e tid c0 c1)
      (WF: Configuration.wf c0)
  :
    exists lang times tr tr_cert,
      (<<STEP: @times_configuration_step times lang tr tr_cert e tid c0 c1>>) /\
      (<<WO: forall loc, well_ordered (times loc)>>).
Proof.
  eapply Trace.step_configuration_step in STEP. des.
  hexploit (trace_times_list_exists tr). i. des. inv STEP0.
  eapply inj_pair2 in H1. subst. destruct (classic (e0 = ThreadEvent.failure)).
  { subst. eexists lang, (fun loc ts => List.In ts (times loc)), (tr'++_), []. splits.
    { econs; eauto. ss. }
    { i. eapply finite_well_ordered. }
  }
  { hexploit CONSISTENT; ss.
    dup WF. inv WF. exploit Trace.steps_future; eauto.
    { ss. eapply WF1; eauto. } i. des. ss.
    hexploit Thread.step_future; eauto. i. des. ss.
    eapply consistent_pf_consistent_super_strong in H0; eauto.
    des. eexists lang, (certimes \2/ (fun loc ts => List.In ts (times loc))), (tr'++_), tr. splits.
    { econs; eauto.
      { i. esplits. eapply pf_consistent_super_strong_mon; eauto. }
      { i. ss. }
      { eapply List.Forall_impl; try apply WFTIME.
        i. ss. eapply wf_time_evt_mon; try apply H0. i. ss. auto. }
    }
    { i. eapply join_well_ordered; eauto. eapply finite_well_ordered. }
  }
Qed.

Lemma times_configuration_step_same_behaviors c beh
      (WF: Configuration.wf c)
      (BEH: behaviors Configuration.step c beh)
  :
    exists times,
      (<<BEH: behaviors (times_configuration_step_all times) c beh>>) /\
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
    exists (times \2/ times0). splits.
    { econs 2; eauto.
      { econs. eapply times_configuration_step_mon; eauto. }
      { eapply le_step_behavior_improve; try apply BEH0.
        eapply times_configuration_step_all_mon; auto. }
    }
    { i. eapply join_well_ordered; eauto. }
    { auto. }
    { auto. }
  }
  { i. exploit times_configuration_step_exists; eauto. i. des.
    exists (times \2/ (fun loc => incr_times) \2/ (fun _ => eq Time.bot)). splits; eauto.
    { econs 3; eauto. econs; eauto.
      eapply times_configuration_step_mon; eauto. }
    { i. eapply join_well_ordered; eauto.
      { eapply join_well_ordered; eauto. eapply incr_times_well_ordered. }
      { eapply singleton_well_ordered. }
    }
    { i. left. right. eexists. eauto. }
  }
  { i. exploit IHBEH.
    { eapply Configuration.step_future; eauto. } i. des.
    exploit times_configuration_step_exists; eauto. i. des.
    exists (times \2/ times0). splits.
    { econs 4; eauto.
      { econs. eapply times_configuration_step_mon; eauto. }
      { eapply le_step_behavior_improve; try apply BEH0.
        eapply times_configuration_step_all_mon; auto. }
    }
    { i. eapply join_well_ordered; eauto. }
    { auto. }
    { auto. }
  }
Qed.
