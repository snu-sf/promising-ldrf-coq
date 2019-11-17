Require Import Omega.
Require Import RelationClasses.

From sflib Require Import sflib.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
Require Import Time.
Require Import Event.
From PromisingLib Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import MemoryFacts.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.
Require Import Progress.

Require Import Race.

Set Implicit Arguments.


Inductive pftstep: forall (e:MachineEvent.t) (tid:Ident.t) (c1 c2: Configuration.t), Prop :=
| pftstep_intro
    e tid c1 lang st1 lc1 e2 st3 lc3 sc3 memory3
    (TID: IdentMap.find tid c1.(Configuration.threads) = Some (existT _ lang st1, lc1))
    (STEPS: rtc (tau (@Thread.program_step _)) (Thread.mk _ st1 lc1 c1.(Configuration.sc) c1.(Configuration.memory)) e2)
    (STEP: Thread.program_step e e2 (Thread.mk _ st3 lc3 sc3 memory3)):
    pftstep (ThreadEvent.get_machine_event e) tid c1 (Configuration.mk (IdentMap.add tid (existT _ _ st3, lc3) c1.(Configuration.threads)) sc3 memory3)
.
Hint Constructors pftstep.

Definition pftstep_all (c0 c1: Configuration.t) :=
  union (fun e => union (pftstep e)) c0 c1.
Hint Unfold pftstep_all.

Inductive opt_pftstep: forall (e: MachineEvent.t) (tid: Ident.t) (c1 c2: Configuration.t), Prop :=
| pftstep_none
    tid c:
    opt_pftstep MachineEvent.silent tid c c
| pftstep_some
    e tid c1 c2
    (STEP: pftstep e tid c1 c2):
    opt_pftstep e tid c1 c2
.
Hint Constructors opt_pftstep.

Definition pf_racefree (c1:Configuration.t): Prop :=
  forall c2
         (STEPS: rtc pftstep_all c1 c2)
         (RACE: pf_race c2), False.

Lemma pf_racefree_step c1 c2 e tid
      (RACEFREE : pf_racefree c1)
      (STEP : pftstep e tid c1 c2) :
  pf_racefree c2.
Proof.
  ii. eapply RACEFREE.
  - econs 2; eauto.
  - auto.
Qed.

Lemma pftstep_future
      e tid c1 c2
      (STEP: pftstep e tid c1 c2)
      (WF1: Configuration.wf c1):
  Configuration.wf c2.
Proof.
  inv WF1. inv WF. inv STEP; s.
  exploit THREADS; ss; eauto. i.
  exploit Thread.rtc_tau_step_future.
  { eapply rtc_implies; try apply STEPS. eapply tau_mon.
    i. econs. econs 2; eauto. } all: eauto. s. i. des.
  exploit Thread.step_future.
  { econs 2; eauto. } all: eauto. s. i. des.
  econs; ss. econs.
  i. Configuration.simplify.
  - exploit THREADS; try apply TH1; eauto. i. des.
    exploit Thread.rtc_tau_step_disjoint.
    { eapply rtc_implies; try apply STEPS. eapply tau_mon.
      i. econs. econs 2; eauto. } all: eauto. i. des.
    exploit Thread.step_disjoint.
    { econs 2; eauto. } all: eauto. i. des. ss.
    symmetry. auto.
  - exploit THREADS; try apply TH2; eauto. i. des.
    exploit Thread.rtc_tau_step_disjoint.
    { eapply rtc_implies; try apply STEPS. eapply tau_mon.
      i. econs. econs 2; eauto. } all: eauto. i. des.
    exploit Thread.step_disjoint.
    { econs 2; eauto. } all: eauto. i. des. ss.
  - eapply DISJOINT; [|eauto|eauto]. auto.
  - i. Configuration.simplify.
    exploit THREADS; try apply TH; eauto. i.
    exploit Thread.rtc_tau_step_disjoint.
    { eapply rtc_implies; try apply STEPS. eapply tau_mon.
      i. econs. econs 2; eauto. } all: eauto. i. des.
    exploit Thread.step_disjoint.
    { econs 2; eauto. } all: eauto. i. des. ss.
Qed.

Lemma write_no_promise mem0 loc from to val released prom1 mem1 kind
      (WRITE: Memory.write Memory.bot mem0 loc from to val released prom1 mem1 kind)
  :
    <<NOPROMISE: prom1 = Memory.bot>> /\ <<ADD: kind = Memory.op_kind_add>>.
Proof.
  inv WRITE. inv PROMISE.
  - split; auto. eapply MemoryFacts.add_remove_eq; eauto.
  - eapply Memory.split_get0 in PROMISES. des.
    erewrite Memory.bot_get in GET0. clarify.
  - eapply Memory.lower_get0 in PROMISES. des.
    erewrite Memory.bot_get in GET. clarify.
  - eapply Memory.remove_get0 in PROMISES. des.
    erewrite Memory.bot_get in GET. clarify.
Qed.

Lemma program_step_no_promise lang (th0 th1: Thread.t lang) e
      (STEP: Thread.program_step e th0 th1)
      (NOPROMISE: th0.(Thread.local).(Local.promises) = Memory.bot)
  :
    th1.(Thread.local).(Local.promises) = Memory.bot.
Proof.
  inv STEP. inv LOCAL; ss.
  - inv LOCAL0. ss.
  - inv LOCAL0. rewrite NOPROMISE in WRITE.
    eapply write_no_promise in WRITE. des. auto.
  - inv LOCAL1. inv LOCAL2. rewrite NOPROMISE in WRITE.
    eapply write_no_promise in WRITE. des. auto.
  - inv LOCAL0. ss.
  - inv LOCAL0. ss.
Qed.

Lemma program_steps_no_promise lang (th0 th1: Thread.t lang)
      (STEP: rtc (tau (@Thread.program_step lang)) th0 th1)
      (NOPROMISE: th0.(Thread.local).(Local.promises) = Memory.bot)
  :
    th1.(Thread.local).(Local.promises) = Memory.bot.
Proof.
  ginduction STEP; ss. i. eapply IHSTEP. inv H.
  eapply program_step_no_promise; eauto.
Qed.

Lemma no_promise_spec c
      (NOPROMISE: ~ Configuration.has_promise c)
      tid st lc
      (FIND: IdentMap.find tid (Configuration.threads c) = Some (st, lc))
  :
    lc.(Local.promises) = Memory.bot.
Proof.
  eapply Memory.ext. i. rewrite Memory.bot_get.
  destruct (Memory.get loc ts (Local.promises lc)) as [[from msg]|] eqn:GET; auto.
  exfalso. eapply NOPROMISE. econs; eauto.
Qed.

Lemma configuration_step_no_promise c0 c1 tid e
      (NOPROMISE: ~ Configuration.has_promise c0)
      (STEP: pftstep tid e c0 c1)
  :
    ~ Configuration.has_promise c1.
Proof.
  inv STEP. ii. inv H. ss. rewrite IdentMap.gsspec in FIND. des_ifs.
  - eapply no_promise_spec in TID; eauto.
    eapply program_steps_no_promise in STEPS; eauto.
    eapply program_step_no_promise in STEP0; eauto.
    ss. rewrite STEP0 in *. rewrite Memory.bot_get in *. clarify.
  - eapply NOPROMISE. econs; eauto.
Qed.
