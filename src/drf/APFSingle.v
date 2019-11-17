Require Import Omega.
Require Import RelationClasses.

From Paco Require Import paco.
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
Require Import Behavior.
Require Import AProp.
Require Import Race.

Require Import ALocal.
Require Import AThread.
Require Import AMemory.

Require Import APF.

Set Implicit Arguments.


Inductive pftstep_single: forall (e:MachineEvent.t) (tid:Ident.t) (c1 c2: Configuration.t), Prop :=
| pftstep_single_intro
    e tid c1 lang st1 lc1 st3 lc3 sc3 memory3
    (TID: IdentMap.find tid c1.(Configuration.threads) = Some (existT _ lang st1, lc1))
    (STEP: AThread.program_step e (Thread.mk _ st1 lc1 c1.(Configuration.sc) c1.(Configuration.memory)) (Thread.mk _ st3 lc3 sc3 memory3))
    c2
    (CONFIG: c2 = Configuration.mk (IdentMap.add tid (existT _ _ st3, lc3) c1.(Configuration.threads)) sc3 memory3)
  :
    pftstep_single (ThreadEvent.get_machine_event e) tid c1 c2
.

Inductive tau_pftstep_single tid (c1 c2: Configuration.t): Prop :=
| tau_pftstep_single_intro
    (STEP: pftstep_single MachineEvent.silent tid c1 c2)
.

Lemma pftstep_single_pftstep
  :
  pftstep_single <4= pftstep.
Proof.
  i. inv PR. econs; eauto.
Qed.

Lemma tau_steps_single_steps c tid lang st1 lc1 st2 lc2 sc2 mem2
      (TID: IdentMap.find tid c.(Configuration.threads) = Some (existT _ lang st1, lc1))
      (STEPS: Relation_Operators.clos_refl_trans_n1 _ (tau (@AThread.program_step _)) (Thread.mk _ st1 lc1 c.(Configuration.sc) c.(Configuration.memory)) (Thread.mk _ st2 lc2 sc2 mem2))
  :
    exists ths',
      (<<STEPS: Relation_Operators.clos_refl_trans_n1 _ (tau_pftstep_single tid) c (Configuration.mk ths' sc2 mem2)>>) /\
      ((ths' = IdentMap.add tid (existT _ lang st2, lc2) c.(Configuration.threads)) \/
       (ths' = c.(Configuration.threads) /\ st1 = st2 /\ lc1 = lc2)).
Proof.
  remember (Thread.mk _ st1 lc1 (Configuration.sc c) (Configuration.memory c)) as th1.
  remember (Thread.mk _ st2 lc2 sc2 mem2) as th2. ginduction STEPS.
  - i. clarify. destruct c. esplits.
    + ss. econs 1.
    + ss. right. auto.
  - i. clarify. destruct y. inv H. exploit IHSTEPS; eauto. i. des; clarify.
    + destruct c. ss. esplits.
      * econs 2; eauto. econs; eauto. rewrite <- EVENT. econs; eauto.
        ss. rewrite IdentMap.gss. ss.
      * ss. left. eapply IdentMap.add_add_eq.
    + destruct c. ss. esplits.
      * econs 2; eauto. econs; eauto. rewrite <- EVENT. econs; eauto.
      * ss. left. auto.
Qed.

Lemma pftstep_single_sim c0 c1 e tid
      (STEP: pftstep e tid c0 c1)
  :
    exists c',
      (<<STEPS: rtc (tau_pftstep_single tid) c0 c'>>) /\
      (<<STEP: pftstep_single e tid c' c1>>).
Proof.
  inv STEP.
  eapply Operators_Properties.clos_rt1n_rt in STEPS.
  eapply Operators_Properties.clos_rt_rtn1 in STEPS.
  destruct e2. exploit tau_steps_single_steps; eauto. i. des; clarify.
  - eapply Operators_Properties.clos_rtn1_rt in STEPS0.
    eapply Operators_Properties.clos_rt_rt1n in STEPS0.
    esplits; eauto. econs.
    + ss. rewrite IdentMap.gss. ss.
    + ss. eauto.
    + ss. f_equal. symmetry. eapply IdentMap.add_add_eq.
  - eapply Operators_Properties.clos_rtn1_rt in STEPS0.
    eapply Operators_Properties.clos_rt_rt1n in STEPS0.
    esplits; eauto. econs; eauto.
Qed.

Lemma taus_pftstep_single tid c0 c1 beh
      (TAUS: rtc (tau_pftstep_single tid) c0 c1)
      (BEH: behaviors pftstep_single c1 beh)
  :
    behaviors pftstep_single c0 beh.
Proof.
  ginduction TAUS; i; auto.
  eapply IHTAUS in BEH. inv H. econs 4; eauto.
Qed.

Lemma pftstep_equiv c
  :
    behaviors pftstep c
    <1=
    behaviors pftstep_single c.
Proof.
  ii. ginduction PR.
  - econs; ss.
  - exploit pftstep_single_sim; eauto. i. des.
    eapply taus_pftstep_single in STEPS; eauto. econs 2; eauto.
  - exploit pftstep_single_sim; eauto. i. des.
    eapply taus_pftstep_single in STEPS; eauto. econs 3; eauto.
  - exploit pftstep_single_sim; eauto. i. des.
    eapply taus_pftstep_single in STEPS; eauto. econs 4; eauto.
Qed.

Lemma pftstep_equiv2 c
  :
    behaviors pftstep_single c
    <1=
    behaviors pftstep c.
Proof.
  eapply le_step_behavior_improve; eauto.
  eapply pftstep_single_pftstep.
Qed.

Definition pftstep_single_all (c0 c1: Configuration.t) :=
  union (fun e => union (pftstep_single e)) c0 c1.
Hint Unfold pftstep_single_all.

Definition pf_racefree (c1:Configuration.t): Prop :=
  forall c2
         (STEPS: rtc pftstep_single_all c1 c2)
         (RACE: pf_race c2), False.
