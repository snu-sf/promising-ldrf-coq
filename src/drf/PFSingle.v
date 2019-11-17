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

Require Import PF.

Inductive pftstep_single: forall (e:MachineEvent.t) (tid:Ident.t) (c1 c2: Configuration.t), Prop :=
| pftstep_single_intro
    e tid c1 lang st1 lc1 st3 lc3 sc3 memory3
    (TID: IdentMap.find tid c1.(Configuration.threads) = Some (existT _ lang st1, lc1))
    (STEP: Thread.program_step e (Thread.mk _ st1 lc1 c1.(Configuration.sc) c1.(Configuration.memory)) (Thread.mk _ st3 lc3 sc3 memory3)):
    pftstep_single (ThreadEvent.get_machine_event e) tid c1 (Configuration.mk (IdentMap.add tid (existT _ _ st3, lc3) c1.(Configuration.threads)) sc3 memory3)
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

Lemma tau_steps_single_steps c
      (FIND

Lemma pftstep_single_sim c0 c1 e tid
      (STEP: pftstep e tid c0 c1)
  :
    exists c',
      (<<STEPS: rtc (tau_pftstep_single tid) c0 c'>>) /\
      (<<STEP: pftstep_single e tid c' c1>>).
Proof.
  inv STEP.
  remember (Thread.mk _ st1 lc1 (Configuration.sc c0) (Configuration.memory c0)) as th1.
  remember (Thread.mk _ st3 lc3 sc3 memory3) as th3. ginduction STEPS; i; clarify.
  - exists c0. splits; auto. econs; eauto.
  - IdentMap.add


Inductive almost_same tid: Configuration.t -> Configuration.t -> Prop :=
| almost_same_refl
    ths sc mem
  :
    Configuration.mk


    Configuration.mk


Lemma pftstep_single_sim c0 c1 e tid
      (STEP: pftstep e tid c0 c1)
  :
    exists c',
      (<<STEPS: rtc (tau_pftstep_single tid) c0 c'>>) /\
      (<<STEP: pftstep_single e tid c' c1>>).
Proof.
  inv STEP.
  remember (Thread.mk _ st1 lc1 (Configuration.sc c0) (Configuration.memory c0)) as th1.
  remember (Thread.mk _ st3 lc3 sc3 memory3) as th3. ginduction STEPS; i; clarify.
  - exists c0. splits; auto. econs; eauto.
  - IdentMap.add

IdentMap.add_add_eq:
  forall (V : Type) (k : IdentMap.key) (v1 v2 : V) (m : IdentMap.t V),
  IdentMap.add k v1 (IdentMap.add k v2 m) = IdentMap.add k v1 m






  dd

  -