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

Require Import AMemory.
Require Import ALocal.
Require Import AThread.

Set Implicit Arguments.

Inductive pftstep: forall (e:MachineEvent.t) (tid:Ident.t) (c1 c2: Configuration.t), Prop :=
| pftstep_intro
    e tid c1 lang st1 lc1 e2 st3 lc3 sc3 memory3
    (TID: IdentMap.find tid c1.(Configuration.threads) = Some (existT _ lang st1, lc1))
    (STEPS: rtc (tau (@AThread.program_step _)) (Thread.mk _ st1 lc1 c1.(Configuration.sc) c1.(Configuration.memory)) e2)
    (STEP: AThread.program_step e e2 (Thread.mk _ st3 lc3 sc3 memory3)):
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

Lemma pf_racefree_step c1 c2
      (RACEFREE : pf_racefree c1)
      (STEP : rtc pftstep_all c1 c2) :
  pf_racefree c2.
Proof.
  intros c3 STEPS RACE.
  apply (RACEFREE c3); auto. etrans; eauto.
Qed.
