Require Import Omega.
Require Import RelationClasses.

Require Import sflib.

Require Import Axioms.
Require Import Basic.
Require Import DataStructure.
Require Import Time.
Require Import Event.
Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import MemoryFacts.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.
Require Import Progress.

Set Implicit Arguments.

Inductive pftstep: forall (e:option Event.t) (tid:Ident.t) (c1 c2: Configuration.t), Prop :=
| pftstep_intro
    e tid c1 lang st1 lc1 e2 st3 lc3 sc3 memory3
    (TID: IdentMap.find tid c1.(Configuration.threads) = Some (existT _ lang st1, lc1))
    (STEPS: rtc (tau (@Thread.program_step _)) (Thread.mk _ st1 lc1 c1.(Configuration.sc) c1.(Configuration.memory)) e2)
    (STEP: Thread.program_step e e2 (Thread.mk _ st3 lc3 sc3 memory3)):
    pftstep (ThreadEvent.get_event e) tid c1 (Configuration.mk (IdentMap.add tid (existT _ _ st3, lc3) c1.(Configuration.threads)) sc3 memory3)
.
Hint Constructors pftstep.

Definition pftstep_all (c0 c1: Configuration.t) :=
  union (fun e => union (pftstep e)) c0 c1.
Hint Unfold pftstep_all.

Inductive opt_pftstep lang : option Event.t -> Thread.t lang -> Thread.t lang -> Prop :=
| opt_pftstep_none
    c:
    opt_pftstep None c c
| opt_pftstep_some
    e e1 e2
    (STEP: Thread.program_step e e1 e2):
    opt_pftstep (ThreadEvent.get_event e) e1 e2
.
Hint Constructors opt_pftstep.
