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

Set Implicit Arguments.



Module Trace.

  Definition t lang := list (Thread.t lang * ThreadEvent.t).

  Inductive steps lang: forall (tr: t lang) (th0 th1: Thread.t lang), Prop :=
  | steps_refl
      th0
    :
      steps [] th0 th0
  | steps_trans
      tr tr' th0 th1 th2 pf e
      (STEP: Thread.step pf e th0 th1)
      (STEPS: steps tr th1 th2)
      (TR: tr' = (th0, e) :: tr)
    :
      steps tr' th0 th2
  .
  Hint Constructors steps.

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
    exists ((x, e)::tr). splits; eauto.
  Qed.

  Lemma steps_app lang tr0 tr1 (th0 th1 th2: Thread.t lang)
        (STEPS0: steps tr0 th0 th1)
        (STEPS1: steps tr1 th1 th2)
    :
      steps (tr0 ++ tr1) th0 th2.
  Proof.
    ginduction STEPS0; eauto. i. subst. econs; eauto.
  Qed.

  Inductive configuration_step: forall lang (tr: t lang) (e:MachineEvent.t) (tid:Ident.t) (c1 c2:Configuration.t), Prop :=
  | step_intro
      lang tr e tr' pf tid c1 st1 lc1 e2 st3 lc3 sc3 memory3
      (TID: IdentMap.find tid c1.(Configuration.threads) = Some (existT _ lang st1, lc1))
      (STEPS: steps tr (Thread.mk _ st1 lc1 c1.(Configuration.sc) c1.(Configuration.memory)) e2)
      (SILENT: List.Forall (fun the => ThreadEvent.get_machine_event (snd the) = MachineEvent.silent) tr)
      (STEP: Thread.step pf e e2 (Thread.mk _ st3 lc3 sc3 memory3))
      (TR: tr' = tr++[(e2, e)])
      (CONSISTENT: forall (EVENT: e <> ThreadEvent.failure),
          Thread.consistent (Thread.mk _ st3 lc3 sc3 memory3))
    :
      configuration_step tr (ThreadEvent.get_machine_event e) tid c1 (Configuration.mk (IdentMap.add tid (existT _ _ st3, lc3) c1.(Configuration.threads)) sc3 memory3)
  .

End Trace.
