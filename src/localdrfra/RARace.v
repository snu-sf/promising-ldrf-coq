Require Import Omega.
Require Import Bool.
Require Import RelationClasses.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Loc.
From PromisingLib Require Import Language.

Require Import Event.
Require Import Time.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.

Require Import OrdStep.


Module ReleaseWrites.
  Section ReleaseWrites.
    Variable L: Loc.t -> bool.

    Definition t: Type := list (Loc.t * Time.t).

    Definition append (e: ThreadEvent.t) (rels: t): t :=
      match ThreadEvent.is_writing e with
      | Some (loc, from, to, val, released, ord) =>
        if L loc
        then if Ordering.le Ordering.acqrel ord then (loc, to) :: rels else rels
        else rels
      | None => rels
      end.

    Definition wf (rels: t) (lc: Local.t) (mem: Memory.t): Prop :=
      forall loc to (IN: List.In (loc, to) rels),
        Memory.get loc to lc.(Local.promises) = None /\
        exists from val released,
          Memory.get loc to mem = Some (from, Message.concrete val released).

    Lemma append_app e rels1 rels2:
      append e rels1 ++ rels2 = append e (rels1 ++ rels2).
    Proof.
      unfold append. des_ifs.
    Qed.
  End ReleaseWrites.
End ReleaseWrites.


Module RAThread.
  Section RAThread.
    Variable lang: language.
    Variable L: Loc.t -> bool.

    Definition ra_race (rels: ReleaseWrites.t) (tview: TView.t) (loc: Loc.t) (to: Time.t) (ordr: Ordering.t): Prop :=
      (<<LOC: L loc>>) /\
      (<<HIGHER: Time.lt (tview.(TView.cur).(View.rlx) loc) to>>) /\
      ((<<ORDW: ~ List.In (loc, to) rels>>) \/
       (<<ORDR: Ordering.le ordr Ordering.strong_relaxed>>)).

    Inductive step rels1: forall (rels2: ReleaseWrites.t) (e: ThreadEvent.t) (e1 e2: Thread.t lang), Prop :=
    | step_normal
        pf e e1 e2
        (STEP: @OrdThread.step lang L Ordering.acqrel pf e e1 e2):
        step rels1 (ReleaseWrites.append L e rels1) e e1 e2
    | step_race
        pf e e1 e2
        loc to val released ord
        (STEP: @OrdThread.step lang L Ordering.acqrel pf e e1 e2)
        (CONS: Local.promise_consistent e1.(Thread.local))
        (EVENT: ThreadEvent.is_reading e = Some (loc, to, val, released, ord))
        (RACE: ra_race rels1 e1.(Thread.local).(Local.tview) loc to ord):
        step rels1 (ReleaseWrites.append L e rels1) ThreadEvent.failure e1 e2
    .

    Inductive steps rels1: forall (rels2: ReleaseWrites.t) (e1 e2: Thread.t lang), Prop :=
    | steps_refl
        e:
        steps rels1 rels1 e e
    | steps_step
        rels2 rels3 e e1 e2 e3
        (STEP: step rels1 rels2 e e1 e2)
        (STEPS: steps rels2 rels3 e2 e3):
        steps rels1 rels3 e1 e3
    .
    Hint Constructors steps.

    Inductive tau_steps rels1: forall (rels2: ReleaseWrites.t) (e1 e2: Thread.t lang), Prop :=
    | tau_steps_refl
        e:
        tau_steps rels1 rels1 e e
    | tau_steps_step
        rels2 rels3 e e1 e2 e3
        (STEP: step rels1 rels2 e e1 e2)
        (SILENT: ThreadEvent.get_machine_event e = MachineEvent.silent)
        (STEPS: tau_steps rels2 rels3 e2 e3):
        tau_steps rels1 rels3 e1 e3
    .
    Hint Constructors tau_steps.

    Definition steps_failure (rels1: ReleaseWrites.t) (e1: Thread.t lang): Prop :=
      exists rels2 rels3 e2 e3,
        (<<STEPS: tau_steps rels1 rels2 e1 e2>>) /\
        (<<FAILURE: step rels2 rels3 ThreadEvent.failure e2 e3>>).
    Hint Unfold steps_failure.

    Definition consistent (rels: ReleaseWrites.t) (e: Thread.t lang): Prop :=
      forall mem1 sc1
        (CAP: Memory.cap e.(Thread.memory) mem1)
        (SC_MAX: Memory.max_concrete_timemap mem1 sc1),
        (<<FAILURE: steps_failure rels (Thread.mk lang e.(Thread.state) e.(Thread.local) sc1 mem1)>>) \/
        exists rels2 e2,
          <<STEPS: tau_steps rels rels2 (Thread.mk lang e.(Thread.state) e.(Thread.local) sc1 mem1) e2>> /\
          <<PROMISES: e2.(Thread.local).(Local.promises) = Memory.bot>>.


    Lemma tau_steps_steps
          rels1 rels2 e1 e2
          (STEPS: tau_steps rels1 rels2 e1 e2):
      steps rels1 rels2 e1 e2.
    Proof.
      induction STEPS; eauto.
    Qed.

    Lemma steps_app
          rels1 rels2 rels3 e1 e2 e3
          (STEPS1: steps rels1 rels2 e1 e2)
          (STEPS2: steps rels2 rels3 e2 e3):
      steps rels1 rels3 e1 e3.
    Proof.
      revert rels3 e3 STEPS2.
      induction STEPS1; i; eauto.
    Qed.

    Lemma tau_steps_app
          rels1 rels2 rels3 e1 e2 e3
          (STEPS1: tau_steps rels1 rels2 e1 e2)
          (STEPS2: tau_steps rels2 rels3 e2 e3):
      tau_steps rels1 rels3 e1 e3.
    Proof.
      revert rels3 e3 STEPS2.
      induction STEPS1; i; eauto.
    Qed.

    Lemma tau_steps_rtc_tau_step
          rels1 rels2 e1 e2
          (STEPS: tau_steps rels1 rels2 e1 e2):
      rtc (@OrdThread.tau_step lang L Ordering.acqrel) e1 e2.
    Proof.
      induction STEPS; eauto.
      econs 2; eauto. inv STEP; ss.
      econs; eauto. econs. eauto.
    Qed.
  End RAThread.
End RAThread.


Module RAConfiguration.
  Section RAConfiguration.
    Variable L: Loc.t -> bool.

    Inductive step:
      forall (e: MachineEvent.t) (tid: Ident.t) (rels1 rels2: ReleaseWrites.t) (c1 c2: Configuration.t), Prop :=
    | step_intro
        rels1 rels2 rels3
        e tid c1 lang st1 lc1 e2 st3 lc3 sc3 memory3
        (TID: IdentMap.find tid c1.(Configuration.threads) = Some (existT _ lang st1, lc1))
        (STEPS: RAThread.tau_steps lang L rels1 rels2
                                   (Thread.mk _ st1 lc1 c1.(Configuration.sc) c1.(Configuration.memory)) e2)
        (STEP: RAThread.step lang L rels2 rels3 e e2 (Thread.mk _ st3 lc3 sc3 memory3))
        (CONSISTENT: e <> ThreadEvent.failure ->
                     RAThread.consistent lang L rels3 (Thread.mk _ st3 lc3 sc3 memory3)):
        step (ThreadEvent.get_machine_event e) tid rels1 rels3
             c1 (Configuration.mk (IdentMap.add tid (existT _ _ st3, lc3) c1.(Configuration.threads)) sc3 memory3)
    .

    Inductive steps rels1: forall (rels2: ReleaseWrites.t) (c1 c2: Configuration.t), Prop :=
    | steps_refl
        c:
        steps rels1 rels1 c c
    | steps_step
        rels2 rels3 e tid c1 c2 c3
        (STEP: step e tid rels1 rels2 c1 c2)
        (STEPS: steps rels2 rels3 c2 c3):
        steps rels1 rels3 c1 c3
    .
    Hint Constructors steps.
  End RAConfiguration.
End RAConfiguration.


Module RARace.
  Section RARace.
    Variable L: Loc.t -> bool.

    Definition racefree (rels: ReleaseWrites.t) (c: Configuration.t): Prop :=
      forall e tid rels2 rels3 c2 c3
        (STEPS: RAConfiguration.steps L rels rels2 c c2)
        (STEP: RAConfiguration.step L e tid rels2 rels3 c2 c3),
        False.

    Definition racefree_syn (syn: Threads.syntax): Prop :=
      racefree [] (Configuration.init syn).
  End RARace.
End RARace.
