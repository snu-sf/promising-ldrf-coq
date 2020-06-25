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


Module RATrace.
  Section RATrace.
    Variable L: Loc.t -> bool.

    Inductive thread_steps lang: forall (rels: ReleaseWrites.t) (e1 e2: Thread.t lang), Prop :=
    | thread_steps_refl
        e:
        thread_steps lang [] e e
    | thread_steps_step
        rels pf e e1 e2 e3
        (STEPS: @thread_steps lang rels e1 e2)
        (STEP: @OrdThread.step lang L Ordering.acqrel pf e e2 e3):
        thread_steps lang (ReleaseWrites.append L e rels) e1 e3
    .
    Hint Constructors thread_steps.

    Inductive thread_tau_steps lang: forall (rels: ReleaseWrites.t) (e1 e2: Thread.t lang), Prop :=
    | thread_tau_steps_refl
        e:
        thread_tau_steps lang [] e e
    | thread_tau_steps_step
        rels pf e e1 e2 e3
        (STEPS: @thread_tau_steps lang rels e1 e2)
        (STEP: @OrdThread.step lang L Ordering.acqrel pf e e2 e3)
        (SILENT: ThreadEvent.get_machine_event e = MachineEvent.silent):
        thread_tau_steps lang (ReleaseWrites.append L e rels) e1 e3
    .
    Hint Constructors thread_steps.

    Inductive configuration_step: forall (e: MachineEvent.t) (tid: Ident.t) (rels: ReleaseWrites.t) (c1 c2: Configuration.t), Prop :=
    | configuration_step_intro
        rels
        pf e tid c1 lang st1 lc1 e2 st3 lc3 sc3 memory3
        (TID: IdentMap.find tid c1.(Configuration.threads) = Some (existT _ lang st1, lc1))
        (STEPS: thread_tau_steps lang rels (Thread.mk _ st1 lc1 c1.(Configuration.sc) c1.(Configuration.memory)) e2)
        (STEP: OrdThread.step L Ordering.acqrel pf e e2 (Thread.mk _ st3 lc3 sc3 memory3))
        (CONSISTENT: OrdThread.consistent L Ordering.acqrel (Thread.mk _ st3 lc3 sc3 memory3)):
        configuration_step (ThreadEvent.get_machine_event e) tid (ReleaseWrites.append L e rels)
                           c1 (Configuration.mk (IdentMap.add tid (existT _ _ st3, lc3) c1.(Configuration.threads)) sc3 memory3)
    .
    Hint Constructors configuration_step.

    Inductive configuration_steps: forall (rels: ReleaseWrites.t) (c1 c2: Configuration.t), Prop :=
    | configuration_steps_refl
        c:
        configuration_steps [] c c
    | configuration_steps_step
        rels e tid rels' c1 c2 c3
        (STEPS: configuration_steps rels c1 c2)
        (STEP: configuration_step e tid rels' c2 c3):
        configuration_steps (rels' ++ rels) c1 c3
    .
    Hint Constructors configuration_steps.

    Lemma thread_tau_steps_steps
          lang rels e1 e2
          (STEPS: thread_tau_steps lang rels e1 e2):
      thread_steps lang rels e1 e2.
    Proof.
      induction STEPS; eauto.
    Qed.

    Lemma thread_steps_app
          lang rels1 rels2 e1 e2 e3
          (STEPS1: thread_steps lang rels1 e1 e2)
          (STEPS2: thread_steps lang rels2 e2 e3):
      thread_steps lang (rels2 ++ rels1) e1 e3.
    Proof.
      revert rels1 e1 STEPS1. induction STEPS2; i; eauto.
      exploit IHSTEPS2; eauto. i.
      rewrite ReleaseWrites.append_app. econs 2; eauto.
    Qed.

    Lemma thread_tau_steps_app
          lang rels1 rels2 e1 e2 e3
          (STEPS1: thread_tau_steps lang rels1 e1 e2)
          (STEPS2: thread_tau_steps lang rels2 e2 e3):
      thread_tau_steps lang (rels2 ++ rels1) e1 e3.
    Proof.
      revert rels1 e1 STEPS1. induction STEPS2; i; eauto.
      exploit IHSTEPS2; eauto. i.
      rewrite ReleaseWrites.append_app. econs 2; eauto.
    Qed.

    Lemma thread_tau_steps_rtc_tau_step
          lang rels e1 e2
          (STEPS: thread_tau_steps lang rels e1 e2):
      rtc (@OrdThread.tau_step lang L Ordering.acqrel) e1 e2.
    Proof.
      induction STEPS; eauto.
      exploit rtc_n1; try exact IHSTEPS; eauto.
      econs; eauto. econs. eauto.
    Qed.

    Lemma configuration_step_ord_step
          e tid rels c1 c2
          (STEP: configuration_step e tid rels c1 c2):
      OrdConfiguration.step L Ordering.acqrel e tid c1 c2.
    Proof.
      inv STEP. exploit thread_tau_steps_rtc_tau_step; eauto. i.
      destruct (ThreadEvent.get_machine_event e0) eqn:EVENT.
      - rewrite <- EVENT. econs 2; eauto. destruct e0; ss.
      - rewrite <- EVENT. econs 2; eauto. destruct e0; ss.
      - destruct e0; ss. econs 1; eauto.
    Qed.
  End RATrace.
End RATrace.


Module RARace.
  Section RARace.
    Variable L: Loc.t -> bool.

    Definition ra_race (rels: ReleaseWrites.t) (tview: TView.t) (loc: Loc.t) (to: Time.t) (ordr: Ordering.t): Prop :=
      <<LOC: L loc>> /\
      <<HIGHER: Time.lt (tview.(TView.cur).(View.rlx) loc) to>> /\
      (<<ORDW: ~ List.In (loc, to) rels>> \/
       <<ORDR: Ordering.le ordr Ordering.strong_relaxed>>).

    Definition racefree (s: Threads.syntax): Prop :=
      forall rels1 c
        tid lang st1 lc1
        rels2 pf e loc to val released ord e2 e3
        (CSTEPS: RATrace.configuration_steps L rels1 (Configuration.init s) c)
        (TID: IdentMap.find tid c.(Configuration.threads) = Some (existT _ lang st1, lc1))
        (STEPS: RATrace.thread_steps L lang rels2
                                     (Thread.mk _ st1 lc1 c.(Configuration.sc) c.(Configuration.memory))
                                     e2)
        (CONS: Local.promise_consistent e2.(Thread.local))
        (STEP: OrdThread.step L Ordering.acqrel pf e e2 e3)
        (READ: ThreadEvent.is_reading e = Some (loc, to, val, released, ord))
        (RACE: ra_race (rels2 ++ rels1) e2.(Thread.local).(Local.tview) loc to ord),
        False.
  End RARace.
End RARace.
