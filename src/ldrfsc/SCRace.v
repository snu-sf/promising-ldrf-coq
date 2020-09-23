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
Require Import MemoryFacts.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.

Require Import SCStep.

Set Implicit Arguments.

Definition is_accessing (e:ProgramEvent.t): option Loc.t :=
  match e with
  | ProgramEvent.read loc _ _ => Some loc
  | ProgramEvent.write loc _ _ => Some loc
  | ProgramEvent.update loc _ _ _ _ => Some loc
  | _ => None
  end.

Module SCRace.
  Section SCRace.
    Variable L: Loc.t -> bool.

    Definition race lang (th: Thread.t lang): Prop :=
      exists e st' loc,
        (<<STEP: Language.step _ e th.(Thread.state) st'>>) /\
        (<<ACCESS: is_accessing e = (Some loc)>>) /\
        (<<LOC: L loc>>) /\
        (<<MAXIMAL: SCLocal.non_maximal th.(Thread.local) th.(Thread.memory) loc>>).

    Lemma non_maximal_equiv lc loc mem
          (LOCAL: Local.wf lc mem)
      :
        SCLocal.non_maximal lc mem loc <->
        ~ Memory.max_concrete_ts mem loc (lc.(Local.tview).(TView.cur).(View.rlx) loc).
    Proof.
      inv LOCAL. unfold SCLocal.non_maximal. split; i.
      - des. ii. eapply H in GET. timetac.
      - inv TVIEW_CLOSED. inv CUR. specialize (RLX loc). des.
        eapply NNPP. ii. eapply H. econs; eauto.
        i. destruct (Time.le_lt_dec to (View.rlx (TView.cur (Local.tview lc)) loc)); auto.
        exfalso. eapply H0. esplits; eauto.
    Qed.

    Definition race_steps (c: Configuration.t) (tid: Ident.t): Prop :=
      exists lang st1 lc1 e2,
        (<<TID: IdentMap.find tid c.(Configuration.threads) = Some (existT _ lang st1, lc1)>>) /\
        (<<THREAD_STEPS: rtc (SCThread.all_step L)
                             (Thread.mk _ st1 lc1 c.(Configuration.sc) c.(Configuration.memory)) e2>>) /\
        (<<CONS: Local.promise_consistent e2.(Thread.local)>>) /\
        (<<SCRACE: race e2>>).

    Definition racefree (c: Configuration.t): Prop :=
      forall tid c2
             (STEPS: rtc (SCConfiguration.all_step L) c c2),
        ~ race_steps c2 tid.

    Definition racefree_syn (syn: Threads.syntax): Prop :=
      racefree (Configuration.init syn).

    Lemma step_racefree
          e tid c1 c2
          (RACEFREE: racefree c1)
          (STEP: SCConfiguration.step L e tid c1 c2):
      racefree c2.
    Proof.
      ii. eapply RACEFREE; cycle 1; eauto.
      econs 2; eauto. econs; eauto.
    Qed.
  End SCRace.
End SCRace.
