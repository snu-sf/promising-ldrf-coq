Require Import RelationClasses.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import Loc.
From PromisingLib Require Import DenseOrder.
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
Require Import Behavior.

Require Import Cover.
Require Import MemorySplit.
Require Import MemoryMerge.
Require Import FulfillStep.
Require Import PromiseConsistent.
Require Import MemoryProps.

Require Import Program.


Set Implicit Arguments.


Module Messages.
  Definition t := forall (loc: Loc.t) (to: Time.t) (from: Time.t) (msg: Message.t), Prop.

  Variant of_memory (mem: Memory.t): t :=
  | of_memory_intro
      loc to from msg
      (GET: Memory.get loc to mem = Some (from, msg))
    :
      of_memory mem loc to from msg
  .
End Messages.

Lemma other_promise_unchangable mem ths sc tid1 tid2 st1 st2 tvw1 prom1 tvw2 prom2
      (CWF: Configuration.wf (Configuration.mk ths sc mem))
      (TID1: IdentMap.find tid1 ths = Some (st1, Local.mk tvw1 prom1))
      (TID2: IdentMap.find tid2 ths = Some (st2, Local.mk tvw2 prom2))
      (DIFF: tid1 <> tid2)
  :
    Messages.of_memory prom2 <4= unchangable mem prom1.
Proof.
  ii. inv PR.
  inv CWF. inv WF. destruct st1, st2. econs; eauto.
  - exploit THREADS; try apply TID2; eauto. intros LCWF. inv LCWF. eauto.
  - destruct (Memory.get x0 x1 prom1) eqn:GET0; eauto. exfalso.
    exploit DISJOINT; eauto. intros LCDISJ. inv LCDISJ. destruct p.
    inv DISJOINT0. exploit DISJOINT1; eauto. i. des.
    eapply Memory.get_ts in GET. eapply Memory.get_ts in GET0. des; clarify.
    eapply x5; eauto.
    + instantiate (1:=x1). econs; ss; eauto. refl.
    + econs; ss; eauto. refl.
Qed.


Section FINALIZED.
  Variant finalized (c: Configuration.t) (l: Loc.t) (t: Time.t) (from: Time.t) (msg: Message.t): Prop :=
  | finalized_intro
      (GET: Memory.get l t c.(Configuration.memory) = Some (from, msg))
      (NPROM: forall tid st lc
                     (TID: IdentMap.find tid c.(Configuration.threads) = Some (st, lc)),
          Memory.get l t lc.(Local.promises) = None)
  .

  Lemma finalized_unchangable c tid st lc
        (FIND: IdentMap.find tid c.(Configuration.threads) = Some (st, lc))
    :
      finalized c <4= unchangable c.(Configuration.memory) lc.(Local.promises).
  Proof.
    i. inv PR. econs; eauto.
  Qed.

  Variant committed (mem0 prom0 mem1 prom1: Memory.t)
          (l: Loc.t) (t: Time.t) (from: Time.t) (msg: Message.t): Prop :=
  | committed_intro
      (UNCHANGABLE: unchangable mem1 prom1 l t from msg)
      (NUNCHANGABLE: ~ unchangable mem0 prom0 l t from msg)
  .

  Lemma committed_same prom mem fin
    :
      fin \4/ committed mem prom mem prom = fin.
  Proof.
    extensionality loc. extensionality to. extensionality from. extensionality msg.
    eapply Coq.Logic.PropExtensionality.propositional_extensionality.
    split; auto. i. des; auto.
    exfalso. inv H. ss.
  Qed.

  Lemma committed_trans
        lang e1 e2 e3
        (STEPS1: rtc (@Thread.all_step lang) e1 e2)
        (STEPS2: rtc (@Thread.all_step lang) e2 e3):
    committed (Thread.memory e1) (Local.promises (Thread.local e1))
              (Thread.memory e3) (Local.promises (Thread.local e3)) =
    (committed (Thread.memory e1) (Local.promises (Thread.local e1))
               (Thread.memory e2) (Local.promises (Thread.local e2)) \4/
     committed (Thread.memory e2) (Local.promises (Thread.local e2))
               (Thread.memory e3) (Local.promises (Thread.local e3))).
  Proof.
    extensionality loc. extensionality to. extensionality from. extensionality msg.
    eapply Coq.Logic.PropExtensionality.propositional_extensionality.
    split; i; des.
    { inv H.
      destruct (classic (unchangable (Thread.memory e2) (Local.promises (Thread.local e2))
                                     loc to from msg)).
      - left. econs; eauto.
      - right. econs; eauto.
    }
    { inv H. econs; eauto.
      eapply unchangable_rtc_all_step_increase; eauto.
    }
    { inv H. econs; eauto.
      ii. apply NUNCHANGABLE.
      eapply unchangable_rtc_all_step_increase; eauto.
    }
  Qed.

  Definition step_finalized e tid c0 c1
             (STEP: Configuration.step e tid c0 c1)
             (WF: Configuration.wf c0)
    :
      finalized c0 <4= finalized c1.
  Proof.
    ii. inv STEP.
    hexploit finalized_unchangable; eauto. i.
    hexploit unchangable_rtc_tau_step_increase; eauto. i.
    hexploit unchangable_increase; eauto. i. ss.
    inv H1. econs; eauto. i. ss.
    rewrite IdentMap.gsspec in TID0. des_ifs.
    inv PR. eapply NPROM0; eauto.
  Qed.

  Definition step_committed_finalized e tid c0 c1 st0 st1 lc0 lc1
             (STEP: Configuration.step e tid c0 c1)
             (FIND0: IdentMap.find tid c0.(Configuration.threads) = Some (st0, lc0))
             (FIND1: IdentMap.find tid c1.(Configuration.threads) = Some (st1, lc1))
             (WF: Configuration.wf c0)
    :
      committed c0.(Configuration.memory) lc0.(Local.promises) c1.(Configuration.memory) lc1.(Local.promises) <4= finalized c1.
  Proof.
    hexploit Configuration.step_future; eauto. i. des.
    ii. inv PR. dup UNCHANGABLE. inv UNCHANGABLE. econs; eauto.
    i. inv STEP. ss.
    rewrite IdentMap.gss in FIND1. clarify.
    dup TID. rewrite IdentMap.gsspec in TID. des_ifs.
    destruct (Memory.get x0 x1 lc.(Local.promises)) as [[from msg]|] eqn:EQ; auto.
    exfalso. eapply NUNCHANGABLE.
    destruct c0, lc, lc0. ss.
    eapply other_promise_unchangable with (tid1:=tid) (tid2:=tid0); eauto.
    econs; eauto. inv WF2. ss.
    inv WF0. destruct st. exploit THREADS; eauto.
    i. inv x4. ss. rewrite EQ. eapply PROMISES in EQ. clarify.
  Qed.
End FINALIZED.

Lemma memory_init_get_if loc to from msg
      (GET: Memory.get loc to Memory.init = Some (from, msg))
  :
    to = Time.bot /\ from = Time.bot /\ msg = Message.elt.
Proof.
  unfold Memory.get, Memory.init in *.
  erewrite Cell.init_get in GET. des_ifs.
Qed.

Lemma memory_init_get loc
  :
  Memory.get loc Time.bot Memory.init = Some (Time.bot, Message.elt).
Proof.
  unfold Memory.get, Memory.init in *.
  erewrite Cell.init_get. des_ifs.
Qed.
