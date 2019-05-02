Require Import RelationClasses.

Require Import sflib.
From Paco Require Import paco.

Require Import Axioms.
Require Import Basic.
Require Import DataStructure.
Require Import DenseOrder.
Require Import Event.
Require Import Time.
Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import MemoryFacts.
Require Import TView.
Require Import Local.
Require Import Thread.

Set Implicit Arguments.


Lemma concrete_promise_step
      lc1 mem1 loc from to msg lc2 mem2 kind
      mem1'
      (CLOSED1: Memory.closed mem1)
      (WF1: Local.wf lc1 mem1)
      (STEP: Local.promise_step lc1 mem1 loc from to msg lc2 mem2 kind)
      (WF1': Local.wf lc1 mem1')
      (CONCRETE: Memory.concrete mem1 mem1'):
  exists mem2',
    <<STEP': Local.promise_step lc1 mem1' loc from to msg lc2 mem2' kind>> /\
    <<CONCRETE2: Memory.concrete mem2 mem2'>>.
Proof.
  inv WF1. inv STEP. inv PROMISE.
  - exploit Memory.add_get0; try exact MEM. i. des.
    exploit Memory.get_ts; try exact GET0. i. des.
    { subst. inv CLOSED1. rewrite INHABITED in GET. inv GET. }
    exploit (@Memory.add_exists mem1' loc from to msg); eauto.
    { ii. assert (GET3: exists msg, Memory.get loc to2 mem1 = Some (from2, msg)).
      { exploit Memory.concrete_complete; eauto. i. des; eauto. }
      des. exploit Memory.add_o; eauto. erewrite GET3. condtac; ss.
      - des. subst. rewrite GET in GET3. inv GET3.
      - i. des; try congr.
        exploit MemoryFacts.get_disjoint; [exact GET0|exact x2|..]. i. des; try congr.
        eapply x3; eauto. }
    { inv MEM. inv ADD. ss. }
    i. des. esplits.
    + econs; try refl.
      * econs; eauto.
      * 
Admitted.

Lemma concrete_read_step
      lc1 mem1 loc ts val released ord lc2
      mem1'
      (STEP: Local.read_step lc1 mem1 loc ts val released ord lc2)
      (CONCRETE: Memory.concrete mem1 mem1'):
  <<STEP': Local.read_step lc1 mem1' loc ts val released ord lc2>>.
Proof.
Admitted.

Lemma concrete_write_step
      lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind
      mem1'
      (STEP: Local.write_step lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind)
      (CONCRETE: Memory.concrete mem1 mem1'):
  exists mem2',
    <<STEP': Local.write_step lc1 sc1 mem1' loc from to val releasedm released ord lc2 sc2 mem2' kind>> /\
    <<CONCRETE2: Memory.concrete mem2 mem2'>>.
Proof.
Admitted.

Lemma concrete_program_step
      e lc1 sc1 mem1 lc2 sc2 mem2
      mem1'
      (STEP: Local.program_step e lc1 sc1 mem1 lc2 sc2 mem2)
      (CONCRETE: Memory.concrete mem1 mem1'):
  exists mem2',
    <<STEP': Local.program_step e lc1 sc1 mem1' lc2 sc2 mem2'>> /\
    <<CONCRETE2: Memory.concrete mem2 mem2'>>.
Proof.
  inv STEP.
  - esplits; eauto.
  - exploit concrete_read_step; eauto.
  - exploit concrete_write_step; eauto. i. des.
    esplits; eauto.
  - exploit concrete_read_step; eauto. i. des.
    exploit concrete_write_step; eauto. i. des.
    esplits; eauto.
  - esplits; eauto.
  - esplits; eauto.
Qed.
