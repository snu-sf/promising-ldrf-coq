From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Basic.
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
Require Import Progress.

Require Import Syntax.
Require Import Semantics.

Set Implicit Arguments.


Lemma progress_program_step_non_update
      rs1 i1 s1 lc1 sc1 mem1
      (WF1: Local.wf lc1 mem1)
      (MEM1: Memory.closed mem1)
      (SC1: Memory.closed_timemap sc1 mem1)
      (PROMISES1: (Local.promises lc1) = Memory.bot)
      (UPDATE: match i1 with Stmt.instr (Instr.update _ _ _ _ _) => False | _ => True end):
  exists e th2, <<STEP: Thread.program_step e (Thread.mk lang (State.mk rs1 (i1::s1)) lc1 sc1 mem1) th2>>.
Proof.
  destruct i1.
  - destruct i; ss; clear UPDATE.
    + esplits. econs; [|econs 1]; eauto. econs. econs.
    + esplits. econs; [|econs 1]; eauto. econs. econs.
    + hexploit progress_read_step; eauto. i. des.
      esplits. econs; [|econs 2]; eauto. econs. econs.
    + hexploit progress_write_step; eauto.
      { apply Time.incr_spec. }
      { i. rewrite PROMISES1. apply Memory.bot_nonsynch_loc. }
      i. des. esplits. econs; [|econs 3]; eauto. econs. econs.
    + hexploit progress_fence_step; eauto.
      { i. rewrite PROMISES1. apply Memory.bot_nonsynch. }
      i. des.
      esplits. econs; [|econs 5]; eauto. econs. econs.
    + hexploit progress_fence_step; eauto.
      { i. rewrite PROMISES1. apply Memory.bot_nonsynch. }
      i. des.
      esplits. econs; [|econs 6]; eauto. econs. econs.
    + hexploit Local.bot_promise_consistent; eauto. i.
      esplits. econs; [|econs 7]; eauto. econs. econs.
  - esplits. econs; [|econs 1]; eauto. econs.
  - esplits. econs; [|econs 1]; eauto. econs.
Grab Existential Variables.
  { auto. }
Qed.
