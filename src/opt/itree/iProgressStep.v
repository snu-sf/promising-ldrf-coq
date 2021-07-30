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

Require Import ITreeLang.

Set Implicit Arguments.


Lemma progress_program_step_non_update
      R0 R1 (pe: MemE.t R0) (k: ktree MemE.t R0 R1) lc1 sc1 mem1
      (WF1: Local.wf lc1 mem1)
      (MEM1: Memory.closed mem1)
      (SC1: Memory.closed_timemap sc1 mem1)
      (PROMISES1: (Local.promises lc1) = Memory.bot)
      (UPDATE: match pe with | MemE.update _ _ _ _ => False | _ => True end):
  exists e th2, <<STEP: Thread.program_step e (Thread.mk (lang R1) (Vis pe k) lc1 sc1 mem1) th2>>.
Proof.
  destruct pe; ss.
  - hexploit progress_read_step; eauto. i. des.
    esplits. econs; [|econs 2]; eauto. econs. econs.
  - hexploit progress_write_step; eauto.
    { apply Time.incr_spec. }
    { i. rewrite PROMISES1. apply Memory.bot_nonsynch_loc. }
    i. des. esplits. econs; [|econs 3]; eauto. econs. econs.
  - hexploit progress_fence_step; eauto.
    { i. rewrite PROMISES1. apply Memory.bot_nonsynch. }
    i. des.
    esplits. econs; [|econs 5]; eauto. econs. econs.
  - hexploit progress_fence_step; eauto.
    { i. rewrite PROMISES1. apply Memory.bot_nonsynch. }
    i. des.
    esplits. econs; [|econs 6]; eauto. econs. econs.
  - hexploit Local.bot_promise_consistent; eauto. i.
    esplits. econs; [|econs 7]; eauto. econs.
  - esplits. econs; [|econs 1]; eauto. econs. econs.
Grab Existential Variables.
  all: try exact 0. all: try exact ITree.spin.
Qed.
