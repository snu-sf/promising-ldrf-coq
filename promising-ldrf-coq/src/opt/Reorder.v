From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Basic.
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

Require Import FulfillStep.

Require Import SimMemory.
Require Import SimPromises.
Require Import SimLocal.
Require Import SimThread.
Require Import Compatibility.

Require Import ReorderStep.
Require Import ReorderLoad.
Require Import ReorderStore.
Require Import ReorderUpdate.
Require Import ReorderFence.
Require Import ReorderAbort.

Require Import Syntax.
Require Import Semantics.

Set Implicit Arguments.


Inductive reorder: forall (i1 i2:Instr.t), Prop :=
| reorder_intro_load
    r1 l1 o1 i2
    (REORDER: reorder_load r1 l1 o1 i2):
    reorder (Instr.load r1 l1 o1) i2
| reorder_intro_store
    l1 v1 o1 i2
    (REORDER: reorder_store l1 v1 o1 i2):
    reorder (Instr.store l1 v1 o1) i2
| reorder_intro_update
    l1 v1 rmw1 or1 ow1 i2
    (REORDER: reorder_update l1 v1 rmw1 or1 ow1 i2):
    reorder (Instr.update l1 v1 rmw1 or1 ow1) i2
| reorder_intro_fence
    or1 ow1 i2
    (REORDER: reorder_fence or1 ow1 i2):
    reorder (Instr.fence or1 ow1) i2
| reorder_intro_abort
    i2
    (REORDER: reorder_abort i2):
    reorder Instr.abort i2
.

Lemma reorder_sim_stmts
      i1 i2 (REORDER: reorder i1 i2):
  sim_stmts eq
            [Stmt.instr i2; Stmt.instr i1]
            [Stmt.instr i1; Stmt.instr i2]
            eq.
Proof.
  pcofix CIH. ii. subst. pfold. ii. splits; ii.
  { inv TERMINAL_TGT. }
  { right. esplits; eauto.
    inv LOCAL. apply SimPromises.sem_bot_inv in PROMISES; auto. rewrite PROMISES. auto.
  }
  inv STEP_TGT; [inv STEP|inv STEP; inv LOCAL0];
    try (inv STATE; inv INSTR; inv REORDER); ss.
  - (* promise *)
    right.
    exploit sim_local_promise; eauto. i. des.
    esplits; try apply SC; eauto; ss.
    econs 2. econs 1; eauto. econs; eauto. eauto.
  - (* load *)
    right.
    exploit sim_local_read; eauto; try refl. i. des.
    esplits; try apply SC; eauto; ss.
    + econs 1.
    + auto.
    + left. eapply paco9_mon; [apply sim_load_sim_thread|]; ss.
      econs; eauto.
      eapply Local.read_step_future; eauto.
  - (* update-load *)
    right.
    exploit sim_local_read; eauto; try refl. i. des.
    esplits; try apply SC; eauto; ss.
    + econs 1.
    + auto.
    + left. eapply paco9_mon; [apply sim_update_sim_thread|]; ss.
      econs; [eauto|..]; s; eauto.
      eapply Local.read_step_future; eauto.
  - (* store *)
    right.
    exploit Local.write_step_future; eauto; try by viewtac. i. des.
    hexploit sim_local_write_bot; try exact LOCAL1; try exact SC;
      try exact WF_SRC; try refl; viewtac. i. des.
    exploit write_promise_fulfill; eauto; try by viewtac. i. des.
    exploit Local.promise_step_future; eauto. i. des.
    esplits.
    + ss.
    + eauto.
    + econs 2. econs 1. econs; eauto.
    + auto.
    + etrans; eauto.
    + auto.
    + left. eapply paco9_mon; [apply sim_store_sim_thread|done].
      econs; eauto.
  - (* update *)
    right.
    exploit Local.read_step_future; eauto. i. des.
    exploit Local.write_step_future; eauto. i. des.
    exploit sim_local_read; eauto; try refl. i. des.
    exploit Local.read_step_future; eauto. i. des.
    hexploit sim_local_write_bot; try apply LOCAL2; try apply LOCAL0; try apply SC; eauto; try refl; try by viewtac. i. des.
    exploit write_promise_fulfill; eauto; try by viewtac. i. des.
    exploit Local.promise_step_future; eauto. i. des.
    exploit reorder_read_promise; try exact STEP_SRC; try exact STEP1; eauto. i. des.
    exploit Local.promise_step_future; eauto. i. des.
    exploit Local.read_step_future; eauto. i. des.
    exploit sim_local_fulfill_bot; try exact STEP2; try exact LOCAL4; try exact REL1;
      try exact WF3; try refl; eauto; try by viewtac. i. des.
    esplits.
    + ss.
    + eauto.
    + econs 2. econs 1. econs; eauto.
    + auto.
    + etrans; eauto.
    + auto.
    + left. eapply paco9_mon; [apply sim_update_sim_thread|done].
      econs; [eauto|..]; s; eauto.
      etrans; eauto.
  - (* fence *)
    right.
    exploit sim_local_fence; try apply SC; eauto; try refl. i. des.
    esplits.
    + ss.
    + eauto.
    + econs 1.
    + auto.
    + etrans; [|eauto]. inv STEP_SRC. apply TViewFacts.write_fence_sc_incr.
    + auto.
    + left. eapply paco9_mon; [apply sim_fence_sim_thread|]; ss.
      econs; eauto.
  - (* abort *)
    left.
    eapply sim_abort_steps_failure. econs; eauto.
    eapply sim_local_failure; eauto.
Grab Existential Variables.
  { econs 2. }
  { econs. econs 3. }
Qed.
