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
Require Import iCompatibility.

Require Import ReorderStep.
Require Import iReorderLoad.
Require Import iReorderStore.
Require Import iReorderUpdate.
Require Import iReorderFence.
Require Import iReorderAbort.

Require Import ITreeLang.
Require Import Program.

Set Implicit Arguments.


Inductive reorder: forall R0 R1 (i1: MemE.t R0) (i2: MemE.t R1), Prop :=
| reorder_intro_load
    R1 l1 o1 (i2: MemE.t R1)
    (REORDER: reorder_load l1 o1 i2):
    reorder (MemE.read l1 o1) i2
| reorder_intro_store
    R1 l1 v1 o1 (i2: MemE.t R1)
    (REORDER: reorder_store l1 o1 i2):
    reorder (MemE.write l1 v1 o1) i2
| reorder_intro_update
    R1 l1 rmw1 or1 ow1 (i2: MemE.t R1)
    (REORDER: reorder_update l1 or1 ow1 i2):
    reorder (MemE.update l1 rmw1 or1 ow1) i2
| reorder_intro_fence
    R1 or1 ow1 (i2: MemE.t R1)
    (REORDER: reorder_fence or1 ow1 i2):
    reorder (MemE.fence or1 ow1) i2
| reorder_intro_abort
    R1 (i2: MemE.t R1)
    (REORDER: reorder_abort i2):
    reorder MemE.abort i2
.

Lemma reorder_sim_itree R0 R1
      (i1: MemE.t R0) (i2: MemE.t R1) (REORDER: reorder i1 i2):
  sim_itree eq
            (r2 <- ITree.trigger i2;; r1 <- ITree.trigger i1;; Ret (r1, r2))
            (r1 <- ITree.trigger i1;; r2 <- ITree.trigger i2;; Ret (r1, r2)).
Proof.
  replace (r2 <- ITree.trigger i2;; r1 <- ITree.trigger i1;; Ret (r1, r2)) with
      (Vis i2 (fun r2 => Vis i1 (fun r1 => Ret (r1, r2)))).
  2:{ unfold ITree.trigger. grind. repeat f_equal. extensionality r2. grind.
      repeat f_equal. extensionality r1. grind. }
  replace (r1 <- ITree.trigger i1;; r2 <- ITree.trigger i2;; Ret (r1, r2)) with
      (Vis i1 (fun r1 => Vis i2 (fun r2 => Ret (r1, r2)))).
  2:{ unfold ITree.trigger. grind. repeat f_equal. extensionality r2. grind.
      repeat f_equal. extensionality r1. grind. }
  (* unfold trigger. rewrite ! bind_vis. *)
  pcofix CIH. ii. subst. pfold. ii. splits; ii.
  { inv TERMINAL_TGT. eapply f_equal with (f:=observe) in H; ss. }
  { right. esplits; eauto.
    inv LOCAL. apply SimPromises.sem_bot_inv in PROMISES; auto. rewrite PROMISES. auto.
  }
  inv STEP_TGT; [inv STEP|destruct REORDER; inv STEP; ss; dependent destruction STATE; inv LOCAL0]; ss; clarify.
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
    + left. eapply paco11_mon; [apply sim_load_sim_thread|]; ss.
      econs; eauto.
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
    + left. eapply paco11_mon; [apply sim_store_sim_thread|done].
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
    + left. eapply paco11_mon; [apply sim_update_sim_thread|done].
      econs; [eauto|..]; s; eauto.
      etrans; eauto.
  - (* update-load *)
    right.
    exploit sim_local_read; eauto; try refl. i. des.
    esplits; try apply SC; eauto; ss.
    + econs 1.
    + auto.
    + left. eapply paco11_mon; [apply sim_update_sim_thread|]; ss.
      econs; [eauto|..]; s; eauto.
      eapply Local.read_step_future; eauto.
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
    + left. eapply paco11_mon; [apply sim_fence_sim_thread|]; ss.
      econs; eauto.
  - (* abort *)
    left.
    eapply sim_abort_steps_failure. econs; eauto.
    eapply sim_local_failure; eauto.
Grab Existential Variables.
  { i. exact ITree.spin. }
  { econs 2. }
  { econs. econs 3. }
Qed.
