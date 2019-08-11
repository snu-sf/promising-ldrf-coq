Require Import Bool.
Require Import List.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Basic.
Require Import Event.
Require Import Language.
Require Import Time.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.
Require Import Progress.

Require Import SimMemory.
Require Import SimPromises.
Require Import SimLocal.
Require Import Compatibility.
Require Import SimThread.

Require Import Syntax.
Require Import Semantics.

Set Implicit Arguments.


Lemma intro_load_sim_stmts
      r loc ord:
  sim_stmts (RegFile.eq_except (RegSet.singleton r))
            []
            [Stmt.instr (Instr.load r loc ord)]
            (RegFile.eq_except (RegSet.singleton r)).
Proof.
  pcofix CIH. ii. subst. pfold. ii. splits; try done; i.
  { exploit SimPromises.cap; try apply LOCAL; eauto. }
  { right. esplits; eauto.
    eapply sim_local_memory_bot; eauto.
  }
  ii. right.
  inv STEP_TGT; inv STEP; try (inv STATE; inv INSTR); ss.
  - (* promise *)
    exploit sim_local_promise; eauto. i. des.
    esplits; try apply SC; eauto; ss.
    econs 2. econs 1; eauto. econs; eauto. eauto.
  - (* load *)
    destruct e_tgt; ss. esplits; eauto; ss.
    + econs 1.
    + ss.
    + by inv LOCAL0.
    + by inv LOCAL0.
    + left. eapply paco9_mon; [apply sim_stmts_nil|]; ss.
      * etrans; [eauto|].
        symmetry. apply RegFile.eq_except_singleton.
      * inv LOCAL. inv LOCAL0. inv LOCAL. econs; ss.
        etrans; eauto. apply TViewFacts.read_tview_incr.
Qed.
