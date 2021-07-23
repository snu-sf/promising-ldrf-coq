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

Require Import SimMemory.
Require Import SimPromises.
Require Import SimLocal.
Require Import SimThread.
Require Import Compatibility.

Require Import MergeStep.
Require Import ReorderStep.

Require Import Syntax.
Require Import Semantics.

Set Implicit Arguments.


Lemma assign_sim_thread:
  forall v1 r2
    rs_src rs_tgt lc_src lc_tgt sc0_src sc0_tgt mem0_src mem0_tgt
    (RS: rs_src = RegFun.add r2 (RegFile.eval_value rs_tgt v1) rs_tgt)
    (LOCAL: sim_local SimPromises.bot lc_src lc_tgt),
    sim_thread
      (sim_terminal eq)
      (State.mk rs_src []) lc_src sc0_src mem0_src
      (State.mk rs_tgt [Stmt.instr (Instr.assign r2 (Instr.expr_val v1))]) lc_tgt sc0_tgt mem0_tgt.
Proof.
  pcofix CIH. i. pfold. ii. splits; ii.
  { right. inv TERMINAL_TGT. }
  { right. esplits; eauto.
    eapply sim_local_memory_bot; eauto.
  }
  right.
  inv STEP_TGT; [inv STEP|inv STEP; inv LOCAL0];
    try (inv STATE; inv INSTR); ss.
  - (* promise *)
    exploit sim_local_promise; eauto. i. des.
    esplits; try apply SC; eauto; ss.
    + econs 2. econs 1. econs; eauto.
    + auto.
  - (* load *)
    esplits; try apply SC; eauto; ss.
    + econs 1.
    + auto.
    + left. eapply paco11_mon.
      * apply sim_stmts_nil; eauto.
      * ii. inv PR.
Qed.


(* merge load; instr *)

Lemma merge_load_load_sim_stmts
      l o
      r1
      r2:
  sim_stmts eq
            [Stmt.instr (Instr.load r1 l o); Stmt.instr (Instr.load r2 l o)]
            [Stmt.instr (Instr.load r1 l o); Stmt.instr (Instr.assign r2 (Instr.expr_val (Value.reg r1)))]
            eq.
Proof.
  pcofix CIH. ii. subst. pfold. ii. splits; ii.
  { right. inv TERMINAL_TGT. }
  { right. esplits; eauto.
    eapply sim_local_memory_bot; eauto.
  }
  right.
  inv STEP_TGT; [inv STEP|inv STEP; inv LOCAL0];
    try (inv STATE; inv INSTR); ss.
  - (* promise *)
    exploit sim_local_promise; eauto. i. des.
    esplits; try apply SC; eauto; ss.
    + econs 2. econs 1. econs; eauto.
    + auto.
  - (* load *)
    exploit sim_local_read; try exact LOCAL0; eauto; try refl. i. des.
    exploit merge_read_read; try exact STEP_SRC; eauto. i. des.
    esplits.
    + ss.
    + econs 2; [|econs 1]. econs.
      * econs. econs 2. econs; [|econs 2]; eauto. econs. econs.
      * eauto.
    + econs 2. econs 2. econs; [|econs 2]; eauto. econs. econs.
    + auto.
    + auto.
    + auto.
    + left. eapply paco11_mon.
      * apply assign_sim_thread; eauto. s. rewrite RegFun.add_spec_eq. auto.
      * i. inv PR.
  - (* racy load *)
    exploit sim_local_racy_read; try exact LOCAL1; eauto; try refl. i. des.
    esplits.
    + ss.
    + econs 2; try refl. econs.
      * econs. econs 2. econs; [|econs 9]; eauto. econs. econs.
      * eauto.
    + econs 2. econs 2. econs; [|econs 9]; eauto. econs. econs.
    + ss.
    + ss.
    + ss.
    + left. eapply paco11_mon.
      * apply assign_sim_thread; eauto. s. rewrite RegFun.add_spec_eq. auto.
      * i. inv PR.
Qed.

Lemma merge_load_store_sim_stmts
      l or ow r1
      (OR: Ordering.le Ordering.plain or)
      (OW: Ordering.le Ordering.plain ow):
  sim_stmts eq
            [Stmt.instr (Instr.load r1 l or); Stmt.instr (Instr.store l (Value.reg r1) ow)]
            [Stmt.instr (Instr.update r1 l (Instr.fetch_add (Value.const 0)) or ow)]
            eq.
Proof.
  pcofix CIH. ii. subst. pfold. ii. splits; ii.
  { right. inv TERMINAL_TGT. }
  { right. esplits; eauto.
    eapply sim_local_memory_bot; eauto.
  }
  inv STEP_TGT; [inv STEP|inv STEP; inv LOCAL0];
    try (inv STATE; inv INSTR); ss.
  - (* promise *)
    right.
    exploit sim_local_promise; eauto. i. des.
    esplits; try apply SC; eauto; ss.
    + econs 2. econs 1. econs; eauto.
    + auto.
  - (* update *)
    right.
    clarify. rewrite Const.add_0_r in *.
    exploit sim_local_read; try exact LOCAL; [..|refl|]; eauto. i. des.
    assert (VIEWLE: View.opt_le None releasedr) by eauto.
    exploit Local.read_step_future; try apply LOCAL1; eauto. i. des.
    exploit Local.read_step_future; try apply STEP_SRC; eauto. i. des.
    hexploit sim_local_write; try apply VIEWLE; try exact SC; try exact LOCAL0;
      try match goal with
          | [|- is_true (Ordering.le _ _)] => refl
          end; eauto.
    i. des.
    rewrite SimPromises.unset_bot in *.
    esplits.
    + ss.
    + econs 2; [|econs 1].
      econs.
      * econs. econs 2. econs; [|econs 2]; eauto. econs. econs.
      * eauto.
    + econs 2. econs 2. econs; [|econs 3].
      * econs. ss. econs.
      * ss. rewrite RegFun.add_spec_eq. eauto.
    + ss.
    + ss.
    + ss.
    + left. eapply paco11_mon.
      * apply sim_stmts_nil; eauto.
      * ii. inv PR.
  - (* racy update *)
    left.
    exploit sim_local_racy_update;
      try match goal with
          | [|- is_true (Ordering.le _ _)] => refl
          end; eauto.
    i. des.
    inv x0; try by destruct ordr, ordw; ss.
    unfold Thread.steps_failure. esplits.
    + econs 2; try refl. econs.
      * econs. econs 2. econs; [|econs 9].
        { econs. econs. }
        { econs; eauto; ss. inv RACE. econs; eauto.
          eapply TimeFacts.le_lt_lt; eauto. apply WF_SRC. }
      * ss.
    + econs 2. econs; [|econs 10]; eauto.
      * econs. econs.
      * econs; eauto. ss.
    + ss.
Grab Existential Variables.
{ ss. }
Qed.


(* merge store; instr *)

Lemma merge_store_load_sim_stmts
      l
      v1 o1
      r2 o2
      (O: Ordering.le Ordering.seqcst o2 -> Ordering.le Ordering.seqcst o1):
  sim_stmts eq
            [Stmt.instr (Instr.store l v1 o1); Stmt.instr (Instr.load r2 l o2)]
            [Stmt.instr (Instr.store l v1 o1); Stmt.instr (Instr.assign r2 v1)]
            eq.
Proof.
  pcofix CIH. ii. subst. pfold. ii. splits; ii.
  { right. inv TERMINAL_TGT. }
  { right. esplits; eauto.
    eapply sim_local_memory_bot; eauto.
  }
  inv STEP_TGT; [inv STEP|inv STEP; inv LOCAL0];
    try (inv STATE; inv INSTR); ss.
  - (* promise *)
    right.
    exploit sim_local_promise; eauto. i. des.
    esplits; try apply SC; eauto; ss.
    + econs 2. econs 1. econs; eauto.
    + auto.
  - (* store *)
    right.
    hexploit sim_local_write_bot; try exact LOCAL1; try exact SC; eauto; try refl; try by viewtac. i. des.
    exploit merge_write_read; try exact STEP_SRC; eauto using View.bot_spec. i. des.
    esplits.
    + ss.
    + econs 2; [|econs 1]. econs.
      * econs. econs 2. econs; [|econs 3]; eauto. econs. econs.
      * eauto.
    + econs 2. econs 2. econs; [|econs 2]; eauto. econs. econs.
    + auto.
    + auto.
    + auto.
    + left. eapply paco11_mon.
      * apply assign_sim_thread; auto.
      * i. inv PR.
  - (* na store *)
    right.
    exploit Local.write_undef_step_future; eauto. i. des.
    exploit sim_local_write_undef; try exact LOCAL1; try exact SC; eauto; try refl. i. des.
    exploit Local.write_undef_step_future; eauto. i. des.
    rewrite SimPromises.unset_bot in *.
    hexploit sim_local_write_bot; try exact LOCAL2; try exact SC0; eauto; try refl. i. des.
    exploit merge_write_read; try exact STEP_SRC0; eauto using View.bot_spec. i.
    esplits.
    + ss.
    + econs 2; [|econs 1]. econs.
      * econs. econs 2. econs; [|econs 8]; eauto. econs. econs.
      * eauto.
    + econs 2. econs 2. econs; [|econs 2]; eauto. econs. econs.
    + ss.
    + ss.
    + ss.
    + left. eapply paco11_mon.
      * apply assign_sim_thread; auto.
      * i. inv PR.
  - (* racy store *)
    left.
    exploit sim_local_racy_write; try exact LOCAL1; eauto; try refl. i. des.
    unfold Thread.steps_failure. esplits.
    + refl.
    + econs 2. econs; [|econs 10]; eauto. econs. econs.
    + ss.
Qed.

Lemma merge_store_store_sim_stmts
      l o
      v1
      v2
      (ORD: Ordering.le Ordering.plain o):
  sim_stmts eq
            [Stmt.instr (Instr.store l v1 o); Stmt.instr (Instr.store l v2 o)]
            [Stmt.instr (Instr.store l v2 o)]
            eq.
Proof.
  pcofix CIH. ii. subst. pfold. ii. splits; ii.
  { right. inv TERMINAL_TGT. }
  { right. esplits; eauto.
    eapply sim_local_memory_bot; eauto.
  }
  inv STEP_TGT; [inv STEP|inv STEP; inv LOCAL0];
    try (inv STATE; inv INSTR); ss.
  - (* promise *)
    right.
    exploit sim_local_promise; eauto. i. des.
    esplits; try apply SC; eauto; ss.
    econs 2. econs 1; eauto. econs; eauto. eauto.
  - (* store *)
    right.
    exploit Time.middle_spec.
    { inv LOCAL1. eapply MemoryFacts.write_time_lt. eauto. }
    i. des.
    hexploit sim_local_write_bot;
      try match goal with
          | [|- is_true (Ordering.le _ _)] => refl
          end; try exact LOCAL0; try exact SC; eauto; try refl; try by viewtac. i. des.
    exploit merge_write_write_None; try exact STEP_SRC; eauto; try by viewtac. i. des.
    + esplits.
      * ss.
      * econs 2; [|econs 2; eauto].
        { econs.
          - econs. econs 1. econs; eauto.
          - auto.
        }
        { econs. econs. econs 2. econs; [|econs 3]; eauto.
          - econs. econs.
          - auto.
        }
      * econs 2. econs 2. econs; [|econs 3]; eauto. econs. econs.
      * auto.
      * etrans; eauto.
      * etrans; eauto.
      * left. eapply paco11_mon.
        { apply sim_stmts_nil; eauto. etrans; eauto. }
        { ii. inv PR. }
    + inv STEP1.
      esplits.
      * ss.
      * econs 2; eauto. econs. econs. econs 2.
        econs; [|econs 3]; try exact STEP2; eauto.
        { econs. econs. }
        { auto. }
      * econs 2. econs 2. econs; [|econs 3]; eauto. econs. econs.
      * auto.
      * etrans; eauto.
      * etrans; eauto.
      * left. eapply paco11_mon.
        { apply sim_stmts_nil; eauto. etrans; eauto. }
        { ii. inv PR. }
  - (* na store *)
    inv LOCAL1. destruct ord; ss.
  - (* racy store *)
    left.
    exploit sim_local_racy_write;
      try match goal with
          | [|- is_true (Ordering.le _ _)] => refl
          end; try exact LOCAL1; eauto; try refl. i. des.
    unfold Thread.steps_failure. esplits.
    + refl.
    + econs 2. econs; [|econs 10]; eauto. econs. econs.
    + ss.
Qed.

Lemma merge_store_update_fetch_add_sim_stmts
      l o
      v1
      r2 or2
      (ORD: Ordering.le Ordering.seqcst or2 -> Ordering.le Ordering.seqcst o)
      (ORDW: Ordering.le Ordering.plain o):
   sim_stmts eq
            [Stmt.instr (Instr.store l v1 o); Stmt.instr (Instr.update r2 l (Instr.fetch_add (Value.const 0)) or2 o)]
            [Stmt.instr (Instr.store l v1 o); Stmt.instr (Instr.assign r2 v1)]
            eq.
Proof.
  pcofix CIH. ii. subst. pfold. ii. splits; ii.
  { right. inv TERMINAL_TGT. }
  { right. esplits; eauto.
    eapply sim_local_memory_bot; eauto.
  }
  inv STEP_TGT; [inv STEP|inv STEP; inv LOCAL0];
    try (inv STATE; inv INSTR); ss.
  - (* promise *)
    right.
    exploit sim_local_promise; eauto. i. des.
    esplits; try apply SC; eauto; ss.
    econs 2. econs 1; eauto. econs; eauto. eauto.
  - (* store *)
    right.
    exploit Time.middle_spec; eauto.
    { inv LOCAL1. eapply MemoryFacts.write_time_lt. eauto. }
    i. des.
    hexploit sim_local_write_bot; try exact LOCAL0;
      try match goal with
          | [|- is_true (Ordering.le _ _)] => refl
          end; try exact SC; eauto; try refl; try by viewtac. i. des.
    exploit merge_write_write; try exact STEP_SRC; eauto; try by viewtac. i. des.
    exploit Local.promise_step_future; eauto. i. des.
    exploit Local.write_step_future; try apply STEP2; eauto; try by viewtac. i. des.
    + esplits.
      * ss.
      * econs 2; [|econs 2; eauto].
        { econs.
          - econs. econs 1. econs; eauto.
          - auto.
        }
        { econs. econs. econs 2. econs; [|econs 3]; eauto.
          - econs. econs.
          - auto.
        }
      * econs 2. econs 2. econs; [|econs 4]; eauto.
        { econs. econs. s. rewrite ? Const.add_0_r. eauto. }
        { eapply merge_write_read; try exact STEP2; eauto using View.bot_spec. }
      * auto.
      * etrans; eauto.
      * etrans; eauto.
      * left. eapply paco11_mon.
        { apply assign_sim_thread; eauto. etrans; eauto. }
        { i. inv PR. }
    + inv STEP1.
      esplits.
      * ss.
      * econs 2; eauto. econs. econs. econs 2. econs; [|econs 3]; try exact STEP2; eauto.
        { econs. econs. }
        { auto. }
      * econs 2. econs 2. econs; [|econs 4]; eauto.
        { econs. econs. s. rewrite ? Const.add_0_r. eauto. }
        { eapply merge_write_read; try apply STEP2; eauto using View.bot_spec. }
      * auto.
      * etrans; eauto.
      * etrans; eauto.
      * left. eapply paco11_mon.
        { apply assign_sim_thread; eauto. etrans; eauto. }
        { i. inv PR. }
  - (* na store *)
    inv LOCAL1. destruct ord; ss.
  - (* racy store *)
    left.
    exploit sim_local_racy_write;
      try match goal with
          | [|- is_true (Ordering.le _ _)] => refl
          end; try exact LOCAL1; eauto; try refl. i. des.
    unfold Thread.steps_failure. esplits.
    + refl.
    + econs 2. econs; [|econs 10]; eauto. econs. econs.
    + ss.
Qed.

Lemma merge_store_update_cas_sim_stmts
      l o
      v1 v2
      r2 or2
      (ORD: Ordering.le Ordering.seqcst or2 -> Ordering.le Ordering.seqcst o)
      (ORDW: Ordering.le Ordering.plain o):
   sim_stmts eq
            [Stmt.instr (Instr.store l v1 o); Stmt.instr (Instr.update r2 l (Instr.cas v1 v2) or2 o)]
            [Stmt.instr (Instr.store l v2 o); Stmt.instr (Instr.assign r2 (Value.const 1))]
            eq.
Proof.
  pcofix CIH. ii. subst. pfold. ii. splits; ii.
  { right. inv TERMINAL_TGT. }
  { right. esplits; eauto.
    eapply sim_local_memory_bot; eauto.
  }
  inv STEP_TGT; [inv STEP|inv STEP; inv LOCAL0];
    try (inv STATE; inv INSTR); ss.
  - (* promise *)
    right.
    exploit sim_local_promise; eauto. i. des.
    esplits; try apply SC; eauto; ss.
    econs 2. econs 1; eauto. econs; eauto. eauto.
  - (* store *)
    right.
    exploit Time.middle_spec; eauto.
    { inv LOCAL1. eapply MemoryFacts.write_time_lt. eauto. }
    i. des.
    hexploit sim_local_write_bot; try exact LOCAL0;
      try match goal with
          | [|- is_true (Ordering.le _ _)] => refl
          end; try exact SC; eauto; try refl; try by viewtac. i. des.
    exploit merge_write_write; try exact STEP_SRC; eauto; try by viewtac. i. des.
    + exploit Local.promise_step_future; eauto. i. des.
      exploit Local.write_step_future; try apply STEP2; eauto; try by viewtac. i. des.
      esplits.
      * ss.
      * econs 2; [|econs 2; eauto].
        { econs.
          - econs. econs 1. econs; eauto.
          - auto.
        }
        { econs. econs. econs 2. econs; [|econs 3]; eauto.
          - econs. econs.
          - auto.
        }
      * econs 2. econs 2. econs; [|econs 4]; eauto.
        { econs. econs. s.
          instantiate (2 := RegFile.eval_value rf2 v1).
          condtac; [refl|congr]. }
        { eapply merge_write_read; try exact STEP2; eauto using View.bot_spec. }
      * auto.
      * etrans; eauto.
      * etrans; eauto.
      * left. eapply paco11_mon.
        { apply assign_sim_thread; eauto. etrans; eauto. }
        { i. inv PR. }
    + inv STEP1.
      esplits.
      * ss.
      * econs 2; eauto. econs. econs. econs 2. econs; [|econs 3]; try exact STEP2; eauto.
        { econs. econs. }
        { auto. }
      * econs 2. econs 2. econs; [|econs 4]; eauto.
        { econs. econs. s.
          instantiate (2 := RegFile.eval_value rf2 v1).
          condtac; [refl|congr]. }
        { eapply merge_write_read; try apply STEP2; eauto using View.bot_spec. }
      * auto.
      * etrans; eauto.
      * etrans; eauto.
      * left. eapply paco11_mon.
        { apply assign_sim_thread; eauto. etrans; eauto. }
        { i. inv PR. }
  - (* na store *)
    inv LOCAL1. destruct ord; ss.
  - (* racy store *)
    left.
    exploit sim_local_racy_write;
      try match goal with
          | [|- is_true (Ordering.le _ _)] => refl
          end; try exact LOCAL1; eauto; try refl. i. des.
    unfold Thread.steps_failure. esplits.
    + refl.
    + econs 2. econs; [|econs 10]; eauto. econs. econs.
    + ss.
Qed.


(* merge update; instr *)

Lemma merge_update_load_sim_stmts
      l
      r1 v1 or ow
      r2 or2
      (O: Ordering.le Ordering.seqcst or2 -> Ordering.le Ordering.seqcst ow)
      (OR2: Ordering.le or2 or):
  sim_stmts eq
            [Stmt.instr (Instr.update r1 l (Instr.fetch_add v1) or ow); Stmt.instr (Instr.load r2 l or2)]
            [Stmt.instr (Instr.update r1 l (Instr.fetch_add v1) or ow); Stmt.instr (Instr.assign r2 r1)]
            eq.
Proof.
  pcofix CIH. ii. subst. pfold. ii. splits; ii.
  { right. inv TERMINAL_TGT. }
  { right. esplits; eauto.
    eapply sim_local_memory_bot; eauto.
  }
  inv STEP_TGT; [inv STEP|inv STEP; inv LOCAL0];
    try (inv STATE; inv INSTR); ss.
  - (* promise *)
    right.
    exploit sim_local_promise; eauto. i. des.
    esplits; try apply SC; eauto; ss.
    econs 2. econs 1; eauto. econs; eauto. eauto.
  - (* update *)
    right.
    exploit Local.read_step_future; eauto. i. des.
    exploit Local.write_step_future; eauto. i. des.
    exploit merge_write_read; try apply LOCAL2; eauto.
    { inv LOCAL1. s. i. repeat (try condtac; aggrtac).
      destruct ordr, or2; inv H; inv COND; inv OR2.
    }
    { inv LOCAL1. s. i. repeat (try condtac; aggrtac).
      destruct ordr, or2; inv H; inv COND; inv OR2.
    }
    i. des.
    exploit sim_local_read; try exact LOCAL1;
      try match goal with
          | [|- is_true (Ordering.le _ _)] => refl
          end; eauto; try refl; try by viewtac. i. des.
    exploit Local.read_step_future; eauto; try by viewtac. i. des.
    hexploit sim_local_write_bot; try apply SC; try apply LOCAL2; eauto; try refl. i. des.
    exploit Local.write_step_future; try apply STEP_SRC; eauto; try by viewtac. i. des.
    exploit sim_local_read; try exact x0; eauto; try refl. i. des.
    esplits.
    + ss.
    + econs 2; [|econs 1]. econs.
      * econs. econs 2. econs; [|econs 4]; eauto. econs. econs. eauto.
      * eauto.
    + econs 2. econs 2. econs; [|econs 2]; eauto. econs. econs.
    + auto.
    + auto.
    + auto.
    + left. eapply paco11_mon.
      * apply assign_sim_thread; auto. s. rewrite RegFun.add_spec_eq. inv RMW. auto.
      * i. inv PR.
  - (* racy update *)
    left.
    exploit sim_local_racy_update;
      try match goal with
          | [|- is_true (Ordering.le _ _)] => refl
          end; try exact LOCAL1; eauto; try refl. i. des.
    unfold Thread.steps_failure. esplits.
    + refl.
    + econs 2. econs; [|econs 11]; eauto. econs. econs. ss.
    + ss.
      Unshelve. ss.
Qed.

Lemma merge_update_store_sim_stmts
      l or ow
      r1 v1 v2 v3
      (VAL: v3 <> Value.reg r1):
  sim_stmts eq
            [Stmt.instr (Instr.update r1 l (Instr.cas v1 v2) or ow);
               Stmt.ite (Instr.expr_op2 Op2.eq (Value.reg r1) (Value.const 1))
                        [Stmt.instr (Instr.store l v3 ow)]
                        nil]
            [Stmt.instr (Instr.update r1 l (Instr.cas v1 v3) or ow)]
            eq.
Proof.
  pcofix CIH. ii. subst. pfold. ii. splits; ii.
  { right. inv TERMINAL_TGT. }
  { right. esplits; eauto.
    eapply sim_local_memory_bot; eauto.
  }
  inv STEP_TGT; [inv STEP|inv STEP; inv LOCAL0];
    try (inv STATE; inv INSTR); ss.
  - (* promise *)
    right.
    exploit sim_local_promise; eauto. i. des.
    esplits; try apply SC; eauto ; ss.
    econs 2. econs 1; eauto. econs; eauto. eauto.
  - (* update fail *)
    right.
    des_ifs. exploit Local.read_step_future; eauto. i. des.
    exploit sim_local_read; try exact LOCAL1;
      try match goal with
          | [|- is_true (Ordering.le _ _)] => refl
          end; eauto; try refl; try by viewtac. i. des.
    exploit Local.read_step_future; try exact STEP_SRC; eauto. i. des.
    esplits.
    + ss.
    + econs 2; [|eauto]. econs.
      * econs. econs 2. econs; [|econs 2]; try exact STEP_SRC. s.
        econs. econs. s. condtac; ss.
      * ss.
    + econs 2. econs 2. econs; [|econs 1]. s. econs.
    + ss.
    + ss.
    + ss.
    + ss. rewrite RegFun.add_spec_eq. condtac; ss.
      left. eapply paco11_mon.
      * apply sim_stmts_nil; eauto.
      * i. inv PR.
  - (* update success *)
    right.
    exploit Time.middle_spec; eauto.
    { inv LOCAL2. eapply MemoryFacts.write_time_lt. eauto. }
    i. des.
    exploit Local.read_step_future; eauto. i. des.
    exploit sim_local_read; try exact LOCAL1;
      try match goal with
          | [|- is_true (Ordering.le _ _)] => refl
          end; eauto; try refl; try by viewtac. i. des.
    exploit Local.read_step_future; eauto. i. des.
    hexploit sim_local_write_bot; try exact LOCAL2; try exact SC; eauto; try refl. i. des.
    exploit merge_write_write_None; try exact STEP_SRC0; eauto.
    { inv STEP_SRC. inv MEM_SRC. exploit CLOSED; eauto. i. des.
      inv MSG_TS. ss. }
    i. des.
    + exploit Local.promise_step_future; eauto. i. des.
      exploit Local.write_step_future; try apply STEP2; eauto; try by viewtac. i. des.
      exploit reorder_read_promise_diff; try exact STEP_SRC; try exact STEP1; eauto.
      { inv LOCAL2. exploit MemoryFacts.write_time_lt; eauto. ii. inv H.
        eapply Time.lt_strorder. eauto.
      }
      i. des.
      esplits.
      * ss.
      * econs 2; [|econs 2; [|econs 2;eauto]].
        { econs.
          - econs. econs 1. econs; eauto.
          - auto.
        }
        { econs.
          - econs. econs 2. econs; [|econs 4]; try exact STEP4; try exact STEP_SRC0; eauto.
            econs. econs. s. condtac; ss.
          - auto.
        }
        { econs.
          - econs. econs 2. econs; [|econs 1]. s. econs.
          - ss.
        }
      * ss. rewrite RegFun.add_spec_eq. condtac; ss.
        econs 2. econs 2. econs; [|econs 3]; eauto. econs. s.
        instantiate (1 := RegFun.add r1 1 rs_tgt).
        revert RMW. condtac; ss. i. inv RMW.
        replace (RegFile.eval_value rs_tgt v3) with (RegFile.eval_value (RegFun.add r1 1 rs_tgt) v3); try econs.
        destruct v3; ss.
        rewrite RegFun.add_spec_neq; ss. congr.
      * auto.
      * etrans; eauto.
      * etrans; eauto.
      * left. eapply paco11_mon.
        { apply sim_stmts_nil; eauto.
          - revert RMW. condtac; ss. i. inv RMW. ss.
          - etrans; eauto. }
        { i. inv PR. }
    + inv STEP1.
      exploit Local.write_step_future; try apply STEP2; eauto; try by viewtac. i. des.
      esplits.
      * ss.
      * econs 2; [|econs 2; eauto].
        { econs.
          - econs. econs 2. econs; [|econs 4]; try exact STEP_SRC; try exact STEP2; eauto.
            econs. econs. s. condtac; ss.
          - auto.
        }
        { econs.
          - econs. econs 2. econs; [|econs 1]. s. econs.
          - ss.
        }
      * ss. rewrite RegFun.add_spec_eq. condtac; ss.
        econs 2. econs 2. econs; [|econs 3]; eauto. econs. s.
        instantiate (1 := RegFun.add r1 1 rs_tgt).
        revert RMW. condtac; ss. i. inv RMW.
        replace (RegFile.eval_value rs_tgt v3) with (RegFile.eval_value (RegFun.add r1 1 rs_tgt) v3); try econs.
        destruct v3; ss.
        rewrite RegFun.add_spec_neq; ss. congr.
      * auto.
      * etrans; eauto.
      * etrans; eauto.
      * left. eapply paco11_mon.
        { apply sim_stmts_nil; eauto.
          - revert RMW. condtac; ss. i. inv RMW. ss.
          - etrans; eauto. }
        { i. inv PR. }
  - (* racy load *)
    right.
    revert RMW. condtac; ss. i. inv RMW.
    exploit sim_local_racy_read; try exact LOCAL1; eauto; try refl. i. des.
    esplits.
    + ss.
    + econs 2; try refl. econs.
      * econs. econs 2. econs; [|econs 9]; eauto. econs. econs. ss.
        rewrite COND. ss.
      * eauto.
    + econs 2. econs 2. econs; [|econs 1]; eauto. econs.
    + ss.
    + ss.
    + ss.
    + ss. rewrite RegFun.add_spec_eq. condtac; ss.
      left. eapply paco11_mon.
      * apply sim_stmts_nil; eauto.
      * i. inv PR.
  - (* racy update *)
    left.
    revert RMW. condtac; ss. i. inv RMW.
    exploit sim_local_racy_update;
      try match goal with
          | [|- is_true (Ordering.le _ _)] => refl
          end; try exact LOCAL1; eauto; try refl. i. des.
    unfold Thread.steps_failure. esplits.
    + refl.
    + econs 2. econs; [|econs 11]; eauto. econs. econs. ss.
      rewrite COND. ss.
    + ss.
Qed.

Lemma merge_update_update_sim_stmts
      l or ow
      r1 v1
      r2 or2
      (O: Ordering.le Ordering.seqcst or2 -> Ordering.le Ordering.seqcst ow)
      (OR2: Ordering.le or2 or):
  sim_stmts eq
            [Stmt.instr (Instr.update r1 l (Instr.fetch_add v1) or ow); Stmt.instr (Instr.update r2 l (Instr.fetch_add 0) or2 ow)]
            [Stmt.instr (Instr.update r1 l (Instr.fetch_add v1) or ow); Stmt.instr (Instr.assign r2 r1)]
            eq.
Proof.
  pcofix CIH. ii. subst. pfold. ii. splits; ii.
  { right. inv TERMINAL_TGT. }
  { right. esplits; eauto.
    eapply sim_local_memory_bot; eauto.
  }
  inv STEP_TGT; [inv STEP|inv STEP; inv LOCAL0];
    try (inv STATE; inv INSTR); ss.
  - (* promise *)
    right.
    exploit sim_local_promise; eauto. i. des.
    esplits; try apply SC; eauto ; ss.
    econs 2. econs 1; eauto. econs; eauto. eauto.
  - (* update *)
    right.
    exploit Time.middle_spec; eauto.
    { inv LOCAL2. eapply MemoryFacts.write_time_lt. eauto. }
    i. des.
    exploit Local.read_step_future; eauto. i. des.
    exploit sim_local_read; try exact LOCAL1;
      try match goal with
          | [|- is_true (Ordering.le _ _)] => refl
          end; eauto; try refl; try by viewtac. i. des.
    exploit Local.read_step_future; eauto. i. des.
    hexploit sim_local_write_bot; try exact LOCAL2; try exact SC; eauto; try refl. i. des.
    exploit merge_write_write; try exact STEP_SRC0; eauto.
    { inv STEP_SRC. inv MEM_SRC. exploit CLOSED; eauto. i. des.
      inv MSG_TS. ss. }
    i. des.
    + exploit Local.promise_step_future; eauto. i. des.
      exploit Local.write_step_future; try apply STEP2; eauto; try by viewtac. i. des.
      exploit reorder_read_promise_diff; try exact STEP_SRC; try exact STEP1; eauto.
      { inv LOCAL2. exploit MemoryFacts.write_time_lt; eauto. ii. inv H.
        eapply Time.lt_strorder. eauto.
      }
      i. des.
      esplits.
      * ss.
      * econs 2; [|econs 2; eauto].
        { econs.
          - econs. econs 1. econs; eauto.
          - auto.
        }
        { econs. econs. econs 2. econs; [|econs 4]; try exact STEP4; try exact STEP_SRC0; eauto.
          - econs. econs. s. eauto.
          - auto.
        }
      * econs 2. econs 2. econs; [|econs 4]; eauto.
        { econs. econs. s. rewrite ? Const.add_0_r. eauto. }
        { inv RMW. eapply merge_write_read; try exact STEP2; viewtac.
          - inv STEP4. s. repeat (try condtac; aggrtac).
            destruct or2, ordr; inv H; inv OR2; inv COND.
          - inv STEP4. s. repeat (try condtac; aggrtac).
            destruct or2, ordr; inv H; inv OR2; inv COND.
        }
      * auto.
      * etrans; eauto.
      * etrans; eauto.
      * left. eapply paco11_mon.
        { apply assign_sim_thread; eauto.
          - s. unfold RegFun.find. unfold RegFun.add at 4. condtac; [|congr]. auto.
          - etrans; eauto.
        }
        { i. inv PR. }
    + inv STEP1.
      exploit Local.write_step_future; try apply STEP2; eauto; try by viewtac. i. des.
      esplits.
      * ss.
      * econs 2; eauto.
        econs. econs. econs 2. econs; [|econs 4]; try exact STEP_SRC; try exact STEP2; eauto.
        { econs. econs. s. eauto. }
        { auto. }
      * econs 2. econs 2. econs; [|econs 4]; eauto.
        { econs. econs. s. rewrite ? Const.add_0_r. eauto. }
        { inv RMW. eapply merge_write_read; try exact STEP2; viewtac.
          - inv STEP_SRC. s. repeat (try condtac; aggrtac).
            destruct or2, ordr; inv H; inv OR2; inv COND.
          - inv STEP_SRC. s. repeat (try condtac; aggrtac).
            destruct or2, ordr; inv H; inv OR2; inv COND.
        }
      * auto.
      * etrans; eauto.
      * etrans; eauto.
      * left. eapply paco11_mon.
        { apply assign_sim_thread; eauto.
          - s. unfold RegFun.find. unfold RegFun.add at 4. condtac; [|congr]. auto.
          - etrans; eauto.
        }
        { i. inv PR. }
  - left.
    exploit sim_local_racy_update;
      try match goal with
          | [|- is_true (Ordering.le _ _)] => refl
          end; eauto.
    i. des.
    unfold Thread.steps_failure. esplits.
    + refl.
    + econs 2. econs; [|econs 11]; eauto. econs. econs. ss.
    + ss.
      Unshelve. ss.
Qed.


(* merge fence; instr *)

Lemma merge_fence_fence_sim_stmts
      ordr ordw:
  sim_stmts eq
            [Stmt.instr (Instr.fence ordr ordw); Stmt.instr (Instr.fence ordr ordw)]
            [Stmt.instr (Instr.fence ordr ordw)]
            eq.
Proof.
  pcofix CIH. ii. subst. pfold. ii. splits; ii.
  { right. inv TERMINAL_TGT. }
  { right. esplits; eauto.
    eapply sim_local_memory_bot; eauto.
  }
  right.
  inv STEP_TGT; [inv STEP|inv STEP; inv LOCAL0];
    try (inv STATE; inv INSTR); ss.
  - (* promise *)
    exploit sim_local_promise; eauto. i. des.
    esplits; try apply SC; eauto; ss.
    econs 2. econs 1; eauto. econs; eauto. eauto.
  - (* fence *)
    exploit sim_local_fence; try exact LOCAL0; try exact SC; eauto; try refl. i. des.
    exploit merge_fence_fence; try exact STEP_SRC; eauto. i. des.
    esplits.
    + ss.
    + econs 2; [|econs 1]. econs.
      * econs. econs 2. econs; [|econs 5]; eauto. econs. econs.
      * eauto.
    + econs 2. econs 2. econs; [|econs 5]; eauto. econs. econs.
    + auto.
    + etrans; eauto.
    + auto.
    + left. eapply paco11_mon.
      * apply sim_stmts_nil; eauto. etrans; eauto.
      * ii. inv PR.
Qed.
