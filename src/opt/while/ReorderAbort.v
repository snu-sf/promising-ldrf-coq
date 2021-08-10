From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
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
Require Import Progress.

Require Import LowerPromises.

Require Import SimMemory.
Require Import SimPromises.
Require Import SimLocal.
Require Import SimThread.
Require Import Compatibility.
Require Import ReorderAbortCommon.

Require Import Syntax.
Require Import Semantics.

Set Implicit Arguments.


Inductive reorder_abort: forall (i2:Instr.t), Prop :=
| reorder_abort_load
    r2 l2 o2
    (ORD2: Ordering.le o2 Ordering.relaxed):
    reorder_abort (Instr.load r2 l2 o2)
| reorder_abort_store
    l2 v2 o2
    (ORD21: Ordering.le o2 Ordering.acqrel)
    (ORD22: Ordering.le Ordering.plain o2):
    reorder_abort (Instr.store l2 v2 o2)
| reorder_abort_fence
    or2 ow2
    (ORDR2: Ordering.le or2 Ordering.relaxed)
    (ORDW2: Ordering.le ow2 Ordering.acqrel):
    reorder_abort (Instr.fence or2 ow2)
.

Inductive sim_abort: forall (st_src:(Language.state lang)) (lc_src:Local.t) (sc1_src:TimeMap.t) (mem1_src:Memory.t), Prop :=
| sim_abort_intro
    rs i2
    lc1_src sc1_src mem1_src
    (REORDER: reorder_abort i2)
    (FAILURE: Local.failure_step lc1_src)
    (WF_SRC: Local.wf lc1_src mem1_src)
    (SC_SRC: Memory.closed_timemap sc1_src mem1_src)
    (MEM_SRC: Memory.closed mem1_src):
    sim_abort
      (State.mk rs [Stmt.instr i2; Stmt.instr Instr.abort]) lc1_src sc1_src mem1_src
.

Lemma sim_abort_steps_failure
      st1_src lc1_src sc1_src mem1_src
      (SIM: sim_abort st1_src lc1_src sc1_src mem1_src):
  Thread.steps_failure (Thread.mk lang st1_src lc1_src sc1_src mem1_src).
Proof.
  inv SIM. inv FAILURE. unfold Thread.steps_failure.
  inv REORDER.
  - (* load *)
    exploit progress_read_step_cur; try exact WF_SRC; eauto. i. des.
    exploit read_step_cur_future; try exact READ; eauto. i. des.
    esplits.
    + econs 2; try refl. econs.
      * econs. econs 2. econs; [|econs 2]; eauto. econs. econs.
      * ss.
    + econs 2. econs; [|econs 7].
      * econs. econs.
      * econs. ii.
        rewrite <- TVIEW. rewrite <- PROMISES in *. eauto.
    + ss.
  - (* store *)
    exploit (@LowerPromises.steps_promises_rel
               lang (Thread.mk lang (State.mk rs [Stmt.instr (Instr.store l2 v2 o2); Stmt.instr Instr.abort])
                               lc1_src sc1_src mem1_src)); s; eauto.
    i. des. destruct e2, state. ss.
    exploit LowerPromises.rtc_opt_promise_step_future; eauto. s. i. des. inv STATE.
    hexploit LowerPromises.promises_rel_promise_consistent; eauto. i.
    hexploit LowerPromises.promises_rel_nonsynch; eauto. i.
    exploit Thread.rtc_tau_step_future; try exact STEPS0; eauto. s. i. des.
    exploit write_step_consistent; try exact WF2; eauto. i. des.
    esplits.
    + eapply rtc_n1; eauto. econs.
      * econs. econs 2. econs; [|econs 3; eauto]. econs. econs.
      * ss.
    + econs 2. econs; [|econs 7].
      * econs. econs.
      * econs. ss.
    + ss.
  - (* fence *)
    exploit (@LowerPromises.steps_promises_rel
               lang (Thread.mk lang (State.mk rs [Stmt.instr (Instr.fence or2 ow2); Stmt.instr Instr.abort])
                               lc1_src sc1_src mem1_src)); s; eauto.
    i. des. destruct e2, state. ss.
    exploit LowerPromises.rtc_opt_promise_step_future; eauto. s. i. des. inv STATE.
    hexploit LowerPromises.promises_rel_promise_consistent; eauto. i.
    hexploit LowerPromises.promises_rel_nonsynch; eauto. i.
    exploit progress_fence_step; eauto.
    { instantiate (1:=ow2). i. subst. ss. }
    i. des.
    esplits.
    + eapply rtc_n1; eauto. econs.
      * econs. econs 2. econs; [|econs 5]; eauto. econs. econs.
      * ss.
    + econs 2. econs; [|econs 7].
      * econs. econs.
      * exploit fence_step_future; eauto. i. des.
        econs. ii. rewrite <- PROMISES in *. rewrite <- TVIEW0. eauto.
    + ss.
Qed.
