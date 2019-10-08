Require Import Omega.
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
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.

Require Import Syntax.
Require Import Semantics.

Require Import PromiseConsistent.

Require Import Promotion.
Require Import SimCommon.

Set Implicit Arguments.
Set Nested Proofs Allowed.


Module SimThreadPromotion.
  Import SimCommon.


  (* sim_state *)

  Inductive sim_state_synch (l: Loc.t) (r: Reg.t) (st_src st_tgt: State.t): Prop :=
  | sim_state_synch_intro
      (STMTS: st_tgt.(State.stmts) = promote_stmts l r st_src.(State.stmts))
      (REGS: RegFile.eq_except (RegSet.singleton r) st_src.(State.regs) st_tgt.(State.regs))
  .
  Hint Constructors sim_state_synch.

  Inductive sim_state_fa (l: Loc.t) (r: Reg.t) (st_src st_tgt: State.t): Prop :=
  | sim_state_fa_intro
      lhs addendum ordr ordw stmts_src stmts_tgt
      (STMTS_SRC: st_src.(State.stmts) =
                  (Stmt.instr (Instr.update lhs l (Instr.fetch_add addendum) ordr ordw)) :: stmts_src)
      (STMTS_TGT: st_tgt.(State.stmts) =
                  (Stmt.instr (Instr.assign r (Instr.expr_op2 Op2.add (Value.reg r) addendum))) :: stmts_tgt)
      (STMTS: stmts_tgt = promote_stmts l r stmts_src)
      (REGS: RegFile.eq_except (RegSet.add lhs (RegSet.singleton r)) st_src.(State.regs) st_tgt.(State.regs))
      (LHS: st_tgt.(State.regs) lhs = st_tgt.(State.regs) r)
  .
  Hint Constructors sim_state_fa.

  Inductive sim_state_cas_success1 (l: Loc.t) (r: Reg.t) (st_src st_tgt: State.t): Prop :=
  | sim_state_cas1_intro
      lhs old new ordr ordw stmts_src stmts_tgt
      (STMTS_SRC: st_src.(State.stmts) =
                  (Stmt.instr (Instr.update lhs l (Instr.cas old new) ordr ordw)) :: stmts_src)
      (STMTS_TGT: st_tgt.(State.stmts) =
                  Stmt.instr (Instr.assign lhs (Instr.expr_val (Value.const 1)))
                             :: (Stmt.instr (Instr.assign r new))
                             :: stmts_tgt)
      (STMTS: stmts_tgt = promote_stmts l r stmts_src)
      (REGS: RegFile.eq_except (RegSet.singleton r) st_src.(State.regs) st_tgt.(State.regs))
      (SUCCESS: st_tgt.(State.regs) r = RegFile.eval_value st_tgt.(State.regs) old)
  .
  Hint Constructors sim_state_cas_success1.

  Inductive sim_state_cas_success2 (l: Loc.t) (r: Reg.t) (st_src st_tgt: State.t): Prop :=
  | sim_state_cas2_intro
      lhs old new ordr ordw stmts_src stmts_tgt
      (STMTS_SRC: st_src.(State.stmts) =
                  (Stmt.instr (Instr.update lhs l (Instr.cas old new) ordr ordw)) :: stmts_src)
      (STMTS_TGT: st_tgt.(State.stmts) =
                  (Stmt.instr (Instr.assign r new)) :: stmts_tgt)
      (STMTS: stmts_tgt = promote_stmts l r stmts_src)
      (REGS: RegFile.eq_except (RegSet.add lhs (RegSet.singleton r)) st_src.(State.regs) st_tgt.(State.regs))
      (LHS: st_tgt.(State.regs) r = 1)
      (SUCCESS: st_tgt.(State.regs) r = RegFile.eval_value st_tgt.(State.regs) old)
  .
  Hint Constructors sim_state_cas_success2.

  Inductive sim_state_cas_fail (l: Loc.t) (r: Reg.t) (st_src st_tgt: State.t): Prop :=
  | sim_state_cas_fail_intro
      lhs old new ordr ordw stmts_src stmts_tgt
      (STMTS_SRC: st_src.(State.stmts) =
                  (Stmt.instr (Instr.update lhs l (Instr.cas old new) ordr ordw)) :: stmts_src)
      (STMTS_TGT: st_tgt.(State.stmts) =
                  Stmt.instr (Instr.assign lhs (Instr.expr_val (Value.const 0))) :: stmts_tgt)
      (STMTS: stmts_tgt = promote_stmts l r stmts_src)
      (REGS: RegFile.eq_except (RegSet.singleton r) st_src.(State.regs) st_tgt.(State.regs))
      (FAIL: st_tgt.(State.regs) r <> RegFile.eval_value st_tgt.(State.regs) old)
  .
  Hint Constructors sim_state_cas_fail.

  Definition sim_state (l: Loc.t) (r: Reg.t) (st_src st_tgt: State.t): Prop :=
    sim_state_synch l r st_src st_tgt \/
    sim_state_fa l r st_src st_tgt \/
    sim_state_cas_success1 l r st_src st_tgt \/
    sim_state_cas_success2 l r st_src st_tgt \/
    sim_state_cas_fail l r st_src st_tgt
  .


  (* sim_thread *)

  Definition promises_safe (l: Loc.t) (lc: Local.t): Prop :=
    forall from to val released
      (GET: Memory.get l to lc.(Local.promises) =
            Some (from, Message.full val (Some released))),
      View.le released lc.(Local.tview).(TView.cur).

  Inductive sim_thread (l: Loc.t) (r: Reg.t) (e_src e_tgt: Thread.t lang): Prop :=
  | sim_thread_intro
      (REGFREE: reg_free_stmts r e_src.(Thread.state).(State.stmts))
      (STATE: sim_state l r e_src.(Thread.state) e_tgt.(Thread.state))
      (LOCAL: sim_local l e_src.(Thread.local) e_tgt.(Thread.local))
      (SC: sim_timemap l e_src.(Thread.sc) e_tgt.(Thread.sc))
      (MEMORY: sim_memory l e_src.(Thread.memory) e_tgt.(Thread.memory))
      (FULFILLABLE: fulfillable l e_src.(Thread.local).(Local.tview) e_src.(Thread.memory)
                                  e_src.(Thread.local).(Local.promises))
      (LATEST: exists from released,
          Memory.get l (Memory.max_ts l e_src.(Thread.memory)) e_src.(Thread.memory) =
          Some (from, Message.full (e_tgt.(Thread.state).(State.regs) r) released))
      (PROMISES: forall to, Memory.get l to e_src.(Thread.local).(Local.promises) = None)
      (SAFE: promises_safe l e_src.(Thread.local))
  .
  Hint Constructors sim_thread.

  Inductive sim_thread_reserve (l: Loc.t) (r: Reg.t) (e_src e_tgt: Thread.t lang): Prop :=
  | sim_thread_reserve_intro
      (REGFREE: reg_free_stmts r e_src.(Thread.state).(State.stmts))
      (STATE: sim_state l r e_src.(Thread.state) e_tgt.(Thread.state))
      (LOCAL: sim_local l e_src.(Thread.local) e_tgt.(Thread.local))
      (SC: sim_timemap l e_src.(Thread.sc) e_tgt.(Thread.sc))
      (MEMORY: sim_memory l e_src.(Thread.memory) e_tgt.(Thread.memory))
      (FULFILLABLE: fulfillable l e_src.(Thread.local).(Local.tview) e_src.(Thread.memory)
                                  e_src.(Thread.local).(Local.promises))
      (LATEST: exists from from' released,
          <<MEM: Memory.get l (Memory.max_ts l e_src.(Thread.memory)) e_src.(Thread.memory) =
                 Some (from, Message.reserve)>> /\
          <<PROMISE: Memory.get l (Memory.max_ts l e_src.(Thread.memory)) e_src.(Thread.local).(Local.promises) =
                     Some (from, Message.reserve)>> /\
          <<LATEST: Memory.get l from e_src.(Thread.memory) =
                    Some (from', Message.full (e_tgt.(Thread.state).(State.regs) r) released)>>)
      (PROMISES: forall to (TO: to <> Memory.max_ts l e_src.(Thread.memory)),
          Memory.get l to e_src.(Thread.local).(Local.promises) = None)
      (SAFE: promises_safe l e_src.(Thread.local))
  .
  Hint Constructors sim_thread_reserve.


  Lemma step_sim_thread_promotion_reserve
        l r e_src e_tgt
        (SIM: sim_thread l r e_src e_tgt):
    exists from to e1_src,
      <<STEP: Thread.step false (ThreadEvent.promise l from to Message.reserve Memory.op_kind_add)
                          e_src e1_src>> /\
      <<SIM: sim_thread_reserve l r e1_src e_tgt>>.
  Proof.
    destruct e_src, e_tgt. inv SIM. ss.
    guardH STATE. des.
  Admitted.

  Lemma step_sim_thread_promotion
        l r e_src e_tgt
        (SIM: sim_thread_reserve l r e_src e_tgt):
    exists from to e1_src,
      <<STEP: Thread.step false (ThreadEvent.promise l from to Message.reserve Memory.op_kind_cancel)
                          e_src e1_src>> /\
      <<SIM: sim_thread l r e1_src e_tgt>>.
  Proof.
    destruct e_src, e_tgt. inv SIM. ss.
    guardH STATE. des.
  Admitted.

  Lemma eq_loc_max_ts
        loc mem1 mem2
        (EQLOC: forall to, Memory.get loc to mem1 = Memory.get loc to mem2):
    Memory.max_ts loc mem1 = Memory.max_ts loc mem2.
  Proof.
    unfold Memory.max_ts.
    replace (mem1 loc) with (mem2 loc); ss.
    apply Cell.ext. eauto.
  Qed.

  Lemma sim_thread_promise_step
        l r e1_src
        pf e_tgt e1_tgt e2_tgt
        (SIM1: sim_thread l r e1_src e1_tgt)
        (WF1_SRC: Local.wf e1_src.(Thread.local) e1_src.(Thread.memory))
        (WF1_TGT: Local.wf e1_tgt.(Thread.local) e1_tgt.(Thread.memory))
        (CLOSED1_SRC: Memory.closed e1_src.(Thread.memory))
        (STEP_TGT: Thread.promise_step pf e_tgt e1_tgt e2_tgt):
    exists e_src e2_src,
      <<STEP_SRC: Thread.opt_promise_step e_src e1_src e2_src>> /\
      <<SIM2: sim_thread l r e2_src e2_tgt>>.
  Proof.
    inversion STEP_TGT. subst.
    destruct (Loc.eq_dec loc l).
    { subst. inv LOCAL; ss.
      esplits; [econs 1|]; eauto.
      inv SIM1. ss.
      exploit promise_loc; try exact PROMISE; try apply LOCAL; eauto. i. des.
      econs; ss; eauto.
      econs; ss; eauto; try apply LOCAL.
    }
    exploit promise_step; try exact LOCAL; try apply SIM1;
      try apply WF1_SRC; try apply WF1_TGT; eauto.
    i. des.
    destruct e1_src. ss.
    esplits.
    - econs 2. econs; eauto.
    - inv SIM1. inv STEP_SRC. ss.
      econs; eauto; ss; ii.
      + erewrite <- promise_eq_mem; eauto.
        erewrite <- eq_loc_max_ts; eauto.
        eapply promise_eq_mem; eauto.
      + erewrite <- promise_eq_promises; eauto.
      + erewrite <- promise_eq_promises in GET; eauto.
  Qed.

  Lemma sim_thread_program_step
        l r e1_src
        e_tgt e1_tgt e2_tgt
        (SIM1: sim_thread l r e1_src e1_tgt)
        (WF1_SRC: Local.wf e1_src.(Thread.local) e1_src.(Thread.memory))
        (WF1_TGT: Local.wf e1_tgt.(Thread.local) e1_tgt.(Thread.memory))
        (SC1_SRC: Memory.closed_timemap e1_src.(Thread.sc) e1_src.(Thread.memory))
        (SC1_TGT: Memory.closed_timemap e1_tgt.(Thread.sc) e1_tgt.(Thread.memory))
        (CLOSED1_SRC: Memory.closed e1_src.(Thread.memory))
        (CLOSED1_TGT: Memory.closed e1_tgt.(Thread.memory))
        (STEP_TGT: Thread.program_step e_tgt e1_tgt e2_tgt):
    exists e_src e1_src e2_src,
      <<STEP_SRC: Thread.opt_program_step e_src e1_src e2_src>> /\
      <<EVENT: ThreadEvent.get_machine_event e_src = ThreadEvent.get_machine_event e_tgt>> /\
      <<SIM2: sim_thread l r e2_src e2_tgt>>.
  Proof.
  Admitted.
End SimThreadPromotion.
