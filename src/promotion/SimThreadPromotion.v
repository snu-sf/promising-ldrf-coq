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


Inductive sim_state_promotion (l: Loc.t) (r: Reg.t) (st_src st_tgt: State.t): Prop :=
| sim_state_promotion_intro
    (STMTS: st_tgt.(State.stmts) = promote_stmts l r st_src.(State.stmts))
    (REGS: RegFile.eq_except (RegSet.singleton r) st_src.(State.regs) st_tgt.(State.regs))
.
Hint Constructors sim_state_promotion.

Inductive sim_state_fa (l: Loc.t) (r: Reg.t) (st_src st_tgt: State.t): Prop :=
| sim_state_fa_intro
    lhs addendum ordr ordw stmts_src stmts_tgt
    (STMTS_SRC: st_src.(State.stmts) =
                (Stmt.instr (Instr.update lhs l (Instr.fetch_add addendum) ordr ordw)) :: stmts_src)
    (STMTS_TGT: st_tgt.(State.stmts) =
                (Stmt.instr (Instr.assign r (Instr.expr_op2 Op2.add (Value.reg r) addendum))) :: stmts_tgt)
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
    (REGS: RegFile.eq_except (RegSet.add lhs (RegSet.singleton r)) st_src.(State.regs) st_tgt.(State.regs))
    (LHS: st_tgt.(State.regs) r = 1)
    (SUCCESS: st_tgt.(State.regs) r = RegFile.eval_value st_tgt.(State.regs) old)
.
Hint Constructors sim_state_cas_success2.

Inductive sim_state_cas_fail (l: Loc.t) (r: Reg.t) (st_src st_tgt: State.t): Prop :=
| sim_state_cas_fail_intro
    lhs old new ordr ordw stmts_src stmts_tgt
    (REGS: RegFile.eq_except (RegSet.singleton r) st_src.(State.regs) st_tgt.(State.regs))
    (STMTS_SRC: st_src.(State.stmts) =
                (Stmt.instr (Instr.update lhs l (Instr.cas old new) ordr ordw)) :: stmts_src)
    (STMTS_TGT: st_tgt.(State.stmts) =
                Stmt.instr (Instr.assign lhs (Instr.expr_val (Value.const 0))) :: stmts_tgt)
    (FAIL: st_tgt.(State.regs) r <> RegFile.eval_value st_tgt.(State.regs) old)
.
Hint Constructors sim_state_cas_fail.

Inductive sim_thread_promotion (l: Loc.t) (r: Reg.t) (e_src e_tgt: Thread.t lang): Prop :=
| sim_thread_promotion_intro
    (REGFREE: reg_free_stmts r e_src.(Thread.state).(State.stmts))
    (STMTS: sim_state_promotion l r e_src.(Thread.state) e_tgt.(Thread.state) \/
            sim_state_fa l r e_src.(Thread.state) e_tgt.(Thread.state) \/
            sim_state_cas_success1 l r e_src.(Thread.state) e_tgt.(Thread.state) \/
            sim_state_cas_success2 l r e_src.(Thread.state) e_tgt.(Thread.state) \/
            sim_state_cas_fail l r e_src.(Thread.state) e_tgt.(Thread.state))
    (LOCAL: sim_local l e_src.(Thread.local) e_tgt.(Thread.local))
    (SC: sim_timemap l e_src.(Thread.sc) e_tgt.(Thread.sc))
    (MEMORY: sim_memory l e_src.(Thread.memory) e_tgt.(Thread.memory))
    (LATEST: exists from released,
        Memory.get l (Memory.max_ts l e_src.(Thread.memory)) e_src.(Thread.memory) = 
        Some (from, Message.full (e_tgt.(Thread.state).(State.regs) r) released))
.
Hint Constructors sim_thread_promotion.

Inductive sim_thread_promotion_reserve (l: Loc.t) (r: Reg.t) (e_src e_tgt: Thread.t lang): Prop :=
| sim_thread_promotion_reserve_intro
    (REGFREE: reg_free_stmts r e_src.(Thread.state).(State.stmts))
    (STMTS: sim_state_promotion l r e_src.(Thread.state) e_tgt.(Thread.state) \/
            sim_state_fa l r e_src.(Thread.state) e_tgt.(Thread.state) \/
            sim_state_cas_success1 l r e_src.(Thread.state) e_tgt.(Thread.state) \/
            sim_state_cas_success2 l r e_src.(Thread.state) e_tgt.(Thread.state) \/
            sim_state_cas_fail l r e_src.(Thread.state) e_tgt.(Thread.state))
    (LOCAL: sim_local l e_src.(Thread.local) e_tgt.(Thread.local))
    (SC: sim_timemap l e_src.(Thread.sc) e_tgt.(Thread.sc))
    (MEMORY: sim_memory l e_src.(Thread.memory) e_tgt.(Thread.memory))
    (LATEST: Memory.latest_val l e_src.(Thread.memory) (e_tgt.(Thread.state).(State.regs) r))
    (RESERVE: exists from,
        Memory.get l (Memory.max_ts l e_src.(Thread.memory)) e_src.(Thread.memory) = 
        Some (from, Message.reserve))
.
Hint Constructors sim_thread_promotion_reserve.
