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

Set Implicit Arguments.


Definition sim_timemap (l: Loc.t) (tm_src tm_tgt: TimeMap.t): Prop :=
  tm_tgt = TimeMap.add l Time.bot tm_src.

Inductive sim_view (l: Loc.t) (view_src view_tgt: View.t): Prop :=
| sim_view_intro
    (PLN: sim_timemap l view_src.(View.pln) view_tgt.(View.pln))
    (RLX: sim_timemap l view_src.(View.rlx) view_tgt.(View.rlx))
.
Hint Constructors sim_view.

Inductive sim_opt_view (l: Loc.t): forall (view_src view_tgt: option View.t), Prop :=
| sim_opt_view_some
    view_src view_tgt
    (SIM: sim_view l view_src view_tgt):
    sim_opt_view l (Some view_src) (Some view_tgt)
| sim_opt_view_none:
    sim_opt_view l None None
.
Hint Constructors sim_opt_view.

Inductive sim_tview (l: Loc.t) (tview_src tview_tgt: TView.t): Prop :=
| sim_tview_intro
    (REL: forall loc, sim_view l (tview_src.(TView.rel) loc) (tview_tgt.(TView.rel) loc))
    (CUR: sim_view l tview_src.(TView.cur) tview_tgt.(TView.cur))
    (ACQ: sim_view l tview_src.(TView.acq) tview_tgt.(TView.acq))
.
Hint Constructors sim_tview.


Inductive sim_message (l: Loc.t): forall (msg_src msg_tgt: Message.t), Prop :=
| sim_message_full
    val released_src released_tgt
    (RELEASED: sim_opt_view l released_src released_tgt):
    sim_message l (Message.full val released_src) (Message.full val released_tgt)
| sim_message_reserve:
    sim_message l Message.reserve Message.reserve
.
Hint Constructors sim_message.

Inductive sim_memory (l: Loc.t) (mem_src mem_tgt: Memory.t): Prop :=
| sim_memory_intro
    (SOUND: forall loc from to msg_src
              (LOC: loc <> l)
              (GET_SRC: Memory.get loc to mem_src = Some (from, msg_src)),
        exists msg_tgt,
          <<GET_TGT: Memory.get loc to mem_tgt = Some (from, msg_tgt)>> /\
          <<MSG: sim_message l msg_src msg_tgt>>)
    (COMPLETE: forall loc from to msg_tgt
                 (LOC: loc <> l)
                 (GET_TGT: Memory.get loc to mem_tgt = Some (from, msg_tgt)),
        exists msg_src,
          <<GET_SRC: Memory.get loc to mem_src = Some (from, msg_src)>> /\
          <<MSG: sim_message l msg_src msg_tgt>>)
.
Hint Constructors sim_memory.

Inductive sim_local (l: Loc.t) (lc_src lc_tgt: Local.t): Prop :=
| sim_local_intro
    (TVIEW: sim_tview l lc_src.(Local.tview) lc_tgt.(Local.tview))
    (PROMISES1: sim_memory l lc_src.(Local.promises) lc_tgt.(Local.promises))
    (PROMISES2: lc_tgt.(Local.promises) l = Cell.bot)
.
Hint Constructors sim_local.

Inductive sim_thread (l: Loc.t) (e_src e_tgt: Thread.t lang): Prop :=
| sim_thread_intro
    (LOCFREE: loc_free_stmts l e_src.(Thread.state).(State.stmts))
    (STATE: e_src.(Thread.state) = e_tgt.(Thread.state))
    (LOCAL: sim_local l e_src.(Thread.local) e_tgt.(Thread.local))
    (SC: sim_timemap l e_src.(Thread.sc) e_tgt.(Thread.sc))
    (MEMORY: sim_memory l e_src.(Thread.memory) e_tgt.(Thread.memory))
.
Hint Constructors sim_thread.

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
    (LATEST: Memory.latest_val l e_src.(Thread.memory) (e_tgt.(Thread.state).(State.regs) r))
.
Hint Constructors sim_thread_promotion.
