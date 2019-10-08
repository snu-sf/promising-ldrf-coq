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

Set Implicit Arguments.


Definition promote_stmt (l: Loc.t) (r: Reg.t) (stmt: Stmt.t): list Stmt.t :=
  match stmt with
  | Stmt.instr (Instr.load lhs rhs _) =>
    if Loc.eq_dec rhs l
    then [Stmt.instr (Instr.assign lhs (Instr.expr_val (Value.reg r)))]
    else [stmt]
  | Stmt.instr (Instr.store lhs rhs _) =>
    if Loc.eq_dec lhs l
    then [Stmt.instr (Instr.assign r rhs)]
    else [stmt]
  | Stmt.instr (Instr.update lhs loc (Instr.fetch_add addendum) _ _) =>
    if Loc.eq_dec loc l
    then [Stmt.instr (Instr.assign lhs (Instr.expr_val (Value.reg r)));
            Stmt.instr (Instr.assign r (Instr.expr_op2 Op2.add (Value.reg r) addendum))]
    else [stmt]
  | Stmt.instr (Instr.update lhs loc (Instr.cas old new) _ _) =>
    if Loc.eq_dec loc l
    then [Stmt.ite
            (Instr.expr_op2 Op2.sub (Value.reg r) old)
            [Stmt.instr (Instr.assign lhs (Instr.expr_val (Value.const 1)));
               Stmt.instr (Instr.assign r new)]
            [Stmt.instr (Instr.assign lhs (Instr.expr_val (Value.const 0)))]
         ]
    else [stmt]
  | _ => [stmt]
  end.

Definition promote_stmts (l: Loc.t) (r: Reg.t) (stmts: list Stmt.t): list Stmt.t :=
  List.fold_left (@List.app _) (List.map (promote_stmt l r) stmts) [].


(* loc_free *)

Definition loc_free_instr (l: Loc.t) (i: Instr.t): Prop :=
  match i with
  | Instr.load _ loc _
  | Instr.store loc _ _
  | Instr.update _ loc _ _ _ => loc <> l
  | _ => true
  end.

Inductive loc_free_stmt (l: Loc.t): forall (stmt: Stmt.t), Prop :=
| loc_free_stmt_instr
    i
    (LOCFREE: loc_free_instr l i):
    loc_free_stmt l (Stmt.instr i)
| loc_free_stmt_ite
    cond stmts1 stmts2
    (LOCFREE1: List.Forall (loc_free_stmt l) stmts1)
    (LOCFREE2: List.Forall (loc_free_stmt l) stmts2):
    loc_free_stmt l (Stmt.ite cond stmts1 stmts2)
| loc_free_stmt_dowhile
    stmts cond
    (LOCFREE: List.Forall (loc_free_stmt l) stmts):
    loc_free_stmt l (Stmt.dowhile stmts cond)
.
Hint Constructors loc_free_stmt.

Definition loc_free_stmts (l: Loc.t) (stmts: list Stmt.t): Prop :=
  List.Forall (loc_free_stmt l) stmts.


(* reg_free *)

Inductive reg_free_stmt (r: Reg.t): forall (stmt: Stmt.t), Prop :=
| reg_free_stmt_instr
    i
    (REGFREE: RegSet.disjoint (RegSet.singleton r) (Instr.regs_of i)):
    reg_free_stmt r (Stmt.instr i)
| reg_free_stmt_ite
    cond stmts1 stmts2
    (REGFREE1: List.Forall (reg_free_stmt r) stmts1)
    (REGFREE2: List.Forall (reg_free_stmt r) stmts2):
    reg_free_stmt r (Stmt.ite cond stmts1 stmts2)
| reg_free_stmt_dowhile
    stmts cond
    (REGFREE: List.Forall (reg_free_stmt r) stmts):
    reg_free_stmt r (Stmt.dowhile stmts cond)
.

Definition reg_free_stmts (r: Reg.t) (stmts: list Stmt.t): Prop :=
  List.Forall (reg_free_stmt r) stmts.


Lemma step_loc_free
      l e st1 st2
      (LOCFREE: loc_free_stmts l st1.(State.stmts))
      (STEP: State.step e st1 st2):
  loc_free_stmts l st2.(State.stmts).
Proof.
  inv STEP; ss.
  - inv LOCFREE. ss.
  - inv LOCFREE. condtac.
    + inv H1. eapply Forall_app; eauto.
    + inv H1. eapply Forall_app; eauto.
  - inv LOCFREE. inv H1.
    eapply Forall_app; eauto.
Qed.

Lemma loc_free_step_is_accessing_loc
      l e st1 st2
      (LOCFREE: loc_free_stmts l st1.(State.stmts))
      (STEP: State.step (ThreadEvent.get_program_event e) st1 st2):
  ~ ThreadEvent.is_accessing_loc l e.
Proof.
  inv STEP; try (by destruct e); ss.
  inv INSTR; destruct e; ss.
  - inv H2. inv LOCFREE. inv H1. ss.
  - inv H2. inv LOCFREE. inv H1. ss.
  - inv H2. inv LOCFREE. inv H1. ss.
  - inv H2. inv LOCFREE. inv H1. ss.
Qed.
