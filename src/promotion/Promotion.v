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


Definition loc_free_instr (l: Loc.t) (i: Instr.t): bool :=
  match i with
  | Instr.load _ loc _
  | Instr.store loc _ _
  | Instr.update _ loc _ _ _ =>
    if Loc.eq_dec loc l then false else true
  | _ => true
  end.

Fixpoint loc_free_stmt (l: Loc.t) (stmt: Stmt.t): bool :=
  match stmt with
  | Stmt.instr i => loc_free_instr l i
  | Stmt.ite cond stmts1 stmts2 =>
    andb
      (List.fold_left andb (List.map (loc_free_stmt l) stmts1) true)
      (List.fold_left andb (List.map (loc_free_stmt l) stmts2) true)
  | Stmt.dowhile stmts cond =>
    List.fold_left andb (List.map (loc_free_stmt l) stmts) true
  end.

Definition loc_free_stmts (l: Loc.t) (stmts: list Stmt.t): bool :=
  List.fold_left andb (List.map (loc_free_stmt l) stmts) true.
