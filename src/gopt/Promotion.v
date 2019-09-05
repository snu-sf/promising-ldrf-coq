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


Definition promote (l: Loc.t) (r: Reg.t) (stmt: Stmt.t): list Stmt.t :=
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
