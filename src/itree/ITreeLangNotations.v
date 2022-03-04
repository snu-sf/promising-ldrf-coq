From ITree Require Export ITree Subevent.

From ITree Require Export
     ITree
     ITreeFacts
     Events.MapDefault
     Events.State
     Events.StateFacts
     EqAxiom
.

Export SumNotations.
Export ITreeNotations.
Export Monads.
Export MonadNotation.
Export CatNotations.
Open Scope cat_scope.
Open Scope monad_scope.
Open Scope itree_scope.

Require Import String.

From sflib Require Import sflib.

From PromisingLib Require Import Basic.

From PromisingLib Require Import Event.
Require Export ITreeLib.

Require Import ITreeLang.

Set Implicit Arguments.

(* ========================================================================== *)
(** ** Notations *)

Module ITreeLangNotations.

  Declare Scope expr_scope.
  Bind Scope expr_scope with Inst.expr.

  Notation "! a" :=
    (Inst.expr_op1 Op1.not a) (at level 30) : expr_scope.

  Notation "a ? b" :=
    (Inst.expr_op2 Op2.eq a b) (at level 30) : expr_scope.

  Infix "+" := (Inst.expr_op2 Op2.add) : expr_scope.
  Infix "-" := (Inst.expr_op2 Op2.sub) : expr_scope.
  Infix "*" := (Inst.expr_op2 Op2.mul) : expr_scope.


  Declare Scope inst_scope.
  Bind Scope inst_scope with Inst.t.

  Notation "'skip#'" :=
    (Inst.skip) (at level 100): inst_scope.

  Notation "x '=#' e" :=
    (Inst.assign x e) (at level 60, e at level 50): inst_scope.

  Notation "'return#' e" :=
    (Inst.assign ret_reg e) (at level 60, e at level 50): inst_scope.

  Notation "x '=#*' l o" :=
    (Inst.load x l o) (at level 60, l at level 9): inst_scope.

  Notation "l '*=#' v o" :=
    (Inst.store l v o) (at level 60, v at level 9): inst_scope.

  Notation "x '=#faa' l c or ow" :=
    (Inst.update x l (MemE.fetch_add c) or ow)
      (at level 60, l at level 9, or at level 9): inst_scope.

  Notation "x '=#cas' l c1 c2 or ow" :=
    (Inst.update x l (MemE.cas c1 c2) or ow)
      (at level 60, l at level 9, or at level 9): inst_scope.

  Notation "'fence#' or ow" :=
    (Inst.fence or ow) (at level 60): inst_scope.

  Notation "x =@ args" :=
    (Inst.syscall x args) (at level 60): inst_scope.

  Notation "'abort#'" :=
    (Inst.abort) (at level 60): inst_scope.


  Declare Scope stmt_scope.
  Bind Scope stmt_scope with stmt.

  Notation "'if#' i 'then#' t 'else#' e 'fi#'" :=
    (ite i t e)
      (at level 100,
       right associativity,
       format
         "'[v ' 'if#'  i '/' '[' 'then#'  t  ']' '/' '[' 'else#'  e ']' '/' 'fi#' ']'").

  Notation "'while#' c 'do#' b 'end#'" :=
    (while c b)
      (at level 100,
       right associativity,
       format
         "'[v ' 'while#' c 'do#' '/' '[' b ']' '/' 'end#' ']'").


  Declare Scope block_scope.
  Bind Scope block_scope with block.

  Notation "{ }" := nil (format "{ }") : block_scope.
  Notation "{ x ; }" := (cons x nil) : block_scope.
  Notation "{ x ; y ; .. ; z }" := (cons x (cons y .. (cons z nil) ..)) : block_scope. 

End ITreeLangNotations.

(* ========================================================================== *)
(** ** Example *)
Section Example.

  Import ITreeLangNotations.

  Local Open Scope expr_scope.
  Local Open Scope inst_scope.
  Local Open Scope stmt_scope.
  Local Open Scope block_scope.

  Require Import BinNums.

  Let n : Ident.t := xH.
  Let out : Ident.t := xO xH.

  Definition factorial : block :=
    { n =# (10: Const.t);
      out =# (1: Const.t);
      while# (! (n ? (0: Const.t))) do#
      { if# (! (n ? (1: Const.t)))
        then#
        { out =# n * out;
          n =# n - (1: Const.t) }
        else#
        { n =# (0: Const.t); }
        fi#;
      }
      end#;
      skip#;
      return# out
    }
  .

End Example.
