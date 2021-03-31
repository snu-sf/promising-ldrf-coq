From ITree Require Export ITree Subevent.

From ITree Require Export
     ITree
     ITreeFacts
     Events.MapDefault
     Events.State
     Events.StateFacts
     EqAxiom
.
From ExtLib Require Export
     (* Data.String *)
     (* Structures.Monad *)
     (* Structures.Traversable *)
     (* Structures.Foldable *)
     (* Structures.Reducible *)
     (* OptionMonad *)
     Functor FunctorLaws
     Structures.Maps
     (* Data.List *)
.

Export SumNotations.
Export ITreeNotations.
Export Monads.
Export MonadNotation.
Export FunctorNotation.
Export CatNotations.
Open Scope cat_scope.
Open Scope monad_scope.
Open Scope itree_scope.

Set Implicit Arguments.

Require Import RelationClasses.
Require Import List.

From sflib Require Import sflib.

From PromisingLib Require Import Basic.
From PromisingLib Require Import Loc.
From PromisingLib Require Import Language.

Require Import Event.


Module MemE.
  Variant rmw :=
  | fetch_add (addendum:Const.t)
  | cas (old new:Const.t)
  .

  Variant t: Type -> Type :=
  | read (loc: Loc.t) (ord: Ordering.t): t Const.t 
  | write (loc: Loc.t) (val: Const.t) (ord: Ordering.t): t unit 
  | update (loc: Loc.t) (rmw:rmw) (ordr ordw: Ordering.t): t Const.t
  | fence (ordr ordw: Ordering.t): t unit
  | syscall (args: list Const.t): t Const.t
  | abort: t unit
  .
End MemE.

Set Implicit Arguments.



Module State.
  Definition t := itree MemE.t Const.t.

  Definition eval_rmw (rmw:MemE.rmw) (val:Const.t): Const.t * option Const.t :=
    match rmw with
    | MemE.fetch_add addendum =>
      (Const.add val addendum, Some (Const.add val addendum))
    | MemE.cas o n =>
      if Const.eq_dec o val
      then (1, Some n)
      else (0, None)
    end.

  Definition is_terminal R (s: itree MemE.t R): Prop :=
    exists r, s = Ret r.

  Inductive step: 
    forall R (e:ProgramEvent.t) (s1: itree MemE.t R) (s2: itree MemE.t R), Prop :=
  | step_tau
      R (itr: itree MemE.t R):
      @step R ProgramEvent.silent
                  (Tau itr)
                  itr
  | step_read
      R (k: Const.t -> itree MemE.t R) loc val ord k: 
      @step R (ProgramEvent.read loc val ord)
                  (Vis (MemE.read loc ord) k)
                  (k val)
  | step_write
      R (k: unit -> itree MemE.t R) loc val ord k: 
      @step R (ProgramEvent.write loc val ord)
                  (Vis (MemE.write loc val ord) k)
                  (k tt)
  | step_update_success
      R (k: Const.t -> itree MemE.t R) loc rmw valr valw valret ordr ordw
      (RMW: eval_rmw rmw valr = (valret, Some valw))
    : 
      @step R (ProgramEvent.update loc valr valw ordr ordw)
                  (Vis (MemE.update loc rmw ordr ordw) k)
                  (k valret)
  | step_update_failure
      R (k: Const.t -> itree MemE.t R) loc rmw valr valret ordr ordw
      (RMW: eval_rmw rmw valr = (valret, None))
    : 
      @step R (ProgramEvent.read loc valr ordr)
                  (Vis (MemE.update loc rmw ordr ordw) k)
                  (k valret)
  | step_fence
      R (k: unit -> itree MemE.t R) ordr ordw
    : 
      @step R (ProgramEvent.fence ordr ordw)
                  (Vis (MemE.fence ordr ordw) k)
                  (k tt)
  | step_syscall
      R (k: Const.t -> itree MemE.t R) valret args
    : 
      @step R (ProgramEvent.syscall (Event.mk valret args))
                  (Vis (MemE.syscall args) k)
                  (k valret)
  | step_abort
      R (k: unit -> itree MemE.t R)
    : 
      @step R (ProgramEvent.failure)
                  (Vis (MemE.abort) k)
                  (k tt)
  .
End State.

Definition lang: Language.t ProgramEvent.t :=
  @Language.mk
    _
    State.t
    State.t
    id
    (@State.is_terminal _)
    (@State.step _)
.
