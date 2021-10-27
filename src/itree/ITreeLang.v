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

Require Import RelationClasses.
Require Import List.

From sflib Require Import sflib.

From PromisingLib Require Import Basic.
From PromisingLib Require Import Loc.
From PromisingLib Require Import Language.

Require Import Event.
Require Export ITreeLib.
Require Export Program.

Set Implicit Arguments.


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
  | abort: t void
  | choose: t Const.t
  .

  Variant ord: forall R (i_src i_tgt:t R), Prop :=
  | ord_read
      l o1 o2 (O: Ordering.le o1 o2):
      ord (read l o1) (read l o2)
  | ord_write
      l v o1 o2 (O: Ordering.le o1 o2):
      ord (write l v o1) (write l v o2)
  | ord_update
      l rmw or1 or2 ow1 ow2
      (OR: Ordering.le or1 or2)
      (OW: Ordering.le ow1 ow2):
      ord (update l rmw or1 ow1) (update l rmw or2 ow2)
  | ord_fence
      or1 or2 ow1 ow2
      (OR: Ordering.le or1 or2)
      (OW: Ordering.le ow1 ow2):
      ord (fence or1 ow1) (fence or2 ow2)
  | ord_syscall
      args:
      ord (syscall args) (syscall args)
  | ord_abort:
      ord abort abort
  | ord_choose:
      ord choose choose
  .
End MemE.


Module ILang.
  Variant eval_rmw: forall (rmw:MemE.rmw) (valr:Const.t) (valret: Const.t) (valw: option Const.t), Prop :=
  | eval_rmw_fetch_add
      addendum valr valret valw
      (VALRET: valret = Const.add valr addendum)
      (VALW: valw = Some (Const.add valr addendum)):
      eval_rmw (MemE.fetch_add addendum) valr valret valw
  | eval_rmw_cas_success
      o n valr valret valw
      (CMP: Const.eqb o valr <> Some false)
      (VALRET: valret = Const.one)
      (VALW: valw = Some n):
      eval_rmw (MemE.cas o n) valr valret valw
  | eval_rmw_cas_fail
      o n valr valret valw
      (CMP: Const.eqb o valr <> Some true)
      (VALRET: valret = Const.zero)
      (VALW: valw = None):
      eval_rmw (MemE.cas o n) valr valret valw
  .
  #[export] Hint Constructors eval_rmw.

  Definition is_terminal R (s: itree MemE.t R): Prop :=
    exists r, s = Ret r.

  Inductive step R:
    forall (e:ProgramEvent.t) (s1: itree MemE.t R) (s2: itree MemE.t R), Prop :=
  | step_tau
      (itr: itree MemE.t R)
      itr1 (EQ: itr1 = itr)
    :
      @step R ProgramEvent.silent
            (Tau itr)
            itr1
  | step_choose
      (k: Const.t -> itree MemE.t R) val
      itr1 (EQ: itr1 = k val)
    :
      @step R ProgramEvent.silent
            (Vis (MemE.choose) k)
            itr1
  | step_read
      (k: Const.t -> itree MemE.t R) loc val ord
      itr1 (EQ: itr1 = k val)
    :
      @step R (ProgramEvent.read loc val ord)
            (Vis (MemE.read loc ord) k)
            itr1
  | step_write
      (k: unit -> itree MemE.t R) loc val ord
      itr1 (EQ: itr1 = k tt)
    :
      @step R (ProgramEvent.write loc val ord)
            (Vis (MemE.write loc val ord) k)
            itr1
  | step_update_success
      (k: Const.t -> itree MemE.t R) loc rmw valr valw valret ordr ordw
      (RMW: eval_rmw rmw valr valret (Some valw))
      itr1 (EQ: itr1 = k valret)
    :
      @step R (ProgramEvent.update loc valr valw ordr ordw)
            (Vis (MemE.update loc rmw ordr ordw) k)
            itr1
  | step_update_failure
      (k: Const.t -> itree MemE.t R) loc rmw valr valret ordr ordw
      (RMW: eval_rmw rmw valr valret None)
      itr1 (EQ: itr1 = k valret)
    :
      @step R (ProgramEvent.read loc valr ordr)
            (Vis (MemE.update loc rmw ordr ordw) k)
            itr1
  | step_fence
      (k: unit -> itree MemE.t R) ordr ordw
      itr1 (EQ: itr1 = k tt)
    :
      @step R (ProgramEvent.fence ordr ordw)
            (Vis (MemE.fence ordr ordw) k)
            itr1
  | step_syscall
      (k: Const.t -> itree MemE.t R) valret args
      itr1 (EQ: itr1 = k valret)
    :
      @step R (ProgramEvent.syscall (Event.mk valret args))
            (Vis (MemE.syscall args) k)
            itr1
  | step_abort
      (k: void -> itree MemE.t R)
    :
      @step R (ProgramEvent.failure)
            (Vis (MemE.abort) k)
            ITree.spin
  .
  #[export] Hint Constructors step: core.

  Inductive opt_step R:
    forall (e:ProgramEvent.t) (s1: itree MemE.t R) (s2: itree MemE.t R), Prop :=
  | opt_step_none
      (st: itree MemE.t R):
      opt_step ProgramEvent.silent st st
  | opt_step_some
      e (st1 st2: itree MemE.t R)
      (STEP: step e st1 st2):
      opt_step e st1 st2
  .
End ILang.

Definition lang (R: Type): Language.t ProgramEvent.t :=
  @Language.mk
    _
    (itree MemE.t R)
    (itree MemE.t R)
    id
    (@ILang.is_terminal _)
    (@ILang.step _)
.

From Paco Require Import paco.

Lemma bind_spin E A B (k: ktree E A B):
  ITree.spin >>= k = ITree.spin.
Proof.
  apply bisim_is_eq. revert k. pcofix CIH.
  i. pfold. red.
  change (observe (ITree.spin: itree E B)) with (@TauF E B _ (ITree.spin: itree E B)).
  change (observe (ITree.spin >>= k)) with (@TauF E B _ (ITree.spin >>= k)).
  econs. right. auto.
Qed.

Lemma unfold_spin E R
  :
    (ITree.spin: itree E R) = tau;;ITree.spin.
Proof.
  apply bisim_is_eq. ginit. gstep. red. ss.
  change (observe ITree.spin) with (@TauF E R _ (ITree.spin: itree E R)).
  refl.
Qed.
