Require Import Bool.
Require Import RelationClasses.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Language.
From PromisingLib Require Import Loc.

Require Import Event.
Require Import List.

Require Import Debt.

Set Implicit Arguments.

Program Instance option_rel_PreOrder A R `{@PreOrder A R}: PreOrder (option_rel R).
Next Obligation.
Proof.
  ii. destruct x; ss. refl.
Qed.
Next Obligation.
Proof.
  ii. destruct x, y, z; ss. etrans; eauto.
Qed.


Module SeqEvent.
  Variant t: Set :=
  | read
      (loc: Loc.t) (val: Const.t) (ord: Ordering.t)
      (d: diffs) (c: SeqCell.t) (f: option Flags.t)
  | write
      (loc: Loc.t) (val: Const.t) (ord: Ordering.t)
      (d: diffs) (c: SeqCell.t) (m_released: option SeqMemory.t)
  | update
      (loc: Loc.t) (valr: Const.t) (valw: Const.t) (ordr: Ordering.t) (ordw: Ordering.t)
      (d: diffs) (c: SeqCell.t) (f: option Flags.t) (m_released: option SeqMemory.t)
  | fence
      (ordr: Ordering.t) (ordw: Ordering.t)
      (d: diffs) (f: option Flags.t) (m_released: option SeqMemory.t)
  | syscall
      (e: Event.t)
      (d: diffs) (f: Flags.t) (m_released: SeqMemory.t)
  | failure
  .

  Variant le: t -> t -> Prop :=
  | le_read
      loc val ord d c0 c1 f0 f1
      (CELL: SeqCell.le c0 c1)
      (FLAGS: option_rel Flags.le f0 f1)
    :
      le (read loc val ord d c0 f0) (read loc val ord d c1 f1)
  | le_write
      loc val ord d c0 c1 m0 m1
      (CELL: SeqCell.le c0 c1)
      (RELEASED: option_rel SeqMemory.le m0 m1)
    :
      le (write loc val ord d c0 m0) (write loc val ord d c1 m1)
  | le_update
      loc valr valw ordr ordw d c0 c1 f0 f1 m0 m1
      (CELL: SeqCell.le c0 c1)
      (FLAGS: option_rel Flags.le f0 f1)
      (RELEASED: option_rel SeqMemory.le m0 m1)
    :
      le (update loc valr valw ordr ordw d c0 f0 m0) (update loc valr valw ordr ordw d c1 f1 m1)
  | le_fence
      ordr ordw d f0 f1 m0 m1
      (FLAGS: option_rel Flags.le f0 f1)
      (RELEASED: option_rel SeqMemory.le m0 m1)
    :
      le (fence ordr ordw d f0 m0) (fence ordr ordw d f1 m1)
  | le_syscall
      e d f0 f1 m0 m1
      (FLAGS: Flags.le f0 f1)
      (RELEASED: SeqMemory.le m0 m1)
    :
      le (syscall e d f0 m0) (syscall e d f1 m1)
  | le_failure
    :
      le failure failure
  .

  Program Instance le_PreOrder: PreOrder le.
  Next Obligation.
  Proof.
    ii. destruct x; econs; refl.
  Qed.
  Next Obligation.
  Proof.
    ii. inv H; inv H0; econs; etrans; eauto.
  Qed.
End SeqEvent.


Module SeqTrace.
  Variant t: Set :=
  | term (es: list SeqEvent.t) (m: SeqMemory.t)
  | partial (es: list SeqEvent.t) (f: Flags.t)
  | ub (es: list SeqEvent.t)
  .

  Variant le: t -> t -> Prop :=
  | le_term
      es_src es_tgt m_tgt m_src
      (EVENTS: Forall2 SeqEvent.le es_tgt es_src)
      (MEMORY: SeqMemory.le m_tgt m_src)
    :
      le (term es_tgt m_tgt) (term es_src m_src)
  | le_pterm
      es0 es1 es2 m0 m1
      (EVENTS: Forall2 SeqEvent.le es0 es1)
      (FLAGS: Flags.le f0 f1)
    :
      le (pterm es0 f0) (pterm es1 f1)





  Variant

          (f: option Flags.t)




  Definition match_event (e: ProgramEvent.t) (m_tgt m_src: t): Prop :=
    match e with
    | ProgramEvent.silent => True
    | ProgramEvent.read loc _ ord =>
      (SeqCell.le (m_tgt loc) (m_src loc)) /\
      (Ordering.le Ordering.acqrel ord -> le_partial m_tgt m_src)
    | ProgramEvent.write loc _ _ =>
      (SeqCell.le (m_tgt loc) (m_src loc))
    | ProgramEvent.update loc _ _ ordr _ =>
      (SeqCell.le (m_tgt loc) (m_src loc)) /\
      (Ordering.le Ordering.acqrel ordr -> le_partial m_tgt m_src)
    | ProgramEvent.fence ordr ordw =>
      (ordw = Ordering.seqcst -> le m_tgt m_src) /\
      (Ordering.le Ordering.acqrel ordr -> le_partial m_tgt m_src)
    | ProgramEvent.syscall _ =>
      le m_tgt m_src
    | ProgramEvent.failure => True
    end.
