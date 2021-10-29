Require Import List.
Require Import PeanoNat.
Require Import Orders.
Require Import MSetList.

From sflib Require Import sflib.

From PromisingLib Require Import DataStructure.
From PromisingLib Require Import Basic.
From PromisingLib Require Import Loc.
From PromisingLib Require Import Language.

Set Implicit Arguments.


Module Const.
  Definition num_t: Type := nat.

  Variant t :=
  | num (n: num_t)
  | undef
  .

  Definition of_nat (n: nat): t := num n.
  Definition zero: t := num 0.
  Definition one: t := num 1.

  Definition eqb (a b: t): option bool :=
    match a, b with
    | num a, num b => Some (a =? b)
    | _, _ => None
    end.

  Definition add (a b: t): t :=
    match a, b with
    | num a, num b => num (a + b)
    | _, _ => undef
    end.

  Definition le (lhs rhs: t): bool :=
    match lhs, rhs with
    | num x, num y => x =? y
    | _, undef => true
    | _, _ => false
    end.

  Lemma eqb_refl a: eqb a a <> Some false.
  Proof.
    destruct a; ss. rewrite Nat.eqb_refl. ss.
  Qed.

  Lemma add_0_l a: add (num 0) a = a.
  Proof.
    destruct a; ss.
  Qed.

  Lemma add_0_r a: add a (num 0) = a.
  Proof.
    destruct a; ss.
    rewrite Nat.add_0_r. ss.
  Qed.

  Lemma add_assoc a b c:
    add a (add b c) = add (add a b) c.
  Proof.
    destruct a, b, c; ss.
    rewrite Nat.add_assoc. ss.
  Qed.

  Lemma antisym
        a b
        (AB: le a b)
        (BA: le b a):
    a = b.
  Proof.
    destruct a, b; ss.
    inv AB. rewrite Nat.eqb_eq in H0. subst. ss.
  Qed.

  Lemma le_num_inv
        c n
        (LE: le c (num n)):
    c = num n.
  Proof.
    destruct c; ss.
    inv LE. rewrite Nat.eqb_eq in H0. subst. ss.
  Qed.

  Lemma undef_le_inv
        c
        (LE: le undef c):
    c = undef.
  Proof.
    destruct c; ss.
  Qed.

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation.
    ii. destruct x; ss. rewrite Nat.eqb_refl. ss.
  Qed.
  Next Obligation.
    ii. destruct x, y, z; ss. inv H. inv H0.
    rewrite Nat.eqb_eq in H1, H2. subst.
    rewrite Nat.eqb_refl. ss.
  Qed.
End Const.
Coercion Const.num: Const.num_t >-> Const.t.
Coercion Const.of_nat: nat >-> Const.t.


Module Ordering.
  (* NOTE: we curently do not support the nonatomics (#61).  Nonatomic
     accesses differ from plain accesses in that nonatomic accesses may
     corrupt data in the presence of a race.

     Even in Java, a data race may result in out-of-thin-air integral
     values.  But even with data races, it is impossible to forge an
     out-of-thin-air reference values.  See the link for more details:
     https://docs.oracle.com/javase/specs/jls/se7/html/jls-17.html#jls-17.7

     Hence, our compilation scheme for Java normal accesses is as
     follows.
     - Normal accesses to pointers are compiled to plain accesses.
     - Normal accesses to numbers are compiled to nonatomic accesses.
   *)
  Inductive t :=
  | na
  | plain
  | relaxed
  | strong_relaxed
  | acqrel
  | seqcst
  .

  Definition le (lhs rhs:t): bool :=
    match lhs, rhs with
    | na, _ => true
    | _, na => false

    | plain, _ => true
    | _, plain => false

    | relaxed, _ => true
    | _, relaxed => false

    | strong_relaxed, _ => true
    | _, strong_relaxed => false

    | acqrel, _ => true
    | _, acqrel => false

    | seqcst, seqcst => true
    end.
  Global Opaque le.

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation.
    ii. destruct x; auto.
  Qed.
  Next Obligation.
    ii. destruct x, y, z; auto.
  Qed.
  Hint Resolve le_PreOrder_obligation_2.

  Definition join (lhs rhs:t): t :=
    match lhs, rhs with
    | na, _ => rhs
    | _, na => lhs

    | plain, _ => rhs
    | _, plain => lhs

    | relaxed, _ => rhs
    | _, relaxed => lhs

    | strong_relaxed, _ => rhs
    | _, strong_relaxed => lhs

    | acqrel, _ => rhs
    | _, acqrel => lhs

    | seqcst, _ => rhs
    end.

  Lemma join_comm lhs rhs: join lhs rhs = join rhs lhs.
  Proof. destruct lhs, rhs; ss. Qed.

  Lemma join_assoc a b c: join (join a b) c = join a (join b c).
  Proof. destruct a, b, c; ss. Qed.

  Lemma join_l lhs rhs:
    le lhs (join lhs rhs).
  Proof. destruct lhs, rhs; ss. Qed.

  Lemma join_r lhs rhs:
    le rhs (join lhs rhs).
  Proof. destruct lhs, rhs; ss. Qed.

  Lemma join_spec lhs rhs o
        (LHS: le lhs o)
        (RHS: le rhs o):
    le (join lhs rhs) o.
  Proof. destruct lhs, rhs; ss. Qed.

  Lemma join_cases lhs rhs:
    join lhs rhs = lhs \/ join lhs rhs = rhs.
  Proof. destruct lhs, rhs; auto. Qed.
End Ordering.


(* NOTE (syscall): In fact, syscalls may change the memory, on the
 * contrary to what is currently defined.
 *)
(* NOTE (syscall): we disallow syscalls in the validation of the
 * consistency check, as syscall's results are not predictable.
 *)
Module Event.
  Structure t := mk {
    output: Const.t;
    inputs: list Const.t;
  }.

  Definition le (e0 e1: t): Prop :=
    e0.(output) = e1.(output) /\ Forall2 Const.le e0.(inputs) e1.(inputs).

  (* TODO: PromisingLib *)
  Global Program Instance PreOrder_Forall2 A R `{PreOrder A R}: PreOrder (Forall2 R).
  Next Obligation.
  Proof.
    ii. induction x; ss. econs; ss. refl.
  Qed.
  Next Obligation.
  Proof.
    intros x. induction x; ii.
    { inv H0; inv H1. econs. }
    { inv H0; inv H1. econs; eauto. etrans; eauto. }
  Qed.

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation.
    ii. red. splits; ss. refl.
  Qed.
  Next Obligation.
    ii. unfold le in *. des. splits; ss.
    { etrans; eauto. }
    { etrans; eauto. }
  Qed.
End Event.


Module MachineEvent.
  Inductive t :=
  | silent
  | syscall (e: Event.t)
  | failure
  .
End MachineEvent.


Module ProgramEvent.
  Inductive t :=
  | silent
  | read (loc:Loc.t) (val:Const.t) (ord:Ordering.t)
  | write (loc:Loc.t) (val:Const.t) (ord:Ordering.t)
  | update (loc:Loc.t) (valr valw:Const.t) (ordr ordw:Ordering.t)
  | fence (ordr ordw:Ordering.t)
  | syscall (e:Event.t)
  | failure
  .

  Definition is_reading (e:t): option (Loc.t * Const.t * Ordering.t) :=
    match e with
    | read loc val ord => Some (loc, val, ord)
    | update loc valr _ ordr _ => Some (loc, valr, ordr)
    | _ => None
    end.

  Definition is_writing (e:t): option (Loc.t * Const.t * Ordering.t) :=
    match e with
    | write loc val ord => Some (loc, val, ord)
    | update loc _ valw _ ordw => Some (loc, valw, ordw)
    | _ => None
    end.

  Definition is_updating (e:t): option (Loc.t * Const.t * Ordering.t) :=
    match e with
    | update loc valr _ ordr _ => Some (loc, valr, ordr)
    | _ => None
    end.

  Inductive ord: forall (e1 e2:t), Prop :=
  | ord_silent:
      ord silent silent
  | ord_read
      l v o1 o2
      (O: Ordering.le o1 o2):
      ord (read l v o1) (read l v o2)
  | ord_write
      l v o1 o2
      (O: Ordering.le o1 o2):
      ord (write l v o1) (write l v o2)
  | ord_update
      l vr vw or1 or2 ow1 ow2
      (OR: Ordering.le or1 or2)
      (OW: Ordering.le ow1 ow2):
      ord (update l vr vw or1 ow1) (update l vr vw or2 ow2)
  | ord_fence
      or1 or2 ow1 ow2
      (OR: Ordering.le or1 or2)
      (OW: Ordering.le ow1 ow2):
      ord (fence or1 ow1) (fence or2 ow2)
  | ord_syscall
      e:
      ord (syscall e) (syscall e)
  | ord_failure:
      ord failure failure
  .

  Definition le (e0 e1: t): Prop :=
    match e0, e1 with
    | write loc0 val0 ord0, write loc1 val1 ord1 =>
      loc0 = loc1 /\ Const.le val0 val1 /\ ord0 = ord1
    | update loc0 valr0 valw0 ordr0 ordw0, update loc1 valr1 valw1 ordr1 ordw1 =>
      loc0 = loc1 /\ valr0 = valr1 /\ Const.le valw0 valw1 /\ ordr0 = ordr1 /\ ordw0 = ordw1
    | syscall e0, syscall e1 => Event.le e0 e1
    | _, _ => e0 = e1
    end.

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation.
    ii. destruct x; ss; splits; try refl.
  Qed.
  Next Obligation.
    ii. destruct x, y, z; ss; des; subst; splits; etrans; eauto.
  Qed.
End ProgramEvent.


Definition language: Type := Language.t ProgramEvent.t.
