From sflib Require Import sflib.


Lemma Forall2_refl
      A (f: A -> A -> Prop) (a: list A)
      (REFL: forall x, f x x):
  List.Forall2 f a a.
Proof.
  induction a; eauto.
Qed.

Lemma Forall2_symm
      A (f: A -> A -> Prop) (a b: list A)
      (SYMM: forall x y, f x y -> f y x)
      (FORALL: List.Forall2 f a b):
  List.Forall2 f b a.
Proof.
  induction FORALL; eauto.
Qed.

Lemma Forall2_trans
      A (f: A -> A -> Prop) (a b c: list A)
      (TRANS: forall x y z, f x y -> f y z -> f x z)
      (FORALL1: List.Forall2 f a b)
      (FORALL2: List.Forall2 f b c):
  List.Forall2 f a c.
Proof.
  revert c FORALL2.
  induction FORALL1; eauto. i.
  inv FORALL2. econs; eauto.
Qed.
