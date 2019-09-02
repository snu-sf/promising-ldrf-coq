From PromisingLib Require Import Axioms.

Set Implicit Arguments.

Notation " ~1 p" := (fun x0 => ~ (p x0)) (at level 50, no associativity).
Notation " ~2 p" := (fun x0 x1 => ~ (p x0 x1)) (at level 50, no associativity).
Notation " ~3 p" := (fun x0 x1 x2 => ~ (p x0 x1 x2)) (at level 50, no associativity).
Notation " ~4 p" := (fun x0 x1 x2 x3 => ~ (p x0 x1 x2 x3)) (at level 50, no associativity).

Notation "p /1\ q" := (fun x0 => and (p x0) (q x0)) (at level 50, no associativity).
Notation "p /2\ q" := (fun x0 x1 => and (p x0 x1) (q x0 x1)) (at level 50, no associativity).
Notation "p /3\ q" := (fun x0 x1 x2 => and (p x0 x1 x2) (q x0 x1 x2)) (at level 50, no associativity).
Notation "p /4\ q" := (fun x0 x1 x2 x3 => and (p x0 x1 x2 x3) (q x0 x1 x2 x3)) (at level 50, no associativity).

Notation "p =1= q" := (forall x0, iff (p x0) (q x0)) (at level 50, no associativity).
Notation "p =2= q" := (forall x0 x1, iff (p x0 x1) (q x0 x1)) (at level 50, no associativity).
Notation "p =3= q" := (forall x0 x1 x2, iff (p x0 x1 x2) (q x0 x1 x2)) (at level 50, no associativity).
Notation "p =4= q" := (forall x0 x1 x2 x3, iff (p x0 x1 x2 x3) (q x0 x1 x2 x3)) (at level 50, no associativity).

Notation "p -1 q" := (p /1\ ~1 q) (at level 50).
Notation "p -2 q" := (p /2\ ~2 q) (at level 50).
Notation "p -3 q" := (p /3\ ~3 q) (at level 50).
Notation "p -4 q" := (p /4\ ~4 q) (at level 50).

Definition singleton A (a0: A): A -> Prop := eq a0.
