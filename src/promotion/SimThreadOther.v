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

Require Import Promotion.
Require Import SimCommon.

Set Implicit Arguments.


Inductive sim_thread_other (l: Loc.t) (e_src e_tgt: Thread.t lang): Prop :=
| sim_thread_other_intro
    (LOCFREE: loc_free_stmts l e_src.(Thread.state).(State.stmts))
    (STATE: e_src.(Thread.state) = e_tgt.(Thread.state))
    (LOCAL: sim_local l e_src.(Thread.local) e_tgt.(Thread.local))
    (SC: sim_timemap l e_src.(Thread.sc) e_tgt.(Thread.sc))
    (MEMORY: sim_memory l e_src.(Thread.memory) e_tgt.(Thread.memory))
    (PROMISES: forall to, Memory.get l to e_src.(Thread.local).(Local.promises) = None)
    (RELEASED: forall loc from to val released
                 (GETP: Memory.get loc to e_src.(Thread.local).(Local.promises) =
                        Some (from, Message.full val (Some released))),
        released_eq_tview_loc l loc released e_src.(Thread.local).(Local.tview))
.
Hint Constructors sim_thread_other.
