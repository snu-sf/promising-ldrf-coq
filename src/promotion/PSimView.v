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


Definition sim_timemap (l: Loc.t) (tm_src tm_tgt: TimeMap.t): Prop :=
  tm_tgt = TimeMap.add l Time.bot tm_src.

Inductive sim_view (l: Loc.t) (view_src view_tgt: View.t): Prop :=
| sim_view_intro
    (PLN: sim_timemap l view_src.(View.pln) view_tgt.(View.pln))
    (RLX: sim_timemap l view_src.(View.rlx) view_tgt.(View.rlx))
.
Hint Constructors sim_view.

Inductive sim_opt_view (l: Loc.t): forall (view_src view_tgt: option View.t), Prop :=
| sim_opt_view_some
    view_src view_tgt
    (SIM: sim_view l view_src view_tgt):
    sim_opt_view l (Some view_src) (Some view_tgt)
| sim_opt_view_none:
    sim_opt_view l None None
.
Hint Constructors sim_opt_view.

Inductive sim_tview (l: Loc.t) (tview_src tview_tgt: TView.t): Prop :=
| sim_tview_intro
    (REL: forall loc, sim_view l (tview_src.(TView.rel) loc) (tview_tgt.(TView.rel) loc))
    (CUR: sim_view l tview_src.(TView.cur) tview_tgt.(TView.cur))
    (ACQ: sim_view l tview_src.(TView.acq) tview_tgt.(TView.acq))
.
Hint Constructors sim_tview.
