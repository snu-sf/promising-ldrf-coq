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

Set Implicit Arguments.


Definition sim_timemap (l: Loc.t) (tm_src tm_tgt: TimeMap.t): Prop :=
  forall loc (LOC: loc <> l), tm_src loc = tm_tgt loc.

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


Inductive sim_message (l: Loc.t): forall (msg_src msg_tgt: Message.t), Prop :=
| sim_message_full
    val released_src released_tgt
    (RELEASED: sim_opt_view l released_src released_tgt):
    sim_message l (Message.full val released_src) (Message.full val released_tgt)
| sim_message_reserve:
    sim_message l Message.reserve Message.reserve
.
Hint Constructors sim_message.

Inductive sim_memory (l: Loc.t) (mem_src mem_tgt: Memory.t): Prop :=
| sim_memory_intro
    (SOUND: forall loc from to msg_src
              (LOC: loc <> l)
              (GET_SRC: Memory.get loc to mem_src = Some (from, msg_src)),
        exists msg_tgt,
          <<GET_TGT: Memory.get loc to mem_tgt = Some (from, msg_tgt)>> /\
          <<MSG: sim_message l msg_src msg_tgt>>)
    (COMPLETE: forall loc from to msg_tgt
                 (LOC: loc <> l)
                 (GET_TGT: Memory.get loc to mem_tgt = Some (from, msg_tgt)),
        exists msg_src,
          <<GET_SRC: Memory.get loc to mem_src = Some (from, msg_src)>> /\
          <<MSG: sim_message l msg_src msg_tgt>>)
.
Hint Constructors sim_memory.

Inductive sim_local (l: Loc.t) (lc_src lc_tgt: Local.t): Prop :=
| sim_local_intro
    (TVIEW: sim_tview l lc_src.(Local.tview) lc_tgt.(Local.tview))
    (PROMISES1: sim_memory l lc_src.(Local.promises) lc_tgt.(Local.promises))
    (PROMISES2: lc_tgt.(Local.promises) l = Cell.bot)
.
Hint Constructors sim_local.

Definition released_eq_tview_loc (l loc: Loc.t) (released: View.t) (tview: TView.t): Prop :=
  <<PLN: released.(View.pln) l = (tview.(TView.rel) loc).(View.pln) l>> /\
  <<RLX: released.(View.rlx) l = (tview.(TView.rel) loc).(View.rlx) l>>.
