Require Import Omega.
Require Import Bool.
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

Require Import Trace.

Set Implicit Arguments.


Module RASimThread.
  Section RASimThread.
    Variable lang: language.
    Variable L: Loc.t -> bool.

    (* normal *)

    Definition normal_view (view: View.t): Prop :=
      forall loc (LOC: L loc), view.(View.pln) loc = view.(View.pln) loc.

    Inductive normal_tview (tview:TView.t): Prop :=
    | normal_tview_intro
        (REL: forall loc, normal_view (tview.(TView.rel) loc))
        (CUR: normal_view tview.(TView.cur))
        (ACQ: normal_view tview.(TView.acq))
    .

    Definition normal_thread (e: Thread.t lang): Prop :=
      normal_tview e.(Thread.local).(Local.tview).


    (* stable *)

    Definition stable_view (mem: Memory.t) (view: View.t): Prop :=
      forall loc from val released
        (LOC: L loc)
        (GET: Memory.get loc (view.(View.rlx) loc) mem = Some (from, Message.concrete val released)),
        View.opt_le released (Some view).

    Inductive stable_tview (mem: Memory.t) (tview: TView.t): Prop :=
    | stable_tview_intro
        (REL: forall loc, stable_view mem (tview.(TView.rel) loc))
        (CUR: stable_view mem tview.(TView.cur))
        (ACQ: stable_view mem tview.(TView.acq))
    .

    Definition stable_memory (mem: Memory.t): Prop :=
      forall loc from to val released
        (GET: Memory.get loc to mem = Some (from, Message.concrete val (Some released))),
        stable_view mem released.

    Inductive stable_thread (e: Thread.t lang): Prop :=
    | stable_thread_intro
        (TVIEW: stable_tview e.(Thread.memory) e.(Thread.local).(Local.tview))
        (MEMORY: stable_memory e.(Thread.memory))
    .


    (* sim_thread *)

    Definition reserve_only (promises: Memory.t): Prop :=
      forall loc from to val released
        (LOC: L loc)
        (PROMISE: Memory.get loc to promises = Some (from, Message.concrete val released)),
        False.

    Inductive sim_message (loc: Loc.t): forall (msg_src msg_tgt: Message.t), Prop :=
    | sim_message_concrete
        val released_src released_tgt
        (RELEASED: if L loc then True else released_src = released_tgt):
        sim_message loc (Message.concrete val released_src) (Message.concrete val released_tgt)
    | sim_message_reserve:
        sim_message loc Message.reserve Message.reserve
    .

    Inductive rel_write (tr: Trace.t lang) (loc: Loc.t) (to: Time.t): Prop :=
    | rel_write_write
        e from val released ord
        (IN: List.In (e, ThreadEvent.write loc from to val released ord) tr)
        (ORD: Ordering.le Ordering.acqrel ord)
    | rel_write_update
        e tsr valr valw releasedr releasedw ordr ordw
        (IN: List.In (e, ThreadEvent.update loc tsr to valr valw releasedr releasedw ordr ordw) tr)
        (ORD: Ordering.le Ordering.acqrel ordw)
    .

    Inductive sim_memory (tr: Trace.t lang) (mem_src mem_tgt: Memory.t): Prop :=
    | sim_memory_intro
        (SOUND: forall loc from to msg_src
                  (GET_SRC: Memory.get loc to mem_src = Some (from, msg_src)),
            exists msg_tgt,
              <<GET_TGT: Memory.get loc to mem_tgt = Some (from, msg_tgt)>> /\
              <<MSG: sim_message loc msg_src msg_tgt>>)
        (COMPLETE: forall loc from to msg_tgt
                     (GET_TGT: Memory.get loc to mem_tgt = Some (from, msg_tgt)),
            exists msg_src,
              <<GET_SRC: Memory.get loc to mem_src = Some (from, msg_src)>> /\
              <<MSG: sim_message loc msg_src msg_tgt>>)
        (REL_WRITES: forall loc to (REL_WRITE: rel_write tr loc to),
            exists from msg,
              <<GET_SRC: Memory.get loc to mem_src = Some (from, msg)>> /\
              <<GET_TGT: Memory.get loc to mem_tgt = Some (from, msg)>>)
    .

    Inductive sim_thread (tr: Trace.t lang) (e_src e_tgt: Thread.t lang): Prop :=
    | sim_thread_intro
        (STABLE: stable_thread e_src)
        (NORMAL_SRC: normal_thread e_src)
        (NORMAL_TGT: normal_thread e_tgt)
        (STATE: e_src.(Thread.state) = e_tgt.(Thread.state))
        (TVIEW: e_src.(Thread.local).(Local.tview) = e_tgt.(Thread.local).(Local.tview))
        (PROMISES_SRC: reserve_only e_src.(Thread.local).(Local.promises))
        (PROMISES_TGT: reserve_only e_tgt.(Thread.local).(Local.promises))
        (SC: e_src.(Thread.sc) = e_tgt.(Thread.sc))
        (MEMORY: sim_memory tr e_src.(Thread.memory) e_tgt.(Thread.memory))
    .
  End RASimThread.
End RASimThread.
