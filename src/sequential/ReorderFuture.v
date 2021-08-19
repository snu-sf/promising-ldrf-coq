Require Import RelationClasses.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import Loc.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Language.

Require Import Event.
Require Import Time.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import MemoryFacts.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.

Require Import Cover.
Require Import MemorySplit.
Require Import MemoryMerge.
Require Import FulfillStep.
Require Import JoinedView.
Require Import Pred.
Require Import Trace.
Require Import MemoryProps.
Require Import LowerMemory.

Require Import gSimAux.

Set Implicit Arguments.

Definition release_event (e: ThreadEvent.t): Prop :=
  match e with
  | ThreadEvent.update _ _ _ _ _ _ _ _ ordw => Ordering.le Ordering.strong_relaxed ordw
  | ThreadEvent.write _ _ _ _ _ ord => Ordering.le Ordering.strong_relaxed ord
  | ThreadEvent.fence _ ordw => Ordering.le Ordering.strong_relaxed ordw
  | ThreadEvent.syscall _ => True
  | _ => False
  end.

Definition delayed
           lang (st0 st1: Language.state lang) (lc0 lc1: Local.t)
           (mem0: Memory.t)
           (sc0: TimeMap.t)
           (views0: Loc.t -> Time.t -> list View.t)
           (fin: Messages.t): Prop
  :=
    forall (mem1: Memory.t)
           (sc1: TimeMap.t)
           (views1: Loc.t -> Time.t -> list View.t)
           (MEM: Memory.closed mem1)
           (FUTURE: Memory.future mem0 mem1)
           (SCLE: TimeMap.le sc0 sc1)
           (FINALIZED: fin <4= Messages.of_memory mem1)
           (VIEWLE: views_le views0 views1)
           (VIEWS: wf_views views1)
           (JOINED: joined_memory views1 mem1)
           (SC: Memory.closed_timemap sc1 mem1)
           (LOCAL: Local.wf lc1 mem1),
    exists mem1' lc1',
      (<<LOCAL: Local.wf lc0 mem1>>) /\
      (<<JOINED: joined_released views1 lc0.(Local.promises) lc0.(Local.tview).(TView.rel)>>) /\
      (<<STEPS: rtc (tau (@pred_step (fun e => no_promise e /\ ~ release_event e) lang)) (Thread.mk _ st0 lc0 sc1 mem1) (Thread.mk _ st1 lc1' sc1 mem1')>>) /\
      (<<LOCAL: lower_local lc1' lc1>>) /\
      (<<MEM: lower_memory mem1' mem1>>)
.

(* Lemma delayed_future *)
(*       lang (st0 st1: Language.state lang) lc0 lc1 *)
(*       mem0 sc0 views0 fin *)
(*       (DELAYED: delayed st0 st1 lc0 lc1 mem0 sc0 views0 fin) *)
(*       mem1 sc1 views1 *)
(*       (MEM: Memory.closed mem1) *)


(*            (MEM: Memory.closed mem1) *)
(*            (FUTURE: Memory.future mem0 mem1) *)
(*            (SCLE: TimeMap.le sc0 sc1) *)
(*            (FINALIZED: fin <4= Messages.of_memory mem1) *)
(*            (VIEWLE: views_le views0 views1) *)
(*            (VIEWS: wf_views views1) *)
(*            (JOINED: joined_memory views1 mem1) *)
(*            (SC: Memory.closed_timemap sc1 mem1) *)
(*            (LOCAL: Local.wf lc1 mem1), *)


(*       (SC: *)

(* Lemma step_delayed *)
(*       lang st0 st1 st2 lc0 lc1 lc2 *)
(*       mem1 views0 views1 fin0 *)
(*       pf e *)
(*       (STEP: JThread.step pf e (Thread.mk _ st1 lc1 sc1 mem1) (Thread.mk _ st2 lc2 sc2 mem2)) *)
(*       (SILENT: no_promise e) *)
(*       (DELAYED: delayed st0 st1 lc0 lc1 mem- m *)
(*   : *)
(*     exists pf' e' st0' lc0', *)
(*       (<<STEP: JThread.opt_step pf' e' *)



(*       (st0 st1: Language.state lang) (lc0 lc1: Local.t) *)
(*       (mem0: Memory.t) *)


(* Definition delayed_strong *)
(*            lang (st0 st1: Language.state lang) (lc0 lc1: Local.t) *)
(*            (mem0: Memory.t) *)
(*            (sc0: TimeMap.t) *)
(*            (views0: Loc.t -> Time.t -> list View.t) *)
(*            (fin: Messages.t): Prop *)
(*   := *)
(*     forall (mem1: Memory.t) *)
(*            (sc1: TimeMap.t) *)
(*            (views1: Loc.t -> Time.t -> list View.t) *)
(*            (MEM: Memory.closed mem1) *)
(*            (FUTURE: Memory.future mem0 mem1) *)
(*            (SCLE: TimeMap.le sc0 sc1) *)
(*            (FINALIZED: fin <4= Messages.of_memory mem1) *)
(*            (VIEWLE: views_le views0 views1) *)
(*            (VIEWS: wf_views views1) *)
(*            (JOINED: joined_memory views1 mem1) *)
(*            (SC: Memory.closed_timemap sc1 mem1) *)
(*            (LOCAL: Local.wf lc1 mem1) *)

(*            (lc0': Local.t) *)
(*            (TVIEW: TView.le lc1'.(Local.tview) lc1.(Local.tview)) *)


(*     , *)
(*     exists mem1' lc1', *)
(*       (<<LOCAL: Local.wf lc0 mem1>>) /\ *)
(*       (<<JOINED: joined_released views1 lc0.(Local.promises) lc0.(Local.tview).(TView.rel)>>) /\ *)
(*       (<<STEPS: rtc (tau (@pred_step (fun e => no_promise e /\ ~ release_event e) lang)) (Thread.mk _ st0 lc0 sc1 mem1) (Thread.mk _ st1 lc1' sc1 mem1')>>) /\ *)
(*       (<<TVIEW: TView.le lc1'.(Local.tview) lc1.(Local.tview)>>) /\ *)
(*       (<<PROMISES: lc1'.(Local.promises) = lc1.(Local.promises)>>) *)
(* . *)
