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

Inductive joined_promise_steps lang:
  forall (th0 th1: Thread.t lang) (views0 views1: Loc.t -> Time.t -> list View.t), Prop :=
| joined_promise_steps_base
    th0 views0
  :
    joined_promise_steps th0 th0 views0 views0
| joined_promise_steps_step
    th0 th1 th2 views0 views1 views2
    pf loc from to msg kind
    (STEP: JThread.step pf (ThreadEvent.promise loc from to msg kind) th0 th1 views0 views1)
    (STEPS: joined_promise_steps th1 th2 views1 views2)
  :
    joined_promise_steps th0 th2 views0 views2
.

Definition release_event (e: ThreadEvent.t): Prop :=
  match e with
  | ThreadEvent.update _ _ _ _ _ _ _ _ ordw => Ordering.le Ordering.strong_relaxed ordw
  | ThreadEvent.write _ _ _ _ _ ord => Ordering.le Ordering.strong_relaxed ord
  | ThreadEvent.fence _ ordw => Ordering.le Ordering.strong_relaxed ordw
  | ThreadEvent.syscall _ => True
  | ThreadEvent.failure => True
  | ThreadEvent.racy_write _ _ _ => True
  | ThreadEvent.racy_update _ _ _ _ _ => True
  | _ => False
  end.

Variant lower_step {lang} (th0 th1: Thread.t lang): Prop :=
| lower_step_intro
    pf e
    (STEP: Thread.step pf e th0 th1)
    (NPROMISE: no_promise e)
    (NRELEASE: ~ release_event e)
    (MEM: lower_memory th1.(Thread.memory) th0.(Thread.memory))
.

Variant lower_steps {lang} (th0 th1: Thread.t lang): Prop :=
| lower_steps_intro
    (STEPS: rtc (tau (@pred_step (fun e => no_promise e /\ ~ release_event e) lang)) th0 th1)
    (MEM: lower_memory th1.(Thread.memory) th0.(Thread.memory))
.

Lemma lower_steps_equiv lang (th0 th1: Thread.t lang)
  :
    lower_steps th0 th1 <-> rtc lower_step th0 th1.
Proof.
  split.
  { i. inv H. revert MEM. induction STEPS.
    { i. refl. }
    { i. admit. }
  }
  { i. induction H.
    { econs; eauto. refl. }
    { inv IHclos_refl_trans_1n. inv H. econs.
      { econs; [|eauto]. econs.
        { econs; eauto. econs; eauto. }
        { destruct e; ss. }
      }
      { etrans; eauto. }
    }
  }
Admitted.

Definition delayed {lang} (th0 th1: Thread.t lang): Prop
  :=
    exists th1',
      (<<STEPS: rtc (tau (@pred_step (fun e => no_promise e /\ ~ release_event e) lang)) th0 th1'>>) /\
      (<<MEM: lower_memory th1'.(Thread.memory) th1.(Thread.memory)>>) /\
      (<<SC: TimeMap.le th1'.(Thread.sc) th1.(Thread.sc)>>) /\
      (<<STATE: th1'.(Thread.state) = th1.(Thread.state)>>) /\
      (<<LOCAL: lower_local th1'.(Thread.local) th1.(Thread.local)>>).

Lemma delayed_refl lang (th: Thread.t lang)
  :
    delayed th th.
Proof.
  eexists. esplits; eauto; try refl.
Qed.

Lemma step_split lang (th0 th2: Thread.t lang) pf e views0 views2
      (STEP: JThread.step pf e th0 th2 views0 views2)
      (NRELEASE: ~ release_event e)
  :
    exists th1,
      (<<PROMISES: joined_promise_steps th0 th1 views0 views2>>) /\
      (<<LOWER: rtc lower_step th1 th2>>) /\
      (<<MEM: th1.(Thread.memory) = th2.(Thread.memory)>>) /\
      (<<SC: th1.(Thread.sc) = th2.(Thread.sc)>>).
Proof.
  inv STEP. inv STEP0.
  { inv STEP. esplits.
    { econs; [|econs]. econs; eauto.
      { econs. econs; eauto. }
    }
    { econs. }
    { ss. }
    { ss. }
  }
  { inv STEP. inv LOCAL; ss.
    { esplits.
      { econs; [|econs]
        {


      { eauto. }

        eauto.  ss. econs.

        econs.
        {


  /\


      /\

      (<<STEP: Thread.step pf th0 th2>>).




destruct (Thread.local th); ss.




        Thread.mk _ st0 lc0 sc1 mem1) (Thread.mk _ st1 lc1' sc1 mem1')>>) /\
      (<<LOCAL: lower_local lc1' lc1>>) /\
      (<<MEM: lower_memory mem1' mem1>>).


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

Lemma delayed_current
      lang (st: Language.state lang) lc
      mem0 sc0 views0 fin
  :
    delayed _ st st lc lc mem0 sc0 views0 fin.
Proof.
Admitted.

Lemma delayed_future
      lang (st0 st1: Language.state lang) lc0 lc1
      mem0 sc0 views0 fin0
      mem1 sc1 views1 fin1
      (MEM: Memory.future mem0 mem1)
      (SC: TimeMap.le sc0 sc1)
      (VIEWS: views_le views0 views1)
      (FIN: fin0 <4= fin1)
      (FINALIZED: fin1 <4= Messages.of_memory mem1)
      (DELAYED: delayed _ st0 st1 lc0 lc1 mem0 sc0 views0 fin0)
  :
    delayed _ st0 st1 lc0 lc1 mem1 sc1 views1 fin1.
Proof.
Admitted.

Lemma delayed_step
      lang (st0 st1 st2: Language.state lang) lc0 lc1 lc2
      mem1 sc1 views1 mem2 sc2 views2 fin
      pf e
      (STEP: JThread.step pf e (Thread.mk _ st1 lc1 sc1 mem1) (Thread.mk _ st2 lc2 sc2 mem2) views1 views2)
      (NRELEASE: ~ release_event e)
      (DELAYED: delayed _ st0 st1 lc0 lc1 mem1 sc1 views1 fin)
  :
    exists lc0',
      (<<PROMISES: joined_promise_steps (Thread.mk _ st0 lc0 sc1 mem1) (Thread.mk _ st0 lc0' sc2 mem2) views1 views2>>) /\
      (<<DELAYED: delayed _ st0 st2 lc0' lc2 mem2 sc2 views2 (fin \4/ committed mem1 lc1.(Local.promises) mem2 lc2.(Local.promises))>>).
Proof.
Admitted.





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

Lemma delayed_current
      lang (st: Language.state lang) lc
      mem0 sc0 views0 fin
  :
    delayed _ st st lc lc mem0 sc0 views0 fin.
Proof.
Admitted.

Lemma delayed_future
      lang (st0 st1: Language.state lang) lc0 lc1
      mem0 sc0 views0 fin0
      mem1 sc1 views1 fin1
      (MEM: Memory.future mem0 mem1)
      (SC: TimeMap.le sc0 sc1)
      (VIEWS: views_le views0 views1)
      (FIN: fin0 <4= fin1)
      (FINALIZED: fin1 <4= Messages.of_memory mem1)
      (DELAYED: delayed _ st0 st1 lc0 lc1 mem0 sc0 views0 fin0)
  :
    delayed _ st0 st1 lc0 lc1 mem1 sc1 views1 fin1.
Proof.
Admitted.

Lemma delayed_step
      lang (st0 st1 st2: Language.state lang) lc0 lc1 lc2
      mem1 sc1 views1 mem2 sc2 views2 fin
      pf e
      (STEP: JThread.step pf e (Thread.mk _ st1 lc1 sc1 mem1) (Thread.mk _ st2 lc2 sc2 mem2) views1 views2)
      (NRELEASE: ~ release_event e)
      (DELAYED: delayed _ st0 st1 lc0 lc1 mem1 sc1 views1 fin)
  :
    exists lc0',
      (<<PROMISES: joined_promise_steps (Thread.mk _ st0 lc0 sc1 mem1) (Thread.mk _ st0 lc0' sc2 mem2) views1 views2>>) /\
      (<<DELAYED: delayed _ st0 st2 lc0' lc2 mem2 sc2 views2 (fin \4/ committed mem1 lc1.(Local.promises) mem2 lc2.(Local.promises))>>).
Proof.
Admitted.
