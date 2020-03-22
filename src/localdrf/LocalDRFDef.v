Require Import RelationClasses.

From Paco Require Import paco.
From sflib Require Import sflib.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import Language.
From PromisingLib Require Import Loc.
Require Import Time.
Require Import Event.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import MemoryFacts.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.
Require Import Progress.
Require Import Behavior.
Require Import Cover.
Require Import Pred.
Require Import Trace.

Set Implicit Arguments.


Inductive step_all A B C D (step: A -> B -> C -> D -> Prop): C -> D -> Prop :=
| step_all_intro
    a b c d
    (STEP: step a b c d)
  :
    step_all step c d.

Section LOCALDRF.

  Variable L: Loc.t -> bool.

  Definition valid_event (e: ThreadEvent.t): Prop :=
    forall loc from to msg kind (PROMISE: e = ThreadEvent.promise loc from to msg kind) (LOC: L loc),
      msg = Message.reserve.

  Definition valid_step (e: MachineEvent.t) (tid: Ident.t)
             (c0 c1: Configuration.t): Prop :=
    exists lang tr,
      (<<STEP: @Trace.configuration_step lang tr e tid c0 c1>>) /\
      (<<VALID: List.Forall (compose valid_event snd) tr>>).

  Inductive configuration_steps_trace:
    forall (c0 c1: Configuration.t) (tr: list (Ident.t * sigT Trace.t)), Prop :=
  | configuration_steps_trace_nil
      c0
    :
      configuration_steps_trace c0 c0 []
  | configuration_steps_trace_cons
      c0 c1 c2 trs lang tr e tid
      (STEPS: configuration_steps_trace c0 c1 trs)
      (STEP: @Trace.configuration_step lang tr e tid c0 c1)
      (VALID: List.Forall (compose valid_event snd) tr)
    :
      configuration_steps_trace c0 c2 (trs ++ [(tid, existT _ _ tr)]) (* add at "last" *)
  .

  Inductive racy_read (loc: Loc.t) (ts: Time.t):
    forall lang (th: Thread.t lang) (e: ThreadEvent.t), Prop :=
  | racy_read_read
      lang (th: Thread.t lang)
      valr releasedr ordr
      (VIEW: Time.lt (th.(Thread.local).(Local.tview).(TView.cur).(View.rlx) loc) ts)
    :
      racy_read loc ts th (ThreadEvent.read loc ts valr releasedr ordr)
  | racy_read_update
      lang (th: Thread.t lang)
      to valr valw releasedr releasedw ordr ordw
      (VIEW: Time.lt (th.(Thread.local).(Local.tview).(TView.cur).(View.rlx) loc) ts)
    :
      racy_read loc ts th (ThreadEvent.update loc ts to valr valw releasedr releasedw ordr ordw)
  .

  Inductive racy_write (loc: Loc.t) (ts: Time.t):
    forall lang (th: Thread.t lang) (e: ThreadEvent.t), Prop :=
  | racy_write_write
      lang (th: Thread.t lang)
      from valw releasedw ordw
      (ORD: Ordering.le ordw Ordering.relaxed)
    :
      racy_write loc ts th (ThreadEvent.write loc from ts valw releasedw ordw)
  | racy_write_update
      lang (th: Thread.t lang)
      from valr valw releasedr releasedw ordr ordw
      (ORD: Ordering.le ordw Ordering.relaxed)
    :
      racy_write loc ts th (ThreadEvent.update loc from ts valr valw releasedr releasedw ordr ordw)
  .

  Definition racefree (s: Threads.syntax): Prop :=
    forall c0 c1 trs
           loc ts
           tid0 tid1 lang0 lang1 tr0 tr1 th0 th1 e0 e1
           (CSTEPS: configuration_steps_trace c0 c1 trs)
           (TRACE0: List.In (tid0, existT _ lang0 tr0) trs)
           (TRACE1: List.In (tid1, existT _ lang1 tr1) trs)
           (EVENT0: List.In (th0, e0) tr0)
           (EVENT1: List.In (th1, e1) tr1)
           (WRITE: racy_write loc ts th0 e0)
           (READ: racy_read loc ts th1 e1),
      False.

  Theorem local_DRF_PF s
          (RACEFRFEE: racefree s)
    :
      behaviors Configuration.step (Configuration.init s) <1=
      behaviors valid_step (Configuration.init s).
  Admitted.

End LOCALDRF.
