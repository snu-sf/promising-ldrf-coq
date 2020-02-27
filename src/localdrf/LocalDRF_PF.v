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

Require Import Trace.

Set Implicit Arguments.


Section LOCALDRF.

  Variable L: Loc.t -> Prop.

  Definition valid_event (e: ThreadEvent.t): Prop :=
    forall loc from to msg (PROMISE: e = ThreadEvent.promise loc from to msg Memory.op_kind_add),
      ~ L loc.

  Definition valid_step (e: MachineEvent.t) (tid: Ident.t)
             (c0 c1: Configuration.t): Prop :=
    exists tr,
      (<<STEP: Trace.configuration_step tr e tid c0 c1>>) /\
      (<<VALID: List.Forall valid_event tr>>).

  Definition racefree (s: Threads.syntax): Prop :=
    forall c0 c1 c2
           loc to
           tid tr from valw releasedw ordw e
           lang st1 lc1 e2 pf st3 lc3 sc3 memory3 valr releasedr ordr
           (CSTEPS0: rtc (union (valid_step MachineEvent.silent)) (Configuration.init s) c0)
           (CSTEP: Trace.configuration_step tr e tid c0 c1)
           (VALID: List.Forall valid_event tr)
           (WRITE: List.In (ThreadEvent.write loc from to valw releasedw ordw) tr)
           (ORD: Ordering.le ordw Ordering.relaxed)
           (CSTEPS1: rtc (union (valid_step MachineEvent.silent)) c1 c2)

           (TID: IdentMap.find tid c2.(Configuration.threads) = Some (existT _ lang st1, lc1))
           (STEPS: Trace.steps tr (Thread.mk _ st1 lc1 c1.(Configuration.sc) c2.(Configuration.memory)) e2)
           (SILENT: List.Forall (fun e => ThreadEvent.get_machine_event e = MachineEvent.silent) tr)
           (VALID: List.Forall valid_event tr)
           (READ: Thread.step pf (ThreadEvent.read loc to valr releasedr ordr)
                              e2 (Thread.mk _ st3 lc3 sc3 memory3))
           (VIEW: Time.lt
                    (e2.(Thread.local).(Local.tview).(TView.cur).(View.rlx) loc) to)
           (CONSISTENT: Thread.consistent (Thread.mk _ st3 lc3 sc3 memory3)),
      False.

  Theorem local_DRF_PF s
          (RACEFRFEE: racefree s)
    :
      behaviors Configuration.step (Configuration.init s) <1=
      behaviors valid_step (Configuration.init s).
  Admitted.

End LOCALDRF.
