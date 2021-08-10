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
Require Import Behavior.

Require Import Cover.
Require Import MemorySplit.
Require Import MemoryMerge.
Require Import FulfillStep.
Require Import PromiseConsistent.

Require Import Program.


Set Implicit Arguments.


Lemma memory_cap_future
      mem0 mem1
      (CAP: Memory.cap mem0 mem1)
  :
    Memory.future_weak mem0 mem1.
Admitted.

(* TODO: use FutureCertify to prove it *)
Module UndefCertify.
  Definition certified (c: Configuration.t): Prop. Admitted.

  Lemma step_certified c0 c1 e tid
        (STEP: Configuration.step e tid c0 c1)
        (CERTIFIED: certified c0)
        (WF: Configuration.wf c0)
    :
      certified c1.
  Admitted.

  Lemma rtc_step_certified c0 c1
        (STEPS: rtc Configuration.tau_step c0 c1)
        (CERTIFIED: certified c0)
        (WF: Configuration.wf c0)
    :
      certified c1.
  Proof.
    revert CERTIFIED WF. induction STEPS; auto.
    i. inv H. eapply IHSTEPS; auto.
    { eapply step_certified; eauto. }
    { eapply Configuration.step_future; eauto. }
  Qed.

  Lemma certified_init s
    :
      certified (Configuration.init s).
  Admitted.

  Definition unchanged (prom: Memory.t) (mem0 mem1: Memory.t): Prop :=
    forall loc to from
           (UNDEF: Memory.get loc to prom = Some (from, Message.undef)),
    forall ts1 ts0 msg
           (GET: Memory.get loc ts1 mem1 = Some (ts0, msg))
           (CONCRETE: msg <> Message.reserve),
      Memory.get loc ts1 mem0 = Some (ts0, msg).

  Program Instance unchanged_PreOrder prom: PreOrder (unchanged prom).
  Next Obligation.
  Proof.
    ii. eauto.
  Qed.
  Next Obligation.
  Proof.
    ii. eauto.
  Qed.

  Lemma cap_unchanged mem0 mem1 prom
        (CAP: Memory.cap mem0 mem1)
        (* (CLOSED: Memory.closed mem0) *)
    :
      unchanged prom mem0 mem1.
  Proof.
    ii. eapply Memory.cap_inv in GET; eauto. des; ss.
  Admitted.

  Lemma step_unchanged c0 c1 tid e
        (CERTIFIED: certified c0)
        (WF: Configuration.wf c0)
        (STEP: Configuration.step e tid c0 c1)
    :
      ((<<UNCHANGED: forall tid' st lc
                            (TID: tid' <> tid)
                            (TID: IdentMap.find tid' c0.(Configuration.threads) = Some (st, lc)),
           UndefCertify.unchanged lc.(Local.promises) c0.(Configuration.memory) c1.(Configuration.memory)>>) \/
       (<<FAILURE: Configuration.steps_failure c0>>)).
  Admitted.

  Lemma opt_step_unchanged c0 c1 tid e
        (CERTIFIED: certified c0)
        (WF: Configuration.wf c0)
        (STEP: Configuration.opt_step e tid c0 c1)
    :
      ((<<UNCHANGED: forall tid' st lc
                            (TID: tid' <> tid)
                            (TID: IdentMap.find tid' c0.(Configuration.threads) = Some (st, lc)),
           UndefCertify.unchanged lc.(Local.promises) c0.(Configuration.memory) c1.(Configuration.memory)>>) \/
       (<<FAILURE: Configuration.steps_failure c0>>)).
  Proof.
    inv STEP.
    { left. red. i. refl. }
    { eapply step_unchanged; eauto. }
  Qed.
End UndefCertify.


(* TODO: from CapFlex.v *)
Module CapFlex.
  Record cap_flex (mem1 mem2: Memory.t) (tm: TimeMap.t): Prop :=
    {
      cap_flex_le: Memory.le mem1 mem2;
      cap_flex_middle: forall loc from1 to1 from2 to2
                              (ADJ: Memory.adjacent loc from1 to1 from2 to2 mem1)
                              (TO: Time.lt to1 from2),
          Memory.get loc from2 mem2 = Some (to1, Message.reserve);
      cap_flex_back: forall loc, Memory.get loc (tm loc) mem2 =
                                 Some (Memory.max_ts loc mem1, Message.reserve);
      cap_flex_complete: forall loc from to msg
                               (GET1: Memory.get loc to mem1 = None)
                               (GET2: Memory.get loc to mem2 = Some (from, msg)),
          (exists f m, Memory.get loc from mem1 = Some (f, m));
    }
  .

  Lemma cap_flex_inv
        mem1 mem2 tm
        loc from to msg
        (CAP: cap_flex mem1 mem2 tm)
        (GET: Memory.get loc to mem2 = Some (from, msg))
        (TM: forall loc, Time.lt (Memory.max_ts loc mem1) (tm loc))
    :
    Memory.get loc to mem1 = Some (from, msg) \/
    (Memory.get loc to mem1 = None /\
     exists from1 to2,
        Memory.adjacent loc from1 from to to2 mem1 /\
        Time.lt from to /\
        msg = Message.reserve) \/
    (Memory.get loc to mem1 = None /\
     from = Memory.max_ts loc mem1 /\
     to = tm loc /\
     msg = Message.reserve).
  Proof.
    inv CAP. move GET at bottom.
    destruct (Memory.get loc to mem1) as [[]|] eqn:GET1.
    { exploit cap_flex_le0; eauto. i.
      rewrite GET in x. inv x. auto. }
    right. exploit cap_flex_complete0; eauto. i. des.
    exploit Memory.max_ts_spec; eauto. i. des. inv MAX.
    - left.
      exploit Memory.adjacent_exists; try eapply H; eauto. i. des.
      assert (LT: Time.lt from from2).
      { clear cap_flex_middle0 cap_flex_back0 cap_flex_complete0 GET0 H.
        (* clear MIDDLE BACK COMPLETE GET0 H. *)
        inv x1. rewrite GET0 in x. inv x.
        exploit Memory.get_ts; try exact GET2. i. des.
        { subst. inv TS. }
        destruct (Time.le_lt_dec from2 from); auto.
        inv l.
        - exfalso.
          exploit Memory.get_ts; try exact GET0. i. des.
          { subst. inv H. }
          exploit Memory.get_disjoint; [exact GET0|exact GET2|..]. i. des.
          { subst. timetac. }
          apply (x2 from); econs; ss.
          + refl.
          + econs. auto.
        - exfalso. inv H.
          exploit cap_flex_le0; try exact GET2. i.
          exploit Memory.get_ts; try exact GET. i. des.
          { subst. rewrite GET1 in GET0. inv GET0. }
          exploit Memory.get_disjoint; [exact GET|exact x|..]. i. des.
          { subst. rewrite GET1 in GET2. inv GET2. }
          destruct (Time.le_lt_dec to to2).
          + apply (x3 to); econs; ss. refl.
          + apply (x3 to2); econs; ss.
            * econs. auto.
            * refl.
      }
      exploit cap_flex_middle0; try eapply x1; eauto. i.
      destruct (Time.eq_dec to from2).
      + subst. rewrite GET in x0. inv x0. esplits; eauto.
      + exfalso. inv x1.
        exploit Memory.get_ts; try exact GET. i. des.
        { subst. rewrite GET1 in x. inv x. }
        exploit Memory.get_ts; try exact x0. i. des.
        { subst. exploit cap_flex_le0; try exact GET3. i.
          exploit Memory.get_disjoint; [exact GET|exact x1|..]. i. des.
          { subst. rewrite GET1 in GET3. inv GET3. }
          destruct (Time.le_lt_dec to to2).
          - apply (x4 to); econs; ss. refl.
          - apply (x4 to2); econs; ss.
            + econs. auto.
            + refl.
        }
        exploit Memory.get_disjoint; [exact GET|exact x0|..]. i. des; try congr.
        destruct (Time.le_lt_dec to from2).
        * apply (x4 to); econs; ss. refl.
        * apply (x4 from2); econs; ss.
          { econs. auto. }
          { refl. }
    - right. inv H. do 2 (split; auto).
      rewrite GET0 in x. inv x.
      specialize (cap_flex_back0 loc).
      exploit Memory.get_ts; try exact GET. i. des; try congr.
      exploit Memory.get_disjoint; [exact GET|exact cap_flex_back0|..]. i. des.
      { subst. esplits; eauto. }
      exfalso.
      destruct (Time.le_lt_dec to (tm loc)).
      + apply (x1 to); econs; ss. refl.
      + apply (x1 (tm loc)); econs; s;
          eauto using TM; try refl.
        econs. ss.
  Qed.

  Lemma cap_flex_exists
        mem1 tm
        (CLOSED1: Memory.closed mem1)
        (TM: forall loc, Time.lt (Memory.max_ts loc mem1) (tm loc))
    :
      exists mem2, (<<CAP: cap_flex mem1 mem2 tm>>).
  Proof.
  Admitted.

  Lemma cap_cap_flex mem1 mem2
        (CAP: Memory.cap mem1 mem2)
    :
      cap_flex mem1 mem2 (fun loc => Time.incr (Memory.max_ts loc mem1)).
  Proof.
    inv CAP. econs; eauto.
  Qed.

  Lemma cap_flex_max_ts mem1 mem2 tm
        (CLOSED: Memory.closed mem1)
        (CAP: cap_flex mem1 mem2 tm)
        (TM: forall loc, Time.lt (Memory.max_ts loc mem1) (tm loc))
    :
      forall loc,
        Memory.max_ts loc mem2 = tm loc.
  Proof.
    i. set (BACK:=(cap_flex_back CAP) loc).
    exploit Memory.max_ts_spec; try exact BACK. i. des.
    apply TimeFacts.antisym; ss.
    destruct (Time.le_lt_dec (Memory.max_ts loc mem2) (tm loc)); ss.
    exploit cap_flex_inv; try exact GET; eauto. i. des.
    - exploit Memory.max_ts_spec; try exact x0. i. des.
      exploit TimeFacts.lt_le_lt; try exact l; try exact MAX0. i.
      specialize (TM loc). rewrite x1 in TM. timetac.
    - inv x1. exploit Memory.get_ts; try exact GET2. i. des.
      { rewrite x1 in *. inv l. }
      exploit Memory.max_ts_spec; try exact GET2. i. des.
      exploit TimeFacts.lt_le_lt; try exact x1; try exact MAX0. i.
      rewrite x3 in l. specialize (TM loc). rewrite l in TM. timetac.
    - subst. rewrite x2 in *. timetac.
  Qed.

  Lemma cap_flex_covered
        mem0 mem1 tm
        (CAP: cap_flex mem0 mem1 tm)
        (CLOSED: Memory.closed mem0)
        (TM: forall loc, Time.lt (Memory.max_ts loc mem0) (tm loc))
        loc to
    :
      Interval.mem (Time.bot, (tm loc)) to
      <->
      covered loc to mem1.
  Proof.
  Admitted.

  Lemma cap_flex_closed mem cap tm
        (CAP: cap_flex mem cap tm)
        (TM: forall loc, Time.lt (Memory.max_ts loc mem) (tm loc))
        (CLOSED: Memory.closed mem)
    :
      Memory.closed cap.
  Proof.
  Admitted.

  Lemma cap_flex_wf
        lc mem1 mem2 tm
        (CAP: cap_flex mem1 mem2 tm)
        (WF: Local.wf lc mem1):
    Local.wf lc mem2.
  Proof.
  Admitted.

  Lemma cap_flex_closed_timemap
        mem1 mem2 sc tm
        (CAP: cap_flex mem1 mem2 tm)
        (CLOSED: Memory.closed_timemap sc mem1):
    Memory.closed_timemap sc mem2.
  Proof.
  Admitted.

  Lemma cap_flex_future_weak
        mem1 mem2 tm
        (CAP: cap_flex mem1 mem2 tm)
        (TM: forall loc, Time.lt (Memory.max_ts loc mem1) (tm loc)):
    Memory.future_weak mem1 mem2.
  Proof.
    econs; ii.
    { eapply CAP in GET. esplits; eauto. refl. }
    { eapply cap_flex_inv in GET2; eauto. des; clarify. }
    { eapply cap_flex_inv in GET2; eauto. des; clarify. }
  Qed.

  Lemma cap_flex_inj
        mem mem1 mem2 tm
        (CAP1: cap_flex mem mem1 tm)
        (CAP2: cap_flex mem mem2 tm)
        (CLOSED: Memory.closed mem)
        (TM: forall loc, Time.lt (Memory.max_ts loc mem) (tm loc)):
    mem1 = mem2.
  Proof.
  Admitted.

  Definition consistent (tm: TimeMap.t) lang (e: Thread.t lang): Prop :=
    forall mem1
           (CAP: cap_flex (Thread.memory e) mem1 tm),
      (<<FAILURE: Thread.steps_failure (Thread.mk _ (Thread.state e) (Thread.local e) (Thread.sc e) mem1)>>) \/
      exists e2,
        ( <<STEPS: rtc (@Thread.tau_step _) (Thread.mk _ (Thread.state e) (Thread.local e) (Thread.sc e) mem1) e2>>) /\
        (<<PROMISES: (Local.promises (Thread.local e2)) = Memory.bot>>).

  Lemma consistent_thread_consistent lang st lc sc mem tm
        (CONSISTENT: consistent tm (Thread.mk lang st lc sc mem))
        (LOCAL: Local.wf lc mem)
        (MEMORY: Memory.closed mem)
        (SC: Memory.closed_timemap sc mem)
        (TM: forall loc, Time.lt (Memory.max_ts loc mem) (tm loc))
    :
      Thread.consistent (Thread.mk lang st lc sc mem).
  Proof.
  Admitted.

  Lemma thread_consistent_consistent lang st lc sc mem tm
        (CONSISTENT: Thread.consistent (Thread.mk lang st lc sc mem))
        (LOCAL: Local.wf lc mem)
        (MEMORY: Memory.closed mem)
        (SC: Memory.closed_timemap sc mem)
        (TM: forall loc, Time.lt (Memory.max_ts loc mem) (tm loc))
    :
      consistent tm (Thread.mk lang st lc sc mem).
  Proof.
  Admitted.

End CapFlex.


Module Messages.
  Definition t := forall (loc: Loc.t) (to: Time.t) (from: Time.t) (msg: Message.t), Prop.

  Variant of_memory (mem: Memory.t): t :=
  | of_memory_intro
      loc to from msg
      (GET: Memory.get loc to mem = Some (from, msg))
    :
      of_memory mem loc to from msg
  .
End Messages.

(* TODO: from MemoryProps.v *)
Section UNCHANGABLE.
  Inductive unchangable (mem prom: Memory.t) (l: Loc.t) (t: Time.t) (from: Time.t) (msg: Message.t): Prop :=
  | unchangable_intro
      (GET: Memory.get l t mem = Some (from, msg))
      (NPROM: Memory.get l t prom = None)
  .

  Lemma step_unchangable pf e lang (th0 th1: Thread.t lang)
        (STEP: Thread.step pf e th0 th1)
    :
      unchangable (Thread.memory th0) (Local.promises (Thread.local th0)) <4=
      unchangable (Thread.memory th1) (Local.promises (Thread.local th1)).
  Proof.
  Admitted.

  Lemma opt_step_unchangable e lang (th0 th1: Thread.t lang)
        (STEP: Thread.opt_step e th0 th1)
    :
      unchangable (Thread.memory th0) (Local.promises (Thread.local th0)) <4=
      unchangable (Thread.memory th1) (Local.promises (Thread.local th1)).
  Proof.
  Admitted.

  Lemma rtc_step_unchangable lang (th0 th1: Thread.t lang)
        (STEP: rtc (@Thread.tau_step _) th0 th1)
    :
      unchangable (Thread.memory th0) (Local.promises (Thread.local th0)) <4=
      unchangable (Thread.memory th1) (Local.promises (Thread.local th1)).
  Proof.
  Admitted.

  Lemma other_promise_unchangable mem ths sc tid1 tid2 st1 st2 tvw1 prom1 tvw2 prom2
        (CWF: Configuration.wf (Configuration.mk ths sc mem))
        (TID1: IdentMap.find tid1 ths = Some (st1, Local.mk tvw1 prom1))
        (TID2: IdentMap.find tid2 ths = Some (st2, Local.mk tvw2 prom2))
        (DIFF: tid1 <> tid2)
    :
      Messages.of_memory prom2 <4= unchangable mem prom1.
  Proof.
    ii. inv PR.
    inv CWF. inv WF. destruct st1, st2. econs; eauto.
    - exploit THREADS; try apply TID2; eauto. intros LCWF. inv LCWF. eauto.
    - destruct (Memory.get x0 x1 prom1) eqn:GET0; eauto. exfalso.
      exploit DISJOINT; eauto. intros LCDISJ. inv LCDISJ. destruct p.
      inv DISJOINT0. exploit DISJOINT1; eauto. i. des.
      eapply Memory.get_ts in GET. eapply Memory.get_ts in GET0. des; clarify.
      eapply x5; eauto.
      + instantiate (1:=x1). econs; ss; eauto. refl.
      + econs; ss; eauto. refl.
  Qed.
End UNCHANGABLE.
