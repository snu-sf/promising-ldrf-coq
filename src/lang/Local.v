Require Import Omega.
Require Import Bool.
Require Import RelationClasses.

Require Import sflib.
From Paco Require Import paco.

Require Import Axioms.
Require Import Basic.
Require Import DataStructure.
Require Import DenseOrder.
Require Import Event.
Require Import Time.
Require Import Language.

Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.

Set Implicit Arguments.


Module ThreadEvent.
  Inductive t :=
  | promise (loc:Loc.t) (from to:Time.t) (msg:Message.t) (kind:Memory.op_kind)
  | silent
  | read (loc:Loc.t) (ts:Time.t) (val:Const.t) (released:option View.t) (ord:Ordering.t)
  | write (loc:Loc.t) (from to:Time.t) (val:Const.t) (released:option View.t) (ord:Ordering.t)
  | update (loc:Loc.t) (tsr tsw:Time.t) (valr valw:Const.t) (releasedr releasedw:option View.t) (ordr ordw:Ordering.t)
  | fence (ordr ordw:Ordering.t)
  | syscall (e:Event.t)
  .
  Hint Constructors t.

  Inductive kind :=
  | kind_promise
  | kind_syscall
  | kind_others
  .
  Hint Constructors kind.

  Definition kinds_all := fun k: kind => True.
  Hint Unfold kinds_all.
  Definition kinds_promise := fun k: kind => k = kind_promise.
  Hint Unfold kinds_promise.
  Definition kinds_program := fun k: kind => k <> kind_promise.
  Hint Unfold kinds_program.
  Definition kinds_tau := fun k: kind => k <> kind_syscall.
  Hint Unfold kinds_tau.

  Definition get_kind (e:t): kind :=
    match e with
    | promise _ _ _ _ _ => kind_promise
    | syscall _ => kind_syscall
    | _ => kind_others
    end.

  Definition get_event (e:t): option Event.t :=
    match e with
    | syscall e => Some e
    | _ => None
    end.

  Definition get_program_event (e:t) : ProgramEvent.t :=
    match e with
    | promise _ _ _ _ _  => ProgramEvent.silent
    | silent => ProgramEvent.silent
    | read loc _ val _ ord => ProgramEvent.read loc val ord
    | write loc _ _ val _ ord => ProgramEvent.write loc val ord
    | update loc _ _ valr valw _ _ ordr ordw => ProgramEvent.update loc valr valw ordr ordw
    | fence ordr ordw => ProgramEvent.fence ordr ordw
    | syscall ev => ProgramEvent.syscall ev
    end.

  Definition is_promising (e:t) : option (Loc.t * Time.t) :=
    match e with
    | promise loc from to msg kind => Some (loc, to)
    | _ => None
    end.

  Definition is_lower_none (e:t) : bool :=
    match e with
    | promise loc from to msg kind => Memory.op_kind_is_lower kind && Message.is_released_none msg
    | _ => false
    end.

  Definition is_reading (e:t): option (Loc.t * Time.t * Const.t * option View.t * Ordering.t) :=
    match e with
    | read loc ts val released ord => Some (loc, ts, val, released, ord)
    | update loc tsr _ valr _ releasedr _ ordr _ => Some (loc, tsr, valr, releasedr, ordr)
    | _ => None
    end.

  Definition is_writing (e:t): option (Loc.t * Time.t * Time.t * Const.t * option View.t * Ordering.t) :=
    match e with
    | write loc from to val released ord => Some (loc, from, to, val, released, ord)
    | update loc tsr tsw _ valw _ releasedw _ ordw => Some (loc, tsr, tsw, valw, releasedw, ordw)
    | _ => None
    end.

  Definition is_accessing (e:t): option (Loc.t * Time.t) :=
    match e with
    | read loc ts _ _ _ => Some (loc, ts)
    | write loc _ ts _ _ _ => Some (loc, ts)
    | update loc _ ts _ _ _ _ _ _ => Some (loc, ts)
    | _ => None
    end.

  Inductive le: forall (lhs rhs:t), Prop :=
  | le_promise
      loc from to msg1 msg2 kind1 kind2
      (LEREL: Message.le msg1 msg2):
      le (promise loc from to msg1 kind1) (promise loc from to msg2 kind2)
  | le_silent:
      le silent silent
  | le_read
      loc ts val rel1 rel2 ord
      (LEREL: View.opt_le rel1 rel2):
      le (read loc ts val rel1 ord) (read loc ts val rel2 ord)
  | le_write
      loc from to val rel1 rel2 ord
      (LEREL: View.opt_le rel1 rel2):
      le (write loc from to val rel1 ord) (write loc from to val rel2 ord)
  | le_update
      loc tsr tsw valr valw relr1 relr2 relw1 relw2 ordr ordw
      (LEREL: View.opt_le relr1 relr2)
      (LEREL: View.opt_le relw1 relw2):
      le (update loc tsr tsw valr valw relr1 relw1 ordr ordw) (update loc tsr tsw valr valw relr2 relw2 ordr ordw)
  | le_fence ordr ordw:
      le (fence ordr ordw) (fence ordr ordw)
  | le_syscall e:
      le (syscall e) (syscall e)
  .
  Hint Constructors le.

  Definition lift (ord0:Ordering.t) (e:t): t :=
    match e with
    | promise loc from to msg kind =>
      promise loc from to msg kind
    | silent => silent
    | read loc ts val released ord =>
      read loc ts val released (Ordering.join ord0 ord)
    | write loc from to val released ord =>
      write loc from to val released (Ordering.join ord0 ord)
    | update loc tsr tsw valr valw releasedr releasedw ordr ordw =>
      update loc tsr tsw valr valw releasedr releasedw (Ordering.join ord0 ordr) (Ordering.join ord0 ordw)
    | fence ordr ordw =>
      fence (Ordering.join ord0 ordr) (Ordering.join ord0 ordw)
    | syscall e =>
      syscall e
    end.

  Lemma lift_plain e:
    lift Ordering.plain e = e.
  Proof. destruct e; ss. Qed.

End ThreadEvent.

Module Local.
  Structure t := mk {
    tview: TView.t;
    promises: Memory.t;
  }.

  Definition init := mk TView.bot Memory.bot.

  Inductive is_terminal (lc:t): Prop :=
  | is_terminal_intro
      (PROMISES: lc.(promises) = Memory.bot)
  .
  Hint Constructors is_terminal.

  Inductive wf (lc:t) (mem:Memory.t): Prop :=
  | wf_intro
      (TVIEW_WF: TView.wf lc.(tview))
      (TVIEW_CLOSED: TView.closed lc.(tview) mem)
      (PROMISES: Memory.le lc.(promises) mem)
  .
  Hint Constructors wf.

  Lemma cap_wf
        lc promises mem1 mem2
        (CAP: Memory.cap promises mem1 mem2)
        (WF: wf lc mem1):
    wf lc mem2.
  Proof.
    inv WF. econs; eauto.
    - eapply TView.cap_closed; eauto.
    - eapply Memory.cap_le; eauto.
  Qed.

  Inductive disjoint (lc1 lc2:t): Prop :=
  | disjoint_intro
      (DISJOINT: Memory.disjoint lc1.(promises) lc2.(promises))
  .
  Hint Constructors disjoint.

  Global Program Instance disjoint_Symmetric: Symmetric disjoint.
  Next Obligation.
    econs. symmetry. apply H.
  Qed.

  Inductive promise_step (lc1:t) (mem1:Memory.t) (loc:Loc.t) (from to:Time.t) (msg:Message.t) (lc2:t) (mem2:Memory.t) (kind:Memory.op_kind): Prop :=
  | promise_step_intro
      promises2
      (PROMISE: Memory.promise lc1.(promises) mem1 loc from to msg promises2 mem2 kind)
      (CLOSED: Memory.closed_message msg mem2)
      (LC2: lc2 = mk lc1.(tview) promises2):
      promise_step lc1 mem1 loc from to msg lc2 mem2 kind
  .
  Hint Constructors promise_step.

  Inductive read_step (lc1:t) (mem1:Memory.t) (loc:Loc.t) (to:Time.t) (val:Const.t) (released:option View.t) (ord:Ordering.t) (lc2:t): Prop :=
  | read_step_intro
      from
      tview2
      (GET: Memory.get loc to mem1 = Some (from, Message.full val released))
      (READABLE: TView.readable lc1.(tview).(TView.cur) loc to released ord)
      (TVIEW: TView.read_tview lc1.(tview) loc to released ord = tview2)
      (LC2: lc2 = mk tview2 lc1.(promises)):
      read_step lc1 mem1 loc to val released ord lc2
  .
  Hint Constructors read_step.

  Inductive write_step (lc1:t) (sc1:TimeMap.t) (mem1:Memory.t) (loc:Loc.t) (from to:Time.t) (val:Const.t) (releasedm released:option View.t) (ord:Ordering.t) (lc2:t) (sc2:TimeMap.t) (mem2:Memory.t) (kind:Memory.op_kind): Prop :=
  | write_step_intro
      promises2
      (RELEASED: released = TView.write_released lc1.(tview) sc1 loc to releasedm ord)
      (WRITABLE: TView.writable lc1.(tview).(TView.cur) sc1 loc to ord)
      (WRITE: Memory.write lc1.(promises) mem1 loc from to val released promises2 mem2 kind)
      (RELEASE: Ordering.le Ordering.strong_relaxed ord -> Memory.nonsynch_loc loc lc1.(promises))
      (LC2: lc2 = mk (TView.write_tview lc1.(tview) sc1 loc to ord) promises2)
      (SC2: sc2 = sc1):
      write_step lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind
  .
  Hint Constructors write_step.

  Inductive fence_step (lc1:t) (sc1:TimeMap.t) (ordr ordw:Ordering.t) (lc2:t) (sc2:TimeMap.t): Prop :=
  | fence_step_intro
      tview2
      (READ: TView.read_fence_tview lc1.(tview) ordr = tview2)
      (RELEASE: Ordering.le Ordering.strong_relaxed ordw -> Memory.nonsynch lc1.(promises))
      (LC2: lc2 = mk (TView.write_fence_tview tview2 sc1 ordw) lc1.(promises))
      (SC2: sc2 = TView.write_fence_sc tview2 sc1 ordw):
      fence_step lc1 sc1 ordr ordw lc2 sc2
  .
  Hint Constructors fence_step.

  Inductive program_step: forall (e:ThreadEvent.t) lc1 sc1 mem1 lc2 sc2 mem2, Prop :=
  | step_silent
      lc1 sc1 mem1:
      program_step ThreadEvent.silent lc1 sc1 mem1 lc1 sc1 mem1
  | step_read
      lc1 sc1 mem1
      loc ts val released ord lc2
      (LOCAL: Local.read_step lc1 mem1 loc ts val released ord lc2):
      program_step (ThreadEvent.read loc ts val released ord) lc1 sc1 mem1 lc2 sc1 mem1
  | step_write
      lc1 sc1 mem1
      loc from to val released ord lc2 sc2 mem2 kind
      (LOCAL: Local.write_step lc1 sc1 mem1 loc from to val None released ord lc2 sc2 mem2 kind):
      program_step (ThreadEvent.write loc from to val released ord) lc1 sc1 mem1 lc2 sc2 mem2
  | step_update
      lc1 sc1 mem1
      loc ordr ordw
      tsr valr releasedr releasedw lc2
      tsw valw lc3 sc3 mem3 kind
      (LOCAL1: Local.read_step lc1 mem1 loc tsr valr releasedr ordr lc2)
      (LOCAL2: Local.write_step lc2 sc1 mem1 loc tsr tsw valw releasedr releasedw ordw lc3 sc3 mem3 kind):
      program_step (ThreadEvent.update loc tsr tsw valr valw releasedr releasedw ordr ordw) lc1 sc1 mem1 lc3 sc3 mem3
  | step_fence
      lc1 sc1 mem1
      ordr ordw lc2 sc2
      (LOCAL: Local.fence_step lc1 sc1 ordr ordw lc2 sc2):
      program_step (ThreadEvent.fence ordr ordw) lc1 sc1 mem1 lc2 sc2 mem1
  | step_syscall
      lc1 sc1 mem1
      e lc2 sc2
      (LOCAL: Local.fence_step lc1 sc1 Ordering.seqcst Ordering.seqcst lc2 sc2):
      program_step (ThreadEvent.syscall e) lc1 sc1 mem1 lc2 sc2 mem1
  .
  Hint Constructors program_step.


  (* step_future *)

  Lemma promise_step_future
        lc1 sc1 mem1 loc from to msg lc2 mem2 kind
        (STEP: promise_step lc1 mem1 loc from to msg lc2 mem2 kind)
        (WF1: wf lc1 mem1)
        (SC1: Memory.closed_timemap sc1 mem1)
        (CLOSED1: Memory.closed mem1):
    <<WF2: wf lc2 mem2>> /\
    <<SC2: Memory.closed_timemap sc1 mem2>> /\
    <<CLOSED2: Memory.closed mem2>> /\
    <<FUTURE: Memory.future mem1 mem2>> /\
    <<TVIEW_FUTURE: TView.le lc1.(tview) lc2.(tview)>> /\
    <<MSG_WF: Message.wf msg>> /\
    <<MSG_TS: Memory.message_to msg loc to>> /\
    <<MSG_CLOSED: Memory.closed_message msg mem2>>.
  Proof.
    inv WF1. inv STEP.
    exploit Memory.promise_future; eauto. i. des.
    splits; ss.
    - econs; ss. eapply TView.future_closed; eauto.
    - eapply Memory.future_closed_timemap; eauto.
    - refl.
    - inv PROMISE.
      + inv PROMISES0. inv ADD. auto.
      + inv PROMISES0. inv SPLIT. auto.
      + inv PROMISES0. inv LOWER. auto.
    - by inv PROMISE.
  Qed.

  Lemma read_step_future
        lc1 mem1 loc ts val released ord lc2
        (STEP: read_step lc1 mem1 loc ts val released ord lc2)
        (WF1: wf lc1 mem1)
        (CLOSED1: Memory.closed mem1):
    <<WF2: wf lc2 mem1>> /\
    <<TVIEW_FUTURE: TView.le lc1.(tview) lc2.(tview)>> /\
    <<REL_WF: View.opt_wf released>> /\
    <<REL_CLOSED: Memory.closed_opt_view released mem1>>.
  Proof.
    inv WF1. inv STEP.
    dup CLOSED1. inv CLOSED0. exploit CLOSED; eauto. i. des.
    inv MSG_WF. inv MSG_CLOSED.
    exploit TViewFacts.read_future; try exact GET; eauto.
    i. des. splits; auto.
    - econs; eauto.
    - apply TViewFacts.read_tview_incr.
  Qed.

  Lemma write_step_future
        lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind
        (STEP: write_step lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind)
        (REL_WF: View.opt_wf releasedm)
        (REL_CLOSED: Memory.closed_opt_view releasedm mem1)
        (WF1: wf lc1 mem1)
        (SC1: Memory.closed_timemap sc1 mem1)
        (CLOSED1: Memory.closed mem1):
    <<WF2: wf lc2 mem2>> /\
    <<SC2: Memory.closed_timemap sc2 mem2>> /\
    <<CLOSED2: Memory.closed mem2>> /\
    <<TVIEW_FUTURE: TView.le lc1.(tview) lc2.(tview)>> /\
    <<SC_FUTURE: TimeMap.le sc1 sc2>> /\
    <<MEM_FUTURE: Memory.future mem1 mem2>> /\
    <<REL_WF: View.opt_wf released>> /\
    <<REL_TS: Time.le (released.(View.unwrap).(View.rlx) loc) to>> /\
    <<REL_CLOSED: Memory.closed_opt_view released mem2>>.
  Proof.
    inv WF1. inv STEP.
    exploit TViewFacts.write_future; eauto.
    { inv WRITE. eapply Memory.promise_op. eauto. }
    s. i. des.
    exploit Memory.write_future; try apply WRITE; eauto. i. des.
    exploit Memory.write_get2; try apply WRITE; eauto; try by viewtac. i. des.
    splits; eauto.
    - apply TViewFacts.write_tview_incr. auto.
    - refl.
    - inv WRITE. inv PROMISE; try inv TS; auto.
  Qed.

  Lemma write_step_strong_relaxed
        lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind
        (STEP: write_step lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind)
        (ORD: Ordering.le Ordering.strong_relaxed ord):
    negb (Memory.op_kind_is_lower kind) \/ (Memory.op_kind_is_lower_half kind).
  Proof.
    destruct kind; eauto.
    inv STEP. specialize (RELEASE ORD).
    inv WRITE. inv PROMISE.
    exploit Memory.lower_get0; try exact PROMISES; eauto. i. des.
    exploit RELEASE; eauto. inv MSG_LE; eauto; i.
    subst. inv RELEASED.
    revert H0. unfold TView.write_released. condtac; ss. by destruct ord.
  Qed.

  Lemma fence_step_future
        lc1 sc1 mem1 ordr ordw lc2 sc2
        (STEP: fence_step lc1 sc1 ordr ordw lc2 sc2)
        (WF1: wf lc1 mem1)
        (SC1: Memory.closed_timemap sc1 mem1)
        (CLOSED1: Memory.closed mem1):
    <<WF2: wf lc2 mem1>> /\
    <<SC2: Memory.closed_timemap sc2 mem1>> /\
    <<TVIEW_FUTURE: TView.le lc1.(tview) lc2.(tview)>> /\
    <<SC_FUTURE: TimeMap.le sc1 sc2>>.
  Proof.
    inv WF1. inv STEP.
    exploit TViewFacts.read_fence_future; eauto. i. des.
    exploit TViewFacts.write_fence_future; eauto. i. des.
    splits; eauto.
    - etrans.
      + apply TViewFacts.write_fence_tview_incr. auto.
      + apply TViewFacts.write_fence_tview_mon; eauto; try refl.
        apply TViewFacts.read_fence_tview_incr. auto.
    - apply TViewFacts.write_fence_sc_incr.
  Qed.

  Lemma program_step_future
        e lc1 sc1 mem1 lc2 sc2 mem2
        (STEP: program_step e lc1 sc1 mem1 lc2 sc2 mem2)
        (WF1: wf lc1 mem1)
        (SC1: Memory.closed_timemap sc1 mem1)
        (CLOSED1: Memory.closed mem1):
    <<WF2: wf lc2 mem2>> /\
    <<SC2: Memory.closed_timemap sc2 mem2>> /\
    <<CLOSED2: Memory.closed mem2>> /\
    <<TVIEW_FUTURE: TView.le lc1.(tview) lc2.(tview)>> /\
    <<SC_FUTURE: TimeMap.le sc1 sc2>> /\
    <<MEM_FUTURE: Memory.future mem1 mem2>>.
  Proof.
    inv STEP.
    - esplits; eauto; try refl.
    - exploit read_step_future; eauto. i. des.
      esplits; eauto; try refl.
    - exploit write_step_future; eauto; try by econs. i. des.
      esplits; eauto; try refl.
    - exploit read_step_future; eauto. i. des.
      exploit write_step_future; eauto; try by econs. i. des.
      esplits; eauto. etrans; eauto.
    - exploit fence_step_future; eauto. i. des. esplits; eauto; try refl.
    - exploit fence_step_future; eauto. i. des. esplits; eauto; try refl.
  Qed.


  (* step_disjoint *)

  Lemma promise_step_disjoint
        lc1 sc1 mem1 loc from to msg lc2 mem2 lc kind
        (STEP: promise_step lc1 mem1 loc from to msg lc2 mem2 kind)
        (WF1: wf lc1 mem1)
        (SC1: Memory.closed_timemap sc1 mem1)
        (CLOSED1: Memory.closed mem1)
        (DISJOINT1: disjoint lc1 lc)
        (WF: wf lc mem1):
    <<DISJOINT2: disjoint lc2 lc>> /\
    <<WF: wf lc mem2>>.
  Proof.
    inv WF1. inv DISJOINT1. inversion WF. inv STEP.
    exploit Memory.promise_future; try apply PROMISE; eauto. i. des.
    exploit Memory.promise_disjoint; try apply PROMISE; eauto. i. des.
    splits; ss. econs; eauto.
    eapply TView.future_closed; eauto.
  Qed.

  Lemma read_step_disjoint
        lc1 mem1 lc2 loc ts val released ord lc
        (STEP: read_step lc1 mem1 loc ts val released ord lc2)
        (WF1: wf lc1 mem1)
        (DISJOINT1: disjoint lc1 lc)
        (WF: wf lc mem1):
    disjoint lc2 lc.
  Proof.
    inv WF1. inv DISJOINT1. inv WF. inv STEP. ss.
  Qed.

  Lemma write_step_disjoint
        lc1 sc1 mem1 lc2 sc2 loc from to val releasedm released ord mem2 kind lc
        (STEP: write_step lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind)
        (WF1: wf lc1 mem1)
        (SC1: Memory.closed_timemap sc1 mem1)
        (CLOSED1: Memory.closed mem1)
        (DISJOINT1: disjoint lc1 lc)
        (WF: wf lc mem1):
    <<DISJOINT2: disjoint lc2 lc>> /\
    <<WF: wf lc mem2>>.
  Proof.
    inv WF1. inv DISJOINT1. inversion WF. inv STEP.
    exploit Memory.write_future0; try apply WRITE; eauto; try by viewtac. i. des.
    exploit Memory.write_disjoint; try apply WRITE; eauto. i. des.
    splits; ss. econs; eauto.
    inv WRITE. eapply TView.promise_closed; eauto.
  Qed.

  Lemma fence_step_disjoint
        lc1 sc1 mem1 lc2 sc2 ordr ordw lc
        (STEP: fence_step lc1 sc1 ordr ordw lc2 sc2)
        (WF1: wf lc1 mem1)
        (SC1: Memory.closed_timemap sc1 mem1)
        (DISJOINT1: disjoint lc1 lc)
        (WF: wf lc mem1):
    <<DISJOINT2: disjoint lc2 lc>> /\
    <<WF: wf lc mem1>>.
  Proof.
    inv WF1. inv DISJOINT1. inv WF. inv STEP. splits; ss.
  Qed.

  Lemma read_step_promises
        lc1 mem loc to val released ord lc2
        (READ: read_step lc1 mem loc to val released ord lc2):
    lc1.(promises) = lc2.(promises).
  Proof.
    inv READ. auto.
  Qed.

  Lemma program_step_disjoint
        e lc1 sc1 mem1 lc2 sc2 mem2 lc
        (STEP: program_step e lc1 sc1 mem1 lc2 sc2 mem2)
        (WF1: wf lc1 mem1)
        (SC1: Memory.closed_timemap sc1 mem1)
        (CLOSED1: Memory.closed mem1)
        (DISJOINT1: disjoint lc1 lc)
        (WF: wf lc mem1):
    <<DISJOINT2: disjoint lc2 lc>> /\
    <<WF: wf lc mem2>>.
  Proof.
    inv STEP.
    - esplits; eauto.
    - exploit read_step_disjoint; eauto.
    - exploit write_step_disjoint; eauto.
    - exploit read_step_future; eauto. i. des.
      exploit read_step_disjoint; eauto. i. des.
      exploit write_step_disjoint; eauto.
    - exploit fence_step_disjoint; eauto.
    - exploit fence_step_disjoint; eauto.
  Qed.


  (* step_no_half_except *)

  Lemma promise_step_no_half_except
        lc1 mem1 loc from to msg lc2 mem2 kind
        (STEP: promise_step lc1 mem1 loc from to msg lc2 mem2 kind)
        (NOHALF1: Memory.no_half_except lc1.(promises) mem1):
    Memory.no_half_except lc2.(promises) mem2.
  Proof.
    ii. inv STEP. s.
    eapply Memory.promise_no_half_except; eauto.
  Qed.

  Lemma program_step_no_half_except
        e lc1 sc1 mem1 lc2 sc2 mem2
        (STEP: program_step e lc1 sc1 mem1 lc2 sc2 mem2)
        (NOHALF1: Memory.no_half_except lc1.(promises) mem1):
    Memory.no_half_except lc2.(promises) mem2.
  Proof.
    ii. inv STEP; try inv LOCAL; eauto; ss.
    - inv WRITE.
      erewrite Memory.remove_o; eauto. condtac; ss.
      + des. subst.
        exploit Memory.promise_get0; eauto. i. des. congr.
      + eapply Memory.promise_no_half_except; eauto.
    - inv LOCAL1. inv LOCAL2. inv WRITE. ss.
      erewrite Memory.remove_o; eauto. condtac; ss.
      + des. subst.
        exploit Memory.promise_get0; eauto. i. des. congr.
      + eapply Memory.promise_no_half_except; eauto.
  Qed.
End Local.
