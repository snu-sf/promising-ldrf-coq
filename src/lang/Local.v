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
  | failure
  | racy_read (loc:Loc.t) (val:Const.t) (ord:Ordering.t)
  | racy_write (loc:Loc.t) (val:Const.t) (ord:Ordering.t)
  | racy_update (loc:Loc.t) (valr valw:Const.t) (ordr ordw:Ordering.t)
  .
  Hint Constructors t.

  Definition get_event (e:t): option Event.t :=
    match e with
    | syscall e => Some e
    | _ => None
    end.

  Definition get_program_event (e:t): ProgramEvent.t :=
    match e with
    | promise _ _ _ _ _  => ProgramEvent.silent
    | silent => ProgramEvent.silent
    | read loc _ val _ ord => ProgramEvent.read loc val ord
    | write loc _ _ val _ ord => ProgramEvent.write loc val ord
    | update loc _ _ valr valw _ _ ordr ordw => ProgramEvent.update loc valr valw ordr ordw
    | fence ordr ordw => ProgramEvent.fence ordr ordw
    | syscall ev => ProgramEvent.syscall ev
    | failure => ProgramEvent.failure
    | racy_read loc val ord => ProgramEvent.read loc val ord
    | racy_write loc val ord => ProgramEvent.write loc val ord
    | racy_update loc valr valw ordr ordw => ProgramEvent.update loc valr valw ordr ordw
    end.

  Definition get_machine_event (e: t): MachineEvent.t :=
    match e with
    | syscall e => MachineEvent.syscall e
    | failure
    | racy_write _ _ _
    | racy_update _ _ _ _ _ => MachineEvent.failure
    | _ => MachineEvent.silent
    end.

  Definition is_promising (e:t) : option (Loc.t * Time.t) :=
    match e with
    | promise loc from to msg kind => Some (loc, to)
    | _ => None
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

  Definition is_accessing_loc (l: Loc.t) (e: t): Prop :=
    match e with
    | read loc _ _ _ _
    | write loc _ _ _ _ _
    | update loc _ _ _ _ _ _ _ _
    | racy_read loc _ _
    | racy_write loc _ _
    | racy_update loc _ _ _ _ => loc = l
    | _ => False
    end.

  Lemma eq_program_event_eq_loc
        e1 e2 loc
        (EVENT: get_program_event e1 = get_program_event e2):
    is_accessing_loc loc e1 <-> is_accessing_loc loc e2.
  Proof.
    unfold is_accessing_loc.
    destruct e1, e2; ss; inv EVENT; ss.
  Qed.

  Definition is_cancel (e: t) : Prop :=
    match e with
    | promise _ _ _ Message.reserve Memory.op_kind_cancel => True
    | _ => False
    end.

  Definition is_reserve (te: t): Prop :=
    match te with
    | promise _ _ _ Message.reserve Memory.op_kind_add => True
    | _ => False
    end.

  Definition is_reservation_event (te: t): Prop :=
    match te with
    | promise _ _ _ Message.reserve _ => True
    | _ => False
    end.

  Definition is_normal (te: t) :=
    ~ is_reservation_event te.

  Lemma is_normal_dec (e: ThreadEvent.t):
    { is_normal e } + { ~ is_normal e }.
  Proof.
    unfold is_normal, is_reservation_event, is_cancel, is_reserve.
    des_ifs; ss; (try by (left; ii; des; ss)); try by (right; ii; eauto).
  Defined.

  Lemma reservation_event_silent te
        (RESERVING: is_reservation_event te)
    :
      get_machine_event te = MachineEvent.silent.
  Proof.
    unfold is_reservation_event, is_cancel, is_reserve in *.
    des; des_ifs.
  Qed.
End ThreadEvent.

Module Local.
  Structure t := mk {
    tview: TView.t;
    promises: Memory.t;
  }.

  Definition init := mk TView.bot Memory.bot.

  Inductive is_terminal (lc:t): Prop :=
  | is_terminal_intro
      (PROMISES: (promises lc) = Memory.bot)
  .
  Hint Constructors is_terminal.

  Inductive wf (lc:t) (mem:Memory.t): Prop :=
  | wf_intro
      (TVIEW_WF: TView.wf (tview lc))
      (TVIEW_CLOSED: TView.closed (tview lc) mem)
      (PROMISES: Memory.le (promises lc) mem)
      (FINITE: Memory.finite (promises lc))
      (BOT: Memory.bot_none (promises lc))
  .
  Hint Constructors wf.

  Lemma cap_wf
        lc mem1 mem2
        (CAP: Memory.cap mem1 mem2)
        (WF: wf lc mem1):
    wf lc mem2.
  Proof.
    inv WF. econs; eauto.
    - eapply TView.cap_closed; eauto.
    - eapply Memory.cap_le; eauto.
  Qed.

  Inductive disjoint (lc1 lc2:t): Prop :=
  | disjoint_intro
      (DISJOINT: Memory.disjoint (promises lc1) (promises lc2))
  .
  Hint Constructors disjoint.

  Global Program Instance disjoint_Symmetric: Symmetric disjoint.
  Next Obligation.
    econs. symmetry. apply H.
  Qed.

  Definition promise_consistent (lc:t): Prop :=
    forall loc ts from msg
      (PROMISE: Memory.get loc ts (promises lc) = Some (from, msg))
      (MSG: msg <> Message.reserve),
      Time.lt (lc.(tview).(TView.cur).(View.rlx) loc) ts.

  Lemma bot_promise_consistent
        lc
        (PROMISES: (promises lc) = Memory.bot):
    promise_consistent lc.
  Proof.
    ii. rewrite PROMISES, Memory.bot_get in *. ss.
  Qed.

  Lemma terminal_promise_consistent
        lc
        (TERMINAL: is_terminal lc):
    promise_consistent lc.
  Proof.
    inv TERMINAL. apply bot_promise_consistent. auto.
  Qed.


  Inductive promise_step (lc1:t) (mem1:Memory.t) (loc:Loc.t) (from to:Time.t) (msg:Message.t) (lc2:t) (mem2:Memory.t) (kind:Memory.op_kind): Prop :=
  | promise_step_intro
      promises2
      (PROMISE: Memory.promise (promises lc1) mem1 loc from to msg promises2 mem2 kind)
      (CLOSED: Memory.closed_message msg mem2)
      (LC2: lc2 = mk (tview lc1) promises2):
      promise_step lc1 mem1 loc from to msg lc2 mem2 kind
  .
  Hint Constructors promise_step.

  Inductive read_step (lc1:t) (mem1:Memory.t) (loc:Loc.t) (to:Time.t) (val:Const.t) (released:option View.t) (ord:Ordering.t) (lc2:t): Prop :=
  | read_step_intro
      from
      tview2
      (GET: Memory.get loc to mem1 = Some (from, Message.concrete val released))
      (READABLE: TView.readable (TView.cur (tview lc1)) loc to released ord)
      (TVIEW: TView.read_tview (tview lc1) loc to released ord = tview2)
      (LC2: lc2 = mk tview2 (promises lc1)):
      read_step lc1 mem1 loc to val released ord lc2
  .
  Hint Constructors read_step.

  Inductive write_step (lc1:t) (sc1:TimeMap.t) (mem1:Memory.t)
                       (loc:Loc.t) (from to:Time.t)
                       (val:Const.t) (releasedm released:option View.t) (ord:Ordering.t)
                       (lc2:t) (sc2:TimeMap.t) (mem2:Memory.t) (kind:Memory.op_kind): Prop :=
  | write_step_intro
      promises2
      (RELEASED: released = TView.write_released (tview lc1) sc1 loc to releasedm ord)
      (WRITABLE: TView.writable (TView.cur (tview lc1)) sc1 loc to ord)
      (WRITE: Memory.write (promises lc1) mem1 loc from to (Message.concrete val released) promises2 mem2 kind)
      (RELEASE: Ordering.le Ordering.strong_relaxed ord -> Memory.nonsynch_loc loc (promises lc1))
      (LC2: lc2 = mk (TView.write_tview (tview lc1) sc1 loc to ord) promises2)
      (SC2: sc2 = sc1):
      write_step lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind
  .
  Hint Constructors write_step.

  Inductive write_undef_step (lc1:t) (sc1:TimeMap.t) (mem1:Memory.t)
                             (loc:Loc.t) (from to:Time.t) (ord:Ordering.t)
                             (lc2:t) (sc2:TimeMap.t) (mem2:Memory.t) (kind:Memory.op_kind): Prop :=
  | write_undef_step_intro
      promises2
      (NA: Ordering.le ord Ordering.na)
      (WRITABLE: TView.writable lc1.(tview).(TView.cur) sc1 loc to ord)
      (WRITE: Memory.write lc1.(promises) mem1 loc from to Message.undef promises2 mem2 kind)
      (LC2: lc2 = mk lc1.(tview) promises2)
      (SC2: sc2 = sc1):
      write_undef_step lc1 sc1 mem1 loc from to ord lc2 sc2 mem2 kind
  .
  Hint Constructors write_undef_step.

  Inductive fence_step (lc1:t) (sc1:TimeMap.t) (ordr ordw:Ordering.t) (lc2:t) (sc2:TimeMap.t): Prop :=
  | fence_step_intro
      tview2
      (READ: TView.read_fence_tview (tview lc1) ordr = tview2)
      (RELEASE: Ordering.le Ordering.strong_relaxed ordw -> Memory.nonsynch (promises lc1))
      (LC2: lc2 = mk (TView.write_fence_tview tview2 sc1 ordw) (promises lc1))
      (SC2: sc2 = TView.write_fence_sc tview2 sc1 ordw)
      (PROMISES: ordw = Ordering.seqcst -> (Local.promises lc1) = Memory.bot):
      fence_step lc1 sc1 ordr ordw lc2 sc2
  .
  Hint Constructors fence_step.

  Inductive failure_step (lc1:t): Prop :=
  | failure_step_intro
      (CONSISTENT: promise_consistent lc1)
  .
  Hint Constructors failure_step.

  Inductive racy_read_step (lc1:t) (mem1:Memory.t) (loc:Loc.t) (val:Const.t) (ord:Ordering.t): Prop :=
  | racy_read_step_intro
      from to msg
      (GET: Memory.get loc to mem1 = Some (from, msg))
      (GETP: Memory.get loc to lc1.(promises) = None)
      (RACE: TView.racy_readable lc1.(tview).(TView.cur) loc to ord)
      (MSG1: msg <> Message.reserve)
      (MSG2: Ordering.le Ordering.plain ord -> msg = Message.undef)
  .
  Hint Constructors racy_read_step.

  Inductive racy_write_step (lc1:t) (mem1:Memory.t) (loc:Loc.t) (ord:Ordering.t): Prop :=
  | racy_write_step_intro
      from to msg
      (GET: Memory.get loc to mem1 = Some (from, msg))
      (GETP: Memory.get loc to lc1.(promises) = None)
      (RACE: TView.racy_writable lc1.(tview).(TView.cur) loc to)
      (MSG1: msg <> Message.reserve)
      (MSG2: Ordering.le Ordering.plain ord -> msg = Message.undef)
      (CONSISTENT: promise_consistent lc1)
  .
  Hint Constructors racy_write_step.

  Inductive racy_update_step (lc1:t) (mem1:Memory.t) (loc:Loc.t) (ordr ordw:Ordering.t): Prop :=
  | racy_update_step_ordr
      (ORDR: Ordering.le ordr Ordering.na)
      (CONSISTENT: promise_consistent lc1)
  | racy_update_step_ordw
      (ORDW: Ordering.le ordw Ordering.na)
      (CONSISTENT: promise_consistent lc1)
  | racy_update_step_intro
      from to msg
      (GET: Memory.get loc to mem1 = Some (from, msg))
      (GETP: Memory.get loc to lc1.(promises) = None)
      (RACE: TView.racy_writable lc1.(tview).(TView.cur) loc to)
      (MSG: msg = Message.undef)
      (CONSISTENT: promise_consistent lc1)
  .
  Hint Constructors racy_update_step.


  Inductive program_step:
    forall (e:ThreadEvent.t) (lc1:t) (sc1:TimeMap.t) (mem1:Memory.t) (lc2:t) (sc2:TimeMap.t) (mem2:Memory.t), Prop :=
  | step_silent
      lc1 sc1 mem1:
      program_step ThreadEvent.silent lc1 sc1 mem1 lc1 sc1 mem1
  | step_read
      lc1 sc1 mem1
      loc ts val released ord lc2
      (LOCAL: read_step lc1 mem1 loc ts val released ord lc2):
      program_step (ThreadEvent.read loc ts val released ord) lc1 sc1 mem1 lc2 sc1 mem1
  | step_write
      lc1 sc1 mem1
      loc from to val released ord lc2 sc2 mem2 kind
      (LOCAL: write_step lc1 sc1 mem1 loc from to val None released ord lc2 sc2 mem2 kind):
      program_step (ThreadEvent.write loc from to val released ord) lc1 sc1 mem1 lc2 sc2 mem2
  | step_update
      lc1 sc1 mem1
      loc ordr ordw
      tsr valr releasedr releasedw lc2
      tsw valw lc3 sc3 mem3 kind
      (LOCAL1: read_step lc1 mem1 loc tsr valr releasedr ordr lc2)
      (LOCAL2: write_step lc2 sc1 mem1 loc tsr tsw valw releasedr releasedw ordw lc3 sc3 mem3 kind):
      program_step (ThreadEvent.update loc tsr tsw valr valw releasedr releasedw ordr ordw)
                   lc1 sc1 mem1 lc3 sc3 mem3
  | step_fence
      lc1 sc1 mem1
      ordr ordw lc2 sc2
      (LOCAL: fence_step lc1 sc1 ordr ordw lc2 sc2):
      program_step (ThreadEvent.fence ordr ordw) lc1 sc1 mem1 lc2 sc2 mem1
  | step_syscall
      lc1 sc1 mem1
      e lc2 sc2
      (LOCAL: fence_step lc1 sc1 Ordering.seqcst Ordering.seqcst lc2 sc2):
      program_step (ThreadEvent.syscall e) lc1 sc1 mem1 lc2 sc2 mem1
  | step_failure
      lc1 sc1 mem1
      (LOCAL: failure_step lc1):
      program_step ThreadEvent.failure lc1 sc1 mem1 lc1 sc1 mem1
  | step_na_write
      loc ord val released
      lc1 sc1 mem1
      from1 to1 kind1
      lc2 sc2 mem2
      from2 to2 kind2
      lc3 sc3 mem3
      (LT: Time.lt to1 to2)
      (LOCAL1: write_undef_step lc1 sc1 mem1 loc from1 to1 ord lc2 sc2 mem2 kind1)
      (LOCAL2: write_step lc2 sc2 mem2 loc from2 to2 val None released ord lc3 sc3 mem3 kind2):
      program_step (ThreadEvent.write loc from2 to2 val released ord) lc1 sc1 mem1 lc3 sc3 mem3
  | step_racy_read
      lc1 sc1 mem1
      loc val ord
      (LOCAL: racy_read_step lc1 mem1 loc val ord):
      program_step (ThreadEvent.racy_read loc val ord) lc1 sc1 mem1 lc1 sc1 mem1
  | step_racy_write
      lc1 sc1 mem1
      loc val ord
      (LOCAL: racy_write_step lc1 mem1 loc ord):
      program_step (ThreadEvent.racy_write loc val ord) lc1 sc1 mem1 lc1 sc1 mem1
  | step_racy_update
      lc1 sc1 mem1
      loc valr valw ordr ordw
      (LOCAL: racy_update_step lc1 mem1 loc ordr ordw):
      program_step (ThreadEvent.racy_update loc valr valw ordr ordw) lc1 sc1 mem1 lc1 sc1 mem1
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
    <<TVIEW_FUTURE: TView.le (tview lc1) (tview lc2)>> /\
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
      + econs.
    - by inv PROMISE.
  Qed.

  Lemma read_step_future
        lc1 mem1 loc ts val released ord lc2
        (STEP: read_step lc1 mem1 loc ts val released ord lc2)
        (WF1: wf lc1 mem1)
        (CLOSED1: Memory.closed mem1):
    <<WF2: wf lc2 mem1>> /\
    <<TVIEW_FUTURE: TView.le (tview lc1) (tview lc2)>> /\
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
    <<TVIEW_FUTURE: TView.le (tview lc1) (tview lc2)>> /\
    <<SC_FUTURE: TimeMap.le sc1 sc2>> /\
    <<MEM_FUTURE: Memory.future mem1 mem2>> /\
    <<REL_WF: View.opt_wf released>> /\
    <<REL_TS: Time.le ((View.rlx (View.unwrap released)) loc) to>> /\
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
    - inv WRITE. inv PROMISE; try inv TS; ss.
  Qed.

  Lemma write_undef_step_future
        lc1 sc1 mem1 loc from to ord lc2 sc2 mem2 kind
        (STEP: write_undef_step lc1 sc1 mem1 loc from to ord lc2 sc2 mem2 kind)
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
    inv WF1. inv STEP.
    exploit Memory.write_future; try apply WRITE; eauto. i. des.
    splits; eauto; try refl.
    - econs; ss. inv TVIEW_CLOSED.
      econs; eauto using Memory.future_closed_view.
    - eauto using Memory.future_closed_timemap.
  Qed.

  Lemma write_step_non_cancel
        lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind
        (STEP: write_step lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind):
    negb (Memory.op_kind_is_cancel kind).
  Proof.
    inv STEP. inv WRITE. inv PROMISE; ss.
  Qed.

  Lemma write_step_strong_relaxed
        lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind
        (STEP: write_step lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind)
        (ORD: Ordering.le Ordering.strong_relaxed ord):
    negb (Memory.op_kind_is_lower kind).
  Proof.
    guardH ORD.
    inv STEP. inv WRITE. destruct kind; ss.
    inv PROMISE. des. subst.
    exploit Memory.lower_get0; try exact PROMISES. i. des.
    unguard. des.
    exploit RELEASE; eauto. inv MSG_LE; eauto. i. subst.
    inv RELEASED. revert H0.
    unfold TView.write_released. condtac; ss. destruct ord; ss.
  Qed.

  Lemma fence_step_future
        lc1 sc1 mem1 ordr ordw lc2 sc2
        (STEP: fence_step lc1 sc1 ordr ordw lc2 sc2)
        (WF1: wf lc1 mem1)
        (SC1: Memory.closed_timemap sc1 mem1)
        (CLOSED1: Memory.closed mem1):
    <<WF2: wf lc2 mem1>> /\
    <<SC2: Memory.closed_timemap sc2 mem1>> /\
    <<TVIEW_FUTURE: TView.le (tview lc1) (tview lc2)>> /\
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
    <<TVIEW_FUTURE: TView.le (tview lc1) (tview lc2)>> /\
    <<SC_FUTURE: TimeMap.le sc1 sc2>> /\
    <<MEM_FUTURE: Memory.future mem1 mem2>>.
  Proof.
    inv STEP; try by (esplits; eauto; try refl).
    - exploit read_step_future; eauto. i. des.
      esplits; eauto; try refl.
    - exploit write_step_future; eauto; try by econs. i. des.
      esplits; eauto; try refl.
    - exploit read_step_future; eauto. i. des.
      exploit write_step_future; eauto; try by econs. i. des.
      esplits; eauto. etrans; eauto.
    - exploit fence_step_future; eauto. i. des. esplits; eauto; try refl.
    - exploit fence_step_future; eauto. i. des. esplits; eauto; try refl.
    - exploit write_undef_step_future; eauto. i. des.
      exploit write_step_future; eauto. i. des.
      esplits; eauto; try refl; etrans; eauto.
  Qed.

  Lemma promise_step_inhabited
        lc1 mem1 loc from to msg lc2 mem2 kind
        (STEP: promise_step lc1 mem1 loc from to msg lc2 mem2 kind)
        (INHABITED1: Memory.inhabited mem1):
    <<INHABITED2: Memory.inhabited mem2>>.
  Proof.
    inv STEP. eauto using Memory.promise_inhabited.
  Qed.

  Lemma program_step_inhabited
        e lc1 sc1 mem1 lc2 sc2 mem2
        (STEP: program_step e lc1 sc1 mem1 lc2 sc2 mem2)
        (INHABITED1: Memory.inhabited mem1):
    <<INHABITED2: Memory.inhabited mem2>>.
  Proof.
    inv STEP; eauto.
    - inv LOCAL. eauto using Memory.write_inhabited.
    - inv LOCAL2. eauto using Memory.write_inhabited.
    - inv LOCAL1. inv LOCAL2. eauto using Memory.write_inhabited.
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
    exploit Memory.write_disjoint; try apply WRITE; eauto. i. des.
    splits; ss. econs; eauto.
    inv WRITE. eapply TView.promise_closed; eauto.
  Qed.

  Lemma write_undef_step_disjoint
        lc1 sc1 mem1 lc2 sc2 loc from to ord mem2 kind lc
        (STEP: write_undef_step lc1 sc1 mem1 loc from to ord lc2 sc2 mem2 kind)
        (WF1: wf lc1 mem1)
        (SC1: Memory.closed_timemap sc1 mem1)
        (CLOSED1: Memory.closed mem1)
        (DISJOINT1: disjoint lc1 lc)
        (WF: wf lc mem1):
    <<DISJOINT2: disjoint lc2 lc>> /\
    <<WF: wf lc mem2>>.
  Proof.
    inv WF1. inv DISJOINT1. inversion WF. inv STEP.
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
    (promises lc1) = (promises lc2).
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
    inv STEP; try by (esplits; eauto).
    - exploit read_step_disjoint; eauto.
    - exploit write_step_disjoint; eauto.
    - exploit read_step_future; eauto. i. des.
      exploit read_step_disjoint; eauto. i. des.
      exploit write_step_disjoint; eauto.
    - exploit fence_step_disjoint; eauto.
    - exploit fence_step_disjoint; eauto.
    - exploit write_undef_step_future; eauto. i. des.
      exploit write_undef_step_disjoint; eauto. i. des.
      exploit write_step_disjoint; eauto.
  Qed.

  Lemma program_step_promises_bot
        e lc1 sc1 mem1 lc2 sc2 mem2
        (STEP: program_step e lc1 sc1 mem1 lc2 sc2 mem2)
        (PROMISES: (promises lc1) = Memory.bot):
    (promises lc2) = Memory.bot.
  Proof.
    inv STEP; try inv LOCAL; ss.
    - eapply Memory.write_promises_bot; eauto.
    - inv LOCAL1. inv LOCAL2.
      eapply Memory.write_promises_bot; eauto.
    - inv LOCAL1. inv LOCAL2.
      do 2 (eapply Memory.write_promises_bot; eauto).
  Qed.

  Lemma program_step_get_diff_promises
        l
        e lc1 sc1 mem1 lc2 sc2 mem2
        (STEP: program_step e lc1 sc1 mem1 lc2 sc2 mem2)
        (LOC: ~ ThreadEvent.is_accessing_loc l e):
    forall to, Memory.get l to lc1.(promises) = Memory.get l to lc2.(promises).
  Proof.
    inv STEP; ss; try by inv LOCAL.
    - i. inv LOCAL. s.
      erewrite <- Memory.write_get_diff_promise; eauto.
    - i. inv LOCAL1. inv LOCAL2. s.
      erewrite <- Memory.write_get_diff_promise; eauto.
    - i. inv LOCAL1. inv LOCAL2. ss.
      erewrite <- Memory.write_get_diff_promise; try exact WRITE; eauto.
      erewrite <- Memory.write_get_diff_promise; eauto.
  Qed.

  Lemma program_step_get_diff
        l
        e lc1 sc1 mem1 lc2 sc2 mem2
        (STEP: program_step e lc1 sc1 mem1 lc2 sc2 mem2)
        (LOC: ~ ThreadEvent.is_accessing_loc l e):
    forall to, Memory.get l to mem1 = Memory.get l to mem2.
  Proof.
    inv STEP; ss; try by inv LOCAL.
    - i. inv LOCAL. s.
      erewrite <- Memory.write_get_diff; eauto.
    - i. inv LOCAL1. inv LOCAL2. s.
      erewrite <- Memory.write_get_diff; eauto.
    - i. inv LOCAL1. inv LOCAL2. ss.
      erewrite <- Memory.write_get_diff; try exact WRITE; eauto.
      erewrite <- Memory.write_get_diff; eauto.
  Qed.
End Local.
