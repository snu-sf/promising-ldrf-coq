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


Require Import MemoryProps.

Section SIM.

  Variable L: Loc.t -> bool.

  Definition in_L (loc: Loc.t) (ts: Time.t) := L loc.

  Inductive sim_memory_content P: option (Time.t * Message.t) -> option (Time.t * Message.t) -> Prop :=
  | sim_memory_content_none
      (NPROM: ~ P)
    :
      sim_memory_content P None None
  | sim_memory_content_normal
      from_src from_tgt msg_src msg_tgt
      (NPROM: ~ P)
      (FROM: Time.le from_tgt from_src)
      (MSG: Message.le msg_src msg_tgt)
      (RESERVE: msg_src = Message.reserve -> msg_tgt = Message.reserve)
    :
      sim_memory_content P (Some (from_src, msg_src)) (Some (from_tgt, msg_tgt))
  | sim_memory_content_forget
      from_src from_tgt msg
      (PROM: P)
      (FROM: Time.le from_tgt from_src)
    :
      sim_memory_content P (Some (from_src, Message.reserve)) (Some (from_tgt, msg))
  .
  Hint Constructors sim_memory_content.

  Definition sim_memory P mem_src mem_tgt : Prop :=
    forall loc ts,
      sim_memory_content (P loc ts) (Memory.get loc ts mem_src) (Memory.get loc ts mem_tgt).

  Definition all_pasts_memory (mem: Memory.t) (pasts: Loc.t -> Time.t -> option Memory.t): Prop :=
    forall loc from to val released
           (GET: Memory.get loc to mem = Some (from, Message.concrete val (Some released))),
    exists past,
      (<<PAST: pasts loc to = Some past>>) /\
      (<<GET: Memory.closed_view released past>>) /\
      (<<PREV: forall past' (PAST: pasts loc from = Some past'),
          Memory.future_weak past' past>>).

  Inductive wf_pasts_memory (mem: Memory.t) (pasts: Loc.t -> Time.t -> option Memory.t): Prop :=
  | wf_pasts_memory_intro
      (COMPLETE: all_pasts_memory mem pasts)
      (ONLY: forall loc ts past (PAST: pasts loc ts = Some past),
          (<<CONCRETE: concrete_promised mem loc ts>>) /\
          (<<CURR: Memory.future_weak past mem>>) /\
          (<<CLOSED: Memory.closed past>>)
      )
  .

  Definition pasts_le
             (pasts0: Loc.t -> Time.t -> option Memory.t)
             (pasts1: Loc.t -> Time.t -> option Memory.t): Prop :=
    forall loc to past (PAST0: pasts0 loc to = Some past), pasts1 loc to = Some past.

  Global Program Instance pasts_le_PreOrder: PreOrder pasts_le.
  Next Obligation.
  Proof. ii. auto. Qed.
  Next Obligation.
  Proof. ii. apply H0, H. auto. Qed.

  Record sim_timemap (past: Memory.t) (tm_src tm_tgt: TimeMap.t): Prop :=
    sim_timemap_intro
      {
        sim_timemap_le: TimeMap.le tm_src tm_tgt;
        sim_timemap_closed: Memory.closed_timemap tm_src past;
        sim_timemap_max: forall tm (CLOSED: Memory.closed_timemap tm past)
                                (TMLE: TimeMap.le tm tm_tgt)
          ,
            TimeMap.le tm tm_src;
      }.
  Hint Constructors sim_timemap.

  Lemma sim_timemap_exists past tm_tgt
        (CLOSED: Memory.closed past)
    :
      exists tm_src, <<SIM: sim_timemap past tm_src tm_tgt>>.
  Proof.
    exploit (@choice _ _ (fun loc ts_src =>
                            (<<GREATEST:
                               forall ts
                                      (PAST: concrete_promised past loc ts)
                                      (LE: Time.le ts (tm_tgt loc)),
                                 Time.le ts ts_src>>) /\
                            (<<CLOSED: concrete_promised past loc ts_src>>) /\
                            (<<TLE: Time.le ts_src (tm_tgt loc)>>))).
    - intros loc.
      hexploit (cell_elements_greatest (past loc) (fun ts => concrete_promised past loc ts /\ Time.le ts (tm_tgt loc))).
      i. des.
      + exists to. split; clarify. ii. splits; auto.
        i. dup PAST. inv PAST. exploit GREATEST; eauto.
      + exfalso. inv CLOSED. eapply EMPTY; eauto. split.
        { econs; eauto. }
        { eapply Time.bot_spec. }
    - intros [f FSPEC]. des. exists f. econs.
      + ii. specialize (FSPEC loc). des. auto.
      + ii. specialize (FSPEC loc). des. inv CLOSED0. esplits; eauto.
      + ii. specialize (FSPEC loc). des.
        specialize (CLOSED0 loc). des.
        exploit GREATEST.
        { econs; eauto. }
        { apply TMLE. }
        auto.
  Qed.

  Record sim_view (past: Memory.t) (view_src view_tgt: View.t): Prop :=
    sim_view_intro
      {
        sim_view_pln: sim_timemap past view_src.(View.pln) view_tgt.(View.pln);
        sim_view_rlx: sim_timemap past view_src.(View.rlx) view_tgt.(View.rlx);
      }
  .
  Hint Constructors sim_view.

  Lemma sim_view_le past vw_src vw_tgt
        (SIM: sim_view past vw_src vw_tgt)
    :
      View.le vw_src vw_tgt.
  Proof.
    inv SIM. econs.
    - eapply sim_timemap_le; eauto.
    - eapply sim_timemap_le; eauto.
  Qed.

  Lemma sim_view_exists past vw_tgt
        (CLOSED: Memory.closed past)
    :
      exists vw_src, <<SIM: sim_view past vw_src vw_tgt>>.
  Proof.
    exploit (@sim_timemap_exists past vw_tgt.(View.pln)); auto. i. des.
    exploit (@sim_timemap_exists past vw_tgt.(View.rlx)); auto. i. des.
    exists (View.mk tm_src tm_src0). econs; eauto.
  Qed.

  Lemma sim_view_closed past vw_src vw_tgt
        (SIM: sim_view past vw_src vw_tgt)
    :
      Memory.closed_view vw_src past.
  Proof.
    econs.
    - eapply sim_timemap_closed; eauto. eapply sim_view_pln; eauto.
    - eapply sim_timemap_closed; eauto. eapply sim_view_rlx; eauto.
  Qed.

  Lemma sim_view_max past vw_src vw_tgt vw
        (SIM: sim_view past vw_src vw_tgt)
        (VWLE: View.le vw vw_tgt)
        (CLOSED: Memory.closed_view vw past)
    :
      View.le vw vw_src.
  Proof.
    inv VWLE. inv CLOSED. econs.
    - eapply sim_timemap_max; eauto. eapply sim_view_pln; eauto.
    - eapply sim_timemap_max; eauto. eapply sim_view_rlx; eauto.
  Qed.

  Lemma sim_view_wf past vw_src vw_tgt
        (SIM: sim_view past vw_src vw_tgt)
        (WF: View.wf vw_tgt)
    :
      View.wf vw_src.
  Proof.
    inv WF. econs.
    eapply sim_timemap_max.
    - eapply sim_view_rlx; eauto.
    - eapply sim_timemap_closed. eapply sim_view_pln; eauto.
    - etrans; eauto. eapply sim_timemap_le. eapply sim_view_pln; eauto.
  Qed.

  Inductive sim_opt_view (past: Memory.t): forall (view_src view_tgt: option View.t), Prop :=
  | sim_opt_view_some
      view_src view_tgt
      (SIM: sim_view past view_src view_tgt):
      sim_opt_view past (Some view_src) (Some view_tgt)
  | sim_opt_view_none:
      sim_opt_view past None None
  .
  Hint Constructors sim_opt_view.

  Lemma sim_opt_view_le past vw_src vw_tgt
        (SIM: sim_opt_view past vw_src vw_tgt)
    :
      View.opt_le vw_src vw_tgt.
  Proof.
    inv SIM. econs; eauto.
    - eapply sim_view_le; eauto.
    - econs.
  Qed.

  Lemma sim_opt_view_exists past vw_tgt
        (CLOSED: Memory.closed past)
    :
      exists vw_src, <<SIM: sim_opt_view past vw_src vw_tgt>>.
  Proof.
    destruct vw_tgt.
    - exploit sim_view_exists; eauto. i. des.
      esplits. econs; eauto.
    - esplits; eauto.
  Qed.

  Lemma sim_opt_view_closed past vw_src vw_tgt
        (SIM: sim_opt_view past vw_src vw_tgt)
    :
      Memory.closed_opt_view vw_src past.
  Proof.
    inv SIM.
    - econs; eauto. eapply sim_view_closed; eauto.
    - econs; eauto.
  Qed.

  Lemma sim_opt_view_max past vw_src vw_tgt vw
        (SIM: sim_opt_view past vw_src vw_tgt)
        (VWLE: View.opt_le vw vw_tgt)
        (CLOSED: Memory.closed_opt_view vw past)
    :
      View.opt_le vw vw_src.
  Proof.
    inv VWLE; inv SIM; econs.
    inv CLOSED. eapply sim_view_max; eauto.
  Qed.

  Lemma sim_opt_view_wf past vw_src vw_tgt
        (SIM: sim_opt_view past vw_src vw_tgt)
        (WF: View.opt_wf vw_tgt)
    :
      View.opt_wf vw_src.
  Proof.
    inv WF; inv SIM; econs.
    eapply sim_view_wf; eauto.
  Qed.

  Inductive sim_message: forall (past: Memory.t) (msg_src msg_tgt: Message.t), Prop :=
  | sim_message_concrete
      past val released_src released_tgt
      (SIM: sim_opt_view past released_src released_tgt):
      sim_message past (Message.concrete val released_src) (Message.concrete val released_tgt)
  | sim_message_reserve
      past
    :
      sim_message past Message.reserve Message.reserve
  .
  Hint Constructors sim_message.

  Lemma sim_message_le past msg_src msg_tgt
        (SIM: sim_message past msg_src msg_tgt)
    :
      Message.le msg_src msg_tgt.
  Proof.
    inv SIM; econs; eauto.
    eapply sim_opt_view_le; eauto.
  Qed.

  Lemma sim_message_exists past msg_tgt
        (CLOSED: Memory.closed past)
    :
      exists msg_src, <<SIM: sim_message past msg_src msg_tgt>>.
  Proof.
    destruct msg_tgt; eauto.
    exploit sim_opt_view_exists; eauto. i. des.
    esplits. econs; eauto.
  Qed.

  Lemma sim_message_closed past msg_src msg_tgt
        (SIM: sim_message past msg_src msg_tgt)
    :
      Memory.closed_message msg_src past.
  Proof.
    inv SIM; econs; eauto.
    eapply sim_opt_view_closed; eauto.
  Qed.

  Lemma sim_message_wf past msg_src msg_tgt
        (SIM: sim_message past msg_src msg_tgt)
        (WF: Message.wf msg_tgt)
    :
      Message.wf msg_src.
  Proof.
    inv WF; inv SIM; econs; eauto.
    eapply sim_opt_view_wf; eauto.
  Qed.

  Inductive sim_promise_content (LOC: bool) (others: Time.t -> Prop)
            (rel_src: View.t)
    :
      option Memory.t -> option (Time.t * Message.t) -> option (Time.t * Message.t) -> Prop :=
  | sim_promise_content_none
      past
    :
      sim_promise_content LOC others rel_src past None None
  | sim_promise_content_normal_concrete
      (NPROM: ~ LOC)
      past from val released_src released_tgt
      (MSG: sim_opt_view past released_src released_tgt)
      (RELVIEW: forall released (MSG: released_src = Some released),
          Memory.closed_view rel_src past)
    :
      sim_promise_content LOC others rel_src
                          (Some past)
                          (Some (from, Message.concrete val released_src))
                          (Some (from, Message.concrete val released_tgt))
  | sim_promise_content_normal_reserve
      (NPROM: ~ LOC)
      past from
    :
      sim_promise_content LOC others rel_src
                          past
                          (Some (from, Message.reserve))
                          (Some (from, Message.reserve))
  | sim_promise_content_forget
      (PROM: LOC)
      past from_src from_tgt msg
      (OTHERS: forall (OTHER: others from_tgt), Time.lt from_tgt from_src)
      (NOTHERS: forall (NOTHER: ~ others from_tgt), from_tgt = from_src)
    :
      sim_promise_content LOC others rel_src
                          past
                          (Some (from_src, Message.reserve))
                          (Some (from_tgt, msg))
  .
  Hint Constructors sim_promise_content.

  Definition sim_promise (others: Loc.t -> Time.t -> Prop)
             (rel_src: LocFun.t View.t)
             (pasts: Loc.t -> Time.t -> option Memory.t)
             (prom_src prom_tgt: Memory.t): Prop :=
    forall loc ts,
      sim_promise_content (L loc) (others loc) (rel_src loc) (pasts loc ts)
                          (Memory.get loc ts prom_src)
                          (Memory.get loc ts prom_tgt).

  Inductive sim_local (others: Loc.t -> Time.t -> Prop) (pasts: Loc.t -> Time.t -> option Memory.t)
            (lc_src lc_tgt: Local.t): Prop :=
  | forget_local_intro
      (TVIEW : TView.le lc_src.(Local.tview) lc_tgt.(Local.tview))
      (PROMS: sim_promise others lc_src.(Local.tview).(TView.rel) pasts lc_src.(Local.promises) lc_tgt.(Local.promises))
    :
      sim_local others pasts lc_src lc_tgt
  .

  Inductive sim_statelocal P (pasts: Loc.t -> Time.t -> option Memory.t):
    sigT (@Language.state ProgramEvent.t) * Local.t -> sigT (@Language.state ProgramEvent.t) * Local.t -> Prop :=
  | forget_statelocal_intro
      st lc_src lc_tgt
      (LOCAL: sim_local P pasts lc_src lc_tgt)
    :
      sim_statelocal P pasts (st, lc_src) (st, lc_tgt)
  .

  Inductive all_promises (proms: Ident.t -> Loc.t -> Time.t -> Prop): Loc.t -> Time.t -> Prop :=
  | all_promises_intro
      tid loc ts
      (PROMS: proms tid loc ts)
    :
      all_promises proms loc ts
  .
  Hint Constructors all_promises.

  Definition promises_not_attached (prom mem: Memory.t): Prop :=
    forall loc ts0 ts1 msg0
           (LOC: L loc)
           (GET: Memory.get loc ts1 prom = Some (ts0, msg0)),
      (<<NOTATTACHED: forall ts2 msg1
                             (ATTACHED: Memory.get loc ts2 mem = Some (ts1, msg1)),
          Memory.get loc ts2 prom = Some (ts1, msg1)>>).

  Definition not_attached_le (others: Loc.t -> Time.t -> Prop)
             (mem0 mem1: Memory.t) :=
    forall loc from (OTHER: others loc from)
           msg to
           (GET: Memory.get loc to mem1 = Some (from, msg)),
    exists to' msg',
      <<GET: Memory.get loc to' mem0 = Some (from, msg')>>.
  Global Program Instance not_attached_le_PreOrder others: PreOrder (not_attached_le others).
  Next Obligation.
  Proof. ii. esplits; eauto. Qed.
  Next Obligation.
  Proof.
    ii. exploit H0; eauto. i. des.
    exploit H; eauto.
  Qed.

  (* Inductive sim_config *)
  (*           (proms: Ident.t -> Loc.t -> Time.t -> Prop) *)
  (*           (pasts: Loc.t -> Time.t -> option Memory.t) *)
  (*           (c_src c_tgt: Configuration.t) *)
  (*   : Prop := *)
  (* | sim_config_intro *)
  (*     (THS: forall tid, option_rel *)
  (*                         (sim_statelocal (proms tid) pasts) *)
  (*                         (IdentMap.find tid c_src.(Configuration.threads)) *)
  (*                         (IdentMap.find tid c_tgt.(Configuration.threads))) *)
  (*     (PAST: wf_pasts_memory c_src.(Configuration.memory) pasts) *)
  (*     (MEM: sim_memory (all_promises proms) c_src.(Configuration.memory) c_tgt.(Configuration.memory)) *)
  (*     (SC: TimeMap.le c_src.(Configuration.sc) c_tgt.(Configuration.sc)) *)
  (*     (ATTACH: not_attached (all_promises proms) c_src.(Configuration.memory)) *)
  (*     (WFSRC: Configuration.wf c_src) *)
  (*     (WFTGT: Configuration.wf c_tgt) *)
  (* (* TODO: can remove all promises *) *)
  (* . *)

  Lemma sim_read_step P others pasts lc_src lc_tgt mem_src mem_tgt loc to val released_tgt ord
        lc_tgt'
        (STEPTGT: Local.read_step lc_tgt mem_tgt loc to val released_tgt ord lc_tgt')
        (NOREAD: ~ P loc to)
        (MEM: sim_memory P mem_src mem_tgt)
        (LOCAL: sim_local others pasts lc_src lc_tgt)
    :
      exists lc_src' released_src,
        (<<STEPSRC: Local.read_step lc_src mem_src loc to val released_src ord lc_src'>>) /\
        (<<SIM: sim_local others pasts lc_src' lc_tgt'>>)
  .
  Proof.
    inv LOCAL. inv STEPTGT.
    specialize (MEM loc to). rewrite GET in *. inv MEM; ss. inv MSG.
    esplits.
    - econs; eauto. eapply TViewFacts.readable_mon; eauto.
      + eapply TVIEW.
      + refl.
    - econs; ss; eauto. eapply read_tview_mon; eauto. refl.
  Qed.

  Lemma sim_fence_step others pasts lc_src lc_tgt sc_src sc_tgt ordr ordw
        sc_tgt' lc_tgt'
        (STEPTGT: Local.fence_step lc_tgt sc_tgt ordr ordw lc_tgt' sc_tgt')
        (SC: TimeMap.le sc_src sc_tgt)
        (LOCAL: sim_local others pasts lc_src lc_tgt)
    :
      exists lc_src' sc_src',
        (<<STEPSRC: Local.fence_step lc_src sc_src ordr ordw lc_src' sc_src'>>) /\
        (<<SC: TimeMap.le sc_src' sc_tgt'>>) /\
        (<<SIM: sim_local others pasts lc_src' lc_tgt'>>)
  .
  Proof.
    inv LOCAL. inv STEPTGT.
    assert (TVIEWLE:
              TView.le
                (TView.write_fence_tview
                   (TView.read_fence_tview (Local.tview lc_src) ordr) sc_src ordw)
                (TView.write_fence_tview
                   (TView.read_fence_tview (Local.tview lc_tgt) ordr) sc_tgt ordw)).
    { eapply write_fence_tview_mon_same_ord; eauto.
      eapply read_fence_tview_mon_same_ord; eauto. }
    esplits.
    - econs; ss; eauto. ii.
      specialize (PROMS loc t). rewrite GET in *. inv PROMS; ss.
      exploit RELEASE; eauto. ss. ii. inv MSG; ss.
    - eapply write_fence_fc_mon_same_ord; eauto.
      eapply read_fence_tview_mon_same_ord; eauto.
    - econs; ss; eauto. ii.
      specialize (PROMS loc ts). des_ifs.
      + inv PROMS; econs; ss; eauto. i.
        exfalso. inv MSG; ss. exploit RELEASE; eauto; ss.
        destruct ordw; eauto.
      + inv PROMS; econs; ss; eauto. i.
        exfalso. inv MSG; ss. exploit RELEASE; eauto; ss.
        destruct ordw; eauto.
      + inv PROMS; econs; ss; eauto. i.
        exfalso. inv MSG; ss. exploit RELEASE; eauto; ss.
        destruct ordw; eauto.
  Qed.

  Lemma sim_promise_consistent prom_self pasts lc_src lc_tgt
        (CONSISTENT: Local.promise_consistent lc_tgt)
        (SIM: sim_local prom_self pasts lc_src lc_tgt)
    :
      Local.promise_consistent lc_src.
  Proof.
    inv SIM. ii.
    specialize (PROMS loc ts). rewrite PROMISE in *. inv PROMS.
    exploit CONSISTENT; eauto. i. eapply TimeFacts.le_lt_lt; eauto.
    inv TVIEW. inv CUR. auto.
  Qed.

  Lemma sim_failure_step prom_self pasts lc_src lc_tgt
        (STEPTGT: Local.failure_step lc_tgt)
        (SIM: sim_local prom_self pasts lc_src lc_tgt)
    :
      Local.failure_step lc_src.
  Proof.
    inv STEPTGT. econs.
    eapply sim_promise_consistent; eauto.
  Qed.

  (* Lemma sim_memory_max_ts P mem_src mem_tgt loc *)
  (*       (CLOSEDSRC: Memory.closed mem_src) *)
  (*       (SIM: sim_memory P mem_src mem_tgt) *)
  (*   : *)
  (*     Time.le (Memory.max_ts loc mem_src) (Memory.max_ts loc mem_tgt). *)
  (* Proof. *)
  (*   inv SIM. *)
  (*   exploit Memory.max_ts_spec. *)
  (*   { apply CLOSEDSRC. } *)
  (*   i. des. dup GET. apply memory_get_ts_strong in GET0. des; clarify. *)
  (*   - rewrite GET1. apply Time.bot_spec. *)
  (*   - exploit COVERED. *)
  (*     + econs; eauto. econs; eauto. reflexivity. *)
  (*     +  i. inv x. inv ITV. etrans; eauto. ss. *)
  (*        eapply Memory.max_ts_spec; eauto. *)
  (* Qed. *)

  (* Lemma sim_memory_max_concrete_timemap P mem_src mem_tgt sc_src sc_tgt *)
  (*       (SIM: sim_memory P mem_src mem_tgt) *)
  (*       (SCSRC: Memory.max_concrete_timemap mem_src sc_src) *)
  (*       (SCTGT: Memory.max_concrete_timemap mem_tgt sc_tgt) *)
  (*   : *)
  (*     TimeMap.le sc_src sc_tgt. *)
  (* Proof. *)
  (*   inv SIM. ii. specialize (SCSRC loc). specialize (SCTGT loc). *)
  (*   inv SCSRC. inv SCTGT. des. *)
  (*   exploit CONCRETE. *)
  (*   - econs. eapply GET. *)
  (*   - i. inv x. eapply MAX0; eauto. *)
  (* Qed. *)

  (* Lemma sim_memory_cap P mem_src mem_tgt cap_src cap_tgt *)
  (*       (SIM: sim_memory P mem_src mem_tgt) *)
  (*       (CLOSEDSRC: Memory.closed mem_src) *)
  (*       (CLOSEDTGT: Memory.closed mem_tgt) *)
  (*       (CAPSRC: Memory.cap mem_src cap_src) *)
  (*       (CAPTGT: Memory.cap mem_tgt cap_tgt) *)
  (*   : *)
  (*     sim_memory P cap_src cap_tgt. *)
  (* Proof. *)
  (*   dup SIM. inv SIM. econs. *)
  (*   - i. eapply Memory.cap_inv in GETTGT; eauto. des; clarify. *)
  (*     apply COMPLETE in GETTGT; eauto. des. *)
  (*     esplits; eauto. eapply Memory.cap_le; eauto. refl. *)
  (*   - i. inv PR. eapply Memory.cap_inv in GET; try apply CAPSRC; eauto. *)
  (*     des; clarify. exploit CONCRETE; eauto. *)
  (*     + econs; eauto. *)
  (*     + i. inv x. eapply Memory.cap_le in GET0. *)
  (*       * econs; eauto. *)
  (*       * eauto. *)
  (*       * refl. *)
  (*   - i. rewrite <- memory_cap_covered; eauto. *)
  (*     rewrite <- memory_cap_covered in COVERED0; try apply CAPSRC; eauto. *)
  (*     inv COVERED0. econs; eauto. ss. rewrite <- MAXTS. auto. *)
  (*   - i. erewrite (@Memory.cap_max_ts mem_src cap_src); eauto. *)
  (*     erewrite (@Memory.cap_max_ts mem_tgt cap_tgt); eauto. *)
  (*     f_equal. auto. *)
  (* Qed. *)

  (* Lemma future_sim_promise P pasts0 pasts1 vw_src vw_tgt proms_src proms_tgt *)
  (*       (SIM: sim_promise P pasts0 vw_src vw_tgt proms_src proms_tgt) *)
  (*       (PASTLE: pasts_le pasts0 pasts1) *)
  (*   : *)
  (*     sim_promise P pasts1 vw_src vw_tgt proms_src proms_tgt. *)
  (* Proof. *)
  (*   inv SIM. econs; eauto. i. *)
  (*   apply NFORGET in GETSRC; auto. des. des_ifs; des; clarify. *)
  (*   - esplits; eauto. *)
  (*   - esplits; eauto. *)
  (* Qed. *)

  (* Lemma future_sim_local prom pasts0 pasts1 lc_src lc_tgt *)
  (*       (SIM: sim_local prom pasts0 lc_src lc_tgt) *)
  (*       (PASTLE: pasts_le pasts0 pasts1) *)
  (*   : *)
  (*     sim_local prom pasts1 lc_src lc_tgt. *)
  (* Proof. *)
  (*   inv SIM. econs; eauto. eapply future_sim_promise; eauto. *)
  (* Qed. *)

  Inductive reserve_future_memory:
    forall (prom0 mem0 prom1 mem1: Memory.t), Prop :=
  | reserve_future_memory_base
      prom0 mem0
    :
      reserve_future_memory
        prom0 mem0 prom0 mem0
  | reserve_future_memory_step
      prom0 mem0 prom1 mem1 prom2 mem2
      loc from to kind
      (LOC: L loc)
      (HD: Memory.promise prom0 mem0 loc from to Message.reserve prom1 mem1 kind)
      (TL: reserve_future_memory prom1 mem1 prom2 mem2)
    :
      reserve_future_memory
        prom0 mem0 prom2 mem2
  .
  Hint Constructors reserve_future_memory.

  Lemma reserve_future_future prom0 mem0 prom1 mem1
        (FUTURE: reserve_future_memory prom0 mem0 prom1 mem1)
    :
      Memory.future mem0 mem1.
  Proof.
    ginduction FUTURE; auto. i. transitivity mem1; auto.
    inv HD; clarify.
    - econs; [|refl]. econs; eauto.
    - econs; [|refl]. econs; eauto.
    - econs; [|refl]. econs; eauto.
    - econs; [|refl]. econs; eauto.
  Qed.

  Lemma reserve_future_concrete_promised prom0 mem0 prom1 mem1
        (FUTURE: reserve_future_memory prom0 mem0 prom1 mem1)
    :
      concrete_promised mem1 <2= concrete_promised mem0.
  Proof.
    ginduction FUTURE; auto. i. apply IHFUTURE in PR; auto.
    inv HD; des; clarify.
    - inv PR. erewrite Memory.add_o in GET; eauto.
      des_ifs. econs; eauto.
    - apply lower_succeed_wf in MEM. des. inv MSG_LE.
    - inv PR. erewrite Memory.remove_o in GET; eauto.
      des_ifs. econs; eauto.
  Qed.

  Lemma reserve_future_wf_pasts_memory prom0 mem0 prom1 mem1 pasts
        (FUTURE: reserve_future_memory prom0 mem0 prom1 mem1)
        (PAST: wf_pasts_memory mem0 pasts)
    :
      wf_pasts_memory mem1 pasts.
  Proof.
    ginduction FUTURE; auto. i. eapply IHFUTURE; eauto. inv PAST.
    dup HD. inv HD; des; clarify.
    - econs.
      + ii. erewrite Memory.add_o in GET; eauto.
        des_ifs. exploit COMPLETE; eauto.
      + i. exploit ONLY; eauto. i. des. esplits; eauto.
        * eapply concrete_promised_increase_promise; eauto.
        * etrans; eauto. eapply Memory.future_future_weak.
          econs; [|refl]. econs.
          { econs 1; eauto. }
          { ss. }
          { ss. }
    - apply lower_succeed_wf in MEM. des. inv MSG_LE.
    - econs.
      + ii. erewrite Memory.remove_o in GET; eauto.
        des_ifs. exploit COMPLETE; eauto.
      + i. exploit ONLY; eauto. i. des. esplits; eauto.
        * eapply concrete_promised_increase_promise; eauto.
        * etrans; eauto. eapply Memory.future_future_weak.
          econs; [|refl]. econs.
          { econs 4; eauto. }
          { ss. }
          { ss. }
  Qed.

  Lemma sim_thread_step others pasts lang st lc_src lc_tgt sc_src sc_tgt mem_src mem_tgt pf e_tgt
        st' lc_tgt' sc_tgt' mem_tgt'
        (STEPTGT: @Thread.step lang pf e_tgt (Thread.mk _ st lc_tgt sc_tgt mem_tgt) (Thread.mk _ st' lc_tgt' sc_tgt' mem_tgt'))
        (NOREAD: no_read_msgs (others \2/ promised lc_src.(Local.promises)) e_tgt)
        (SC: TimeMap.le sc_src sc_tgt)
        (MEM: sim_memory (others \2/ promised lc_src.(Local.promises)) mem_src mem_tgt)
        (SCSRC: Memory.closed_timemap sc_src mem_src)
        (SCTGT: Memory.closed_timemap sc_tgt mem_tgt)
        (MEMSRC: Memory.closed mem_src)
        (MEMTGT: Memory.closed mem_tgt)
        (LOCALSRC: Local.wf lc_src mem_src)
        (LOCALTGT: Local.wf lc_tgt mem_tgt)
        (SIM: sim_local others pasts lc_src lc_tgt)
        (PAST: wf_pasts_memory mem_src pasts)
        (PROMATTACH: promises_not_attached lc_src.(Local.promises) mem_src)
    :
      exists tr pasts' lc_src' sc_src' mem_src',
        (<<STEPSRC: Trace.steps tr (Thread.mk _ st lc_src sc_src mem_src) (Thread.mk _ st' lc_src' sc_src' mem_src')>>) /\
        (<<MEM: sim_memory (others \2/ promised lc_src'.(Local.promises)) mem_src' mem_tgt'>>) /\
        (<<ATTACHEDLE: not_attached_le others mem_src mem_src'>>) /\
        (<<PROMATTACH: promises_not_attached lc_src'.(Local.promises) mem_src'>>) /\
        (<<SC: TimeMap.le sc_src' sc_tgt'>>) /\
        (<<SIM: sim_local others pasts' lc_src' lc_tgt'>>) /\
        (<<PAST: wf_pasts_memory mem_src' pasts'>>) /\
        (<<PASTLE: pasts_le pasts pasts'>>)
  (* TODO: condition about event *)
  .
  Proof.
    inv STEPTGT.
    - inv STEP. destruct (L loc) eqn:LOC.
      + admit.
      + admit.
    - inv STEP. inv LOCAL.
      + eexists [(_, ThreadEvent.silent)], pasts, lc_src, sc_src, mem_src. splits; ss.
        * econs 2; [|econs 1|ss]. econs 2. econs; eauto.
        * refl.
      + exploit sim_read_step; eauto. i. des.
        eexists [(_, ThreadEvent.read loc ts val released_src ord)],
        pasts, lc_src', sc_src, mem_src. splits; ss.
        * econs 2; [|econs 1|ss]. econs 2. econs; eauto.
        * inv STEPSRC. ss.
        * refl.
        * inv STEPSRC. ss.
      + admit.
      + admit.
      + exploit sim_fence_step; eauto. i. des.
        eexists [(_, ThreadEvent.fence ordr ordw)],
        pasts, lc_src', sc_src', mem_src. splits; ss.
        * econs 2; [|econs 1|ss]. econs 2. econs; eauto.
        * inv STEPSRC. ss.
        * refl.
        * inv STEPSRC. ss.
      + exploit sim_fence_step; eauto. i. des.
        eexists [(_, ThreadEvent.syscall e)],
        pasts, lc_src', sc_src', mem_src. splits; ss.
        * econs 2; [|econs 1|ss]. econs 2. econs; eauto.
        * inv STEPSRC. ss.
        * refl.
        * inv STEPSRC. ss.
      + exploit sim_failure_step; eauto. i. des.
        eexists [(_, ThreadEvent.failure)],
        pasts, lc_src, sc_src, mem_src. splits; ss.
        * econs 2; [|econs 1|ss]. econs 2. econs; eauto.
        * refl.
  Admitted.

  Lemma sim_promise_step_forget others pasts mem_src mem_tgt rel_src prom_src prom_tgt
        loc from to msg_tgt prom_tgt' mem_tgt' kind_tgt
        (NLOC: ~ L loc)
        (STEPTGT: Memory.promise prom_tgt mem_tgt loc from to msg_tgt prom_tgt' mem_tgt' kind_tgt)
        (MEM: sim_memory (others \2/ (in_L /2\ promised prom_src)) mem_src mem_tgt)
        (MEMSRC: Memory.closed mem_src)
        (MEMTGT: Memory.closed mem_tgt)
        (WFSRC: Memory.le prom_src mem_src)
        (WFTGT: Memory.le prom_tgt mem_tgt)
        (RELSRC: forall (loc: Loc.t), Memory.closed_view (rel_src loc) mem_src)
        (PROMISE: sim_promise others rel_src pasts prom_src prom_tgt)
        (PAST: wf_pasts_memory mem_src pasts)
        (PROMATTACH: promises_not_attached prom_src mem_src)
        (OTHERSWF: forall loc' to', others loc' to' -> L loc')
    :
      exists msg_src kind_src pasts' prom_src' mem_src',
        (<<STEPSRC: Memory.promise prom_src mem_src loc from to msg_src prom_src' mem_src' kind_src>>) /\
        (<<MEM: sim_memory (others \2/ (in_L /2\ promised prom_src)) mem_src' mem_tgt'>>) /\
        (<<ATTACHEDLE: not_attached_le others mem_src mem_src'>>) /\
        (<<PROMISE: sim_promise others rel_src pasts' prom_src' prom_tgt'>>) /\
        (<<PAST: wf_pasts_memory mem_src' pasts'>>) /\
        (<<PASTLE: pasts_le pasts pasts'>>) /\
        (<<PROMATTACH: promises_not_attached prom_src' mem_src'>>) /\
        (<<CLOSED: Memory.closed_message msg_src mem_src'>>)
  .
  Proof.
    inv STEPTGT.

    (* add case *)
    - exploit sim_message_exists.
      { apply MEMSRC. } instantiate (1:=msg_tgt). i. des.

      exploit add_succeed_wf; try apply MEM0. i. des.
      hexploit (@Memory.add_exists mem_src loc from to msg_src); ss.
      { i. specialize (MEM loc to2). rewrite GET2 in *. inv MEM; cycle 1.
        { exfalso. apply NLOC. des; ss. eapply OTHERSWF; eauto. }
        ii. eapply DISJOINT; eauto.
        inv RHS. econs; ss. eapply TimeFacts.le_lt_lt; eauto. }
      { eapply sim_message_wf; eauto. }
      intros [mem_src' ADDMEMSRC].
      exploit Memory.add_exists_le; try apply ADDMEMSRC; eauto.
      intros [prom_src' ADDPROMSRC].

      assert (ATTACHSRC: forall val released to' msg'
                                (MSG: msg_src = Message.concrete val released)
                                (GET: Memory.get loc to' mem_src = Some (to, msg')), False).
      { i. clarify. inv SIM.
        specialize (MEM loc to'). rewrite GET in *. inv MEM; cycle 1.
        { exfalso. apply NLOC. des; ss. eapply OTHERSWF; eauto. }
        inv FROM.
        { exploit DISJOINT; auto.
          - symmetry. eapply H.
          - instantiate (1:=to). econs; ss. refl.
          - econs; ss. eapply memory_get_ts_le; eauto.
        }
        { inv H0. exploit ATTACH; eauto. }
      }

      assert (MSGTO: Memory.message_to msg_src loc to).
      { inv SIM; econs. inv TS. etrans; eauto.
        apply sim_opt_view_le in SIM0. apply View.unwrap_opt_le in SIM0.
        inv SIM0. auto.
      }

      assert (PROMISESRC: Memory.promise prom_src mem_src loc from to msg_src prom_src' mem_src' Memory.op_kind_add).
      { econs; eauto. }

      assert (FUTURE: Memory.future mem_src mem_src').
      { econs; [|refl]. econs; eauto.
        eapply Memory.add_closed_message; eauto.
        eapply sim_message_closed; eauto. }

      exists msg_src, Memory.op_kind_add,
      (fun loc' to' => if loc_ts_eq_dec (loc', to') (loc, to) then (if msg_src then (Some mem_src) else None) else pasts loc' to'),
      prom_src', mem_src'. splits; auto.
      + ii. erewrite (@Memory.add_o mem_src'); eauto.
        erewrite (@Memory.add_o mem_tgt'); eauto. des_ifs.
        ss. des; clarify. econs; eauto.
        * ii. des; ss. eapply OTHERSWF in H; eauto.
        * refl.
        * eapply sim_message_le; eauto.
        * i. clarify. inv SIM.
          auto.
      + ii. erewrite (@Memory.add_o mem_src') in GET; eauto. des_ifs; eauto.
        ss. des; clarify. eapply OTHERSWF in OTHER; ss.
      + ii. erewrite (@Memory.add_o prom_src'); eauto.
        erewrite (@Memory.add_o prom_tgt'); eauto. des_ifs.
        * ss. des; clarify. inv SIM; econs; eauto.
        * ss. des; clarify. inv SIM; econs; eauto.
      + inv PAST. econs.
        * ii. erewrite (@Memory.add_o mem_src') in GET; eauto.
          destruct (loc_ts_eq_dec (loc0, to0) (loc, to)).
          { ss. des; clarify. esplits; eauto.
            - eapply sim_message_closed in SIM. inv SIM. inv CLOSED. auto.
            - i. des_ifs.
              { exfalso. ss. des; clarify. eapply Time.lt_strorder; eauto. }
              guardH o. exploit ONLY; eauto. i. des; auto.
          }
          { guardH o. exploit COMPLETE; eauto. i. des.
            esplits; eauto. des_ifs. ss. des; clarify.
            exfalso. inv SIM. eapply ATTACHSRC; eauto.
          }
        * i. des_ifs.
          { ss. des; clarify. splits; auto.
            - econs. eapply Memory.add_get0; eauto.
            - apply Memory.future_future_weak. auto.
          }
          { guardH o. exploit ONLY; eauto. i. des. splits; auto.
            - eapply concrete_promised_increase_promise; eauto.
            - etrans; eauto. apply Memory.future_future_weak. auto. }
      + ii. destruct (loc_ts_eq_dec (loc0, to0) (loc, to)); auto.
        ss. des; clarify. exfalso.
        inv PAST. apply ONLY in PAST0. des. inv CONCRETE.
        apply Memory.add_get0 in ADDMEMSRC. des. clarify.
      + ii. erewrite (@Memory.add_o prom_src'); eauto.
        erewrite (@Memory.add_o mem_src' mem_src) in ATTACHED; eauto.
        erewrite (@Memory.add_o prom_src') in GET; eauto. des_ifs.
        * guardH o. ss. des; clarify.
        * guardH o. guardH o0.
          eapply PROMATTACH; eauto.
      + eapply Memory.add_closed_message; eauto.
        eapply sim_message_closed; eauto.

    - exploit split_succeed_wf; try apply PROMISES. i. des. clarify.
      dup PROMISE. specialize (PROMISE0 loc ts3). rewrite GET2 in *.
      inv PAST. inv PROMISE0; ss; [destruct released_src as [released_src|]|].

      (* split normal message with non-none view *)
      { exploit ONLY; eauto. i. des.
        exploit sim_message_exists.
        { apply CLOSED. } instantiate (1:=Message.concrete val' released'). i. des.
        hexploit (@Memory.split_exists prom_src loc from to ts3 msg_src); ss.
        { eauto. }
        { eapply sim_message_wf; eauto. }
        intros [prom_src' SPLITPROMSRC].
        exploit Memory.split_exists_le; try apply SPLITPROMSRC; eauto.
        intros [mem_src' SPLITMEMSRC].

        assert (MSGTO: Memory.message_to msg_src loc to).
        { inv SIM; econs. inv TS. etrans; eauto.
          apply sim_opt_view_le in SIM0. apply View.unwrap_opt_le in SIM0.
          inv SIM0. auto.
        }

        assert (PROMISESRC: Memory.promise prom_src mem_src loc from to msg_src prom_src' mem_src' (Memory.op_kind_split ts3 (Message.concrete val (Some released_src)))).
        { econs; eauto. inv SIM. eauto. }

        assert (FUTURE: Memory.future mem_src mem_src').
        { econs; [|refl]. econs; eauto.
          eapply Memory.split_closed_message; eauto.
          eapply Memory.future_weak_closed_message; eauto.
          eapply sim_message_closed; eauto. }

        exists msg_src, (Memory.op_kind_split ts3 (Message.concrete val (Some released_src))),
        (fun loc' to' => if loc_ts_eq_dec (loc', to') (loc, to)
                         then (Some past)
                         else pasts loc' to'),
        prom_src', mem_src'. splits; auto.
        + ii. erewrite (@Memory.split_o mem_src'); eauto.
          erewrite (@Memory.split_o mem_tgt'); eauto. des_ifs.
          { ss. des; clarify. econs; eauto.
            * ii. des; ss. eapply OTHERSWF in H1; eauto.
            * refl.
            * eapply sim_message_le; eauto.
            * i. clarify. inv SIM.
          }
          { guardH o. ss. des; clarify. econs; eauto.
            * ii. des; ss. eapply OTHERSWF in H1; eauto.
            * refl.
            * eapply sim_message_le; eauto.
            * i. clarify.
          }
        + ii. erewrite (@Memory.split_o mem_src') in GET; eauto. des_ifs; eauto.
          * ss. des; clarify. eapply OTHERSWF in OTHER; ss.
          * guardH o. ss. des; clarify. eapply OTHERSWF in OTHER; ss.
        + ii. erewrite (@Memory.split_o prom_src'); eauto.
          erewrite (@Memory.split_o prom_tgt'); eauto. des_ifs.
          * ss. des; clarify. inv SIM; econs; eauto.
          * guardH o. ss. des; clarify. inv SIM.
            rewrite <- H0. econs; eauto.
        + econs.
          * ii. erewrite (@Memory.split_o mem_src') in GET; eauto.
            destruct (loc_ts_eq_dec (loc0, to0) (loc, to)).
            { ss. des; clarify. esplits; eauto.
              - eapply sim_message_closed in SIM. inv SIM. inv CLOSED0. auto.
              - i. des_ifs.
                { exfalso. ss. des; clarify. eapply Time.lt_strorder; eauto. }
                guardH o. exploit COMPLETE; eauto. i. des.
                apply PREV in PAST. rewrite PAST0 in *. clarify.
            }
            guardH o. destruct (loc_ts_eq_dec (loc0, to0) (loc, ts3)).
            { ss. des; clarify. rewrite <- H0 in *. esplits; eauto.
              - inv MSG. eapply sim_view_closed; eauto.
              - i. des_ifs.
                + refl.
                + ss. des; clarify.
            }
            { guardH o0. exploit COMPLETE; eauto. i. des.
              esplits; eauto. i. des_ifs.
              - ss. des; clarify. exfalso.
                exploit memory_get_from_inj.
                { eapply Memory.split_get0 in SPLITMEMSRC. des. eapply GET5. }
                { instantiate (1:=Message.concrete val0 (Some released)).
                  instantiate (1:=to0). erewrite Memory.split_o; [|eauto]. des_ifs.
                  - ss. unguard. des; clarify.
                  - ss. unguard. des; clarify. }
                { i. des; clarify.
                  - unguard. des; clarify.
                  - eapply Time.lt_strorder; eauto.
                  - eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
                    + eapply TS12.
                    + eapply Time.bot_spec. }
              - guardH o1. exploit COMPLETE; eauto.
            }
          * i. des_ifs.
            { ss. des; clarify. splits; auto.
              - eapply Memory.split_get0 in SPLITMEMSRC. des.
                inv SIM. econs; eauto.
              - etrans; eauto. apply Memory.future_future_weak. auto.
            }
            { guardH o. exploit ONLY; eauto. i. des. splits; auto.
              - eapply concrete_promised_increase_promise; eauto.
              - etrans; eauto. apply Memory.future_future_weak. auto. }
        + ii. destruct (loc_ts_eq_dec (loc0, to0) (loc, to)); auto.
          ss. des; clarify. exfalso.
          apply ONLY in PAST0. des. inv CONCRETE0.
          apply Memory.split_get0 in SPLITMEMSRC. des. clarify.
        + ii. erewrite (@Memory.split_o prom_src'); eauto.
          erewrite (@Memory.split_o mem_src' mem_src) in ATTACHED; eauto.
          erewrite (@Memory.split_o prom_src') in GET; eauto. des_ifs.
          * guardH o. ss. des; clarify.
          * guardH o. ss. des; clarify.
          * guardH o. guardH o0.
            eapply PROMATTACH; eauto.
        + eapply Memory.split_closed_message; eauto.
          eapply Memory.future_weak_closed_message; eauto.
          eapply sim_message_closed; eauto.
      }


      (* split normal message with none view *)
      { exploit ONLY; eauto. i. des.
        exploit sim_message_exists.
        { apply MEMSRC. } instantiate (1:=Message.concrete val' released'). i. des.
        hexploit (@Memory.split_exists prom_src loc from to ts3 msg_src); ss.
        { eauto. }
        { eapply sim_message_wf; eauto. }
        intros [prom_src' SPLITPROMSRC].
        exploit Memory.split_exists_le; try apply SPLITPROMSRC; eauto.
        intros [mem_src' SPLITMEMSRC].

        assert (MSGTO: Memory.message_to msg_src loc to).
        { inv SIM; econs. inv TS. etrans; eauto.
          apply sim_opt_view_le in SIM0. apply View.unwrap_opt_le in SIM0.
          inv SIM0. auto.
        }

        assert (PROMISESRC: Memory.promise prom_src mem_src loc from to msg_src prom_src' mem_src' (Memory.op_kind_split ts3 (Message.concrete val None))).
        { econs; eauto. inv SIM. eauto. }

        assert (FUTURE: Memory.future mem_src mem_src').
        { econs; [|refl]. econs; eauto.
          eapply Memory.split_closed_message; eauto.
          eapply sim_message_closed; eauto. }

        exists msg_src, (Memory.op_kind_split ts3 (Message.concrete val None)),
        (fun loc' to' => if loc_ts_eq_dec (loc', to') (loc, to)
                         then (Some mem_src)
                         else pasts loc' to'),
        prom_src', mem_src'. splits; auto.
        + ii. erewrite (@Memory.split_o mem_src'); eauto.
          erewrite (@Memory.split_o mem_tgt'); eauto. des_ifs.
          { ss. des; clarify. econs; eauto.
            * ii. des; ss. eapply OTHERSWF in H1; eauto.
            * refl.
            * eapply sim_message_le; eauto.
            * i. clarify. inv SIM.
          }
          { guardH o. ss. des; clarify. econs; eauto.
            * ii. des; ss. eapply OTHERSWF in H1; eauto.
            * refl.
            * i. clarify.
          }
        + ii. erewrite (@Memory.split_o mem_src') in GET; eauto. des_ifs; eauto.
          * ss. des; clarify. eapply OTHERSWF in OTHER; ss.
          * guardH o. ss. des; clarify. eapply OTHERSWF in OTHER; ss.
        + ii. erewrite (@Memory.split_o prom_src'); eauto.
          erewrite (@Memory.split_o prom_tgt'); eauto. des_ifs.
          * ss. des; clarify. inv SIM; econs; eauto.
          * guardH o. ss. des; clarify. inv SIM.
            rewrite <- H0. econs; eauto.
        + econs.
          * ii. erewrite (@Memory.split_o mem_src') in GET; eauto.
            destruct (loc_ts_eq_dec (loc0, to0) (loc, to)).
            { ss. des; clarify. esplits; eauto.
              - eapply sim_message_closed in SIM. inv SIM. inv CLOSED0. auto.
              - i. des_ifs.
                { exfalso. ss. des; clarify. eapply Time.lt_strorder; eauto. }
                guardH o. eapply ONLY; eauto.
            }
            guardH o. destruct (loc_ts_eq_dec (loc0, to0) (loc, ts3)).
            { ss. }
            { guardH o0. exploit COMPLETE; eauto. i. des.
              esplits; eauto. i. des_ifs.
              - ss. des; clarify. exfalso.
                exploit memory_get_from_inj.
                { eapply Memory.split_get0 in SPLITMEMSRC. des. eapply GET5. }
                { instantiate (1:=Message.concrete val0 (Some released)).
                  instantiate (1:=to0). erewrite Memory.split_o; [|eauto]. des_ifs.
                  - ss. unguard. des; clarify.
                  - ss. unguard. des; clarify. }
                { i. des; clarify.
                  - unguard. des; clarify.
                  - eapply Time.lt_strorder; eauto.
                  - eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
                    + eapply TS12.
                    + eapply Time.bot_spec. }
              - guardH o1. exploit COMPLETE; eauto.
            }
          * i. des_ifs.
            { ss. des; clarify. splits; auto.
              - eapply Memory.split_get0 in SPLITMEMSRC. des.
                inv SIM. econs; eauto.
              - apply Memory.future_future_weak. auto.
            }
            { guardH o. exploit ONLY; eauto. i. des. splits; auto.
              - eapply concrete_promised_increase_promise; eauto.
              - etrans; eauto. apply Memory.future_future_weak. auto. }
        + ii. destruct (loc_ts_eq_dec (loc0, to0) (loc, to)); auto.
          ss. des; clarify. exfalso.
          apply ONLY in PAST0. des. inv CONCRETE0.
          apply Memory.split_get0 in SPLITMEMSRC. des. clarify.
        + ii. erewrite (@Memory.split_o prom_src'); eauto.
          erewrite (@Memory.split_o mem_src' mem_src) in ATTACHED; eauto.
          erewrite (@Memory.split_o prom_src') in GET; eauto. des_ifs.
          * guardH o. ss. des; clarify.
          * guardH o. ss. des; clarify.
          * guardH o. guardH o0.
            eapply PROMATTACH; eauto.
        + eapply Memory.split_closed_message; eauto.
          eapply sim_message_closed; eauto.
      }


      (* split reserve *)
      { exploit sim_message_exists.
        { apply MEMSRC. } instantiate (1:=Message.concrete val' released'). i. des.
        hexploit (@Memory.split_exists prom_src loc from to ts3 msg_src); ss.
        { eauto. }
        { eapply sim_message_wf; eauto. }
        intros [prom_src' SPLITPROMSRC].
        exploit Memory.split_exists_le; try apply SPLITPROMSRC; eauto.
        intros [mem_src' SPLITMEMSRC].

        assert (MSGTO: Memory.message_to msg_src loc to).
        { inv SIM; econs. inv TS. etrans; eauto.
          apply sim_opt_view_le in SIM0. apply View.unwrap_opt_le in SIM0.
          inv SIM0. auto.
        }

        assert (PROMISESRC: Memory.promise prom_src mem_src loc from to msg_src prom_src' mem_src' (Memory.op_kind_split ts3 Message.reserve)).
        { econs; eauto. inv SIM. eauto. }

        assert (FUTURE: Memory.future mem_src mem_src').
        { econs; [|refl]. econs; eauto.
          eapply Memory.split_closed_message; eauto.
          eapply sim_message_closed; eauto. }

        exists msg_src, (Memory.op_kind_split ts3 Message.reserve),
        (fun loc' to' => if loc_ts_eq_dec (loc', to') (loc, to)
                         then (Some mem_src)
                         else pasts loc' to'),
        prom_src', mem_src'. splits; auto.
        + ii. erewrite (@Memory.split_o mem_src'); eauto.
          erewrite (@Memory.split_o mem_tgt'); eauto. des_ifs.
          { ss. des; clarify. econs; eauto.
            * ii. des; ss. eapply OTHERSWF in H; eauto.
            * refl.
            * eapply sim_message_le; eauto.
            * i. clarify. inv SIM.
          }
          { guardH o. ss. des; clarify. econs; eauto.
            * ii. des; ss. eapply OTHERSWF in H; eauto.
            * refl.
          }
        + ii. erewrite (@Memory.split_o mem_src') in GET; eauto. des_ifs; eauto.
          * ss. des; clarify. eapply OTHERSWF in OTHER; ss.
          * guardH o. ss. des; clarify. eapply OTHERSWF in OTHER; ss.
        + ii. erewrite (@Memory.split_o prom_src'); eauto.
          erewrite (@Memory.split_o prom_tgt'); eauto. des_ifs.
          * ss. des; clarify. inv SIM; econs; eauto.
          * guardH o. ss. des; clarify. inv SIM. econs; eauto.
        + econs.
          * ii. erewrite (@Memory.split_o mem_src') in GET; eauto.
            destruct (loc_ts_eq_dec (loc0, to0) (loc, to)).
            { ss. des; clarify. esplits; eauto.
              - eapply sim_message_closed in SIM. inv SIM. inv CLOSED. auto.
              - i. des_ifs.
                { exfalso. ss. des; clarify. eapply Time.lt_strorder; eauto. }
                guardH o. eapply ONLY; eauto.
            }
            guardH o. destruct (loc_ts_eq_dec (loc0, to0) (loc, ts3)).
            { ss. }
            { guardH o0. exploit COMPLETE; eauto. i. des.
              esplits; eauto. i. des_ifs.
              - ss. des; clarify. exfalso.
                exploit memory_get_from_inj.
                { eapply Memory.split_get0 in SPLITMEMSRC. des. eapply GET5. }
                { instantiate (1:=Message.concrete val (Some released)).
                  instantiate (1:=to0). erewrite Memory.split_o; [|eauto]. des_ifs.
                  - ss. unguard. des; clarify.
                  - ss. unguard. des; clarify. }
                { i. des; clarify.
                  - unguard. des; clarify.
                  - eapply Time.lt_strorder; eauto.
                  - eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
                    + eapply TS12.
                    + eapply Time.bot_spec. }
              - guardH o1. exploit COMPLETE; eauto.
            }
          * i. des_ifs.
            { ss. des; clarify. splits; auto.
              - eapply Memory.split_get0 in SPLITMEMSRC. des.
                inv SIM. econs; eauto.
              - apply Memory.future_future_weak. auto.
            }
            { guardH o. exploit ONLY; eauto. i. des. splits; auto.
              - eapply concrete_promised_increase_promise; eauto.
              - etrans; eauto. apply Memory.future_future_weak. auto. }
        + ii. destruct (loc_ts_eq_dec (loc0, to0) (loc, to)); auto.
          ss. des; clarify. exfalso.
          apply ONLY in PAST0. des. inv CONCRETE.
          apply Memory.split_get0 in SPLITMEMSRC. des. clarify.
        + ii. erewrite (@Memory.split_o prom_src'); eauto.
          erewrite (@Memory.split_o mem_src' mem_src) in ATTACHED; eauto.
          erewrite (@Memory.split_o prom_src') in GET; eauto. des_ifs.
          * guardH o. ss. des; clarify.
          * guardH o. ss. des; clarify.
          * guardH o. guardH o0.
            eapply PROMATTACH; eauto.
        + eapply Memory.split_closed_message; eauto.
          eapply sim_message_closed; eauto.
      }

    (* lower case *)
    - exploit lower_succeed_wf; try apply PROMISES. i. des. clarify.
      dup PROMISE. specialize (PROMISE0 loc to). rewrite GET in *.
      inv PAST. inv PROMISE0; ss.

      exploit ONLY; eauto. i. des.
      exploit sim_message_exists.
      { apply CLOSED. } instantiate (1:=msg_tgt). i. des.

      inv MSG_LE. dup SIM. inv SIM.
      assert (VIEWLE: View.opt_le released_src0 released_src).
      { eapply sim_opt_view_max; eauto.
        - etrans; eauto. eapply sim_opt_view_le; eauto.
        - eapply sim_opt_view_closed; eauto. }

      hexploit (@Memory.lower_exists prom_src loc from to (Message.concrete val released_src) (Message.concrete val released_src0)); ss.
      { eapply sim_message_wf; eauto. }
      { econs; eauto. }

      intros [prom_src' LOWERPROMSRC].
      exploit Memory.lower_exists_le; try apply LOWERPROMSRC; eauto.
      intros [mem_src' LOWERMEMSRC].

      assert (MSGTO: Memory.message_to (Message.concrete val released_src0) loc to).
      { econs. inv TS. etrans; eauto.
        apply sim_opt_view_le in SIM1. apply View.unwrap_opt_le in SIM1.
        inv SIM1. auto.
      }

      assert (PROMISESRC: Memory.promise prom_src mem_src loc from to (Message.concrete val released_src0) prom_src' mem_src' (Memory.op_kind_lower (Message.concrete val released_src))).
      { econs; eauto. }

      assert (FUTURE: Memory.future mem_src mem_src').
      { econs; [|refl]. econs; eauto.
        eapply Memory.lower_closed_message; eauto.
        eapply Memory.future_weak_closed_message; eauto.
        econs. eapply sim_opt_view_closed; eauto. }

      exists (Message.concrete val released_src0), (Memory.op_kind_lower (Message.concrete val released_src)), pasts, prom_src', mem_src'. splits; auto.
      + ii. erewrite (@Memory.lower_o mem_src'); eauto.
        erewrite (@Memory.lower_o mem_tgt'); eauto. des_ifs.
        ss. des; clarify. econs; eauto.
        * ii. des; ss. eapply OTHERSWF in H1; eauto.
        * refl.
        * eapply sim_message_le; eauto.
        * i. clarify.
      + ii. erewrite (@Memory.lower_o mem_src') in GET0; eauto. des_ifs; eauto.
        ss. des; clarify. eapply OTHERSWF in OTHER; ss.
      + ii. erewrite (@Memory.lower_o prom_src'); eauto.
        erewrite (@Memory.lower_o prom_tgt'); eauto. des_ifs.
        ss. des; clarify. rewrite <- H0. econs; eauto.
        i. clarify. inv VIEWLE. eapply RELVIEW; eauto.
      + econs.
        * ii. erewrite (@Memory.lower_o mem_src') in GET0; eauto. des_ifs.
          { inv VIEWLE. ss. des; clarify. esplits; eauto.
            - inv SIM1. eapply sim_view_closed; eauto.
            - i. exploit COMPLETE; eauto. i. des.
              rewrite PAST0 in *. clarify. eauto.
          }
          { guardH o. exploit COMPLETE; eauto. }
        * i. exploit ONLY; eauto. i. des. splits; auto.
          { eapply concrete_promised_increase_promise; eauto. }
          { etrans; eauto. apply Memory.future_future_weak. auto. }
      + refl.
      + ii. erewrite (@Memory.lower_o prom_src'); eauto.
        erewrite (@Memory.lower_o mem_src' mem_src) in ATTACHED; eauto.
        erewrite (@Memory.lower_o prom_src') in GET0; eauto. des_ifs.
        * guardH o. ss. des; clarify.
        * eapply PROMATTACH; eauto.
      + eapply Memory.lower_closed_message; eauto.
        eapply Memory.future_weak_closed_message; eauto.
        econs. eapply sim_opt_view_closed; eauto.

    (* cancel case *)
    - exploit Memory.remove_get0; try apply PROMISES. i. des.
      dup PROMISE. specialize (PROMISE0 loc to). rewrite GET in *.
      inv PROMISE0; ss.

      hexploit (@Memory.remove_exists prom_src loc from to Message.reserve); ss.
      intros [prom_src' REMOVEPROMSRC].
      exploit Memory.remove_exists_le; try apply REMOVEPROMSRC; eauto.
      intros [mem_src' REMOVEMEMSRC].

      assert (PROMISESRC: Memory.promise prom_src mem_src loc from to Message.reserve prom_src' mem_src' Memory.op_kind_cancel).
      { econs; eauto. }

      assert (FUTURE: Memory.future mem_src mem_src').
      { econs; [|refl]. econs; eauto. }

      exists Message.reserve, Memory.op_kind_cancel, pasts, prom_src', mem_src'.
      splits; auto.
      + ii. erewrite (@Memory.remove_o mem_src'); eauto.
        erewrite (@Memory.remove_o mem_tgt'); eauto. des_ifs.
        ss. des; clarify. econs; eauto.
        * ii. des; ss. eapply OTHERSWF in H; eauto.
      + ii. erewrite (@Memory.remove_o mem_src') in GET1; eauto. des_ifs; eauto.
      + ii. erewrite (@Memory.remove_o prom_src'); eauto.
        erewrite (@Memory.remove_o prom_tgt'); eauto. des_ifs.
      + inv PAST. econs.
        * ii. erewrite (@Memory.remove_o mem_src') in GET1; eauto. des_ifs.
          { exploit COMPLETE; eauto. }
        * i. exploit ONLY; eauto. i. des. splits; auto.
          { eapply concrete_promised_increase_promise; eauto. }
          { etrans; eauto. apply Memory.future_future_weak. auto. }
      + refl.
      + ii. erewrite (@Memory.remove_o prom_src'); eauto.
        erewrite (@Memory.remove_o mem_src' mem_src) in ATTACHED; eauto.
        erewrite (@Memory.remove_o prom_src') in GET1; eauto. des_ifs.
        eapply PROMATTACH; eauto.
  Qed.




  Lemma sim_promise_step_normal
        others pasts lang st lc_src lc_tgt sc_src sc_tgt mem_src mem_tgt pf e_tgt
        st' lc_tgt' sc_tgt' mem_tgt'
        (STEPTGT: @Thread.step lang pf e_tgt (Thread.mk _ st lc_tgt sc_tgt mem_tgt) (Thread.mk _ st' lc_tgt' sc_tgt' mem_tgt'))
        (NOREAD: no_read_msgs (others \2/ promised lc_src.(Local.promises)) e_tgt)
        (SC: TimeMap.le sc_src sc_tgt)
        (MEM: sim_memory (others \2/ promised lc_src.(Local.promises))
                         mem_src mem_tgt)
        (SCSRC: Memory.closed_timemap sc_src mem_src)
        (SCTGT: Memory.closed_timemap sc_tgt mem_tgt)
        (MEMSRC: Memory.closed mem_src)
        (MEMTGT: Memory.closed mem_tgt)
        (LOCALSRC: Local.wf lc_src mem_src)
        (LOCALTGT: Local.wf lc_tgt mem_tgt)
        (SIM: sim_local others pasts lc_src lc_tgt)
        (PAST: wf_pasts_memory mem_src pasts)
        (PROMATTACH: promises_not_attached lc_src.(Local.promises) mem_src)
    :
      exists tr pasts' lc_src' sc_src' mem_src',
        (<<STEPSRC: Trace.steps tr (Thread.mk _ st lc_src sc_src mem_src) (Thread.mk _ st' lc_src' sc_src' mem_src')>>) /\
        (<<MEM: sim_memory (others \2/ promised lc_src'.(Local.promises)) mem_src' mem_tgt'>>) /\
        (<<ATTACHEDLE: not_attached_le others mem_src mem_src'>>) /\
        (<<PROMATTACH: promises_not_attached lc_src'.(Local.promises) mem_src'>>) /\
        (<<SC: TimeMap.le sc_src' sc_tgt'>>) /\
        (<<SIM: sim_local others pasts' lc_src' lc_tgt'>>) /\
        (<<PAST: wf_pasts_memory mem_src' pasts'>>) /\
        (<<PASTLE: pasts_le pasts pasts'>>)
  (* TODO: condition about event *)
  .
  Proof.
    inv STEPTGT.
    - inv STEP. destruct (L loc) eqn:LOC.
      + admit.
      + admit.
    - inv STEP. inv LOCAL.
      + eexists [(_, ThreadEvent.silent)], pasts, lc_src, sc_src, mem_src. splits; ss.
        * econs 2; [|econs 1|ss]. econs 2. econs; eauto.
        * refl.
      + exploit sim_read_step; eauto. i. des.
        eexists [(_, ThreadEvent.read loc ts val released_src ord)],
        pasts, lc_src', sc_src, mem_src. splits; ss.
        * econs 2; [|econs 1|ss]. econs 2. econs; eauto.
        * inv STEPSRC. ss.
        * refl.
        * inv STEPSRC. ss.
      + admit.
      + admit.
      + exploit sim_fence_step; eauto. i. des.
        eexists [(_, ThreadEvent.fence ordr ordw)],
        pasts, lc_src', sc_src', mem_src. splits; ss.
        * econs 2; [|econs 1|ss]. econs 2. econs; eauto.
        * inv STEPSRC. ss.
        * refl.
        * inv STEPSRC. ss.
      + exploit sim_fence_step; eauto. i. des.
        eexists [(_, ThreadEvent.syscall e)],
        pasts, lc_src', sc_src', mem_src. splits; ss.
        * econs 2; [|econs 1|ss]. econs 2. econs; eauto.
        * inv STEPSRC. ss.
        * refl.
        * inv STEPSRC. ss.
      + exploit sim_failure_step; eauto. i. des.
        eexists [(_, ThreadEvent.failure)],
        pasts, lc_src, sc_src, mem_src. splits; ss.
        * econs 2; [|econs 1|ss]. econs 2. econs; eauto.
        * refl.
  Admitted.


  Lemma split_reserve_exists prom1 mem1 loc ts1 ts2 ts3
        (MLE: Memory.le prom1 mem1)
        (GET: Memory.get loc ts3 prom1 = Some (ts1, Message.reserve))
        (TS12: Time.lt ts1 ts2)
        (TS23: Time.lt ts2 ts3)
    :
      exists prom2 mem2,
        (<<FUTURE: reserve_future_memory prom1 mem1 prom2 mem2>>) /\
        (<<SPLITMEM:
           forall l t,
             Memory.get l t mem2 =
             (if loc_ts_eq_dec (l, t) (loc, ts2)
              then Some (ts1, Message.reserve)
              else
                if loc_ts_eq_dec (l, t) (loc, ts3)
                then Some (ts2, Message.reserve)
                else Memory.get l t mem1)>>) /\
        (<<SPLITPROM:
           forall l t,
             Memory.get l t prom2 =
             (if loc_ts_eq_dec (l, t) (loc, ts2)
              then Some (ts1, Message.reserve)
              else
                if loc_ts_eq_dec (l, t) (loc, ts3)
                then Some (ts2, Message.reserve)
                else Memory.get l t prom1)>>)
  .
  Proof.
    exploit Memory.remove_exists.
    { apply GET. } intros [prom_mid0 PROM0].
    exploit Memory.remove_exists_le; eauto. intros [mem_mid0 MEM0].
    assert (STEP0: Memory.promise prom1 mem1 loc ts1 ts3 Message.reserve prom_mid0 mem_mid0 Memory.op_kind_cancel).
    { econs; eauto. }
    hexploit promise_memory_le; eauto. intros MLE0.
    exploit (@Memory.add_exists mem_mid0 loc ts2 ts3 Message.reserve).
    { ii. erewrite Memory.remove_o in GET2; eauto. des_ifs. ss. guardH o.
      exploit Memory.get_disjoint.
      - apply MLE. apply GET.
      - apply GET2.
      - i. des; clarify.
        + unguard. des; auto.
        + eapply x1; eauto. inv LHS. econs; eauto. }
    { auto. }
    { econs. } intros [mem_mid1 MEM1].
    exploit Memory.add_exists_le; eauto. intros [prom_mid1 PROM11].
    assert (STEP1: Memory.promise prom_mid0 mem_mid0 loc ts2 ts3 Message.reserve prom_mid1 mem_mid1 Memory.op_kind_add).
    { econs; eauto. i. clarify.
    }
    hexploit promise_memory_le; eauto. intros MLE1.
    exploit (@Memory.add_exists mem_mid1 loc ts1 ts2 Message.reserve).
    { ii. erewrite Memory.add_o in GET2; eauto. des_ifs.
      { ss. des; clarify. inv LHS. inv RHS. ss.
        eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt.
        - apply TO.
        - apply FROM0.
      } ss. guardH o.
      erewrite Memory.remove_o in GET2; eauto. des_ifs. ss. guardH o0.
      exploit Memory.get_disjoint.
      - apply MLE. apply GET.
      - apply GET2.
      - i. des; clarify.
        + unguard. des; auto.
        + eapply x1; eauto. inv LHS. econs; eauto. etrans; eauto. left. auto.
    }
    { auto. }
    { econs. } intros [mem2 MEM2].
    exploit Memory.add_exists_le; eauto. intros [prom2 PROM2].
    assert (STEP2: Memory.promise prom_mid1 mem_mid1 loc ts1 ts2 Message.reserve prom2 mem2 Memory.op_kind_add).
    { econs; eauto. i. clarify.
    }
    assert (NEQ23: ts2 <> ts3).
    { ii. clarify. eapply Time.lt_strorder. eauto. }
    exists prom2, mem2. splits.
    - eauto.
    - i. erewrite (@Memory.add_o mem2 mem_mid1); eauto.
      erewrite (@Memory.add_o mem_mid1 mem_mid0); eauto. erewrite (@Memory.remove_o mem_mid0 mem1); eauto.
      des_ifs.
    - i. erewrite (@Memory.add_o prom2 prom_mid1); eauto.
      erewrite (@Memory.add_o prom_mid1 prom_mid0); eauto. erewrite (@Memory.remove_o prom_mid0 prom1); eauto.
      des_ifs.
  Admitted.

  Lemma sim_promise_step_forget prom_self prom_others pasts mem_src mem_tgt rel_src rel_tgt prom_src prom_tgt
        loc from to msg prom_tgt' mem_tgt' kind
        (NLOC: L loc)
        (STEPTGT: Memory.promise prom_tgt mem_tgt loc from to msg prom_tgt' mem_tgt' kind)
        (MEM: sim_memory (prom_others \2/ prom_self) mem_src mem_tgt)
        (ATTACH: not_attached (prom_others \2/ prom_self) mem_src)
        (MEMSRC: Memory.closed mem_src)
        (MEMTGT: Memory.closed mem_tgt)
        (WFSRC: Memory.le prom_src mem_src)
        (WFTGT: Memory.le prom_tgt mem_tgt)
        (RELSRC: forall (loc: Loc.t), Memory.closed_view (rel_src loc) mem_src)
        (RELTGT: forall (loc: Loc.t), Memory.closed_view (rel_tgt loc) mem_src)
        (PROMISE: sim_promise prom_self pasts rel_src rel_tgt prom_src prom_tgt)
        (PAST: wf_pasts_memory mem_src pasts)
    :
      exists prom_self' prom_src' mem_src',
        (<<FUTURE: reserve_future_memory prom_src mem_src prom_src' mem_src'>>) /\
        (<<MEM: sim_memory (prom_others \2/ prom_self') mem_src' mem_tgt'>>) /\
        (<<ATTACH: not_attached (prom_others \2/ prom_self') mem_src'>>) /\
        (<<PROMISE: sim_promise prom_self' pasts rel_src rel_tgt prom_src' prom_tgt'>>) /\
        (<<PAST: wf_pasts_memory mem_src' pasts>>)
  .
  Proof.
    inv PROMISE. inv MEM. dup STEPTGT. inv STEPTGT.
    - dup MEM. apply add_succeed_wf in MEM0. des.
      exploit Memory.add_exists; try apply TO1.
      { instantiate (1:=mem_src). instantiate (1:=loc). ii.
        exploit COVERED.
        { econs; eauto. } i. inv x0.
        eapply DISJOINT; eauto. }
      { eapply Message.wf_reserve. } i. des.
      exploit Memory.add_exists_le; try apply x0; eauto. i. des.
      assert (FUTURE: reserve_future_memory prom_src mem_src promises2 mem2).
      { econs.
        - econs 1; eauto. i. clarify.
        - econs 1. }
      destruct msg.
      { exists (fun loc' to' => prom_self loc' to' \/ (loc' = loc /\ to' = to)), promises2, mem2.
        splits; auto.
        + econs.
          * ii. erewrite Memory.add_o in GETTGT; eauto. erewrite Memory.add_o; eauto.
            des_ifs; ss.
            { des; clarify. exfalso. auto. }
            exploit COMPLETE0; eauto. ii. apply NPROMS. des; auto.
          * i. eapply concrete_promised_increase_promise; eauto.
            apply CONCRETE. eapply reserve_future_concrete_promised; eauto.
          * i. erewrite add_covered in COVERED0; eauto.
            eapply add_covered; eauto. des; auto.
        + ii. erewrite Memory.add_o in GET; eauto. des_ifs.
          ss. des; clarify; try by (eapply ATTACH; eauto).
          exploit ATTACH0; eauto.
          admit. (* change it *)
        + econs.
          * i. erewrite Memory.add_o in GETSRC; eauto.
            erewrite Memory.add_o; eauto.
            destruct (loc_ts_eq_dec (loc0, to0) (loc, to)); clarify.
            { des; clarify. exfalso. auto. }
            exploit NFORGET; eauto.
          * i. erewrite Memory.add_o in GETTGT; eauto.
            erewrite Memory.add_o; try eassumption.
            des_ifs; clarify; eauto.
          * i. erewrite (@Memory.add_o promises2 prom_src); eauto.
            erewrite (@Memory.add_o prom_tgt' prom_tgt); eauto. des_ifs; eauto.
            { ss. destruct a. clarify. esplits; eauto. }
            { exploit FORGET; eauto. des; clarify. }
        + eapply reserve_future_wf_pasts_memory; eauto.
      }
      { exists prom_self, promises2, mem2.
        splits; auto.
        + econs.
          * ii. erewrite Memory.add_o in GETTGT; eauto. erewrite Memory.add_o; eauto.
            des_ifs; ss.
            exploit COMPLETE0; eauto.
          * i. eapply concrete_promised_increase_promise; eauto.
            apply CONCRETE. eapply reserve_future_concrete_promised; eauto.
          * i. erewrite add_covered in COVERED0; eauto.
            eapply add_covered; eauto. des; auto.
        + ii. erewrite Memory.add_o in GET; eauto. des_ifs.
          ss. des; clarify; try by (eapply ATTACH; eauto).
        + econs.
          * i. erewrite Memory.add_o in GETSRC; eauto.
            erewrite Memory.add_o; eauto.
            destruct (loc_ts_eq_dec (loc0, to0) (loc, to)); clarify; eauto.
          * i. erewrite Memory.add_o in GETTGT; eauto.
            erewrite Memory.add_o; try eassumption.
            des_ifs; clarify; eauto.
          * i. erewrite (@Memory.add_o promises2 prom_src); eauto.
            erewrite (@Memory.add_o prom_tgt' prom_tgt); eauto. des_ifs; eauto.
            ss. des; clarify. exploit FORGET; eauto. i. des.
            eapply Memory.add_get0 in PROMISES. des. clarify.
        + eapply reserve_future_wf_pasts_memory; eauto.
      }

    - dup PROMISES. apply split_succeed_wf in PROMISES0. des. clarify.
      destruct (classic (prom_self loc ts3)) as [PROM|NPROM].
      { exploit FORGET; eauto. i. des. clarify.
        exploit split_reserve_exists; try apply GETSRC; eauto. i. des.
        exists (fun loc' to' => prom_self loc' to' \/ (loc' = loc /\ to' = to)), prom2, mem2.
        splits; auto.
        + econs.
          * ii. erewrite Memory.split_o in GETTGT0; eauto. erewrite SPLITMEM; eauto.
            des_ifs; ss.
            { des; clarify. exfalso. auto. }
            { des; clarify. exfalso. auto. }
            exploit COMPLETE0; eauto. ii. apply NPROMS. des; auto.
          * i. eapply concrete_promised_increase_promise; eauto.
            apply CONCRETE. eapply reserve_future_concrete_promised; eauto.
          * i. erewrite split_covered; cycle 1; eauto. apply COVERED.
            inv COVERED0. rewrite SPLITMEM in GET. des_ifs; des; ss; clarify; econs; eauto.
            { inv ITV. econs; eauto. ss. etrans; eauto. left. auto. }
            { inv ITV. econs; eauto. }
        + ii. erewrite SPLITMEM in GET. des_ifs. guardH o. guardH o0.
          ss. exploit ATTACH; cycle 1; eauto. des; auto. clarify. exfalso.
          exploit memory_get_ts_strong; try apply GET. i. des; clarify.
          { unguard. des; auto. }
          exfalso. exploit Memory.get_disjoint.
          * apply GET.
          * apply WFSRC. apply GETSRC.
          * i. des; clarify. specialize (x0 (Time.meet to' ts3)).
            unfold Time.meet in *. des_ifs.
            { eapply x0; eauto; econs; ss.
              - refl.
              - etrans; eauto. }
            { eapply x0; eauto; econs; ss.
              - left. auto.
              - etrans; eauto.
              - refl. }
        + econs.
          * i. erewrite SPLITPROM in GETSRC0; eauto.
            erewrite Memory.split_o; eauto.
            destruct (loc_ts_eq_dec (loc0, to0) (loc, to)); clarify.
            { ss. des; clarify. exfalso. auto. }
            destruct (loc_ts_eq_dec (loc0, to0) (loc, ts3)); clarify.
            { ss. des; clarify. exfalso. auto. }
            exploit NFORGET; eauto.
          * i. erewrite Memory.split_o in GETTGT0; eauto.
            erewrite SPLITPROM.
            des_ifs; clarify; eauto.
          * i. apply or_comm in PROM0. apply or_strengthen in PROM0.
            erewrite SPLITPROM; eauto.
            erewrite (@Memory.split_o prom_tgt' prom_tgt); eauto.
            des_ifs; des; ss; clarify; eauto.
            { ss. destruct a. clarify. esplits; eauto. }
            { exfalso. auto. }
            { esplits; eauto. }
        + eapply reserve_future_wf_pasts_memory; eauto.
      }
      { exploit COMPLETE; eauto. i. des.
        exploit NFORGET; eauto. i. des. des_ifs; des; clarify.
        exploit split_reserve_exists; try apply GETSRC; eauto. i. des.
        exists (fun loc' to' => prom_self loc' to' \/ (loc' = loc /\ to' = to)), prom2, mem2.
        splits; auto.
        + econs.
          * ii. erewrite Memory.split_o in GETTGT0; eauto. erewrite SPLITMEM; eauto.
            des_ifs; ss.
            { des; clarify. exfalso. auto. }
            exploit COMPLETE0; eauto. ii. apply NPROMS. des; auto.
          * i. eapply concrete_promised_increase_promise; eauto.
            apply CONCRETE. eapply reserve_future_concrete_promised; eauto.
          * i. erewrite split_covered; cycle 1; eauto. apply COVERED.
            inv COVERED0. rewrite SPLITMEM in GET. des_ifs; des; ss; clarify; econs; eauto.
            { inv ITV. econs; eauto. ss. etrans; eauto. left. auto. }
            { inv ITV. econs; eauto. }
        + ii. erewrite SPLITMEM in GET. des_ifs. guardH o. guardH o0.
          ss. exploit ATTACH; cycle 1; eauto. des; auto. clarify. exfalso.
          exploit memory_get_ts_strong; try apply GET. i. des; clarify.
          { unguard. des; auto. }
          exfalso. exploit Memory.get_disjoint.
          * apply GET.
          * apply WFSRC. apply GETSRC.
          * i. des; clarify. specialize (x0 (Time.meet to' ts3)).
            unfold Time.meet in *. des_ifs.
            { eapply x0; eauto; econs; ss.
              - refl.
              - etrans; eauto. }
            { eapply x0; eauto; econs; ss.
              - left. auto.
              - etrans; eauto.
              - refl. }
        + econs.
          * i. erewrite SPLITPROM in GETSRC0; eauto.
            erewrite Memory.split_o; eauto.
            destruct (loc_ts_eq_dec (loc0, to0) (loc, to)); clarify.
            { ss. des; clarify. exfalso. auto. }
            destruct (loc_ts_eq_dec (loc0, to0) (loc, ts3)); clarify.
            { ss. des; clarify. eauto. }
            exploit NFORGET; eauto.
          * i. erewrite Memory.split_o in GETTGT0; eauto.
            erewrite SPLITPROM.
            des_ifs; clarify; eauto.
          * i. apply or_comm in PROM. apply or_strengthen in PROM.
            erewrite SPLITPROM; eauto.
            erewrite (@Memory.split_o prom_tgt' prom_tgt); eauto.
            des_ifs; des; ss; clarify; eauto.
            { ss. destruct a. clarify. esplits; eauto. }
            { exfalso. auto. }
        + eapply reserve_future_wf_pasts_memory; eauto.
      }

    - dup PROMISES. apply lower_succeed_wf in PROMISES0. des. clarify. inv MSG_LE.
      assert (PROM: prom_self loc to).
      { exploit COMPLETE; eauto. i. des.
        apply NNPP. ii. exploit NFORGET; eauto. i. des. des_ifs. des. clarify. }
      exploit FORGET; eauto. i. des.
      exists prom_self, prom_src, mem_src. esplits; eauto.
      + econs.
        * ii. erewrite Memory.lower_o in GETTGT0; eauto.
          des_ifs; ss.
          { des; clarify. exfalso. apply NPROMS. auto. }
          exploit COMPLETE0; eauto.
        * i. eapply concrete_promised_increase_promise; eauto.
        * i. eapply lower_covered; eauto.
      + econs.
        * i. erewrite Memory.lower_o; eauto.
          destruct (loc_ts_eq_dec (loc0, to0) (loc, to)); clarify.
          { ss. des; clarify. }
          guardH o. exploit NFORGET; eauto.
        * i. erewrite Memory.lower_o in GETTGT0; eauto.
          des_ifs; clarify.
          { ss. des. clarify. eauto. }
          { guardH o. exploit COMPLETE; eauto. }
        * i. erewrite (@Memory.lower_o prom_tgt' prom_tgt); eauto. des_ifs; eauto.
          exploit FORGET; eauto. i. des. ss. clarify. esplits; eauto.

    - dup PROMISES. apply Memory.remove_get0 in PROMISES0. des.
      exploit COMPLETE; eauto. i. des. exploit NFORGET; eauto.
      { ii. exploit FORGET; eauto. i. des. rewrite GET in GETTGT. clarify. }
      i. des. rewrite GETTGT in *. clarify. des_ifs; des; clarify.
      exploit Memory.remove_exists.
      { eapply GETSRC. } i. des.
      exploit Memory.remove_exists_le; try apply x0; eauto. i. des.
      assert (FUTURE: reserve_future_memory prom_src mem_src mem2 mem0).
      { econs.
        - econs 4; eauto.
        - econs 1. }
      exists prom_self, mem2, mem0. splits; auto.
      + econs.
        * ii. erewrite Memory.remove_o in GETTGT0; eauto. erewrite Memory.remove_o; eauto.
          des_ifs. guardH o. exploit COMPLETE0; eauto.
        * i. eapply concrete_promised_increase_promise; eauto.
          apply CONCRETE. eapply reserve_future_concrete_promised; eauto.
        * i. erewrite remove_covered in COVERED0; eauto.
          eapply remove_covered; eauto. des; split; auto.
      + ii. erewrite Memory.remove_o in GET; eauto. des_ifs.
        eapply ATTACH; eauto.
      + econs.
        * i. erewrite Memory.remove_o in GETSRC0; eauto.
          erewrite Memory.remove_o; eauto.
          destruct (loc_ts_eq_dec (loc0, to0) (loc, to)); clarify. guardH o.
          exploit NFORGET; eauto.
        * i. erewrite Memory.remove_o in GETTGT0; eauto.
          erewrite Memory.remove_o; try eassumption.
          des_ifs; clarify. guardH o.
          exploit COMPLETE; eauto.
        * i. erewrite (@Memory.remove_o mem2 prom_src); eauto.
          erewrite (@Memory.remove_o prom_tgt' prom_tgt); eauto. des_ifs; eauto.
          exploit FORGET; eauto. i. des. ss. clarify.
      + eapply reserve_future_wf_pasts_memory; eauto.
        Unshelve. all: auto.
  Admitted.

  Lemma sim_remove_step_forget prom_self prom_others pasts mem_src mem_tgt rel_src rel_tgt prom_src prom_tgt
        loc from_tgt from_src to prom_tgt' val released_tgt released_src
        (NLOC: L loc)
        (REMOVEPROM: Memory.remove prom_tgt loc from_tgt to (Message.concrete val released_tgt) prom_tgt')
        (MEM: sim_memory (prom_others \2/ prom_self) mem_src mem_tgt)
        (ATTACH: not_attached (prom_others \2/ prom_self) mem_src)
        (MEMSRC: Memory.closed mem_src)
        (MEMTGT: Memory.closed mem_tgt)
        (WFSRC: Memory.le prom_src mem_src)
        (WFTGT: Memory.le prom_tgt mem_tgt)
        (RELSRC: forall (loc: Loc.t), Memory.closed_view (rel_src loc) mem_src)
        (RELTGT: forall (loc: Loc.t), Memory.closed_view (rel_tgt loc) mem_src)
        (PROMISE: sim_promise prom_self pasts rel_src rel_tgt prom_src prom_tgt)
        (PAST: wf_pasts_memory mem_src pasts)
        (FROM: Time.le from_tgt from_src)
        (TO: Time.lt from_src to)
        (RELEASEDWF: View.opt_wf released_src)
        (RELEASEDLE: View.opt_le released_src released_tgt)
        (RELEASEDCLOSED: Memory.closed_opt_view released_src mem_src)
        (NREAD: ~ (prom_others \2/ prom_self) loc from_src)
        (OTHERS: forall loc to, prom_others loc to -> prom_self loc to -> False)
    :
      exists prom_mid mem_mid prom_self' pasts' prom_src' mem_src',
        (<<FUTURE: reserve_future_memory prom_src mem_src prom_mid mem_mid>>) /\
        (<<WRITETGT: Memory.write prom_mid mem_mid loc from_src to val released_src prom_src' mem_src' Memory.op_kind_add>>) /\
        (<<MEM: sim_memory (prom_others \2/ prom_self') mem_src' mem_tgt>>) /\
        (<<ATTACH: not_attached (prom_others \2/ prom_self') mem_src'>>) /\
        (<<PROMISE: sim_promise prom_self' pasts' rel_src rel_tgt prom_src' prom_tgt'>>) /\
        (<<PAST: wf_pasts_memory mem_src' pasts'>>) /\
        (<<PASTLE: pasts_le pasts pasts'>>)
  .
  Proof.
    inv PROMISE. inv MEM.
    exploit Memory.remove_get0; eauto. i. des.
    assert (PROM: prom_self loc to).
    { exploit COMPLETE; eauto. i. des.
      apply NNPP. ii. exploit NFORGET; eauto. i. des. des_ifs. des. clarify. }
    exploit FORGET; eauto. i. des.
    i. des. rewrite GETTGT in *. clarify. des_ifs; des; clarify.
    exploit Memory.remove_exists.
    { eapply GETSRC. } i. des.
    exploit Memory.remove_exists_le; try apply x0; eauto. i. des.
    assert (FUTURE: reserve_future_memory prom_src mem_src mem2 mem0).
    { econs.
      - econs 4; eauto.
      - econs 1. }

    exploit Memory.add_exists.
    { instantiate (2:=from_src).
      ii. erewrite Memory.remove_o in GET2; eauto. des_ifs.
      exploit Memory.get_disjoint.
      - apply GET2.
      - apply WFSRC. apply GETSRC.
      - i. ss. des; clarify. eapply x3; eauto.
        inv LHS. econs; eauto. ss. eapply TimeFacts.le_lt_lt; eauto. }
    { apply TO. }
    { econs 1. apply RELEASEDWF. } intros [mem_src' ADDMEM].
    exploit Memory.add_exists_le.
    { instantiate (1:=mem0). instantiate (1:=mem2).
      ii. erewrite Memory.remove_o; eauto.
      erewrite Memory.remove_o in LHS; cycle 1; eauto. des_ifs. auto. }
    { eapply ADDMEM. } intros [prom_mid' ADDPROM].
    exploit Memory.remove_exists.
    { eapply Memory.add_get0. apply ADDPROM. } intros [prom_src' REMOVEPROMSRC].
    exists mem2, mem0, (fun loc' to' => prom_self loc' to' /\ (loc' <> loc \/ to' <> to)),
    (fun loc' to' => if loc_ts_eq_dec (loc', to') (loc, to) then Some mem_src else pasts loc' to'), prom_src', mem_src'.
    exploit MemoryFacts.add_remove_eq.
    { apply ADDPROM. }
    { apply REMOVEPROMSRC. } i. clarify.

    assert (PROMISESRC: Memory.promise mem2 mem0 loc from_src to (Message.concrete val released_src) prom_mid' mem_src' Memory.op_kind_add).
    { econs; eauto.
      - econs. etrans.
        + apply View.unwrap_opt_le in RELEASEDLE.
          inv RELEASEDLE. apply RLX.
        + inv MEMTGT. apply WFTGT in GETTGT.
          eapply CLOSED in GETTGT. des. inv MSG_TS. auto.
      - i. destruct msg'; cycle 1.
        { admit. }
        clarify. erewrite Memory.remove_o in GET; eauto. des_ifs.
        exploit ATTACH; eauto.
    }

    assert (FUTUREMEM: Memory.future mem_src mem_src').
    { etrans.
      - eapply reserve_future_future; eauto.
      - econs; [|refl]. econs.
        + econs. apply ADDMEM.
        + econs; eauto.
          eapply Memory.promise_closed_opt_view; cycle 1.
          { apply PROMISESRC. }
          eapply Memory.promise_closed_opt_view; eauto.
        + econs. etrans.
          * apply View.unwrap_opt_le in RELEASEDLE.
            inv RELEASEDLE. apply RLX.
          * inv MEMTGT. apply WFTGT in GETTGT.
            eapply CLOSED in GETTGT. des. inv MSG_TS. auto.
    }

    splits; auto.
    - econs; eauto.
    - econs; eauto.
      + i. erewrite Memory.add_o; eauto. erewrite Memory.remove_o; eauto. des_ifs.
        * ss. des; clarify. apply WFTGT in GETTGT. clarify.
          esplits; eauto.
        * exploit COMPLETE0.
          { ii. apply NPROMS. des; eauto. }
          { eauto. }
          i. guardH o. des. esplits; eauto.
      + i. inv PR. erewrite Memory.add_o in GET; eauto. des_ifs.
        * ss. des; clarify. econs; eauto.
        * eapply CONCRETE; eauto. erewrite Memory.remove_o in GET; eauto.
          des_ifs. econs; eauto.
      + i. rewrite add_covered in COVERED0; eauto.
        rewrite remove_covered in COVERED0; eauto. apply COVERED.
        apply or_comm in COVERED0. apply or_strengthen in COVERED0. des; clarify; auto.
        econs; eauto. inv COVERED1. econs; ss. eapply TimeFacts.le_lt_lt; eauto.
    - ii.
      erewrite Memory.add_o in GET; eauto.
      erewrite Memory.remove_o in GET; eauto. des_ifs.
      + ss. destruct a; clarify.
        apply NREAD. des; auto.
      + eapply ATTACH; cycle 1; eauto. des; auto.

    - econs; eauto.
      + i. erewrite Memory.remove_o in GETSRC0; try apply x0; eauto.
        erewrite Memory.remove_o; eauto. des_ifs; ss.
        * exploit NFORGET; try apply GETSRC0; eauto.
        * exploit NFORGET; try apply GETSRC0; eauto.
      + i. erewrite Memory.remove_o; try apply x0; eauto.
        erewrite Memory.remove_o in GETTGT0; cycle 1; eauto. des_ifs.
        exploit COMPLETE; eauto.
      + i. erewrite (@Memory.remove_o mem2 prom_src); eauto.
        erewrite (@Memory.remove_o prom_tgt' prom_tgt); eauto. des_ifs.
        * ss. des; clarify.
        * ss. eapply FORGET. des; auto.

    - inv PAST. econs.
      + ii. erewrite Memory.add_o in GET; eauto.
        erewrite Memory.remove_o in GET; eauto.
        destruct (loc_ts_eq_dec (loc0, to0) (loc, to)); ss.
        * des; clarify. esplits; eauto. des_ifs.
          { ss. des; clarify. exfalso. eapply Time.lt_strorder. eauto. }
          { guardH o. i. apply ONLY in PAST. des. auto. }
        * guardH o. exploit COMPLETE1; eauto. i. des. esplits; eauto.
          i. des_ifs.
          { ss. des; clarify. unguard.
            exfalso. exploit ATTACH; eauto. }
          { exploit ONLY; eauto. }
      + ii. des_ifs.
        * ss. des; clarify. splits; auto.
          { econs; eauto. eapply Memory.add_get0; eauto. }
          { apply Memory.future_future_weak; eauto. }
        * guardH o.
          apply ONLY in PAST. des. splits; auto.
          { eapply concrete_promised_increase_promise; eauto.
            eapply concrete_promised_increase_promise; eauto. }
          { etrans; eauto. eapply Memory.future_future_weak. auto. }
    - ii. des_ifs; eauto. ss. des; clarify.
      inv PAST. eapply ONLY in PAST0. des.
      inv CONCRETE0. apply WFSRC in GETSRC. clarify.
  Admitted.

  Lemma sim_write_step_forget prom_self prom_others pasts lc_src lc_tgt sc_src sc_tgt mem_src mem_tgt
        lc_tgt' sc_tgt' mem_tgt' loc from_tgt to val None released_tgt ord kind
        (NLOC: L loc)
        (STEPTGT: Local.write_step lc_tgt sc_tgt mem_tgt loc from_tgt to val None released_tgt ord lc_tgt' sc_tgt' mem_tgt' kind)
        (SC: TimeMap.le sc_src sc_tgt)
        (MEM: sim_memory (prom_others \2/ prom_self) mem_src mem_tgt)
        (ATTACH: not_attached (prom_others \2/ prom_self) mem_src)
        (SCSRC: Memory.closed_timemap sc_src mem_src)
        (SCTGT: Memory.closed_timemap sc_tgt mem_tgt)
        (MEMSRC: Memory.closed mem_src)
        (MEMTGT: Memory.closed mem_tgt)
        (LOCALSRC: Local.wf lc_src mem_src)
        (LOCALTGT: Local.wf lc_tgt mem_tgt)
        (SIM: sim_local prom_self pasts lc_src lc_tgt)
        (PAST: wf_pasts_memory mem_src pasts)
    :
      exists prom_self' prom_src mem_src_mid pasts' lc_src' sc_src' mem_src' from_src released_src,
        (<<FUTURE: reserve_future_memory lc_src.(Local.promises) mem_src prom_src mem_src_mid>>) /\
        (<<STEPSRC: Local.write_step (Local.mk lc_src.(Local.tview) prom_src) sc_src mem_src loc from_src to val None released_src ord lc_src' sc_src' mem_src' kind>>) /\
        (<<MEM: sim_memory (prom_others \2/ prom_self') mem_src' mem_tgt'>>) /\
        (<<ATTACH: not_attached (prom_others \2/ prom_self') mem_src'>>) /\
        (<<SC: TimeMap.le sc_src' sc_tgt'>>) /\
        (<<SIM: sim_local prom_self' pasts' lc_src' lc_tgt'>>) /\
        (<<PAST: wf_pasts_memory mem_src' pasts'>>) /\
        (<<PASTLE: pasts_le pasts pasts'>>)
  (* TODO: condition about event *)
  .
  Proof.
  Admitted.

  Lemma sim_thread_step prom_self prom_others pasts lang st lc_src lc_tgt sc_src sc_tgt mem_src mem_tgt pf e_tgt
        st' lc_tgt' sc_tgt' mem_tgt'
        (STEPTGT: @Thread.step lang pf e_tgt (Thread.mk _ st lc_tgt sc_tgt mem_tgt) (Thread.mk _ st' lc_tgt' sc_tgt' mem_tgt'))
        (NOREAD: no_read_msgs (prom_others \2/ prom_self) e_tgt)
        (SC: TimeMap.le sc_src sc_tgt)
        (MEM: sim_memory (prom_others \2/ prom_self) mem_src mem_tgt)
        (ATTACH: not_attached (prom_others \2/ prom_self) mem_src)
        (SCSRC: Memory.closed_timemap sc_src mem_src)
        (SCTGT: Memory.closed_timemap sc_tgt mem_tgt)
        (MEMSRC: Memory.closed mem_src)
        (MEMTGT: Memory.closed mem_tgt)
        (LOCALSRC: Local.wf lc_src mem_src)
        (LOCALTGT: Local.wf lc_tgt mem_tgt)
        (SIM: sim_local prom_self pasts lc_src lc_tgt)
        (PAST: wf_pasts_memory mem_src pasts)
    :
      exists tr prom_self' pasts' lc_src' sc_src' mem_src',
        (<<STEPSRC: Trace.steps tr (Thread.mk _ st lc_src sc_src mem_src) (Thread.mk _ st' lc_src' sc_src' mem_src')>>) /\
        (<<MEM: sim_memory (prom_others \2/ prom_self') mem_src' mem_tgt'>>) /\
        (<<ATTACH: not_attached (prom_others \2/ prom_self') mem_src'>>) /\
        (<<SC: TimeMap.le sc_src' sc_tgt'>>) /\
        (<<SIM: sim_local prom_self' pasts' lc_src' lc_tgt'>>) /\
        (<<PAST: wf_pasts_memory mem_src' pasts'>>) /\
        (<<PASTLE: pasts_le pasts pasts'>>)
          (* TODO: condition about event *)
  .
  Proof.
  Admitted.

  Lemma sim_promise_step_normal prom_self prom_others pasts mem_src mem_tgt rel_src rel_tgt prom_src prom_tgt
        loc from to msg_tgt prom_tgt' mem_tgt' kind
        (NLOC: ~ L loc)
        (STEPTGT: Memory.promise prom_tgt mem_tgt loc from to msg_tgt prom_tgt' mem_tgt' kind)
        (MEM: sim_memory (prom_others \2/ prom_self) mem_src mem_tgt)
        (ATTACH: not_attached (prom_others \2/ prom_self) mem_src)
        (MEMSRC: Memory.closed mem_src)
        (MEMTGT: Memory.closed mem_tgt)
        (WFSRC: Memory.le prom_src mem_src)
        (WFTGT: Memory.le prom_tgt mem_tgt)
        (RELSRC: forall (loc: Loc.t), Memory.closed_view (rel_src loc) mem_src)
        (RELTGT: forall (loc: Loc.t), Memory.closed_view (rel_tgt loc) mem_src)
        (PROMISE: sim_promise prom_self pasts rel_src rel_tgt prom_src prom_tgt)
        (PAST: wf_pasts_memory mem_src pasts)
        (MSGTGT: Memory.closed_message msg_tgt mem_tgt')
    :
      exists msg_src pasts' prom_src' mem_src',
        (<<STEPTGT: Memory.promise prom_src mem_src loc from to msg_src prom_src' mem_src' kind>>) /\
        (<<MSGSRC: Memory.closed_message msg_src mem_src'>>) /\
        (<<MEM: sim_memory (prom_others \2/ prom_self) mem_src' mem_tgt'>>) /\
        (<<ATTACH: not_attached (prom_others \2/ prom_self) mem_src'>>) /\
        (<<PROMISE: sim_promise prom_self pasts' rel_src rel_tgt prom_src' prom_tgt'>>) /\
        (<<PAST: wf_pasts_memory mem_src' pasts'>>) /\
        (<<PASTLE: pasts_le pasts pasts'>>)
  .
  Proof.
    exploit sim_message_exists.
    { eapply MEMSRC. }
    instantiate (1:=msg_tgt). i. des.

    inv PROMISE. inv MEM. dup STEPTGT. inv STEPTGT.
    - dup MEM. apply add_succeed_wf in MEM0. des.
      exploit Memory.add_exists; try apply TO1.
      { instantiate (1:=mem_src). instantiate (1:=loc). ii.
        exploit COVERED.
        { econs; eauto. } i. inv x0.
        eapply DISJOINT; eauto. }
      { instantiate (1:=msg_src). admit. (* Message.wf *) } intros [mem_src' ADDMEM].
      exploit Memory.add_exists_le; try apply ADDMEM; eauto. intros [prom_src' ADDPROM].
      exists msg_src. inv SIM.

      { exists (fun loc' to' => if loc_ts_eq_dec (loc', to') (loc, to) then Some mem_src else pasts loc' to')
        , prom_src', mem_src'.
        splits; auto.
        - econs; eauto.
          + econs; eauto.
            apply sim_opt_view_le in SIM0.
            apply View.unwrap_opt_le in SIM0.
            inv SIM0. inv TS. etrans; eauto.
          + i. clarify.
            admit.
        - econs.
          admit. (* Memory.closed_opt_view released_src mem_src' *)
        - econs.
          + i. erewrite Memory.add_o in GETTGT; eauto.
            erewrite Memory.add_o; eauto. des_ifs.
            * ss; des; clarify. esplits; eauto.
              eapply sim_opt_view_le; eauto.
            * exploit COMPLETE0; eauto.
          + i. inv PR. erewrite Memory.add_o in GET; eauto. des_ifs.
            * ss. des; clarify. econs.
              eapply Memory.add_get0; eauto.
            * exploit CONCRETE; eauto.
              { econs; eauto. } i. inv x.
              eapply Memory.add_get1 in GET0; eauto. econs; eauto.
          + i. erewrite add_covered in COVERED0; eauto.
            erewrite add_covered; cycle 1; eauto. des; auto.
        - ii.
          admit. (* change it *)
        - econs.
          + i. erewrite Memory.add_o in GETSRC; eauto.
            erewrite Memory.add_o; eauto.
            destruct (loc_ts_eq_dec (loc0, to0) (loc, to)); eauto.
            ss. des; clarify. esplits; eauto.
          + i. erewrite Memory.add_o in GETTGT; eauto.
            erewrite Memory.add_o; cycle 1; eauto. des_ifs; eauto.
          + i. erewrite (@Memory.add_o prom_src'); eauto.
            erewrite (@Memory.add_o prom_tgt'); eauto. des_ifs.
            * ss. des; clarify. exfalso.
              exploit FORGET; eauto. i. des. clarify.
            * exploit FORGET; eauto.
        - inv PAST. econs.
          + ii. erewrite Memory.add_o in GET; eauto.
            destruct (loc_ts_eq_dec (loc0, to0) (loc, to)).
            * ss. des; clarify. esplits; eauto.
              { admit. (* Memory.closed_opt_view released mem_src *) }
              { i. des_ifs.
                - ss. des; clarify. refl.
                - guardH o. apply ONLY in PAST. des. auto. }
            * guardH o. exploit COMPLETE1; eauto. i. des.
              esplits; eauto. i. des_ifs.
              { ss. des; clarify. exfalso.
                exploit ATTACH0; eauto.
                admit. }
              { ss. exploit COMPLETE1; eauto. }
          + i. des_ifs.
            * ss. des; clarify. esplits; eauto.
              { econs. eapply Memory.add_get0. eauto. }
              { apply Memory.future_future_weak.
                admit. }
            * guardH o. exploit ONLY; eauto. i. des. splits; auto.
              { inv CONCRETE0. eapply Memory.add_get1 in GET; eauto. econs; eauto. }
              { etrans; eauto.
                admit. }
        - ii. des_ifs. ss. des; clarify. exfalso.
          inv PAST. exploit ONLY; eauto. i. des. inv CONCRETE0.
          apply Memory.add_get0 in ADDMEM. des. clarify.
      }

      { exists pasts, prom_src', mem_src'.
        splits; auto.
        - econs; eauto. i. clarify.
        - econs.
          + i. erewrite Memory.add_o in GETTGT; eauto.
            erewrite Memory.add_o; eauto. des_ifs.
            exploit COMPLETE0; eauto.
          + i. inv PR. erewrite Memory.add_o in GET; eauto. des_ifs.
            exploit CONCRETE; eauto.
            { econs; eauto. } i. inv x.
            eapply Memory.add_get1 in GET0; eauto. econs; eauto.
          + i. erewrite add_covered in COVERED0; eauto.
            erewrite add_covered; cycle 1; eauto. des; auto.
        - ii.
          admit. (* change it *)
        - econs.
          + i. erewrite Memory.add_o in GETSRC; eauto.
            erewrite Memory.add_o; eauto.
            destruct (loc_ts_eq_dec (loc0, to0) (loc, to)); eauto.
            ss. des; clarify. esplits; eauto.
          + i. erewrite Memory.add_o in GETTGT; eauto.
            erewrite Memory.add_o; cycle 1; eauto. des_ifs; eauto.
          + i. erewrite (@Memory.add_o prom_src'); eauto.
            erewrite (@Memory.add_o prom_tgt'); eauto. des_ifs.
            * ss. des; clarify. exfalso.
              exploit FORGET; eauto. i. des. clarify.
            * exploit FORGET; eauto.
        - inv PAST. econs.
          + ii. erewrite Memory.add_o in GET; eauto.
            destruct (loc_ts_eq_dec (loc0, to0) (loc, to)).
            * ss.
            * guardH o. exploit COMPLETE1; eauto.
          + i. exploit ONLY; eauto. i. des. splits; auto.
            * inv CONCRETE0. eapply Memory.add_get1 in GET; eauto. econs; eauto.
            * etrans; eauto.
              apply Memory.future_future_weak. econs; [|refl]. econs; eauto.
        - refl.
      }

    - dup PROMISES. apply split_succeed_wf in PROMISES0. des. clarify.
      exploit COMPLETE; eauto. i. des.
      exploit NFORGET; eauto.
      { ii. exploit FORGET; eauto. i. des. clarify. } i. des. des_ifs.

      { des. clarify.
        exploit Memory.split_exists.
  Admitted.

End SIM.
