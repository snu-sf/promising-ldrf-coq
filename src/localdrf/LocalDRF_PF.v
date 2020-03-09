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

  Variable L: Loc.t -> Prop.

  Definition valid_event (e: ThreadEvent.t): Prop :=
    forall loc from to msg kind (PROMISE: e = ThreadEvent.promise loc from to msg kind) (LOC: L loc),
      msg = Message.reserve.

  Definition valid_step (e: MachineEvent.t) (tid: Ident.t)
             (c0 c1: Configuration.t): Prop :=
    exists lang (tr: Trace.t lang),
      (<<STEP: Trace.configuration_step tr e tid c0 c1>>) /\
      (<<VALID: List.Forall (compose valid_event snd) tr>>).

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
    forall c0 c1 c2 c3
           loc ts
           tid0 lang0 (th0: Thread.t lang0) e0 tr0 me0
           tid1 lang1 (th1: Thread.t lang1) e1 tr1 me1

           (CSTEPS0: rtc (step_all valid_step) (Configuration.init s) c0)

           (CSTEP0: Trace.configuration_step tr0 me0 tid0 c0 c1)
           (VALID0: List.Forall (compose valid_event snd) tr0)
           (EVENT0: List.In (th0, e0) tr0)
           (WRITE: racy_write loc ts th0 e0)

           (CSTEPS1: rtc (step_all valid_step) c1 c2)

           (CSTEP1: Trace.configuration_step tr1 me1 tid1 c2 c3)
           (VALID1: List.Forall (compose valid_event snd) tr1)
           (EVENT1: List.In (th1, e1) tr1)
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

  Variable L: Loc.t -> Prop.

  Inductive sim_memory P mem_src mem_tgt : Prop :=
  | sim_memory_intro
      (COMPLETE: forall loc ts from_tgt val released_tgt (NPROMS: ~ P loc ts)
                        (GETTGT: Memory.get loc ts mem_tgt = Some (from_tgt, Message.concrete val released_tgt)),
          exists from_src released_src,
            (<<GETSRC: Memory.get loc ts mem_src = Some (from_src, Message.concrete val released_src)>>) /\
            (<<RELEASED: View.opt_le released_src released_tgt>>))
      (CONCRETE: concrete_promised mem_src <2= concrete_promised mem_tgt)
      (COVERED: forall loc ts (COVERED: covered loc ts mem_src), covered loc ts mem_tgt)
      (MAXTS: forall loc, Memory.max_ts loc mem_src = Memory.max_ts loc mem_tgt)
  .

  Definition all_pasts_memory (mem: Memory.t) (pasts: Loc.t -> Time.t -> option Memory.t): Prop :=
    forall loc from to val released
           (GET: Memory.get loc to mem = Some (from, Message.concrete val released)),
    exists past,
      (<<PAST: pasts loc to = Some past>>) /\
      (<<GET: Memory.closed_opt_view released past>>) /\
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

  Inductive sim_timemap (past: Memory.t) (tm_src tm_tgt: TimeMap.t): Prop :=
  | sim_timemap_intro
      (IN: forall loc (LOC: ~ L loc), tm_src loc = tm_tgt loc)
      (NIN: forall loc (LOC: L loc),
          (<<GREATEST:
             forall ts
                    (PAST: concrete_promised past loc ts)
                    (LE: Time.le ts (tm_tgt loc)),
               Time.le ts (tm_src loc)>>) /\
          (<<CLOSED: concrete_promised past loc (tm_src loc)>>) /\
          (<<TLE: Time.le (tm_src loc) (tm_tgt loc)>>)
      )
  .

  Lemma sim_timemap_le past tm_src tm_tgt
        (SIM: sim_timemap past tm_src tm_tgt)
    :
      TimeMap.le tm_src tm_tgt.
  Proof.
    ii. inv SIM. destruct (classic (L loc)) as [LOC|NLOC].
    - apply NIN. auto.
    - right. apply IN. auto.
  Qed.

  Lemma sim_timemap_exists past tm_tgt
        (CLOSED: Memory.closed past)
    :
      exists tm_src, <<SIM: sim_timemap past tm_src tm_tgt>>.
  Proof.
    exploit (@choice _ _ (fun loc ts_src =>
                            (<<IN: forall (LOC: ~ L loc), ts_src = tm_tgt loc>>) /\
                            (<<NIN: forall (LOC: L loc),
                                (<<GREATEST:
                                   forall ts
                                          (PAST: concrete_promised past loc ts)
                                          (LE: Time.le ts (tm_tgt loc)),
                                     Time.le ts ts_src>>) /\
                                (<<CLOSED: concrete_promised past loc ts_src>>) /\
                                (<<TLE: Time.le ts_src (tm_tgt loc)>>)>>))).
    - intros loc. destruct (classic (L loc)) as [LOC|NLOC].
      + hexploit (cell_elements_greatest (past loc) (fun ts => concrete_promised past loc ts /\ Time.le ts (tm_tgt loc))).
        i. des.
        * exists to. split; clarify. ii. splits; auto.
          i. dup PAST. inv PAST. exploit GREATEST; eauto.
        * exfalso. inv CLOSED. eapply EMPTY; eauto. split.
          { econs; eauto. }
          { eapply Time.bot_spec. }
      + esplits; clarify.
    - intros [f FSPEC]. des. exists f. econs; i.
      + eapply FSPEC; eauto.
      + hexploit (FSPEC loc); eauto. i. des. exploit NIN; eauto.
  Qed.

  Inductive sim_view (past: Memory.t) (view_src view_tgt: View.t): Prop :=
  | sim_view_intro
      (PLN: sim_timemap past view_src.(View.pln) view_tgt.(View.pln))
      (RLX: sim_timemap past view_src.(View.rlx) view_tgt.(View.rlx))
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

  (* Inductive sim_message (past: Memory.t): forall (msg_src msg_tgt: Message.t), Prop := *)
  (* | sim_message_concrete *)
  (*     val released_src released_tgt *)
  (*     (SIM: sim_opt_view past released_src released_tgt): *)
  (*     sim_message past (Message.concrete val released_src) (Message.concrete val released_tgt) *)
  (* | sim_message_reserve: *)
  (*     sim_message past Message.reserve Message.reserve *)
  (* . *)
  (* Hint Constructors sim_message. *)

  (* Lemma sim_message_exists past msg_tgt *)
  (*       (CLOSED: Memory.closed past) *)
  (*   : *)
  (*     exists msg_src, <<SIM: sim_message past msg_src msg_tgt>>. *)
  (* Proof. *)
  (*   destruct msg_tgt. *)
  (*   - exploit sim_opt_view_exists; eauto. i. des. *)
  (*     esplits. econs; eauto. *)
  (*   - esplits; eauto. *)
  (* Qed. *)

  Inductive sim_promise P (pasts: Loc.t -> Time.t -> option Memory.t)
            (rel_src rel_tgt: LocFun.t View.t) (prom_src prom_tgt: Memory.t): Prop :=
  | sim_promise_intro
      (NFORGET: forall loc to from msg_src
                       (NPROM: ~ P loc to)
                       (GETSRC: Memory.get loc to prom_src = Some (from, msg_src)),
          exists msg_tgt,
            (<<GETTGT: Memory.get loc to prom_tgt = Some (from, msg_tgt)>>) /\
            (<<MESSAGE: match msg_src with
                        | Message.reserve => msg_tgt = Message.reserve
                        | Message.concrete val released_src =>
                          exists past released_tgt,
                          (<<PAST: pasts loc to = Some past>>) /\
                          (<<MESSAGE: msg_tgt = Message.concrete val released_tgt>>) /\
                          (<<RELEASED: sim_opt_view past released_src released_tgt>>) /\
                          (<<CLOSED: forall released' (MSG: released_src = Some released'),
                              Memory.closed_view (rel_src loc) past>>) /\
                          (<<NLOC: ~ L loc>>)
                        end>>))
      (COMPLETE: forall loc to from_tgt msg_tgt
                        (GETTGT: Memory.get loc to prom_tgt = Some (from_tgt, msg_tgt)),
          exists from_src msg_src,
            (<<GETSRC: Memory.get loc to prom_src = Some (from_src, msg_src)>>))
      (FORGET: forall loc to (PROM: P loc to),
          (<<LOC: L loc>>) /\
          exists from val released,
            (<<GETSRC: Memory.get loc to prom_src = Some (from, Message.reserve)>>) /\
            (<<GETTGT: Memory.get loc to prom_tgt = Some (from, Message.concrete val released)>>))
  .

  (* Inductive sim_promise P (pasts: Loc.t -> Time.t -> option Memory.t) *)
  (*           (rel_src rel_tgt: LocFun.t View.t) (prom_src prom_tgt: Memory.t): Prop := *)
  (* | sim_promise_intro *)
  (*     (NFORGET: forall loc to from msg_src *)
  (*                      (NPROM: ~ P loc to) *)
  (*                      (GETSRC: Memory.get loc to prom_src = Some (from, msg_src)), *)
  (*         exists past msg_tgt, *)
  (*           (<<PAST: pasts loc to = Some past>>) /\ *)
  (*           (<<GETTGT: Memory.get loc to prom_tgt = Some (from, msg_tgt)>>) /\ *)
  (*           (<<SIM: sim_message past msg_src msg_tgt>>) /\ *)
  (*           (<<CLOSED: forall val released (MSG: msg_src = Message.concrete val (Some released)), *)
  (*               Memory.closed_view (rel_src loc) past>>)) *)
  (*     (COMPLETE: forall loc to from_tgt msg_tgt *)
  (*                       (GETTGT: Memory.get loc to prom_tgt = Some (from_tgt, msg_tgt)), *)
  (*         exists from_src msg_src, *)
  (*           (<<GETSRC: Memory.get loc to prom_src = Some (from_src, msg_src)>>)) *)
  (*     (FORGET: forall loc to (PROM: P loc to), *)
  (*         exists from val released, *)
  (*           (<<GETSRC: Memory.get loc to prom_src = Some (from, Message.reserve)>>) /\ *)
  (*           (<<GETTGT: Memory.get loc to prom_tgt = Some (from, Message.concrete val released)>>)) *)
  (* . *)

  Inductive sim_local P (pasts: Loc.t -> Time.t -> option Memory.t) (lc_src lc_tgt: Local.t): Prop :=
  | forget_local_intro
      (TVIEW : TView.le lc_src.(Local.tview) lc_tgt.(Local.tview))
      (PROMS: sim_promise P pasts lc_src.(Local.tview).(TView.rel) lc_tgt.(Local.tview).(TView.rel) lc_src.(Local.promises) lc_tgt.(Local.promises))
    :
      sim_local P pasts lc_src lc_tgt
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

  Definition not_attached (P: Loc.t -> Time.t -> Prop) (mem: Memory.t) :=
    forall loc to (SAT: P loc to)
           val released to'
           (GET: Memory.get loc to' mem = Some (to, Message.concrete val released)), False
  .

  Inductive sim_config
            (proms: Ident.t -> Loc.t -> Time.t -> Prop)
            (pasts: Loc.t -> Time.t -> option Memory.t)
            (c_src c_tgt: Configuration.t)
    : Prop :=
  | sim_config_intro
      (THS: forall tid, option_rel
                          (sim_statelocal (proms tid) pasts)
                          (IdentMap.find tid c_src.(Configuration.threads))
                          (IdentMap.find tid c_tgt.(Configuration.threads)))
      (PAST: wf_pasts_memory c_src.(Configuration.memory) pasts)
      (MEM: sim_memory (all_promises proms) c_src.(Configuration.memory) c_tgt.(Configuration.memory))
      (SC: TimeMap.le c_src.(Configuration.sc) c_tgt.(Configuration.sc))
      (ATTACH: not_attached (all_promises proms) c_src.(Configuration.memory))
      (WFSRC: Configuration.wf c_src)
      (WFTGT: Configuration.wf c_tgt)
  (* TODO: can remove all promises *)
  .

  Lemma sim_read_step prom_self prom_others pasts lc_src lc_tgt mem_src mem_tgt loc to val released_tgt ord
        lc_tgt'
        (STEPTGT: Local.read_step lc_tgt mem_tgt loc to val released_tgt ord lc_tgt')
        (NOREAD: ~ (prom_others \2/ prom_self) loc to)
        (MEM: sim_memory (prom_others \2/ prom_self) mem_src mem_tgt)
        (SIM: sim_local prom_self pasts lc_src lc_tgt)
    :
      exists lc_src' released_src,
        (<<STEPTGT: Local.read_step lc_src mem_src loc to val released_src ord lc_src'>>) /\
        (<<SIM: sim_local prom_self pasts lc_src' lc_tgt'>>)
  .
  Proof.
    inv MEM. inv SIM. inv STEPTGT.
    hexploit COMPLETE; eauto. i. des. esplits.
    - econs; eauto. eapply TViewFacts.readable_mon; eauto.
      + eapply TVIEW.
      + refl.
    - econs; ss; eauto. eapply read_tview_mon; eauto. refl.
  Qed.

  Lemma sim_fence_step prom_self pasts lc_src lc_tgt sc_src sc_tgt ordr ordw
        sc_tgt' lc_tgt'
        (STEPTGT: Local.fence_step lc_tgt sc_tgt ordr ordw lc_tgt' sc_tgt')
        (SC: TimeMap.le sc_src sc_tgt)
        (SIM: sim_local prom_self pasts lc_src lc_tgt)
    :
      exists lc_src' sc_src',
        (<<STEPTGT: Local.fence_step lc_src sc_src ordr ordw lc_src' sc_src'>>) /\
        (<<SC: TimeMap.le sc_src' sc_tgt'>>) /\
        (<<SIM: sim_local prom_self pasts lc_src' lc_tgt'>>)
  .
  Proof.
    inv SIM. inv PROMS. inv STEPTGT.
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
      destruct (classic (prom_self loc t)) as [PROM|NPROM].
      { eapply FORGET in PROM. des. clarify. }
      eapply NFORGET in NPROM; eauto. des. des_ifs. des. clarify.
      inv RELEASED; auto. exploit RELEASE; eauto. ss.
    - eapply write_fence_fc_mon_same_ord; eauto.
      eapply read_fence_tview_mon_same_ord; eauto.
    - econs; ss; eauto. econs; ss. i.
      hexploit NFORGET; eauto. i. des. esplits; eauto.
      des_ifs; ss; des; clarify.
      + esplits; eauto. i. clarify. inv RELEASED.
        exploit RELEASE; eauto; ss. destruct ordw; eauto.
      + esplits; eauto. i. clarify. inv RELEASED.
        exploit RELEASE; eauto; ss. destruct ordw; eauto.
      + esplits; eauto. i. clarify. inv RELEASED.
        exploit RELEASE; eauto; ss. destruct ordw; eauto.
  Qed.

  Lemma sim_promise_consistent prom_self pasts lc_src lc_tgt
        (CONSISTENT: Local.promise_consistent lc_tgt)
        (SIM: sim_local prom_self pasts lc_src lc_tgt)
    :
      Local.promise_consistent lc_src.
  Proof.
    inv SIM. inv PROMS. ii.
    destruct (classic (prom_self loc ts)) as [PROM|NPROM].
    { eapply FORGET in PROM. des. clarify. }
    exploit NFORGET; eauto. i. des. clarify.
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

  Lemma sim_memory_max_ts P mem_src mem_tgt loc
        (CLOSEDSRC: Memory.closed mem_src)
        (SIM: sim_memory P mem_src mem_tgt)
    :
      Time.le (Memory.max_ts loc mem_src) (Memory.max_ts loc mem_tgt).
  Proof.
    inv SIM.
    exploit Memory.max_ts_spec.
    { apply CLOSEDSRC. }
    i. des. dup GET. apply memory_get_ts_strong in GET0. des; clarify.
    - rewrite GET1. apply Time.bot_spec.
    - exploit COVERED.
      + econs; eauto. econs; eauto. reflexivity.
      +  i. inv x. inv ITV. etrans; eauto. ss.
         eapply Memory.max_ts_spec; eauto.
  Qed.

  Lemma sim_memory_max_concrete_timemap P mem_src mem_tgt sc_src sc_tgt
        (SIM: sim_memory P mem_src mem_tgt)
        (SCSRC: Memory.max_concrete_timemap mem_src sc_src)
        (SCTGT: Memory.max_concrete_timemap mem_tgt sc_tgt)
    :
      TimeMap.le sc_src sc_tgt.
  Proof.
    inv SIM. ii. specialize (SCSRC loc). specialize (SCTGT loc).
    inv SCSRC. inv SCTGT. des.
    exploit CONCRETE.
    - econs. eapply GET.
    - i. inv x. eapply MAX0; eauto.
  Qed.

  Lemma sim_memory_cap P mem_src mem_tgt cap_src cap_tgt
        (SIM: sim_memory P mem_src mem_tgt)
        (CLOSEDSRC: Memory.closed mem_src)
        (CLOSEDTGT: Memory.closed mem_tgt)
        (CAPSRC: Memory.cap mem_src cap_src)
        (CAPTGT: Memory.cap mem_tgt cap_tgt)
    :
      sim_memory P cap_src cap_tgt.
  Proof.
    dup SIM. inv SIM. econs.
    - i. eapply Memory.cap_inv in GETTGT; eauto. des; clarify.
      apply COMPLETE in GETTGT; eauto. des.
      esplits; eauto. eapply Memory.cap_le; eauto. refl.
    - i. inv PR. eapply Memory.cap_inv in GET; try apply CAPSRC; eauto.
      des; clarify. exploit CONCRETE; eauto.
      + econs; eauto.
      + i. inv x. eapply Memory.cap_le in GET0.
        * econs; eauto.
        * eauto.
        * refl.
    - i. rewrite <- memory_cap_covered; eauto.
      rewrite <- memory_cap_covered in COVERED0; try apply CAPSRC; eauto.
      inv COVERED0. econs; eauto. ss. rewrite <- MAXTS. auto.
    - i. erewrite (@Memory.cap_max_ts mem_src cap_src); eauto.
      erewrite (@Memory.cap_max_ts mem_tgt cap_tgt); eauto.
      f_equal. auto.
  Qed.

  Lemma future_sim_promise P pasts0 pasts1 vw_src vw_tgt proms_src proms_tgt
        (SIM: sim_promise P pasts0 vw_src vw_tgt proms_src proms_tgt)
        (PASTLE: pasts_le pasts0 pasts1)
    :
      sim_promise P pasts1 vw_src vw_tgt proms_src proms_tgt.
  Proof.
    inv SIM. econs; eauto. i.
    apply NFORGET in GETSRC; auto. des. des_ifs; des; clarify.
    - esplits; eauto.
    - esplits; eauto.
  Qed.

  Lemma future_sim_local prom pasts0 pasts1 lc_src lc_tgt
        (SIM: sim_local prom pasts0 lc_src lc_tgt)
        (PASTLE: pasts_le pasts0 pasts1)
    :
      sim_local prom pasts1 lc_src lc_tgt.
  Proof.
    inv SIM. econs; eauto. eapply future_sim_promise; eauto.
  Qed.

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
      (HD: Memory.promise prom0 mem0 loc from to Message.reserve prom1 mem1 kind)
      (TL: reserve_future_memory prom1 mem1 prom2 mem2)
    :
      reserve_future_memory
        prom0 mem0 prom2 mem2
  .

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
      { instantiate (1:=mem_src).
        instantiate (1:=loc).
        admit. }
      { eapply Message.wf_reserve. } i. des.
      exploit Memory.add_exists_le; try apply x0; eauto. i. des.
      assert (FUTURE: reserve_future_memory prom_src mem_src promises2 mem2).
      { econs.
        - econs 1; eauto.
          { admit. (* will be removed *) }
          i. clarify.
        - econs 1. }
      destruct msg.
      { exists (fun loc' to' => prom_self loc' to' \/ (loc = loc' /\ to' = to)), promises2, mem2.
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
          * admit. (* change it *)
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
          * admit. (* change it *)
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
    - admit.
    - dup PROMISES. apply lower_succeed_wf in PROMISES0. des. clarify. inv MSG_LE.
      assert (PROM: prom_self loc to).
      { exploit COMPLETE; eauto. i. des.
        apply NNPP. ii. exploit NFORGET; eauto. i. des. des_ifs. des. clarify. }
      exploit FORGET; eauto. i. des.
      exists prom_self, prom_src, mem_src. esplits; eauto.
      + econs 1.
      + econs.
        * ii. erewrite Memory.lower_o in GETTGT0; eauto.
          des_ifs; ss.
          { des; clarify. exfalso. apply NPROMS. auto. }
          exploit COMPLETE0; eauto.
        * i. eapply concrete_promised_increase_promise; eauto.
        * i. eapply lower_covered; eauto.
        * admit. (* change it *)
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
        * admit. (* change it *)
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
  Admitted.

  Lemma sim_remove_step_forget prom_self prom_others pasts mem_src mem_tgt rel_src rel_tgt prom_src prom_tgt
        loc from to msg prom_tgt' mem_tgt'
        (NLOC: L loc)
        (REMOVEPROM: Memory.remove prom_tgt loc from to (Message.concrete val released) prom_tgt')
        (REMOVEMEM: Memory.remove mem_tgt loc from to msg mem_tgt')
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
        (<<FUTURE: Memory.write prom_src mem_src prom_src' mem_src'>>) /\
        (<<MEM: sim_memory (prom_others \2/ prom_self') mem_src' mem_tgt'>>) /\
        (<<ATTACH: not_attached (prom_others \2/ prom_self') mem_src'>>) /\
        (<<PROMISE: sim_promise prom_self' pasts rel_src rel_tgt prom_src' prom_tgt'>>) /\
        (<<PAST: wf_pasts_memory mem_src' pasts>>)
  .
  Proof.
Memory.write

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
    inv STEPTGT.

    Memory.promise

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
    inv STEPTGT.

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

End SIM.
