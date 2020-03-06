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

  Inductive sim_memory_content :
    option (Time.t * Message.t) -> option (Time.t * Message.t) -> Prop :=
  | sim_memory_content_some
      from_tgt from_src msg_src msg_tgt
      (FROM: Time.le from_tgt from_src)
      (MESSAGE: Message.le msg_src msg_tgt)
      (RESERVE: msg_tgt = Message.reserve -> msg_src = Message.reserve)
    :
      sim_memory_content
        (Some (from_src, msg_src))
        (Some (from_tgt, msg_tgt))
  | sim_memory_content_none
    :
      sim_memory_content None None
  .

  Inductive sim_memory P mem_src mem_tgt : Prop :=
  | sim_memory_intro
      (COMPLETE: forall l t (NPROMS: ~ P l t),
          sim_memory_content
            (Memory.get l t mem_src) (Memory.get l t mem_tgt))
      (FORGET: forall l t (PROMS: P l t),
          exists from msg,
            (<<SRCGET: Memory.get l t mem_src = Some (from, Message.reserve)>>) /\
            (<<TGTGET: Memory.get l t mem_tgt = Some (from, msg)>>))
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

  Inductive sim_promise P (pasts: Loc.t -> Time.t -> option Memory.t)
            (rel_src rel_tgt: LocFun.t View.t) (prom_src prom_tgt: Memory.t): Prop :=
  | sim_promise_intro
      (COMPLETE: forall loc to past from_src from_tgt val_src val_tgt released_src released_tgt
                        (PAST: pasts loc to = Some past)
                        (GETSRC: Memory.get loc to prom_src = Some (from_src, Message.concrete val_src released_src))
                        (GETTGT: Memory.get loc to prom_tgt = Some (from_tgt, Message.concrete val_tgt released_tgt))
        ,
          (<<SIM: sim_opt_view past released_src released_tgt>>) /\
          (<<CLOSED: forall (SOME: released_src <> None), Memory.closed_view (rel_src loc) past>>)
      )
      (MEMORY: sim_memory P prom_src prom_tgt)
      (NOPROMS: forall loc (LOC: L loc)
                       to from msg (GET: Memory.get loc to prom_src = Some (from, msg)), msg = Message.reserve)
  .

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
    hexploit COMPLETE; eauto. i. inv H; rewrite GET in *; clarify. inv MESSAGE. esplits.
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
    inv SIM. inv PROMS. inv MEMORY. inv STEPTGT.
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
      eapply COMPLETE0 in NPROM. rewrite GET in *. inv NPROM. clarify.
      exploit RELEASE; eauto. i. inv MESSAGE.
      + clarify. inv RELEASED. auto.
      + rewrite RESERVE; auto.
    - eapply write_fence_fc_mon_same_ord; eauto.
      eapply read_fence_tview_mon_same_ord; eauto.
    - econs; ss; eauto. econs; ss. i.
      destruct (classic (prom_self loc to)) as [PROM|NPROM].
      { eapply FORGET in PROM. des. clarify. }
      hexploit COMPLETE0; eauto. i.
      rewrite GETSRC in *. rewrite GETTGT in *. inv H; clarify. inv MESSAGE.
      inv TVIEWLE. ss. des_ifs; ss; eauto.
      + exploit RELEASE; eauto.
        { destruct ordw; eauto. }
        ss. i. clarify. ss. inv RELEASED. split; ss.
      + exploit RELEASE; eauto.
        { destruct ordw; eauto. }
        ss. i. clarify. ss. inv RELEASED. split; ss.
      + exploit RELEASE; eauto.
        { destruct ordw; eauto. }
        ss. i. clarify. ss. inv RELEASED. split; ss.
  Qed.

  Lemma sim_promise_consistent prom_self pasts lc_src lc_tgt
        (CONSISTENT: Local.promise_consistent lc_tgt)
        (SIM: sim_local prom_self pasts lc_src lc_tgt)
    :
      Local.promise_consistent lc_src.
  Proof.
    inv SIM. inv PROMS. inv MEMORY. ii.
    destruct (classic (prom_self loc ts)) as [PROM|NPROM].
    { eapply FORGET in PROM. des. clarify. }
    exploit COMPLETE0; eauto. i. rewrite PROMISE in *. inv x.
    inv MESSAGE; clarify.
    - exploit CONSISTENT; eauto. i. eapply TimeFacts.le_lt_lt; eauto.
      inv TVIEW. inv CUR. auto.
    - exploit RESERVE; eauto. clarify.
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

  Lemma sim_memory_max_concrete_timemap P mem_src mem_tgt sc_src sc_tgt
        (SIM: sim_memory P mem_src mem_tgt)
        (SCSRC: Memory.max_concrete_timemap mem_src sc_src)
        (SCTGT: Memory.max_concrete_timemap mem_tgt sc_tgt)
    :
      TimeMap.le sc_src sc_tgt.
  Proof.
    inv SIM. ii. specialize (SCSRC loc). specialize (SCTGT loc).
    inv SCSRC. inv SCTGT. des.
    destruct (classic (P loc (sc_src loc))) as [PROM|NPROM].
    - apply FORGET in PROM. des.
      setoid_rewrite SRCGET in GET. clarify.
    - apply COMPLETE in NPROM. setoid_rewrite GET in NPROM.
      inv NPROM. inv MESSAGE; clarify.
      + eapply MAX0; eauto.
      + exploit RESERVE; eauto. clarify.
  Qed.


  Lemma sim_promise_pasts_le P pasts0 pasts1 rel_src rel_tgt prom_src prom_tgt
        (SIM: sim_promise P pasts0 rel_src rel_tgt prom_src prom_tgt)
        (PASTLE: pasts_le pasts0 pasts1)
    :
      sim_promise P pasts1 rel_src rel_tgt prom_src prom_tgt.
  Proof.
    inv SIM. econs; eauto.
    i.



  Lemma pasts_le_all_pasts_memory mem pasts0 pasts1
        (ALL: all_pasts_memory mem pasts0)
        (PASTLE: pasts_le pasts0 pasts1)
    :
      all_pasts_memory mem pasts1.
  Proof.
    ii. exploit ALL; eauto. i. des.
    apply PASTLE in PAST. esplits; eauto.
    i. apply



            (PAST: wf_pasts_memory mem_src pasts)
        (<<PAST: wf_pasts_memory mem_src' pasts'>>) /\
        (<<PASTLE: pasts_le pasts pasts'>>)


  Lemma sim_memory_max_concrete_timemap P mem_src mem_tgt sc_src sc_tgt
        (SIM: sim_memory P mem_src mem_tgt)
        (SCSRC: Memory.max_concrete_timemap mem_src sc_src)
        (SCTGT: Memory.max_concrete_timemap mem_tgt sc_tgt)
    :
      TimeMap.le sc_src sc_tgt.
  Proof.

    Memory.cap
    inv SIM. ii. specialize (SCSRC loc). specialize (SCTGT loc).
    inv SCSRC. inv SCTGT. des.
    destruct (classic (P loc (sc_src loc))) as [PROM|NPROM].
    - apply FORGET in PROM. des.
      setoid_rewrite SRCGET in GET. clarify.
    - apply COMPLETE in NPROM. setoid_rewrite GET in NPROM.
      inv NPROM. inv MESSAGE; clarify.
      + eapply MAX0; eauto.
      + exploit RESERVE; eauto. clarify.
  Qed.

  Inductive sim_memory P mem_src mem_tgt : Prop :=
  | sim_memory_intro
      (COMPLETE: forall l t (NPROMS: ~ P l t),
          sim_memory_content
            (Memory.get l t mem_src) (Memory.get l t mem_tgt))
      (FORGET: forall l t (PROMS: P l t),
          exists from msg,
            (<<SRCGET: Memory.get l t mem_src = Some (from, Message.reserve)>>) /\
            (<<TGTGET: Memory.get l t mem_tgt = Some (from, msg)>>))
  .


Memory.cap (Thread.memory e) mem1 ->
Memory.max_concrete_timemap mem1 sc1 ->


  Thread.consistent


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
