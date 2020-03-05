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
            (<<SRCGET: Memory.get l t mem_src = Some (from, msg)>>) /\
            (<<TGTGET: Memory.get l t mem_tgt = Some (from, Message.reserve)>>))
  .

  Inductive wf_pasts_memory (mem: Memory.t) (pasts: Loc.t -> Time.t -> option Memory.t): Prop :=
  | wf_pasts_memory_intro
      (COMPLETE: forall loc from to val released
                        (GET: Memory.get loc to mem = Some (from, Message.concrete val released)),
          exists past,
            (<<PAST: pasts loc to = Some past>>) /\
            (<<GET: Memory.closed_opt_view released past>>) /\
            (<<PREV: forall past' (PAST: pasts loc from = Some past'),
                Memory.future_weak past' past>>)
      )
      (ONLY: forall loc ts past (PAST: pasts loc ts = Some past),
          (<<CLOSED: concrete_promised mem loc ts>>) /\
          (<<CURR: Memory.future_weak past mem>>)
      )
  .

  Definition pasts_le
             (pasts0: Loc.t -> Time.t -> option Memory.t)
             (pasts1: Loc.t -> Time.t -> option Memory.t): Prop :=
    forall loc to past (PAST0: pasts0 loc to = Some past), pasts1 loc to = Some past.

  Inductive sim_timemap (past: Memory.t) (tm_src tm_tgt: TimeMap.t): Prop :=
  | sim_timemap_intro
      (IN: forall loc (LOC: ~ L loc), tm_src loc = tm_tgt loc)
      (NIN: forall loc (LOC: L loc) ts
                   (PAST: concrete_promised past loc ts)
                   (LE: Time.le ts (tm_tgt loc)),
          Time.le ts (tm_src loc))
  .

  Inductive sim_view (past: Memory.t) (view_src view_tgt: View.t): Prop :=
  | sim_view_intro
      (PLN: sim_timemap past view_src.(View.pln) view_tgt.(View.pln))
      (RLX: sim_timemap past view_src.(View.rlx) view_tgt.(View.rlx))
  .

  Inductive sim_opt_view (past: Memory.t): forall (view_src view_tgt: option View.t), Prop :=
  | sim_opt_view_some
      view_src view_tgt
      (SIM: sim_view past view_src view_tgt):
      sim_opt_view past (Some view_src) (Some view_tgt)
  | sim_opt_view_none:
      sim_opt_view past None None
  .
  Hint Constructors sim_opt_view.

  Inductive sim_promise P (pasts: Loc.t -> Time.t -> option Memory.t)
            (rel_src rel_tgt: LocFun.t View.t) (prom_src prom_tgt: Memory.t): Prop :=
  | sim_promise_intro
      (COMPLETE: forall loc to past from_src from_tgt val_src val_tgt released_src released_tgt
                        (PAST: pasts loc to = Some past)
                        (GETSRC: Memory.get loc to prom_src = Some (from_src, Message.concrete val_src released_src))
                        (GETTGT: Memory.get loc to prom_tgt = Some (from_tgt, Message.concrete val_tgt released_tgt))
                        (PAST: pasts loc to = Some past)
        ,
          (<<SIM: sim_opt_view past released_src released_tgt>>) /\
          (<<REL: forall (VLE: View.le (rel_tgt loc) (View.unwrap released_tgt)),
              View.le (rel_src loc) (View.unwrap released_src)>>))
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
  .
  Proof.
  Admitted.

End SIM.
