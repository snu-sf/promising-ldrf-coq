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
      (FORGET: forall l t (PROMS: P l t), Memory.get l t mem_src = None)
  .

  Inductive sim_memory P mem_src mem_tgt : Prop :=
  | sim_memory_intro
      (COMPLETE: forall l t (NPROMS: ~ P l t),
          sim_memory_content
            (Memory.get l t mem_src) (Memory.get l t mem_tgt))
      (FORGET: forall l t (PROMS: P l t), Memory.get l t mem_src = None)
  .


  Inductive sim_promise

  Inductive sim_statelocal:
    sigT (@Language.state ProgramEvent.t) * Local.t -> sigT (@Language.state ProgramEvent.t) * Local.t -> Prop :=
  | forget_statelocal_intro
      st lc_src lc_tgt
      (TVIEW : TView.le lc_src.(Local.tview) lc_tgt.(Local.tview))
      (PROMS : lc1.(Local.promises) = Memory.bot)
    :
      forget_statelocal (st, lc1) (st, lc2)
  .


  Require Import MemoryProps.


concrete_promised

Inductive sim_statelocal:
  sigT (@Language.state ProgramEvent.t) * Local.t -> sigT (@Language.state ProgramEvent.t) * Local.t -> Prop :=
| forget_statelocal_intro
    st lc1 lc2
    (TVIEW : TView.le lc1.(Local.tview) lc2.(Local.tview))
    (PROMS : lc1.(Local.promises) = Memory.bot)
  :
    forget_statelocal (st, lc1) (st, lc2)
.


View.

Inductive forget_memory P msrc mtgt : Prop :=
| forget_memory_intro
    (COMPLETE: forall l t (NPROMS: ~ P l t),
        Memory.get l t msrc = Memory.get l t mtgt)
    (FORGET: forall l t (PROMS: P l t), Memory.get l t msrc = None)
.


option
option_rel Message.le


Inductive forget_memory P msrc mtgt : Prop :=
| forget_memory_intro
    (COMPLETE: forall l t (NPROMS: ~ P l t),
        Memory.get l t msrc = Memory.get l t mtgt)
    (FORGET: forall l t (PROMS: P l t), Memory.get l t msrc = None)
.



low view
shorter



Module Inv.

  Record t mem lang (st: Language.state lang) lc
         (proms: Memory.t)
         (spaces : Loc.t -> Time.t -> Prop)
         (updates : Loc.t -> Time.t -> Prop)
         (aupdates : Loc.t -> Time.t -> Prop)
         (mlast: Memory.t): Prop :=
    {
      SPACES: forall loc ts (IN: spaces loc ts), concrete_covered proms mem loc ts;
      AUPDATES: forall loc ts (IN: aupdates loc ts),
          exists to msg,
            (<<TS: Time.lt ts to>>) /\
            (<<GET: Memory.get loc to proms = Some (ts, msg)>>);
      PROMS: forall
          loc to m sc (PROM : concrete_promised proms loc to)
          (FUTURE: unchanged_on spaces mlast m)
          (UNCHANGED: not_attatched (updates \2/ aupdates) m),
          exists st' lc' sc' m',
            (<<STEPS : rtc (tau (@AThread.program_step _))
                           (Thread.mk _ st lc sc m)
                           (Thread.mk _ st' lc' sc' m')>>) /\
            (<<WRITING : is_writing _ st' loc Ordering.relaxed>>);
      UPDATE : forall
          loc to m sc (UPD : updates loc to)
          (FUTURE: unchanged_on spaces mlast m)
          (UNCHANGED: not_attatched (updates \2/ aupdates) m),
          exists st' lc' sc' m',
            (<<STEPS : rtc (tau (@AThread.program_step _))
                           (Thread.mk _ st lc sc m)
                           (Thread.mk _ st' lc' sc' m')>>) /\
            (<<READING : is_updating _ st' loc Ordering.strong_relaxed>>);
      AUPDATE : forall
          loc to m sc (UPD : aupdates loc to)
          (FUTURE: unchanged_on spaces mlast m)
          (UNCHANGED: not_attatched (updates \2/ aupdates) m),
          exists st' lc' sc' m',
            (<<STEPS : rtc (tau (@AThread.program_step _))
                           (Thread.mk _ st lc sc m)
                           (Thread.mk _ st' lc' sc' m')>>) /\
            (<<READING : is_updating _ st' loc Ordering.seqcst>>);
    }.

End Inv.



Section SIMPF.

  Inductive thread_wf lang (th: Thread.t lang): Prop :=
  | thread_wf_intro
      (SC: Memory.closed_timemap th.(Thread.sc) th.(Thread.memory))
      (CLOSED: Memory.closed th.(Thread.memory))
      (LCWF: Local.wf th.(Thread.local) th.(Thread.memory))
  .

  Inductive sim_pf_one
            (tid: Ident.t)
            (mlast: Memory.t)
            (spaces : (Loc.t -> Time.t -> Prop))
            (updates: (Loc.t -> Time.t -> Prop))
            (aupdates: (Loc.t -> Time.t -> Prop))
            (c_src c_tgt: Configuration.t) : Prop :=
  | sim_pf_one_intro
      (FUTURE: unchanged_on spaces mlast c_src.(Configuration.memory))
      (NOATTATCH: not_attatched (updates \2/ aupdates) c_src.(Configuration.memory))
      (INV:
         forall
           lang_src st_src lc_src lang_tgt st_tgt lc_tgt
           (TIDSRC: IdentMap.find tid c_src.(Configuration.threads) =
                    Some (existT _ lang_src st_src, lc_src))
           (TIDTGT: IdentMap.find tid c_tgt.(Configuration.threads) =
                    Some (existT _ lang_tgt st_tgt, lc_tgt)),
           Inv.t c_tgt.(Configuration.memory) _ st_src lc_src lc_tgt.(Local.promises) spaces updates aupdates mlast)
      (INVBOT:
         forall
           (TIDSRC: IdentMap.find tid c_src.(Configuration.threads) = None),
           (<<SPACESBOT: spaces <2= bot2>>) /\
           (<<UPDATESBOT: updates <2= bot2>>) /\
           (<<AUPDATESBOT: aupdates <2= bot2>>))
  .

  Inductive sim_pf
            (idents: Ident.t -> Prop)
            (mlast: Ident.t -> Memory.t)
            (spaces : Ident.t -> (Loc.t -> Time.t -> Prop))
            (updates: Ident.t -> (Loc.t -> Time.t -> Prop))
            (aupdates: Ident.t -> (Loc.t -> Time.t -> Prop))
            (c_src c_tgt: Configuration.t) : Prop :=
  | sim_pf_intro
      (FORGET: forget_config c_src c_tgt)
      (THREADS: forall tid (IDENT: idents tid),
          sim_pf_one tid (mlast tid) (spaces tid) (updates tid) (aupdates tid) c_src c_tgt)
      (RACEFREE: pf_racefree APFConfiguration.step c_src)
      (WFSRC: Configuration.wf c_src)
      (WFTGT: Configuration.wf c_tgt)
      (RESERVEWF: memory_reserve_wf c_tgt.(Configuration.memory))
      (RESERVERTGT: reserver_exists c_tgt)
      (RESERVERSRC: reserver_exists c_src)
  .

  Definition sim_pf_minus_one
             (tid: Ident.t)
             (mlast: Ident.t -> Memory.t)
             (spaces : Ident.t -> (Loc.t -> Time.t -> Prop))
             (updates: Ident.t -> (Loc.t -> Time.t -> Prop))
             (aupdates: Ident.t -> (Loc.t -> Time.t -> Prop))
             (c_src c_tgt: Configuration.t) : Prop :=
    sim_pf (fun tid' => tid <> tid') mlast spaces updates aupdates c_src c_tgt.

  Inductive sim_pf_all c_src c_tgt: Prop :=
  | sim_pf_all_intro mlast spaces updates aupdates
                     (SIM : sim_pf (fun _ => True) mlast spaces updates aupdates c_src c_tgt)
  .

  Lemma init_pf s tid st lc
        (TID: IdentMap.find tid (Threads.init s) = Some (st, lc))
    :
      Local.promises lc = Memory.bot.
  Proof.
    unfold Threads.init in *. erewrite IdentMap.Properties.F.map_o in *.
    unfold option_map in *. des_ifs.
  Qed.

  Lemma sim_pf_init
        s
        (RACEFREE: pf_racefree APFConfiguration.step (Configuration.init s))
    :
      sim_pf_all (Configuration.init s) (Configuration.init s)
  .
  Proof.
    econs.
    instantiate (1:=fun _ _ _ => False).
    instantiate (1:=fun _ _ _ => False).
    instantiate (1:=fun _ _ _ => False).
    instantiate (1:=fun _ => Memory.init).
    econs; eauto; ss; i.
    - econs; i; ss.
      + unfold Threads.init in *. erewrite IdentMap.Properties.F.map_o in *.
        unfold option_map in *. des_ifs.
      + econs.
        * instantiate (1:= Memory.init). econs; ss; eauto.
          ii. inv PROMS. ss.
          exploit init_pf; eauto. i. rewrite x0 in *.
          inv PROMISED. rewrite Memory.bot_get in *. clarify.
        * refl.
    - econs; ss.
      + refl.
      + ii. des; clarify.
      + i. econs; eauto; ii; clarify.
        exploit init_pf; try apply TIDTGT; eauto. i.
        rewrite x0 in *. inv PROM.
        rewrite Memory.bot_get in *. clarify.
      + i; splits; i; clarify.
    - eapply Configuration.init_wf.
    - eapply Configuration.init_wf.
    - ii. unfold Memory.get in GET. rewrite Cell.init_get in GET.
      des_ifs.
    - ii. unfold Memory.get in RESERVE. rewrite Cell.init_get in RESERVE.
      des_ifs.
    - ii. unfold Memory.get in RESERVE. rewrite Cell.init_get in RESERVE.
      des_ifs.
  Qed.

  Lemma sim_pf_src_no_promise idents mlast spaces updates aupdates c_src c_tgt
        (SIM: sim_pf idents mlast spaces updates aupdates c_src c_tgt)
        tid st lc
        (TIDSRC: IdentMap.find tid c_src.(Configuration.threads) =
                 Some (st, lc))
    :
      lc.(Local.promises) = Memory.bot.
  Proof.
    inv SIM. inv FORGET. specialize (THS tid).
    unfold option_rel in THS. des_ifs. inv THS. auto.
  Qed.

  Lemma sim_pf_src_no_reserve idents mlast spaces updates aupdates c_src c_tgt
        (SIM: sim_pf idents mlast spaces updates aupdates c_src c_tgt)
        loc to from
        (RESERVE: Memory.get loc to c_src.(Configuration.memory) = Some (from, Message.reserve))
    :
      False.
  Proof.
    dup SIM. inv SIM. eapply RESERVERSRC in RESERVE; eauto.
    des. eapply sim_pf_src_no_promise in TIDSRC; eauto.
    rewrite TIDSRC in *. erewrite Memory.bot_get in *; clarify.
  Qed.

  Lemma less_covered_max_ts mem0 mem1
        (INHABITED: Memory.inhabited mem0)
        (SHORTER: forall loc to (COVER: covered loc to mem0), covered loc to mem1)
        loc
    :
      Time.le (Memory.max_ts loc mem0) (Memory.max_ts loc mem1).
  Proof.
    specialize (INHABITED loc). eapply Memory.max_ts_spec in INHABITED.
    des. dup GET. eapply memory_get_ts_strong in GET. des; clarify.
    - erewrite GET1. eapply Time.bot_spec.
    - exploit SHORTER.
      { econs; eauto. econs; [|refl]. eauto. }
      intros COVER. inv COVER. inv ITV.
      eapply Memory.max_ts_spec in GET. des. ss.
      etrans; eauto.
  Qed.

  Lemma sim_pf_max_timemap idents mlast spaces updates aupdates c_src c_tgt max
        (SIM: sim_pf idents mlast spaces updates aupdates c_src c_tgt)
        (MAX: Memory.max_concrete_timemap c_tgt.(Configuration.memory) max)
    :
      TimeMap.le (Memory.max_timemap c_src.(Configuration.memory)) max.
  Proof.
    inv SIM. inv WFTGT. inv MEM. inv WFSRC. inv MEM. inv FORGET. ii.
    inv MEM. inv SHORTER. eapply less_covered_max_ts in COVER; eauto. etrans; eauto.
    exploit Memory.max_ts_spec.
    { inv FORGET. erewrite COMPLETE0.
      - eapply (INHABITED loc).
      - ii. inv H. destruct st as [lang st]. inv PROMISED. destruct msg.
        inv WF. exploit THREADS0; eauto. intros []. erewrite BOT in GET. clarify. }
    i. des. eapply forget_memory_get in GET; eauto. des. destruct msg.
    - eapply Memory.max_concrete_ts_spec in GET0; eauto. des. auto.
    - exfalso. eapply NOT.
      eapply RESERVERTGT in GET0. des. destruct st as [lang st].
      econs; eauto. econs; eauto.
  Qed.

  Lemma pf_sim_memory_exists_or_blank L mem_src mem_tgt
        (MEM: pf_sim_memory L mem_src mem_tgt)
        loc to from val released
        (GET: Memory.get loc to mem_tgt = Some (from, Message.concrete val released))
    :
      (exists from', (<<GET: Memory.get loc to mem_src = Some (from', Message.concrete val released)>>)) \/
      (<<BLANK: forall ts (ITV: Interval.mem (from, to) ts),
          (<<NCOVER: ~ covered loc ts mem_src>>) /\ (<<FORGET: L loc to>>)>>).
  Proof.
    inv MEM. dup FORGET. inv FORGET. destruct (classic (L loc to)).
    - right. ii. split; auto. ii.
      inv SHORTER. eapply COVER in H0. inv H0.
      eapply forget_memory_get in GET0; eauto. des; clarify.
      exploit Memory.get_disjoint.
      { eapply GET1. }
      { eapply GET. }
      i. des; clarify. eapply x0; eauto.
    - left. erewrite <- COMPLETE in GET; eauto.
      inv SHORTER. eapply COMPLETE0 in GET. des. eauto.
  Qed.


End SIMPF.
