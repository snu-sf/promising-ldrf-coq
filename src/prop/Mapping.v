Require Import Lia.
Require Import RelationClasses.

From Paco Require Import paco.
From sflib Require Import sflib.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import Loc.
From PromisingLib Require Import Language.

Require Import Time.
Require Import Event.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import Cover.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.
Require Import Progress.

Require Import Program.
Require Import Cell.
Require Import Time.
Require Import Pred.
Require Import Trace.
Require Import MemoryProps.

Set Implicit Arguments.


Section MAPPED.

  Variable f: Loc.t -> Time.t -> Time.t -> Prop.

  Definition mapping_map_le:=
    forall loc t0 t1 ft0 ft1
           (MAP0: f loc t0 ft0)
           (MAP1: f loc t1 ft1),
      Time.le t0 t1 -> Time.le ft0 ft1.

  Definition mapping_map_lt:=
    forall loc t0 t1 ft0 ft1
           (MAP0: f loc t0 ft0)
           (MAP1: f loc t1 ft1),
      Time.lt t0 t1 -> Time.lt ft0 ft1.

  Definition mapping_map_bot :=
    forall loc,
      f loc Time.bot Time.bot.

  Definition mapping_map_eq :=
    forall loc to ft0 ft1
           (MAP0: f loc to ft0)
           (MAP1: f loc to ft1),
      ft0 = ft1.

  Hypothesis map_le: mapping_map_le.
  Hypothesis map_bot: mapping_map_bot.
  Hypothesis map_eq: mapping_map_eq.

  Definition dom loc to: Prop :=
    exists fto, f loc to fto.

  Definition collapsed (loc: Loc.t) (t0 t1: Time.t): Prop :=
    exists ft,
      (<<MAP0: f loc t0 ft>>) /\ (<<MAP1: f loc t1 ft>>).

  Global Program Instance collapsed_Symmetric (loc: Loc.t): Symmetric (collapsed loc).
  Next Obligation.
    destruct H. eexists. des. splits; eauto.
  Qed.

  Lemma collapsed_inside
        loc
        t0 t1 t2 t3
        ft0 ft1 ft2 ft3
        (MAP0: f loc t0 ft0)
        (MAP1: f loc t1 ft1)
        (MAP2: f loc t2 ft2)
        (MAP3: f loc t3 ft3)
        (CLPS: collapsed loc t0 t3)
        (TLE0: Time.le t0 t1)
        (TLE1: Time.le t1 t2)
        (TLE2: Time.le t2 t3)
    :
      collapsed loc t1 t2.
  Proof.
    eapply map_le in TLE0; eauto.
    eapply map_le in TLE1; eauto.
    eapply map_le in TLE2; eauto.
    unfold collapsed in *. des.
    hexploit (map_eq MAP0 MAP4). i. subst.
    hexploit (map_eq MAP3 MAP5). i. subst.
    exploit TimeFacts.antisym; eauto. i. subst.
    exploit TimeFacts.antisym; eauto. i. subst.
    esplits; eauto.
  Qed.

  Lemma not_collapsed_outside
        loc
        t0 t1 t2 t3
        ft0 ft1 ft2 ft3
        (MAP0: f loc t0 ft0)
        (MAP1: f loc t1 ft1)
        (MAP2: f loc t2 ft2)
        (MAP3: f loc t3 ft3)
        (NCLPS: ~ collapsed loc t1 t2)
        (TLE0: Time.le t0 t1)
        (TLE1: Time.le t1 t2)
        (TLE2: Time.le t2 t3)
    :
      ~ collapsed loc t0 t3.
  Proof.
    ii. apply NCLPS. eapply collapsed_inside.
    - apply MAP0.
    - apply MAP1.
    - apply MAP2.
    - apply MAP3.
    - auto.
    - auto.
    - auto.
    - auto.
  Qed.

  Lemma map_lt_only_if
        loc t0 t1 ft0 ft1
        (MAP0: f loc t0 ft0)
        (MAP1: f loc t1 ft1)
    :
      Time.lt ft0 ft1 -> Time.lt t0 t1.
  Proof.
    set (TimeFacts.OrderTac.TO.lt_total t0 t1). des; eauto.
    - clarify. i.
      hexploit (map_eq MAP0 MAP1). i. subst.
      timetac.
    - exploit map_le.
      + eapply MAP1.
      + eapply MAP0.
      + left. eauto.
      + i. timetac.
  Qed.
  Hint Resolve map_lt_only_if.

  Definition map_eq_iff
             loc t0 t1 ft0 ft1
             (MAP0: f loc t0 ft0)
             (MAP1: f loc t1 ft1)
             (CLPS: ~ collapsed loc t0 t1)
    :
      t0 = t1 <-> ft0 = ft1.
  Proof.
    split; i; clarify; eauto.
    exfalso. apply CLPS. eexists. eauto.
  Qed.
  Hint Resolve map_eq_iff.

  Definition map_lt_iff
             loc t0 t1 ft0 ft1
             (MAP0: f loc t0 ft0)
             (MAP1: f loc t1 ft1)
             (CLPS: ~ collapsed loc t0 t1)
    :
      Time.lt t0 t1 <-> Time.lt ft0 ft1.
  Proof.
    split; i; cycle 1.
    { eapply map_lt_only_if; eauto. }
    exploit map_le.
    - eapply MAP0.
    - eapply MAP1.
    - left. eauto.
    - i. destruct x; auto. exfalso. apply CLPS.
      destruct H0. eexists. eauto.
  Qed.
  Hint Resolve map_lt_iff.

  Definition map_le_iff
             loc t0 t1 ft0 ft1
             (MAP0: f loc t0 ft0)
             (MAP1: f loc t1 ft1)
             (CLPS: ~ collapsed loc t0 t1)
    :
      Time.le t0 t1 <-> Time.le ft0 ft1.
  Proof.
    repeat rewrite Time.le_lteq.
    split; i; des; clarify; eauto.
    - left. erewrite <- map_lt_iff; eauto.
    - right. eapply map_eq_iff; eauto.
  Qed.
  Hint Resolve map_le_iff.

  Definition timemap_map (tm ftm: TimeMap.t): Prop :=
    forall loc, f loc (tm loc) (ftm loc).

  Record view_map (vw fvw: View.t): Prop :=
    view_map_intro
      { map_pln: timemap_map (View.pln vw) (View.pln fvw);
        map_rlx: timemap_map (View.rlx vw) (View.rlx fvw);
      }.

  Inductive opt_view_map: option View.t -> option View.t -> Prop :=
  | opt_view_map_some
      vw fvw
      (MAP: view_map vw fvw)
    :
      opt_view_map (Some vw) (Some fvw)
  | opt_view_map_none
    :
      opt_view_map None None
  .

  Record tview_map (vw fvw: TView.t): Prop :=
    tview_map_intro
      { map_rel: forall loc, view_map ((TView.rel vw) loc) ((TView.rel fvw) loc);
        map_cur: view_map (TView.cur vw) (TView.cur fvw);
        map_acq: view_map (TView.acq vw) (TView.acq fvw);
      }.

  Inductive msg_map: Message.t -> Message.t -> Prop :=
  | msg_map_reserve
    :
      msg_map Message.reserve Message.reserve
  | msg_map_undef
    :
      msg_map Message.undef Message.undef
  | msg_map_concrete
      val released freleased
      (MAP: opt_view_map released freleased)
    :
      msg_map (Message.concrete val released) (Message.concrete val freleased)
  .

  Inductive memory_op_kind_map (loc: Loc.t) : Memory.op_kind -> Memory.op_kind -> Prop :=
  | memory_op_kind_map_add
    :
      memory_op_kind_map loc (Memory.op_kind_add) (Memory.op_kind_add)
  | memory_op_kind_map_split
      to fto msg fmsg
      (MSG: msg_map msg fmsg)
      (TO: f loc to fto)
    :
      memory_op_kind_map loc (Memory.op_kind_split to msg) (Memory.op_kind_split fto fmsg)
  | memory_op_kind_map_lower
      msg fmsg
      (MSG: msg_map msg fmsg)
    :
      memory_op_kind_map loc (Memory.op_kind_lower msg) (Memory.op_kind_lower fmsg)
  | memory_op_kind_map_cancel
    :
      memory_op_kind_map loc (Memory.op_kind_cancel) (Memory.op_kind_cancel)
  .
  Hint Constructors memory_op_kind_map.

  Inductive tevent_map: ThreadEvent.t -> ThreadEvent.t -> Prop :=
  | tevent_map_promise
      loc from ffrom to fto msg fmsg kind fkind
      (FROM: f loc from ffrom)
      (TO: f loc to fto)
      (MSG: msg_map msg fmsg)
      (KIND: memory_op_kind_map loc kind fkind)
    :
      tevent_map
        (ThreadEvent.promise loc ffrom fto fmsg fkind)
        (ThreadEvent.promise loc from to msg kind)
  | tevent_map_read
      loc to fto val released freleased freleased' ordr
      (TO: f loc to fto)
      (RELEASED: opt_view_map released freleased')
      (RELEASEDLE: View.opt_le freleased freleased')
    :
      tevent_map
        (ThreadEvent.read loc fto val freleased ordr)
        (ThreadEvent.read loc to val released ordr)
  | tevent_map_write
      loc from ffrom to fto val released freleased freleased' ordw
      (FROM: f loc from ffrom)
      (TO: f loc to fto)
      (RELEASED: opt_view_map released freleased')
      (RELEASEDLE: View.opt_le freleased freleased')
    :
      tevent_map
        (ThreadEvent.write loc ffrom fto val freleased ordw)
        (ThreadEvent.write loc from to val released ordw)
  | tevent_map_write_na
      loc msgs fmsgs from ffrom to fto val ordw
      (MSGS: List.Forall2
               (fun m fm =>
                  f loc (fst (fst m)) (fst (fst fm)) /\
                  f loc (snd (fst m)) (snd (fst fm)) /\
                  msg_map (snd m) (snd fm))
               msgs fmsgs)
      (FROM: f loc from ffrom)
      (TO: f loc to fto)
    :
      tevent_map
        (ThreadEvent.write_na loc fmsgs ffrom fto val ordw)
        (ThreadEvent.write_na loc msgs from to val ordw)
  | tevent_map_update
      loc from ffrom to fto valr valw releasedr freleasedr freleasedr'
      releasedw freleasedw freleasedw' ordr ordw
      (FROM: f loc from ffrom)
      (TO: f loc to fto)
      (RELEASEDR: opt_view_map releasedr freleasedr')
      (RELEASEDW: opt_view_map releasedw freleasedw')
      (RELEASEDRLE: View.opt_le freleasedr freleasedr')
      (RELEASEDWLE: View.opt_le freleasedw freleasedw')
    :
      tevent_map
        (ThreadEvent.update loc ffrom fto valr valw freleasedr freleasedw ordr ordw)
        (ThreadEvent.update loc from to valr valw releasedr releasedw ordr ordw)
  | tevent_map_fence
      or ow
    :
      tevent_map
        (ThreadEvent.fence or ow)
        (ThreadEvent.fence or ow)
  | tevent_map_syscall
      e
    :
      tevent_map
        (ThreadEvent.syscall e)
        (ThreadEvent.syscall e)
  | tevent_map_silent
    :
      tevent_map
        (ThreadEvent.silent)
        (ThreadEvent.silent)
  | tevent_map_failure
    :
      tevent_map
        (ThreadEvent.failure)
        (ThreadEvent.failure)
  | tevent_map_racy_read
      loc to val ord
      fto
      (TO: f loc to fto)
    :
      tevent_map
        (ThreadEvent.racy_read loc fto val ord)
        (ThreadEvent.racy_read loc to val ord)
  | tevent_map_racy_write
      loc to val ord
      fto
      (TO: f loc to fto)
    :
      tevent_map
        (ThreadEvent.racy_write loc fto val ord)
        (ThreadEvent.racy_write loc to val ord)
  | tevent_map_racy_update
      loc to valr valw ordr ordw
      fto
      (TO: f loc to fto)
    :
      tevent_map
        (ThreadEvent.racy_update loc fto valr valw ordr ordw)
        (ThreadEvent.racy_update loc to valr valw ordr ordw)
  .

  Inductive msg_map_weak: Message.t -> Message.t -> Prop :=
  | msg_map_weak_reserve
    :
      msg_map_weak Message.reserve Message.reserve
  | msg_map_weak_undef
    :
      msg_map_weak Message.undef Message.undef
  | msg_map_weak_concrete
      val released freleased
    :
      msg_map_weak (Message.concrete val released) (Message.concrete val freleased)
  .

  Inductive tevent_map_weak
  : ThreadEvent.t -> ThreadEvent.t -> Prop :=
  | tevent_map_weak_promise
      loc from ffrom to fto msg fmsg kind fkind
      (FROM: f loc from ffrom)
      (TO: f loc to fto)
      (MSG: msg = Message.reserve <-> fmsg = Message.reserve)
    :
      tevent_map_weak
        (ThreadEvent.promise loc ffrom fto fmsg fkind)
        (ThreadEvent.promise loc from to msg kind)
  | tevent_map_weak_read
      loc to fto val released freleased ordr
      (TO: f loc to fto)
    :
      tevent_map_weak
        (ThreadEvent.read loc fto val freleased ordr)
        (ThreadEvent.read loc to val released ordr)
  | tevent_map_weak_write
      loc from ffrom to fto val released freleased ordw
      (FROM: f loc from ffrom)
      (TO: f loc to fto)
    :
      tevent_map_weak
        (ThreadEvent.write loc ffrom fto val freleased ordw)
        (ThreadEvent.write loc from to val released ordw)
  | tevent_map_weak_write_na
      loc msgs fmsgs from ffrom to fto val ordw
      (MSGS: List.Forall2
               (fun m fm =>
                  f loc (fst (fst m)) (fst (fst fm)) /\
                  f loc (snd (fst m)) (snd (fst fm)) /\
                  msg_map_weak (snd m) (snd fm))
               msgs fmsgs)
      (FROM: f loc from ffrom)
      (TO: f loc to fto)
    :
      tevent_map_weak
        (ThreadEvent.write_na loc fmsgs ffrom fto val ordw)
        (ThreadEvent.write_na loc msgs from to val ordw)
  | tevent_map_weak_update
      loc from ffrom to fto valr valw releasedr freleasedr
      releasedw freleasedw ordr ordw
      (FROM: f loc from ffrom)
      (TO: f loc to fto)
    :
      tevent_map_weak
        (ThreadEvent.update loc ffrom fto valr valw freleasedr freleasedw ordr ordw)
        (ThreadEvent.update loc from to valr valw releasedr releasedw ordr ordw)
  | tevent_map_weak_fence
      or ow
    :
      tevent_map_weak
        (ThreadEvent.fence or ow)
        (ThreadEvent.fence or ow)
  | tevent_map_weak_syscall
      e
    :
      tevent_map_weak
        (ThreadEvent.syscall e)
        (ThreadEvent.syscall e)
  | tevent_map_weak_silent
    :
      tevent_map_weak
        (ThreadEvent.silent)
        (ThreadEvent.silent)
  | tevent_map_weak_failure
    :
      tevent_map_weak
        (ThreadEvent.failure)
        (ThreadEvent.failure)
  | tevent_map_weak_racy_read
      loc to val ord
      fto
      (TO: f loc to fto)
    :
      tevent_map_weak
        (ThreadEvent.racy_read loc fto val ord)
        (ThreadEvent.racy_read loc to val ord)
  | tevent_map_weak_racy_write
      loc to val ord
      fto
      (TO: f loc to fto)
    :
      tevent_map_weak
        (ThreadEvent.racy_write loc fto val ord)
        (ThreadEvent.racy_write loc to val ord)
  | tevent_map_weak_racy_update
      loc to valr valw ordr ordw
      fto
      (TO: f loc to fto)
    :
      tevent_map_weak
        (ThreadEvent.racy_update loc fto valr valw ordr ordw)
        (ThreadEvent.racy_update loc to valr valw ordr ordw)
  .
  Hint Constructors tevent_map_weak.

  Lemma msg_map_msg_map_weak
        m fm
        (MSG: msg_map m fm):
    msg_map_weak m fm.
  Proof.
    inv MSG; econs.
  Qed.

  Lemma tevent_map_tevent_map_weak e fe
        (EVENT: tevent_map e fe)
    :
      tevent_map_weak e fe.
  Proof.
    inv EVENT; eauto.
    - econs; eauto. inv MSG; ss.
    - econs; eauto. clear - MSGS.
      induction MSGS; eauto. econs; eauto.
      des. splits; auto.
      apply msg_map_msg_map_weak. ss.
  Qed.

  Definition non_collapsable (loc: Loc.t) (to: Time.t): Prop :=
    forall to' (TLE: Time.lt to' to),
      ~ collapsed loc to' to.

  Lemma map_lt_non_collapsable
        loc t0 t1 ft0 ft1
        (MAP0: f loc t0 ft0)
        (MAP1: f loc t1 ft1)
        (NCLPS: non_collapsable loc t1)
    :
      Time.lt t0 t1 <-> Time.lt ft0 ft1.
  Proof.
    split; i.
    - erewrite <- map_lt_iff; eauto.
    - eapply map_lt_only_if; eauto.
  Qed.

  Lemma time_join_map loc t0 t1 ft0 ft1
        (MAP0: f loc t0 ft0)
        (MAP1: f loc t1 ft1)
    :
      f loc (Time.join t0 t1) (Time.join ft0 ft1).
  Proof.
    unfold Time.join. des_ifs.
    - eapply map_le in l; eauto. timetac.
    - destruct l0; auto.
      + eapply map_lt_only_if in H; eauto.
        exfalso. eapply Time.lt_strorder. etrans; eauto.
      + destruct H. auto.
  Qed.

  Lemma timemap_bot_map
    :
      timemap_map TimeMap.bot TimeMap.bot.
  Proof.
    ii. eapply map_bot.
  Qed.

  Lemma view_bot_map
    :
      view_map View.bot View.bot.
  Proof.
    econs.
    - eapply timemap_bot_map; eauto.
    - eapply timemap_bot_map; eauto.
  Qed.

  Lemma timemap_singleton_map loc to fto
        (MAP: f loc to fto)
    :
      timemap_map (TimeMap.singleton loc to) (TimeMap.singleton loc fto).
  Proof.
    ii. unfold TimeMap.singleton.
    setoid_rewrite LocFun.add_spec. des_ifs.
  Qed.

  Lemma singleton_ur_map loc to fto
        (MAP: f loc to fto)
    :
      view_map (View.singleton_ur loc to) (View.singleton_ur loc fto).
  Proof.
    unfold View.singleton_ur. econs; ss.
    - eapply timemap_singleton_map; eauto.
    - eapply timemap_singleton_map; eauto.
  Qed.

  Lemma singleton_rw_map loc to fto
        (MAP: f loc to fto)
    :
      view_map (View.singleton_rw loc to) (View.singleton_rw loc fto).
  Proof.
    unfold View.singleton_ur. econs; ss.
    eapply timemap_singleton_map; eauto.
  Qed.

  Lemma singleton_ur_if_map loc to fto cond
        (MAP: f loc to fto)
    :
      view_map (View.singleton_ur_if cond loc to) (View.singleton_ur_if cond loc fto).
  Proof.
    unfold View.singleton_ur_if. des_ifs.
    - eapply singleton_ur_map; eauto.
    - eapply singleton_rw_map; eauto.
  Qed.

  Lemma timemap_join_map tm0 tm1 ftm0 ftm1
        (TM0: timemap_map tm0 ftm0)
        (TM1: timemap_map tm1 ftm1)
    :
      timemap_map (TimeMap.join tm0 tm1) (TimeMap.join ftm0 ftm1).
  Proof.
    ii. unfold TimeMap.join.
    eapply time_join_map; eauto.
  Qed.

  Lemma timemap_le_map tm0 tm1 ftm0 ftm1
        (TM0: timemap_map tm0 ftm0)
        (TM1: timemap_map tm1 ftm1)
        (TMLE: TimeMap.le tm0 tm1)
    :
      TimeMap.le ftm0 ftm1.
  Proof.
    ii. eapply map_le; eauto.
  Qed.

  Inductive memory_map2 m fm: Prop :=
  | memory_map2_intro
      (MAPPED: forall loc to from msg (GET: Memory.get loc to m = Some (from, msg)),
          msg = Message.reserve \/
          exists fto ffrom fmsg' fmsg,
            (<<TO: f loc to fto>>) /\
            (<<MSG: msg_map msg fmsg'>>) /\
            (<<MSGLE: Message.le fmsg fmsg'>>) /\
            (<<GET: Memory.get loc fto fm = Some (ffrom, fmsg)>>))
      (ONLY: forall loc fto ffrom fmsg
                    (GET: Memory.get loc fto fm = Some (ffrom, fmsg)),
          exists to from msg,
            (<<TO: f loc to fto>>) /\
            (<<GET: Memory.get loc to m = Some (from, msg)>>) /\
            (<<FROM: f loc from ffrom>>))
  .

  Inductive memory_map m fm: Prop :=
  | memory_map_intro
      (MAPPED: forall loc to from msg (GET: Memory.get loc to m = Some (from, msg)),
          msg = Message.reserve \/
          exists fto ffrom fmsg' fmsg,
            (<<TO: f loc to fto>>) /\
            (<<MSG: msg_map msg fmsg'>>) /\
            (<<MSGLE: Message.le fmsg fmsg'>>) /\
            (<<GET: Memory.get loc fto fm = Some (ffrom, fmsg)>>))
      (ONLY: forall loc fto ffrom fmsg
                    (GET: Memory.get loc fto fm = Some (ffrom, fmsg)),
          (exists to from fto' ffrom',
              (<<TO: f loc to fto'>>) /\
              (<<TS0: Time.le ffrom' ffrom>>) /\
              (<<TS1: Time.le fto fto'>>) /\
              (<<FROM: f loc from ffrom'>>) /\
              (<<COVERED: forall ts (ITV: Interval.mem (from, to) ts),
                  covered loc ts m>>)) \/
          (<<OUT: forall ts fts (MAP: f loc ts fts), Time.lt fts ffrom>>))
  .

  Lemma memory_map2_memory_map
    :
      memory_map2 <2= memory_map.
  Proof.
    ii. inv PR. econs; eauto.
    i. exploit ONLY; eauto. i. des.
    left. esplits.
    - eapply TO.
    - refl.
    - refl.
    - eapply FROM.
    - i. econs; eauto.
  Qed.

  Inductive promises_map m fm: Prop :=
  | promises_map_intro
      (MAPPED: forall loc to from msg (GET: Memory.get loc to m = Some (from, msg)),
          exists fto ffrom fmsg,
            (<<NCLPS: non_collapsable loc to>>) /\
            (<<TO: f loc to fto>>) /\
            (<<MSG: msg_map msg fmsg>>) /\
            (<<GET: Memory.get loc fto fm = Some (ffrom, fmsg)>>))
      (ONLY: forall loc fto ffrom fmsg
                    (GET: Memory.get loc fto fm = Some (ffrom, fmsg)),
          exists to from msg,
            (<<TO: f loc to fto>>) /\
            (<<GET: Memory.get loc to m = Some (from, msg)>>) /\
            (<<FROM: f loc from ffrom>>))
  .

  Definition collapsable_unwritable prom mem: Prop :=
    forall loc t
           (SAT: (fun loc' t' => exists ts0 ts1,
                      (<<CLPS: collapsed loc' ts0 ts1>>) /\
                      (<<ITV: Interval.mem (ts0, ts1) t'>>)) loc t),
      unwritable mem prom loc t.

  Lemma collapsable_unwritable_step pf e lang (th0 th1: Thread.t lang)
        (STEP: Thread.step pf e th0 th1)
        (WFMEM: collapsable_unwritable (Local.promises (Thread.local th0)) (Thread.memory th0))
    :
      collapsable_unwritable (Local.promises (Thread.local th1)) (Thread.memory th1) .
  Proof.
    ii. eapply unwritable_increase; eauto.
  Qed.

  Lemma collapsable_unwritable_steps P lang (th0 th1: Thread.t lang)
        (STEP: rtc (tau (@pred_step P lang)) th0 th1)
        (WFMEM: collapsable_unwritable (Local.promises (Thread.local th0)) (Thread.memory th0))
    :
      collapsable_unwritable (Local.promises (Thread.local th1)) (Thread.memory th1) .
  Proof.
    revert WFMEM. induction STEP; auto.
    i. eapply IHSTEP. inv H. inv TSTEP. inv STEP0.
    eapply collapsable_unwritable_step; eauto.
  Qed.

  Lemma promises_map_memory_map2 m fm
        (PROMISES: promises_map m fm)
    :
      memory_map2 m fm.
  Proof.
    inv PROMISES. econs; eauto.
    i. exploit MAPPED; eauto. i. des.
    right. esplits; eauto. refl.
  Qed.

  Lemma promises_map_memory_map m fm
        (PROMISES: promises_map m fm)
    :
      memory_map m fm.
  Proof.
    eapply memory_map2_memory_map.
    eapply promises_map_memory_map2; eauto.
  Qed.
  Hint Resolve promises_map_memory_map.

  Lemma closed_timemap_map m fm tm ftm
        (MEM: memory_map m fm)
        (TM: timemap_map tm ftm)
        (CLOSED: Memory.closed_timemap tm m)
    :
      Memory.closed_timemap ftm fm.
  Proof.
    inv MEM. ii. specialize (CLOSED loc). des.
    eapply MAPPED in CLOSED. des; clarify. inv MSG.
    specialize (TM loc).
    hexploit (map_eq TM TO). i. subst.
    inv MSGLE. esplits; eauto.
  Qed.

  Lemma closed_view_map m fm vw fvw
        (MEM: memory_map m fm)
        (VIEW: view_map vw fvw)
        (CLOSED: Memory.closed_view vw m)
    :
      Memory.closed_view fvw fm.
  Proof.
    inv CLOSED. inv VIEW. econs.
    - eapply closed_timemap_map; eauto.
    - eapply closed_timemap_map; eauto.
  Qed.

  Lemma closed_opt_view_map m fm vw fvw
        (MEM: memory_map m fm)
        (VIEW: opt_view_map vw fvw)
        (CLOSED: Memory.closed_opt_view vw m)
    :
      Memory.closed_opt_view fvw fm.
  Proof.
    inv CLOSED.
    - inv VIEW. econs. eapply closed_view_map; eauto.
    - inv VIEW. econs.
  Qed.

  Lemma view_join_map v0 v1 fv0 fv1
        (VIEW0: view_map v0 fv0)
        (VIEW1: view_map v1 fv1)
    :
      view_map (View.join v0 v1) (View.join fv0 fv1).
  Proof.
    inv VIEW0. inv VIEW1.
    unfold View.join. econs; ss.
    - eapply timemap_join_map; eauto.
    - eapply timemap_join_map; eauto.
  Qed.

  Lemma tviewjoin_map tv0 tv1 ftv0 ftv1
        (TVIEW0: tview_map tv0 ftv0)
        (TVIEW1: tview_map tv1 ftv1)
    :
      tview_map (TView.join tv0 tv1) (TView.join ftv0 ftv1).
  Proof.
    inv TVIEW0. inv TVIEW1.
    unfold TView.join. econs; ss.
    - i. eapply view_join_map; eauto.
    - eapply view_join_map; eauto.
    - eapply view_join_map; eauto.
  Qed.

  Lemma unwrap_map released freleased
        (VIEW: opt_view_map released freleased)
    :
      view_map (View.unwrap released) (View.unwrap freleased).
  Proof.
    inv VIEW; ss.
  Qed.

  Lemma readable_map vw fvw loc to fto released freleased ordr
        (VIEW: view_map vw fvw)
        (TO: f loc to fto)
        (RELEASED: opt_view_map released freleased)
        (READABLE: TView.readable vw loc to released ordr)
    :
      TView.readable fvw loc fto freleased ordr.
  Proof.
    inv READABLE. econs.
    - eapply map_le; eauto.
      inv VIEW. eauto.
    - intros ORD. specialize (RLX ORD).
      eapply map_le; eauto.
      inv VIEW. eauto.
  Qed.

  Lemma read_tview_map tvw ftvw loc to fto released freleased ord
        (TVIEW: tview_map tvw ftvw)
        (TO: f loc to fto)
        (RELEASED: opt_view_map released freleased)
    :
      tview_map
        (TView.read_tview tvw loc to released ord)
        (TView.read_tview ftvw loc fto freleased ord).
  Proof.
    unfold TView.read_tview. econs; ss.
    - i. eapply map_rel; eauto.
    - eapply view_join_map.
      + eapply view_join_map.
        * eapply map_cur; eauto.
        * eapply singleton_ur_if_map; eauto.
      + des_ifs. eapply unwrap_map; eauto.
    - eapply view_join_map.
      + eapply view_join_map.
        * eapply map_acq; eauto.
        * eapply singleton_ur_if_map; eauto.
      + des_ifs. eapply unwrap_map; eauto.
  Qed.

  Lemma write_tview_map tvw ftvw sc fsc loc to fto ord
        (TVIEW: tview_map tvw ftvw)
        (TO: f loc to fto)
    :
      tview_map
        (TView.write_tview tvw sc loc to ord)
        (TView.write_tview ftvw fsc loc fto ord).
  Proof.
    unfold TView.write_tview. econs; ss.
    - i. setoid_rewrite LocFun.add_spec. des_ifs.
      + eapply view_join_map.
        * eapply map_cur; eauto.
        * eapply singleton_ur_map; eauto.
      + eapply view_join_map.
        * eapply map_rel; eauto.
        * eapply singleton_ur_map; eauto.
      + eapply map_rel in TVIEW. eauto.
    - eapply view_join_map.
      + eapply map_cur; eauto.
      + eapply singleton_ur_map; eauto.
    - eapply view_join_map.
      + eapply map_acq; eauto.
      + eapply singleton_ur_map; eauto.
  Qed.

  Lemma read_fence_tview_map tvw ftvw ord
        (TVIEW: tview_map tvw ftvw)
    :
      tview_map
        (TView.read_fence_tview tvw ord)
        (TView.read_fence_tview ftvw ord).
  Proof.
    unfold TView.read_fence_tview. econs; ss.
    - i. eapply map_rel; eauto.
    - des_ifs.
      + eapply map_acq; eauto.
      + eapply map_cur; eauto.
    - eapply map_acq; eauto.
  Qed.

  Lemma write_fence_sc_map tvw ftvw sc fsc ord
        (TVIEW: tview_map tvw ftvw)
        (SC: timemap_map sc fsc)
    :
      timemap_map
        (TView.write_fence_sc tvw sc ord)
        (TView.write_fence_sc ftvw fsc ord).
  Proof.
    unfold TView.write_fence_sc. des_ifs.
    eapply timemap_join_map; eauto.
    eapply map_rlx; eauto. eapply map_cur; eauto.
  Qed.

  Lemma write_fence_tview_map tvw ftvw sc fsc ord
        (TVIEW: tview_map tvw ftvw)
        (SC: timemap_map sc fsc)
    :
      tview_map
        (TView.write_fence_tview tvw sc ord)
        (TView.write_fence_tview ftvw fsc ord).
  Proof.
    unfold TView.write_fence_tview. econs; ss.
    - i. des_ifs.
      + econs; ss.
        * eapply write_fence_sc_map; eauto.
        * eapply write_fence_sc_map; eauto.
      + eapply map_cur; eauto.
      + eapply map_rel; eauto.
    - des_ifs.
      + econs; ss.
        * eapply write_fence_sc_map; eauto.
        * eapply write_fence_sc_map; eauto.
      + eapply map_cur; eauto.
    - eapply view_join_map.
      + eapply map_acq; eauto.
      + des_ifs. econs; ss.
        * eapply write_fence_sc_map; eauto.
        * eapply write_fence_sc_map; eauto.
  Qed.

  Lemma write_released_map tvw ftvw sc fsc loc to fto released freleased ord
        (TVIEW: tview_map tvw ftvw)
        (SC: timemap_map sc fsc)
        (TO: f loc to fto)
        (VIEW: opt_view_map released freleased)
    :
      opt_view_map
        (TView.write_released tvw sc loc to released ord)
        (TView.write_released ftvw fsc loc fto freleased ord).
  Proof.
    unfold TView.write_released. des_ifs; econs.
    eapply view_join_map; eauto.
    - eapply unwrap_map; eauto.
    - eapply map_rel; eauto. eapply write_tview_map; eauto.
  Qed.

  Lemma bot_promises_map fprom
        (MEM: promises_map Memory.bot fprom)
    :
      fprom = Memory.bot.
  Proof.
    inv MEM. eapply Memory.ext. i.
    rewrite Memory.bot_get.
    destruct (Memory.get loc ts fprom) eqn:GET; auto.
    destruct p. eapply ONLY in GET. des.
    rewrite Memory.bot_get in GET; eauto. clarify.
  Qed.

  Lemma no_reserves_map prom fprom
        (RESERVES: no_reserves prom)
        (MEM: promises_map prom fprom)
    :
      no_reserves fprom.
  Proof.
    inv MEM. ii. clarify. dup GET.
    eapply ONLY in GET0. des.
    dup GET0. eapply MAPPED in GET1. des.
    hexploit (map_eq TO TO0). i. clarify. inv MSG.
    eapply RESERVES in GET0. clarify.
  Qed.

  Lemma msg_get_map m fm loc to from msg
        (MEM: memory_map m fm)
        (GET: Memory.get loc to m = Some (from, msg))
    :
      msg = Message.reserve \/
      exists ffrom fto fmsg fmsg',
        (<<GET: Memory.get loc fto fm = Some (ffrom, fmsg)>>) /\
        (<<TO: f loc to fto>>) /\
        (<<MSG: msg_map msg fmsg'>>) /\
        (<<MSGLE: Message.le fmsg fmsg'>>).
  Proof.
    inv MEM. eapply MAPPED in GET. des; auto.
    right. esplits; eauto.
  Qed.

  Lemma msg_get_map_if m fm loc to fto from msg
        (MEM: memory_map m fm)
        (TO: f loc to fto)
        (GET: Memory.get loc to m = Some (from, msg))
    :
      msg = Message.reserve \/
      exists ffrom fmsg fmsg',
        (<<GET: Memory.get loc fto fm = Some (ffrom, fmsg)>>) /\
        (<<MSG: msg_map msg fmsg'>>) /\
        (<<MSGLE: Message.le fmsg fmsg'>>).
  Proof.
    inv MEM. eapply MAPPED in GET. des; auto. right.
    hexploit (map_eq TO TO0). i. subst.
    esplits; eauto.
  Qed.

  (* Lemma msg_get_map_only_if m fm *)
  (*       (MEM: memory_map m fm) *)
  (*       loc fto ffrom fmsg *)
  (*       (GET: Memory.get loc fto fm = Some (ffrom, fmsg)) *)
  (*   : *)
  (*     exists to from msg fmsg', *)
  (*       (<<TO: f loc to fto>>) /\ *)
  (*       (<<GET: Memory.get loc to m = Some (from, msg)>>) /\ *)
  (*       (<<FROM: f loc from ffrom>>) /\ *)
  (*       (<<MSG: msg_map msg fmsg'>>) /\ *)
  (*       (<<MSGLE: Message.le fmsg fmsg' >>) *)
  (* . *)
  (* Proof. *)
  (*   inv MEM. *)
  (*   dup GET. eapply ONLY in GET. des. *)
  (*   dup GET. eapply MAPPED in GET1. des. *)
  (*   - clarify. esplits; eauto. econs. *)
  (*   - hexploit (map_eq TO TO0). i. clarify. *)
  (*     esplits; eauto. *)
  (* Qed. *)

  Lemma promise_consistent_map tvw ftvw prom fprom
        (TVIEW: tview_map tvw ftvw)
        (PROMS: promises_map prom fprom)
        (CONSISTENT: Local.promise_consistent (Local.mk tvw prom))
    :
      Local.promise_consistent (Local.mk ftvw fprom).
  Proof.
    ii. ss.
    inv PROMS. exploit ONLY; eauto. i. des.
    exploit MAPPED; eauto. i. des.
    hexploit (map_eq TO TO0). i. clarify.
    exploit CONSISTENT; eauto; ss.
    { inv MSG0; ss. }
    i. erewrite <- map_lt_iff; eauto.
    eapply map_rlx. eapply map_cur. auto.
  Qed.

  Lemma nonsynch_loc_map loc prom fprom
        (PROMS: promises_map prom fprom)
        (NONSYNCH: Memory.nonsynch_loc loc prom)
    :
      Memory.nonsynch_loc loc fprom.
  Proof.
    ii. dup GET.
    inv PROMS. exploit ONLY; eauto. i. des.
    exploit MAPPED; eauto. i. des.
    hexploit (map_eq TO TO0). i. clarify.
    eapply NONSYNCH in GET1. des_ifs.
    - inv MSG. inv MAP. ss.
    - inv MSG.
    - inv MSG.
  Qed.

  Lemma writable_map vw fvw sc fsc loc to fto released freleased ordw
        (VIEW: view_map vw fvw)
        (TO: f loc to fto)
        (RELEASED: opt_view_map released freleased)
        (NCLPS: non_collapsable loc to)
        (WRITABLE: TView.writable vw sc loc to ordw)
    :
      TView.writable fvw fsc loc fto ordw.
  Proof.
    inv WRITABLE. econs.
    erewrite <- map_lt_non_collapsable; eauto.
    eapply map_rlx. eauto.
  Qed.

  Lemma timemap_map_exists mem fmem tm
        (MEM: memory_map mem fmem)
        (CLOSED: Memory.closed_timemap tm mem)
    :
      exists ftm,
        (<<TM: timemap_map tm ftm>>) /\
        (<<CLOSED: Memory.closed_timemap ftm fmem>>).
  Proof.
    hexploit (choice (fun loc to =>
                        (<<MAP: f loc (tm loc) to>>) /\
                        exists from val released,
                          Memory.get loc to fmem = Some (from, Message.concrete val released))).
    { intros loc. specialize (CLOSED loc). des.
      inv MEM. eapply MAPPED in CLOSED. des; clarify.
      inv MSG. inv MSGLE.
      esplits; eauto. }
    i. des. esplits; eauto.
    - ii. specialize (H loc). des. eauto.
    - ii. specialize (H loc). des. eauto.
  Qed.

  Lemma opt_view_map_exists mem fmem vw
        (MEM: memory_map mem fmem)
        (CLOSED: Memory.closed_opt_view vw mem)
    :
      exists fvw,
        (<<VIEW: opt_view_map vw fvw>>) /\
        (<<CLOSED: Memory.closed_opt_view fvw fmem>>).
  Proof.
    inv CLOSED.
    - inv CLOSED0.
      hexploit (timemap_map_exists MEM PLN). i. des.
      hexploit (timemap_map_exists MEM RLX). i. des.
      exists (Some (View.mk ftm ftm0)). esplits; eauto.
      econs. econs; eauto.
    - exists None. esplits; eauto. econs.
  Qed.

  Lemma view_wf_map vw fvw
        (VIEW: view_map vw fvw)
        (VIEWWF: View.wf vw)
    :
      View.wf fvw.
  Proof.
    inv VIEWWF. inv VIEW.
    econs. eapply timemap_le_map; eauto.
  Qed.

  Lemma opt_view_wf_map vw fvw
        (VIEW: opt_view_map vw fvw)
        (VIEWWF: View.opt_wf vw)
    :
      View.opt_wf fvw.
  Proof.
    inv VIEWWF; inv VIEW; econs.
    eapply view_wf_map; eauto.
  Qed.

  Lemma msg_wf_map msg fmsg
        (MSG: msg_map msg fmsg)
        (MSGWF: Message.wf msg)
    :
      Message.wf fmsg.
  Proof.
    inv MSGWF; inv MSG; econs; ss.
    eapply opt_view_wf_map; eauto.
  Qed.

  Lemma time_meet_map loc t0 t1 ft0 ft1
        (MAP0: f loc t0 ft0)
        (MAP1: f loc t1 ft1)
    :
      f loc (Time.meet t0 t1) (Time.meet ft0 ft1).
  Proof.
    unfold Time.meet. des_ifs.
    - eapply map_le in l; eauto. timetac.
    - destruct l0; auto.
      + eapply map_lt_only_if in H; eauto.
        exfalso. eapply Time.lt_strorder. etrans; eauto.
      + destruct H. auto.
  Qed.

  Lemma disjoint_map loc from0 ffrom0 to0 fto0 from1 ffrom1 to1 fto1
        (FROM0: f loc from0 ffrom0)
        (TO0: f loc to0 fto0)
        (FROM1: f loc from1 ffrom1)
        (TO1: f loc to1 fto1)
        (DISJOINT: Interval.disjoint (from0, to0) (from1, to1))
    :
      Interval.disjoint (ffrom0, fto0) (ffrom1, fto1).
  Proof.
    apply NNPP. ii. revert DISJOINT.
    apply disjoint_equivalent. apply disjoint_equivalent in H. des.
    splits.
    - eapply map_lt_only_if; eauto.
    - eapply map_lt_only_if; eauto.
    - eapply map_lt_only_if; eauto.
      + eapply time_join_map; eauto.
      + eapply time_meet_map; eauto.
  Qed.

  Lemma view_le_map vw0 vw1 fvw0 fvw1
        (VIEW0: view_map vw0 fvw0)
        (VIEW1: view_map vw1 fvw1)
        (VIEWLE: View.le vw0 vw1)
    :
      View.le fvw0 fvw1.
  Proof.
    inv VIEWLE. econs; eauto.
    - eapply timemap_le_map.
      + eapply map_pln; eauto.
      + eapply map_pln; eauto.
      + eauto.
    - eapply timemap_le_map.
      + eapply map_rlx; eauto.
      + eapply map_rlx; eauto.
      + eauto.
  Qed.

  Lemma opt_view_le_map vw0 vw1 fvw0 fvw1
        (VIEW0: opt_view_map vw0 fvw0)
        (VIEW1: opt_view_map vw1 fvw1)
        (VIEWLE: View.opt_le vw0 vw1)
    :
      View.opt_le fvw0 fvw1.
  Proof.
    inv VIEWLE.
    - inv VIEW0. econs.
    - inv VIEW0. inv VIEW1. econs.
      eapply view_le_map; eauto.
  Qed.

  Lemma msg_le_map msg0 msg1 fmsg0 fmsg1
        (MSG0: msg_map msg0 fmsg0)
        (MSG1: msg_map msg1 fmsg1)
        (MSGLE: Message.le msg1 msg0)
    :
      Message.le fmsg1 fmsg0.
  Proof.
    inv MSGLE.
    - inv MSG0. inv MSG1. econs; eauto.
      eapply opt_view_le_map; eauto.
    - inv MSG0. inv MSG1. econs; eauto.
    - inv MSG0. inv MSG1. econs; eauto.
  Qed.

  Lemma msg_get_promises_map m fm loc to from msg
        (MEM: promises_map m fm)
        (GET: Memory.get loc to m = Some (from, msg))
    :
      exists ffrom fto fmsg,
        (<<NCLPS: non_collapsable loc to>>) /\
        (<<GET: Memory.get loc fto fm = Some (ffrom, fmsg)>>) /\
        (<<FROM: f loc from ffrom>>) /\
        (<<TO: f loc to fto>>) /\
        (<<MSG: msg_map msg fmsg>>) /\
        (<<UNIQUE:
           forall to' (TO: f loc to' fto) frommsg
                  (GET: Memory.get loc to' m = Some frommsg),
             to = to'>>).
  Proof.
    inv MEM.
    exploit MAPPED; eauto. i. des.
    exploit ONLY; eauto. i. des.
    exploit MAPPED; try apply GET1; eauto. i. des.
    hexploit (map_eq TO0 TO1). i. subst.
    destruct (Time.le_lt_dec to to0); [destruct l|].
    - exfalso. exploit NCLPS0; eauto. econs; eauto.
    - destruct H. clarify. esplits; eauto.
      i. destruct frommsg. eapply MAPPED in GET. des.
      destruct (Time.le_lt_dec to to'); [destruct l|]; auto.
      + exfalso. exploit NCLPS1; eauto. econs; eauto.
      + exfalso. exploit NCLPS; eauto. econs; eauto.
    - exfalso. exploit NCLPS; eauto. econs; eauto.
  Qed.

  Lemma add_promises_map0 mem0 fmem0 loc from ffrom to fto msg fmsg mem1 fmem1
        (ADD0: Memory.add mem0 loc from to msg mem1)
        (PROMS: promises_map mem0 fmem0)
        (FROM: f loc from ffrom)
        (TO: f loc to fto)
        (NCLPS: non_collapsable loc to)
        (MSG: msg_map msg fmsg)
        (ADD1: Memory.add fmem0 loc ffrom fto fmsg fmem1)
    :
      promises_map mem1 fmem1.
  Proof.
    econs.
    - i. erewrite Memory.add_o in GET; eauto. des_ifs.
      + ss. des; clarify.
        esplits; eauto.
        eapply Memory.add_get0; eauto.
      + eapply msg_get_promises_map in GET; eauto.
        guardH o. des. unguard.
        esplits; eauto.
        eapply Memory.add_get1; eauto.
    - i. erewrite Memory.add_o in GET; eauto. des_ifs.
      + ss. des; clarify. exists to. esplits; eauto.
        eapply Memory.add_get0; eauto.
      + inv PROMS. eapply ONLY in GET; eauto.
        guardH o. des. esplits; eauto.
        eapply Memory.add_get1; eauto.
  Qed.

  Lemma add_promises_map mem0 fmem0 loc from ffrom to fto msg fmsg mem1
        (ADD: Memory.add mem0 loc from to msg mem1)
        (PROMS: promises_map mem0 fmem0)
        (FROM: f loc from ffrom)
        (TO: f loc to fto)
        (NCLPS: non_collapsable loc to)
        (MSG: msg_map msg fmsg)
    :
      exists fmem1,
        (<<PROMS: promises_map mem1 fmem1>>) /\
        (<<ADD: Memory.add fmem0 loc ffrom fto fmsg fmem1>>).
  Proof.
    hexploit add_succeed_wf; eauto. i. des.
    hexploit (@Memory.add_exists fmem0 loc ffrom fto fmsg).
    { i. dup GET2. dup PROMS. inv PROMS. eapply ONLY in GET2; eauto. des.
      eapply disjoint_map; eauto. }
    { erewrite <- map_lt_non_collapsable; eauto. }
    { eapply msg_wf_map; eauto. }
    i. des. esplits; eauto.
    eapply add_promises_map0; eauto.
  Qed.

  Lemma lower_promises_map mem0 fmem0 loc from to msg0 msg1 fmsg1 mem1
        (LOWER: Memory.lower mem0 loc from to msg0 msg1 mem1)
        (MEM: promises_map mem0 fmem0)
        (MSG: msg_map msg1 fmsg1)
    :
      exists ffrom fto fmsg0 fmem1,
        (<<FROM: f loc from ffrom>>) /\
        (<<TO: f loc to fto>>) /\
        (<<MSG: msg_map msg0 fmsg0>>) /\
        (<<MEM: promises_map mem1 fmem1>>) /\
        (<<LOWER: Memory.lower fmem0 loc ffrom fto fmsg0 fmsg1 fmem1>>).
  Proof.
    exploit Memory.lower_get0; eauto. i. des.
    hexploit lower_succeed_wf; eauto. i. des.
    eapply msg_get_promises_map in GET; eauto. des.
    hexploit (@Memory.lower_exists fmem0 loc ffrom fto fmsg fmsg1); eauto.
    { erewrite <- map_lt_non_collapsable; eauto. }
    { eapply msg_wf_map; eauto. }
    { eapply msg_le_map; eauto. }
    i. des. esplits; eauto.
    econs.
    - i. erewrite Memory.lower_o in GET2; eauto. des_ifs.
      + ss. des; clarify.
        esplits; eauto.
        eapply Memory.lower_get0; eauto.
      + eapply msg_get_promises_map in GET2; eauto.
        guardH o. des. unguard.
        exists fto0, ffrom0, fmsg0. esplits; eauto.
        erewrite Memory.lower_o; eauto. des_ifs.
        ss. des; clarify. exfalso. eauto.
    - i. erewrite Memory.lower_o in GET2; eauto. des_ifs.
      + ss. des; clarify.
        esplits; eauto.
      + dup MEM. inv MEM. eapply ONLY in GET2.
        guardH o. des. unguard.
        exists to0, from0, msg.
        esplits; eauto. erewrite Memory.lower_o; eauto.
        des_ifs. ss; des; clarify.
        hexploit (map_eq TO0 TO). i. clarify.
  Qed.

  Lemma split_promises_map mem0 fmem0 loc ts1 ts2 ts3 msg0 msg1 fmsg0 mem1 fts2
        (SPLIT: Memory.split mem0 loc ts1 ts2 ts3 msg0 msg1 mem1)
        (MEM: promises_map mem0 fmem0)
        (TS2: f loc ts2 fts2)
        (MSG: msg_map msg0 fmsg0)
        (NCLPS: non_collapsable loc ts2)
    :
      exists fts1 fts3 fmsg1 fmem1,
        (<<TS1: f loc ts1 fts1>>) /\
        (<<TS3: f loc ts3 fts3>>) /\
        (<<MSG: msg_map msg1 fmsg1>>) /\
        (<<MEM: promises_map mem1 fmem1>>) /\
        (<<SPLIT: Memory.split fmem0 loc fts1 fts2 fts3 fmsg0 fmsg1 fmem1>>).
  Proof.
    exploit Memory.split_get0; eauto. i. des.
    hexploit split_succeed_wf; eauto. i. des.
    eapply msg_get_promises_map in GET3; eauto. des.
    hexploit (@Memory.split_exists fmem0 loc ffrom fts2 fto fmsg0 fmsg); eauto.
    { erewrite <- map_lt_non_collapsable; try apply TS12; eauto. }
    { erewrite <- map_lt_non_collapsable; try apply TS23; eauto. }
    { eapply msg_wf_map; eauto. }
    i. des. esplits; eauto.
    econs.
    - i. erewrite Memory.split_o in GET4; eauto. des_ifs.
      + ss. des; clarify.
        exploit Memory.split_get0; eauto. i. des.
        esplits; eauto.
      + ss. des; clarify.
        exploit Memory.split_get0; eauto. i. des.
        esplits; eauto.
      + eapply msg_get_promises_map in GET4; eauto.
        guardH o. guardH o0. des. unguard.
        exists fto0, ffrom0, fmsg1. esplits; eauto.
        erewrite Memory.split_o; eauto.
        des_ifs; ss; des; clarify.
        * exploit Memory.split_get0; eauto. i. des. clarify.
        * ss. des; clarify.
          hexploit UNIQUE0; try apply TO; eauto.
          i. clarify.
    - i. erewrite Memory.split_o in GET4; eauto. des_ifs.
      + ss. des; clarify.
        esplits; eauto.
      + ss. des; clarify.
        esplits; eauto.
      + dup MEM. inv MEM. eapply ONLY in GET4.
        guardH o. guardH o0. des.
        esplits; eauto.
        erewrite Memory.split_o; eauto.
        unguard. ss. des_ifs; ss; eauto.
        * ss; des; clarify.
        * ss; des; clarify. exfalso.
          hexploit (map_eq TO0 TO). i. clarify.
  Qed.

  Lemma remove_promises_map mem0 fmem0 loc from to msg mem1
        (REMOVE: Memory.remove mem0 loc from to msg mem1)
        (MEM: promises_map mem0 fmem0)
    :
      exists ffrom fto fmsg fmem1,
        (<<TO: f loc to fto>>) /\
        (<<FROM: f loc from ffrom>>) /\
        (<<MSG: msg_map msg fmsg>>) /\
        (<<MEM: promises_map mem1 fmem1>>) /\
        (<<REMOVE: Memory.remove fmem0 loc ffrom fto fmsg fmem1>>).
  Proof.
    exploit Memory.remove_get0; eauto. i. des.
    eapply msg_get_promises_map in GET; eauto. des.
    hexploit (@Memory.remove_exists fmem0 loc ffrom fto fmsg); eauto.
    i. des. esplits; eauto.
    econs.
    - i. erewrite Memory.remove_o in GET1; eauto. des_ifs. ss.
      dup GET1. eapply msg_get_promises_map in GET1; eauto.
      guardH o. des. unguard.
      exists fto0, ffrom0, fmsg0. esplits; eauto.
      erewrite Memory.remove_o; eauto. des_ifs; ss. des; clarify.
      exploit UNIQUE; eauto. i. clarify.
    - i. erewrite Memory.remove_o in GET1; eauto. des_ifs.
      dup MEM. inv MEM. eapply ONLY in GET1.
      guardH o. des.
      esplits; eauto.
      erewrite Memory.remove_o; eauto.
      unguard. ss. des_ifs; ss; eauto.
      des; clarify. exfalso.
      hexploit (map_eq TO0 TO). i. clarify.
  Qed.

  Lemma remove_memory_map mem0 fmem0 loc from to mem1
        fto ffrom
        (REMOVE: Memory.remove mem0 loc from to Message.reserve mem1)
        (TO: f loc to fto)
        (NCLPS: non_collapsable loc to)
        (FROM: f loc from ffrom)
        (SRCGET: Memory.get loc fto fmem0 = Some (ffrom, Message.reserve))
        (MEM: memory_map mem0 fmem0)
    :
      exists fmem1,
        (<<MEM: memory_map mem1 fmem1>>) /\
        (<<REMOVE: Memory.remove fmem0 loc ffrom fto Message.reserve fmem1>>).
  Proof.
    exploit Memory.remove_get0; eauto. i. des.
    hexploit (@Memory.remove_exists fmem0 loc ffrom fto Message.reserve); eauto.
    i. des. esplits; eauto.
    econs.
    - i. erewrite Memory.remove_o in GET1; eauto. des_ifs. ss.
      dup GET1. eapply msg_get_map in GET1; eauto.
      guardH o. des; auto. unguard.
      destruct msg; auto; right.
      + exists fto0, ffrom0, fmsg', fmsg. esplits; eauto.
        erewrite Memory.remove_o; eauto. des_ifs; ss. des; clarify.
        exfalso. inv MSGLE. inv MSG.
      + exists fto0, ffrom0, fmsg', fmsg.
        esplits; eauto.
        erewrite Memory.remove_o; eauto. des_ifs; ss. des; clarify.
        inv MSG. inv MSGLE.
    - i. erewrite Memory.remove_o in GET1; eauto. des_ifs.
      apply or_strengthen in o. ss. des.
      { dup MEM. inv MEM. dup GET1. eapply ONLY in GET1.
        des; auto. left.
        exists to0, from0, fto', ffrom'. splits; auto.
        i. erewrite remove_covered; eauto. }
      apply NNPP in NOT. clarify.
      dup MEM. inv MEM. dup GET1. eapply ONLY in GET1.
      des; auto. left.
      destruct (Time.le_lt_dec to from0).
      { exists to0, from0, fto', ffrom'. splits; auto.
        i. erewrite remove_covered; [|eauto]. splits; auto.
        right. ii. inv ITV. inv H0. ss.
        eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
        { eapply FROM1. }
        etrans; eauto. }
      destruct (Time.le_lt_dec to0 from).
      { exists to0, from0, fto', ffrom'. splits; auto.
        i. erewrite remove_covered; [|eauto]. splits; auto.
        right. ii. inv ITV. inv H0. ss.
        eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
        { eapply FROM2. }
        etrans.
        { eapply TO1. }
        { eauto. } }
      dup GET2. apply memory_get_ts_strong in GET1. des; clarify.
      { exists Time.bot, Time.bot, Time.bot, Time.bot. splits; auto.
        - refl.
        - refl.
        - i. inv ITV. ss. exfalso. eapply Time.lt_strorder.
          eapply TimeFacts.lt_le_lt; eauto. }
      dup SRCGET. apply memory_get_ts_strong in SRCGET0. des; clarify.
      { assert (BOT: to = Time.bot).
        { destruct (Time.le_lt_dec to Time.bot).
          - destruct l1; auto. exfalso. eapply Time.lt_strorder.
            eapply TimeFacts.lt_le_lt.
            + apply H0.
            + apply Time.bot_spec.
          - exfalso. eapply NCLPS; eauto. econs; eauto. }
        clarify. exfalso. eapply Time.lt_strorder.
        eapply TimeFacts.lt_le_lt.
        - eapply l.
        - eapply Time.bot_spec. }
      assert (DISJOINT: Time.le fto ffrom0 \/ Time.le fto0 ffrom).
      { destruct (Time.le_lt_dec fto ffrom0); auto.
        destruct (Time.le_lt_dec fto0 ffrom); auto.
        exfalso. exploit Memory.get_disjoint.
        { eapply GET2. }
        { eapply SRCGET. }
        i. des; clarify.
        revert x0. eapply disjoint_equivalent. splits; auto.
        unfold Time.join, Time.meet. des_ifs. }
      des.
      + exists to0, to, fto', fto. splits; auto.
        i. erewrite remove_covered; [|eauto]. splits; auto.
        * eapply COVERED. inv ITV. econs; ss. etrans; eauto.
        * right. ii. inv ITV. inv H0. ss.
          eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
          { eapply FROM1. }
          { eapply TO4. }
      + exists from, from0, ffrom, ffrom'. splits; auto.
        i. erewrite remove_covered; [|eauto]. splits; auto.
        * eapply COVERED. inv ITV. econs; ss. etrans; eauto.
          left. auto.
        * right. ii. inv ITV. inv H0. ss.
          eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
          { eapply FROM2. }
          { eapply TO3. }
  Qed.

  Lemma add_memory_map mem0 fmem0 loc from ffrom to fto msg fmsg' fmsg mem1
        (ADD: Memory.add mem0 loc from to msg mem1)
        (MEM: memory_map mem0 fmem0)
        (FROM: f loc from ffrom)
        (TO: f loc to fto)
        (NCLPS: non_collapsable loc to)
        (MSG: msg_map msg fmsg')
        (MSGLE: Message.le fmsg fmsg')
        (MSGWF: Message.wf fmsg)
    :
      exists fmem1,
        (<<MEM: memory_map mem1 fmem1>>) /\
        (<<ADD: Memory.add fmem0 loc ffrom fto fmsg fmem1>>).
  Proof.
    hexploit add_succeed_wf; eauto. i. des.
    hexploit (@Memory.add_exists fmem0 loc ffrom fto fmsg).
    { i. dup GET2. dup MEM. inv MEM0. eapply ONLY in GET2. des.
      - hexploit disjoint_map.
        + eapply FROM.
        + eapply TO.
        + eapply FROM0.
        + eapply TO0.
        + ii. eapply COVERED in RHS. inv RHS.
          eapply DISJOINT in GET. eapply GET; eauto.
        + ii. eapply H; eauto. inv RHS. econs; ss.
          * eapply TimeFacts.le_lt_lt; eauto.
          * etrans; eauto.
      - eapply OUT in TO. ii. inv LHS. inv RHS. ss.
        eapply Time.lt_strorder. etrans.
        { eapply TO. }
        eapply TimeFacts.lt_le_lt; eauto. }
    { erewrite <- map_lt_non_collapsable; eauto. }
    { auto. }
    i. des. esplits; eauto.
    econs.
    - i. erewrite Memory.add_o in GET; eauto. des_ifs.
      + ss. des; clarify. right.
        esplits; eauto.
        eapply Memory.add_get0; eauto.
      + eapply msg_get_map in GET; eauto.
        guardH o. des; auto. right. unguard.
        esplits; eauto.
        eapply Memory.add_get1; eauto.
    - i. erewrite Memory.add_o in GET; eauto. des_ifs.
      + ss. des; clarify. left.
        exists to, from, fto, ffrom0. splits; auto.
        * refl.
        * refl.
        * i. econs; eauto.
          eapply Memory.add_get0; eauto.
      + guardH o. inv MEM. eapply ONLY in GET. des; auto.
        left. exists to0, from0, fto', ffrom'. splits; auto.
        i. eapply add_covered; eauto.
  Qed.

  Lemma lower_memory_map mem0 fmem0 loc from to ffrom fto msg0 fmsg0 msg1 fmsg1 fmsg1' mem1
        (LOWER: Memory.lower mem0 loc from to msg0 msg1 mem1)
        (MEM: memory_map mem0 fmem0)
        (SRCGET: Memory.get loc fto fmem0 = Some (ffrom, fmsg0))
        (MSG0: msg_map msg0 fmsg0)
        (MSG1: msg_map msg1 fmsg1')
        (MSGLE: Message.le fmsg1 fmsg1')
        (MSGWF: Message.wf fmsg1)
        (FROM: f loc from ffrom)
        (TO: f loc to fto)
        (NCLPS: non_collapsable loc to)
    :
      exists fmem1,
        (<<MEM: memory_map mem1 fmem1>>) /\
        (<<LOWER: Memory.lower fmem0 loc ffrom fto fmsg0 fmsg1 fmem1>>).
  Proof.
    exploit Memory.lower_get0; eauto. i. des.
    hexploit lower_succeed_wf; eauto. i. des.
    hexploit (@Memory.lower_exists fmem0 loc ffrom fto fmsg0 fmsg1); eauto.
    { erewrite <- map_lt_non_collapsable; eauto. }
    { etrans; eauto.
      eapply msg_le_map; eauto. }
    i. des. esplits; eauto.
    econs.
    - i. erewrite Memory.lower_o in GET2; eauto. des_ifs.
      + ss. des; clarify. right.
        esplits; eauto.
        eapply Memory.lower_get0; eauto.
      + eapply msg_get_map in GET2; eauto.
        guardH o. ss. des; auto. right.
        eapply Memory.lower_get1 in GET3; eauto. des.
        exists fto0, ffrom0, fmsg', m'. esplits; eauto.
        etrans; eauto.
    - i. erewrite Memory.lower_o in GET2; eauto. des_ifs.
      + ss. des; clarify. left.
        exists to, from, fto, ffrom0. splits; auto.
        * refl.
        * refl.
        * i. erewrite lower_covered; eauto.
          econs; eauto.
      + guardH o. inv MEM. eapply ONLY in GET2. des; auto.
        left.  exists to0, from0, fto', ffrom'. splits; auto.
        i. erewrite lower_covered; eauto.
  Qed.

  Lemma no_attach_map prom mem fmem from ffrom loc
        (NBOT: Time.lt Time.bot ffrom)
        (EMPTY: ~ covered loc from mem)
        (MEM: memory_map mem fmem)
        (FROM: f loc from ffrom)
        (UNWRITABLE: collapsable_unwritable prom mem)
        (NOATTACH: forall to msg (GET: Memory.get loc to mem = Some (from, msg)), False)
    :
      forall to msg (GET: Memory.get loc to fmem = Some (ffrom, msg)), False.
  Proof.
    i. inv MEM. dup GET. eapply ONLY in GET. des.
    - destruct (Time.le_lt_dec to0 from).
      + dup l. eapply map_le in l; eauto.
        dup GET0. eapply memory_get_ts_strong in GET1. des; clarify.
        * eapply Time.lt_strorder; eauto.
        * eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
          { apply TS. }
          etrans; eauto.
      + hexploit (@closed_point mem loc from to0); auto.
        { destruct (Time.le_lt_dec from0 from).
          - i. eapply COVERED; eauto. inv ITV. econs; ss.
            eapply TimeFacts.le_lt_lt; eauto.
          - i. destruct (Time.le_lt_dec t from0).
            + exploit UNWRITABLE.
              * exists from, from0. splits.
                { apply NNPP. ii.
                  erewrite <- map_le_iff in TS0; eauto.
                  - eapply Time.lt_strorder.
                    eapply TimeFacts.lt_le_lt; eauto.
                  - ii. symmetry in H0. eauto. }
                { inv ITV. econs; eauto. }
              * i. eapply unwritable_covered; eauto.
            + eapply COVERED; eauto. inv ITV. econs; ss. }
        i. des. destruct TS2.
        { eapply EMPTY. econs; eauto. econs; ss.
          left. auto. }
        { inv H. eauto. }
    - eapply OUT in FROM. eapply Time.lt_strorder; eauto.
  Qed.

  Lemma msg_map_message_to
        msg loc to
        fmsg' fmsg fto
        (MSG: msg_map msg fmsg')
        (MSG_LE: Message.le fmsg fmsg')
        (TO: f loc to fto)
        (TS: Memory.message_to msg loc to):
    Memory.message_to fmsg loc fto.
  Proof.
    inv MSG; inv MSG_LE; eauto. inv TS. econs.
    eapply View.unwrap_opt_le in RELEASED.
    eapply unwrap_map in MAP.
    eapply map_rlx in MAP. specialize (MAP loc).
    eapply map_le in TS0; cycle 1; eauto.
    etrans; eauto. apply RELEASED.
  Qed.

  Lemma write_add_map
        mem0 fmem0 prom0 fprom0 loc from ffrom to fto msg fmsg' fmsg mem1 prom1
        (MLE: Memory.le fprom0 fmem0)
        (ADD: Memory.write prom0 mem0 loc from to msg prom1 mem1 Memory.op_kind_add)
        (MEM: memory_map mem0 fmem0)
        (UNWRITABLE: collapsable_unwritable prom0 mem0)
        (PROM: promises_map prom0 fprom0)
        (FROM: f loc from ffrom)
        (TO: f loc to fto)
        (NCLPS: non_collapsable loc to)
        (MSG: msg_map msg fmsg')
        (MSGLE: Message.le fmsg fmsg')
        (MSGWF: Message.wf fmsg)
    :
      exists fprom1 fmem1,
        (<<MEM: memory_map mem1 fmem1>>) /\
        (<<PROM: promises_map prom1 fprom1>>) /\
        (<<ADD: Memory.write fprom0 fmem0 loc ffrom fto fmsg fprom1 fmem1 Memory.op_kind_add>>).
  Proof.
    inv ADD. inv PROMISE.
    exploit add_memory_map; try apply MEM0; try eassumption. i. des.
    exploit Memory.add_exists_le.
    { eapply MLE. }
    { eapply ADD. }
    i. des.
    exploit Memory.remove_exists.
    { eapply Memory.add_get0 in x0. des. apply GET0. }
    i. des.
    exploit (@MemoryFacts.MemoryFacts.add_remove_eq fprom0 promises0 mem2); eauto. i. clarify.
    exploit (@MemoryFacts.MemoryFacts.add_remove_eq prom0 promises2 prom1); eauto. i. clarify.
    esplits; eauto. econs; eauto. econs; eauto.
    - eapply msg_map_message_to; try exact TS; eauto.
    - i. clarify.
      assert (TS0: Time.lt Time.bot fto).
      { inv ADD. inv ADD0. eapply TimeFacts.le_lt_lt; eauto.
        eapply Time.bot_spec. }
      exploit no_attach_map; try apply MEM; eauto; cycle 1.
      { inv MSGLE; inv MSG; ss; eauto.
        i. eapply ATTACH; eauto. ss.
      }
      ii. inv H. eapply add_succeed_wf in MEM0. des.
      eapply DISJOINT.
      + eapply GET0.
      + instantiate (1:=to). econs; ss. refl.
      + eauto.
  Qed.

  Lemma write_lower_map
        mem0 fmem0 prom0 fprom0 loc from ffrom to fto msg fmsg' fmsg msg0 mem1 prom1
        (MLE: Memory.le fprom0 fmem0)
        (LOWER: Memory.write prom0 mem0 loc from to msg prom1 mem1 (Memory.op_kind_lower msg0))
        (MEM: memory_map mem0 fmem0)
        (PROM: promises_map prom0 fprom0)
        (FROM: f loc from ffrom)
        (TO: f loc to fto)
        (MSG: msg_map msg fmsg')
        (MSGLE: Message.le fmsg fmsg')
        (MSGWF: Message.wf fmsg)
    :
      exists fmsg0 fprom1 fmem1,
        (<<MSG: msg_map msg0 fmsg0>>) /\
        (<<MEM: memory_map mem1 fmem1>>) /\
        (<<PROM: promises_map prom1 fprom1>>) /\
        (<<LOWER: Memory.write fprom0 fmem0 loc ffrom fto fmsg fprom1 fmem1 (Memory.op_kind_lower fmsg0)>>).
  Proof.
    inv LOWER. inv PROMISE.
    dup PROMISES. eapply Memory.lower_get0 in PROMISES0. des. clarify.
    eapply msg_get_promises_map in GET; eauto. des.

    exploit lower_memory_map.
    { apply MEM0. }
    { apply MEM. }
    { apply MLE. apply GET. }
    { apply MSG1. }
    { apply MSG. }
    { eauto. }
    { eauto. }
    { apply FROM0. }
    { apply TO0. }
    { apply NCLPS. }
    i. des.

    exploit lower_succeed_wf; try eapply LOWER. i. des.
    exploit Memory.lower_exists; try apply GET; eauto. i. des.
    exploit Memory.remove_exists.
    { eapply Memory.lower_get0 in x0. des. eapply GET3. } i. des.
    exploit lower_remove_remove.
    { eapply PROMISES. }
    { eapply REMOVE. } intros REMOVETGT.
    exploit lower_remove_remove.
    { eapply x0. }
    { eapply x1. } intros REMOVESRC.
    exploit remove_promises_map; try apply REMOVETGT; eauto.
    i. des.
    hexploit (map_eq TO1 TO0). i. clarify.
    hexploit (map_eq FROM1 FROM0). i. clarify.
    hexploit (map_eq TO0 TO). i. clarify.
    hexploit (map_eq FROM0 FROM). i. clarify.
    exploit Memory.remove_inj.
    { eapply REMOVESRC. }
    { eapply REMOVE0. } i. clarify.

    esplits; cycle 1.
    { eauto. }
    { eauto. }
    { econs; eauto. econs; eauto; cycle 1.
      - ii. subst. inv MSGLE. inv MSG_LE0. inv MSG1. inv MSG_LE. ss.
      - eapply msg_map_message_to; try exact TS; eauto.
    }
    { ss. }
  Qed.

  Lemma split_memory_map
        mem0 fmem0 loc ts1 ts2 ts3 msg0 msg1 fmsg0 mem1 fts2
        fts1 fts3 fmsg0' fmsg1
        (SPLIT: Memory.split mem0 loc ts1 ts2 ts3 msg0 msg1 mem1)
        (MEM: memory_map mem0 fmem0)
        (SRCGET: Memory.get loc fts3 fmem0 = Some (fts1, fmsg1))
        (TS1: f loc ts1 fts1)
        (TS2: f loc ts2 fts2)
        (TS3: f loc ts3 fts3)
        (MSG: msg_map msg0 fmsg0')
        (MSGLE: Message.le fmsg0 fmsg0')
        (MSGWF: Message.wf fmsg0)
        (NCLPS2: non_collapsable loc ts2)
        (NCLPS3: non_collapsable loc ts3)
    :
      exists fmem1,
        (<<MEM: memory_map mem1 fmem1>>) /\
        (<<SPLIT: Memory.split fmem0 loc fts1 fts2 fts3 fmsg0 fmsg1 fmem1>>).
  Proof.
    exploit Memory.split_get0; eauto. i. des.
    hexploit split_succeed_wf; eauto. i. des.
    hexploit (@Memory.split_exists fmem0 loc fts1 fts2 fts3 fmsg0 fmsg1); eauto.
    { erewrite <- map_lt_non_collapsable; try apply TS12; eauto. }
    { erewrite <- map_lt_non_collapsable; try apply TS23; eauto. }
    i. des. esplits; eauto.
    econs.
    - i. erewrite Memory.split_o in GET4; eauto. des_ifs.
      + ss. des; clarify.
        exploit Memory.split_get0; eauto. i. des.
        right. esplits; eauto.
      + guardH o. eapply msg_get_map in GET3; eauto.
        des; auto. right.
        eapply Memory.split_get1 in GET4; eauto. des.
        ss. des; clarify. esplits; eauto.
      + guardH o. guardH o0. eapply msg_get_map in GET4; eauto.
        des; auto. right.
        eapply Memory.split_get1 in GET5; eauto. des.
        ss. esplits; eauto.


    - i. erewrite Memory.split_o in GET4; eauto. des_ifs.
      + ss. des; clarify. left.
        exists ts2, ts1, fts2, ffrom. esplits; eauto.
        * refl.
        * refl.
        * i. econs; cycle 1; eauto.
      + ss. guardH o. des; clarify. left.
        exists ts3, ts2, fts3, ffrom. esplits; eauto.
        * refl.
        * refl.
        * i. econs; cycle 1; eauto.
      + guardH o. guardH o0. inv MEM. eapply ONLY in GET4. des; auto.
        left. exists to, from, fto', ffrom'. splits; auto.
        i. eapply split_covered; eauto.
  Qed.

  Lemma shorten_promises_map
        mem0 fmem0 loc from from' ffrom ffrom' to fto mem1 msg fmsg fmem1
        (GET0: Memory.get loc to mem0 = Some (from, msg))
        (GET1: Memory.get loc fto fmem0 = Some (ffrom, fmsg))
        (SHORTEN0:
           forall l t,
             Memory.get l t fmem1 =
             if loc_ts_eq_dec (l, t) (loc, fto) then Some (ffrom', fmsg) else Memory.get l t fmem0)
        (SHORTEN1:
           forall l t,
             Memory.get l t mem1 =
             if loc_ts_eq_dec (l, t) (loc, to) then Some (from', msg) else Memory.get l t mem0)
        (MEM: promises_map mem0 fmem0)
        (TO: f loc to fto)
        (FROM': f loc from' ffrom')
    :
      promises_map mem1 fmem1.
  Proof.
    dup GET0. eapply msg_get_promises_map in GET0; eauto. des.
    hexploit (map_eq TO0 TO). i. clarify.
    inv MEM. econs.
    - i. erewrite SHORTEN1 in GET0. des_ifs.
      + ss. des; clarify.
        esplits; cycle 1; eauto.
        erewrite SHORTEN0. des_ifs. ss. des; clarify.
      + guardH o. apply MAPPED in GET0. des.
        esplits; eauto.
        rewrite SHORTEN0. des_ifs; eauto.
        unguard. ss; des; clarify. exfalso.
        destruct (Time.le_lt_dec to0 to).
        { destruct l; clarify.
          erewrite map_lt_non_collapsable in H; eauto.
          eapply Time.lt_strorder; eauto. }
        { erewrite map_lt_non_collapsable in l; eauto.
          eapply Time.lt_strorder; eauto. }
    - i. erewrite SHORTEN0 in GET0. des_ifs.
      + ss. des; clarify. esplits; eauto.
        erewrite SHORTEN1. des_ifs. ss. des; clarify.
      + guardH o. eapply ONLY in GET0. des.
        esplits; eauto. erewrite SHORTEN1; eauto.
        des_ifs; eauto. unguard. ss; des; clarify.
        hexploit (map_eq TO TO1). i. clarify.
  Qed.

  Lemma write_split_map
        mem0 fmem0 prom0 fprom0 loc from ffrom to fto msg fmsg' fmsg msg0 mem1 prom1 ts3
        (MLE: Memory.le fprom0 fmem0)
        (SPLIT: Memory.write prom0 mem0 loc from to msg prom1 mem1 (Memory.op_kind_split ts3 msg0))
        (MEM: memory_map mem0 fmem0)
        (PROM: promises_map prom0 fprom0)
        (FROM: f loc from ffrom)
        (TO: f loc to fto)
        (MSG: msg_map msg fmsg')
        (MSGLE: Message.le fmsg fmsg')
        (MSGWF: Message.wf fmsg)
        (NCLPS: non_collapsable loc to)
    :
      exists fmsg0 fts3 fprom1 fmem1,
        (<<MSG: msg_map msg0 fmsg0>>) /\
        (<<SPLIT: memory_map mem1 fmem1>>) /\
        (<<TS3: f loc ts3 fts3>>) /\
        (<<PROM: promises_map prom1 fprom1>>) /\
        (<<LOWER: Memory.write fprom0 fmem0 loc ffrom fto fmsg fprom1 fmem1 (Memory.op_kind_split fts3 fmsg0)>>).
  Proof.
    inv SPLIT. inv PROMISE.
    dup PROMISES. eapply Memory.split_get0 in PROMISES0. des. clarify.
    eapply msg_get_promises_map in GET0; eauto. des.
    hexploit (map_eq FROM0 FROM). i. clarify.
    exploit split_memory_map.
    { apply MEM0. }
    { apply MEM. }
    { apply MLE. apply GET0. }
    { apply FROM. }
    { apply TO. }
    { apply TO0. }
    { apply MSG. }
    { apply MSGLE. }
    { apply MSGWF. }
    { auto. }
    { auto. }
    i. des.
    exploit split_succeed_wf; try eapply SPLIT. i. des.
    exploit split_remove_exists.
    { apply GET0. }
    { eapply TS12. }
    { eapply TS23. }
    { eapply MSG_WF. }
    i. des.
    exists fmsg0, fto0, mem3, fmem1. esplits; eauto.
    - eapply shorten_promises_map; cycle 2.
      + eapply split_remove_shorten; eauto.
      + eapply split_remove_shorten; eauto.
      + eauto.
      + eauto.
      + eauto.
      + eapply Memory.split_get0 in PROMISES. des. eauto.
      + eapply Memory.split_get0 in SPLIT0. des. eauto.
    - econs; eauto. econs; eauto.
      + eapply msg_map_message_to; try exact TS; eauto.
      + ii. subst. inv MSGLE. inv MSG. ss.
      + ii. subst. inv MSG1. ss.
  Qed.

  Lemma promise_add_map
        mem0 fmem0 prom0 fprom0 loc from ffrom to fto msg fmsg mem1 prom1
        (MLE: Memory.le fprom0 fmem0)
        (ADD: Memory.promise prom0 mem0 loc from to msg prom1 mem1 Memory.op_kind_add)
        (MEM: memory_map mem0 fmem0)
        (PROM: promises_map prom0 fprom0)
        (UNWRITABLE: collapsable_unwritable prom0 mem0)
        (FROM: f loc from ffrom)
        (TO: f loc to fto)
        (NCLPS: non_collapsable loc to)
        (MSG: msg_map msg fmsg)
    :
      exists fprom1 fmem1,
        (<<MEM: memory_map mem1 fmem1>>) /\
        (<<PROM: promises_map prom1 fprom1>>) /\
        (<<ADD: Memory.promise fprom0 fmem0 loc ffrom fto fmsg fprom1 fmem1 Memory.op_kind_add>>).
  Proof.
    inv ADD.
    exploit add_memory_map; try apply MEM0; try eassumption.
    { refl. }
    { eapply msg_wf_map; eauto.
      exploit add_succeed_wf; try apply MEM0. i. des. auto. }
    i. des.
    exploit add_promises_map; try apply PROMISES; try eassumption.
    i. des.
    esplits; eauto. econs; eauto.
    - eapply msg_map_message_to; try exact TS; eauto. refl.
    - i.
      assert (TS0: Time.lt Time.bot fto).
      { inv ADD. inv ADD1. eapply TimeFacts.le_lt_lt; eauto.
        eapply Time.bot_spec. }
      exploit no_attach_map; try apply MEM; eauto.
      { ii. inv H. eapply add_succeed_wf in MEM0. des.
        eapply DISJOINT.
        + eapply GET0.
        + instantiate (1:=to). econs; ss. refl.
        + eauto.
      }
      i. eapply ATTACH; eauto.
      ii. subst. inv MSG. ss.
  Qed.

  Lemma promise_lower_map
        mem0 fmem0 prom0 fprom0 loc from ffrom to fto msg fmsg mem1 prom1 msg0
        (MLE: Memory.le fprom0 fmem0)
        (LOWER: Memory.promise prom0 mem0 loc from to msg prom1 mem1 (Memory.op_kind_lower msg0))
        (MEM: memory_map mem0 fmem0)
        (PROM: promises_map prom0 fprom0)
        (FROM: f loc from ffrom)
        (TO: f loc to fto)
        (NCLPS: non_collapsable loc to)
        (MSG: msg_map msg fmsg)
    :
      exists fmsg0 fprom1 fmem1,
        (<<MEM: memory_map mem1 fmem1>>) /\
        (<<MSG: msg_map msg0 fmsg0>>) /\
        (<<PROM: promises_map prom1 fprom1>>) /\
        (<<LOWER: Memory.promise fprom0 fmem0 loc ffrom fto fmsg fprom1 fmem1 (Memory.op_kind_lower fmsg0)>>).
  Proof.
    inv LOWER.
    exploit lower_promises_map; try apply PROMISES; try eassumption.
    i. des.
    exploit lower_succeed_wf; try apply LOWER; eauto. i. des. clarify.
    hexploit (map_eq TO TO0). i. clarify.
    hexploit (map_eq FROM FROM0). i. clarify.
    exploit lower_memory_map; try apply MEM0; try eassumption.
    { eapply MLE. eauto. }
    { refl. }
    i. des. esplits; eauto. econs; eauto.
    - eapply msg_map_message_to; try exact TS; eauto. refl.
    - ii. subst. inv MSG. ss.
  Qed.

  Lemma promise_split_map mem0 fmem0 prom0 fprom0 loc from ffrom to fto msg fmsg mem1 prom1 ts3 msg0
        (MLE: Memory.le fprom0 fmem0)
        (SPLIT: Memory.promise prom0 mem0 loc from to msg prom1 mem1 (Memory.op_kind_split ts3 msg0))
        (MEM: memory_map mem0 fmem0)
        (PROM: promises_map prom0 fprom0)
        (FROM: f loc from ffrom)
        (TO: f loc to fto)
        (NCLPS: non_collapsable loc to)
        (MSG: msg_map msg fmsg)
    :
      exists fmsg0 fts3 fprom1 fmem1,
        (<<MEM: memory_map mem1 fmem1>>) /\
        (<<TS3: f loc ts3 fts3>>) /\
        (<<MSG: msg_map msg0 fmsg0>>) /\
        (<<PROM: promises_map prom1 fprom1>>) /\
        (<<SPLIT: Memory.promise fprom0 fmem0 loc ffrom fto fmsg fprom1 fmem1 (Memory.op_kind_split fts3 fmsg0)>>).
  Proof.
    inv SPLIT.
    exploit split_promises_map; try apply PROMISES; try eassumption.
    i. des.
    exploit split_succeed_wf; try apply SPLIT; eauto. i. des. clarify.
    hexploit (map_eq FROM TS1). i. clarify.
    exploit split_memory_map; try apply MEM0; try eassumption.
    { eapply MLE. eauto. }
    { refl. }
    { eapply Memory.split_get0 in PROMISES. des.
      inv PROM. eapply MAPPED in GET0. des. auto. }
    i. des. esplits; eauto. econs; eauto.
    - eapply msg_map_message_to; try exact TS; eauto. refl.
    - ii. subst. inv MSG. ss.
    - ii. subst. inv MSG1. ss.
  Qed.

  Lemma promise_cancel_map mem0 fmem0 prom0 fprom0 loc from ffrom to fto msg fmsg mem1 prom1
        (MLE: Memory.le fprom0 fmem0)
        (CANCEL: Memory.promise prom0 mem0 loc from to msg prom1 mem1 Memory.op_kind_cancel)
        (MEM: memory_map mem0 fmem0)
        (PROM: promises_map prom0 fprom0)
        (FROM: f loc from ffrom)
        (TO: f loc to fto)
        (NCLPS: non_collapsable loc to)
        (MSG: msg_map msg fmsg)
    :
      exists fprom1 fmem1,
        (<<MEM: memory_map mem1 fmem1>>) /\
        (<<PROM: promises_map prom1 fprom1>>) /\
        (<<CANCEL: Memory.promise fprom0 fmem0 loc ffrom fto fmsg fprom1 fmem1 Memory.op_kind_cancel>>).
  Proof.
    inv CANCEL.
    exploit remove_promises_map; try apply PROMISES; try eassumption.
    i. des.
    hexploit (map_eq FROM FROM0). i. clarify.
    hexploit (map_eq TO TO0). i. clarify.
    inv MSG. inv MSG0.
    exploit remove_memory_map; try apply MEM0; try eassumption.
    { eapply MLE. eapply Memory.remove_get0 in REMOVE. des. auto. }
    i. des. esplits; eauto.
  Qed.

  Lemma promise_map mem0 fmem0 prom0 fprom0 loc from ffrom to fto msg fmsg mem1 prom1 kind
        (MLE: Memory.le fprom0 fmem0)
        (PROMISE: Memory.promise prom0 mem0 loc from to msg prom1 mem1 kind)
        (MEM: memory_map mem0 fmem0)
        (PROM: promises_map prom0 fprom0)
        (UNWRITABLE: collapsable_unwritable prom0 mem0)
        (FROM: f loc from ffrom)
        (TO: f loc to fto)
        (NCLPS: non_collapsable loc to)
        (MSG: msg_map msg fmsg)
    :
      exists fkind fprom1 fmem1,
        (<<MEM: memory_map mem1 fmem1>>) /\
        (<<KIND: memory_op_kind_map loc kind fkind>>) /\
        (<<PROM: promises_map prom1 fprom1>>) /\
        (<<PROMISE: Memory.promise fprom0 fmem0 loc ffrom fto fmsg fprom1 fmem1 fkind>>).
  Proof.
    inv PROMISE.
    - exploit promise_add_map; try apply PROM; eauto. i. des.
      esplits; eauto.
    - exploit promise_split_map; try apply PROM; eauto. i. des.
      esplits; eauto.
    - exploit promise_lower_map; try apply PROM; eauto. i. des.
      esplits; eauto.
    - exploit promise_cancel_map; try apply PROM; try apply MEM; eauto. i. des.
      esplits; eauto.
  Qed.

  Lemma write_map
        mem0 fmem0 prom0 fprom0 loc from ffrom to fto mem1 prom1 kind
        msg fmsg' fmsg
        (MLE: Memory.le fprom0 fmem0)
        (WRITE: Memory.write prom0 mem0 loc from to msg prom1 mem1 kind)
        (MEM: memory_map mem0 fmem0)
        (PROM: promises_map prom0 fprom0)
        (UNWRITABLE: collapsable_unwritable prom0 mem0)
        (FROM: f loc from ffrom)
        (TO: f loc to fto)
        (NCLPS: non_collapsable loc to)
        (MSG: msg_map msg fmsg')
        (MSGLE: Message.le fmsg fmsg')
        (MSGWF: Message.wf fmsg)
    :
      exists fkind fprom1 fmem1,
        (<<MEM: memory_map mem1 fmem1>>) /\
        (<<KIND: memory_op_kind_map loc kind fkind>>) /\
        (<<PROM: promises_map prom1 fprom1>>) /\
        (<<WRITE: Memory.write fprom0 fmem0 loc ffrom fto fmsg fprom1 fmem1 fkind>>).
  Proof.
    exploit Memory.write_not_cancel; eauto. i.
    destruct kind; ss.
    - exploit write_add_map; try apply WRITE; eauto. i. des.
      esplits; eauto.
    - exploit write_split_map; try apply WRITE; eauto. i. des.
      esplits; eauto.
    - exploit write_lower_map; try apply WRITE; eauto. i. des.
      esplits; eauto.
  Qed.

  Lemma write_na_map
        ts mem0 prom0 loc from to val prom1 mem1 msgs kinds kind
        fts' fts fmem0 fprom0 ffrom fto ffts
        (WRITE: Memory.write_na ts prom0 mem0 loc from to val prom1 mem1 msgs kinds kind)
        (MLE: Memory.le fprom0 fmem0)
        (TS: f loc ts fts')
        (TSLE: Time.le fts fts')
        (MEM: memory_map mem0 fmem0)
        (PROM: promises_map prom0 fprom0)
        (UNWRITABLE: collapsable_unwritable prom0 mem0)
        (FROM: f loc from ffrom)
        (TO: f loc to fto)
        (NCLPS: non_collapsable loc to)
        (MSGS: List.Forall2
                 (fun m fm =>
                    f loc (fst (fst m)) (fst fm) /\
                    f loc (snd (fst m)) (snd fm))
                 msgs ffts)
        (MSGS_NCLPS: List.Forall (fun m => non_collapsable loc (snd (fst m))) msgs)
    :
      exists fmsgs fkinds fkind fprom1 fmem1,
        (<<MEM: memory_map mem1 fmem1>>) /\
        (<<MSGS: List.Forall2
                   (fun m fm =>
                      f loc (fst (fst m)) (fst (fst fm)) /\
                      f loc (snd (fst m)) (snd (fst fm)) /\
                      msg_map (snd m) (snd fm))
                 msgs fmsgs>>) /\
        (<<KIND: memory_op_kind_map loc kind fkind>>) /\
        (<<PROM: promises_map prom1 fprom1>>) /\
        (<<WRITE: Memory.write_na fts fprom0 fmem0 loc ffrom fto val fprom1 fmem1 fmsgs fkinds fkind>>).
  Proof.
    revert_until WRITE.
    revert fts' fts fmem0 fprom0 ffrom fto ffts.
    induction WRITE; i.
    { inv MSGS.
      exploit write_map;
        try match goal with
            | [|- msg_map ?a ?b] => econs 3
            | [|- Message.le ?a ?b] => try refl
            end; eauto.
      { econs. }
      i. des.
      esplits; eauto.
      econs; ss.
      eapply TimeFacts.le_lt_lt; eauto.
      exploit map_le; (try by econs; exact WRITABLE); eauto.
      i. inv x; ss. inv H.
      exploit NCLPS; eauto; ss.
      exists fto. splits; ss.
    }

    inv MSGS. inv MSGS_NCLPS. des.
    destruct y as [ffrom' fto']. ss.
    assert (MSG': exists fmsg', msg_map msg' fmsg' /\ Message.wf fmsg').
    { unguard. des; subst.
      - esplits; econs.
      - esplits; econs; econs.
    }
    des.
    exploit write_map; try exact WRITE_EX; eauto; try refl. i. des.
    hexploit Memory.write_le; eauto. i. des.
    exploit IHWRITE; try exact H; eauto; try refl.
    { ii. exploit UNWRITABLE; eauto. i. inv x. econs; eauto.
      eapply unchangable_write; eauto.
    }
    i. des. esplits; eauto.
    - instantiate (1 := (ffrom', fto', fmsg') :: fmsgs). eauto.
    - econs 2; eauto.
      + exploit map_le; (try by econs; exact WRITABLE_EX); eauto.
        i. eapply TimeFacts.le_lt_lt; eauto.
        inv x; ss. inv H5.
        exploit H2; eauto; ss.
        exists fto'. splits; ss.
      + unguard. des; subst; inv MSG'; eauto. inv MAP. eauto.
  Qed.


  Inductive local_map (lc flc: Local.t): Prop :=
  | local_map_intro
      ftv'
      (TVIEWLE: TView.le (Local.tview flc) ftv')
      (TVIEW: tview_map (Local.tview lc) ftv')
      (* (TVWF: TView.wf ftv') *)
      (PROMISES: promises_map (Local.promises lc) (Local.promises flc))
  .

  Lemma read_step_map lc0 flc0 mem0 fmem0 loc to val released ord lc1
        (LOCAL: local_map lc0 flc0)
        (TVWF: TView.wf (Local.tview flc0))
        (MEM: memory_map mem0 fmem0)
        (READ: Local.read_step lc0 mem0 loc to val released ord lc1)
    :
      exists fto freleased' freleased flc1,
        (<<READ: Local.read_step flc0 fmem0 loc fto val freleased ord flc1>>) /\
        (<<TO: f loc to fto>>) /\
        (<<RELEASED: opt_view_map released freleased'>>) /\
        (<<RELEASEDLE: View.opt_le freleased freleased'>>) /\
        (<<LOCAL: local_map lc1 flc1>>).
  Proof.
    inv LOCAL. inv READ. exploit msg_get_map; eauto. i. des; clarify.
    inv MSG. inv MSGLE.
    eapply readable_map in READABLE; eauto; cycle 1.
    { eapply map_cur; eauto. }
    esplits.
    - econs; eauto; try by (etrans; eauto).
      eapply TViewFacts.readable_mon; eauto.
      + inv TVIEWLE. auto.
      + refl.
    - auto.
    - eauto.
    - eauto.
    - econs; ss.
      + eapply read_tview_mon.
        * eapply TVIEWLE.
        * eauto.
        * refl.
      + eapply read_tview_map; eauto.
  Qed.

  Lemma write_released_mon_same_ord
        tview1 tview2 ord loc to sc1 sc2 released1 released2
        (SC: TimeMap.le sc1 sc2)
        (TVIEW: TView.le tview1 tview2)
        (RELEASED: View.opt_le released1 released2)
    :
      View.opt_le
        (TView.write_released tview1 sc1 loc to released1 ord)
        (TView.write_released tview2 sc2 loc to released2 ord).
  Proof.
    unfold TView.write_released.
    dup TVIEW. inv TVIEW. des_ifs. econs.
    eapply view_join_mon; eauto.
    - eapply View.unwrap_opt_le; eauto.
    - exploit write_tview_mon_same_ord; eauto. i.
      inv x0. eauto.
  Qed.

  Lemma write_step_map
        lc0 flc0 mem0 mem1 fmem0 loc from to val releasedr releasedw ord lc1
        kind ffrom fto freleasedr freleasedr' sc0 sc1 fsc0 fsc0'
        (LOCAL: local_map lc0 flc0)
        (MLE: Memory.le (Local.promises flc0) fmem0)
        (TVWF: TView.wf (Local.tview flc0))
        (MEM: memory_map mem0 fmem0)
        (UNWRITABLE: collapsable_unwritable (Local.promises lc0) mem0)
        (RELEASEDR: opt_view_map releasedr freleasedr')
        (RELEASEDRLE: View.opt_le freleasedr freleasedr')
        (RELEASEDRWF: View.opt_wf freleasedr)
        (FROM: f loc from ffrom)
        (TO: f loc to fto)
        (NCLPS: non_collapsable loc to)
        (SC: timemap_map sc0 fsc0')
        (SCLE: TimeMap.le fsc0 fsc0')
        (WRITE: Local.write_step lc0 sc0 mem0 loc from to val releasedr releasedw ord lc1 sc1 mem1 kind)
    :
      exists flc1 fmem1 fsc1' fsc1 freleasedw' freleasedw fkind,
        (<<WRITE: Local.write_step flc0 fsc0 fmem0 loc ffrom fto val freleasedr freleasedw ord flc1 fsc1 fmem1 fkind>>) /\
        (<<RELEASEDW: opt_view_map releasedw freleasedw'>>) /\
        (<<RELEASEDWLE: View.opt_le freleasedw freleasedw'>>) /\
        (<<LOCAL: local_map lc1 flc1>>) /\
        (<<SC: timemap_map sc1 fsc1'>>) /\
        (<<SCLE: TimeMap.le fsc1 fsc1'>>) /\
        (<<MEM: memory_map mem1 fmem1>>) /\
        (<<KIND: memory_op_kind_map loc kind fkind>>)
  .
  Proof.
    inv LOCAL. inv WRITE.
    exploit write_released_map; eauto. intros RELEASEDW.
    exploit write_released_mon_same_ord.
    { eapply SCLE. }
    { eapply TVIEWLE. }
    { eapply RELEASEDRLE. }
    intros VIEWLE.
    exploit write_map.
    { eauto. }
    { eauto. }
    { ss. }
    { ss. }
    { ss. }
    { eauto. }
    { eauto. }
    { ss. }
    { econs 3. eauto. }
    { econs; try eapply VIEWLE. refl. }
    { econs. eapply TViewFacts.write_future0; eauto. }
    i. des.
    esplits; eauto.
    - econs; eauto.
      + eapply TViewFacts.writable_mon.
        * eapply TVIEWLE.
        * eapply SCLE.
        * refl.
        * eapply writable_map; eauto. eapply TVIEW.
      + i. eapply nonsynch_loc_map; eauto.
    - econs; ss.
      + eapply write_tview_mon_same_ord.
        { eapply TVIEWLE. }
        { eapply SCLE. }
      + eapply write_tview_map; eauto.
  Qed.

  Lemma write_na_step_map
        lc0 flc0 mem0 mem1 fmem0 loc from to val ord lc1 msgs kinds kind
        ffrom fto sc0 sc1 fsc0 fsc0' ffts
        (LOCAL: local_map lc0 flc0)
        (MLE: Memory.le (Local.promises flc0) fmem0)
        (TVWF: TView.wf (Local.tview flc0))
        (MEM: memory_map mem0 fmem0)
        (UNWRITABLE: collapsable_unwritable (Local.promises lc0) mem0)
        (FROM: f loc from ffrom)
        (TO: f loc to fto)
        (NCLPS: non_collapsable loc to)
        (SC: timemap_map sc0 fsc0')
        (SCLE: TimeMap.le fsc0 fsc0')
        (MSGS: List.Forall2
                 (fun m fm =>
                    f loc (fst (fst m)) (fst fm) /\
                    f loc (snd (fst m)) (snd fm))
                 msgs ffts)
        (MSGS_NCLPS: List.Forall (fun m => non_collapsable loc (snd (fst m))) msgs)
        (WRITE: Local.write_na_step lc0 sc0 mem0 loc from to val ord lc1 sc1 mem1 msgs kinds kind)
    :
      exists flc1 fmem1 fsc1' fsc1 fmsgs fkinds fkind,
        (<<WRITE: Local.write_na_step flc0 fsc0 fmem0 loc ffrom fto val ord flc1 fsc1 fmem1 fmsgs fkinds fkind>>) /\
        (<<LOCAL: local_map lc1 flc1>>) /\
        (<<SC: timemap_map sc1 fsc1'>>) /\
        (<<SCLE: TimeMap.le fsc1 fsc1'>>) /\
        (<<MEM: memory_map mem1 fmem1>>) /\
        (<<MSGS: List.Forall2
                   (fun m fm =>
                      f loc (fst (fst m)) (fst (fst fm)) /\
                      f loc (snd (fst m)) (snd (fst fm)) /\
                      msg_map (snd m) (snd fm))
                 msgs fmsgs>>) /\
        (<<KIND: memory_op_kind_map loc kind fkind>>)
  .
  Proof.
    inv LOCAL. inv WRITE.
    exploit write_na_map.
    { eauto. }
    { eauto. }
    { eapply map_cur. eauto. }
    { eapply TVIEWLE. }
    { ss. }
    { ss. }
    { ss. }
    { eauto. }
    { eauto. }
    { ss. }
    { eauto. }
    { eauto. }
    i. des.
    esplits; eauto.
    econs; ss.
    - eapply write_tview_mon_same_ord.
      { eapply TVIEWLE. }
      { eapply SCLE. }
    - eapply write_tview_map; eauto.
  Qed.

  Lemma nonsynch_map prom fprom
        (PROMS: promises_map prom fprom)
        (NONSYNCH: Memory.nonsynch prom)
    :
      Memory.nonsynch fprom.
  Proof.
    ii. dup GET.
    inv PROMS. exploit ONLY; eauto. i. des.
    exploit MAPPED; eauto. i. des.
    hexploit (map_eq TO TO0). i. clarify.
    eapply NONSYNCH in GET1. des_ifs.
    - inv MSG. inv MAP. ss.
    - inv MSG.
    - inv MSG.
  Qed.

  Lemma fence_step_map lc0 flc0 sc0 sc1 fsc0' fsc0 ordr ordw lc1
        (LOCAL: local_map lc0 flc0)
        (SC: timemap_map sc0 fsc0')
        (SCLE: TimeMap.le fsc0 fsc0')
        (TVWF: TView.wf (Local.tview flc0))
        (FENCE: Local.fence_step lc0 sc0 ordr ordw lc1 sc1)
    :
      exists flc1 fsc1 fsc1',
        (<<FENCE: Local.fence_step flc0 fsc0 ordr ordw flc1 fsc1>>) /\
        (<<LOCAL: local_map lc1 flc1>>) /\
        (<<SC: timemap_map sc1 fsc1'>>) /\
        (<<SCLE: TimeMap.le fsc1 fsc1'>>)
  .
  Proof.
    inv LOCAL. inv FENCE.
    exploit read_fence_tview_map; eauto. intros READVIEW.
    exploit read_fence_tview_mon_same_ord; eauto. intros READVIEWLE.
    exploit write_fence_tview_map; eauto. intros WRITEVIEW.
    exploit write_fence_tview_mon_same_ord; eauto. intros WRITEVIEWLE.
    esplits.
    - econs; ss.
      + i. eapply nonsynch_map; eauto.
      + i. subst. erewrite PROMISES0 in PROMISES; eauto.
        eapply bot_promises_map; eauto.
    - econs; eauto.
    - eapply write_fence_sc_map; eauto.
    - eapply write_fence_fc_mon_same_ord; eauto.
  Qed.

  Lemma promise_consistent_mon vw0 vw1 prom0 prom1
        (CONSISTENT: Local.promise_consistent (Local.mk vw1 prom1))
        (VIEW: TView.le vw0 vw1)
        (MLE: Memory.le prom0 prom1)
    :
      Local.promise_consistent (Local.mk vw0 prom0).
  Proof.
    ii. eapply MLE in PROMISE. eapply CONSISTENT in PROMISE.
    eapply TimeFacts.le_lt_lt; eauto. inv VIEW. inv CUR. ss.
  Qed.

  Lemma promise_consistent_local_map
        lc flc
        (LOCAL: local_map lc flc)
        (CONS: Local.promise_consistent lc):
    Local.promise_consistent flc.
  Proof.
    destruct lc, flc. inv LOCAL. ss.
    eapply promise_consistent_mon.
    { eapply promise_consistent_map; eauto. }
    { eauto. }
    { refl. }
  Qed.

  Lemma failure_step_map lc0 flc0
        (LOCAL: local_map lc0 flc0)
        (FAILURE: Local.failure_step lc0)
    :
      Local.failure_step flc0.
  Proof.
    inv FAILURE. econs.
    eapply promise_consistent_local_map; eauto.
  Qed.

  Lemma racy_view_map
        lc loc to flc fto
        (MAP_LT: mapping_map_lt)
        (LOCAL: local_map lc flc)
        (TO: f loc to fto)
        (RACE: TView.racy_view lc.(Local.tview).(TView.cur) loc to):
    TView.racy_view flc.(Local.tview).(TView.cur) loc fto.
  Proof.
    unfold TView.racy_view in *. inv LOCAL.
    exploit MAP_LT; try exact RACE; try eapply TVIEW; eauto. i.
    eapply TimeFacts.le_lt_lt; eauto. apply TVIEWLE.
  Qed.

  Lemma is_racy_map
        lc mem loc to ord
        flc fmem
        (MAP_LT: mapping_map_lt)
        (LOCAL: local_map lc flc)
        (MEM: memory_map mem fmem)
        (WF: Local.wf lc mem)
        (UNWRITABLE: collapsable_unwritable (Local.promises lc) mem)
        (RACE: Local.is_racy lc mem loc to ord):
    exists fto,
      (<<RACE: Local.is_racy flc fmem loc fto ord>>) /\
      (<<TO: f loc to fto>>).
  Proof.
    inv RACE. exploit msg_get_map; eauto. i. des; try congr.
    esplits; eauto. econs; eauto.
    - destruct (Memory.get loc fto (Local.promises flc)) as [[]|] eqn:GETPF; ss.
      inv LOCAL. inv PROMISES. exploit ONLY; eauto. i. des.
      destruct (classic (to = to0)); try by congr.
      destruct (TimeFacts.le_lt_dec to to0).
      + inv l; ss. exploit MAP_LT; try exact H0; eauto. i. timetac.
      + exploit MAP_LT; try exact l; eauto. i. timetac.
    - eapply racy_view_map; eauto.
    - ii. subst. inv MSGLE. inv MSG. ss.
    - i. exploit MSG2; eauto. i. subst.
      inv MSG. inv MSGLE. ss.
  Qed.

  Lemma racy_read_step_map
        lc mem loc to val ord
        flc fmem
        (MAP_LT: mapping_map_lt)
        (LOCAL: local_map lc flc)
        (MEM: memory_map mem fmem)
        (WF: Local.wf lc mem)
        (UNWRITABLE: collapsable_unwritable (Local.promises lc) mem)
        (RACE: Local.racy_read_step lc mem loc to val ord):
    exists fto,
      (<<RACE: Local.racy_read_step flc fmem loc fto val ord>>) /\
      (<<TO: f loc to fto>>).
  Proof.
    inv RACE.
    exploit is_racy_map; eauto. i. des.
    esplits; eauto.
  Qed.

  Lemma racy_write_step_map
        lc mem loc to ord
        flc fmem
        (MAP_LT: mapping_map_lt)
        (LOCAL: local_map lc flc)
        (MEM: memory_map mem fmem)
        (WF: Local.wf lc mem)
        (UNWRITABLE: collapsable_unwritable (Local.promises lc) mem)
        (RACE: Local.racy_write_step lc mem loc to ord):
    exists fto,
      (<<RACE: Local.racy_write_step flc fmem loc fto ord>>) /\
      (<<TO: f loc to fto>>).
  Proof.
    inv RACE.
    exploit is_racy_map; eauto. i. des.
    esplits; eauto using promise_consistent_local_map.
  Qed.

  Lemma racy_update_step_map
        lc mem loc to ordr ordw
        flc fmem
        (MAP_LT: mapping_map_lt)
        (LOCAL: local_map lc flc)
        (MEM: memory_map mem fmem)
        (WF: Local.wf lc mem)
        (UNWRITABLE: collapsable_unwritable (Local.promises lc) mem)
        (RACE: Local.racy_update_step lc mem loc to ordr ordw):
    exists fto,
      (<<RACE: Local.racy_update_step flc fmem loc fto ordr ordw>>) /\
      (<<TO: f loc to fto>>).
  Proof.
    inv RACE.
    - esplits; [econs 1|]; eauto using promise_consistent_local_map.
    - esplits; [econs 2|]; eauto using promise_consistent_local_map.
    - exploit is_racy_map; eauto. i. des.
      esplits; [econs 3|]; eauto using promise_consistent_local_map.
  Qed.

  Definition mappable_time loc to :=
    exists fto, (<<MAPPED: f loc to fto>>).

  Definition mappable_memory mem :=
    forall loc to from val released (GET: Memory.get loc to mem = Some (from, Message.concrete val released)),
      mappable_time loc to.

  Lemma mappable_memory_op mem0 loc from to msg mem1 kind
        (OP: Memory.op mem0 loc from to msg mem1 kind)
        (FROM: mappable_time loc from)
        (TO: mappable_time loc to)
        (MEM: mappable_memory mem0)
    :
      mappable_memory mem1.
  Proof.
    ii. inv OP.
    - erewrite Memory.add_o in GET; eauto. des_ifs; eauto.
      ss. des; clarify.
    - erewrite Memory.split_o in GET; eauto. des_ifs; eauto.
      + ss. des; clarify.
      + ss. des; clarify.
        eapply Memory.split_get0 in SPLIT. des. eauto.
    - erewrite Memory.lower_o in GET; eauto. des_ifs; eauto.
      ss. des; clarify.
    - erewrite Memory.remove_o in GET; eauto. des_ifs; eauto.
  Qed.

  Lemma memory_map_mappable mem fmem
        (MEM: memory_map mem fmem)
    :
      mappable_memory mem.
  Proof.
    inv MEM. ii.
    eapply MAPPED in GET. des; clarify.
    eexists. eauto.
  Qed.

  Lemma mappable_memory_closed_timemap_exists
        tm mem
        (CLOSED: Memory.closed_timemap tm mem)
        (MEM: mappable_memory mem)
    :
      exists ftm, (<<TM: timemap_map tm ftm>>).
  Proof.
    unfold timemap_map.
    exploit (choice (fun loc t => f loc (tm loc) t)).
    - intros loc. specialize (CLOSED loc). des.
      eapply MEM in CLOSED. eauto.
    - i. des. eauto.
  Qed.

  Lemma mappable_memory_closed_view_exists
        vw mem
        (CLOSED: Memory.closed_view vw mem)
        (MEM: mappable_memory mem)
    :
      exists fvw, (<<VW: view_map vw fvw>>).
  Proof.
    inv CLOSED.
    eapply mappable_memory_closed_timemap_exists in PLN; eauto.
    eapply mappable_memory_closed_timemap_exists in RLX; eauto.
    des. exists (View.mk ftm0 ftm). econs; eauto.
  Qed.

  Lemma mappable_memory_closed_opt_view_exists
        vw mem
        (CLOSED: Memory.closed_opt_view vw mem)
        (MEM: mappable_memory mem)
    :
      exists fvw, (<<VW: opt_view_map vw fvw>>).
  Proof.
    inv CLOSED.
    - eapply mappable_memory_closed_view_exists in CLOSED0; eauto.
      des. esplits. econs; eauto.
    - esplits. econs.
  Qed.

  Lemma mappable_memory_closed_msg_exists
        msg mem
        (CLOSED: Memory.closed_message msg mem)
        (MEM: mappable_memory mem)
    :
      exists fmsg, (<<MSG: msg_map msg fmsg>>).
  Proof.
    inv CLOSED.
    - eapply mappable_memory_closed_opt_view_exists in CLOSED0; eauto.
      des. esplits. econs; eauto.
    - esplits. econs.
    - esplits. econs.
  Qed.

  Lemma msg_map_exists mem fmem msg
        (MEM: memory_map mem fmem)
        (CLOSED: Memory.closed_message msg mem)
    :
      exists fmsg,
        (<<MSG: msg_map msg fmsg>>) /\
        (<<CLOSED: Memory.closed_message fmsg fmem>>).
  Proof.
    inv CLOSED.
    - exploit opt_view_map_exists; eauto. i. des.
      exists (Message.concrete val fvw).
      esplits; eauto. econs; eauto.
    - exists Message.undef.
      esplits; eauto. econs; eauto.
    - exists Message.reserve.
      esplits; eauto. econs; eauto.
  Qed.

  Lemma closed_message_map mem fmem msg fmsg
        (MEM: memory_map mem fmem)
        (MSG: msg_map msg fmsg)
        (CLOSED: Memory.closed_message msg mem)
    :
      Memory.closed_message fmsg fmem.
  Proof.
    inv CLOSED.
    - inv MSG. econs.
      eapply closed_opt_view_map; eauto.
    - inv MSG. econs.
    - inv MSG. econs.
  Qed.

  Definition mappable_evt (e: ThreadEvent.t) : Prop :=
    match e with
    | ThreadEvent.promise loc from to msg kind =>
      (<<FROM: mappable_time loc from>>) /\
      (<<TO: mappable_time loc to>>)
    | ThreadEvent.write loc from to val released ordw =>
      (<<FROM: mappable_time loc from>>) /\
      (<<TO: mappable_time loc to>>)
    | ThreadEvent.write_na loc msgs from to val ord =>
      (<<MSGS: List.Forall
                 (fun m => mappable_time loc (fst (fst m)) /\ mappable_time loc (snd (fst m)))
                 msgs>>) /\
      (<<FROM: mappable_time loc from>>) /\
      (<<TO: mappable_time loc to>>)
    | ThreadEvent.update loc from to valr valw releasedr releasedw ordr ordw =>
      (<<FROM: mappable_time loc from>>) /\
      (<<TO: mappable_time loc to>>)
    | _ => True
    end.

  Lemma wf_time_mapped_mappable (tr: Trace.t) times
        (WFTIME: List.Forall (fun em => wf_time_evt times (snd em)) tr)
        (COMPLETE: forall loc to (IN: times loc to),
            exists fto, (<<MAPPED: f loc to fto>>))
    :
      List.Forall (fun em => mappable_evt (snd em)) tr.
  Proof.
    eapply List.Forall_impl; eauto. i. ss. destruct a. destruct t0; ss.
    - des. split.
      + apply COMPLETE in FROM. des. esplit. eauto.
      + apply COMPLETE in TO. des. esplit. eauto.
    - des. split.
      + apply COMPLETE in FROM. des. esplit. eauto.
      + apply COMPLETE in TO. des. esplit. eauto.
    - des. splits.
      + clear - MSGS COMPLETE. induction MSGS; ss.
        des. econs; eauto. apply COMPLETE in H, H0. des.
        split; esplit; eauto.
      + apply COMPLETE in FROM. des. esplit. eauto.
      + apply COMPLETE in TO. des. esplit. eauto.
    - des. split.
      + apply COMPLETE in FROM. des. esplit. eauto.
      + apply COMPLETE in TO. des. esplit. eauto.
  Qed.

  Lemma wf_time_evt_map times te fte
        (WF: wf_time_evt times te)
        (MAP: tevent_map fte te)
    :
      wf_time_evt (fun loc fts => exists ts, (<<IN: times loc ts>>) /\ (<<MAP: f loc ts fts>>)) fte.
  Proof.
    inv MAP; ss.
    { des. splits; eauto. }
    { des. splits; eauto. }
    { des. splits; eauto.
      clear - MSGS MSGS0. induction MSGS; eauto.
      inv MSGS0. exploit IHMSGS; eauto. i. econs; eauto.
      des. splits; eauto.
    }
    { des. splits; eauto. }
  Qed.

  Lemma mappable_messages_exists
        loc (msgs: list (Time.t * Time.t * Message.t))
        (MAPPABLE: List.Forall
                     (fun m => mappable_time loc (fst (fst m)) /\ mappable_time loc (snd (fst m)))
                     msgs):
    exists ffts, List.Forall2
              (fun m fm =>
                 f loc (fst (fst m)) (fst fm) /\
                 f loc (snd (fst m)) (snd fm))
              msgs ffts.
  Proof.
    induction msgs; eauto.
    destruct a as [[from to] msg].
    inv MAPPABLE. unfold mappable_time in H1. des. ss.
    exploit IHmsgs; eauto. i. des.
    exists ((fto0, fto) :: ffts). econs 2; eauto.
  Qed.

  Lemma mapping_map_lt_non_collapsable
        (MAP_LT: mapping_map_lt):
    forall loc to, non_collapsable loc to.
  Proof.
    ii. unfold collapsed in *. des.
    exploit MAP_LT; try exact TLE; eauto. i. timetac.
  Qed.

  Lemma step_map
        P lang th0 th1 fth0 st0 st1 lc0 lc1 flc0
        sc0 sc1 fsc0 fsc0' mem0 mem1 fmem0 e
        (MAP_LT: mapping_map_lt)
        (MAPPABLE: P <1= mappable_evt)
        (STEP: (@pred_step P lang) e th0 th1)
        (TH_TGT0: th0 = Thread.mk lang st0 lc0 sc0 mem0)
        (TH_TGT1: th1 = Thread.mk lang st1 lc1 sc1 mem1)
        (TH_SRC: fth0 = Thread.mk lang st0 flc0 fsc0 fmem0)
        (LCWF0: Local.wf lc0 mem0)
        (LCWF1: Local.wf flc0 fmem0)
        (CLOSED: Memory.closed fmem0)
        (LOCAL: local_map lc0 flc0)
        (MEM: memory_map mem0 fmem0)
        (UNWRITABLE: collapsable_unwritable (Local.promises lc0) mem0)
        (SC: timemap_map sc0 fsc0')
        (SCLE: TimeMap.le fsc0 fsc0')
    :
      exists flc1 fmem1 fsc1 fsc1' fe,
        (<<EVT: tevent_map fe e>>) /\
        (<<STEP: Thread.step_allpf
                   fe fth0
                   (Thread.mk lang st1 flc1 fsc1 fmem1)>>) /\
        (<<SC: timemap_map sc1 fsc1'>>) /\
        (<<SCLE: TimeMap.le fsc1 fsc1'>>) /\
        (<<MEM: memory_map mem1 fmem1>>) /\
        (<<LOCAL: local_map lc1 flc1>>)
  .
  Proof.
    clarify. inv STEP. eapply MAPPABLE in SAT. inv STEP0.
    exploit step_write_not_in; eauto.
    { inv LCWF0. auto. } intros WRITENOTIN. ss.

    eapply write_not_in_mon in WRITENOTIN; cycle 1.
    { apply UNWRITABLE. }
    eapply step_write_not_in_boundary in WRITENOTIN; eauto.

    inv STEP.
    - inv STEP0. ss. inv LOCAL. inv LOCAL0. inv LCWF1. des.
      exploit mappable_memory_closed_msg_exists; eauto.
      { eapply mappable_memory_op.
        - eapply Memory.promise_op; eauto.
        - eauto.
        - eauto.
        - eapply memory_map_mappable; eauto. }
      i. des. unfold mappable_time in FROM, TO. des.
      exploit promise_map; eauto.
      { ii. unfold collapsed in H. des. des_ifs.
        - destruct kind; ss. exploit UNWRITABLE.
          + exists to', to. unfold collapsed. esplits; eauto.
            instantiate (1:=to). econs; ss. refl.
          + ii. inv x. inv UNCH. inv PROMISE.
            eapply Memory.remove_get0 in MEM0.
            eapply Memory.remove_get0 in PROMISES1. des.
            exploit Memory.get_disjoint.
            { eapply GET2. }
            { eapply GET. } i. des; clarify.
            eapply x0; eauto. econs; ss.
            * eapply Memory.get_ts in GET2. des; clarify.
              exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
              { eapply TLE. }
              { eapply Time.bot_spec. }
            * refl.
        - apply WRITENOTIN.
          exists to', to. esplits; ss; econs; eauto. refl. }
      i. des.
      exists (Local.mk (Local.tview flc0) fprom1). esplits; eauto.
      + econs; eauto.
      + econs; eauto. econs; eauto. econs; eauto. econs; eauto.
        eapply closed_message_map; eauto.
      + ss. econs; eauto.
    - inv LCWF1. inv STEP0. inv LOCAL0; ss.
      + esplits; eauto.
        * econs; eauto.
        * econs; eauto. econs 2; eauto. econs; eauto.
      + exploit read_step_map; eauto. i. des.
        esplits; eauto.
        * econs; eauto.
        * econs; eauto. econs 2; eauto. econs; eauto.
      + unfold mappable_time in SAT. des.
        hexploit write_step_map; try apply LOCAL1; try eassumption.
        { econs. }
        { econs. }
        { econs. }
        { ii. unfold collapsed in H. des. apply WRITENOTIN.
          exists to', to. esplits; ss; econs; eauto. refl. }
        i. des. esplits; eauto.
        * econs; eauto.
        * econs; eauto. econs 2; eauto. econs; eauto.
      + unfold mappable_time in SAT. des.
        hexploit read_step_map; try apply LOCAL1; try eassumption. i. des.
        exploit Local.read_step_future; eauto. i. des.
        hexploit write_step_map; try apply LOCAL2; try eassumption.
        { inv READ. ss. }
        { inv WF2. auto. }
        { inv LOCAL1. auto. }
        { ii. unfold collapsed in H. des. apply WRITENOTIN.
          exists to', tsw. esplits; ss; econs; eauto. refl. }
        i. des. esplits; eauto.
        * econs; eauto.
        * econs; eauto. econs 2; eauto. econs; eauto.
      + hexploit fence_step_map; try apply LOCAL1; try eassumption. i. des.
        esplits; eauto.
        * econs; eauto.
        * econs; eauto. econs 2; eauto. econs; eauto.
      + hexploit fence_step_map; try apply LOCAL1; try eassumption. i. des.
        esplits; eauto.
        * econs; eauto.
        * econs; eauto. econs 2; eauto. econs; eauto.
      + hexploit failure_step_map; try apply LOCAL1; try eassumption. i. des.
        esplits; eauto.
        * econs; eauto.
        * econs; eauto. econs 2; eauto. econs; eauto.
      + unfold mappable_time in SAT. des.
        exploit mappable_messages_exists; eauto. i. des.
        hexploit write_na_step_map; try apply LOCAL1; try eassumption.
        { apply mapping_map_lt_non_collapsable. ss. }
        { clear - MAP_LT. induction msgs; ss. econs; eauto.
          eapply mapping_map_lt_non_collapsable. ss. }
        i. des. esplits; eauto.
        * econs; eauto.
        * econs; eauto. econs 2; eauto. econs; eauto.
      + hexploit racy_read_step_map; try apply LOCAL1; try eassumption. i. des.
        esplits; eauto.
        * econs; eauto.
        * econs; eauto. econs 2; eauto. econs; eauto.
      + hexploit racy_write_step_map; try apply LOCAL1; try eassumption. i. des.
        esplits; eauto.
        * econs; eauto.
        * econs; eauto. econs 2; eauto. econs; eauto.
      + hexploit racy_update_step_map; try apply LOCAL1; try eassumption. i. des.
        esplits; eauto.
        * econs; eauto.
        * econs; eauto. econs 2; eauto. econs; eauto.
  Qed.

  Lemma tevent_map_same_machine_event e fe
        (TEVENT: tevent_map e fe)
    :
      same_machine_event e fe.
  Proof.
    inv TEVENT; ss; eauto.
  Qed.

  Inductive thread_map lang: Thread.t lang -> Thread.t lang -> Prop :=
  | thread_map_intro
      st lc flc mem fmem sc fsc fsc'
      (LOCAL: local_map lc flc)
      (MEM: memory_map mem fmem)
      (UNWRITABLE: collapsable_unwritable (Local.promises lc) mem)
      (SC: timemap_map sc fsc')
      (SCLE: TimeMap.le fsc fsc')
    :
      thread_map
        (Thread.mk _ st lc sc mem)
        (Thread.mk _ st flc fsc fmem)
  .

  Lemma steps_map
        P0 P1 lang th0 th1 fth0 st0 st1 lc0 lc1 flc0
        sc0 sc1 fsc0 fsc0' mem0 mem1 fmem0
        (MAP_LT: mapping_map_lt)
        (MAPPABLE: P0 <1= mappable_evt)
        (STEP: rtc (tau (@pred_step P0 lang)) th0 th1)
        (TH_TGT0: th0 = Thread.mk lang st0 lc0 sc0 mem0)
        (TH_TGT1: th1 = Thread.mk lang st1 lc1 sc1 mem1)
        (TH_SRC: fth0 = Thread.mk lang st0 flc0 fsc0 fmem0)
        (LCWF0: Local.wf lc0 mem0)
        (LCWF1: Local.wf flc0 fmem0)
        (CLOSED0: Memory.closed fmem0)
        (CLOSED1: Memory.closed mem0)
        (CLOSEDSC0: Memory.closed_timemap fsc0 fmem0)
        (CLOSEDSC1: Memory.closed_timemap sc0 mem0)
        (LOCAL: local_map lc0 flc0)
        (MEM: memory_map mem0 fmem0)
        (UNWRITABLE: collapsable_unwritable (Local.promises lc0) mem0)
        (SC: timemap_map sc0 fsc0')
        (SCLE: TimeMap.le fsc0 fsc0')
        (SHIFT: te_pred_shift P1 P0 tevent_map)
    :
      exists flc1 fmem1 fsc1 fsc1',
        (<<STEP: rtc (tau (@pred_step P1 lang))
                     fth0
                     (Thread.mk lang st1 flc1 fsc1 fmem1)>>) /\
        (<<SC: timemap_map sc1 fsc1'>>) /\
        (<<SCLE: TimeMap.le fsc1 fsc1'>>) /\
        (<<MEM: memory_map mem1 fmem1>>) /\
        (<<LOCAL: local_map lc1 flc1>>)
  .
  Proof.
    ginduction STEP; i; ss; clarify.
    - esplits; eauto.
    - inv H. destruct y. exploit step_map; try apply TSTEP; ss; eauto.
      i. des.
      dup TSTEP. inv TSTEP0. inv STEP1.
      exploit Thread.step_future; try apply STEP2; ss. i. des.
      dup STEP0. inv STEP1.
      exploit Thread.step_future; try apply STEP3; ss. i. des.
      exploit IHSTEP; try apply MEM0; eauto.
      { eapply collapsable_unwritable_step in STEP2; eauto. }
      i. des.
      esplits; eauto. econs 2; eauto. econs.
      + econs; eauto.
      + erewrite tevent_map_same_machine_event; eauto.
  Qed.

  Lemma trace_steps_map
        lang (th0 th1 fth0: Thread.t lang) st0 st1 lc0 lc1 flc0
        sc0 sc1 fsc0 fsc0' mem0 mem1 fmem0 tr
        (MAP_LT: mapping_map_lt)
        (PRED: List.Forall (fun em => mappable_evt (snd em)) tr)
        (STEPS: Trace.steps tr th0 th1)
        (TH_TGT0: th0 = Thread.mk lang st0 lc0 sc0 mem0)
        (TH_TGT1: th1 = Thread.mk lang st1 lc1 sc1 mem1)
        (TH_SRC: fth0 = Thread.mk lang st0 flc0 fsc0 fmem0)
        (LCWF0: Local.wf lc0 mem0)
        (LCWF1: Local.wf flc0 fmem0)
        (CLOSED0: Memory.closed fmem0)
        (CLOSED1: Memory.closed mem0)
        (CLOSEDSC0: Memory.closed_timemap fsc0 fmem0)
        (CLOSEDSC1: Memory.closed_timemap sc0 mem0)
        (LOCAL: local_map lc0 flc0)
        (MEM: memory_map mem0 fmem0)
        (UNWRITABLE: collapsable_unwritable (Local.promises lc0) mem0)
        (SC: timemap_map sc0 fsc0')
        (SCLE: TimeMap.le fsc0 fsc0')
    :
      exists ftr flc1 fmem1 fsc1 fsc1',
        (<<STEPS: Trace.steps ftr fth0 (Thread.mk lang st1 flc1 fsc1 fmem1)>>) /\
        (<<SC: timemap_map sc1 fsc1'>>) /\
        (<<SCLE: TimeMap.le fsc1 fsc1'>>) /\
        (<<MEM: memory_map mem1 fmem1>>) /\
        (<<LOCAL: local_map lc1 flc1>>) /\
        (<<TRACE: List.Forall2 (fun the fthe => <<EVENT: tevent_map (snd fthe) (snd the)>> /\ <<LOCAL: local_map (fst the) (fst fthe)>>) tr ftr>>)
  .
  Proof.
    ginduction STEPS; i; ss; clarify.
    - esplits; eauto.
    - ss. destruct th1. inv PRED. exploit step_map; ss.
      { instantiate (1:=mappable_evt). ss. }
      { econs; eauto. econs; eauto. }
      { eauto. }
      { eapply LCWF1. }
      { eauto. }
      { eauto. }
      { eauto. }
      { eauto. }
      i. des.
      exploit Thread.step_future; try apply STEP; ss. i. des.
      inv STEP0. exploit Thread.step_future; try apply STEP1; ss. i. des.
      exploit IHSTEPS; try apply STEPS; eauto.
      { eapply collapsable_unwritable_step in STEP; eauto. }
      i. des. esplits; eauto.
  Qed.

  Lemma thread_trace_steps_map
        lang (th0 th1 fth0: Thread.t lang) st0 st1 lc0 lc1 flc0
        sc0 sc1 fsc0 mem0 mem1 fmem0 tr
        (MAP_LT: mapping_map_lt)
        (PRED: List.Forall (fun em => mappable_evt (snd em)) tr)
        (STEPS: ThreadTrace.steps tr th0 th1)
        (TH_TGT0: th0 = Thread.mk lang st0 lc0 sc0 mem0)
        (TH_TGT1: th1 = Thread.mk lang st1 lc1 sc1 mem1)
        (TH_SRC: fth0 = Thread.mk lang st0 flc0 fsc0 fmem0)
        (LCWF0: Local.wf lc0 mem0)
        (LCWF1: Local.wf flc0 fmem0)
        (CLOSED0: Memory.closed fmem0)
        (CLOSED1: Memory.closed mem0)
        (CLOSEDSC0: Memory.closed_timemap fsc0 fmem0)
        (CLOSEDSC1: Memory.closed_timemap sc0 mem0)
        (MAP: thread_map th0 fth0)
    :
      exists ftr flc1 fmem1 fsc1,
        (<<STEPS: ThreadTrace.steps ftr fth0 (Thread.mk lang st1 flc1 fsc1 fmem1)>>) /\
        (<<MAP: thread_map th1 (Thread.mk lang st1 flc1 fsc1 fmem1)>>) /\
        (<<TRACE: List.Forall2 (fun the fthe => <<EVENT: tevent_map (snd fthe) (snd the)>> /\ <<THREAD: thread_map (fst the) (fst fthe)>>) tr ftr>>)
  .
  Proof.
    ginduction STEPS; i; ss; clarify.
    - esplits; eauto.
    - ss. destruct th1. inv PRED. inv MAP. ss. exploit step_map; ss.
      { instantiate (1:=mappable_evt). ss. }
      { econs; eauto. econs; eauto. }
      { eauto. }
      { eapply LCWF1. }
      { eauto. }
      { eauto. }
      { eauto. }
      { eauto. }
      i. des.
      exploit Thread.step_future; try apply STEP; ss. i. des.
      inv STEP0. exploit Thread.step_future; try apply STEP1; ss. i. des.
      exploit IHSTEPS; try apply STEPS; eauto.
      { econs; eauto.
        eapply collapsable_unwritable_step in STEP; eauto. }
      i. des. esplits; eauto. econs; eauto.
      splits; auto. econs; eauto.
  Qed.


End MAPPED.


Section MAPLT.

  Definition mapping_map_lt_iff (f: Loc.t -> Time.t -> Time.t -> Prop): Prop :=
    forall loc t0 t1 ft0 ft1
           (MAP0: f loc t0 ft0)
           (MAP1: f loc t1 ft1),
      Time.lt t0 t1 <-> Time.lt ft0 ft1.

  Definition mapping_map_lt_iff_loc (f: Time.t -> Time.t -> Prop):=
    forall t0 t1 ft0 ft1
           (MAP0: f t0 ft0)
           (MAP1: f t1 ft1),
      Time.lt t0 t1 <-> Time.lt ft0 ft1.

  Lemma mapping_map_lt_iff_locwise f
        (MAPLT: forall loc, mapping_map_lt_iff_loc (f loc))
    :
      mapping_map_lt_iff f.
  Proof.
    eauto.
  Qed.

  Lemma mapping_map_lt_iff_loc_map_eq f
        (MAPLT: mapping_map_lt_iff_loc f)
        to ft0 ft1
        (MAP0: f to ft0)
        (MAP1: f to ft1)
    :
      ft0 = ft1.
  Proof.
    destruct (Time.le_lt_dec ft0 ft1).
    - inv l; auto.
      erewrite <- (@MAPLT to to) in H; eauto.
       exfalso. eapply Time.lt_strorder; eauto.
    - erewrite <- (@MAPLT to to) in l; eauto.
      exfalso. eapply Time.lt_strorder; eauto.
  Qed.

  Lemma mapping_map_lt_iff_loc_map_le f
        (MAPLT: mapping_map_lt_iff_loc f)
        t0 t1 ft0 ft1
        (MAP0: f t0 ft0)
        (MAP1: f t1 ft1)
        (TS: Time.le t0 t1)
    :
      Time.le ft0 ft1.
  Proof.
    inv TS.
    - left. erewrite (@MAPLT t0 t1) in H; eauto.
    - right. inv H.
      eapply mapping_map_lt_iff_loc_map_eq; eauto.
  Qed.

  Lemma mapping_map_lt_iff_map_eq f
        (MAPLT: mapping_map_lt_iff f)
    :
      mapping_map_eq f.
  Proof.
    ii. eapply mapping_map_lt_iff_loc_map_eq; eauto.
    ii. eauto.
  Qed.

  Lemma mapping_map_lt_iff_map_le f
        (MAPLT: mapping_map_lt_iff f)
    :
      mapping_map_le f.
  Proof.
    ii. eapply mapping_map_lt_iff_loc_map_le; eauto.
    ii. eauto.
  Qed.

  Lemma mapping_map_lt_iff_map_lt f
        (MAPLT: mapping_map_lt_iff f)
    :
      mapping_map_lt f.
  Proof.
    ii. exploit MAPLT; [exact MAP0|exact MAP1|].
    i. rewrite x in *. ss.
  Qed.

  Lemma mapping_map_lt_iff_non_collapsable f
        (MAPLT: mapping_map_lt_iff f)
        loc to
    :
      non_collapsable f loc to.
  Proof.
    ii. unfold collapsed in *. des.
    erewrite (MAPLT loc to' to) in TLE; eauto. eapply Time.lt_strorder; eauto.
  Qed.

  Lemma mapping_map_lt_iff_inj f
        (MAPLT: mapping_map_lt_iff f)
        loc to0 to1 fto
        (MAP0: f loc to0 fto)
        (MAP1: f loc to1 fto)
    :
      to0 = to1.
  Proof.
    destruct (Time.le_lt_dec to0 to1).
    { destruct l; auto.
      erewrite (MAPLT _ _ _ _ _ MAP0 MAP1) in H; eauto. timetac. }
    { erewrite (MAPLT _ _ _ _ _ MAP1 MAP0) in l; eauto. timetac. }
  Qed.

  Lemma mapping_map_lt_iff_collapsable_unwritable f prom mem
        (MAPLT: mapping_map_lt_iff f)
    :
      collapsable_unwritable f prom mem.
  Proof.
    ii. exfalso. des.
    eapply mapping_map_lt_iff_non_collapsable; try eassumption.
    inv ITV. eapply TimeFacts.lt_le_lt; eauto.
  Qed.

End MAPLT.


Section IDENTMAP.

  Definition ident_map (loc: Loc.t) := @eq Time.t.

  Lemma ident_map_lt
    :
      mapping_map_lt ident_map.
  Proof.
    unfold ident_map in *. ii. clarify.
  Qed.

  Lemma ident_map_lt_iff
    :
      mapping_map_lt_iff ident_map.
  Proof.
    unfold ident_map in *. ii. clarify.
  Qed.

  Lemma ident_map_le
    :
      mapping_map_le ident_map.
  Proof.
    apply mapping_map_lt_iff_map_le, ident_map_lt_iff.
  Qed.

  Lemma ident_map_bot
    :
      mapping_map_bot ident_map.
  Proof.
    unfold ident_map in *. ii. clarify.
  Qed.

  Lemma ident_map_eq
    :
      mapping_map_eq ident_map.
  Proof.
    apply mapping_map_lt_iff_map_eq, ident_map_lt_iff.
  Qed.

  Lemma ident_map_total
        loc to
    :
      exists fto,
        <<MAP: ident_map loc to fto >>.
  Proof.
    esplits; eauto. refl.
  Qed.

  Lemma ident_map_timemap
        tm
    :
      timemap_map ident_map tm tm.
  Proof.
    ii. refl.
  Qed.

  Lemma ident_map_view
        vw
    :
      view_map ident_map vw vw.
  Proof.
    econs; eapply ident_map_timemap.
  Qed.

  Lemma ident_map_message
        msg
    :
      msg_map ident_map msg msg.
  Proof.
    destruct msg; econs. destruct released; econs.
    apply ident_map_view.
  Qed.

  Lemma ident_map_promises
        prom
    :
      promises_map ident_map prom prom.
  Proof.
    econs; i.
    - esplits; eauto.
      + eapply mapping_map_lt_iff_non_collapsable.
        eapply ident_map_lt_iff.
      + refl.
      + eapply ident_map_message.
    - esplits; eauto; refl.
  Qed.

  Lemma ident_map_local
        lc
    :
      local_map ident_map lc lc.
  Proof.
    econs; i.
    - refl.
    - econs; i; eapply ident_map_view.
    - eapply ident_map_promises.
  Qed.

  Lemma ident_map_timemap_eq tm0 tm1
        (MAP: timemap_map ident_map tm0 tm1)
    :
      tm0 = tm1.
  Proof.
    extensionality loc. apply MAP.
  Qed.

  Lemma ident_map_view_eq vw0 vw1
        (MAP: view_map ident_map vw0 vw1)
    :
      vw0 = vw1.
  Proof.
    destruct vw0, vw1. f_equal.
    { eapply ident_map_timemap_eq. eapply MAP. }
    { eapply ident_map_timemap_eq. eapply MAP. }
  Qed.

  Lemma ident_map_opt_view_eq vw0 vw1
        (MAP: opt_view_map ident_map vw0 vw1)
    :
      vw0 = vw1.
  Proof.
    inv MAP; eauto. f_equal.
    eapply ident_map_view_eq; eauto.
  Qed.

  Lemma ident_map_message_eq msg0 msg1
        (MAP: msg_map ident_map msg0 msg1)
    :
      msg0 = msg1.
  Proof.
    inv MAP; eauto. f_equal.
    eapply ident_map_opt_view_eq; eauto.
  Qed.

  Lemma ident_map_kind_eq loc kind0 kind1
        (MAP: memory_op_kind_map ident_map loc kind0 kind1)
    :
      kind0 = kind1.
  Proof.
    inv MAP; eauto.
    { f_equal; eauto. eapply ident_map_message_eq; eauto. }
    { f_equal; eauto. eapply ident_map_message_eq; eauto. }
  Qed.

  Lemma ident_map_compose_tevent f te0 te1 te2
        (MAP0: tevent_map f te1 te0)
        (MAP1: tevent_map ident_map te2 te1)
    :
      tevent_map f te2 te0.
  Proof.
    inv MAP0; inv MAP1; econs.
    { inv FROM0. auto. }
    { inv TO0. auto. }
    { eapply ident_map_message_eq in MSG0. subst. auto. }
    { eapply ident_map_kind_eq in KIND0. subst. auto. }
    { inv TO0. eauto. }
    { eauto. }
    { eapply ident_map_opt_view_eq in RELEASED0. subst. etrans; eauto. }
    { inv FROM0. eauto. }
    { inv TO0. eauto. }
    { eauto. }
    { eapply ident_map_opt_view_eq in RELEASED0. subst. etrans; eauto. }
    { clear - MSGS MSGS0. revert fmsgs0 MSGS0.
      induction MSGS; i.
      { inv MSGS0. econs. }
      inv MSGS0. econs; eauto. des. splits.
      - inv H2. ss.
      - inv H0. ss.
      - eapply ident_map_message_eq in H1. rewrite H1 in *. ss.
    }
    { inv FROM0. eauto. }
    { inv TO0. eauto. }
    { inv FROM0. eauto. }
    { inv TO0. eauto. }
    { eauto. }
    { eauto. }
    { eapply ident_map_opt_view_eq in RELEASEDR0. subst. etrans; eauto. }
    { eapply ident_map_opt_view_eq in RELEASEDW0. subst. etrans; eauto. }
    { inv TO0. eauto. }
    { inv TO0. eauto. }
    { inv TO0. eauto. }
  Qed.

  Lemma ident_map_mappable_time loc ts
    :
      mappable_time ident_map loc ts.
  Proof.
    exists ts. ss.
  Qed.

  Lemma ident_map_mappable_evt te
    :
      mappable_evt ident_map te.
  Proof.
    destruct te; ss; splits; try apply ident_map_mappable_time.
    rewrite List.Forall_forall. i.
    split; apply ident_map_mappable_time.
  Qed.

  Lemma ident_map_write_not_in MSGS te fte
        (MAP: tevent_map ident_map fte te)
        (NOTIN: write_not_in MSGS te)
    :
      write_not_in MSGS fte.
  Proof.
    inv MAP; auto.
    { inv FROM. inv TO. inv KIND; ss. }
    { inv FROM. inv TO. ss. }
    { ss. des. split.
      - inv FROM. inv TO. ss.
      - clear from to NOTIN ffrom fto FROM TO.
        revert fmsgs MSGS0. induction NOTIN0; i; inv MSGS0; ss.
        des. econs; eauto.
        destruct x as [[] ?], y as [[] ?]. ss.
        inv H2. inv H0. ss.
    }
    { inv FROM. inv TO. ss. }
  Qed.

  Lemma ident_map_no_read_msgs MSGS te fte
        (MAP: tevent_map ident_map fte te)
        (NOREAD: no_read_msgs MSGS te)
    :
      no_read_msgs MSGS fte.
  Proof.
    inv MAP; auto.
    { inv TO. ss. }
    { inv FROM. ss. }
    { inv TO. ss. }
    { inv TO. ss. }
    { inv TO. ss. }
  Qed.

  Lemma promises_ident_map_covered f prom_src prom_tgt
        (PROMISES: promises_map f prom_src prom_tgt)
        (IDENT: forall loc to fto (MAP: f loc to fto), to = fto)
        loc ts
    :
      covered loc ts prom_src <-> covered loc ts prom_tgt.
  Proof.
    split; i.
    { inv H. dup GET. eapply PROMISES in GET; eauto. des.
      dup GET. eapply PROMISES in GET. des. clarify.
      eapply IDENT in FROM. eapply IDENT in TO0. subst. eapply IDENT in TO. subst.
      clarify. econs; eauto. }
    { inv H. eapply PROMISES in GET. des. eapply IDENT in TO. eapply IDENT in FROM. subst.
      econs; eauto. }
  Qed.

  Lemma memory_ident_map_concrete f mem fmem
        (MEM: memory_map f mem fmem)
        (IDENT: forall loc to fto (MAP: f loc to fto), to = fto)
        loc ts
        (CONCRETE: concrete_promised mem loc ts)
    :
      concrete_promised fmem loc ts.
  Proof.
    inv CONCRETE. eapply MEM in GET. des; ss.
    eapply IDENT in TO. subst.
    inv MSG; inv MSGLE; econs; eauto; ss.
  Qed.

  Lemma timemap_ident_map f tm ftm
        (MAP: timemap_map f tm ftm)
        (IDENT: forall loc to fto (MAP: f loc to fto), to = fto)
    :
      tm = ftm.
  Proof.
    extensionality loc. specialize (MAP loc). eapply IDENT in MAP. auto.
  Qed.

  Lemma view_ident_map f vw fvw
        (MAP: view_map f vw fvw)
        (IDENT: forall loc to fto (MAP: f loc to fto), to = fto)
    :
      vw = fvw.
  Proof.
    destruct vw, fvw. inv MAP. f_equal.
    { eapply timemap_ident_map; eauto. }
    { eapply timemap_ident_map; eauto. }
  Qed.

  Lemma opt_view_ident_map f vw fvw
        (MAP: opt_view_map f vw fvw)
        (IDENT: forall loc to fto (MAP: f loc to fto), to = fto)
    :
      vw = fvw.
  Proof.
    inv MAP; auto. f_equal. eapply view_ident_map; eauto.
  Qed.

  Lemma tview_ident_map f vw fvw
        (MAP: tview_map f vw fvw)
        (IDENT: forall loc to fto (MAP: f loc to fto), to = fto)
    :
      vw = fvw.
  Proof.
    destruct vw, fvw. inv MAP. ss. f_equal.
    { extensionality loc. eapply view_ident_map; eauto. }
    { eapply view_ident_map; eauto. }
    { eapply view_ident_map; eauto. }
  Qed.

End IDENTMAP.


Section MAPIDENT.

  Definition map_ident_in_memory (f: Loc.t -> Time.t -> Time.t -> Prop)
             (mem: Memory.t): Prop :=
    forall loc to
           (TS: Time.le to (Memory.max_ts loc mem)),
      f loc to to.

  Definition map_ident_in_memory_bot
             f mem
             (MAP: map_ident_in_memory f mem)
    :
      mapping_map_bot f.
  Proof.
    ii. eapply MAP. eapply Time.bot_spec.
  Qed.

  Lemma map_ident_in_memory_closed_timemap
        f mem tm
        (MAP: map_ident_in_memory f mem)
        (CLOSED: Memory.closed_timemap tm mem)
    :
      timemap_map f tm tm.
  Proof.
    ii. eapply MAP; eauto.
    exploit CLOSED; eauto. i. des.
    eapply Memory.max_ts_spec in x. des. eauto.
  Qed.

  Lemma map_ident_in_memory_closed_view
        f mem vw
        (MAP: map_ident_in_memory f mem)
        (CLOSED: Memory.closed_view vw mem)
    :
      view_map f vw vw.
  Proof.
    inv CLOSED. econs.
    - eapply map_ident_in_memory_closed_timemap; eauto.
    - eapply map_ident_in_memory_closed_timemap; eauto.
  Qed.

  Lemma map_ident_in_memory_closed_tview
        f mem tvw
        (MAP: map_ident_in_memory f mem)
        (CLOSED: TView.closed tvw mem)
    :
      tview_map f tvw tvw.
  Proof.
    inv CLOSED. econs.
    - i. eapply map_ident_in_memory_closed_view; eauto.
    - eapply map_ident_in_memory_closed_view; eauto.
    - eapply map_ident_in_memory_closed_view; eauto.
  Qed.

  Lemma map_ident_in_memory_closed_opt_view
        f mem vw
        (MAP: map_ident_in_memory f mem)
        (CLOSED: Memory.closed_opt_view vw mem)
    :
      opt_view_map f vw vw.
  Proof.
    inv CLOSED; econs.
    eapply map_ident_in_memory_closed_view; eauto.
  Qed.

  Lemma map_ident_in_memory_closed_message
        f mem msg
        (MAP: map_ident_in_memory f mem)
        (CLOSED: Memory.closed_message msg mem)
    :
      msg_map f msg msg.
  Proof.
    inv CLOSED; econs.
    eapply map_ident_in_memory_closed_opt_view; eauto.
  Qed.

  Lemma map_ident_in_memory_promises
        f mem0 mem
        (MAP: map_ident_in_memory f mem)
        (MAPLT: mapping_map_lt_iff f)
        (CLOSED: Memory.closed mem)
        (MLE: Memory.le mem0 mem)
    :
      promises_map f mem0 mem0.
  Proof.
    inv CLOSED. econs.
    - i. esplits; eauto.
      + eapply mapping_map_lt_iff_non_collapsable; auto.
      + eapply MLE in GET. eapply Memory.max_ts_spec in GET. des.
        eapply MAP; eauto.
      + eapply MLE in GET. eapply CLOSED0 in GET. des.
        eapply map_ident_in_memory_closed_message; eauto.
    - i. esplits; eauto.
      + eapply MLE in GET. eapply Memory.max_ts_spec in GET. des.
        eapply MAP; eauto.
      + eapply MLE in GET. eapply MAP. etrans.
        * eapply memory_get_ts_le; eauto.
        * eapply Memory.max_ts_spec in GET. des. auto.
  Qed.

  Lemma map_ident_in_memory_memory
        f mem
        (MAP: map_ident_in_memory f mem)
        (MAPLT: mapping_map_lt_iff f)
        (CLOSED: Memory.closed mem)
    :
      memory_map f mem mem.
  Proof.
    eapply promises_map_memory_map.
    eapply map_ident_in_memory_promises; eauto. refl.
  Qed.

  Lemma map_ident_in_memory_local
        f mem lc
        (MAP: map_ident_in_memory f mem)
        (MAPLT: mapping_map_lt_iff f)
        (LOCAL: Local.wf lc mem)
        (CLOSED: Memory.closed mem)
    :
      local_map f lc lc.
  Proof.
    inv LOCAL. econs.
    - refl.
    - eapply map_ident_in_memory_closed_tview; eauto.
    - eapply map_ident_in_memory_promises; eauto.
  Qed.

  Lemma map_ident_in_memory_timemap_ident
        f mem
        (MAP: map_ident_in_memory f mem)
        (MAPLT: mapping_map_lt_iff f)
        tm ftm
        (TM: timemap_map f tm ftm)
        (CLOSED: Memory.closed_timemap ftm mem)
    :
      ftm = tm.
  Proof.
    extensionality loc. specialize (TM loc).
    specialize (CLOSED loc). des.
    eapply mapping_map_lt_iff_inj; eauto.
    eapply MAP. eapply Memory.max_ts_spec in CLOSED. des. auto.
  Qed.

  Lemma map_ident_in_memory_view_ident
        f mem
        (MAP: map_ident_in_memory f mem)
        (MAPLT: mapping_map_lt_iff f)
        vw fvw
        (VIEW: view_map f vw fvw)
        (CLOSED: Memory.closed_view fvw mem)
    :
      fvw = vw.
  Proof.
    destruct vw, fvw. f_equal.
    { eapply map_ident_in_memory_timemap_ident; eauto.
      { eapply VIEW. }
      { eapply CLOSED. }
    }
    { eapply map_ident_in_memory_timemap_ident; eauto.
      { eapply VIEW. }
      { eapply CLOSED. }
    }
  Qed.

  Lemma map_ident_in_memory_opt_view_ident
        f mem
        (MAP: map_ident_in_memory f mem)
        (MAPLT: mapping_map_lt_iff f)
        vw fvw
        (VIEW: opt_view_map f vw fvw)
        (CLOSED: Memory.closed_opt_view fvw mem)
    :
      fvw = vw.
  Proof.
    inv VIEW; ss. f_equal. inv CLOSED.
    eapply map_ident_in_memory_view_ident; eauto.
  Qed.

  Lemma map_ident_in_memory_message_ident
        f mem
        (MAP: map_ident_in_memory f mem)
        (MAPLT: mapping_map_lt_iff f)
        msg fmsg
        (MSG: msg_map f msg fmsg)
        (CLOSED: Memory.closed_message fmsg mem)
    :
      fmsg = msg.
  Proof.
    inv MSG; ss. f_equal. inv CLOSED.
    eapply map_ident_in_memory_opt_view_ident; eauto.
  Qed.

End MAPIDENT.


Section SHIFTMAP.

  Record mapping_map_lt_iff_pair_loc (f: Time.t -> (Time.t * Time.t) -> Prop)
         (max: option Time.t): Prop:=
    {
      mapping_map_lt_iff_pair_loc_lt:
        forall t0 t1 ft0 ft1
               (MAP0: f t0 ft0)
               (MAP1: f t1 ft1)
               (TS: Time.lt t0 t1),
          Time.lt (snd ft0) (fst ft1);
      mapping_map_lt_iff_pair_loc_wf:
        forall t ft
               (MAP: f t ft),
          Time.le (fst ft) (snd ft);
      mapping_map_lt_iff_pair_loc_inj:
        forall t ft0 ft1
               (MAP0: f t ft0)
               (MAP0: f t ft1),
          ft0 = ft1;
      (* mapping_map_lt_iff_pair_loc_bot: f Time.bot (Time.bot, Time.bot); *)
      mapping_map_lt_iff_pair_loc_max: forall ts fts max' (MAP: f ts fts) (MAX: max = Some max'),
          Time.lt (snd fts) max';
      mapping_map_lt_iff_pair_loc_closed:
        forall ts (NMAP: forall fts (MAP: f ts fts), False),
          (exists ts_left fts_left,
              (<<LEFT: Time.lt ts_left ts>>) /\
              (<<MAP: f ts_left fts_left>>) /\
              (<<INF: forall ts' fts' (TS: Time.lt ts' ts) (MAP: f ts' fts'),
                  Time.le ts' ts_left>>)) /\
          ((<<MAX: forall ts' fts' (MAP: f ts' fts'),
               Time.lt ts' ts>>)
           \/ exists ts_right fts_right,
              (<<RIGHT: Time.lt ts ts_right>>) /\
              (<<MAP: f ts_right fts_right>>) /\
              (<<SUP: forall ts' fts' (TS: Time.lt ts ts') (MAP: f ts' fts'),
                  Time.le ts_right ts'>>));
    }.

  Lemma bound_mapping_map_lt_iff_pair_loc bound max
        (TS: forall max' (MAX: max = Some max'), Time.lt bound max')
    :
      mapping_map_lt_iff_pair_loc
        (fun ts fts => fts = (ts, ts) /\ <<TS: Time.le ts bound>>)
        max
  .
  Proof.
    econs.
    - ii. des; subst. ss.
    - ii. des; subst. ss. refl.
    - ii. des; subst. ss.
    (* - split; auto. apply Time.bot_spec. *)
    - ii. des; subst. ss. eapply TimeFacts.le_lt_lt; eauto.
    - ii. destruct (Time.le_lt_dec ts bound).
      { exfalso. eapply NMAP. eauto. }
      split.
      + exists bound, (bound, bound). splits; auto.
        * refl.
        * i. des; subst. auto.
      + left. ii. des; subst. eapply TimeFacts.le_lt_lt; eauto.
  Qed.

  Lemma bound_mapping_map_lt_iff_loc max
    :
      mapping_map_lt_iff_loc
        (fun ts fts => fts = ts /\ <<TS: Time.le ts max>>)
  .
  Proof.
    ii. des; subst. auto.
  Qed.

  Lemma ident_map_mapping_map_lt_iff_pair_loc
    :
      mapping_map_lt_iff_pair_loc (fun ts fts => fts = (ts, ts)) None.
  Proof.
    econs.
    - ii. des; subst. ss.
    - ii. des; subst. ss. refl.
    - ii. des; subst. ss.
    (* - split; auto. *)
    - ii. clarify.
    - i. exfalso. eauto.
  Qed.

  Definition mapping_single_in_pair
             (fpair: Time.t -> Time.t * Time.t -> Prop)
             (f: Time.t -> Time.t -> Prop): Prop :=
    (<<IN: forall ts fts
                      (MAPSINGLE: f ts fts),
        exists ftspair,
          (<<MAPPAIR: fpair ts ftspair>>) /\
          (<<LEFT: Time.le (fst ftspair) fts>>) /\
          (<<RIGHT: Time.le fts (snd ftspair)>>)>>) /\
    (<<INJ: forall ts fts0 fts1
                   (MAP0: f ts fts0)
                   (MAP1: f ts fts1),
        fts0 = fts1>>).

  Lemma mapping_map_lt_iff_pair_single
        (fpair: Time.t -> Time.t * Time.t -> Prop)
        (f: Time.t -> Time.t -> Prop)
        max
        (PAIR: mapping_map_lt_iff_pair_loc fpair max)
        (SINGLE: mapping_single_in_pair fpair f)
    :
      mapping_map_lt_iff_loc f.
  Proof.
    unfold mapping_single_in_pair in *. des. ii.
    exploit IN; try apply MAP0; eauto. i. des.
    exploit IN; try apply MAP1; eauto. i. des.
    destruct (Time.le_lt_dec t0 t1); cycle 1.
    { split; i; auto.
      { exfalso. eapply Time.lt_strorder. etrans; eauto. }
      { exfalso. eapply Time.lt_strorder. etrans.
        { eapply H. }
        eapply TimeFacts.le_lt_lt.
        { eauto. } eapply TimeFacts.lt_le_lt.
        { eapply (mapping_map_lt_iff_pair_loc_lt PAIR); try apply l; eauto. }
        { eauto. }
      }
    }
    destruct l.
    { split; i; auto. eapply TimeFacts.le_lt_lt.
      { eauto. } eapply TimeFacts.lt_le_lt.
      { eapply (mapping_map_lt_iff_pair_loc_lt PAIR); eauto. }
      { eauto. }
    }
    { inv H. split; i.
      - exfalso. eapply Time.lt_strorder; eauto.
      - hexploit (INJ t1 ft0 ft1); eauto. i. subst.
        exfalso. eapply Time.lt_strorder; eauto. }
  Qed.

  Lemma mapping_map_lt_iff_pair_single_complete
        (fpair: Time.t -> Time.t * Time.t -> Prop)
        (f: Time.t -> Time.t -> Prop)
        max
        (PAIR: mapping_map_lt_iff_pair_loc fpair max)
        (SINGLE: mapping_single_in_pair fpair f)
    :
      exists f',
        (<<INCR: f <2= f'>>) /\
        (<<SINGLE: mapping_single_in_pair fpair f'>>) /\
        (<<COMPLETE: forall ts ftspair
                            (MAPPAIR: fpair ts ftspair),
            exists fts, <<MAPSINGLE: f' ts fts>> >>).
  Proof.
    hexploit (choice (fun ts p =>
                        (exists fts,
                            (<<MAP: f ts fts>>) /\
                            (<<EQ: p = f ts>>)) \/
                        (exists fts ftspair,
                            (<<NONE: forall fts', ~ f ts fts'>>) /\
                            (<<MAPPAIR: fpair ts ftspair>>) /\
                            (<<LEFT: Time.le (fst ftspair) fts>>) /\
                            (<<RIGHT: Time.le fts (snd ftspair)>>) /\
                            (<<EQ: p = eq fts>>)) \/
                        ((<<NONE: forall fts, ~ f ts fts>>) /\
                         (<<NONEPAIR: forall ftspair, ~ fpair ts ftspair>>) /\
                         (<<EQ: p = fun _ => False>>)))).
    { intros ts. destruct (classic (exists fts, <<MAP: f ts fts>>)).
      { des. esplits. left. eauto. }
      destruct (classic (exists ftspair, <<MAPPAIR: fpair ts ftspair>>)).
      { des. esplits. right. left. esplits; eauto.
        - refl.
        - eapply (mapping_map_lt_iff_pair_loc_wf PAIR); eauto. }
      { esplits. right. right. esplits; eauto. ss. }
    }
    intros [f' FSPEC]. exists f'. splits.
    { i. specialize (FSPEC x0). des.
      { rewrite EQ. eauto. }
      { exfalso. eapply NONE; eauto. }
      { exfalso. eapply NONE; eauto. }
    }
    { split.
      - ii. specialize (FSPEC ts). des.
        { rewrite EQ in *. eapply SINGLE; eauto. }
        { rewrite EQ in *. subst. esplits; eauto. }
        { rewrite EQ in *. clarify. }
      - ii. specialize (FSPEC ts). des.
        { rewrite EQ in *. eapply SINGLE; eauto. }
        { rewrite EQ in *. subst. auto. }
        { rewrite EQ in *. clarify. }
    }
    { ii. specialize (FSPEC ts). des.
      { rewrite EQ in *. eauto. }
      { rewrite EQ in *. eauto. }
      { exfalso. eapply NONEPAIR. eauto. }
    }
  Qed.

  Lemma mapping_map_lt_iff_pair_loc_update_one f max ts fts
        (MAPLT: mapping_map_lt_iff_pair_loc f max)
        (LEFT: forall ts' fts' (TS: Time.lt ts' ts) (MAP: f ts' fts'),
            Time.lt (snd fts') (fst fts))
        (RIGHT: forall ts' fts' (TS: Time.lt ts ts') (MAP: f ts' fts'),
            Time.lt (snd fts) (fst fts'))
        (WF: Time.le (fst fts) (snd fts))
        (MAX: forall max' (MAX: max = Some max'), Time.lt (snd fts) max')
    :
      mapping_map_lt_iff_pair_loc
        (fun t ft => (<<REMOV: t <> ts>> /\ <<ORIG: f t ft>>) \/ (<<NEW: t = ts /\ ft = fts>>))
        max
  .
  Proof.
    assert (INCR: forall t ft (MAP: f t ft),
               exists ft',
                 (fun t ft => (<<REMOV: t <> ts>> /\ <<ORIG: f t ft>>) \/ (<<NEW: t = ts /\ ft = fts>>)) t ft').
    { i. destruct (Time.eq_dec t ts); eauto. }
    econs.
    - ii. des; subst.
      + eapply (mapping_map_lt_iff_pair_loc_lt MAPLT); eauto.
      + eapply RIGHT; eauto.
      + eapply LEFT; eauto.
      + exfalso. eapply Time.lt_strorder; eauto.
    - i. des; subst.
      + eapply (mapping_map_lt_iff_pair_loc_wf MAPLT); eauto.
      + auto.
    - i. des; subst.
      + eapply (mapping_map_lt_iff_pair_loc_inj MAPLT); eauto.
      + exfalso. eauto.
      + exfalso. eauto.
      + auto.
    (* - left. eapply (mapping_map_lt_iff_pair_loc_bot MAPLT); eauto. *)
    - ii. des; subst.
      + eapply (mapping_map_lt_iff_pair_loc_max MAPLT); eauto.
      + eapply MAX; eauto.
    - i. assert (NEQ: ts <> ts0).
      { ii. subst. eapply NMAP. eauto. }
      hexploit ((mapping_map_lt_iff_pair_loc_closed MAPLT) ts0).
      { i. eapply NMAP. eauto. } i.

      destruct H. guardH H0. des. split.
      { hexploit (INCR ts_left); eauto. intros [fts_left' LEFTMAP]. guardH LEFTMAP.
        destruct (Time.le_lt_dec ts ts_left).
        { exists ts_left, fts_left'. splits; auto.
          i. des; eauto. subst. auto. }
        destruct (Time.le_lt_dec ts0 ts).
        { exists ts_left, fts_left'. splits; auto.
          i. des; eauto. subst.
          exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt; eauto. }
        exists ts, fts. splits; auto.
        i. des; subst; [..|refl]. etrans.
        - eapply INF; eauto.
        - left. eapply l. }
      unguard. des.

      { destruct (Time.le_lt_dec ts0 ts); cycle 1.
        { left. ii. des; subst; eauto. }
        destruct l; cycle 1.
        { inv H. exfalso. eauto. }
        right. exists ts, fts.
        splits; auto. i. des; subst; [..|refl].
        exfalso. eapply Time.lt_strorder. etrans; eauto. }
      { hexploit (INCR ts_right); eauto. intros [fts_right' RIGHTMAP]. guardH RIGHTMAP.
        right. destruct (Time.le_lt_dec ts_right ts).
        { exists ts_right, fts_right'. splits; auto.
          i. des; eauto. subst. auto. }
        destruct (Time.le_lt_dec ts ts0).
        { exists ts_right, fts_right'. splits; auto.
          i. des; eauto. subst. exfalso.
          eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt; eauto. }
        { exists ts, fts. splits; auto.
          i. des; subst; [..|refl]. etrans.
          - left. eapply l.
          - eapply SUP; eauto. }
      }
  Qed.

  Lemma mapping_map_lt_pair_loc_extend_one f max ts
        (MAPLT: mapping_map_lt_iff_pair_loc f max)
    :
      exists f',
        (<<MAPLT: mapping_map_lt_iff_pair_loc f' max>>) /\
        (<<INCR: f <2= f'>>) /\
        (<<MAPPED: exists fts, f' ts fts>>).
  Proof.
    destruct (classic (exists fts, f ts fts)) as [MAPPED|NMAPPED].
    { des. exists f. splits; eauto. }
    exploit mapping_map_lt_iff_pair_loc_closed; eauto. i. des.
    { set (fts := match max with
                  | Some max' => Time.middle (snd fts_left) max'
                  | None => Time.incr (snd fts_left)
                  end).
      esplits.
      - eapply mapping_map_lt_iff_pair_loc_update_one.
        + eauto.
        + instantiate (1:=(fts, fts)). i. exploit INF; eauto. i. ss.
          eapply (@TimeFacts.le_lt_lt _ (snd fts_left)).
          { destruct x.
            - transitivity (fst fts_left).
              + left. eapply (mapping_map_lt_iff_pair_loc_lt MAPLT); eauto.
              + eapply (mapping_map_lt_iff_pair_loc_wf MAPLT); eauto.
            - inv H. hexploit ((mapping_map_lt_iff_pair_loc_inj MAPLT) _ _ _ MAP MAP0); eauto.
              i. subst. refl. }
          { unfold fts. des_ifs.
            - eapply Time.middle_spec. eapply (mapping_map_lt_iff_pair_loc_max MAPLT); eauto.
            - eapply Time.incr_spec. }
        + i. exploit MAX; eauto. i.
          exfalso. eapply Time.lt_strorder. etrans; eauto.
        + refl.
        + i. subst. unfold fts. eapply Time.middle_spec.
          eapply (mapping_map_lt_iff_pair_loc_max MAPLT); eauto.
      - i. ss. destruct (Time.eq_dec x0 ts).
        { subst. exfalso. eauto. }
        { eauto. }
      - ss. eauto.
    }
    { assert (LEFTRIGHT: Time.lt (snd fts_left) (fst fts_right)).
      { eapply (mapping_map_lt_iff_pair_loc_lt MAPLT); eauto. }
      esplits.
      - eapply mapping_map_lt_iff_pair_loc_update_one.
        + eauto.
        + instantiate (1:=(Time.middle (snd fts_left) (fst fts_right), Time.middle (snd fts_left) (fst fts_right))).
          i. exploit INF; eauto. i. ss.
          eapply (@TimeFacts.le_lt_lt _ (snd fts_left)).
          { destruct x.
            - transitivity (fst fts_left).
              + left. eapply (mapping_map_lt_iff_pair_loc_lt MAPLT); eauto.
              + eapply (mapping_map_lt_iff_pair_loc_wf MAPLT); eauto.
            - inv H. hexploit ((mapping_map_lt_iff_pair_loc_inj MAPLT) _ _ _ MAP MAP1); eauto.
              i. subst. refl. }
          { eapply Time.middle_spec. auto. }
        + i. exploit SUP; eauto. i. ss.
          eapply (@TimeFacts.lt_le_lt _ (fst fts_right)).
          { eapply Time.middle_spec. auto. }
          { destruct x.
            - transitivity (snd fts_right).
              + eapply (mapping_map_lt_iff_pair_loc_wf MAPLT); eauto.
              + left. eapply (mapping_map_lt_iff_pair_loc_lt MAPLT); eauto.
            - inv H. hexploit ((mapping_map_lt_iff_pair_loc_inj MAPLT) _ _ _ MAP0 MAP1); eauto.
              i. subst. refl. }
        + refl.
        + i. ss. etrans.
          { eapply TimeFacts.lt_le_lt.
            - eapply Time.middle_spec. auto.
            - eapply (mapping_map_lt_iff_pair_loc_wf MAPLT); eauto.
          }
          { eapply (mapping_map_lt_iff_pair_loc_max MAPLT); eauto.
          }
      - i. ss. destruct (Time.eq_dec x0 ts).
        { subst. exfalso. eauto. }
        { eauto. }
      - ss. right. eauto.
    }
  Qed.

  Lemma mapping_map_lt_pair_loc_extend f max (times: list Time.t)
        (MAPLT: mapping_map_lt_iff_pair_loc f max)
    :
      exists f',
        (<<MAPLT: mapping_map_lt_iff_pair_loc f' max>>) /\
        (<<INCR: f <2= f'>>) /\
        (<<MAPPED: forall ts (IN: List.In ts times),
            exists fts, f' ts fts>>).
  Proof.
    ginduction times.
    - i. exists f. splits; ss.
    - i. exploit IHtimes; eauto. i. des.
      hexploit (@mapping_map_lt_pair_loc_extend_one f' max a); auto.
      i. des. exists f'0. splits; ss; eauto.
      i. des; subst; eauto.
      exploit MAPPED; eauto. i. des. eauto.
  Qed.

  Lemma shift_map_pair_exists max ts0 ts1 (T: list Time.t)
        (MAX: Time.le max ts0)
        (TS: Time.lt ts0 ts1)
    :
      exists (f: Time.t -> (Time.t * Time.t) -> Prop),
        (<<COMPLETE: forall to (IN: List.In to T), exists fto, (<<MAPPED: f to fto>>)>>) /\
        (<<SAME: forall ts (TS: Time.lt ts max), f ts (ts, ts)>>) /\
        (<<GAP: f max (max, ts0)>>) /\
        (<<BOUND: forall to fto (MAPPED: f to fto) (TS: Time.lt max to),
            (Time.lt ts0 (fst fto) /\ Time.lt (snd fto) ts1)>>) /\
        (<<MAPLT: mapping_map_lt_iff_pair_loc f (Some ts1)>>)
  .
  Proof.
    hexploit (@bound_mapping_map_lt_iff_pair_loc max (Some ts1)).
    { i. clarify. eapply TimeFacts.le_lt_lt; eauto. }
    intros MAPLT0.
    hexploit mapping_map_lt_iff_pair_loc_update_one.
    { eapply MAPLT0. }
    { instantiate (1:=(max, ts0)).
      instantiate (1:=max).
      i. ss. des; subst. ss. }
    { i. ss. des; subst. exfalso.
      eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt; eauto. }
    { ss. }
    { ss. i. clarify. }
    intros MAPLT1.
    hexploit mapping_map_lt_pair_loc_extend.
    { eapply MAPLT1. }
    i. des. exists f'. splits.
    - eapply MAPPED.
    - i. eapply INCR. left. split.
      { ii. subst. eapply Time.lt_strorder; eauto. }
      { split; ss. left. auto. }
    - eapply INCR. eauto.
    - i. eapply MAPLT in TS0; cycle 1; eauto. ss. split; auto.
      eapply (mapping_map_lt_iff_pair_loc_max MAPLT); eauto.
    - auto.
  Qed.

  Lemma shift_map_exists max ts0 ts1 (T: list Time.t)
        (MAX: Time.le max ts0)
        (TS: Time.lt ts0 ts1)
    :
      exists (f: Time.t -> Time.t -> Prop),
        (<<COMPLETE: forall to (IN: List.In to T), exists fto, (<<MAPPED: f to fto>>)>>) /\
        (<<SAME: forall ts (TS: Time.le ts max), f ts ts>>) /\
        (<<BOUND: forall to fto (MAPPED: f to fto) (TS: Time.lt max to),
            (Time.lt ts0 fto /\ Time.lt fto ts1)>>) /\
        (<<MAPLT: mapping_map_lt_iff_loc f>>)
  .
  Proof.
    hexploit shift_map_pair_exists; eauto. i. des.
    hexploit mapping_map_lt_iff_pair_single_complete.
    { eauto. }
    { instantiate (1:=(fun ts fts => fts = ts /\ <<TS: Time.le ts max >>)).
      econs.
      - ii. des; subst. destruct TS0.
        { esplits; eauto; try refl. }
        { inv H. esplits; eauto. refl. }
      - ii. des; subst. auto. }
    i. des. exists f'. splits; auto.
    - i. exploit COMPLETE; eauto. i. des.
      exploit COMPLETE0; eauto.
    - i. unfold mapping_single_in_pair in *. des.
      exploit IN; eauto. i. des.
      exploit BOUND; eauto. i. des. splits.
      { eapply TimeFacts.lt_le_lt; eauto. }
      { eapply TimeFacts.le_lt_lt; eauto. }
    - eapply mapping_map_lt_iff_pair_single; eauto.
  Qed.

End SHIFTMAP.

Section CONCRETEIDENT.

  Definition map_ident_concrete (f: Loc.t -> Time.t -> Time.t -> Prop)
             (mem: Memory.t): Prop :=
    forall loc to
           (CONCRETE: concrete_promised mem loc to),
      f loc to to.

  Definition map_ident_concrete_bot
             f mem
             (MAP: map_ident_concrete f mem)
             (CLOSED: Memory.closed mem)
    :
      mapping_map_bot f.
  Proof.
    ii. eapply MAP. inv CLOSED. econs; eauto. ss.
  Qed.

  Lemma map_ident_concrete_closed_timemap
        f mem tm
        (MAP: map_ident_concrete f mem)
        (CLOSED: Memory.closed_timemap tm mem)
    :
      timemap_map f tm tm.
  Proof.
    ii. eapply MAP; eauto.
    exploit CLOSED; eauto. i. des. econs; eauto. ss.
  Qed.

  Lemma map_ident_concrete_closed_view
        f mem vw
        (MAP: map_ident_concrete f mem)
        (CLOSED: Memory.closed_view vw mem)
    :
      view_map f vw vw.
  Proof.
    inv CLOSED. econs.
    - eapply map_ident_concrete_closed_timemap; eauto.
    - eapply map_ident_concrete_closed_timemap; eauto.
  Qed.

  Lemma map_ident_concrete_closed_tview
        f mem tvw
        (MAP: map_ident_concrete f mem)
        (CLOSED: TView.closed tvw mem)
    :
      tview_map f tvw tvw.
  Proof.
    inv CLOSED. econs.
    - i. eapply map_ident_concrete_closed_view; eauto.
    - eapply map_ident_concrete_closed_view; eauto.
    - eapply map_ident_concrete_closed_view; eauto.
  Qed.

  Lemma map_ident_concrete_closed_opt_view
        f mem vw
        (MAP: map_ident_concrete f mem)
        (CLOSED: Memory.closed_opt_view vw mem)
    :
      opt_view_map f vw vw.
  Proof.
    inv CLOSED; econs.
    eapply map_ident_concrete_closed_view; eauto.
  Qed.

  Lemma map_ident_concrete_closed_message
        f mem msg
        (MAP: map_ident_concrete f mem)
        (CLOSED: Memory.closed_message msg mem)
    :
      msg_map f msg msg.
  Proof.
    inv CLOSED; econs.
    eapply map_ident_concrete_closed_opt_view; eauto.
  Qed.

  Lemma promise_writing_event_map loc to mem from msg f e fe
        (CLOSED: Memory.closed mem)
        (GET: Memory.get loc to mem = Some (from, msg))
        (NRESERVE: msg <> Message.reserve)
        (MAPLT: mapping_map_lt_iff f)
        (IDENT: forall loc' to' from' msg' ts
                       (GET: Memory.get loc' to' mem = Some (from', msg'))
                       (RESERVE: msg' <> Message.reserve)
                       (TS: Time.le ts to')
          ,
            f loc' ts ts)
        (WRITING: promise_writing_event loc from to msg e)
        (EVENT: tevent_map f fe e)
    :
      promise_writing_event loc from to msg fe.
  Proof.
    assert (CONCRETE: map_ident_concrete f mem).
    { ii. inv CONCRETE. eapply IDENT; eauto. refl. }
    inv WRITING; inv EVENT.
    { assert (to = fto).
      { eapply mapping_map_lt_iff_map_eq; eauto. eapply IDENT; eauto; ss. refl. }
      subst.
      assert (from' = ffrom).
      { eapply mapping_map_lt_iff_map_eq; eauto. }
      subst.
      econs; eauto. inv MSG. econs; eauto.
      exploit opt_view_le_map.
      { eapply mapping_map_lt_iff_map_le; eauto. }
      { eapply RELEASED. }
      { eapply CLOSED in GET. des. inv MSG_CLOSED.
        eapply map_ident_concrete_closed_opt_view; eauto. }
      { eauto. }
      i. etrans; eauto.
    }
    { assert (to = fto).
      { eapply mapping_map_lt_iff_map_eq; eauto. eapply IDENT; eauto; ss. refl. }
      subst.
      assert (from' = ffrom).
      { eapply mapping_map_lt_iff_map_eq; eauto. }
      subst.
      econs; eauto. inv MSG. econs; eauto.
      exploit opt_view_le_map.
      { eapply mapping_map_lt_iff_map_le; eauto. }
      { eapply RELEASEDW. }
      { eapply CLOSED in GET. des. inv MSG_CLOSED.
        eapply map_ident_concrete_closed_opt_view; eauto. }
      { eauto. }
      i. transitivity freleasedw'; auto.
    }
    { assert (to = fto).
      { eapply mapping_map_lt_iff_map_eq; eauto. eapply IDENT; eauto; ss. refl. }
      subst.
      assert (from' = ffrom).
      { eapply mapping_map_lt_iff_map_eq; eauto. }
      subst.
      econs; eauto.
    }
    { eapply list_Forall2_in2 in IN; eauto. des.
      ss. destruct b as [[from0 to0] msg0]. ss.
      assert (to = to0).
      { eapply mapping_map_lt_iff_map_eq; eauto. eapply IDENT; eauto; ss. refl. }
      subst.
      assert (from' = from0).
      { eapply mapping_map_lt_iff_map_eq; eauto. }
      subst.
      econs; eauto.
    }
  Qed.

End CONCRETEIDENT.

Section COMPOSE.

  Inductive compose_map (f0 f1: Loc.t -> Time.t -> Time.t -> Prop)
    : Loc.t -> Time.t -> Time.t -> Prop :=
  | compose_map_intro
      loc ts0 ts1 ts2
      (MAP0: f0 loc ts0 ts1)
      (MAP1: f1 loc ts1 ts2)
    :
      compose_map f0 f1 loc ts0 ts2
  .
  Hint Constructors compose_map.

  Lemma compose_map_eq f0 f1
        (MAPEQ0: mapping_map_eq f0)
        (MAPEQ1: mapping_map_eq f1)
    :
      mapping_map_eq (compose_map f0 f1).
  Proof.
    unfold mapping_map_eq in *. i. inv MAP0. inv MAP1.
    hexploit (@MAPEQ0 _ _ _ _ MAP2 MAP0); eauto. i. clarify.
    eauto.
  Qed.

  Lemma compose_map_le f0 f1
        (MAPLE0: mapping_map_le f0)
        (MAPLE1: mapping_map_le f1)
    :
      mapping_map_le (compose_map f0 f1).
  Proof.
    unfold mapping_map_le in *. i. inv MAP0. inv MAP1.
    hexploit (@MAPLE0 _ _ _ _ _ MAP2 MAP0); eauto.
  Qed.

  Lemma compose_map_bot f0 f1
        (MAPBOT0: mapping_map_bot f0)
        (MAPBOT1: mapping_map_bot f1)
    :
      mapping_map_bot (compose_map f0 f1).
  Proof.
    ii. econs; eauto.
  Qed.

  Lemma compose_map_lt_iff f0 f1
        (MAPLT0: mapping_map_lt_iff f0)
        (MAPLT1: mapping_map_lt_iff f1)
    :
      mapping_map_lt_iff (compose_map f0 f1).
  Proof.
    unfold mapping_map_lt_iff in *. i. inv MAP0. inv MAP1.
    transitivity (Time.lt ts1 ts2); eauto.
  Qed.

  Lemma compose_map_timemap f0 f1 tm0 tm1 tm2
        (MAP0: timemap_map f0 tm0 tm1)
        (MAP1: timemap_map f1 tm1 tm2)
    :
      timemap_map (compose_map f0 f1) tm0 tm2.
  Proof.
    ii. eauto.
  Qed.

  Lemma compose_map_view f0 f1 vw0 vw1 vw2
        (MAP0: view_map f0 vw0 vw1)
        (MAP1: view_map f1 vw1 vw2)
    :
      view_map (compose_map f0 f1) vw0 vw2.
  Proof.
    inv MAP0. inv MAP1. econs.
    - eapply compose_map_timemap; eauto.
    - eapply compose_map_timemap; eauto.
  Qed.

  Lemma compose_map_opt_view f0 f1 vw0 vw1 vw2
        (MAP0: opt_view_map f0 vw0 vw1)
        (MAP1: opt_view_map f1 vw1 vw2)
    :
      opt_view_map (compose_map f0 f1) vw0 vw2.
  Proof.
    inv MAP0; inv MAP1; econs.
    eapply compose_map_view; eauto.
  Qed.

  Lemma compose_map_tview f0 f1 tvw0 tvw1 tvw2
        (MAP0: tview_map f0 tvw0 tvw1)
        (MAP1: tview_map f1 tvw1 tvw2)
    :
      tview_map (compose_map f0 f1) tvw0 tvw2.
  Proof.
    inv MAP0. inv MAP1. econs.
    - i. eapply compose_map_view; eauto.
    - eapply compose_map_view; eauto.
    - eapply compose_map_view; eauto.
  Qed.

  Lemma compose_map_msg f0 f1 msg0 msg1 msg2
        (MAP0: msg_map f0 msg0 msg1)
        (MAP1: msg_map f1 msg1 msg2)
    :
      msg_map (compose_map f0 f1) msg0 msg2.
  Proof.
    inv MAP0; inv MAP1; econs.
    eapply compose_map_opt_view; eauto.
  Qed.

  Lemma compose_map_op_kind f0 f1 loc kind0 kind1 kind2
        (MAP0: memory_op_kind_map f0 loc kind0 kind1)
        (MAP1: memory_op_kind_map f1 loc kind1 kind2)
    :
      memory_op_kind_map (compose_map f0 f1) loc kind0 kind2.
  Proof.
    inv MAP0; inv MAP1; econs.
    { eapply compose_map_msg; eauto. }
    { econs; eauto. }
    { eapply compose_map_msg; eauto. }
  Qed.

  Lemma compose_map_mappable f0 f1 mem0 mem1
        (MAP: memory_map f0 mem0 mem1)
        (MAPPABLE: mappable_memory f1 mem1)
    :
      mappable_memory (compose_map f0 f1) mem0.
  Proof.
    ii. inv MAP. exploit MAPPED; eauto. i. des; clarify.
    inv MSG. inv MSGLE. exploit MAPPABLE; eauto. i. inv x.
    eexists. eauto.
  Qed.

  Lemma compose_map_memory2 f0 f1 m0 m1 m2
        (MAPEQ0: mapping_map_eq f0)
        (MAPLE: mapping_map_le f1)
        (MEM0: memory_map2 f0 m0 m1)
        (CLOSED0: Memory.closed m0)
        (MEM1: memory_map2 f1 m1 m2)
    :
      memory_map2 (compose_map f0 f1) m0 m2.
  Proof.
    dup MEM0. dup MEM1.
    inv MEM0. inv MEM1. econs.
    - ii. exploit MAPPED; eauto. i. des; auto.
      exploit MAPPED0; eauto. i. des; auto.
      + subst. inv MSGLE. inv MSG. auto.
      + right. inv CLOSED0. exploit CLOSED; eauto. i. des.
        exploit closed_message_map; try apply MSG; eauto.
        { eapply memory_map2_memory_map; eauto. } intros MSG_CLOSED1.
        exploit msg_map_exists; try apply MSG_CLSOED1; eauto.
        { eapply memory_map2_memory_map; eauto. } i. des.
        esplits; [..|eauto].
        * eauto.
        * eapply compose_map_msg; eauto.
        * etrans; eauto. eapply msg_le_map; eauto.
    - i. exploit ONLY0; eauto. i. des.
      exploit ONLY; eauto. i. des. esplits; eauto.
  Qed.

  Lemma compose_map_promise f0 f1 m0 m1 m2
        (MAPLT0: mapping_map_lt_iff f0)
        (MAPLT1: mapping_map_lt_iff f1)
        (MEM0: promises_map f0 m0 m1)
        (CLOSED0: Memory.closed m0)
        (MEM1: promises_map f1 m1 m2)
    :
      promises_map (compose_map f0 f1) m0 m2.
  Proof.
    dup MEM0. dup MEM1.
    inv MEM0. inv MEM1. econs.
    - ii. exploit MAPPED; eauto. i. des; auto.
      exploit MAPPED0; eauto. i. des; auto. esplits; eauto.
      + eapply mapping_map_lt_iff_non_collapsable.
        eapply compose_map_lt_iff; eauto.
      + eapply compose_map_msg; eauto.
    - ii. exploit ONLY0; eauto. i. des.
      exploit ONLY; eauto. i. des. esplits; eauto.
  Qed.

  Lemma tevent_map_weak_compose (f0 f1 f2: Loc.t -> Time.t -> Time.t -> Prop) e0 e1 e2
        (EVENT0: tevent_map_weak f0 e1 e0)
        (EVENT1: tevent_map_weak f1 e2 e1)
        (COMPOSE: forall loc ts0 ts1 ts2 (MAP0: f0 loc ts0 ts1) (MAP1: f1 loc ts1 ts2),
            f2 loc ts0 ts2)
    :
      tevent_map_weak f2 e2 e0.
  Proof.
    inv EVENT0; inv EVENT1; econs; eauto.
    - etrans; eauto.
    - clear - COMPOSE MSGS MSGS0. revert fmsgs0 MSGS0.
      induction MSGS; i.
      { inv MSGS0. econs. }
      inv MSGS0. exploit IHMSGS; eauto. i. econs; eauto.
      des. splits; eauto.
      destruct x, y, y0; ss.
      inv H5; inv H1; econs.
  Qed.

  Lemma tevent_map_weak_rev (f0 f1: Loc.t -> Time.t -> Time.t -> Prop) e0 e1
        (EVENT: tevent_map_weak f0 e1 e0)
        (REV: forall loc ts0 ts1 (MAP: f0 loc ts0 ts1), f1 loc ts1 ts0)
    :
      tevent_map_weak f1 e0 e1.
  Proof.
    inv EVENT; econs; eauto.
    - symmetry. auto.
    - induction MSGS; eauto. econs; eauto. des.
      splits; eauto.
      destruct x, y; ss. inv H1; econs.
  Qed.


End COMPOSE.

Section INCR.

  Variable f0 f1: Loc.t -> Time.t -> Time.t -> Prop.
  Hypothesis INCR: f0 <3= f1.
  Hypothesis MAPLT: mapping_map_lt_iff f1.

  Lemma mappalbe_time_incr loc to
        (TIME: mappable_time f0 loc to)
    :
      mappable_time f1 loc to.
  Proof.
    unfold mappable_time in *. des. eapply INCR in MAPPED. eauto.
  Qed.

  Lemma timamap_map_incr tm ftm
        (MAP: timemap_map f0 tm ftm)
    :
      timemap_map f1 tm ftm.
  Proof.
    ii. eauto.
  Qed.

  Lemma view_map_incr vw fvw
        (MAP: view_map f0 vw fvw)
    :
      view_map f1 vw fvw.
  Proof.
    inv MAP. econs.
    { eapply timamap_map_incr; eauto. }
    { eapply timamap_map_incr; eauto. }
  Qed.

  Lemma opt_view_map_incr vw fvw
        (MAP: opt_view_map f0 vw fvw)
    :
      opt_view_map f1 vw fvw.
  Proof.
    inv MAP; econs.
    eapply view_map_incr; eauto.
  Qed.

  Lemma tview_map_incr vw fvw
        (MAP: tview_map f0 vw fvw)
    :
      tview_map f1 vw fvw.
  Proof.
    inv MAP; econs.
    { i. eapply view_map_incr; eauto. }
    { eapply view_map_incr; eauto. }
    { eapply view_map_incr; eauto. }
  Qed.

  Lemma message_map_incr msg fmsg
        (MAP: msg_map f0 msg fmsg)
    :
      msg_map f1 msg fmsg.
  Proof.
    inv MAP; econs. eapply opt_view_map_incr; eauto.
  Qed.

  Lemma promises_map_incr prom fprom
        (MAP: promises_map f0 prom fprom)
    :
      promises_map f1 prom fprom.
  Proof.
    inv MAP. econs.
    { i. exploit MAPPED; eauto. i. des. esplits; eauto.
      { eapply mapping_map_lt_iff_non_collapsable; eauto. }
      { eapply message_map_incr; eauto. }
    }
    { i. exploit ONLY; eauto. i. des. esplits; eauto. }
  Qed.

  Lemma local_map_incr lc flc
        (MAP: local_map f0 lc flc)
    :
      local_map f1 lc flc.
  Proof.
    inv MAP. econs; eauto.
    { eapply tview_map_incr; eauto. }
    { eapply promises_map_incr; eauto. }
  Qed.

End INCR.

Lemma cap_steps_current_steps lang
      th0 th1 mem1 tr
      (LOCAL: Local.wf (Thread.local th0) (Thread.memory th0))
      (MEMORY: Memory.closed (Thread.memory th0))
      (SC: Memory.closed_timemap (Thread.sc th0) (Thread.memory th0))
      (CAP: Memory.cap (Thread.memory th0) mem1)
      (STEPS: Trace.steps
                tr
                (Thread.mk lang (Thread.state th0) (Thread.local th0) (Thread.sc th0) mem1)
                th1)
      (CONSISTENT: Local.promise_consistent (Thread.local th1))
  :
    exists lc' sc' mem' ftr,
      (<<STEPS: Trace.steps
                  ftr
                  th0
                  (Thread.mk lang (Thread.state th1) lc' sc' mem')>>) /\
      (<<CONSISTENT: Local.promise_consistent lc'>>) /\
      (<<TRACE: List.Forall2 (fun the fthe => <<EVENT: tevent_map ident_map (snd fthe) (snd the)>> /\ <<LOCAL: local_map ident_map (fst the) (fst fthe)>>) tr ftr>>)
.
Proof.
  destruct th0, th1. ss.
  hexploit trace_steps_map.
  { eapply ident_map_le. }
  { eapply ident_map_bot. }
  { eapply ident_map_eq. }
  { eapply ident_map_lt. }
  { eapply List.Forall_forall. i. eapply ident_map_mappable_evt. }
  { eapply STEPS. }
  { ss. }
  { ss. }
  { ss. }
  { eapply Local.cap_wf; eauto. }
  { eapply LOCAL. }
  { eauto. }
  { eapply Memory.cap_closed; eauto. }
  { eauto. }
  { eapply Memory.cap_closed_timemap; eauto. }
  { eapply map_ident_in_memory_local; eauto; ss.
    eapply ident_map_lt_iff.
  }
  { econs.
    { i. destruct (classic (msg = Message.reserve)); auto. right.
      exists to, from, msg.
      eapply Memory.cap_inv in GET; eauto. des; ss. esplits; eauto.
      { refl. }
      { eapply ident_map_message. }
      { refl. }
    }
    { i. eapply CAP in GET. left. exists fto, ffrom, fto, ffrom. splits; ss.
      { refl. }
      { refl. }
      { i. econs; eauto. }
    }
  }
  { eapply mapping_map_lt_iff_collapsable_unwritable. eapply ident_map_lt_iff. }
  { eapply ident_map_timemap. }
  { refl. }
  i. des. esplits; eauto.
  { inv LOCAL0. eapply promise_consistent_mon; cycle 1; eauto.
    { refl. }
    eapply promise_consistent_map; eauto.
    { eapply ident_map_le; eauto. }
    { eapply ident_map_eq; eauto. }
  }
Qed.

Lemma cap_tau_steps_current_steps lang
      th0 th1 mem1
      (LOCAL: Local.wf (Thread.local th0) (Thread.memory th0))
      (MEMORY: Memory.closed (Thread.memory th0))
      (SC: Memory.closed_timemap (Thread.sc th0) (Thread.memory th0))
      (CAP: Memory.cap (Thread.memory th0) mem1)
      (STEPS: rtc (@Thread.tau_step lang)
                  (Thread.mk lang (Thread.state th0) (Thread.local th0) (Thread.sc th0) mem1)
                  th1)
      (CONSISTENT: Local.promise_consistent (Thread.local th1))
  :
    exists lc' sc' mem',
      (<<STEPS: rtc (@Thread.tau_step lang)
                    th0
                    (Thread.mk lang (Thread.state th1) lc' sc' mem')>>) /\
      (<<CONSISTENT: Local.promise_consistent lc'>>)
.
Proof.
  eapply Trace.tau_steps_silent_steps in STEPS. des.
  exploit cap_steps_current_steps; eauto. i. des. esplits; eauto.
  eapply Trace.silent_steps_tau_steps; eauto.
  eapply List.Forall_forall. i.
  eapply list_Forall2_in in H; eauto. des.
  eapply List.Forall_forall in IN; eauto. ss.
  erewrite tevent_map_same_machine_event; eauto.
Qed.

Lemma cap_failure_current_steps lang
      th0 mem1
      (LOCAL: Local.wf (Thread.local th0) (Thread.memory th0))
      (MEMORY: Memory.closed (Thread.memory th0))
      (SC: Memory.closed_timemap (Thread.sc th0) (Thread.memory th0))
      (CAP: Memory.cap (Thread.memory th0) mem1)
      (STEPS: Thread.steps_failure (Thread.mk lang (Thread.state th0) (Thread.local th0) (Thread.sc th0) mem1))
  :
    Thread.steps_failure th0.
Proof.
  red in STEPS. des.
  eapply Trace.tau_steps_silent_steps in STEPS0. des.
  exploit cap_steps_current_steps.
  { eauto. }
  { eauto. }
  { eauto. }
  { eauto. }
  { eapply Trace.steps_app.
    { eauto. }
    { eapply Trace.steps_one. eauto. }
  }
  { inv STEP_FAILURE; inv STEP; ss. inv LOCAL0; ss; try by (inv LOCAL1; ss). }
  i. des.
  eapply List.Forall2_app_inv_l in TRACE. des; subst.
  inv TRACE0. inv H3. des.
  eapply Trace.steps_separate in STEPS0. des.
  inv STEPS2. inv TR. inv STEPS0; ss.
  assert (FAILURE: ThreadEvent.get_machine_event e0 = MachineEvent.failure).
  { erewrite tevent_map_same_machine_event; eauto. }
  assert (pf = true).
  { inv STEP; ss. inv STEP0; ss. }
  subst. red. esplits.
  { eapply Trace.silent_steps_tau_steps; eauto.
    eapply List.Forall_forall. i.
    eapply list_Forall2_in in H; eauto. des.
    eapply List.Forall_forall in IN; eauto. ss.
    erewrite tevent_map_same_machine_event; eauto.
  }
  { eauto. }
  { eauto. }
Qed.
