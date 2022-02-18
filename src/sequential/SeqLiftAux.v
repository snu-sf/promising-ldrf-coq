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

Require Import Cover.
Require Import MemorySplit.
Require Import MemoryMerge.
Require Import FulfillStep.
Require Import MemoryProps.

Require Import gSimAux.
Require Import LowerMemory.
Require Import JoinedView.

Require Import MaxView.
Require Import Delayed.

Require Import Lia.

Require Import JoinedView.
Require Import SeqLift.
Require Import gSimulation.
Require Import Simple.

Require Import Pred.

Require Import SeqLiftStep.



Lemma mapped_msgs_exists_aux f0 f1 vers msgs_tgt prom_tgt loc flag_new
      mem_src
      (PROM: exists srctm flag_src flag_tgt prom_src, sim_promises srctm flag_src flag_tgt f0 vers prom_src prom_tgt)
      (MAPLE: Mapping.le (f0 loc) f1)
      (MSGS: forall from to msg (IN: List.In (from, to, msg) msgs_tgt), Memory.get loc to prom_tgt = Some (from, msg))
      (WF0: Mapping.wfs f0)
      (WF1: Mapping.wf f1)
      (VERSWF: versions_wf f0 vers)
      (BOTNONE: Memory.bot_none prom_tgt)
      (MSGSWF: wf_cell_msgs msgs_tgt)
      (SIM: sim_closed_memory f0 mem_src)

      ts_tgt ts_src
      (SIMTIME: sim_timestamp_exact f1 f1.(Mapping.ver) ts_src ts_tgt)
      (MAX: Time.le (Memory.max_ts loc mem_src) ts_src)
      (RESERVE: forall from_tgt to_tgt msg_tgt from_src to_src
                       (GET: Memory.get loc to_tgt prom_tgt = Some (from_tgt, msg_tgt))
                       (TS: Time.lt from_tgt ts_tgt)
                       (TO: sim_timestamp_exact (f0 loc) (f0 loc).(Mapping.ver) to_src to_tgt)
                       (FROM: sim_timestamp_exact (f0 loc) (f0 loc).(Mapping.ver) from_src from_tgt),
          (<<RESERVE: msg_tgt = Message.reserve>>) /\
          (<<TS: Time.lt to_tgt ts_tgt>>) /\
          (<<DISJOINT: forall from to msg (GET: Memory.get loc to mem_src = Some (from, msg)),
              Interval.disjoint (from_src, to_src) (from, to)>>))
      (SAME: forall to_tgt to_src
                    (TS: Time.lt to_tgt ts_tgt)
                    (MAP: sim_timestamp_exact (f0 loc) (f0 loc).(Mapping.ver) to_src to_tgt),
          sim_timestamp_exact f1 f1.(Mapping.ver) to_src to_tgt)
  :
    exists msgs_src,
      (<<FORALL: List.Forall2
                   (fun '(from_src, to_src, msg_src) '(from_tgt, to_tgt, msg_tgt) =>
                      (<<FROM: sim_timestamp_exact f1 f1.(Mapping.ver) from_src from_tgt>>) /\
                      (<<TO: sim_timestamp_exact f1 f1.(Mapping.ver) to_src to_tgt>>) /\
                      (<<MESSAGE: sim_message_max flag_new loc to_src f0 (vers loc to_tgt) msg_src msg_tgt>>))
                   msgs_src msgs_tgt>>) /\
      (<<DISJOINT: List.Forall
                     (fun '(from, to, msg) => (__guard__((<<MAX: Time.le (Memory.max_ts loc mem_src) from>>) \/ (<<RESERVE: msg = Message.reserve>>) /\ (<<DISJOINT: forall to2 from2 msg2 (GET: Memory.get loc to2 mem_src = Some (from2, msg2)), Interval.disjoint (from, to) (from2, to2)>>))) /\ (<<TS: Time.lt from to>>) /\ (<<MSGTO: Memory.message_to msg loc to>>) /\ (<<WF: Message.wf msg>>) /\ (<<CLOSED: semi_closed_message msg mem_src loc to>>)) msgs_src>>) /\
      (<<MSGSWF: wf_cell_msgs msgs_src>>)
.
Proof.
  pose proof mapping_latest_wf_loc as VERWF.
  revert MSGS MSGSWF. induction msgs_tgt; i.
  { exists []. splits.
    { econs. }
    { econs. }
    { red. splits; econs. }
  }
  des. destruct a as [[from_tgt to_tgt] msg_tgt].
  hexploit MSGS.
  { left. eauto. }
  intros GETTGT. hexploit sim_promises_get; eauto. i. des.
  hexploit sim_timestamp_exact_mon_exists; [eapply FROM|..]; eauto. i. des.
  hexploit sim_timestamp_exact_mon_exists; [eapply TO|..]; eauto. i. des.
  hexploit (@sim_message_max_exists flag_new loc ts_src0 f0 (vers loc to_tgt) msg_tgt); eauto.
  { i. hexploit VERS; eauto. i. des. esplits; eauto.
    exploit VERSWF. rewrite VER. ss.
  }
  i. des. red in MSGSWF. des. inv DISJOINT. inv MSGSWF0.
  hexploit IHmsgs_tgt; eauto.
  { i. eapply MSGS. right. auto. }
  { red. splits; auto. }
  i. destruct H1 as [MSGWF TIMEWF]. guardH TIMEWF.
  des.
  assert (FROMTO: Time.lt ts_src1 ts_src0).
  { eapply sim_timestamp_exact_lt; eauto.
    hexploit memory_get_ts_strong; eauto. i. des; clarify.
    rewrite BOTNONE in GETTGT. ss.
  }
  exists ((ts_src1, ts_src0, msg_src)::msgs_src). splits.
  { econs; eauto. }
  { econs; eauto. splits.
    { destruct (Time.le_lt_dec ts_tgt from_tgt).
      { left. transitivity ts_src; auto. eapply sim_timestamp_exact_le; eauto. }
      { right. hexploit RESERVE; eauto. i. des. subst.
        hexploit (@SAME to_tgt to_src); eauto. i.
        eapply sim_timestamp_exact_inject in SIM1; eauto. subst.
        hexploit (@SAME from_tgt from_src); eauto. i.
        eapply sim_timestamp_exact_inject in SIM0; eauto. subst.
        splits.
        { inv MAX0; ss. }
        { i. eauto. }
      }
    }
    { auto. }
    { eapply sim_message_max_msg_to; eauto. }
    { eapply sim_message_max_msg_wf; eauto. }
    { eapply sim_closed_memory_sim_message; eauto. }
  }
  { red in MSGSWF. des. red. splits.
    { econs; eauto.
      eapply List.Forall_forall. intros [[from_src0 to_src0] msg_src0] IN.
      eapply list_Forall2_in2 in IN; eauto. des.
      destruct b as [[from_tgt0 to_tgt0] msg_tgt0]. des.
      eapply List.Forall_forall in HD; eauto. ss.
      eapply sim_timestamp_exact_le; eauto.
    }
    { econs; eauto. splits; auto.
      eapply sim_message_max_msg_wf; eauto.
    }
  }
Qed.

Lemma messages_times_exists (msgs: list (Time.t * Time.t * Message.t)) (f0: Mapping.t) ts
      (MAPWF: Mapping.wf f0)
  :
    exists (f1: Mapping.t),
      (<<MAPWF: Mapping.wf f1>>) /\
      (<<MAPLE: Mapping.le_strong f0 f1>>) /\
      (<<CLOSEDIF: forall to (CLOSED: Mapping.closed f1 f1.(Mapping.ver) to),
          (<<CLOSED: Mapping.closed f0 f0.(Mapping.ver) to>>) \/
          (exists from val released, (<<IN: List.In (from, to, Message.concrete val released) msgs>>)) \/
          (<<TS: to = ts>>)>>) /\
      (<<CLOSED: List.Forall (fun '(from_src, to_src, msg_src) =>
                                forall val released (MSG: msg_src = Message.concrete val released),
                                  Mapping.closed f1 f1.(Mapping.ver) to_src) msgs>>) /\
      (<<CLOSEDTS: Mapping.closed f1 f1.(Mapping.ver) ts>>)
.
Proof.
  hexploit (@mapping_update_times f0 (fun to => to = ts \/ exists from val released, List.In (from, to, Message.concrete val released) msgs)).
  { eauto. }
  { induction msgs.
    { exists [ts]. i. des; ss; auto. }
    { des. destruct a as [[from to] msg]. destruct msg.
      { exists (to::l). i. ss. des; clarify.
        { right. eapply IHmsgs. left. auto. }
        { auto. }
        { right. eapply IHmsgs. right. eauto. }
      }
      { exists l. i. eapply IHmsgs. ss. des; clarify; eauto. }
      { exists l. i. eapply IHmsgs. ss. des; clarify; eauto. }
    }
  }
  i. des. exists f1. splits; eauto.
  { i. eapply TIMES in CLOSED. des; auto.
    right. esplits; eauto.
  }
  { eapply List.Forall_forall. intros [[from to] msg] IN. i. subst.
    eapply TIMES. right. esplits; eauto.
  }
  { eapply TIMES. right. left. auto. }
Qed.

Lemma mapped_msgs_complete f0 f1 msgs_src msgs_tgt loc vers flag_new
      (WF1: Mapping.wf f1)
      (FORALL: List.Forall2
                 (fun '(from_src, to_src, msg_src) '(from_tgt, to_tgt, msg_tgt) =>
                    (<<FROM: sim_timestamp_exact f1 f1.(Mapping.ver) from_src from_tgt>>) /\
                    (<<TO: sim_timestamp_exact f1 f1.(Mapping.ver) to_src to_tgt>>) /\
                    (<<MESSAGE: sim_message_max flag_new loc to_src f0 (vers loc to_tgt) msg_src msg_tgt>>))
                 msgs_src msgs_tgt)
      (CLOSED: List.Forall (fun '(from_src, to_src, msg_src) =>
                              forall val released (MSG: msg_src = Message.concrete val released),
                                Mapping.closed f1 f1.(Mapping.ver) to_src) msgs_src)
  :
    forall to_tgt from_tgt msg_tgt
           (RESERVE: msg_tgt <> Message.reserve)
           (GETTGT: List.In (from_tgt, to_tgt, msg_tgt) msgs_tgt),
    exists to_src from_src msg_src,
      (<<TO: sim_timestamp_exact f1 f1.(Mapping.ver) to_src to_tgt>>) /\
      (<<MSG: sim_message false loc f0 (vers loc to_tgt) msg_src msg_tgt>>) /\
      (<<CLOSED: forall val released (MSG: msg_tgt = Message.concrete val released), Mapping.closed f1 f1.(Mapping.ver) to_src>>) /\
      (<<IN: List.In (from_src, to_src, msg_src) msgs_src>>).
Proof.
  i. eapply list_Forall2_in in GETTGT; eauto. des.
  destruct a as [[from_src to_src] msg_src]. des. esplits; eauto.
  { eapply sim_message_flag_mon. eapply sim_message_max_sim; eauto. }
  { i. subst. eapply List.Forall_forall in CLOSED; eauto. ss.
    inv MESSAGE; eauto.
  }
Qed.

Lemma mapped_msgs_sound f0 f1 msgs_src msgs_tgt loc vers flag_new
      (WF1: Mapping.wf f1)
      (FORALL: List.Forall2
                 (fun '(from_src, to_src, msg_src) '(from_tgt, to_tgt, msg_tgt) =>
                    (<<FROM: sim_timestamp_exact f1 f1.(Mapping.ver) from_src from_tgt>>) /\
                    (<<TO: sim_timestamp_exact f1 f1.(Mapping.ver) to_src to_tgt>>) /\
                    (<<MESSAGE: sim_message_max flag_new loc to_src f0 (vers loc to_tgt) msg_src msg_tgt>>))
                 msgs_src msgs_tgt)
  :
    forall to_src from_src msg_src
           (IN: List.In (from_src, to_src, msg_src) msgs_src),
    exists to_tgt from_tgt msg_tgt,
      (<<TO: sim_timestamp_exact f1 f1.(Mapping.ver) to_src to_tgt>>) /\
      (<<FROM: sim_timestamp_exact f1 f1.(Mapping.ver) from_src from_tgt>>) /\
      (<<GET: List.In (from_tgt, to_tgt, msg_tgt) msgs_tgt>>).
Proof.
  i. eapply list_Forall2_in2 in IN; eauto. des.
  destruct b as [[from_tgt to_tgt] msg_tgt]. des. esplits; eauto.
Qed.

Lemma mapped_msgs_complete_promise f0 f1 msgs_src msgs_tgt loc vers flag_new
      (WF1: Mapping.wf f1)
      (FORALL: List.Forall2
                 (fun '(from_src, to_src, msg_src) '(from_tgt, to_tgt, msg_tgt) =>
                    (<<FROM: sim_timestamp_exact f1 f1.(Mapping.ver) from_src from_tgt>>) /\
                    (<<TO: sim_timestamp_exact f1 f1.(Mapping.ver) to_src to_tgt>>) /\
                    (<<MESSAGE: sim_message_max flag_new loc to_src f0 (vers loc to_tgt) msg_src msg_tgt>>))
                 msgs_src msgs_tgt)
      (CLOSED: List.Forall (fun '(from_src, to_src, msg_src) =>
                              forall val released (MSG: msg_src = Message.concrete val released),
                                Mapping.closed f1 f1.(Mapping.ver) to_src) msgs_src)
  :
    forall to_tgt from_tgt msg_tgt
           (GETTGT: List.In (from_tgt, to_tgt, msg_tgt) msgs_tgt),
    exists to_src from_src msg_src,
      (<<TO: sim_timestamp_exact f1 f1.(Mapping.ver) to_src to_tgt>>) /\
      (<<MSG: sim_message_max flag_new loc to_src f0 (vers loc to_tgt) msg_src msg_tgt>>) /\
      (<<CLOSED: forall val released (MSG: msg_tgt = Message.concrete val released), Mapping.closed f1 f1.(Mapping.ver) to_src>>) /\
      (<<IN: List.In (from_src, to_src, msg_src) msgs_src>>).
Proof.
  i. eapply list_Forall2_in in GETTGT; eauto. des.
  destruct a as [[from_src to_src] msg_src]. des. esplits; eauto.
  eapply List.Forall_forall in CLOSED; eauto. ss.
  inv MESSAGE; eauto.
Qed.

Lemma mapped_msgs_sound_promise f0 f1 msgs_src msgs_tgt loc vers flag_new
      (WF1: Mapping.wf f1)
      (FORALL: List.Forall2
                 (fun '(from_src, to_src, msg_src) '(from_tgt, to_tgt, msg_tgt) =>
                    (<<FROM: sim_timestamp_exact f1 f1.(Mapping.ver) from_src from_tgt>>) /\
                    (<<TO: sim_timestamp_exact f1 f1.(Mapping.ver) to_src to_tgt>>) /\
                    (<<MESSAGE: sim_message_max flag_new loc to_src f0 (vers loc to_tgt) msg_src msg_tgt>>))
                 msgs_src msgs_tgt)
      (CLOSED: List.Forall (fun '(from_src, to_src, msg_src) =>
                              forall val released (MSG: msg_src = Message.concrete val released),
                                Mapping.closed f1 f1.(Mapping.ver) to_src) msgs_src)
  :
    forall to_src from_src msg_src
           (IN: List.In (from_src, to_src, msg_src) msgs_src),
    exists to_tgt from_tgt msg_tgt,
      (<<TO: sim_timestamp_exact f1 f1.(Mapping.ver) to_src to_tgt>>) /\
      (<<FROM: sim_timestamp_exact f1 f1.(Mapping.ver) from_src from_tgt>>) /\
      (<<GET: List.In (from_tgt, to_tgt, msg_tgt) msgs_tgt>>).
Proof.
  i. eapply list_Forall2_in2 in IN; eauto. des.
  destruct b as [[from_tgt to_tgt] msg_tgt]. des. esplits; eauto.
Qed.

Lemma shited_mapping_space_future_memory srctm flag_src f0 vers mem_src mem_tgt
      loc f1 ts_src ts_tgt from val released
      (SIM: sim_memory srctm flag_src f0 vers mem_src mem_tgt)
      (MAPLE: Mapping.le (f0 loc) f1)
      (MAPWF0: Mapping.wfs f0)
      (MAPWF1: Mapping.wf f1)
      (PRESERVE: forall to_tgt to_src
                        (TS: Time.lt to_tgt ts_tgt)
                        (SIM: sim_timestamp_exact (f0 loc) (f0 loc).(Mapping.ver) to_src to_tgt),
          sim_timestamp_exact f1 f1.(Mapping.ver) to_src to_tgt)
      (SIMTS: sim_timestamp_exact f1 f1.(Mapping.ver) ts_src ts_tgt)
      (MAX: ts_src = Memory.max_ts loc mem_src)
      (GET: Memory.get loc ts_tgt mem_tgt = Some (from, Message.concrete val released))
  :
    space_future_memory
      (Messages.of_memory mem_tgt)
      f0 mem_src
      (fun loc0 => if Loc.eq_dec loc0 loc then f1 else f0 loc0) mem_src.
Proof.
  pose proof mapping_latest_wf_loc as VERWF.
  econs. i. inv MSGS. destruct (Loc.eq_dec loc0 loc); cycle 1.
  { eapply sim_timestamp_exact_inject in FROM0; eauto.
    eapply sim_timestamp_exact_inject in TO0; eauto.
  }
  subst. destruct (Time.le_lt_dec to_tgt ts_tgt).
  { inv l.
    2:{ inv H. clarify. }
    hexploit PRESERVE; [|eapply TO0|..]; eauto.
    i. eapply sim_timestamp_exact_inject in TO1; eauto.
    hexploit PRESERVE; [|eapply FROM0|..]; eauto.
    { eapply TimeFacts.le_lt_lt; eauto. eapply memory_get_ts_le; eauto. }
    i. eapply sim_timestamp_exact_inject in FROM1; eauto.
  }
  { hexploit memory_get_from_mon.
    { eapply GET. }
    { eapply GET0. }
    { eauto. }
    i. exfalso.
    hexploit sim_timestamp_exact_le; [| |eapply H|..]; eauto. i.
    inv COVERED. eapply Memory.max_ts_spec in GET1. des.
    inv ITV0. ss. inv ITV. ss. eapply Time.lt_strorder.
    eapply TimeFacts.le_lt_lt.
    { eapply TO. }
    eapply TimeFacts.le_lt_lt.
    { eapply MAX. }
    eapply TimeFacts.le_lt_lt.
    { eapply H0. }
    { eapply FROM2. }
  }
Qed.

Lemma added_memory_space_future_memory f loc msgs_src prom_tgt mem_src0 mem_src1 mem_tgt
      (MAPWF: Mapping.wfs f)
      (ADDED: added_memory loc msgs_src mem_src0 mem_src1)
      (SOUND: forall to_src from_src msg_src
                     (IN: List.In (from_src, to_src, msg_src) msgs_src),
          exists to_tgt from_tgt msg_tgt,
            (<<TO: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) to_src to_tgt>>) /\
            (<<FROM: sim_timestamp_exact (f loc) (f loc).(Mapping.ver) from_src from_tgt>>) /\
            (<<GET: Memory.get loc to_tgt prom_tgt = Some (from_tgt, msg_tgt)>>))
      (MLE: Memory.le prom_tgt mem_tgt)
  :
    space_future_memory
      (unchangable mem_tgt prom_tgt)
      f mem_src0
      f mem_src1.
Proof.
  pose proof mapping_latest_wf_loc as VERWF.
  inv ADDED. econs. i.
  eapply sim_timestamp_exact_inject in FROM0; eauto.
  eapply sim_timestamp_exact_inject in TO0; eauto. subst. splits; auto.
  inv COVERED. econs; eauto.
  destruct (Loc.eq_dec loc0 loc); subst.
  2:{ rewrite OTHER in GET; eauto. }
  eapply SOUND0 in GET. des; eauto. exfalso.
  eapply SOUND in IN. des. inv MSGS.
  hexploit Memory.get_disjoint.
  { eapply GET0. }
  { eapply MLE. eapply GET. }
  i. des; clarify.
  hexploit sim_disjoint; [..|eapply H|]; eauto.
Qed.

Lemma sim_timemap_shifted (L0 L1: Loc.t -> Prop) f0 f1 tm_src tm_tgt
      loc ts_src ts_tgt
      (SIM: sim_timemap L0 f0 (Mapping.vers f0) tm_src tm_tgt)
      (MAPLE: Mapping.les f0 f1)
      (MAPWF0: Mapping.wfs f0)
      (MAPWF1: Mapping.wfs f1)
      (TS: sim_timestamp_exact (f1 loc) (f1 loc).(Mapping.ver) ts_src ts_tgt)
      (CLOSED: Mapping.closed (f1 loc) (f1 loc).(Mapping.ver) (tm_src loc))
      (TMSRC: Time.le (tm_src loc) ts_src)
      (TMTGT: Time.le ts_tgt (tm_tgt loc))
      (LOCS: forall loc0 (IN: L1 loc0), L0 loc0 \/ loc0 = loc)
  :
    sim_timemap L1 f1 (Mapping.vers f1) tm_src tm_tgt.
Proof.
  pose proof mapping_latest_wf_loc as VERWF.
  ii. eapply LOCS in LOC. des.
  { eapply sim_timestamp_mon_ver.
    { erewrite <- sim_timestamp_mon_mapping.
      { eauto. }
      { eauto. }
      { eauto. }
      { eauto. }
    }
    { eapply MAPLE. }
    { eauto. }
    { eauto. }
  }
  subst. red. esplits; eauto.
Qed.

Lemma sim_thread_flag_src_view
      f vers flag_src flag_tgt vs_src vs_tgt
      mem_src mem_tgt lc_src lc_tgt sc_src sc_tgt
      loc
      (SIM: sim_thread
              f vers flag_src flag_tgt vs_src vs_tgt
              mem_src mem_tgt lc_src lc_tgt sc_src sc_tgt)
      (LOCALSRC: Local.wf lc_src mem_src)
      (FLAG: flag_src loc = true)
  :
    (<<ACQRLX: lc_src.(Local.tview).(TView.acq).(View.rlx) loc = lc_src.(Local.tview).(TView.cur).(View.rlx) loc>>) /\
    (<<ACQPLN: lc_src.(Local.tview).(TView.acq).(View.pln) loc = lc_src.(Local.tview).(TView.cur).(View.rlx) loc>>).
Proof.
  inv SIM. inv LOCAL. ss.
  hexploit FLAGSRC; eauto. i.
  hexploit MAXTIMES; eauto. i.
  rewrite SRCTM in *. des.
  inv LOCALSRC. inv TVIEW_CLOSED. inv CUR. inv ACQ. ss. splits; auto.
  { eapply TimeFacts.antisym.
    { rewrite H0.
      specialize (RLX0 loc). des. eapply Memory.max_ts_spec in RLX0. des. eauto.
    }
    { eapply TVIEW_WF. }
  }
  { eapply TimeFacts.antisym.
    { rewrite H0.
      specialize (PLN0 loc). des. eapply Memory.max_ts_spec in PLN0. des. eauto.
    }
    { rewrite H. eapply TVIEW_WF. }
  }
Qed.

Lemma sim_view_shifted (L0 L1: Loc.t -> Prop) f0 f1 vw_src vw_tgt
      loc ts_src ts_tgt
      (SIM: sim_view L0 f0 (Mapping.vers f0) vw_src vw_tgt)
      (MAPLE: Mapping.les f0 f1)
      (MAPWF0: Mapping.wfs f0)
      (MAPWF1: Mapping.wfs f1)
      (TS: sim_timestamp_exact (f1 loc) (f1 loc).(Mapping.ver) ts_src ts_tgt)
      (CLOSED: Mapping.closed (f1 loc) (f1 loc).(Mapping.ver) (vw_src.(View.rlx) loc))
      (TMSRC: Time.le (vw_src.(View.rlx) loc) ts_src)
      (TMTGT: Time.le ts_tgt (vw_tgt.(View.pln) loc))
      (LOCS: forall loc0 (IN: L1 loc0), L0 loc0 \/ loc0 = loc)
      (VIEWWF: View.wf vw_tgt)
      (SRCMAX: vw_src.(View.rlx) loc = vw_src.(View.pln) loc)
  :
    sim_view L1 f1 (Mapping.vers f1) vw_src vw_tgt.
Proof.
  econs.
  { eapply sim_timemap_shifted; eauto.
    { eapply SIM. }
    { rewrite <- SRCMAX. auto. }
    { rewrite <- SRCMAX. auto. }
  }
  { eapply sim_timemap_shifted; eauto.
    { eapply SIM. }
    { etrans; eauto. eapply VIEWWF. }
  }
Qed.

Lemma sim_tview_shifted flag_src0 flag_src1 f0 f1 rel_vers tvw_src tvw_tgt
      loc ts_src ts_tgt
      (SIM: sim_tview f0 flag_src0 rel_vers tvw_src tvw_tgt)
      (MAPLE: Mapping.les f0 f1)
      (MAPWF0: Mapping.wfs f0)
      (MAPWF1: Mapping.wfs f1)
      (TS: sim_timestamp_exact (f1 loc) (f1 loc).(Mapping.ver) ts_src ts_tgt)
      (CLOSED: Mapping.closed (f1 loc) (f1 loc).(Mapping.ver) (tvw_src.(TView.cur).(View.rlx) loc))
      (TMSRC: Time.le (tvw_src.(TView.cur).(View.rlx) loc) ts_src)
      (TMTGT: Time.le ts_tgt (tvw_tgt.(TView.cur).(View.pln) loc))
      (LOCS: forall loc0 (IN: flag_src1 loc0 = false), flag_src0 loc0 = false \/ loc0 = loc)
      (VIEWWF: TView.wf tvw_tgt)
      (SRCMAX0: tvw_src.(TView.cur).(View.pln) loc = tvw_src.(TView.cur).(View.rlx) loc)
      (SRCMAX1: tvw_src.(TView.acq).(View.rlx) loc = tvw_src.(TView.cur).(View.rlx) loc)
      (SRCMAX2: tvw_src.(TView.acq).(View.pln) loc = tvw_src.(TView.cur).(View.rlx) loc)
  :
    sim_tview f1 flag_src1 rel_vers tvw_src tvw_tgt.
Proof.
  inv SIM. econs.
  { i. erewrite <- sim_view_mon_mapping; eauto. }
  { eapply sim_view_shifted; eauto. eapply VIEWWF. }
  { eapply sim_view_shifted; eauto.
    { rewrite SRCMAX1. auto. }
    { rewrite SRCMAX1. auto. }
    { etrans; eauto. eapply VIEWWF. }
    { eapply VIEWWF. }
    { rewrite SRCMAX1. auto. }
  }
  { i. eapply version_wf_mapping_mon; eauto. }
Qed.

Lemma sim_thread_deflag_match_aux2
      f0 vers flag_src flag_tgt vs_src vs_tgt
      mem_src0 mem_tgt lc_src0 lc_tgt sc_src sc_tgt
      loc
      (SIM: sim_thread
              f0 vers flag_src flag_tgt vs_src vs_tgt
              mem_src0 mem_tgt lc_src0 lc_tgt sc_src sc_tgt)
      (CONSISTENT: Local.promise_consistent lc_tgt)
      (LOCALSRC: Local.wf lc_src0 mem_src0)
      (LOCALTGT: Local.wf lc_tgt mem_tgt)
      (MEMSRC: Memory.closed mem_src0)
      (MEMTGT: Memory.closed mem_tgt)
      (SCSRC: Memory.closed_timemap sc_src mem_src0)
      (SCTGT: Memory.closed_timemap sc_tgt mem_tgt)
      (WF: Mapping.wfs f0)
      (VERSWF: versions_wf f0 vers)
      (FLAG: flag_src loc = true)
      (VAL: option_rel Const.le (vs_tgt loc) (vs_src loc))
      lang st
  :
    exists lc_src1 mem_src1 f1,
      (<<STEPS: rtc (tau (@pred_step is_promise _))
                    (Thread.mk lang st lc_src0 sc_src mem_src0)
                    (Thread.mk _ st lc_src1 sc_src mem_src1)>>) /\
      (<<SIM: sim_thread
                f1 vers
                (fun loc0 => if Loc.eq_dec loc0 loc then false else flag_src loc0)
                (fun loc0 => if Loc.eq_dec loc0 loc then false else flag_tgt loc0)
                vs_src vs_tgt
                mem_src1 mem_tgt lc_src1 lc_tgt sc_src sc_tgt>>) /\
      (<<WF: Mapping.wfs f1>>) /\
      (<<MAPLE: Mapping.les f0 f1>>) /\
      (<<UNCH: forall loc0 (NEQ: loc0 <> loc), f1 loc0 = f0 loc0>>) /\
      (<<MAPFUTURE: map_future_memory f0 f1 mem_src1>>) /\
      (<<SPACE: space_future_memory (unchangable mem_tgt lc_tgt.(Local.promises)) f0 mem_src0 f1 mem_src1>>)
.
Proof.
  hexploit sim_thread_flag_src_view; eauto. i. des.
  inv SIM. hexploit (MAXSRC loc). intros MAXTSSRC.
  hexploit (MAXTGT loc). intros MAXTSTGT.
  destruct (vs_src loc) eqn:VSRC; cycle 1.
  { hexploit max_value_src_flag_none; eauto. i. clarify. }
  inv MAXTSSRC. hexploit MAX; eauto. i. des.
  destruct (vs_tgt loc) eqn:VTGT; ss.
  inv MAXTSTGT. hexploit MAX1; eauto. i. des.
  assert (TS: srctm loc = View.rlx (TView.cur tvw) loc).
  { inv LOCAL. auto. }
  hexploit sim_memory_top; eauto. intros TOP.
  hexploit (@shifted_mapping_exists (f0 loc) (View.pln (TView.cur tvw0) loc) (srctm loc)); eauto. i. des.
  hexploit (@wf_cell_msgs_exists (prom0 loc)). intros [msgs_tgt ?]. des.
  hexploit mapped_msgs_exists_aux.
  { inv LOCAL. eauto. }
  { eauto. }
  { i. eapply COMPLETE. eauto. }
  { eauto. }
  { eauto. }
  { eauto. }
  { eapply LOCALTGT. }
  { eauto. }
  { eauto. }
  { eapply TS0. }
  { inv LOCAL. rewrite MAXTIMES; auto. refl. }
  { i. admit. }
  { eauto. }
  i. des.
  inv MAX0. inv MAX2. ss.
  hexploit sim_memory_sound; eauto. i. des.
  { exfalso. eapply TOP in TO. eapply Time.lt_strorder.
    eapply TimeFacts.lt_le_lt.
    { eapply TO. }
    { inv LOCAL. rewrite SRCTM. rewrite FLAGSRC; auto. }
  }
  hexploit NONE1; eauto. i. subst.
  hexploit (messages_times_exists msgs_src f1); auto. i. des.
  eapply list_Forall2_impl in FORALL; cycle 1.
  { i. instantiate (1:= fun '(from_src, to_src, msg_src) '(from_tgt, to_tgt, msg_tgt) =>
                          (<<FROM: sim_timestamp_exact f2 f2.(Mapping.ver) from_src from_tgt>>) /\
                          (<<TO: sim_timestamp_exact f2 f2.(Mapping.ver) to_src to_tgt>>) /\
                          (<<MESSAGE: sim_message_max false loc to_src f0 (vers loc to_tgt) msg_src msg_tgt>>)).
    destruct a as [[from_src to_src] msg_src]. destruct b as [[from_tgt to_tgt] msg_tgt].
    des. splits; eauto.
    { eapply sim_timestamp_exact_mon_strong; [..|eauto]; eauto.  }
    { eapply sim_timestamp_exact_mon_strong; [..|eauto]; eauto.  }
  }
  pose proof (mapped_msgs_complete _ _ _ _ _ _ _ MAPWF FORALL CLOSED0) as COMPLETEMEM.
  pose proof (mapped_msgs_sound _ _ _ _ _ _ _ MAPWF FORALL) as SOUNDMEM.
  pose proof (mapped_msgs_complete_promise _ _ _ _ _ _ _ MAPWF FORALL) as COMPLETEPROM.
  pose proof (mapped_msgs_sound_promise _ _ _ _ _ _ _ MAPWF FORALL) as SOUNDPROM.
  set (f' := fun loc0 => if Loc.eq_dec loc0 loc then f2 else f0 loc0).
  assert (MAPSLE: Mapping.les f0 f').
  { unfold f'. ii. condtac; subst.
    { etrans; eauto. eapply Mapping.le_strong_le; eauto. }
    { refl. }
  }
  assert (MAPSWF: Mapping.wfs f').
  { unfold f'. ii. condtac; subst; eauto. }
  hexploit add_promises_latest.
  { eapply MSGSWF. }
  { eapply LOCALSRC. }
  { eapply MEMSRC. }
  { eauto. }
  i. des. inv LOCAL.
  hexploit added_memory_sim_memory; eauto.
  { rewrite TS. rewrite FLAGSRC; eauto. }
  {  hexploit sim_memory_get; eauto; ss. i. des.
     inv MSG; econs; eauto; econs.
  }
  { ss. }
  { i. eapply MAX0 in GETTGT; eauto.
    eapply COMPLETE in GETTGT. eapply COMPLETEMEM; eauto.
  }
  { i. eapply SOUNDMEM in IN. des. esplits; eauto.
    eapply LOCALTGT. eapply COMPLETE; eauto.
  }
  { etrans; eauto. eapply Mapping.le_strong_le; eauto. }
  { i. eapply sim_timestamp_exact_mon_strong; [|eauto|..]; eauto. }
  { eapply sim_timestamp_exact_mon_strong; [|eauto|..]; eauto. }
  { i. eapply CLOSEDIF in CLOSED1. des.
    { left. eapply CLOSED. auto. }
    { right. left. eauto. }
    { subst. right. right. esplits; eauto. }
  }
  i. destruct H as [MEM1 ?]. des.
  esplits.
  { eapply STEPS. }
  { econs.
    { instantiate (1:=f'). eapply sim_timemap_mon_latest; eauto. }
    { eapply added_memory_sim_memory; eauto.
      { rewrite TS. rewrite FLAGSRC; eauto. }
      {  hexploit sim_memory_get; eauto; ss. i. des.
         inv MSG; econs; eauto; econs.
      }
      { ss. }
      { i. eapply MAX0 in GETTGT; eauto.
        eapply COMPLETE in GETTGT. eapply COMPLETEMEM; eauto.
      }
      { i. eapply SOUNDMEM in IN. des. esplits; eauto.
        eapply LOCALTGT. eapply COMPLETE; eauto.
      }
      { etrans; eauto. eapply Mapping.le_strong_le; eauto. }
      { i. eapply sim_timestamp_exact_mon_strong; [|eauto|..]; eauto. }
      { eapply sim_timestamp_exact_mon_strong; [|eauto|..]; eauto. }
      { i. eapply CLOSEDIF in CLOSED1. des.
        { left. eapply CLOSED. auto. }
        { right. left. eauto. }
        { subst. right. right. esplits; eauto. }
      }
    }
    { econs.
      { eapply sim_tview_shifted; eauto.
        { eapply sim_timestamp_exact_mon_strong; [..|eapply TS0]; eauto.
          unfold f'. des_ifs.
        }
        { unfold f'. des_ifs. rewrite <- SRCTM. auto. }
        { rewrite <- SRCTM. refl. }
        { refl. }
        { i. des_ifs; auto. }
        { eapply LOCALTGT. }
        { rewrite FLAGSRC; auto. }
      }
      { eapply added_memory_sim_promise_match; eauto.
        { i. eapply COMPLETE in GETTGT. eapply COMPLETEPROM in GETTGT; eauto. }
        { i. eapply SOUNDPROM in IN; eauto. des.
          esplits; eauto. eapply COMPLETE; eauto.
        }
        { etrans; eauto. eapply Mapping.le_strong_le; eauto. }
      }
      { eauto. }
      { i. des_ifs. eauto. }
      { eauto. }
    }
    { eapply promise_steps_max_values_src; eauto. }
    { eauto. }
    { eauto. }
    { red in FIN. des.
      hexploit (list_filter_exists (fun loc0 => loc0 <> loc) dom). i. des.
      exists l'. splits. i. etrans; [|eapply COMPLETE0]. condtac; subst.
      { split; i; des; ss. }
      { split; i.
        { split; auto. eapply DOM; auto. }
        { des. eapply DOM; eauto. }
      }
    }
    { eauto. }
    { eauto. }
    { i. des_ifs. rewrite MAXTIMES; auto.
      eapply unchanged_loc_max_ts.
      { eapply added_memory_unchanged_loc; eauto. }
      { eapply MEMSRC. }
    }
  }
  { eauto. }
  { eauto. }
  { i. unfold f'. des_ifs. }
  { eauto. }
  { eapply space_future_memory_trans.
    { eapply space_future_memory_mon_msgs.
      { eapply shited_mapping_space_future_memory.
        { eauto. }
        { etrans; eauto. eapply Mapping.le_strong_le; eauto. }
        { eauto. }
        { eauto. }
        { i. eapply sim_timestamp_exact_mon_strong; [..|eapply SAME]; eauto. }
        { eapply sim_timestamp_exact_mon_strong; [..|eauto]; eauto. }
        { eauto. }
        { eauto. }
      }
      { eapply unchangable_messages_of_memory. }
    }
    { eapply added_memory_space_future_memory; eauto.
      { i. eapply SOUNDPROM in IN; eauto. des. esplits; eauto.
        { des_ifs; eauto. }
        { des_ifs; eauto. }
        { eapply COMPLETE; eauto. }
      }
      { eapply LOCALTGT. }
    }
    { eauto. }
    { refl. }
    { eauto. }
    { eauto. }
    { eauto. }
  }
Admitted.
