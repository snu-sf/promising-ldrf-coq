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
  { admit. }
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
      { admit. }
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
    { admit. }
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
    { i. des_ifs. admit. }
  }
  { eauto. }
  { eauto. }
  { i. unfold f'. des_ifs. }
  { eauto. }
  { econs. unfold f'. i. des_ifs.
    { destruct (Time.le_lt_dec (srctm loc) to_tgt).
      { admit. }
      { rewrite SRCTM in l. rewrite FLAGSRC in l; eauto.
        eapply SAME in TO0; eauto.


        eapply SAME in FROM1.

 admit.

}
    { eapply sim_timestamp_exact_inject in FROM0; eauto.
      eapply sim_timestamp_exact_inject in TO0; eauto. subst. splits; auto.
      inv MEM0. inv COVERED. rewrite OTHER in GET1; eauto. econs; eauto.
    }
  }


ss.

inv MSGS.

 eauto. }

 eauto.

eauto.



eapply COMPLETE in GETTGT. eapply COMPLETEPROM in GETTGT; eauto. }



        3:{
eapply MAX0 in GETTGT; eauto.
        eapply COMPLETE in GETTGT. eapply COMPLETEMEM; eauto.
      }

in GETTGT; eauto.


econs. assert (released = None).
        { admit. }
        { admit. }
        sim_memory

        subst. econs.
released 4 with None.

econs. eauto.

eauto.

sim_memory sim_closed_memory eauto.

 eauto.


  hexploit mapped_msgs_complete.
  { eapply MAPWF. }
  { eapply FORALL. }
  { eapply CLOSED0. }
eauto. }
  { eauto. }
  {

eapply list_Forall2_impl; eaut.
    {


/ List.Forall_impl.

  hexploit messages_times_exists.


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
      (<<MAPFUTURE: map_future_memory f0 f1 mem_src1>>)
.
Proof.
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
  hexploit (@shifted_mapping_exists (f0 loc) (srctm loc)); eauto. i. des.
Admitted.



(*   { rewrite TOP in TOP. *)

(*   i. des. rewrite *)



(* Lemma add_promises_latest lang (st: lang.(Language.state)) tvw sc loc msgs: *)
(*   forall prom0 mem0 *)
(*          (WFMSGS: wf_cell_msgs msgs) *)
(*          (MLE: Memory.le prom0 mem0) *)
(*          (MEM: Memory.closed mem0) *)
(*          (FORALL: List.Forall *)
(*                     (fun '(from, to, msg) => (__guard__((<<MAX: Time.le (Memory.max_ts loc mem0) from>>) \/ (<<RESERVE: msg = Message.reserve>>) /\ (<<DISJOINT: forall to2 from2 msg2 (GET: Memory.get loc to2 mem0 = Some (from2, msg2)), Interval.disjoint (from, to) (from2, to2)>>))) /\ (<<TS: Time.lt from to>>) /\ (<<MSGTO: Memory.message_to msg loc to>>) /\ (<<WF: Message.wf msg>>) /\ (<<CLOSED: semi_closed_message msg mem0 loc to>>)) msgs), *)


(*   { *)

(* ; eauto. *)
(*   hexploit (MAXSRC loc). *)


(*     { speeapply MAXSRC. *)

(*   2:{ *)

(* hexploit NONMAX; eauto. i. des. *)



(* sim_memory *)
(*   inv SIM. *)
(*   hexploit sim_memory_top; eauto. intros TOP. *)


(* Lemma shifted_mapping_exists (f0: Mapping.t) *)
(*       (ts: Time.t) (fts: Time.t) *)
(*       (TOP: top_time fts f0) *)
(*       (WF: Mapping.wf f0) *)
(*   : *)
(*     exists f1, *)
(*       (<<SAME: forall to fto *)
(*                       (TS: Time.lt to ts) *)
(*                       (MAP: sim_timestamp_exact f0 f0.(Mapping.ver) fto to), *)
(*           sim_timestamp_exact f1 f1.(Mapping.ver) fto to>>) /\ *)
(*       (<<TS: sim_timestamp_exact f1 f1.(Mapping.ver) fts ts>>) /\ *)
(*       (<<LE: Mapping.le f0 f1>>) /\ *)
(*       (<<WF: Mapping.wf f1>>) /\ *)
(*       (<<CLOSED: forall ts, Mapping.closed f1 f1.(Mapping.ver) ts <-> Mapping.closed f0 f0.(Mapping.ver) ts>>) *)
(* . *)



(* Admitted. *)

(* Lemma sim_thread_deflag_unmatch_aux2 *)
(*       f0 vers flag_src flag_tgt vs_src vs_tgt *)
(*       mem_src0 mem_tgt lc_src0 lc_tgt sc_src sc_tgt *)
(*       loc ts *)
(*       (SIM: sim_thread *)
(*               f0 vers flag_src flag_tgt vs_src vs_tgt *)
(*               mem_src0 mem_tgt lc_src0 lc_tgt sc_src sc_tgt) *)
(*       (CONSISTENT: Local.promise_consistent lc_tgt) *)
(*       (LOCALSRC: Local.wf lc_src0 mem_src0) *)
(*       (LOCALTGT: Local.wf lc_tgt mem_tgt) *)
(*       (MEMSRC: Memory.closed mem_src0) *)
(*       (MEMTGT: Memory.closed mem_tgt) *)
(*       (SCSRC: Memory.closed_timemap sc_src mem_src0) *)
(*       (SCTGT: Memory.closed_timemap sc_tgt mem_tgt) *)
(*       (WF: Mapping.wfs f0) *)
(*       (FLAG: flag_src loc = Some ts) *)
(*       lang st *)
(*   : *)
(*     exists lc_src1 mem_src1 f1 flag, *)
(*       (<<STEPS: rtc (tau (@pred_step is_promise _)) *)
(*                     (Thread.mk lang st lc_src0 sc_src mem_src0) *)
(*                     (Thread.mk _ st lc_src1 sc_src mem_src1)>>) /\ *)
(*       (<<SIM: sim_thread *)
(*                 f1 vers *)
(*                 (fun loc0 => if Loc.eq_dec loc0 loc then None else flag_src loc0) *)
(*                 (fun loc0 => if Loc.eq_dec loc0 loc then flag else flag_tgt loc0) *)
(*                 vs_src vs_tgt *)
(*                 mem_src1 mem_tgt lc_src1 lc_tgt sc_src sc_tgt>>) /\ *)
(*       (<<WF: Mapping.wfs f1>>) /\ *)
(*       (<<MAPLE: Mapping.les f0 f1>>) /\ *)
(*       (<<UNCH: forall loc0 (NEQ: loc0 <> loc), f1 loc0 = f0 loc0>>) /\ *)
(*       (<<MAPFUTURE: map_future_memory f0 f1 mem_src1>>) *)
(* . *)
(* Proof. *)
(* Admitted. *)
