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



Lemma mapped_msgs_exists_aux f0 f1 vers srctm flag_src flag_tgt msgs_tgt prom_src prom_tgt loc flag_new
      (PROM: sim_promises srctm flag_src flag_tgt f0 vers prom_src prom_tgt)
      (MAPLE: Mapping.le (f0 loc) f1)
      (MSGS: forall from to msg (IN: List.In (from, to, msg) msgs_tgt), Memory.get loc to prom_tgt = Some (from, msg))
      (WF0: Mapping.wfs f0)
      (WF1: Mapping.wf f1)
      (VERSWF: versions_wf f0 vers)
  :
    exists msgs_src,
      (<<FORALL: List.Forall2
                   (fun '(from_src, to_src, msg_src) '(from_tgt, to_tgt, msg_tgt) =>
                      (<<FROM: sim_timestamp_exact f1 f1.(Mapping.ver) from_src from_tgt>>) /\
                      (<<TO: sim_timestamp_exact f1 f1.(Mapping.ver) to_src to_tgt>>) /\
                      (<<MESSAGE: sim_message_max flag_new loc to_src f0 (vers loc to_tgt) msg_src msg_tgt>>))
                   msgs_src msgs_tgt>>).
Proof.
  revert MSGS. induction msgs_tgt; i.
  { exists []. red. econs. }
  destruct a as [[from_tgt to_tgt] msg_tgt].
  hexploit MSGS.
  { left. eauto. }
  intros GETTGT. hexploit sim_promises_get; eauto. i. des.
  hexploit sim_timestamp_exact_mon_exists; [eapply FROM|..]; eauto. i. des.
  hexploit sim_timestamp_exact_mon_exists; [eapply TO|..]; eauto. i. des.
  hexploit (@sim_message_max_exists flag_new loc ts_src0 f0 (vers loc to_tgt) msg_tgt); eauto.
  { i. hexploit VERS; eauto. i. des. esplits; eauto.
    exploit VERSWF. rewrite VER. ss.
  }
  i. des.
  hexploit IHmsgs_tgt; eauto.
  { i. eapply MSGS. right. auto. }
  i. des. exists ((ts_src1, ts_src0, msg_src)::msgs_src).
  red. econs; eauto.
Qed.

Lemma mapped_msgs_wf_msgs f0 f1 msgs_src msgs_tgt loc vers flag_new
      (WF1: Mapping.wf f1)
      (MSGSWF: wf_cell_msgs msgs_tgt)
      (FORALL: List.Forall2
                 (fun '(from_src, to_src, msg_src) '(from_tgt, to_tgt, msg_tgt) =>
                    (<<FROM: sim_timestamp_exact f1 f1.(Mapping.ver) from_src from_tgt>>) /\
                    (<<TO: sim_timestamp_exact f1 f1.(Mapping.ver) to_src to_tgt>>) /\
                    (<<MESSAGE: sim_message_max flag_new loc to_src f0 (vers loc to_tgt) msg_src msg_tgt>>))
                 msgs_src msgs_tgt)
      (BOTNONE: List.Forall (fun '(_, to, _) => to <> Time.bot) msgs_tgt)
  :
    wf_cell_msgs msgs_src.
Proof.
  pose proof mapping_latest_wf_loc as VERWF.
  red in MSGSWF. des.
  revert msgs_src DISJOINT MSGSWF0 FORALL BOTNONE. induction msgs_tgt; i.
  { inv FORALL. repeat red. splits.
    { econs. }
    { econs. }
  }
  inv FORALL. inv MSGSWF0. inv DISJOINT. inv BOTNONE.
  destruct x as [[from_src to_src] msg_src]. des; clarify.
  hexploit IHmsgs_tgt; eauto. i. repeat red in H. repeat red. des. econs.
  { econs; eauto.
    eapply List.Forall_forall. intros [[from_src0 to_src0] msg_src0] IN.
    eapply list_Forall2_in2 in IN; eauto. des.
    destruct b as [[from_tgt0 to_tgt0] msg_tgt0]. des.
    eapply List.Forall_forall in HD; eauto. ss.
    eapply sim_timestamp_exact_le; eauto.
  }
  { econs; eauto. split.
    { eapply sim_message_max_msg_wf; eauto. }
    { right. eapply sim_timestamp_exact_lt; eauto. }
  }
Qed.

Lemma mapped_msgs_disjoint f0 f1 msgs_src msgs_tgt loc vers flag_new mem_src
      ts_tgt ts_src
      (WF1: Mapping.wf f1)
      (MSGSWF: wf_cell_msgs msgs_tgt)
      (FORALL: List.Forall2
                 (fun '(from_src, to_src, msg_src) '(from_tgt, to_tgt, msg_tgt) =>
                    (<<FROM: sim_timestamp_exact f1 f1.(Mapping.ver) from_src from_tgt>>) /\
                    (<<TO: sim_timestamp_exact f1 f1.(Mapping.ver) to_src to_tgt>>) /\
                    (<<MESSAGE: sim_message_max flag_new loc to_src f0 (vers loc to_tgt) msg_src msg_tgt>>))
                 msgs_src msgs_tgt)
      (BOTNONE: List.Forall (fun '(_, to, _) => to <> Time.bot) msgs_tgt)


      (TS

  :
    List.Forall
      (fun '(from, to, msg) => (__guard__((<<MAX: Time.le (Memory.max_ts loc mem_src) from>>) \/ (<<RESERVE: msg = Message.reserve>>) /\ (<<DISJOINT: forall to2 from2 msg2 (GET: Memory.get loc to2 mem_src = Some (from2, msg2)), Interval.disjoint (from, to) (from2, to2)>>))) /\ (<<TS: Time.lt from to>>) /\ (<<MSGTO: Memory.message_to msg loc to>>) /\ (<<WF: Message.wf msg>>) /\ (<<CLOSED: semi_closed_message msg mem_src loc to>>)) msgs_src.
Proof.


shifted_mapping_exists


Lemma mapped_msgs_wf_msgs f0 f1 msgs_src msgs_tgt loc vers flag_new
      mem_src
      (WF1: Mapping.wf f1)
      (MSGSWF: wf_cell_msgs msgs_tgt)
      (FORALL: List.Forall2
                 (fun '(from_src, to_src, msg_src) '(from_tgt, to_tgt, msg_tgt) =>
                    (<<FROM: sim_timestamp_exact f1 f1.(Mapping.ver) from_src from_tgt>>) /\
                    (<<TO: sim_timestamp_exact f1 f1.(Mapping.ver) to_src to_tgt>>) /\
                    (<<MESSAGE: sim_message_max flag_new loc to_src f0 (vers loc to_tgt) msg_src msg_tgt>>))
                 msgs_src msgs_tgt)
      (BOTNONE: List.Forall (fun '(_, to, _) => to <> Time.bot) msgs_tgt)
  :
    (<<MSGSWF: wf_cell_msgs msgs_src>>) /\
    (<<MSGS: List.Forall
               (fun '(from, to, msg) => (__guard__((<<MAX: Time.le (Memory.max_ts loc mem_src) from>>) \/ (<<RESERVE: msg = Message.reserve>>) /\ (<<DISJOINT: forall to2 from2 msg2 (GET: Memory.get loc to2 mem_src = Some (from2, msg2)), Interval.disjoint (from, to) (from2, to2)>>))) /\ (<<TS: Time.lt from to>>) /\ (<<MSGTO: Memory.message_to msg loc to>>) /\ (<<WF: Message.wf msg>>) /\ (<<CLOSED: semi_closed_message msg mem_src loc to>>)) msgs_src>>)
.
Proof.
  pose proof mapping_latest_wf_loc as VERWF.
  red in MSGSWF. des.
  revert msgs_src DISJOINT MSGSWF0 FORALL BOTNONE. induction msgs_tgt; i.
  { inv FORALL. repeat red. splits.
    { econs. }
    { econs. }
  }
  inv FORALL. inv MSGSWF0. inv DISJOINT. inv BOTNONE.
  destruct x as [[from_src to_src] msg_src]. des; clarify.
  hexploit IHmsgs_tgt; eauto. i. repeat red in H. repeat red. des. econs.
  { econs; eauto.
    eapply List.Forall_forall. intros [[from_src0 to_src0] msg_src0] IN.
    eapply list_Forall2_in2 in IN; eauto. des.
    destruct b as [[from_tgt0 to_tgt0] msg_tgt0]. des.
    eapply List.Forall_forall in HD; eauto. ss.
    eapply sim_timestamp_exact_le; eauto.
  }
  { econs; eauto. split.
    { eapply sim_message_max_msg_wf; eauto. }
    { right. eapply sim_timestamp_exact_lt; eauto. }
  }
Qed.



Lemma mapped_msgs_complete f0 f1 msgs_src msgs_tgt loc vers flag_new
      (WF1: Mapping.wf f1)
      (MSGSWF: wf_cell_msgs msgs_tgt)
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
      (MSGSWF: wf_cell_msgs msgs_tgt)
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
      (MSGSWF: wf_cell_msgs msgs_tgt)
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
      (MSGSWF: wf_cell_msgs msgs_tgt)
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

Lemma mapped_msgs_disjoint f0 f1 msgs_src msgs_tgt loc vers flag_new mem_src
      (WF1: Mapping.wf f1)
      (MSGSWF: wf_cell_msgs msgs_tgt)
      (FORALL: List.Forall2
                 (fun '(from_src, to_src, msg_src) '(from_tgt, to_tgt, msg_tgt) =>
                    (<<FROM: sim_timestamp_exact f1 f1.(Mapping.ver) from_src from_tgt>>) /\
                    (<<TO: sim_timestamp_exact f1 f1.(Mapping.ver) to_src to_tgt>>) /\
                    (<<MESSAGE: sim_message_max flag_new loc to_src f0 (vers loc to_tgt) msg_src msg_tgt>>))
                 msgs_src msgs_tgt)
  :
    List.Forall
      (fun '(from, to, msg) => (__guard__((<<MAX: Time.le (Memory.max_ts loc mem_src) from>>) \/ (<<RESERVE: msg = Message.reserve>>) /\ (<<DISJOINT: forall to2 from2 msg2 (GET: Memory.get loc to2 mem_src = Some (from2, msg2)), Interval.disjoint (from, to) (from2, to2)>>))) /\ (<<TS: Time.lt from to>>) /\ (<<MSGTO: Memory.message_to msg loc to>>) /\ (<<WF: Message.wf msg>>) /\ (<<CLOSED: semi_closed_message msg mem_src loc to>>)) msgs_src.
Proof.
  i. eapply List.Forall_forall. i.
  eapply list_Forall2_in2 in H; eauto. des.
  destruct b as [[from_tgt to_tgt] msg_tgt].
  destruct x as [[from_src to_src] msg_src]. des. esplits; eauto.



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

List.Forall
                    (fun '(from, to, msg) => (__guard__((<<MAX: Time.le (Memory.max_ts loc mem0) from>>) \/ (<<RESERVE: msg = Message.reserve>>) /\ (<<DISJOINT: forall to2 from2 msg2 (GET: Memory.get loc to2 mem0 = Some (from2, msg2)), Interval.disjoint (from, to) (from2, to2)>>))) /\ (<<TS: Time.lt from to>>) /\ (<<MSGTO: Memory.message_to msg loc to>>) /\ (<<WF: Message.wf msg>>) /\ (<<CLOSED: semi_closed_message msg mem0 loc to>>)) msgs

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
  hexploit (@shifted_mapping_exists (f0 loc) (srctm loc)); eauto. i. des.

  hexploit


    (MSGCOMPLETE: forall to_tgt from_tgt msg_tgt
                         (GETTGT: Memory.get loc to_tgt prom_tgt = Some (from_tgt, msg_tgt)),
        exists to_src from_src msg_src,
          (<<TO: sim_timestamp_exact f1 f1.(Mapping.ver) to_src to_tgt>>) /\
          (<<MSG: sim_message_max false loc to_src f0 (vers loc to_tgt) msg_src msg_tgt>>) /\
          (<<CLOSED: Mapping.closed f1 f1.(Mapping.ver) to_src>>) /\
          (<<IN: List.In (from_src, to_src, msg_src) msgs>>))
    (MSGSOUND: forall to_src from_src msg_src
                      (IN: List.In (from_src, to_src, msg_src) msgs),
        exists to_tgt from_tgt msg_tgt,
          (<<TO: sim_timestamp_exact f1 f1.(Mapping.ver) to_src to_tgt>>) /\
          (<<FROM: sim_timestamp_exact f1 f1.(Mapping.ver) from_src from_tgt>>) /\
          (<<GET: Memory.get loc to_tgt prom_tgt = Some (from_tgt, msg_tgt)>>))

    (CLOSEDIF: forall ts (CLOSED: Mapping.closed f1 f1.(Mapping.ver) ts),
        (<<CLOSED: Mapping.closed (f0 loc) (f0 loc).(Mapping.ver) ts>>) \/
        (exists from val released, (<<IN: List.In (from, ts, Message.concrete val released) msgs>>)))

         (FORALL: List.Forall
                    (fun '(from, to, msg) => (__guard__((<<MAX: Time.le (Memory.max_ts loc mem0) from>>) \/ (<<RESERVE: msg = Message.reserve>>) /\ (<<DISJOINT: forall to2 from2 msg2 (GET: Memory.get loc to2 mem0 = Some (from2, msg2)), Interval.disjoint (from, to) (from2, to2)>>))) /\ (<<TS: Time.lt from to>>) /\ (<<MSGTO: Memory.message_to msg loc to>>) /\ (<<WF: Message.wf msg>>) /\ (<<CLOSED: semi_closed_message msg mem0 loc to>>)) msgs),




  wf_cell_msgs

add_promises_latest


Admitted.


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
