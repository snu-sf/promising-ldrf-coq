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
