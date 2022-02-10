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

Require Import gSimulation.

Require Import JoinedView.
Require Import SeqLift.
Require Import Simple.

Require Import Pred.

Require Import SeqLiftStep.


Lemma wf_release_vers_versions_le
      vers0 vers1 prom rel_vers
      (WF: wf_release_vers vers0 prom rel_vers)
      (VERSLE: versions_le vers0 vers1)
  :
  wf_release_vers vers1 prom rel_vers.
Proof.
  inv WF. econs. i. hexploit PROM; eauto. i. des.
  esplits; eauto.
Qed.

Lemma undef_added_failure lang st lc sc0 mem0 sc1 mem1
      (CONSISTENT: Thread.consistent (Thread.mk lang st lc sc0 mem0))
      (MEMLE: Memory.future_weak mem0 mem1)
      (SCLE: TimeMap.le sc0 sc1)
      (LOCAL: Local.wf lc mem0)
      (MEM0: Memory.closed mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM1: Memory.closed mem1)
      (SC1: Memory.closed_timemap sc1 mem1)
      loc from0 to0 msg from1 to1
      (GET0: Memory.get loc to0 lc.(Local.promises) = Some (from0, msg))
      (MSG: msg <> Message.reserve)
      (GET1: Memory.get loc to1 mem1 = Some (from1, Message.undef))
      (TS: Time.lt to0 to1)
      (NONE: Memory.get loc to1 lc.(Local.promises) = None)
  :
  Thread.steps_failure (Thread.mk _ st lc sc1 mem1).
Proof.
Admitted.

Lemma sim_thread_future
      f0 vers0 flag_tgt vs_src0 vs_tgt0
      mem_src0 mem_tgt0 lc_src0 lc_tgt0 sc_src0 sc_tgt0

      f1 vers1 mem_src1 mem_tgt1 sc_src1 sc_tgt1
      (SIM: sim_thread
              f0 vers0 (fun _ => false) flag_tgt vs_src0 vs_tgt0
              mem_src0 mem_tgt0 lc_src0 lc_tgt0 sc_src0 sc_tgt0)

      (MEMLESRC: Memory.future_weak mem_src0 mem_src1)
      (MEMLETGT: Memory.future_weak mem_tgt0 mem_tgt1)
      (SCLESRC: TimeMap.le sc_src0 sc_src1)
      (SCLETGT: TimeMap.le sc_tgt0 sc_tgt1)
      (SIMMEM: sim_memory_interference f1 vers1 mem_src1 mem_tgt1)
      (VERSIONED: versioned_memory vers1 mem_tgt1)
      (SIMCLOSED: sim_closed_memory f1 mem_src1)

      (SIMSC: sim_timemap (fun _ => True) f1 (Mapping.vers f1) sc_src1 sc_tgt1)
      (MAPLE: Mapping.les f0 f1)
      (VERSLE: versions_le vers0 vers1)

      (CONSISTENT: Local.promise_consistent lc_tgt0)
      (LOCALSRC: Local.wf lc_src0 mem_src0)
      (LOCALTGT: Local.wf lc_tgt0 mem_tgt0)
      (MEMSRC0: Memory.closed mem_src0)
      (MEMTGT0: Memory.closed mem_tgt0)
      (SCSRC0: Memory.closed_timemap sc_src0 mem_src0)
      (SCTGT0: Memory.closed_timemap sc_tgt0 mem_tgt0)
      (WF0: Mapping.wfs f0)
      (VERS0: versions_wf f0 vers0)

      (MEMSRC1: Memory.closed mem_src1)
      (MEMTGT1: Memory.closed mem_tgt1)
      (SCSRC1: Memory.closed_timemap sc_src1 mem_src1)
      (SCTGT1: Memory.closed_timemap sc_tgt1 mem_tgt1)
      (WF1: Mapping.wfs f1)
      (VERS1: versions_wf f1 vers1)
      lang st
  :
  exists lc_src2 sc_src2 mem_src2,
    (<<STEPS: rtc (@Thread.tau_step lang) (Thread.mk lang st lc_src0 sc_src1 mem_src1) (Thread.mk lang st lc_src2 sc_src2 mem_src2)>>) /\
      ((<<FAILURE: Thread.steps_failure (Thread.mk lang st lc_src2 sc_src2 mem_src2)>>) \/
         exists vs_src1 vs_tgt1,
           (<<SIM: sim_thread
                     f1 vers1 (fun _ => false) flag_tgt vs_src1 vs_tgt1
                     mem_src2 mem_tgt1 lc_src2 lc_tgt0 sc_src2 sc_tgt1>>) /\
             (<<VALSRC: forall loc val (VAL: vs_src1 loc = Some val),
               exists val_old,
                 (<<VS: vs_src0 loc = Some val_old>>) /\
                   (<<VAL: Const.le val_old val>>)>>) /\
             (<<VALTGT: forall loc val (VAL: vs_tgt1 loc = Some val), vs_tgt0 loc = Some val>>) /\
             (<<CLOSED: sim_closed_memory f1 mem_src2>>))
.
Proof.
Admitted.
(*   hexploit (@max_values_src_exists mem_src1 lc_src0). *)
(*   intros [vs_src1 MAXSRC1]. des. *)
(*   assert (VALSRC: forall loc val (VAL: vs_src1 loc = Some val), vs_src0 loc = Some val). *)
(*   { admit. } *)
(*   set (vs_tgt1 := fun loc => match vs_src1 loc with *)
(*                              | Some _ => vs_tgt0 loc *)
(*                              | None => None *)
(*                              end). *)
(*   right. esplits. *)
(*   { inv SIM. econs. *)
(*     { eapply sim_timemap_mon_locs; eauto. i. ss. } *)
(*     { eauto. } *)
(*     { inv LOCAL. econs; eauto. *)
(*       { eapply sim_tview_mon_latest; eauto. } *)
(*       { admit. } *)
(*       { eapply wf_release_vers_versions_le; eauto. } *)
(*     } *)
(*     { eauto. } *)
(*     { instantiate (1:=vs_tgt1). admit. *)
(*     } *)
(*     { i. unfold vs_tgt1. des_ifs. *)
(*       hexploit VALSRC; eauto. i. hexploit (PERM loc). *)
(*       rewrite H. auto. *)
(*     } *)
(*     { eauto. } *)
(*     { eauto. } *)
(*     { eauto. } *)
(*   } *)
(*   { admit. } *)
(* Admitted. *)
