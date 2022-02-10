Require Import Omega.
Require Import Bool.
Require Import RelationClasses.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Language.
From PromisingLib Require Import Loc.

Require Import Event.
Require Import Time.

Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.

Require Import Cover.
(* Require Import Mapping. *)
(* Require Import Pred. *)
(* Require Import Trace. *)
(* Require Import MemoryProps. *)
(* Require Import PFConsistent. *)
(* Require Import PFConsistentStrong. *)

Set Implicit Arguments.

Module FutureCertify.
  Section FutureCertify.
    Variable (lang: language).

    (* Lemma cap_steps_current_steps *)
    (*       th0 th1 mem1 sc1 *)
    (*       (LOCAL: Local.wf (Thread.local th0) (Thread.memory th0)) *)
    (*       (MEMORY: Memory.closed (Thread.memory th0)) *)
    (*       (SC: Memory.closed_timemap (Thread.sc th0) (Thread.memory th0)) *)
    (*       (CAP: Memory.cap (Thread.memory th0) mem1) *)
    (*       (SC_MAX: Memory.max_concrete_timemap mem1 sc1) *)
    (*       (STEPS: rtc (@Thread.tau_step lang) *)
    (*                   (Thread.mk lang (Thread.state th0) (Thread.local th0) sc1 mem1) *)
    (*                   th1) *)
    (*       (CONSISTENT: Local.promise_consistent (Thread.local th1)) *)
    (*   : *)
    (*     exists lc' sc' mem', *)
    (*       (<<STEPS: rtc (@Thread.tau_step lang) *)
    (*                     th0 *)
    (*                     (Thread.mk lang (Thread.state th1) lc' sc' mem')>>) /\ *)
    (*       (<<CONSISTENT: Local.promise_consistent lc'>>) *)
    (* . *)
    (* Proof. *)
    (*   eapply pred_steps_thread_steps in STEPS. *)
    (*   destruct th0, th1. ss. *)
    (*   hexploit steps_map. *)
    (*   { eapply ident_map_le. } *)
    (*   { eapply ident_map_bot. } *)
    (*   { eapply ident_map_eq. } *)
    (*   { i. eapply ident_map_mappable_evt. } *)
    (*   { eapply STEPS. } *)
    (*   { ss. } *)
    (*   { ss. } *)
    (*   { ss. } *)
    (*   { eapply Local.cap_wf; eauto. } *)
    (*   { eapply LOCAL. } *)
    (*   { eauto. } *)
    (*   { eapply Memory.cap_closed; eauto. } *)
    (*   { eauto. } *)
    (*   { eapply Memory.max_concrete_timemap_closed; eauto. } *)
    (*   { eapply map_ident_in_memory_local; eauto; ss. *)
    (*     eapply ident_map_lt. *)
    (*   } *)
    (*   { econs. *)
    (*     { i. destruct msg as [val released|]; auto. right. *)
    (*       exists to, from, (Message.concrete val released), (Message.concrete val released). *)
    (*       eapply Memory.cap_inv in GET; eauto. des; ss. esplits; eauto. *)
    (*       { refl. } *)
    (*       { eapply ident_map_message. } *)
    (*       { refl. } *)
    (*     } *)
    (*     { i. eapply CAP in GET. left. exists fto, ffrom, fto, ffrom. splits; ss. *)
    (*       { refl. } *)
    (*       { refl. } *)
    (*       { i. econs; eauto. } *)
    (*     } *)
    (*   } *)
    (*   { eapply mapping_map_lt_collapsable_unwritable. eapply ident_map_lt. } *)
    (*   { eapply ident_map_timemap. } *)
    (*   { eapply Memory.max_concrete_timemap_spec; eauto. *)
    (*     eapply Memory.cap_closed_timemap; eauto. } *)
    (*   { instantiate (1:=fun _ => True). ss. } *)
    (*   i. des. esplits. *)
    (*   { eapply rtc_implies; try apply STEP. i. inv H. inv TSTEP. econs; eauto. } *)
    (*   { inv LOCAL0. eapply promise_consistent_mon; cycle 1; eauto. *)
    (*     { refl. } *)
    (*     eapply promise_consistent_map; eauto. *)
    (*     { eapply ident_map_le; eauto. } *)
    (*     { eapply ident_map_eq; eauto. } *)
    (*   } *)
    (* Qed. *)

    (* Definition future_certify lang (e:Thread.t lang): Prop := *)
    (*   forall sc1 mem1 *)
    (*     (FUTURE: Memory.future_weak (Thread.memory e) mem1) *)
    (*     (FUTURE: TimeMap.le (Thread.sc e) sc1) *)
    (*     (WF: Local.wf (Thread.local e) mem1) *)
    (*     (SC: Memory.closed_timemap sc1 mem1) *)
    (*     (MEM: Memory.closed mem1), *)
    (*     (<<FAILURE: Thread.steps_failure (Thread.mk lang (Thread.state e) (Thread.local e) sc1 mem1)>>) \/ *)
    (*     exists e2, *)
    (*       (<<STEPS: rtc (@Thread.tau_step lang) (Thread.mk lang (Thread.state e) (Thread.local e) sc1 mem1) e2>>) /\ *)
    (*       (<<PROMISES: (Local.promises (Thread.local e2)) = Memory.bot>>). *)

    (* Lemma future_certify_exists *)
    (*       e *)
    (*       (LOCAL: Local.wf (Thread.local e) (Thread.memory e)) *)
    (*       (MEMORY: Memory.closed (Thread.memory e)) *)
    (*       (SC: Memory.closed_timemap (Thread.sc e) (Thread.memory e)) *)
    (*       (CONSISTENT: @Thread.consistent lang e): *)
    (*   future_certify e. *)
    (* Proof. *)
    (*   eapply consistent_pf_consistent_super_strong in CONSISTENT; eauto. des. *)
    (*   exploit (@concrete_promise_max_timemap_exists (Thread.memory e) (Local.promises (Thread.local e))). *)
    (*   { eapply MEMORY. } i. des. *)
    (*   ii. exploit (CONSISTENT0 mem1 TimeMap.bot sc1); eauto. i. des. *)
    (*   eapply Trace.silent_steps_tau_steps in STEPS; cycle 1. *)
    (*   { eapply List.Forall_impl; eauto. i. ss. des. auto. } *)
    (*   unguard. des. *)
    (*   { left. unfold Thread.steps_failure. destruct e1. ss. esplits; eauto. } *)
    (*   { right. esplits; eauto. } *)
    (* Qed. *)

    Lemma future_consistent
          e sc' mem'
          (LOCAL: Local.wf (Thread.local e) (Thread.memory e))
          (MEMORY: Memory.closed (Thread.memory e))
          (SC: Memory.closed_timemap (Thread.sc e) (Thread.memory e))
          (CONSISTENT: @Thread.consistent lang e)
          (SC_FUTURE: TimeMap.le (Thread.sc e) sc')
          (MEM_FUTURE: Memory.future_weak (Thread.memory e) mem')
          (LOCAL': Local.wf (Thread.local e) mem')
          (MEMORY': Memory.closed mem')
          (SC': Memory.closed_timemap sc' mem'):
      Thread.consistent (Thread.mk lang (Thread.state e) (Thread.local e) sc' mem').
    Proof.
    (*   ii. ss. *)
    (*   eapply future_certify_exists; try exact CONSISTENT; eauto. *)
    (*   - etrans; eauto. eapply Memory.cap_future_weak; eauto. *)
    (*   - etrans; eauto. *)
    (*     hexploit Memory.cap_closed_timemap; try exact SC'; eauto. i. *)
    (*     hexploit Memory.max_concrete_timemap_spec; eauto. *)
    (*   - eapply Local.cap_wf; eauto. *)
    (*   - eapply Memory.max_concrete_timemap_closed; eauto. *)
    (*   - eapply Memory.cap_closed; eauto. *)
    (* Qed. *)
    Admitted.
  End FutureCertify.

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
        (NONE: Memory.get loc to1 mem0 = None)
    :
      Thread.steps_failure (Thread.mk _ st lc sc1 mem1).
  Proof.
  Admitted.
End FutureCertify.
