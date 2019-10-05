Require Import Omega.
Require Import RelationClasses.

From Paco Require Import paco.
From sflib Require Import sflib.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
Require Import Time.
Require Import Event.
From PromisingLib Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import Cover.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.
Require Import Progress.
Require Import PromiseConsistent.
From PromisingLib Require Import Loc.

Require Import PF.
Require Import Race.
Require Import Behavior.
Require Import SimMemory.
Require Import yjtac.
Require Import Program.
Require Import Cell.
Require Import Time.
Require Import PredStep.
Require Import ReorderPromises2.
Require Import AbortProp.

Require Import DRF_PF.

Require Import PFConsistent.

Set Implicit Arguments.



(* Inductive my_caps (mem0 prom : Memory.t) (l : Loc.t) (t from : Time.t) (msg : Message.t) := *)
(*   (<<CAPS: caps mem0 prom l t from msg>>) /\ *)
(*   (<< *)


Definition wf_time_evt (P: Loc.t -> Time.t -> Prop) (e: ThreadEvent.t) : Prop :=
  match e with
  | ThreadEvent.promise loc from to msg kind =>
    (<<FROM: P loc from>>) /\ (<<TO: P loc to>>)
  | ThreadEvent.write loc from to val released ordw =>
    (<<FROM: P loc from>>) /\ (<<TO: P loc to>>)
  | ThreadEvent.update loc from to valr valw releasedr releasedw ordr ordw =>
    (<<TO: P loc to>>)
  | _ => True
  end.

Lemma wf_time_evt_mon P0 P1
      (LE: P0 <2= P1)
  :
    wf_time_evt P0 <1= wf_time_evt P1.
Proof.
  ii. unfold wf_time_evt in *. des_ifs; des; splits; eauto.
Qed.

Lemma step_times_list_exists P lang th0 th1 e
      (STEPS: (@pred_step P lang) e th0 th1)
  :
    exists times,
      (@pred_step (P /1\ wf_time_evt (fun loc to => List.In to (times loc))) lang) e th0 th1.
Proof.
  inv STEPS. destruct e.
  - exists (fun l => if Loc.eq_dec l loc then
                       [from; to] else []).
    econs; eauto.
    ss. splits; auto; des_ifs; ss; eauto.
  - exists (fun _ => []). econs; eauto. ss.
  - exists (fun _ => []). econs; eauto. ss.
  - exists (fun l => if Loc.eq_dec l loc then
                       [from; to] else []).
    econs; eauto.
    ss. splits; auto; des_ifs; ss; eauto.
  - exists (fun l => if Loc.eq_dec l loc then
                       [tsw] else []).
    econs; eauto.
    ss. splits; auto; des_ifs; ss; eauto.
  - exists (fun _ => []). econs; eauto. ss.
  - exists (fun _ => []). econs; eauto. ss.
  - exists (fun _ => []). econs; eauto. ss.
Qed.

Lemma times_list_exists P lang th0 th1
      (STEPS: rtc (tau (@pred_step P lang)) th0 th1)
  :
    exists times,
      rtc (tau (@pred_step (P /1\ wf_time_evt (fun loc to => List.In to (times loc))) lang)) th0 th1.
Proof.
  ginduction STEPS.
  - exists (fun _ => []). refl.
  - dup H. inv H0.
    eapply step_times_list_exists in TSTEP. des.
    exists (fun loc => times loc ++ times0 loc). econs 2.
    + econs; eauto. eapply pred_step_mon; eauto.
      i. ss. des. split; auto.
      eapply wf_time_evt_mon; eauto.
      i. ss. eapply List.in_or_app; eauto.
    + eapply pred_step_rtc_mon; eauto.
      i. ss. des. split; auto.
      eapply wf_time_evt_mon; eauto.
      i. ss. eapply List.in_or_app; eauto.
Qed.



Inductive diff_after_promises (prom mem0 mem1: Memory.t)
          (caps: Loc.t -> Time.t -> Time.t -> Message.t -> Prop): Prop :=
| diff_after_promises_intro
    (MLE: Memory.le mem0 mem1)
    (DIFF: forall loc to from msg
                  (GET: Memory.get loc to mem1 = Some (from, msg))
                  (NONE: Memory.get loc to mem0 = None),
        (<<CAP: caps loc to from msg>>) /\
        (exists from' to' val released,
            (<<PROM: Memory.get loc to' prom = Some (from', Message.full val released)>>)) /\
        (<<AFTER: forall from' to' val released
                         (PROM: Memory.get loc to' prom = Some (from', Message.full val released)),
            (<<TLE: Time.le to' from>>) >>))
.


Lemma steps_write_not_in P lang (th0 th1: Thread.t lang)




Lemma collapse_other_cappe

Lemma

Lemma my_



Lemma step_wirte_not_in lang (th_tgt th_tgt': Thread.t lang) e_tgt pf
      (STEP: Thread.step pf e_tgt th_tgt th_tgt')
  :
    write_not_in (unchangables th_tgt.(Thread.memory) th_tgt.(Thread.local).(Local.promises))
                 e_tgt.
Proof.
  unfold unchangables. inv STEP.
  - inv STEP0; ss.
  - inv STEP0; ss. inv LOCAL; ss.
    + inv LOCAL0. ii. exploit step_wirte_not_in_write; eauto.
    + inv LOCAL1. inv LOCAL2. ss. ii. exploit step_wirte_not_in_write; eauto.
Qed.


Definition pf_consistent_strong lang (e0:Thread.t lcapped intrang): Prop :=
  forall mem1 sc1
         (CAP: Memory.cap e0.(Thread.local).(Local.promises) e0.(Thread.memory) mem1),
  exists e1,
    (<<STEPS0: rtc (tau (@pred_step is_cancel lang)) (Thread.mk _ e0.(Thread.state) e0.(Thread.local) sc1 mem1) e1>>) /\
    (<<NORESERVE: no_reserves e1.(Thread.local).(Local.promises)>>) /\
    exists e2,
      (<<STEPS1: rtc (tau (@pred_step ((promise_free /1\ (fun e => ~ is_cancel e) /1\ no_acq_read_msgs (caps_loc e0.(Thread.memory) e0.(Thread.local).(Local.promises))) /1\ no_sc) lang)) e1 e2>>) /\
      ((<<FAILURE: Local.failure_step e2.(Thread.local)>>) \/
       (<<PROMISES: e2.(Thread.local).(Local.promises) = Memory.bot>>)).
