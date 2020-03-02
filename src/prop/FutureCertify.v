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
Require Import Mapping.
Require Import Pred.
Require Import MemoryProps.
Require Import PFConsistent.
Require Import PFConsistentStrong.

Set Implicit Arguments.


Lemma memory_cap_covered
      mem0 mem1
      loc to
      (CAP: Memory.cap mem0 mem1)
      (INHABITED: Memory.inhabited mem0)
      (ITV: Interval.mem (Time.bot, Time.incr (Memory.max_ts loc mem0)) to):
  covered loc to mem1.
Proof.
  inv ITV. inv CAP. set (@cell_elements_least
         (mem0 loc)
         (fun to' => Time.le to to')). des; cycle 1.
  { destruct (Time.le_lt_dec to (Memory.max_ts loc mem0)).
    - exfalso. exploit Memory.max_ts_spec.
      + eapply INHABITED.
      + i. des. exploit EMPTY; eauto.
    - econs.
      + eapply BACK.
      + econs; eauto. }
  set (@cell_elements_greatest
         (mem0 loc)
         (fun to' => Time.lt to' to)). des; cycle 1.
  { exfalso. exploit EMPTY.
    - eapply INHABITED.
    - eauto.
    - ss. }
  destruct (Time.le_lt_dec to from).
  - exploit MIDDLE.
    + econs.
      * eapply GET0.
      * eapply GET.
      * eapply TimeFacts.lt_le_lt; eauto.
      * i. destruct (Memory.get loc ts mem0) eqn:GET1; auto.
        exfalso. destruct p.
        destruct (Time.le_lt_dec to ts).
        { exploit LEAST; eauto. i.
          eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt.
          { eapply x. }
          eapply TimeFacts.le_lt_lt.
          { eapply TS2. }
          { eapply memory_get_ts_strong in GET. des; clarify; ss.
            exfalso. eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt.
            - eapply l.
            - eauto. } }
        { exploit GREATEST; eauto. i.
          eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt.
          { eapply x. }
          { eauto. } }
    + eapply TimeFacts.lt_le_lt; eauto.
    + i. econs; eauto. econs; eauto.
  - econs.
    + eapply Memory.cap_le; try apply GET; eauto. refl.
    + econs; eauto.
Qed.


Module FutureCertify.
  Section FutureCertify.
    Variable (lang: language).

    Lemma future_memory_map
          mem mem_cap mem_future times
          (CAP: Memory.cap mem mem_cap)
          (FUTURE: Memory.future_weak mem mem_future)
          (CLOSED: Memory.closed mem):
      exists (f: Loc.t -> Time.t -> Time.t -> Prop),
        (<<IDENT: map_ident_in_memory f mem>>) /\
        (<<MAPLT: mapping_map_lt f>>) /\
        (<<MEMORY: memory_map f mem_cap mem_future>>) /\
        (<<COMPLETE: forall loc to (IN: List.In to (times loc)),
            exists fto, (<<MAPPED: f loc to fto>>)>>).
    Proof.
      exploit (choice (fun loc f =>
                         (<<COMPLETE: forall to (IN: List.In to (Time.incr (Memory.max_ts loc mem)::(times loc))), exists fto, (<<MAPPED: f to fto>>)>>) /\
                         (<<SAME: forall ts (TS: Time.le ts (Memory.max_ts loc mem)), f ts ts>>) /\
                         (<<BOUND: forall to fto (MAPPED: f to fto) (TS: Time.lt (Memory.max_ts loc mem) to),
                             (Time.lt (Time.join (Memory.max_ts loc mem_future) (Memory.max_ts loc mem)) fto)>>) /\
                         (<<MAPLT: mapping_map_lt_loc f>>))).
      { intros loc. hexploit shift_map_exists.
        - eapply Time.join_r.
        - eapply Time.incr_spec.
        - i. des. exists f. esplits; eauto.
          i. exploit BOUND; eauto. i. des. eapply x. }
      intros [f FSPEC]. exists f.
      assert (IDENT: map_ident_in_memory f mem).
      { ii. specialize (FSPEC loc). des. eauto. }
      splits; eauto.
      - ii. specialize (FSPEC loc). des. eauto.
      - econs.
        + i. eapply Memory.cap_inv in GET; eauto. des; eauto.
          dup GET. destruct msg; eauto. eapply Memory.future_weak_get1 in GET; eauto. des.
          right. esplits; eauto.
          * specialize (FSPEC loc). des. eapply SAME.
            eapply Memory.max_ts_spec in GET0. des. auto.
          * eapply map_ident_in_memory_closed_message; eauto.
            inv CLOSED. eapply CLOSED0 in GET0. des. eauto.
        + i. specialize (FSPEC loc). des.
          exploit COMPLETE.
          { ss. left. auto. } i. des.
          exploit BOUND; eauto.
          { eapply Time.incr_spec. } i.
          left. esplits.
          * eapply MAPPED.
          * eapply Time.bot_spec.
          * eapply Memory.max_ts_spec in GET. des.
            etrans; eauto. etrans.
            { eapply Time.join_l. }
            { left. eapply x. }
          * eapply map_ident_in_memory_bot; eauto.
          * i. inv CLOSED. eapply memory_cap_covered; eauto.
      - ii. specialize (FSPEC loc). des. eapply COMPLETE; ss; eauto.
    Qed.

    Lemma cap_steps_current_steps
          th0 th1 mem1 sc1
          (LOCAL: Local.wf th0.(Thread.local) th0.(Thread.memory))
          (MEMORY: Memory.closed th0.(Thread.memory))
          (SC: Memory.closed_timemap th0.(Thread.sc) th0.(Thread.memory))
          (CAP: Memory.cap th0.(Thread.memory) mem1)
          (SC_MAX: Memory.max_concrete_timemap mem1 sc1)
          (STEPS: rtc (@Thread.tau_step lang)
                      (Thread.mk lang th0.(Thread.state) th0.(Thread.local) sc1 mem1)
                      th1)
          (CONSISTENT: Local.promise_consistent th1.(Thread.local))
      :
        exists lc' sc' mem',
          (<<STEPS: rtc (@Thread.tau_step lang)
                        th0
                        (Thread.mk lang th1.(Thread.state) lc' sc' mem')>>) /\
          (<<CONSISTENT: Local.promise_consistent lc'>>)
    .
    Proof.
      eapply pred_steps_thread_steps in STEPS.
      eapply pred_steps_traced_step in STEPS. des.
      hexploit traced_times_list_exists; eauto. i. des.
      exploit (@future_memory_map _ _ th0.(Thread.memory) times CAP); eauto.
      { refl. } i. des.
      destruct th0, th1. ss.
      hexploit traced_steps_map.
      { eapply mapping_map_lt_map_le; eauto. }
      { eapply map_ident_in_memory_bot; eauto. }
      { eapply mapping_map_lt_map_eq; eauto. }
      { eapply wf_time_mapped_mappable; eauto. }
      { eauto. }
      { ss. }
      { ss. }
      { ss. }
      { eapply Local.cap_wf; eauto. }
      { eapply LOCAL. }
      { eauto. }
      { eapply Memory.cap_closed; eauto. }
      { eauto. }
      { eapply Memory.max_concrete_timemap_closed; eauto. }
      { eapply map_ident_in_memory_local; eauto. }
      { eauto. }
      { eapply mapping_map_lt_collapsable_unwritable. eauto. }
      { eapply map_ident_in_memory_closed_timemap; eauto.
        ss. eapply memory_concrete_le_closed_timemap; cycle 1.
        - eapply Memory.max_concrete_timemap_closed; eauto.
        - ii. eapply Memory.cap_inv in GET; eauto. des; clarify. }
      { eapply Memory.max_concrete_timemap_spec; eauto.
        eapply Memory.cap_closed_timemap; eauto. }
      i. des. eapply pred_steps_traced_step2 in STEPS.
      - exists flc1, fsc1, fmem1. split.
        + eapply thread_steps_pred_steps; eauto.
        + inv LOCAL0. eapply promise_consistent_mon; cycle 1; eauto.
          { refl. }
          eapply promise_consistent_map; eauto.
          { eapply mapping_map_lt_map_le; eauto. }
          { eapply mapping_map_lt_map_eq; eauto. }
      - apply List.Forall_forall. ii.
        eapply list_Forall2_in in H; eauto. des. split.
        { instantiate (1:=fun _ => True). ss. }
        eapply List.Forall_forall in EVENTS; eauto. des.
        destruct a, x. ss. inv EVENT; auto.
    Qed.

    Definition future_certify lang (e:Thread.t lang): Prop :=
      forall sc1 mem1
        (FUTURE: Memory.future_weak e.(Thread.memory) mem1)
        (FUTURE: TimeMap.le e.(Thread.sc) sc1)
        (WF: Local.wf e.(Thread.local) mem1)
        (SC: Memory.closed_timemap sc1 mem1)
        (MEM: Memory.closed mem1),
        (<<FAILURE: Thread.steps_failure (Thread.mk lang e.(Thread.state) e.(Thread.local) sc1 mem1)>>) \/
        exists e2,
          (<<STEPS: rtc (@Thread.tau_step lang) (Thread.mk lang e.(Thread.state) e.(Thread.local) sc1 mem1) e2>>) /\
          (<<PROMISES: e2.(Thread.local).(Local.promises) = Memory.bot>>).

    Lemma future_certify_exists
          e
          (LOCAL: Local.wf e.(Thread.local) e.(Thread.memory))
          (MEMORY: Memory.closed e.(Thread.memory))
          (SC: Memory.closed_timemap e.(Thread.sc) e.(Thread.memory))
          (CONSISTENT: @Thread.consistent lang e):
      future_certify e.
    Proof.
      eapply consistent_pf_consistent in CONSISTENT; eauto.
      eapply pf_consistent_pf_consistent_strong in CONSISTENT; eauto.
      ii. hexploit Memory.cap_exists.
      { eapply MEMORY. } i. des.
      exploit CONSISTENT; eauto.
      instantiate (1:=TimeMap.bot). i. des.
      eapply pred_steps_traced_step in STEPS0. des.
      eapply pred_steps_traced_step in STEPS1. des.

      hexploit traced_times_list_exists.
      { eapply traced_step_trans.
        - eapply STEPS.
        - eapply STEPS0. } i. des.
      hexploit (future_memory_map times CAP FUTURE); eauto. i. des.

      destruct e1, e2.
      hexploit traced_steps_map.
      { eapply mapping_map_lt_map_le; eauto. }
      { eapply map_ident_in_memory_bot; eauto. }
      { eapply mapping_map_lt_map_eq; eauto. }
      { eapply wf_time_mapped_mappable; eauto. }
      { eapply traced_step_trans; eauto. }
      { eauto. }
      { eauto. }
      { eauto. }
      { eapply Local.cap_wf; eauto. }
      { eapply WF. }
      { eauto. }
      { eapply Memory.cap_closed; eauto. }
      { eapply Memory.closed_timemap_bot. inv MEM. auto. }
      { eapply Memory.closed_timemap_bot.
        eapply Memory.cap_closed in MEMORY; eauto. inv MEMORY. auto. }
      { eapply map_ident_in_memory_local; eauto. }
      { eauto. }
      { eapply mapping_map_lt_collapsable_unwritable. eauto. }
      { eapply timemap_bot_map. eapply map_ident_in_memory_bot; eauto. }
      { refl. }
      i. des.
      hexploit no_sc_any_sc_traced.
      { eapply STEPS1. }
      { eauto. }
      { eauto. }
      { eauto. }
      { ii. eapply list_Forall2_in in IN; eauto. des.
        eapply List.in_app_or in IN0. des.
        + eapply List.Forall_forall in EVENTS; eauto. des.
          destruct a, e0. ss. inv EVENT; ss.
        + eapply List.Forall_forall in EVENTS0; eauto. des.
          destruct a, e0. ss. inv EVENT; ss. }
      i. des. eapply pred_steps_traced_step2 in STEPS2.
      - unguard. des; ss.
        + left. unfold Thread.steps_failure. esplits.
          * eapply thread_steps_pred_steps. eapply STEPS2.
          * econs 2. econs; eauto. econs. econs.
            inv LOCAL0. inv LOCAL1. destruct local0.
            eapply promise_consistent_mon.
            { eapply promise_consistent_map; eauto.
              - eapply mapping_map_lt_map_le; eauto.
              - eapply mapping_map_lt_map_eq; eauto. }
            { auto. }
            { refl. }
        + right. esplits.
          * eapply thread_steps_pred_steps. eapply STEPS2.
          * ss. inv LOCAL0. rewrite PROMISES in *.
            eapply bot_promises_map in PROMISES0. auto.
      - apply List.Forall_forall. ii.
        eapply list_Forall2_in in H; eauto. des. split.
        { instantiate (1:=fun _ => True). ss. }
        eapply List.in_app_or in IN. des.
        + eapply List.Forall_forall in EVENTS; eauto. des.
          destruct a, x. ss. inv EVENT; auto.
        + eapply List.Forall_forall in EVENTS0; eauto. des.
          destruct a, x. ss. inv EVENT; auto.
    Qed.

    Lemma future_consistent
          e sc' mem'
          (LOCAL: Local.wf e.(Thread.local) e.(Thread.memory))
          (MEMORY: Memory.closed e.(Thread.memory))
          (SC: Memory.closed_timemap e.(Thread.sc) e.(Thread.memory))
          (CONSISTENT: @Thread.consistent lang e)
          (SC_FUTURE: TimeMap.le e.(Thread.sc) sc')
          (MEM_FUTURE: Memory.future_weak e.(Thread.memory) mem')
          (LOCAL': Local.wf e.(Thread.local) mem')
          (MEMORY': Memory.closed mem')
          (SC': Memory.closed_timemap sc' mem'):
      Thread.consistent (Thread.mk lang e.(Thread.state) e.(Thread.local) sc' mem').
    Proof.
      ii. ss.
      eapply future_certify_exists; try exact CONSISTENT; eauto.
      - etrans; eauto. eapply Memory.cap_future_weak; eauto.
      - etrans; eauto.
        hexploit Memory.cap_closed_timemap; try exact SC'; eauto. i.
        hexploit Memory.max_concrete_timemap_spec; eauto.
      - eapply Local.cap_wf; eauto.
      - eapply Memory.max_concrete_timemap_closed; eauto.
      - eapply Memory.cap_closed; eauto.
    Qed.
  End FutureCertify.
End FutureCertify.
