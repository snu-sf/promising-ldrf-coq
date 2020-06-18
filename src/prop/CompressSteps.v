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
Require Import Mapping.
Require Import Pred.
Require Import Trace.
Require Import MemoryProps.

Set Implicit Arguments.


Module CompressSteps.
  Section CompressSteps.
    Variable (lang: language).

    Inductive spatial_mem (mem_src mem_tgt: Memory.t): Prop :=
    | spatial_mem_intro
        loc from to
        (SPACE: Time.lt (Memory.max_ts loc mem_tgt) from)
        (ADD: Memory.add mem_tgt loc from to Message.reserve mem_src)
    .

    Inductive spatial_thread (e_src e_tgt: Thread.t lang): Prop :=
    | spatial_thread_intro
        (STATE: e_src.(Thread.state) = e_tgt.(Thread.state))
        (LOCAL: e_src.(Thread.local) = e_tgt.(Thread.local))
        (SC: e_src.(Thread.sc) = e_tgt.(Thread.sc))
        (MEMORY: spatial_mem e_src.(Thread.memory) e_tgt.(Thread.memory))
    .

    Lemma spatial_memory_map mem_src mem_tgt times
          (SPATIAL: spatial_mem mem_src mem_tgt)
          (CLOSED: Memory.closed mem_tgt)
      :
        exists (f: Loc.t -> Time.t -> Time.t -> Prop),
          (<<IDENT: map_ident_in_memory f mem_tgt>>) /\
          (<<MAPLT: mapping_map_lt f>>) /\
          (<<MEMORY: memory_map f mem_tgt mem_src>>) /\
          (<<COMPLETE: forall loc to (IN: List.In to (times loc)),
              exists fto, (<<MAPPED: f loc to fto>>)>>).
    Proof.
      inv SPATIAL.
      hexploit shift_map_exists.
      { refl. }
      { eapply SPACE. }
      i. des.
      exists (fun loc' => if (Loc.eq_dec loc loc') then f else eq).
      assert (IDENT: map_ident_in_memory (fun loc' => if LocSet.Facts.eq_dec loc loc' then f else eq) mem_tgt).
      { ii. des_ifs. eapply SAME; eauto. } splits; ss.
      - ii. des_ifs. eapply MAPLT; eauto.
      - econs.
        + i. right. exists to0, from0, msg, msg. splits; auto.
          * des_ifs. eapply SAME.
            eapply Memory.max_ts_spec in GET. des. eauto.
          * eapply map_ident_in_memory_closed_message; eauto.
            inv CLOSED. eapply CLOSED0 in GET. des. auto.
          * refl.
          * eapply Memory.add_get1; eauto.
        + i. erewrite Memory.add_o in GET; eauto.
          destruct (loc_ts_eq_dec (loc0, fto) (loc, to)).
          { ss. des; clarify. right. ii. des_ifs.
            destruct (Time.le_lt_dec ts (Memory.max_ts loc mem_tgt)).
            - dup l. eapply SAME in l. replace fts with ts in *.
              + eapply TimeFacts.le_lt_lt; eauto.
              + destruct (Time.le_lt_dec ts fts).
                * destruct l1; auto.
                  eapply MAPLT in H; eauto.
                  exfalso. eapply Time.lt_strorder; eauto.
                * eapply MAPLT in l1; eauto.
                  exfalso. eapply Time.lt_strorder; eauto.
            - eapply BOUND in MAP; eauto. des. auto. }
          { guardH o. left. exists fto, ffrom, fto, ffrom. splits.
            - eapply IDENT. eapply Memory.max_ts_spec in GET. des; auto.
            - refl.
            - refl.
            - eapply IDENT. dup GET. eapply Memory.max_ts_spec in GET. des; auto.
              eapply Memory.get_ts in GET0. des; clarify.
              etrans; eauto. left. auto.
            - i. econs; eauto. }
      - i. des_ifs.
        + eapply COMPLETE in IN; eauto.
        + eauto.
    Qed.

    Lemma compress_steps_failure
          e1_src e1_tgt
          (THREAD1: spatial_thread e1_src e1_tgt)
          (WF1_SRC: Local.wf e1_src.(Thread.local) e1_src.(Thread.memory))
          (WF1_TGT: Local.wf e1_tgt.(Thread.local) e1_tgt.(Thread.memory))
          (SC1_SRC: Memory.closed_timemap e1_src.(Thread.sc) e1_src.(Thread.memory))
          (SC1_TGT: Memory.closed_timemap e1_tgt.(Thread.sc) e1_tgt.(Thread.memory))
          (MEM1_SRC: Memory.closed e1_src.(Thread.memory))
          (MEM1_TGT: Memory.closed e1_tgt.(Thread.memory))
          (STEPS_TGT: @Thread.steps_failure lang e1_tgt):
      Thread.steps_failure e1_src.
    Proof.
      inv THREAD1. destruct e1_src, e1_tgt. ss. clarify.
      unfold Thread.steps_failure in *. des.
      eapply pred_steps_thread_steps in STEPS.
      eapply pred_steps_trace_steps in STEPS. des.
      hexploit (trace_times_list_exists tr). i. des.
      hexploit (spatial_memory_map times MEMORY); eauto. i. des.
      destruct e2. hexploit trace_steps_map; try apply STEPS0; try apply MEMORY0; eauto.
      { eapply mapping_map_lt_map_le; eauto. }
      { eapply map_ident_in_memory_bot; eauto. }
      { eapply mapping_map_lt_map_eq; eauto. }
      { eapply wf_time_mapped_mappable; eauto. }
      { eapply map_ident_in_memory_local; eauto. }
      { eapply mapping_map_lt_collapsable_unwritable; eauto. }
      { eapply map_ident_in_memory_closed_timemap; eauto. }
      { refl. }
      i. des. inv FAILURE; inv STEP. inv LOCAL0. inv LOCAL1.
      esplits.
      - eapply thread_steps_pred_steps.
        eapply pred_steps_trace_steps2.
        + eapply STEPS.
        + instantiate (1:=fun _ => True). eapply List.Forall_forall. ii.
          eapply list_Forall2_in in H; eauto. des.
          eapply List.Forall_forall in EVENTS; try apply IN. destruct a, x.
          ss. des. split; auto. inv SAT; ss.
      - econs 2. econs; eauto. econs. econs.
        destruct lc2, flc1. inv LOCAL. ss.
        eapply promise_consistent_mon.
        + eapply promise_consistent_map.
          { eapply mapping_map_lt_map_le; eauto. }
          { eapply mapping_map_lt_map_eq; eauto. }
          { eapply TVIEW. }
          { eapply PROMISES. }
          { eapply CONSISTENT. }
        + eauto.
        + refl.
    Qed.

    Lemma compress_steps_fulfill
          e1_src e1_tgt
          e2_tgt
          (THREAD1: spatial_thread e1_src e1_tgt)
          (WF1_SRC: Local.wf e1_src.(Thread.local) e1_src.(Thread.memory))
          (WF1_TGT: Local.wf e1_tgt.(Thread.local) e1_tgt.(Thread.memory))
          (SC1_SRC: Memory.closed_timemap e1_src.(Thread.sc) e1_src.(Thread.memory))
          (SC1_TGT: Memory.closed_timemap e1_tgt.(Thread.sc) e1_tgt.(Thread.memory))
          (MEM1_SRC: Memory.closed e1_src.(Thread.memory))
          (MEM1_TGT: Memory.closed e1_tgt.(Thread.memory))
          (STEPS_TGT: rtc (@Thread.tau_step lang) e1_tgt e2_tgt)
          (PROMISES_TGT: e2_tgt.(Thread.local).(Local.promises) = Memory.bot):
      exists e2_src,
        <<STEPS_SRC: rtc (@Thread.tau_step lang) e1_src e2_src>> /\
                     <<PROMISES_SRC: e2_src.(Thread.local).(Local.promises) = Memory.bot>>.
    Proof.
      inv THREAD1. destruct e1_src, e1_tgt. ss. clarify.
      unfold Thread.steps_failure in *. des.
      eapply pred_steps_thread_steps in STEPS_TGT.
      eapply pred_steps_trace_steps in STEPS_TGT. des.
      hexploit (trace_times_list_exists tr). i. des.
      hexploit (spatial_memory_map times MEMORY); eauto. i. des.
      destruct e2_tgt. hexploit trace_steps_map; try apply STEPS; try apply MEMORY0; eauto.
      { eapply mapping_map_lt_map_le; eauto. }
      { eapply map_ident_in_memory_bot; eauto. }
      { eapply mapping_map_lt_map_eq; eauto. }
      { eapply wf_time_mapped_mappable; eauto. }
      { eapply map_ident_in_memory_local; eauto. }
      { eapply mapping_map_lt_collapsable_unwritable; eauto. }
      { eapply map_ident_in_memory_closed_timemap; eauto. }
      { refl. }
      i. des. esplits.
      - eapply thread_steps_pred_steps.
        eapply pred_steps_trace_steps2.
        + eapply STEPS0.
        + instantiate (1:=fun _ => True). eapply List.Forall_forall. ii.
          eapply list_Forall2_in in H; eauto. des.
          eapply List.Forall_forall in EVENTS; try apply IN. destruct a, x.
          ss. des. split; auto. inv SAT; ss.
      - ss. inv LOCAL. rewrite PROMISES_TGT in *.
        eapply bot_promises_map; eauto.
    Qed.
  End CompressSteps.
End CompressSteps.
