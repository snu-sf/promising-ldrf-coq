Require Import Omega.
Require Import Bool.
Require Import RelationClasses.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Loc.
From PromisingLib Require Import Language.

Require Import Event.
Require Import Time.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.

Require Import Trace.

Require Import OrdStep.
Require Import Stable.

Set Implicit Arguments.


Module RASimThread.
  Section RASimThread.
    Variable lang: language.
    Variable L: Loc.t -> bool.

    (* stable *)

    Inductive stable_thread (e: Thread.t lang): Prop :=
    | stable_thread_intro
        (NORMAL_TVIEW: Stable.normal_tview L e.(Thread.local).(Local.tview))
        (NORMAL_MEMORY: Stable.normal_memory L e.(Thread.memory))
        (STABLE_TVIEW: Stable.stable_tview L e.(Thread.memory) e.(Thread.local).(Local.tview))
        (STABLE_SC: Stable.stable_timemap L e.(Thread.memory) e.(Thread.sc))
        (STABLE_MEMORY: Stable.stable_memory L e.(Thread.memory))
    .

    Lemma future_stable_thread
          e sc' mem'
          (WF: Local.wf e.(Thread.local) e.(Thread.memory))
          (STABLE: stable_thread e)
          (SC: TimeMap.le e.(Thread.sc) sc')
          (MEM: Memory.future e.(Thread.memory) mem')
          (NORMAL_MEM: Stable.normal_memory L mem')
          (STABLE_SC: Stable.stable_timemap L mem' sc')
          (STABLE_MEM: Stable.stable_memory L mem'):
      stable_thread (Thread.mk lang e.(Thread.state) e.(Thread.local) sc' mem').
    Proof.
      destruct e, local. inv STABLE. inv WF. ss.
      econs; i; ss; eauto using Stable.future_stable_tview.
    Qed.


    (* sim *)

    Definition reserve_only (promises: Memory.t): Prop :=
      forall loc from to val released
        (LOC: L loc)
        (PROMISE: Memory.get loc to promises = Some (from, Message.concrete val released)),
        False.

    Inductive sim_tview (tview_src tview_tgt: TView.t): Prop :=
    | sim_tview_intro
        (REL: forall loc (LOC: ~ L loc),
            tview_src.(TView.rel) loc = tview_tgt.(TView.rel) loc)
        (CUR: tview_src.(TView.cur) = tview_tgt.(TView.cur))
        (ACQ: tview_src.(TView.acq) = tview_tgt.(TView.acq))
    .

    Definition rel_write (e: ThreadEvent.t): option (Loc.t * Time.t) :=
      match e with
      | ThreadEvent.write loc from to val released ord =>
        if Ordering.le Ordering.acqrel ord then Some (loc, to) else None
      | ThreadEvent.update loc tsr to valr valw releasedr releasedw ordr ordw =>
        if Ordering.le Ordering.acqrel ordw then Some (loc, to) else None
      | _ => None
      end.

    Inductive sim_local (tr: Trace.t lang) (lc_src lc_tgt: Local.t): Prop :=
    | sim_local_intro
        (TVIEW: sim_tview lc_src.(Local.tview) lc_tgt.(Local.tview))
        (PROMISES: lc_src.(Local.promises) = lc_tgt.(Local.promises))
        (RESERVE: reserve_only lc_src.(Local.promises))
        (REL_WRITES_NONE: forall loc to th e
                            (IN: List.In (th, e) tr)
                            (REL: rel_write e = Some (loc, to)),
            Memory.get loc to lc_src.(Local.promises) = None)
    .

    Inductive sim_message (loc: Loc.t): forall (msg_src msg_tgt: Message.t), Prop :=
    | sim_message_concrete
        val released_src released_tgt
        (RELEASED: if L loc then True else released_src = released_tgt):
        sim_message loc (Message.concrete val released_src) (Message.concrete val released_tgt)
    | sim_message_reserve:
        sim_message loc Message.reserve Message.reserve
    .

    Program Instance sim_message_Equivalence: forall loc, Equivalence (sim_message loc).
    Next Obligation.
      ii. destruct x; econs; eauto. des_ifs.
    Qed.
    Next Obligation.
      ii. inv H; econs; eauto. des_ifs.
    Qed.
    Next Obligation.
      ii. inv H; inv H0; ss; econs; eauto. des_ifs.
    Qed.

    Inductive sim_memory (tr: Trace.t lang) (mem_src mem_tgt: Memory.t): Prop :=
    | sim_memory_intro
        (SOUND: forall loc from to msg_src
                  (GET_SRC: Memory.get loc to mem_src = Some (from, msg_src)),
            exists msg_tgt,
              <<GET_TGT: Memory.get loc to mem_tgt = Some (from, msg_tgt)>> /\
              <<MSG: sim_message loc msg_src msg_tgt>>)
        (COMPLETE: forall loc from to msg_tgt
                     (GET_TGT: Memory.get loc to mem_tgt = Some (from, msg_tgt)),
            exists msg_src,
              <<GET_SRC: Memory.get loc to mem_src = Some (from, msg_src)>> /\
              <<MSG: sim_message loc msg_src msg_tgt>>)
        (REL_WRITES: forall loc to th e
                       (IN: List.In (th, e) tr)
                       (REL: rel_write e = Some (loc, to)),
            exists from msg,
              <<GET_SRC: Memory.get loc to mem_src = Some (from, msg)>> /\
              <<GET_TGT: Memory.get loc to mem_tgt = Some (from, msg)>>)
    .

    Inductive sim_thread (tr: Trace.t lang) (e_src e_tgt: Thread.t lang): Prop :=
    | sim_thread_intro
        (STABLE_SRC: stable_thread e_src)
        (STATE: e_src.(Thread.state) = e_tgt.(Thread.state))
        (LOCAL: sim_local tr e_src.(Thread.local) e_tgt.(Thread.local))
        (SC: e_src.(Thread.sc) = e_tgt.(Thread.sc))
        (MEMORY: sim_memory tr e_src.(Thread.memory) e_tgt.(Thread.memory))
    .

    Lemma sim_memory_closed_timemap
          tr mem_src mem_tgt tm
          (SIM: sim_memory tr mem_src mem_tgt)
          (CLOSED_TGT: Memory.closed_timemap tm mem_tgt):
      Memory.closed_timemap tm mem_src.
    Proof.
      inv SIM. ii.
      specialize (CLOSED_TGT loc). des.
      exploit COMPLETE; eauto. i. des. inv MSG.
      eauto.
    Qed.

    Lemma sim_memory_closed_view
          tr mem_src mem_tgt view
          (SIM: sim_memory tr mem_src mem_tgt)
          (CLOSED_TGT: Memory.closed_view view mem_tgt):
      Memory.closed_view view mem_src.
    Proof.
      inv CLOSED_TGT. econs; eauto using sim_memory_closed_timemap.
    Qed.

    Lemma sim_memory_closed_opt_view
          tr mem_src mem_tgt view
          (SIM: sim_memory tr mem_src mem_tgt)
          (CLOSED_TGT: Memory.closed_opt_view view mem_tgt):
      Memory.closed_opt_view view mem_src.
    Proof.
      inv CLOSED_TGT; eauto using sim_memory_closed_view.
    Qed.

    Lemma sim_memory_closed_message
          tr mem_src mem_tgt msg
          (SIM: sim_memory tr mem_src mem_tgt)
          (CLOSED_TGT: Memory.closed_message msg mem_tgt):
      Memory.closed_message msg mem_src.
    Proof.
      inv CLOSED_TGT; eauto using sim_memory_closed_opt_view.
    Qed.

    Lemma sim_memory_add
          tr mem1_src
          mem1_tgt loc from to msg mem2_tgt
          (SIM1: sim_memory tr mem1_src mem1_tgt)
          (ADD_TGT: Memory.add mem1_tgt loc from to msg mem2_tgt):
      exists mem2_src,
        <<ADD_SRC: Memory.add mem1_src loc from to msg mem2_src>> /\
        <<SIM2: sim_memory tr mem2_src mem2_tgt>>.
    Proof.
      inv SIM1.
      exploit (@Memory.add_exists mem1_src loc from to msg).
      { ii. inv LHS. inv RHS. ss.
        exploit SOUND; eauto. i. des.
        exploit Memory.add_get0; eauto. i. des.
        exploit Memory.add_get1; eauto. i.
        exploit Memory.get_ts; try exact GET0. i. des.
        { subst. timetac. }
        exploit Memory.get_ts; try exact x1. i. des.
        { subst. timetac. }
        exploit Memory.get_disjoint; [exact GET0|exact x1|..]. i. des.
        { subst. congr. }
        apply (x4 x); econs; eauto. }
      { inv ADD_TGT. inv ADD. ss. }
      { inv ADD_TGT. inv ADD. ss. }
      i. des.
      esplits; eauto. econs; i.
      - revert GET_SRC. erewrite Memory.add_o; eauto. condtac; ss.
        + i. des. inv GET_SRC.
          erewrite Memory.add_o; eauto. condtac; ss.
          esplits; eauto. refl.
        + i. erewrite Memory.add_o; eauto. condtac; ss. eauto.
      - revert GET_TGT. erewrite Memory.add_o; eauto. condtac; ss.
        + i. des. inv GET_TGT.
          erewrite Memory.add_o; eauto. condtac; ss.
          esplits; eauto. refl.
        + i. erewrite Memory.add_o; eauto. condtac; ss. eauto.
      - exploit REL_WRITES; eauto. i. des.
        erewrite Memory.add_o; eauto.
        erewrite (@Memory.add_o mem2_tgt); eauto.
        condtac; ss; eauto.
        des. subst. esplits; eauto.
    Qed.

    Lemma sim_memory_split
          tr mem1_src
          mem1_tgt loc ts1 ts2 ts3 msg2 msg3 mem2_tgt
          (SIM1: sim_memory tr mem1_src mem1_tgt)
          (LOC: L loc = false)
          (SPLIT_TGT: Memory.split mem1_tgt loc ts1 ts2 ts3 msg2 msg3 mem2_tgt):
      exists mem2_src,
        <<SPLIT_SRC: Memory.split mem1_src loc ts1 ts2 ts3 msg2 msg3 mem2_src>> /\
        <<SIM2: sim_memory tr mem2_src mem2_tgt>>.
    Proof.
      inv SIM1.
      exploit (@Memory.split_exists mem1_src loc ts1 ts2 ts3 msg2 msg3).
      { exploit Memory.split_get0; eauto. i. des.
        exploit COMPLETE; try exact GET0. i. des.
        inv MSG; ss. rewrite LOC in *. subst. ss. }
      { inv SPLIT_TGT. inv SPLIT. ss. }
      { inv SPLIT_TGT. inv SPLIT. ss. }
      { inv SPLIT_TGT. inv SPLIT. ss. }
      i. des.
      esplits; eauto. econs; i.
      - revert GET_SRC. erewrite Memory.split_o; eauto. repeat condtac; ss; i.
        + des. inv GET_SRC.
          erewrite Memory.split_o; eauto. repeat condtac; ss.
          esplits; eauto. refl.
        + guardH o. des. inv GET_SRC.
          erewrite Memory.split_o; eauto. repeat condtac; ss.
          esplits; eauto. refl.
        + erewrite Memory.split_o; eauto. repeat condtac; ss. eauto.
      - revert GET_TGT. erewrite Memory.split_o; eauto. repeat condtac; ss; i.
        + des. inv GET_TGT.
          erewrite Memory.split_o; eauto. repeat condtac; ss.
          esplits; eauto. refl.
        + guardH o. des. inv GET_TGT.
          erewrite Memory.split_o; eauto. repeat condtac; ss.
          esplits; eauto. refl.
        + erewrite Memory.split_o; eauto. repeat condtac; ss. eauto.
      - exploit REL_WRITES; eauto. i. des.
        erewrite Memory.split_o; eauto.
        erewrite (@Memory.split_o mem2_tgt); eauto.
        repeat condtac; ss; eauto.
        + des. subst. esplits; eauto.
        + guardH o. des. subst. esplits; eauto.
    Qed.

    Lemma sim_memory_lower
          tr mem1_src
          mem1_tgt loc from to msg1 msg2 mem2_tgt
          (SIM1: sim_memory tr mem1_src mem1_tgt)
          (LOC: L loc = false)
          (LOWER_TGT: Memory.lower mem1_tgt loc from to msg1 msg2 mem2_tgt):
      exists mem2_src,
        <<LOWER_SRC: Memory.lower mem1_src loc from to msg1 msg2 mem2_src>> /\
        <<SIM2: sim_memory tr mem2_src mem2_tgt>>.
    Proof.
      inv SIM1.
      exploit (@Memory.lower_exists mem1_src loc from to msg1 msg2).
      { exploit Memory.lower_get0; eauto. i. des.
        exploit COMPLETE; eauto. i. des. inv MSG; ss.
        rewrite LOC in *. subst. ss. }
      { inv LOWER_TGT. inv LOWER. ss. }
      { inv LOWER_TGT. inv LOWER. ss. }
      { inv LOWER_TGT. inv LOWER. ss. }
      i. des.
      esplits; eauto. econs; i.
      - revert GET_SRC. erewrite Memory.lower_o; eauto. condtac; ss.
        + i. des. inv GET_SRC.
          erewrite Memory.lower_o; eauto. condtac; ss.
          esplits; eauto. refl.
        + i. erewrite Memory.lower_o; eauto. condtac; ss. eauto.
      - revert GET_TGT. erewrite Memory.lower_o; eauto. condtac; ss.
        + i. des. inv GET_TGT.
          erewrite Memory.lower_o; eauto. condtac; ss.
          esplits; eauto. refl.
        + i. erewrite Memory.lower_o; eauto. condtac; ss. eauto.
      - exploit REL_WRITES; eauto. i. des.
        erewrite Memory.lower_o; eauto.
        erewrite (@Memory.lower_o mem2_tgt); eauto.
        condtac; ss; eauto.
        des. subst. esplits; eauto.
    Qed.

    Lemma sim_memory_remove
          tr mem1_src
          mem1_tgt loc from to msg mem2_tgt
          (SIM1: sim_memory tr mem1_src mem1_tgt)
          (LOC: L loc = false)
          (REL_WRITE: forall th e
                        (IN: List.In (th, e) tr)
                        (REL_WRITE: rel_write e = Some (loc, to)),
              False)
          (REMOVE_TGT: Memory.remove mem1_tgt loc from to msg mem2_tgt):
      exists mem2_src,
        <<REMOVE_SRC: Memory.remove mem1_src loc from to msg mem2_src>> /\
        <<SIM2: sim_memory tr mem2_src mem2_tgt>>.
    Proof.
      inv SIM1.
      exploit (@Memory.remove_exists mem1_src loc from to msg).
      { exploit Memory.remove_get0; eauto. i. des.
        exploit COMPLETE; eauto. i. des.
        inv MSG; ss. rewrite LOC in *. subst. ss. }
      i. des.
      esplits; eauto. econs; i.
      - revert GET_SRC. erewrite Memory.remove_o; eauto. condtac; ss.
        i. erewrite Memory.remove_o; eauto. condtac; ss. eauto.
      - revert GET_TGT. erewrite Memory.remove_o; eauto. condtac; ss.
        i. erewrite Memory.remove_o; eauto. condtac; ss. eauto.
      - exploit REL_WRITES; eauto. i. des.
        erewrite Memory.remove_o; eauto.
        erewrite (@Memory.remove_o mem2_tgt); eauto.
        condtac; ss; eauto.
        des. subst. exploit REL_WRITE; eauto. ss.
    Qed.


    (* race condition *)

    Definition ra_race (tr: Trace.t lang) (lc: Local.t) (loc: Loc.t) (to: Time.t) (ordr: Ordering.t): Prop :=
      <<LOC: L loc>> /\
      <<HIGHER: Time.lt (lc.(Local.tview).(TView.cur).(View.rlx) loc) to>> /\
      (<<ORDW: forall th e
                 (IN: List.In (th, e) tr)
                 (REL: rel_write e = Some (loc, to)),
          False>> \/
       <<ORDR: Ordering.le ordr Ordering.strong_relaxed>>).


    (* step *)

    (* Lemma promise_step *)
    (*       tr lc1_src mem1_src *)
    (*       lc1_tgt mem1_tgt loc from to msg lc2_tgt mem2_tgt kind *)
    (*       (LC1: sim_local tr lc1_src lc1_tgt) *)
    (*       (MEM1: sim_memory tr mem1_src mem1_tgt) *)
    (*       (WF1_SRC: Local.wf lc1_src mem1_src) *)
    (*       (WF1_TGT: Local.wf lc1_src mem1_tgt) *)
    (*       (STEP_TGT: Local.promise_step lc1_tgt mem1_tgt loc from to msg lc2_tgt mem2_tgt kind) *)
    (*       (RESERVE: L loc -> msg = Message.reserve): *)
    (*   exists lc2_src mem2_src, *)
    (*     <<STEP_SRC: Local.promise_step lc1_src mem1_src loc from to msg lc2_src mem2_src kind>> /\ *)
    (*     <<LC2: sim_local tr lc2_src lc2_tgt>> /\ *)
    (*     <<MEM2: sim_memory tr mem2_src mem2_tgt>>. *)
    (* Proof. *)
    (*   destruct (L loc) eqn:LOC. *)
    (*   { (* promise on L *) *)
    (*     rewrite RESERVE in *; ss. *)
    (*     inv LC1. inv MEM1. inv STEP_TGT. inv PROMISE. *)
    (*     - (* add *) *)
    (*       exploit (@Memory.add_exists mem1_src loc from to Message.reserve). *)
    (*       { ii. inv LHS. inv RHS. ss. *)
    (*         exploit SOUND; eauto. i. des. *)
    (*         exploit Memory.add_get0; try exact MEM. i. des. *)
    (*         exploit Memory.add_get1; try exact GET_TGT; eauto. i. *)
    (*         exploit Memory.get_ts; try exact GET0. i. des. *)
    (*         { subst. timetac. } *)
    (*         exploit Memory.get_ts; try exact x1. i. des. *)
    (*         { subst. timetac. } *)
    (*         exploit Memory.get_disjoint; [exact GET0|exact x1|..]. i. des. *)
    (*         { subst. congr. } *)
    (*         apply (x4 x); econs; ss. } *)
    (*       { inv MEM. inv ADD. ss. } *)
    (*       { econs. } *)
    (*       i. des. *)
    (*       exploit Memory.add_exists_le; try eapply WF1_SRC; eauto. i. des. *)
    (*       esplits. *)
    (*       + econs; [econs; eauto|..]; ss. *)
    (*       + econs; ss. *)
    (*         * rewrite PROMISES in *. *)
    (*           eapply Memory.add_inj; eauto. *)
    (*         * ii. revert PROMISE. *)
    (*           erewrite Memory.add_o; eauto. condtac; ss. eauto. *)
    (*         * i. erewrite Memory.add_o; eauto. condtac; ss; eauto. des. subst. *)
    (*           exploit REL_WRITES; eauto. i. des. *)
    (*           exploit Memory.add_get0; try exact MEM. i. des. congr. *)
    (*       + econs; i. *)
    (*         * revert GET_SRC. erewrite Memory.add_o; eauto. condtac; ss. *)
    (*           { i. des. inv GET_SRC. *)
    (*             exploit Memory.add_get0; try exact MEM. i. des. *)
    (*             esplits; eauto. econs. } *)
    (*           { i. erewrite Memory.add_o; eauto. condtac; ss; eauto. } *)
    (*         * revert GET_TGT. erewrite Memory.add_o; eauto. condtac; ss. *)
    (*           { i. des. inv GET_TGT. *)
    (*             exploit Memory.add_get0; try exact x0. i. des. *)
    (*             esplits; eauto. econs. } *)
    (*           { i. erewrite Memory.add_o; eauto. condtac; ss; eauto. } *)
    (*         * exploit REL_WRITES; eauto. i. des. *)
    (*           erewrite Memory.add_o; eauto. *)
    (*           erewrite (@Memory.add_o mem2_tgt); eauto. *)
    (*           condtac; ss; eauto. des. subst. *)
    (*           exploit Memory.add_get0; try exact MEM. i. des. congr. *)
    (*     - (* split *) *)
    (*       des. ss. *)
    (*     - (* lower *) *)
    (*       des. subst. inv MEM. inv LOWER. inv MSG_LE. *)
    (*     - (* cancel *) *)
    (*       rewrite <- PROMISES in *. *)
    (*       exploit Memory.remove_get0; try exact PROMISES0. i. des. *)
    (*       exploit Memory.remove_exists_le; try eapply WF1_SRC; eauto. i. des. *)
    (*       esplits. *)
    (*       + econs; [econs; eauto|..]; ss. *)
    (*       + econs; ss. *)
    (*         * ii. revert PROMISE. *)
    (*           erewrite Memory.remove_o; eauto. condtac; ss; eauto. *)
    (*         * i. erewrite Memory.remove_o; eauto. condtac; ss; eauto. *)
    (*       + econs; i. *)
    (*         * revert GET_SRC. erewrite Memory.remove_o; eauto. condtac; ss. i. *)
    (*           erewrite Memory.remove_o; eauto. condtac; ss. eauto. *)
    (*         * revert GET_TGT. erewrite Memory.remove_o; eauto. condtac; ss. i. *)
    (*           erewrite Memory.remove_o; eauto. condtac; ss. eauto. *)
    (*         * exploit REL_WRITES; eauto. i. des. *)
    (*           erewrite Memory.remove_o; eauto. *)
    (*           erewrite (@Memory.remove_o mem2_tgt); eauto. *)
    (*           condtac; ss; eauto. des. subst. *)
    (*           exploit REL_WRITES_NONE; eauto. i. *)
    (*           exploit Memory.remove_get0; try exact PROMISES0. i. des. congr. *)
    (*   } *)

    (*   (* promises on other loc *) *)
    (*   clear RESERVE. inv LC1. inv STEP_TGT. *)
    (*   rewrite <- PROMISES in *. inv PROMISE. *)
    (*   - (* add *) *)
    (*     exploit sim_memory_add; eauto. i. des. *)
    (*     inv MEM1. esplits. *)
    (*     + econs; [econs; eauto|..]; ss. *)
    (*       * i. subst. exploit SOUND; eauto. i. des. eauto. *)
    (*       * eapply sim_memory_closed_message; eauto. *)
    (*     + econs; ss. *)
    (*       * ii. revert PROMISE. *)
    (*         erewrite Memory.add_o; eauto. condtac; ss; eauto. *)
    (*         i. des. subst. congr. *)
    (*       * i. erewrite Memory.add_o; eauto. condtac; ss; eauto. *)
    (*         des. subst. exploit REL_WRITES; eauto. i. des. *)
    (*         exploit Memory.add_get0; try exact MEM. i. des. congr. *)
    (*     + ss. *)
    (*   - (* split *) *)
    (*     exploit sim_memory_split; eauto. i. des. *)
    (*     inv MEM1. esplits. *)
    (*     + econs; [econs; eauto|..]; ss. *)
    (*       eapply sim_memory_closed_message; eauto. *)
    (*     + econs; ss. *)
    (*       * ii. revert PROMISE. *)
    (*         erewrite Memory.split_o; eauto. repeat condtac; ss; eauto. *)
    (*         { i. des. subst. congr. } *)
    (*         { guardH o. i. des. subst. congr. } *)
    (*       * i. erewrite Memory.split_o; eauto. repeat condtac; ss; eauto. *)
    (*         { des. subst. exploit REL_WRITES; eauto. i. des. *)
    (*           exploit Memory.split_get0; try exact MEM. i. des. congr. } *)
    (*         { guardH o. des. subst. *)
    (*           exploit REL_WRITES_NONE; eauto. i. *)
    (*           exploit Memory.split_get0; try exact PROMISES0. i. des. congr. } *)
    (*     + ss. *)
    (*   - (* lower *) *)
    (*     exploit sim_memory_lower; eauto. i. des. *)
    (*     inv MEM1. esplits. *)
    (*     + econs; [econs; eauto|..]; ss. *)
    (*       eapply sim_memory_closed_message; eauto. *)
    (*     + econs; ss. *)
    (*       * ii. revert PROMISE. *)
    (*         erewrite Memory.lower_o; eauto. condtac; ss; eauto. *)
    (*         i. des. subst. congr. *)
    (*       * i. erewrite Memory.lower_o; eauto. condtac; ss; eauto. *)
    (*         des. subst. exploit REL_WRITES_NONE; eauto. i. *)
    (*         exploit Memory.lower_get0; try exact PROMISES0. i. des. congr. *)
    (*     + ss. *)
    (*   - (* cancel *) *)
    (*     exploit sim_memory_remove; eauto. *)
    (*     { i. exploit REL_WRITES_NONE; eauto. i. *)
    (*       exploit Memory.remove_get0; try exact PROMISES0. i. des. congr. } *)
    (*     i. des. *)
    (*     inv MEM1. esplits. *)
    (*     + econs; [econs; eauto|..]; ss. *)
    (*     + econs; ss. *)
    (*       * ii. revert PROMISE. *)
    (*         erewrite Memory.remove_o; eauto. condtac; ss; eauto. *)
    (*       * i. erewrite Memory.remove_o; eauto. condtac; ss; eauto. *)
    (*     + ss. *)
    (* Qed. *)

    (* Lemma read_step *)
    (*       tr lc1_src mem1_src *)
    (*       lc1_tgt mem1_tgt loc to val released_tgt ord lc2_tgt *)
    (*       (LC1: sim_local tr lc1_src lc1_tgt) *)
    (*       (MEM1: sim_memory tr mem1_src mem1_tgt) *)
    (*       (WF1_SRC: Local.wf lc1_src mem1_src) *)
    (*       (WF1_TGT: Local.wf lc1_src mem1_tgt) *)
    (*       (STEP_TGT: Local.read_step lc1_tgt mem1_tgt loc to val released_tgt ord lc2_tgt): *)
    (*   exists released_src lc2_src, *)
    (*     <<STEP_SRC: OrdLocal.read_step L Ordering.acqrel lc1_src mem1_src loc to val released_src ord lc2_src>> /\ *)
    (*     (<<LC2: sim_local tr lc2_src lc2_tgt>> \/ *)
    (*      <<RACE: ra_race tr lc1_src loc to ord>>). *)
    (* Proof. *)
    (*   destruct (L loc) eqn:LOC; cycle 1. *)
    (*   { (* read from other loc *) *)
    (*     inv LC1. inv TVIEW. inv MEM1. inv STEP_TGT. *)
    (*     exploit COMPLETE; eauto. i. des. inv MSG. *)
    (*     rewrite LOC in *. subst. *)
    (*     esplits. *)
    (*     { econs; eauto. econs; eauto. rewrite CUR, LOC in *. ss. } *)
    (*     left. rewrite LOC in *. econs; eauto; ss. *)
    (*     - econs; eauto; ss; congr. *)
    (*     - admit. *)
    (*     - admit. *)
    (*   } *)

    (*   (* read from L *) *)
    (*   inv LC1. inv TVIEW. inv MEM1. inv STEP_TGT. *)
    (*   exploit COMPLETE; eauto. i. des. inv MSG. clear RELEASED. *)
    (*   esplits. *)
    (*   { econs; eauto. econs; eauto. *)
    (*     rewrite CUR in *. inv READABLE. econs; eauto. i. *)
    (*     inv NORMAL_TGT. rewrite CUR0; ss. } *)
    (* Admitted. *)

    (* Lemma sim_thread_step *)
    (*       tr e1_src e1_tgt *)
    (*       pf e_tgt e2_tgt *)
    (*       (SIM1: sim_thread tr e1_src e1_tgt) *)
    (*       (WF1_SRC: Local.wf e1_src.(Thread.local) e1_src.(Thread.memory)) *)
    (*       (WF1_TGT: Local.wf e1_tgt.(Thread.local) e1_tgt.(Thread.memory)) *)
    (*       (SC1_SRC: Memory.closed_timemap e1_src.(Thread.sc) e1_src.(Thread.memory)) *)
    (*       (SC1_TGT: Memory.closed_timemap e1_tgt.(Thread.sc) e1_tgt.(Thread.memory)) *)
    (*       (MEM1_SRC: Memory.closed e1_src.(Thread.memory)) *)
    (*       (MEM1_TGT: Memory.closed e1_tgt.(Thread.memory)) *)
    (*       (STEP_TGT: Thread.step pf e_tgt e1_tgt e2_tgt) *)
    (*       (PROMISES_TGT: reserve_only e2_tgt.(Thread.local).(Local.promises)): *)
    (*   (True) \/ *)
    (*   (exists e_src e2_src, *)
    (*       <<STEP_SRC: Thread.step pf e_src e1_src e2_src>> /\ *)
    (*       <<SIM2: sim_thread ((e1_src, e_src) :: tr) e2_src e2_tgt>> /\ *)
    (*       <<EVENT: ThreadEvent.get_machine_event e_src = ThreadEvent.get_machine_event e_tgt>>). *)
    (* Proof. *)
    (* Admitted. *)
  End RASimThread.
End RASimThread.
