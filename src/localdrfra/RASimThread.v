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

Require Import MemoryMerge.
Require Import Trace.

Require Import OrdStep.
Require Import Stable.

Set Implicit Arguments.


Module ReleaseWrites.
  Definition t: Type := list (Loc.t * Time.t).
End ReleaseWrites.


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
        (REL: forall loc (LOC: L loc = false),
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

    Inductive sim_local (rels: ReleaseWrites.t) (lc_src lc_tgt: Local.t): Prop :=
    | sim_local_intro
        (TVIEW: sim_tview lc_src.(Local.tview) lc_tgt.(Local.tview))
        (PROMISES: lc_src.(Local.promises) = lc_tgt.(Local.promises))
        (RESERVE: reserve_only lc_src.(Local.promises))
        (REL_WRITES_NONE: forall loc to (IN: List.In (loc, to) rels),
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

    Inductive sim_memory (rels: ReleaseWrites.t) (mem_src mem_tgt: Memory.t): Prop :=
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
        (REL_WRITES: forall loc to (IN: List.In (loc, to) rels),
            exists from msg,
              <<GET_SRC: Memory.get loc to mem_src = Some (from, msg)>> /\
              <<GET_TGT: Memory.get loc to mem_tgt = Some (from, msg)>>)
    .

    Inductive sim_thread (rels: ReleaseWrites.t) (e_src e_tgt: Thread.t lang): Prop :=
    | sim_thread_intro
        (STATE: e_src.(Thread.state) = e_tgt.(Thread.state))
        (LOCAL: sim_local rels e_src.(Thread.local) e_tgt.(Thread.local))
        (SC: e_src.(Thread.sc) = e_tgt.(Thread.sc))
        (MEMORY: sim_memory rels e_src.(Thread.memory) e_tgt.(Thread.memory))
    .

    Lemma sim_tview_write_released
          tview_src tview_tgt
          sc loc to releasedm ord
          (SIM: sim_tview tview_src tview_tgt)
          (LOC: L loc = false):
      TView.write_released tview_src sc loc to releasedm ord =
      TView.write_released tview_tgt sc loc to releasedm ord.
    Proof.
      inv SIM. unfold TView.write_released. ss.
      condtac; ss.
      unfold LocFun.add. condtac; ss. condtac; ss.
      - rewrite CUR. ss.
      - rewrite REL; ss.
    Qed.

    Lemma sim_memory_closed_timemap
          rels mem_src mem_tgt tm
          (SIM: sim_memory rels mem_src mem_tgt)
          (CLOSED_TGT: Memory.closed_timemap tm mem_tgt):
      Memory.closed_timemap tm mem_src.
    Proof.
      inv SIM. ii.
      specialize (CLOSED_TGT loc). des.
      exploit COMPLETE; eauto. i. des. inv MSG.
      eauto.
    Qed.

    Lemma sim_memory_closed_view
          rels mem_src mem_tgt view
          (SIM: sim_memory rels mem_src mem_tgt)
          (CLOSED_TGT: Memory.closed_view view mem_tgt):
      Memory.closed_view view mem_src.
    Proof.
      inv CLOSED_TGT. econs; eauto using sim_memory_closed_timemap.
    Qed.

    Lemma sim_memory_closed_opt_view
          rels mem_src mem_tgt view
          (SIM: sim_memory rels mem_src mem_tgt)
          (CLOSED_TGT: Memory.closed_opt_view view mem_tgt):
      Memory.closed_opt_view view mem_src.
    Proof.
      inv CLOSED_TGT; eauto using sim_memory_closed_view.
    Qed.

    Lemma sim_memory_closed_message
          rels mem_src mem_tgt msg
          (SIM: sim_memory rels mem_src mem_tgt)
          (CLOSED_TGT: Memory.closed_message msg mem_tgt):
      Memory.closed_message msg mem_src.
    Proof.
      inv CLOSED_TGT; eauto using sim_memory_closed_opt_view.
    Qed.

    Lemma sim_memory_add
          rels mem1_src
          mem1_tgt loc from to msg mem2_tgt
          (SIM1: sim_memory rels mem1_src mem1_tgt)
          (ADD_TGT: Memory.add mem1_tgt loc from to msg mem2_tgt):
      exists mem2_src,
        <<ADD_SRC: Memory.add mem1_src loc from to msg mem2_src>> /\
        <<SIM2: sim_memory rels mem2_src mem2_tgt>>.
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
          rels mem1_src
          mem1_tgt loc ts1 ts2 ts3 msg2 msg3 mem2_tgt
          (SIM1: sim_memory rels mem1_src mem1_tgt)
          (LOC: L loc = false)
          (SPLIT_TGT: Memory.split mem1_tgt loc ts1 ts2 ts3 msg2 msg3 mem2_tgt):
      exists mem2_src,
        <<SPLIT_SRC: Memory.split mem1_src loc ts1 ts2 ts3 msg2 msg3 mem2_src>> /\
        <<SIM2: sim_memory rels mem2_src mem2_tgt>>.
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
          rels mem1_src
          mem1_tgt loc from to msg1 msg2 mem2_tgt
          (SIM1: sim_memory rels mem1_src mem1_tgt)
          (LOC: L loc = false)
          (LOWER_TGT: Memory.lower mem1_tgt loc from to msg1 msg2 mem2_tgt):
      exists mem2_src,
        <<LOWER_SRC: Memory.lower mem1_src loc from to msg1 msg2 mem2_src>> /\
        <<SIM2: sim_memory rels mem2_src mem2_tgt>>.
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
          rels mem1_src
          mem1_tgt loc from to msg mem2_tgt
          (SIM1: sim_memory rels mem1_src mem1_tgt)
          (LOC: L loc = false)
          (REL: ~ List.In (loc, to) rels)
          (REMOVE_TGT: Memory.remove mem1_tgt loc from to msg mem2_tgt):
      exists mem2_src,
        <<REMOVE_SRC: Memory.remove mem1_src loc from to msg mem2_src>> /\
        <<SIM2: sim_memory rels mem2_src mem2_tgt>>.
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
        des. subst. exploit REL; eauto. ss.
    Qed.


    (* race condition *)

    Definition ra_race (rels: ReleaseWrites.t) (tview: TView.t) (loc: Loc.t) (to: Time.t) (ordr: Ordering.t): Prop :=
      <<LOC: L loc>> /\
      <<HIGHER: Time.lt (tview.(TView.cur).(View.rlx) loc) to>> /\
      (<<ORDW: ~ List.In (loc, to) rels>> \/
       <<ORDR: Ordering.le ordr Ordering.strong_relaxed>>).


    (* step *)

    Lemma promise
          rels mem1_src
          promises1 mem1_tgt loc from to msg promises2 mem2_tgt kind
          (PROMISES1: reserve_only promises1)
          (REL1: forall loc to (IN: List.In (loc, to) rels),
              Memory.get loc to promises1 = None)
          (MEM1: sim_memory rels mem1_src mem1_tgt)
          (LE1_SRC: Memory.le promises1 mem1_src)
          (LE1_TGT: Memory.le promises1 mem1_tgt)
          (STEP_TGT: Memory.promise promises1 mem1_tgt loc from to msg promises2 mem2_tgt kind)
          (MSG: L loc -> msg = Message.reserve):
      exists mem2_src,
        <<STEP_SRC: Memory.promise promises1 mem1_src loc from to msg promises2 mem2_src kind>> /\
        <<PROMISES2: reserve_only promises2>> /\
        <<REL2: forall loc to (IN: List.In (loc, to) rels),
            Memory.get loc to promises2 = None>> /\
        <<MEM2: sim_memory rels mem2_src mem2_tgt>>.
    Proof.
      destruct (L loc) eqn:LOC.
      { (* promise on L *)
        rewrite MSG in *; ss.
        inv MEM1. inv STEP_TGT.
        - (* add *)
          exploit (@Memory.add_exists mem1_src loc from to Message.reserve).
          { ii. inv LHS. inv RHS. ss.
            exploit SOUND; eauto. i. des.
            exploit Memory.add_get0; try exact MEM. i. des.
            exploit Memory.add_get1; try exact GET_TGT; eauto. i.
            exploit Memory.get_ts; try exact GET0. i. des.
            { subst. timetac. }
            exploit Memory.get_ts; try exact x1. i. des.
            { subst. timetac. }
            exploit Memory.get_disjoint; [exact GET0|exact x1|..]. i. des.
            { subst. congr. }
            apply (x4 x); econs; ss. }
          { inv MEM. inv ADD. ss. }
          { econs. }
          i. des.
          exploit Memory.add_exists_le; try apply LE1_SRC; eauto. i. des.
          esplits.
          + econs; eauto. ss.
          + ii. revert PROMISE.
            erewrite Memory.add_o; eauto. condtac; ss. eauto.
          + i. erewrite Memory.add_o; eauto. condtac; ss; eauto. des. subst.
            exploit REL_WRITES; eauto. i. des.
            exploit Memory.add_get0; try exact MEM. i. des. congr.
          + econs; i.
            * revert GET_SRC. erewrite Memory.add_o; eauto. condtac; ss.
              { i. des. inv GET_SRC.
                exploit Memory.add_get0; try exact MEM. i. des.
                esplits; eauto. econs. }
              { i. erewrite Memory.add_o; eauto. condtac; ss; eauto. }
            * revert GET_TGT. erewrite Memory.add_o; eauto. condtac; ss.
              { i. des. inv GET_TGT.
                exploit Memory.add_get0; try exact x0. i. des.
                esplits; eauto. econs. }
              { i. erewrite Memory.add_o; eauto. condtac; ss; eauto. }
            * exploit REL_WRITES; eauto. i. des.
              erewrite Memory.add_o; eauto.
              erewrite (@Memory.add_o mem2_tgt); eauto.
              condtac; ss; eauto. des. subst.
              exploit Memory.add_get0; try exact MEM. i. des. congr.
        - (* split *)
          des. ss.
        - (* lower *)
          des. subst. inv MEM. inv LOWER. inv MSG_LE.
        - (* cancel *)
          exploit Memory.remove_get0; try exact PROMISES. i. des.
          exploit Memory.remove_exists_le; try apply LE1_SRC; eauto. i. des.
          esplits.
          + econs; eauto.
          + ii. revert PROMISE.
            erewrite Memory.remove_o; eauto. condtac; ss; eauto.
          + i. erewrite Memory.remove_o; eauto. condtac; ss; eauto.
          + econs; i.
            * revert GET_SRC. erewrite Memory.remove_o; eauto. condtac; ss. i.
              erewrite Memory.remove_o; eauto. condtac; ss. eauto.
            * revert GET_TGT. erewrite Memory.remove_o; eauto. condtac; ss. i.
              erewrite Memory.remove_o; eauto. condtac; ss. eauto.
            * exploit REL_WRITES; eauto. i. des.
              erewrite Memory.remove_o; eauto.
              erewrite (@Memory.remove_o mem2_tgt); eauto.
              condtac; ss; eauto. des. subst.
              exploit REL1; eauto. i.
              exploit Memory.remove_get0; try exact PROMISES. i. des. congr.
      }

      (* promises on other loc *)
      clear MSG. inv STEP_TGT.
      - (* add *)
        exploit sim_memory_add; eauto. i. des.
        inv MEM1. esplits.
        + econs; eauto.
          i. subst. exploit SOUND; eauto. i. des. eauto.
        + ii. revert PROMISE.
          erewrite Memory.add_o; eauto. condtac; ss; eauto.
          i. des. subst. congr.
        + i. erewrite Memory.add_o; eauto. condtac; ss; eauto.
          des. subst. exploit REL_WRITES; eauto. i. des.
          exploit Memory.add_get0; try exact MEM. i. des. congr.
        + ss.
      - (* split *)
        exploit sim_memory_split; eauto. i. des.
        inv MEM1. esplits.
        + econs; eauto.
        + ii. revert PROMISE.
          erewrite Memory.split_o; eauto. repeat condtac; ss; eauto.
          * i. des. subst. congr.
          * guardH o. i. des. subst. congr.
        + i. erewrite Memory.split_o; eauto. repeat condtac; ss; eauto.
          * des. subst. exploit REL_WRITES; eauto. i. des.
            exploit Memory.split_get0; try exact MEM. i. des. congr.
          * guardH o. des. subst.
            exploit REL1; eauto. i.
            exploit Memory.split_get0; try exact PROMISES. i. des. congr.
        + ss.
      - (* lower *)
        exploit sim_memory_lower; eauto. i. des.
        inv MEM1. esplits.
        + econs; eauto.
        + ii. revert PROMISE.
          erewrite Memory.lower_o; eauto. condtac; ss; eauto.
          i. des. subst. congr.
        + i. erewrite Memory.lower_o; eauto. condtac; ss; eauto.
          des. subst. exploit REL1; eauto. i.
          exploit Memory.lower_get0; try exact PROMISES. i. des. congr.
        + ss.
      - (* cancel *)
        exploit sim_memory_remove; eauto.
        { ii. exploit REL1; eauto. i.
          exploit Memory.remove_get0; try exact PROMISES. i. des. congr. }
        i. des.
        inv MEM1. esplits.
        + econs; eauto.
        + ii. revert PROMISE.
          erewrite Memory.remove_o; eauto. condtac; ss; eauto.
        + i. erewrite Memory.remove_o; eauto. condtac; ss; eauto.
        + ss.
    Qed.

    Lemma promise_step
          rels lc1_src mem1_src
          lc1_tgt mem1_tgt loc from to msg lc2_tgt mem2_tgt kind
          (LC1: sim_local rels lc1_src lc1_tgt)
          (MEM1: sim_memory rels mem1_src mem1_tgt)
          (WF1_SRC: Local.wf lc1_src mem1_src)
          (WF1_TGT: Local.wf lc1_src mem1_tgt)
          (STEP_TGT: Local.promise_step lc1_tgt mem1_tgt loc from to msg lc2_tgt mem2_tgt kind)
          (MSG: L loc -> msg = Message.reserve):
      exists lc2_src mem2_src,
        <<STEP_SRC: Local.promise_step lc1_src mem1_src loc from to msg lc2_src mem2_src kind>> /\
        <<LC2: sim_local rels lc2_src lc2_tgt>> /\
        <<MEM2: sim_memory rels mem2_src mem2_tgt>>.
    Proof.
      inv LC1. inv STEP_TGT. destruct lc1_src, lc1_tgt. ss. subst.
      exploit promise; try exact PROMISE; eauto.
      { apply WF1_SRC. }
      { apply WF1_TGT. }
      i. des. esplits; try exact MEM2.
      - econs; eauto.
        eapply sim_memory_closed_message; eauto.
      - econs; eauto.
    Qed.

    Lemma read_step_loc
          rels lc1_src mem1_src
          lc1_tgt mem1_tgt loc to val released_tgt ord lc2_tgt
          (LC1: sim_local rels lc1_src lc1_tgt)
          (MEM1: sim_memory rels mem1_src mem1_tgt)
          (NORMAL_TVIEW1_SRC: Stable.normal_tview L lc1_src.(Local.tview))
          (NORMAL_TVIEW1_TGT: Stable.normal_tview L lc1_tgt.(Local.tview))
          (STABLE_TVIEW1_SRC: Stable.stable_tview L mem1_src lc1_src.(Local.tview))
          (STABLE_TVIEW1_TGT: Stable.stable_tview L mem1_tgt lc1_tgt.(Local.tview))
          (WF1_SRC: Local.wf lc1_src mem1_src)
          (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
          (LOC: L loc)
          (STEP_TGT: Local.read_step lc1_tgt mem1_tgt loc to val released_tgt ord lc2_tgt):
      exists released_src lc2_src,
        <<STEP_SRC: OrdLocal.read_step L Ordering.acqrel lc1_src mem1_src loc to val released_src ord lc2_src>> /\
        (<<LC2: sim_local rels lc2_src lc2_tgt>> \/
         <<RACE: ra_race rels lc1_src.(Local.tview) loc to ord>>).
    Proof.
      inv LC1. inv TVIEW. inv MEM1. inv STEP_TGT.
      exploit COMPLETE; eauto. i. des. inv MSG. clear RELEASED.
      inv READABLE. dup NORMAL_TVIEW1_SRC. inv NORMAL_TVIEW1_SRC0.
      rewrite <- CUR, <- CUR0 in *; ss. clear RLX.
      esplits.
      { do 3 (econs; eauto). rewrite <- CUR0; ss. }
      inv PLN; cycle 1.
      { (* read from cur view *)
        inv H. left. econs; ss. rewrite LOC.
        erewrite Stable.stable_tview_read_tview; eauto; try apply WF1_SRC.
        rewrite CUR in *.
        erewrite Stable.stable_tview_read_tview; eauto; try apply WF1_TGT.
        econs; eauto.
      }
      destruct (classic (List.In (loc, to) rels)); cycle 1.
      { (* non release write *)
        right. unfold ra_race. auto.
      }
      destruct (Ordering.le ord Ordering.strong_relaxed) eqn:ORDR.
      { (* non acquire read *)
        right. unfold ra_race. auto.
      }

      (* RA synchronized *)
      left. econs; ss. rewrite LOC.
      exploit REL_WRITES; eauto. i. des.
      rewrite GET_SRC0, GET_TGT in *. inv GET_SRC. inv GET.
      econs; ss.
      - replace (Ordering.join ord Ordering.acqrel) with ord by (destruct ord; ss).
        condtac; try by (destruct ord; ss).
        rewrite CUR. refl.
      - replace (Ordering.join ord Ordering.acqrel) with ord by (destruct ord; ss).
        condtac; try by (destruct ord; ss).
        rewrite ACQ. refl.
    Qed.

    Lemma read_step_other
          rels lc1_src mem1_src
          lc1_tgt mem1_tgt loc to val released_tgt ord lc2_tgt
          (LC1: sim_local rels lc1_src lc1_tgt)
          (MEM1: sim_memory rels mem1_src mem1_tgt)
          (NORMAL_TVIEW1_SRC: Stable.normal_tview L lc1_src.(Local.tview))
          (NORMAL_TVIEW1_TGT: Stable.normal_tview L lc1_tgt.(Local.tview))
          (STABLE_TVIEW1_SRC: Stable.stable_tview L mem1_src lc1_src.(Local.tview))
          (STABLE_TVIEW1_TGT: Stable.stable_tview L mem1_tgt lc1_tgt.(Local.tview))
          (WF1_SRC: Local.wf lc1_src mem1_src)
          (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
          (LOC: L loc = false)
          (STEP_TGT: Local.read_step lc1_tgt mem1_tgt loc to val released_tgt ord lc2_tgt):
      exists released_src lc2_src,
        <<STEP_SRC: OrdLocal.read_step L Ordering.acqrel lc1_src mem1_src loc to val released_src ord lc2_src>> /\
        <<LC2: sim_local rels lc2_src lc2_tgt>>.
    Proof.
      inv LC1. inv TVIEW. inv MEM1. inv STEP_TGT.
      exploit COMPLETE; eauto. i. des. inv MSG.
      rewrite LOC in *. subst.
      esplits.
      { econs; eauto. econs; eauto. rewrite CUR, LOC in *. ss. }
      rewrite LOC in *. econs; eauto; ss.
      econs; eauto; ss; congr.
    Qed.

    Lemma write_step_loc
          rels lc1_src mem1_src releasedm_src
          lc1_tgt sc1 mem1_tgt loc from to val releasedm_tgt released_tgt ord lc2_tgt sc2 mem2_tgt kind
          (LC1: sim_local rels lc1_src lc1_tgt)
          (MEM1: sim_memory rels mem1_src mem1_tgt)
          (NORMAL_TVIEW1_SRC: Stable.normal_tview L lc1_src.(Local.tview))
          (NORMAL_TVIEW1_TGT: Stable.normal_tview L lc1_tgt.(Local.tview))
          (STABLE_TVIEW1_SRC: Stable.stable_tview L mem1_src lc1_src.(Local.tview))
          (STABLE_TVIEW1_TGT: Stable.stable_tview L mem1_tgt lc1_tgt.(Local.tview))
          (WF1_SRC: Local.wf lc1_src mem1_src)
          (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
          (RELEASEDM_SRC: View.opt_wf releasedm_src)
          (RELEASEDM_TGT: View.opt_wf releasedm_tgt)
          (RELEASEDM_LE: Time.le (releasedm_src.(View.unwrap).(View.rlx) loc) to)
          (LOC: L loc)
          (RELEASEDM: __guard__ (releasedm_src = releasedm_tgt \/
                                (View.opt_le releasedm_src (Some lc1_src.(Local.tview).(TView.cur)) /\
                                 View.opt_le releasedm_tgt (Some lc1_tgt.(Local.tview).(TView.cur)))))
          (STEP_TGT: Local.write_step lc1_tgt sc1 mem1_tgt loc from to val releasedm_tgt released_tgt ord
                                      lc2_tgt sc2 mem2_tgt kind):
      exists rels' released_src lc2_src mem2_src,
        <<STEP_SRC: OrdLocal.write_step L Ordering.acqrel
                                        lc1_src sc1 mem1_src loc from to val releasedm_src released_src ord
                                        lc2_src sc2 mem2_src kind>> /\
        <<REL_WRITES: rels' = if Ordering.le Ordering.acqrel ord then (loc, to) :: rels else rels>> /\
        <<LC2: sim_local rels' lc2_src lc2_tgt>> /\
        <<MEM2: sim_memory rels' mem2_src mem2_tgt>>.
    Proof.
      destruct (Ordering.le Ordering.acqrel ord) eqn:ORD.
      { (* release write *)
        destruct lc1_src, lc1_tgt. inv LC1. ss. subst.
        inv STEP_TGT. inv WRITE. inv PROMISE; ss.
        - exploit (@Memory.add_exists
                     mem1_src loc from to
                     (Message.concrete val (TView.write_released tview sc1 loc to releasedm_src ord))).
          { ii. inv MEM1.
            exploit SOUND; eauto. i. des.
            exploit Memory.add_get1; try exact GET_TGT; eauto. i.
            exploit Memory.add_get0; try exact MEM. i. des.
            exploit Memory.get_disjoint; [exact x1|exact GET0|..]. i. des; eauto.
            subst. congr. }
          { inv MEM. inv ADD. ss. }
          { econs. eapply TViewFacts.write_future0; eauto. apply WF1_SRC. }
          i. des.
          exploit Memory.add_exists_le; try exact x0; try eapply WF1_SRC. i. des. ss.
          exploit Memory.add_get0; try exact x1. i. des.
          exploit Memory.remove_exists; try exact GET0. i. des.
          esplits.
          + econs.
            { replace (Ordering.join ord Ordering.acqrel) with ord; [condtac; ss|].
              destruct ord; ss. }
            econs; ss.
            * inv TVIEW. rewrite CUR. ss.
            * econs; eauto. econs; eauto.
              { econs. inv TS.
                unfold TView.write_released.
                repeat (condtac; ss); try apply Time.bot_spec.
                unfold LocFun.add. condtac; ss.
                unfold TimeMap.join, TimeMap.singleton, LocFun.add, LocFun.find. condtac; ss.
                apply Time.join_spec; ss.
                apply Time.join_spec; try refl.
                inv TVIEW. rewrite CUR. inv WRITABLE. econs. ss.
              }
              { i. inv MEM1. exploit SOUND; try exact GET1. i. des. eauto. }
          + ss.
          + econs; ss.
            * inv TVIEW. econs; ss; try congr. i.
              rewrite ORD. unfold LocFun.add. condtac; ss.
              { subst. rewrite LOC0 in *. ss. }
              { unfold LocFun.find. rewrite REL; ss. }
            * exploit MemoryMerge.add_remove; try exact PROMISES; eauto. i. subst.
              exploit MemoryMerge.add_remove; try exact x1; eauto.
            * ii. revert PROMISE.
              erewrite Memory.remove_o; eauto. condtac; ss.
              erewrite Memory.add_o; eauto. condtac; ss. eauto.
            * exploit MemoryMerge.add_remove; try exact x1; eauto. i. subst.
              des; eauto. inv IN.
              exploit Memory.add_get0; try exact x1. i. des. ss.
          + inv MEM1. econs; i.
            * erewrite Memory.add_o; eauto.
              revert GET_SRC. erewrite Memory.add_o; eauto.
              condtac; ss; eauto. i. des. inv GET_SRC.
              esplits; eauto. econs. condtac; ss.
            * erewrite Memory.add_o; eauto.
              revert GET_TGT. erewrite Memory.add_o; eauto.
              condtac; ss; eauto. i. des. inv GET_TGT.
              esplits; eauto. econs. condtac; ss.
            * inv IN.
              { inv H. exploit Memory.add_get0; try exact MEM. i. des.
                exploit Memory.add_get0; try exact x0. i. des.
                esplits; eauto.
                cut (TView.write_released tview0 sc1 loc0 to0 releasedm_tgt ord =
                     TView.write_released tview sc1 loc0 to0 releasedm_src ord); try congr.
                unfold TView.write_released. condtac; ss. condtac; ss.
                unfold LocFun.add. condtac; ss.
                inv TVIEW. rewrite CUR.
                unguard. des; try congr.
                move RELEASEDM at bottom.
                move RELEASEDM0 at bottom.
                rewrite (@View.le_join_r releasedm_src.(View.unwrap)); cycle 1.
                { etrans; [|apply View.join_l].
                  destruct releasedm_src; try apply View.bot_spec. ss.
                  rewrite <- CUR. inv RELEASEDM. ss. }
                rewrite (@View.le_join_r releasedm_tgt.(View.unwrap)); ss.
                etrans; [|apply View.join_l].
                destruct releasedm_tgt; try apply View.bot_spec. ss.
                inv RELEASEDM0. ss.
              }
              { exploit REL_WRITES; eauto. i. des.
                exploit Memory.add_get1; try exact GET_SRC; eauto. i.
                exploit Memory.add_get1; try exact GET_TGT; eauto. }
        - clear RESERVE0.
          exploit (@Memory.split_exists
                     promises0 loc from to ts3
                     (Message.concrete val (TView.write_released tview sc1 loc to releasedm_src ord)) msg3).
          { exploit Memory.split_get0; try exact PROMISES. i. des. ss. }
          { inv MEM. inv SPLIT. ss. }
          { inv MEM. inv SPLIT. ss. }
          { econs. eapply TViewFacts.write_future0; eauto. apply WF1_SRC. }
          i. des.
          exploit Memory.split_exists_le; try exact x0; try eapply WF1_SRC. i. des.
          exploit Memory.split_get0; try exact x0. i. des.
          exploit Memory.remove_exists; try exact GET1. i. des.
          esplits.
          + econs.
            { replace (Ordering.join ord Ordering.acqrel) with ord; [condtac; ss|].
              destruct ord; ss. }
            econs; ss.
            * inv TVIEW. rewrite CUR. ss.
            * econs; eauto. econs; eauto.
              econs. inv TS.
              unfold TView.write_released.
              repeat (condtac; ss); try apply Time.bot_spec.
              unfold LocFun.add. condtac; ss.
              unfold TimeMap.join, TimeMap.singleton, LocFun.add, LocFun.find. condtac; ss.
              apply Time.join_spec; ss.
              apply Time.join_spec; try refl.
              inv TVIEW. rewrite CUR. inv WRITABLE. econs. ss.
          + ss.
          + econs; ss.
            * inv TVIEW. econs; ss; try congr. i.
              rewrite ORD. unfold LocFun.add. condtac; ss.
              { subst. rewrite LOC0 in *. ss. }
              { unfold LocFun.find. rewrite REL; ss. }
            * apply Memory.ext. i.
              erewrite Memory.remove_o; eauto.
              erewrite (@Memory.remove_o promises2); try exact REMOVE.
              condtac; ss. guardH o.
              erewrite Memory.split_o; eauto.
              erewrite (@Memory.split_o promises1); try exact PROMISES.
              repeat condtac; ss.
            * ii. revert PROMISE.
              erewrite Memory.remove_o; eauto. condtac; ss.
              erewrite Memory.split_o; eauto. repeat condtac; ss; eauto.
              guardH o. guardH o0. i. des. inv PROMISE.
              exploit Memory.split_get0; try exact PROMISES. i. des. eauto.
            * i. des.
              { inv IN. exploit Memory.remove_get0; try exact x2. i. des. ss. }
              { erewrite Memory.remove_o; eauto. condtac; ss. guardH o.
                erewrite Memory.split_o; eauto. repeat condtac; ss; eauto.
                des; subst; ss.
                exploit Memory.split_get0; try exact PROMISES. i. des.
                exploit REL_WRITES_NONE; eauto. i. congr. }
          + inv MEM1. econs; i.
            * erewrite Memory.split_o; eauto.
              revert GET_SRC. erewrite Memory.split_o; eauto.
              repeat condtac; ss; eauto; i.
              { des. subst. inv GET_SRC.
                esplits; eauto. econs. condtac; ss. }
              { guardH o. des. subst. inv GET_SRC.
                esplits; eauto. refl. }
            * erewrite Memory.split_o; eauto.
              revert GET_TGT. erewrite Memory.split_o; eauto.
              repeat condtac; ss; eauto; i.
              { des. subst. inv GET_TGT.
                esplits; eauto. econs. condtac; ss. }
              { guardH o. des. subst. inv GET_TGT.
                esplits; eauto. refl. }
            * inv IN.
              { inv H. exploit Memory.split_get0; try exact MEM. i. des.
                exploit Memory.split_get0; try exact x1. i. des.
                esplits; eauto.
                cut (TView.write_released tview0 sc1 loc0 to0 releasedm_tgt ord =
                     TView.write_released tview sc1 loc0 to0 releasedm_src ord); try congr.
                unfold TView.write_released. condtac; ss. condtac; ss.
                unfold LocFun.add. condtac; ss.
                inv TVIEW. rewrite CUR.
                unguard. des; try congr.
                move RELEASEDM at bottom.
                move RELEASEDM0 at bottom.
                rewrite (@View.le_join_r releasedm_src.(View.unwrap)); cycle 1.
                { etrans; [|apply View.join_l].
                  destruct releasedm_src; try apply View.bot_spec. ss.
                  rewrite <- CUR. inv RELEASEDM. ss. }
                rewrite (@View.le_join_r releasedm_tgt.(View.unwrap)); ss.
                etrans; [|apply View.join_l].
                destruct releasedm_tgt; try apply View.bot_spec. ss.
                inv RELEASEDM0. ss.
              }
              { exploit REL_WRITES; eauto. i. des.
                erewrite Memory.split_o; eauto.
                erewrite (@Memory.split_o mem2_tgt); eauto.
                repeat condtac; ss; eauto.
                - des. subst.
                  exploit Memory.split_get0; try exact MEM. i. des. congr.
                - guardH o. des. subst. esplits; eauto.
              }
        - des. subst.
          exploit Memory.lower_get0; try exact PROMISES. i. des.
          exploit RESERVE; eauto. ss.
      }

      (* relaxed write *)
      destruct lc1_src, lc1_tgt. inv LC1. ss. subst.
      inv STEP_TGT. inv WRITE. inv PROMISE; ss.
      - exploit (@Memory.add_exists
                   mem1_src loc from to
                   (Message.concrete val (TView.write_released tview sc1 loc to releasedm_src Ordering.acqrel))).
        { ii. inv MEM1.
          exploit SOUND; eauto. i. des.
          exploit Memory.add_get1; try exact GET_TGT; eauto. i.
          exploit Memory.add_get0; try exact MEM. i. des.
          exploit Memory.get_disjoint; [exact x1|exact GET0|..]. i. des; eauto.
          subst. congr. }
        { inv MEM. inv ADD. ss. }
        { econs. eapply TViewFacts.write_future0; eauto. apply WF1_SRC. }
        i. des.
        exploit Memory.add_exists_le; try exact x0; try eapply WF1_SRC. i. des. ss.
        exploit Memory.add_get0; try exact x1. i. des.
        exploit Memory.remove_exists; try exact GET0. i. des.
        esplits.
        + econs.
          { instantiate (1 := Ordering.acqrel).
            condtac; ss. destruct ord; ss. }
          econs; ss.
          * inv TVIEW. rewrite CUR. inv WRITABLE. econs. ss.
          * econs; eauto. econs; eauto.
            { econs. inv TS.
              unfold TView.write_released. repeat (condtac; ss).
              unfold LocFun.add. condtac; ss.
              unfold TimeMap.join, TimeMap.singleton, LocFun.add, LocFun.find. condtac; ss.
              apply Time.join_spec; ss.
              apply Time.join_spec; try refl.
              inv TVIEW. rewrite CUR. inv WRITABLE. econs. ss.
            }
            { i. inv MEM1. exploit SOUND; try exact GET1. i. des. eauto. }
          * ii. destruct msg; ss. exploit RESERVE; eauto. ss.
        + ss.
        + econs; ss.
          * inv TVIEW. econs; ss; try congr. i.
            rewrite ORD. condtac; ss.
            unfold LocFun.add. condtac; ss.
            { subst. rewrite LOC0 in *. ss. }
            { unfold LocFun.find. rewrite REL; ss. }
          * exploit MemoryMerge.add_remove; try exact PROMISES; eauto. i. subst.
            exploit MemoryMerge.add_remove; try exact x1; eauto.
          * ii. revert PROMISE.
            erewrite Memory.remove_o; eauto. condtac; ss.
            erewrite Memory.add_o; eauto. condtac; ss. eauto.
          * exploit MemoryMerge.add_remove; try exact x1; eauto.
            i. subst. des; eauto. 
        + inv MEM1. econs; i.
          * erewrite Memory.add_o; eauto.
            revert GET_SRC. erewrite Memory.add_o; eauto.
            condtac; ss; eauto. i. des. inv GET_SRC.
            esplits; eauto. econs. condtac; ss.
          * erewrite Memory.add_o; eauto.
            revert GET_TGT. erewrite Memory.add_o; eauto.
            condtac; ss; eauto. i. des. inv GET_TGT.
            esplits; eauto. econs. condtac; ss.
          *  exploit REL_WRITES; eauto. i. des.
             exploit Memory.add_get1; try exact GET_SRC; eauto. i.
             exploit Memory.add_get1; try exact GET_TGT; eauto.
      - clear RESERVE0.
        exploit (@Memory.split_exists
                   promises0 loc from to ts3
                   (Message.concrete val (TView.write_released tview sc1 loc to releasedm_src Ordering.acqrel)) msg3).
        { exploit Memory.split_get0; try exact PROMISES. i. des. ss. }
        { inv MEM. inv SPLIT. ss. }
        { inv MEM. inv SPLIT. ss. }
        { econs. eapply TViewFacts.write_future0; eauto. apply WF1_SRC. }
        i. des.
        exploit Memory.split_exists_le; try exact x0; try eapply WF1_SRC. i. des.
        exploit Memory.split_get0; try exact x0. i. des.
        exploit Memory.remove_exists; try exact GET1. i. des.
        esplits.
        + econs.
          { instantiate (1 := Ordering.acqrel).
            condtac; ss. destruct ord; ss. }
          econs; ss.
          * inv TVIEW. rewrite CUR. inv WRITABLE. econs. ss.
          * econs; eauto. econs; eauto.
            econs. inv TS.
            unfold TView.write_released. repeat (condtac; ss).
            unfold LocFun.add. condtac; ss.
            unfold TimeMap.join, TimeMap.singleton, LocFun.add, LocFun.find. condtac; ss.
            apply Time.join_spec; ss.
            apply Time.join_spec; try refl.
            inv TVIEW. rewrite CUR. inv WRITABLE. econs. ss.
          * ii. destruct msg; ss. exploit RESERVE; eauto. ss.
        + ss.
        + econs; ss.
          * inv TVIEW. econs; ss; try congr. i.
            rewrite ORD. unfold LocFun.add. condtac; ss.
            { subst. rewrite LOC0 in *. ss. }
            { unfold LocFun.find. rewrite REL; ss. }
          * apply Memory.ext. i.
            erewrite Memory.remove_o; eauto.
            erewrite (@Memory.remove_o promises2); try exact REMOVE.
            condtac; ss. guardH o.
            erewrite Memory.split_o; eauto.
            erewrite (@Memory.split_o promises1); try exact PROMISES.
            repeat condtac; ss.
          * ii. revert PROMISE.
            erewrite Memory.remove_o; eauto. condtac; ss.
            erewrite Memory.split_o; eauto. repeat condtac; ss; eauto.
            guardH o. guardH o0. i. des. inv PROMISE.
            exploit Memory.split_get0; try exact PROMISES. i. des. eauto.
          * i. des.
            erewrite Memory.remove_o; eauto. condtac; ss. guardH o.
            erewrite Memory.split_o; eauto. repeat condtac; ss; eauto.
            des; subst; ss.
            exploit Memory.split_get0; try exact PROMISES. i. des.
            exploit REL_WRITES_NONE; eauto. i. congr.
        + inv MEM1. econs; i.
          * erewrite Memory.split_o; eauto.
            revert GET_SRC. erewrite Memory.split_o; eauto.
            repeat condtac; ss; eauto; i.
            { des. subst. inv GET_SRC.
              esplits; eauto. econs. condtac; ss. }
            { guardH o. des. subst. inv GET_SRC.
              esplits; eauto. refl. }
          * erewrite Memory.split_o; eauto.
            revert GET_TGT. erewrite Memory.split_o; eauto.
            repeat condtac; ss; eauto; i.
            { des. subst. inv GET_TGT.
              esplits; eauto. econs. condtac; ss. }
            { guardH o. des. subst. inv GET_TGT.
              esplits; eauto. refl. }
          * exploit REL_WRITES; eauto. i. des.
            erewrite Memory.split_o; eauto.
            erewrite (@Memory.split_o mem2_tgt); eauto.
            repeat condtac; ss; eauto.
            { des. subst.
              exploit Memory.split_get0; try exact MEM. i. des. congr. }
            { guardH o. des. subst. esplits; eauto. }
      - des. subst.
        exploit Memory.lower_get0; try exact PROMISES. i. des.
        exploit RESERVE; eauto. ss.
    Qed.

    Lemma write_step_other
          rels lc1_src mem1_src
          lc1_tgt sc1 mem1_tgt loc from to val releasedm released_tgt ord lc2_tgt sc2 mem2_tgt kind
          (LC1: sim_local rels lc1_src lc1_tgt)
          (MEM1: sim_memory rels mem1_src mem1_tgt)
          (NORMAL_TVIEW1_SRC: normal_tview L lc1_src.(Local.tview))
          (NORMAL_TVIEW1_TGT: normal_tview L lc1_tgt.(Local.tview))
          (STABLE_TVIEW1_SRC: stable_tview L mem1_src lc1_src.(Local.tview))
          (STABLE_TVIEW1_TGT: stable_tview L mem1_tgt lc1_tgt.(Local.tview))
          (WF1_SRC: Local.wf lc1_src mem1_src)
          (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
          (LOC: L loc = false)
          (STEP_TGT: Local.write_step lc1_tgt sc1 mem1_tgt loc from to val releasedm released_tgt ord
                                      lc2_tgt sc2 mem2_tgt kind):
      exists rels' released_src lc2_src mem2_src,
        <<STEP_SRC: OrdLocal.write_step L Ordering.acqrel
                                        lc1_src sc1 mem1_src loc from to val releasedm released_src ord
                                        lc2_src sc2 mem2_src kind>> /\
        <<REL_WRITES: rels' = if Ordering.le Ordering.acqrel ord then (loc, to) :: rels else rels>> /\
        <<LC2: sim_local rels' lc2_src lc2_tgt>> /\
        <<MEM2: sim_memory rels' mem2_src mem2_tgt>>.
    Proof.
      destruct lc1_src, lc1_tgt.
      inv LC1. inv STEP_TGT. inv WRITE. ss. subst.
      exploit promise; try exact PROMISE; eauto.
      { apply WF1_SRC. }
      { apply WF1_TGT. }
      { rewrite LOC in *. ss. }
      i. des. esplits.
      - econs; [rewrite LOC; ss|].
        econs; ss.
        { inv TVIEW. rewrite CUR. ss. }
        erewrite sim_tview_write_released; eauto.
      - ss.
      - econs; ss.
        + inv TVIEW. econs; ss; try congr.
          i. unfold LocFun.add. condtac; ss; eauto. subst.
          condtac; try congr. rewrite REL; ss.
        + ii. revert PROMISE0.
          erewrite Memory.remove_o; eauto. condtac; ss. guardH o.
          inv PROMISE; ss.
          * erewrite Memory.add_o; eauto. condtac; ss; eauto.
          * exploit Memory.split_get0; try exact PROMISES. i. des. eauto.
          * exploit Memory.lower_get0; try exact PROMISES. i. des. eauto.
        + cut (forall loc to (IN: List.In (loc, to) rels), Memory.get loc to promises2 = None).
          { condtac; ss; eauto.
            i. des; eauto. inv IN.
            exploit Memory.remove_get0; try exact REMOVE. i. des. ss. }
          i. erewrite Memory.remove_o; eauto. condtac; ss. guardH o.
          inv PROMISE; ss.
          * erewrite Memory.add_o; eauto. condtac; ss; eauto.
          * exploit Memory.split_get0; try exact PROMISES. i. des. eauto.
          * exploit Memory.lower_get0; try exact PROMISES. i. des. eauto.
      - condtac; ss.
        inv MEM2. econs; ss.
        i. des; eauto. inv IN.
        exploit Memory.promise_get0; try exact PROMISE.
        { inv PROMISE; ss. }
        i. des.
        exploit Memory.promise_get0; try exact STEP_SRC.
        { inv STEP_SRC; ss. }
        i. des.
        esplits; eauto.
    Qed.

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
