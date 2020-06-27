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

Require Import OrdStep.
Require Import RARace.
Require Import Stable.

Set Implicit Arguments.


Module PFtoRASimThread.
  Section PFtoRASimThread.
    Variable lang: language.
    Variable L: Loc.t -> bool.

    (* stable *)

    Inductive normal_thread (e: Thread.t lang): Prop :=
    | normal_thread_intro
        (NORMAL_TVIEW: Stable.normal_tview L e.(Thread.local).(Local.tview))
        (NORMAL_MEMORY: Stable.normal_memory L e.(Thread.memory))
    .
    Hint Constructors normal_thread.

    Inductive stable_thread (rels: ReleaseWrites.t) (e: Thread.t lang): Prop :=
    | stable_thread_intro
        (STABLE_TVIEW: Stable.stable_tview L e.(Thread.memory) e.(Thread.local).(Local.tview))
        (STABLE_SC: Stable.stable_timemap L e.(Thread.memory) e.(Thread.sc))
        (STABLE_MEMORY: Stable.stable_memory L rels e.(Thread.memory))
    .
    Hint Constructors stable_thread.

    Lemma future_normal_thread
          e sc' mem'
          (NORMAL: normal_thread e)
          (NORMAL_MEM: Stable.normal_memory L mem'):
      normal_thread (Thread.mk lang e.(Thread.state) e.(Thread.local) sc' mem').
    Proof.
      inv NORMAL. econs; ss.
    Qed.

    Lemma future_stable_thread
          rels e sc' mem'
          (WF: Local.wf e.(Thread.local) e.(Thread.memory))
          (STABLE: stable_thread rels e)
          (SC: TimeMap.le e.(Thread.sc) sc')
          (MEM: Memory.future e.(Thread.memory) mem')
          (STABLE_SC: Stable.stable_timemap L mem' sc')
          (STABLE_MEM: Stable.stable_memory L rels mem'):
      stable_thread rels (Thread.mk lang e.(Thread.state) e.(Thread.local) sc' mem').
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
        (REL: forall loc, if L loc
                     then View.le (tview_tgt.(TView.rel) loc) (tview_src.(TView.rel) loc)
                     else tview_src.(TView.rel) loc = tview_tgt.(TView.rel) loc)
        (CUR: tview_src.(TView.cur) = tview_tgt.(TView.cur))
        (ACQ: tview_src.(TView.acq) = tview_tgt.(TView.acq))
    .

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
        (RELEASED: if L loc then View.opt_le released_tgt released_src else released_src = released_tgt):
        sim_message loc (Message.concrete val released_src) (Message.concrete val released_tgt)
    | sim_message_reserve:
        sim_message loc Message.reserve Message.reserve
    .

    Program Instance sim_message_PreOrder: forall loc, PreOrder (sim_message loc).
    Next Obligation.
      ii. destruct x; econs; eauto. des_ifs. refl.
    Qed.
    Next Obligation.
      ii. inv H; inv H0; ss; econs; eauto. des_ifs. etrans; eauto.
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
            exists from val released,
              <<GET_SRC: Memory.get loc to mem_src = Some (from, Message.concrete val (Some released))>> /\
              <<GET_TGT: Memory.get loc to mem_tgt = Some (from, Message.concrete val (Some released))>>)
    .

    Inductive sim_statelocal (rels: ReleaseWrites.t):
      forall (sl_src sl_tgt: {lang : language & Language.state lang} * Local.t), Prop :=
    | sim_statelocal_intro
        lang st lc_src lc_tgt
        (LOCAL: sim_local rels lc_src lc_tgt):
        sim_statelocal rels (existT _ lang st, lc_src) (existT _ lang st, lc_tgt)
    .
    Hint Constructors sim_statelocal.

    Inductive sim_thread (rels: ReleaseWrites.t) (e_src e_tgt: Thread.t lang): Prop :=
    | sim_thread_intro
        (STATE: e_src.(Thread.state) = e_tgt.(Thread.state))
        (LOCAL: sim_local rels e_src.(Thread.local) e_tgt.(Thread.local))
        (SC: e_src.(Thread.sc) = e_tgt.(Thread.sc))
        (MEMORY: sim_memory rels e_src.(Thread.memory) e_tgt.(Thread.memory))
    .
    Hint Constructors sim_thread.


    Lemma sim_tview_write_released
          tview_src tview_tgt
          sc loc to releasedm ord
          (SIM: sim_tview tview_src tview_tgt)
          (LOC: ~ L loc):
      TView.write_released tview_src sc loc to releasedm ord =
      TView.write_released tview_tgt sc loc to releasedm ord.
    Proof.
      inv SIM. unfold TView.write_released. ss.
      condtac; ss.
      unfold LocFun.add. condtac; ss. condtac; ss.
      - rewrite CUR. ss.
      - specialize (REL loc). des_ifs. rewrite REL. ss.
    Qed.

    Lemma sim_local_promise_consistent
          rels lc_src lc_tgt
          (SIM: sim_local rels lc_src lc_tgt)
          (CONS: Local.promise_consistent lc_tgt):
      Local.promise_consistent lc_src.
    Proof.
      inv SIM. inv TVIEW. ii.
      rewrite PROMISES, CUR in *. eauto.
    Qed.

    Lemma sim_memory_closed_timemap_src
          rels mem_src mem_tgt tm
          (SIM: sim_memory rels mem_src mem_tgt)
          (CLOSED: Memory.closed_timemap tm mem_src):
      Memory.closed_timemap tm mem_tgt.
    Proof.
      inv SIM. ii.
      specialize (CLOSED loc). des.
      exploit SOUND; eauto. i. des. inv MSG.
      eauto.
    Qed.

    Lemma sim_memory_closed_view_src
          rels mem_src mem_tgt view
          (SIM: sim_memory rels mem_src mem_tgt)
          (CLOSED: Memory.closed_view view mem_src):
      Memory.closed_view view mem_tgt.
    Proof.
      inv CLOSED. econs; eauto using sim_memory_closed_timemap_src.
    Qed.

    Lemma sim_memory_closed_opt_view_src
          rels mem_src mem_tgt view
          (SIM: sim_memory rels mem_src mem_tgt)
          (CLOSED: Memory.closed_opt_view view mem_src):
      Memory.closed_opt_view view mem_tgt.
    Proof.
      inv CLOSED; eauto using sim_memory_closed_view_src.
    Qed.

    Lemma sim_memory_closed_message_src
          rels mem_src mem_tgt msg
          (SIM: sim_memory rels mem_src mem_tgt)
          (CLOSED: Memory.closed_message msg mem_src):
      Memory.closed_message msg mem_tgt.
    Proof.
      inv CLOSED; eauto using sim_memory_closed_opt_view_src.
    Qed.

    Lemma sim_memory_closed_timemap_tgt
          rels mem_src mem_tgt tm
          (SIM: sim_memory rels mem_src mem_tgt)
          (CLOSED: Memory.closed_timemap tm mem_tgt):
      Memory.closed_timemap tm mem_src.
    Proof.
      inv SIM. ii.
      specialize (CLOSED loc). des.
      exploit COMPLETE; eauto. i. des. inv MSG.
      eauto.
    Qed.

    Lemma sim_memory_closed_view_tgt
          rels mem_src mem_tgt view
          (SIM: sim_memory rels mem_src mem_tgt)
          (CLOSED: Memory.closed_view view mem_tgt):
      Memory.closed_view view mem_src.
    Proof.
      inv CLOSED. econs; eauto using sim_memory_closed_timemap_tgt.
    Qed.

    Lemma sim_memory_closed_opt_view_tgt
          rels mem_src mem_tgt view
          (SIM: sim_memory rels mem_src mem_tgt)
          (CLOSED: Memory.closed_opt_view view mem_tgt):
      Memory.closed_opt_view view mem_src.
    Proof.
      inv CLOSED; eauto using sim_memory_closed_view_tgt.
    Qed.

    Lemma sim_memory_closed_message_tgt
          rels mem_src mem_tgt msg
          (SIM: sim_memory rels mem_src mem_tgt)
          (CLOSED: Memory.closed_message msg mem_tgt):
      Memory.closed_message msg mem_src.
    Proof.
      inv CLOSED; eauto using sim_memory_closed_opt_view_tgt.
    Qed.

    Lemma sim_memory_add
          rels mem1_src
          mem1_tgt loc from to msg mem2_tgt
          (SIM1: sim_memory rels mem1_src mem1_tgt)
          (RELS: ~ List.In (loc, to) rels)
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
        des. subst. ss.
    Qed.

    Lemma sim_memory_split
          rels mem1_src
          mem1_tgt loc ts1 ts2 ts3 msg2 msg3 mem2_tgt
          (SIM1: sim_memory rels mem1_src mem1_tgt)
          (LOC: ~ L loc)
          (RELS: ~ List.In (loc, ts3) rels)
          (SPLIT_TGT: Memory.split mem1_tgt loc ts1 ts2 ts3 msg2 msg3 mem2_tgt):
      exists mem2_src,
        <<SPLIT_SRC: Memory.split mem1_src loc ts1 ts2 ts3 msg2 msg3 mem2_src>> /\
        <<SIM2: sim_memory rels mem2_src mem2_tgt>>.
    Proof.
      inv SIM1.
      exploit (@Memory.split_exists mem1_src loc ts1 ts2 ts3 msg2 msg3).
      { exploit Memory.split_get0; eauto. i. des.
        exploit COMPLETE; try exact GET0. i. des.
        inv MSG; ss. des_ifs; ss. }
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
        + des. subst. exploit REL_WRITES; eauto. i. des.
          exploit Memory.split_get0; try exact x0. i. des. congr.
        + guardH o. des. subst. ss.
    Qed.

    Lemma sim_memory_lower
          rels mem1_src
          mem1_tgt loc from to msg1 msg2 mem2_tgt
          (SIM1: sim_memory rels mem1_src mem1_tgt)
          (LOC: ~ L loc)
          (RELS: ~ List.In (loc, to) rels)
          (LOWER_TGT: Memory.lower mem1_tgt loc from to msg1 msg2 mem2_tgt):
      exists mem2_src,
        <<LOWER_SRC: Memory.lower mem1_src loc from to msg1 msg2 mem2_src>> /\
        <<SIM2: sim_memory rels mem2_src mem2_tgt>>.
    Proof.
      inv SIM1.
      exploit (@Memory.lower_exists mem1_src loc from to msg1 msg2).
      { exploit Memory.lower_get0; eauto. i. des.
        exploit COMPLETE; eauto. i. des. inv MSG; ss.
        des_ifs; ss. }
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
        des. subst. ss.
    Qed.

    Lemma sim_memory_remove
          rels mem1_src
          mem1_tgt loc from to msg mem2_tgt
          (SIM1: sim_memory rels mem1_src mem1_tgt)
          (LOC: ~ L loc)
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
        inv MSG; ss. des_ifs; ss. }
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

    Lemma sim_memory_get_tgt
          rels mem_src mem_tgt
          loc from to val released_tgt
          (SIM: sim_memory rels mem_src mem_tgt)
          (GET_TGT: Memory.get loc to mem_tgt = Some (from, Message.concrete val released_tgt)):
      exists released_src,
        (<<GET_SRC: Memory.get loc to mem_src = Some (from, Message.concrete val released_src)>>) /\
        (<<RELEASED: View.opt_le released_tgt released_src>>).
    Proof.
      inv SIM. exploit COMPLETE; eauto. i. des. inv MSG.
      esplits; eauto. des_ifs; ss. refl.
    Qed.

    Lemma sim_memory_stable_view
          rels mem_src mem_tgt view
          (SIM: sim_memory rels mem_src mem_tgt)
          (STABLE_SRC: Stable.stable_view L mem_src view):
      Stable.stable_view L mem_tgt view.
    Proof.
      ii. exploit sim_memory_get_tgt; eauto. i. des. inv RELEASED.
      etrans; eauto.
    Qed.

    Lemma sim_memory_stable_tview
          rels tview_src tview_tgt mem_src mem_tgt
          (TVIEW: sim_tview tview_src tview_tgt)
          (MEM: sim_memory rels mem_src mem_tgt)
          (STABLE_SRC: Stable.stable_tview L mem_src tview_src):
      Stable.stable_tview L mem_tgt tview_tgt.
    Proof.
      destruct tview_src, tview_tgt. inv TVIEW. ss. subst.
      inv STABLE_SRC. econs; eauto using sim_memory_stable_view; ss. i.
      specialize (REL loc). des_ifs.
      rewrite <- REL. eapply sim_memory_stable_view; eauto.
      apply REL0. congr.
    Qed.

    Lemma sim_memory_stable_memory
          rels mem_src mem_tgt
          (SIM: sim_memory rels mem_src mem_tgt)
          (STABLE_SRC: Stable.stable_memory L rels mem_src):
      Stable.stable_memory L rels mem_tgt.
    Proof.
      dup SIM. inv SIM0. unfold Stable.stable_memory. i. des.
      - exploit COMPLETE; try exact GET. i. des. inv MSG. des_ifs.
        eapply sim_memory_stable_view; eauto.
        eapply STABLE_SRC; eauto. left. congr.
      - exploit REL_WRITES; eauto. i. des.
        rewrite GET_TGT in *. inv GET.
        eauto using sim_memory_stable_view; eauto.
    Qed.

    Lemma sim_thread_stable
          rels e_src e_tgt
          (SIM: sim_thread rels e_src e_tgt)
          (STABLE_SRC: stable_thread rels e_src):
      stable_thread rels e_tgt.
    Proof.
      destruct e_src, e_tgt. inv SIM. inv STABLE_SRC. ss. subst.
      inv LOCAL. econs; ss; eauto.
      - eapply sim_memory_stable_tview; eauto.
      - eapply sim_memory_stable_view; eauto.
      - eapply sim_memory_stable_memory; eauto.
    Qed.

    Lemma sim_release_writes_wf
          rels lc_src lc_tgt mem_src mem_tgt
          (LC: sim_local rels lc_src lc_tgt)
          (MEM: sim_memory rels mem_src mem_tgt):
      <<RELS_WF_SRC: ReleaseWrites.wf rels lc_src.(Local.promises) mem_src>> /\
      <<RELS_WF_TGT: ReleaseWrites.wf rels lc_tgt.(Local.promises) mem_tgt>>.
    Proof.
      inv LC. inv MEM. split; ii.
      - exploit REL_WRITES; eauto. i. des. esplits; eauto.
      - rewrite <- PROMISES.
        exploit REL_WRITES; eauto. i. des. esplits; eauto.
    Qed.


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
        exploit sim_memory_add; eauto.
        { inv MEM1. ii. exploit REL_WRITES; eauto. i. des.
          exploit Memory.add_get0; eauto. i. des. congr. }
        i. des.
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
        exploit sim_memory_split; eauto; try congr.
        { ii. exploit REL1; eauto. i.
          exploit Memory.split_get0; try exact PROMISES. i. des. congr. }
        i. des.
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
        exploit sim_memory_lower; eauto; try congr.
        { ii. exploit REL1; eauto. i.
          exploit Memory.lower_get0; try exact PROMISES. i. des. congr. }
        i. des.
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
        exploit sim_memory_remove; eauto; try congr.
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
          (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
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
        eapply sim_memory_closed_message_tgt; eauto.
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
          (NORMAL_MEM1_SRC: Stable.normal_memory L mem1_src)
          (NORMAL_MEM1_TGT: Stable.normal_memory L mem1_tgt)
          (STABLE_MEM1_SRC: Stable.stable_memory L rels mem1_src)
          (WF1_SRC: Local.wf lc1_src mem1_src)
          (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
          (MEM1_SRC: Memory.closed mem1_src)
          (MEM1_TGT: Memory.closed mem1_tgt)
          (LOC: L loc)
          (STEP_TGT: Local.read_step lc1_tgt mem1_tgt loc to val released_tgt ord lc2_tgt):
      exists released_src lc2_src,
        <<STEP_SRC: OrdLocal.read_step L Ordering.acqrel lc1_src mem1_src loc to val released_src ord lc2_src>> /\
        __guard__ (
            (<<LC2: sim_local rels lc2_src lc2_tgt>>) /\
            (<<RELEASED_SRC: View.opt_le released_src (Some lc2_src.(Local.tview).(TView.cur))>>) /\
            (<<RELEASED_TGT: View.opt_le released_tgt (Some lc2_tgt.(Local.tview).(TView.cur))>>) /\
            (<<NORMAL_TVIEW1_SRC: Stable.normal_tview L lc2_src.(Local.tview)>>) /\
            (<<NORMAL_TVIEW1_TGT: Stable.normal_tview L lc2_tgt.(Local.tview)>>) /\
            (<<STABLE_TVIEW1_SRC: Stable.stable_tview L mem1_src lc2_src.(Local.tview)>>)
            \/
            (<<RACE: RAThread.ra_race L rels lc1_src.(Local.tview) loc to ord>>)).
    Proof.
      exploit sim_memory_stable_tview; eauto; try apply LC1. intro STABLE_TVIEW1_TGT.
      hexploit sim_memory_stable_memory; eauto. intro STABLE_MEM1_TGT.
      inv LC1. inv TVIEW. inv MEM1.
      dup STEP_TGT. inv STEP_TGT.
      exploit COMPLETE; eauto. i. des. inv MSG. clear RELEASED.
      inv READABLE. dup NORMAL_TVIEW1_SRC. inv NORMAL_TVIEW1_SRC0.
      rewrite <- CUR, <- CUR0 in *; ss. clear RLX.
      assert (exists released_src lc2_src,
                 <<STEP_SRC: OrdLocal.read_step L Ordering.acqrel lc1_src mem1_src loc to val released_src ord lc2_src>>).
      { esplits. do 3 (econs; eauto). rewrite <- CUR0; ss. }
      i. des. esplits; eauto.
      dup STEP_SRC. inv STEP_SRC0. inv STEP. ss.
      rewrite GET0 in *. inv GET_SRC.
      inv PLN; cycle 1.
      { (* read from cur view *)
        inv H. left. splits; ss.
        - econs; ss. rewrite LOC.
          erewrite Stable.stable_tview_read_tview; eauto; try apply WF1_SRC.
          rewrite CUR in *.
          erewrite Stable.stable_tview_read_tview; eauto; try apply WF1_TGT.
          econs; eauto.
        - destruct released_src; ss. econs.
          inv STABLE_TVIEW1_SRC. exploit CUR1; eauto. i.
          etrans; eauto.
          do 2 (etrans; [|apply View.join_l]).
          refl.
        - destruct released_tgt; ss. econs.
          inv STABLE_TVIEW1_TGT.
          rewrite <- CUR in *. exploit CUR1; eauto. i.
          etrans; eauto.
          do 2 (etrans; [|apply View.join_l]).
          refl.
        - rewrite LOC.
          erewrite Stable.stable_tview_read_tview; eauto; try apply WF1_SRC.
        - rewrite CUR in *.
          erewrite Stable.stable_tview_read_tview; eauto; try apply WF1_TGT.
        - rewrite LOC.
          erewrite Stable.stable_tview_read_tview; eauto; try apply WF1_SRC.
      }
      destruct (classic (List.In (loc, to) rels)); cycle 1.
      { (* non release write *)
        right. unfold RAThread.ra_race. auto.
      }
      destruct (Ordering.le ord Ordering.strong_relaxed) eqn:ORDR.
      { (* non acquire read *)
        right. unfold RAThread.ra_race. auto.
      }

      (* RA synchronized *)
      inv STEP_SRC. exploit Stable.read_step_loc_ra; try eapply STEP; eauto.
      { ii. split; eauto. exploit REL_WRITES; eauto. i. des. eauto. }
      { rewrite LOC. destruct ord; ss. }
      i. des.
      left. splits; ss.
      - econs; ss. rewrite LOC.
        exploit REL_WRITES; eauto. i. des.
        rewrite GET_SRC, GET_TGT in *. inv GET0. inv GET.
        econs; ss.
        + replace (Ordering.join ord Ordering.acqrel) with ord by (destruct ord; ss).
          condtac; try by (destruct ord; ss).
          rewrite CUR. refl.
        + replace (Ordering.join ord Ordering.acqrel) with ord by (destruct ord; ss).
          condtac; try by (destruct ord; ss).
          rewrite ACQ. refl.
      - repeat (condtac; ss); try by (destruct ord; ss).
        destruct released_src; ss. econs.
        etrans; [|eapply View.join_r]. refl.
      - repeat (condtac; ss); try by (destruct ord; ss).
        destruct released_tgt; ss. econs.
        etrans; [|eapply View.join_r]. refl.
      - exploit Stable.read_step_loc_ra; try apply STEP_TGT0; eauto.
        { ii. rewrite <- PROMISES. split; eauto.
          exploit REL_WRITES; eauto. i. des. eauto. }
        { destruct ord; ss. }
        i. des. ss.
    Qed.

    Lemma read_step_other_aux
          rels lc1_src mem1_src
          lc1_tgt mem1_tgt loc to val released ord lc2_tgt
          (LC1: sim_local rels lc1_src lc1_tgt)
          (MEM1: sim_memory rels mem1_src mem1_tgt)
          (LOC: L loc = false)
          (STEP_TGT: Local.read_step lc1_tgt mem1_tgt loc to val released ord lc2_tgt):
      exists lc2_src,
        (<<STEP_SRC: OrdLocal.read_step L Ordering.acqrel lc1_src mem1_src loc to val released ord lc2_src>>) /\
        (<<LC2: sim_local rels lc2_src lc2_tgt>>).
    Proof.
      inv LC1. inv TVIEW. inv MEM1. inv STEP_TGT.
      exploit COMPLETE; eauto. i. des. inv MSG.
      rewrite LOC in *. subst.
      esplits.
      - econs; eauto. econs; eauto. rewrite CUR, LOC in *. ss.
      - rewrite LOC in *. econs; eauto; ss.
        econs; eauto; ss; congr.
    Qed.

    Lemma read_step_other
          rels lc1_src mem1_src
          lc1_tgt mem1_tgt loc to val released ord lc2_tgt
          (LC1: sim_local rels lc1_src lc1_tgt)
          (MEM1: sim_memory rels mem1_src mem1_tgt)
          (NORMAL_TVIEW1_SRC: Stable.normal_tview L lc1_src.(Local.tview))
          (NORMAL_TVIEW1_TGT: Stable.normal_tview L lc1_tgt.(Local.tview))
          (STABLE_TVIEW1_SRC: Stable.stable_tview L mem1_src lc1_src.(Local.tview))
          (NORMAL_MEM1_SRC: Stable.normal_memory L mem1_src)
          (NORMAL_MEM1_TGT: Stable.normal_memory L mem1_tgt)
          (STABLE_MEM1_SRC: Stable.stable_memory L rels mem1_src)
          (WF1_SRC: Local.wf lc1_src mem1_src)
          (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
          (MEM1_SRC: Memory.closed mem1_src)
          (MEM1_TGT: Memory.closed mem1_tgt)
          (LOC: L loc = false)
          (STEP_TGT: Local.read_step lc1_tgt mem1_tgt loc to val released ord lc2_tgt):
      exists lc2_src,
        (<<STEP_SRC: OrdLocal.read_step L Ordering.acqrel lc1_src mem1_src loc to val released ord lc2_src>>) /\
        (<<LC2: sim_local rels lc2_src lc2_tgt>>) /\
        (<<NORMAL_TVIEW1_SRC: Stable.normal_tview L lc2_src.(Local.tview)>>) /\
        (<<NORMAL_TVIEW1_TGT: Stable.normal_tview L lc2_tgt.(Local.tview)>>) /\
        (<<STABLE_TVIEW1_SRC: Stable.stable_tview L mem1_src lc2_src.(Local.tview)>>).
    Proof.
      exploit sim_release_writes_wf; eauto. i. des.
      exploit sim_memory_stable_tview; try eapply LC1; eauto. intro STABLE_TVIEW1_TGT.
      hexploit sim_memory_stable_memory; eauto. intro STABLE_MEM1_TGT.
      exploit read_step_other_aux; eauto. i. des.
      dup STEP_SRC. inv STEP_SRC0.
      exploit Stable.read_step_other; try exact STEP; eauto; try congr. i. des.
      exploit Stable.read_step_other; try exact STEP_TGT; eauto; try congr. i. des.
      esplits; eauto.
    Qed.

    Lemma write_step_loc_aux
          rels lc1_src mem1_src releasedm_src
          lc1_tgt sc1 mem1_tgt loc from to val releasedm_tgt released_tgt ord lc2_tgt sc2 mem2_tgt kind
          (LC1: sim_local rels lc1_src lc1_tgt)
          (MEM1: sim_memory rels mem1_src mem1_tgt)
          (WF1_SRC: Local.wf lc1_src mem1_src)
          (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
          (RELEASEDM: View.opt_le releasedm_tgt releasedm_src)
          (RELEASEDM_SRC: View.opt_le releasedm_src (Some lc1_src.(Local.tview).(TView.cur)))
          (RELEASEDM_TGT: View.opt_le releasedm_tgt (Some lc1_tgt.(Local.tview).(TView.cur)))
          (RELEASEDM_WF_SRC: View.opt_wf releasedm_src)
          (RELEASEDM_WF_TGT: View.opt_wf releasedm_tgt)
          (LOC: L loc)
          (STEP_TGT: Local.write_step lc1_tgt sc1 mem1_tgt loc from to val releasedm_tgt released_tgt ord
                                      lc2_tgt sc2 mem2_tgt kind):
      exists rels' released_src lc2_src mem2_src,
        <<STEP_SRC: OrdLocal.write_step L Ordering.acqrel
                                        lc1_src sc1 mem1_src loc from to val releasedm_src released_src ord
                                        lc2_src sc2 mem2_src kind>> /\
        <<REL: rels' = if Ordering.le Ordering.acqrel ord then (loc, to) :: rels else rels>> /\
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
                - destruct releasedm_src; try apply Time.bot_spec. ss.
                  inv RELEASEDM_SRC. etrans; try eapply LE.
                  inv TVIEW. rewrite CUR. inv WRITABLE. econs. ss.
                - apply Time.join_spec; try refl.
                  inv TVIEW. rewrite CUR. inv WRITABLE. econs. ss.
              }
              { i. inv MEM1. exploit SOUND; try exact GET1. i. des. eauto. }
          + ss.
          + econs; ss.
            * inv TVIEW. econs; ss; try congr. i.
              rewrite ORD. unfold LocFun.add. repeat (condtac; ss).
              { rewrite CUR. refl. }
              { specialize (REL loc0). des_ifs. }
              { rewrite CUR. refl. }
              { specialize (REL loc0). des_ifs. }
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
              unfold TView.write_released. repeat (condtac; ss). econs.
              inv TVIEW. rewrite CUR.
              specialize (REL loc). des_ifs.
              apply View.join_spec.
              { etrans; [|apply View.join_l].
                inv RELEASEDM; ss. apply View.bot_spec. }
              { etrans; [|apply View.join_r].
                unfold LocFun.add. condtac; ss. refl. }
            * erewrite Memory.add_o; eauto.
              revert GET_TGT. erewrite Memory.add_o; eauto.
              condtac; ss; eauto. i. des. inv GET_TGT.
              esplits; eauto. econs. condtac; ss.
              unfold TView.write_released. repeat (condtac; ss). econs.
              inv TVIEW. rewrite CUR.
              specialize (REL loc). des_ifs.
              apply View.join_spec.
              { etrans; [|apply View.join_l].
                inv RELEASEDM; ss. apply View.bot_spec. }
              { etrans; [|apply View.join_r].
                unfold LocFun.add. condtac; ss. refl. }
            * inv IN.
              { inv H. exploit Memory.add_get0; try exact MEM. i. des.
                exploit Memory.add_get0; try exact x0. i. des.
                cut (TView.write_released tview0 sc1 loc0 to0 releasedm_tgt ord =
                     TView.write_released tview sc1 loc0 to0 releasedm_src ord).
                { i. rewrite H in *. revert GET2 GET4.
                  unfold TView.write_released. condtac; ss.
                  - esplits; eauto.
                  - destruct ord; ss. }
                unfold TView.write_released. repeat (condtac; ss). f_equal.
                unfold LocFun.add. condtac; ss.
                inv TVIEW. rewrite CUR.
                rewrite (@View.le_join_r releasedm_src.(View.unwrap)); cycle 1.
                { etrans; [|apply View.join_l].
                  destruct releasedm_src; try apply View.bot_spec. ss.
                  rewrite <- CUR. inv RELEASEDM_SRC. ss. }
                rewrite (@View.le_join_r releasedm_tgt.(View.unwrap)); ss.
                etrans; [|apply View.join_l].
                destruct releasedm_tgt; try apply View.bot_spec. ss.
                inv RELEASEDM_TGT. ss.
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
              { destruct releasedm_src; try apply Time.bot_spec. ss.
                  inv RELEASEDM_SRC. etrans; try eapply LE.
                  inv TVIEW. rewrite CUR. inv WRITABLE. econs. ss. }
              { apply Time.join_spec; try refl.
                inv TVIEW. rewrite CUR. inv WRITABLE. econs. ss. }
          + ss.
          + econs; ss.
            * inv TVIEW. econs; ss; try congr. i.
              rewrite ORD. unfold LocFun.add. repeat (condtac; ss).
              { rewrite CUR. refl. }
              { specialize (REL loc0). des_ifs. }
              { rewrite CUR. refl. }
              { specialize (REL loc0). des_ifs. }
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
                esplits; eauto. econs. condtac; ss.
                unfold TView.write_released. repeat (condtac; ss). econs.
                inv TVIEW. rewrite CUR.
                specialize (REL loc). des_ifs.
                apply View.join_spec.
                - etrans; [|apply View.join_l].
                  inv RELEASEDM; ss. apply View.bot_spec.
                - etrans; [|apply View.join_r].
                  unfold LocFun.add. condtac; ss. refl. }
              { guardH o. des. subst. inv GET_SRC.
                esplits; eauto. refl. }
            * erewrite Memory.split_o; eauto.
              revert GET_TGT. erewrite Memory.split_o; eauto.
              repeat condtac; ss; eauto; i.
              { des. subst. inv GET_TGT.
                esplits; eauto. econs. condtac; ss.
                unfold TView.write_released. repeat (condtac; ss). econs.
                inv TVIEW. rewrite CUR.
                specialize (REL loc). des_ifs.
                apply View.join_spec.
                - etrans; [|apply View.join_l].
                  inv RELEASEDM; ss. apply View.bot_spec.
                - etrans; [|apply View.join_r].
                  unfold LocFun.add. condtac; ss. refl. }
              { guardH o. des. subst. inv GET_TGT.
                esplits; eauto. refl. }
            * inv IN.
              { inv H. exploit Memory.split_get0; try exact MEM. i. des.
                exploit Memory.split_get0; try exact x1. i. des.
                cut (TView.write_released tview0 sc1 loc0 to0 releasedm_tgt ord =
                     TView.write_released tview sc1 loc0 to0 releasedm_src ord).
                { i. rewrite H in *. revert GET5 GET9.
                  unfold TView.write_released. condtac; ss; i.
                  - esplits; eauto.
                  - destruct ord; ss. }
                unfold TView.write_released. condtac; ss. condtac; ss.
                unfold LocFun.add. condtac; ss.
                inv TVIEW. rewrite CUR.
                rewrite (@View.le_join_r releasedm_src.(View.unwrap)); cycle 1.
                { etrans; [|apply View.join_l].
                  destruct releasedm_src; try apply View.bot_spec. ss.
                  rewrite <- CUR. inv RELEASEDM_SRC. ss. }
                rewrite (@View.le_join_r releasedm_tgt.(View.unwrap)); ss.
                etrans; [|apply View.join_l].
                destruct releasedm_tgt; try apply View.bot_spec. ss.
                inv RELEASEDM_TGT. ss.
              }
              { exploit REL_WRITES; eauto. i. des.
                erewrite Memory.split_o; eauto.
                erewrite (@Memory.split_o mem2_tgt); eauto.
                repeat condtac; ss; eauto.
                - des. subst.
                  exploit Memory.split_get0; try exact MEM. i. des. congr.
                - guardH o. des. subst.
                  exploit Memory.split_get0; try exact MEM. i. des.
                  exploit Memory.split_get0; try exact x1. i. des.
                  rewrite GET_SRC, GET_TGT in *. inv GET8. inv GET4.
                  esplits; eauto.
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
              unfold TView.write_released.
              repeat (condtac; ss); try apply Time.bot_spec.
              unfold LocFun.add. condtac; ss.
              unfold TimeMap.join, TimeMap.singleton, LocFun.add, LocFun.find. condtac; ss.
              apply Time.join_spec; ss.
              - destruct releasedm_src; try apply Time.bot_spec. ss.
                inv RELEASEDM_SRC. etrans; try eapply LE.
                inv TVIEW. rewrite CUR. inv WRITABLE. econs. ss.
              - apply Time.join_spec; try refl.
                inv TVIEW. rewrite CUR. inv WRITABLE. econs. ss.
            }
            { i. inv MEM1. exploit SOUND; try exact GET1. i. des. eauto. }
          * ii. destruct msg; ss. exploit RESERVE; eauto. ss.
        + ss.
        + econs; ss.
          * inv TVIEW. econs; ss; try congr. i.
            rewrite ORD. repeat (condtac; ss); try congr.
            { unfold LocFun.add. condtac; ss.
              - subst. rewrite CUR.
                inv WF1_TGT. inv TVIEW_WF. ss.
                apply View.join_spec.
                + etrans; [|apply View.join_l]. apply REL_CUR.
                + etrans; [|apply View.join_r]. refl.
              - unfold LocFun.find. specialize (REL loc0). des_ifs. }
            { unfold LocFun.add. condtac; ss.
              - subst. congr.
              - unfold LocFun.find. specialize (REL loc0). des_ifs. }
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
            unfold TView.write_released. repeat (condtac; ss). econs.
            inv TVIEW. rewrite CUR.
            specialize (REL loc). des_ifs.
            apply View.join_spec.
            { etrans; [|apply View.join_l].
              inv RELEASEDM; ss. apply View.bot_spec. }
            { etrans; [|apply View.join_r].
              unfold LocFun.add. condtac; ss.
              apply View.join_spec.
              - etrans; [|apply View.join_l].
                inv WF1_TGT. inv TVIEW_WF. apply REL_CUR.
              - etrans; [|apply View.join_r]. refl. }
          * erewrite Memory.add_o; eauto.
            revert GET_TGT. erewrite Memory.add_o; eauto.
            condtac; ss; eauto. i. des. inv GET_TGT.
            esplits; eauto. econs. condtac; ss.
            unfold TView.write_released. repeat (condtac; ss). econs.
            inv TVIEW. rewrite CUR.
            specialize (REL loc). des_ifs.
            apply View.join_spec.
            { etrans; [|apply View.join_l].
              inv RELEASEDM; ss. apply View.bot_spec. }
            { etrans; [|apply View.join_r].
              unfold LocFun.add. condtac; ss.
              apply View.join_spec.
              - etrans; [|apply View.join_l].
                inv WF1_TGT. inv TVIEW_WF. apply REL_CUR.
              - etrans; [|apply View.join_r]. refl. }
          * exploit REL_WRITES; eauto. i. des.
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
            unfold TView.write_released.
            repeat (condtac; ss); try apply Time.bot_spec.
            unfold LocFun.add. condtac; ss.
            unfold TimeMap.join, TimeMap.singleton, LocFun.add, LocFun.find. condtac; ss.
            apply Time.join_spec; ss.
            { destruct releasedm_src; try apply Time.bot_spec. ss.
              inv RELEASEDM_SRC. etrans; try eapply LE.
              inv TVIEW. rewrite CUR. inv WRITABLE. econs. ss. }
            { apply Time.join_spec; try refl.
              inv TVIEW. rewrite CUR. inv WRITABLE. econs. ss. }
          * ii. destruct msg; ss. exploit RESERVE; eauto. ss.
        + ss.
        + econs; ss.
          * inv TVIEW. econs; ss; try congr. i.
            rewrite ORD. unfold LocFun.add. repeat (condtac; ss); try congr.
            { apply View.join_spec.
              - etrans; [|apply View.join_l]. rewrite CUR.
                inv WF1_TGT. inv TVIEW_WF. auto.
              - etrans; [|apply View.join_r]. refl. }
            { specialize (REL loc0). des_ifs. }
            { specialize (REL loc0). des_ifs. }
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
          * i. erewrite Memory.remove_o; eauto. condtac; ss. guardH o.
            erewrite Memory.split_o; eauto. repeat condtac; ss; eauto.
            des; subst; ss.
            exploit Memory.split_get0; try exact PROMISES. i. des.
            exploit REL_WRITES_NONE; eauto. i. congr.
        + inv MEM1. econs; i.
          * erewrite Memory.split_o; eauto.
            revert GET_SRC. erewrite Memory.split_o; eauto.
            repeat condtac; ss; eauto; i.
            { des. subst. inv GET_SRC.
              esplits; eauto. econs. condtac; ss.
              unfold TView.write_released. repeat (condtac; ss). econs.
              unfold LocFun.add. condtac; ss.
              inv TVIEW. rewrite CUR.
              specialize (REL loc). des_ifs.
              apply View.join_spec.
              - etrans; [|apply View.join_l].
                inv RELEASEDM; ss. apply View.bot_spec.
              - etrans; [|apply View.join_r].
                apply View.join_spec.
                + etrans; [|apply View.join_l]. apply WF1_TGT.
                + etrans; [|apply View.join_r]. refl. }
            { guardH o. des. subst. inv GET_SRC.
              esplits; eauto. refl. }
          * erewrite Memory.split_o; eauto.
            revert GET_TGT. erewrite Memory.split_o; eauto.
            repeat condtac; ss; eauto; i.
            { des. subst. inv GET_TGT.
              esplits; eauto. econs. condtac; ss.
              unfold TView.write_released. repeat (condtac; ss). econs.
              unfold LocFun.add. condtac; ss.
              inv TVIEW. rewrite CUR.
              specialize (REL loc). des_ifs.
              apply View.join_spec.
              - etrans; [|apply View.join_l].
                inv RELEASEDM; ss. apply View.bot_spec.
              - etrans; [|apply View.join_r].
                apply View.join_spec.
                + etrans; [|apply View.join_l]. apply WF1_TGT.
                + etrans; [|apply View.join_r]. refl. }
            { guardH o. des. subst. inv GET_TGT.
              esplits; eauto. refl. }
          * exploit REL_WRITES; eauto. i. des.
            erewrite Memory.split_o; eauto.
            erewrite (@Memory.split_o mem2_tgt); eauto.
            repeat condtac; ss; eauto.
            { des. subst.
              exploit Memory.split_get0; try exact MEM. i. des. congr. }
            { guardH o. des. subst.
              exploit Memory.split_get0; try exact MEM. i. des.
              exploit Memory.split_get0; try exact x1. i. des.
              rewrite GET_SRC, GET_TGT in *. inv GET4. inv GET8.
              esplits; eauto. }
      - des. subst.
        exploit Memory.lower_get0; try exact PROMISES. i. des.
        exploit RESERVE; eauto. ss.
    Qed.

    Lemma write_step_loc
          rels lc1_src mem1_src releasedm_src
          lc1_tgt sc1 mem1_tgt loc from to val releasedm_tgt released_tgt ord lc2_tgt sc2 mem2_tgt kind
          (LC1: sim_local rels lc1_src lc1_tgt)
          (MEM1: sim_memory rels mem1_src mem1_tgt)
          (NORMAL_TVIEW1_SRC: Stable.normal_tview L lc1_src.(Local.tview))
          (NORMAL_TVIEW1_TGT: Stable.normal_tview L lc1_tgt.(Local.tview))
          (STABLE_TVIEW1_SRC: Stable.stable_tview L mem1_src lc1_src.(Local.tview))
          (NORMAL_MEM1_SRC: Stable.normal_memory L mem1_src)
          (NORMAL_MEM1_TGT: Stable.normal_memory L mem1_tgt)
          (STABLE_MEM1_SRC: Stable.stable_memory L rels mem1_src)
          (WF1_SRC: Local.wf lc1_src mem1_src)
          (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
          (SC1_SRC: Memory.closed_timemap sc1 mem1_src)
          (SC1_TGT: Memory.closed_timemap sc1 mem1_tgt)
          (MEM1_SRC: Memory.closed mem1_src)
          (MEM1_TGT: Memory.closed mem1_tgt)
          (RELEASEDM: View.opt_le releasedm_tgt releasedm_src)
          (RELEASEDM_SRC: View.opt_le releasedm_src (Some lc1_src.(Local.tview).(TView.cur)))
          (RELEASEDM_TGT: View.opt_le releasedm_tgt (Some lc1_tgt.(Local.tview).(TView.cur)))
          (RELEASEDM_NORMAL_SRC: Stable.normal_view L releasedm_src.(View.unwrap))
          (RELEASEDM_NORMAL_TGT: Stable.normal_view L releasedm_tgt.(View.unwrap))
          (RELEASEDM_WF_SRC: View.opt_wf releasedm_src)
          (RELEASEDM_WF_TGT: View.opt_wf releasedm_tgt)
          (RELEASEDM_CLOSED_SRC: Memory.closed_opt_view releasedm_src mem1_src)
          (RELEASEDM_CLOSED_TGT: Memory.closed_opt_view releasedm_tgt mem1_tgt)
          (LOC: L loc)
          (STEP_TGT: Local.write_step lc1_tgt sc1 mem1_tgt loc from to val releasedm_tgt released_tgt ord
                                      lc2_tgt sc2 mem2_tgt kind):
      exists rels' released_src lc2_src mem2_src,
        (<<STEP_SRC: OrdLocal.write_step L Ordering.acqrel
                                         lc1_src sc1 mem1_src loc from to val releasedm_src released_src ord
                                         lc2_src sc2 mem2_src kind>>) /\
        (<<REL: rels' = if Ordering.le Ordering.acqrel ord then (loc, to) :: rels else rels>>) /\
        (<<LC2: sim_local rels' lc2_src lc2_tgt>>) /\
        (<<MEM2: sim_memory rels' mem2_src mem2_tgt>>) /\
        (<<NORMAL_TVIEW2_SRC: Stable.normal_tview L lc2_src.(Local.tview)>>) /\
        (<<NORMAL_TVIEW2_TGT: Stable.normal_tview L lc2_tgt.(Local.tview)>>) /\
        (<<STABLE_TVIEW2_SRC: Stable.stable_tview L mem2_src lc2_src.(Local.tview)>>) /\
        (<<NORMAL_MEM2_SRC: Stable.normal_memory L mem2_src>>) /\
        (<<NORMAL_MEM2_TGT: Stable.normal_memory L mem2_tgt>>) /\
        (<<STABLE_MEM2_SRC: Stable.stable_memory L rels' mem2_src>>).
    Proof.
      exploit sim_release_writes_wf; eauto. i. des.
      exploit sim_memory_stable_tview; try apply LC1; eauto. intro STABLE_TVIEW1_TGT.
      hexploit sim_memory_stable_memory; eauto. intro STABLE_MEM1_TGT.
      exploit write_step_loc_aux; try exact STEP_TGT; try exact RELEASEDM_SRC; eauto. i. des.
      exploit Stable.write_step_loc; try exact STEP_TGT; eauto.
      { destruct releasedm_tgt; ss; try by apply View.bot_spec.
        inv RELEASEDM_TGT. ss. }
      i. des.
      dup STEP_SRC. inv STEP_SRC.
      exploit Stable.write_step_loc; try exact STEP; eauto.
      { destruct releasedm_src; ss; try by apply View.bot_spec.
        inv RELEASEDM_SRC. ss. }
      i. des.
      esplits; eauto.
      destruct (L loc); ss.
      revert STABLE_MEM0. condtac; ss; try by (destruct ord; ss). i.
      condtac; ss. eauto using Stable.stable_memory_tail.
    Qed.

    Lemma write_step_other_aux
          rels lc1_src mem1_src
          lc1_tgt sc1 mem1_tgt loc from to val releasedm released_tgt ord lc2_tgt sc2 mem2_tgt kind
          (LC1: sim_local rels lc1_src lc1_tgt)
          (MEM1: sim_memory rels mem1_src mem1_tgt)
          (WF1_SRC: Local.wf lc1_src mem1_src)
          (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
          (LOC: ~ L loc)
          (STEP_TGT: Local.write_step lc1_tgt sc1 mem1_tgt loc from to val releasedm released_tgt ord
                                      lc2_tgt sc2 mem2_tgt kind):
      exists released_src lc2_src mem2_src,
        <<STEP_SRC: OrdLocal.write_step L Ordering.acqrel
                                        lc1_src sc1 mem1_src loc from to val releasedm released_src ord
                                        lc2_src sc2 mem2_src kind>> /\
        <<LC2: sim_local rels lc2_src lc2_tgt>> /\
        <<MEM2: sim_memory rels mem2_src mem2_tgt>>.
    Proof.
      destruct (L loc) eqn:LOC'; try by congr.
      destruct lc1_src, lc1_tgt.
      inv LC1. inv STEP_TGT. inv WRITE. ss. subst.
      exploit promise; try exact PROMISE; eauto; try congr.
      { apply WF1_SRC. }
      { apply WF1_TGT. }
      i. des. esplits.
      - econs; [des_ifs|].
        econs; ss.
        { inv TVIEW. rewrite CUR. ss. }
        erewrite sim_tview_write_released; eauto. congr.
      - econs; ss.
        + inv TVIEW. econs; ss; try congr.
          i. unfold LocFun.add.
          repeat (condtac; ss; eauto); subst; try congr.
          * specialize (REL loc0). des_ifs.
          * specialize (REL loc). des_ifs. rewrite REL. refl.
          * specialize (REL loc0). des_ifs.
        + ii. revert PROMISE0.
          erewrite Memory.remove_o; eauto. condtac; ss. guardH o.
          inv PROMISE; ss.
          * erewrite Memory.add_o; eauto. condtac; ss; eauto.
          * exploit Memory.split_get0; try exact PROMISES. i. des. eauto.
          * exploit Memory.lower_get0; try exact PROMISES. i. des. eauto.
        + i. erewrite Memory.remove_o; eauto. condtac; ss. guardH o.
          inv PROMISE; ss.
          * erewrite Memory.add_o; eauto. condtac; ss; eauto.
          * exploit Memory.split_get0; try exact PROMISES. i. des. eauto.
          * exploit Memory.lower_get0; try exact PROMISES. i. des. eauto.
      - ss.
    Qed.

    Lemma write_step_other
          rels lc1_src mem1_src
          lc1_tgt sc1 mem1_tgt loc from to val releasedm released_tgt ord lc2_tgt sc2 mem2_tgt kind
          (LC1: sim_local rels lc1_src lc1_tgt)
          (MEM1: sim_memory rels mem1_src mem1_tgt)
          (NORMAL_TVIEW1_SRC: Stable.normal_tview L lc1_src.(Local.tview))
          (NORMAL_TVIEW1_TGT: Stable.normal_tview L lc1_tgt.(Local.tview))
          (STABLE_TVIEW1_SRC: Stable.stable_tview L mem1_src lc1_src.(Local.tview))
          (NORMAL_MEM1_SRC: Stable.normal_memory L mem1_src)
          (NORMAL_MEM1_TGT: Stable.normal_memory L mem1_tgt)
          (STABLE_MEM1_SRC: Stable.stable_memory L rels mem1_src)
          (WF1_SRC: Local.wf lc1_src mem1_src)
          (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
          (SC1_SRC: Memory.closed_timemap sc1 mem1_src)
          (SC1_TGT: Memory.closed_timemap sc1 mem1_tgt)
          (MEM1_SRC: Memory.closed mem1_src)
          (MEM1_TGT: Memory.closed mem1_tgt)
          (RELEASEDM_WF: View.opt_wf releasedm)
          (RELEASEDM_CLOSED: Memory.closed_opt_view releasedm mem1_src)
          (RELEASEDM_NORMAL: Stable.normal_view L releasedm.(View.unwrap))
          (RELEASEDM_STABLE: Stable.stable_view L mem1_src releasedm.(View.unwrap))
          (LOC: ~ L loc)
          (STEP_TGT: Local.write_step lc1_tgt sc1 mem1_tgt loc from to val releasedm released_tgt ord
                                      lc2_tgt sc2 mem2_tgt kind):
      exists released_src lc2_src mem2_src,
        (<<STEP_SRC: OrdLocal.write_step L Ordering.acqrel
                                         lc1_src sc1 mem1_src loc from to val releasedm released_src ord
                                         lc2_src sc2 mem2_src kind>>) /\
        (<<LC2: sim_local rels lc2_src lc2_tgt>>) /\
        (<<MEM2: sim_memory rels mem2_src mem2_tgt>>) /\
        (<<NORMAL_TVIEW2_SRC: Stable.normal_tview L lc2_src.(Local.tview)>>) /\
        (<<NORMAL_TVIEW2_TGT: Stable.normal_tview L lc2_tgt.(Local.tview)>>) /\
        (<<STABLE_TVIEW2_SRC: Stable.stable_tview L mem2_src lc2_src.(Local.tview)>>) /\
        (<<NORMAL_MEM2_SRC: Stable.normal_memory L mem2_src>>) /\
        (<<NORMAL_MEM2_TGT: Stable.normal_memory L mem2_tgt>>) /\
        (<<STABLE_MEM2_SRC: Stable.stable_memory L rels mem2_src>>).
    Proof.
      exploit sim_release_writes_wf; eauto. i. des.
      exploit sim_memory_stable_tview; try apply LC1; eauto. intro STABLE_TVIEW1_TGT.
      hexploit sim_memory_stable_memory; eauto. intro STABLE_MEM1_TGT.
      hexploit sim_memory_closed_opt_view_src; eauto. intro RELEASEDM_CLOSED_TGT.
      hexploit sim_memory_stable_view; eauto. intro RELEASEDM_STABLE_TGT.
      exploit write_step_other_aux; eauto. i. des.
      exploit Stable.write_step_other; try exact STEP_TGT; eauto. i. des.
      dup STEP_SRC. inv STEP_SRC0.
      exploit Stable.write_step_other; try exact STEP; eauto. i. des.
      esplits; eauto.
    Qed.

    Lemma fence_step_aux
          rels lc1_src
          lc1_tgt sc1 ordr ordw lc2_tgt sc2
          (LC1: sim_local rels lc1_src lc1_tgt)
          (STEP_TGT: Local.fence_step lc1_tgt sc1 ordr ordw lc2_tgt sc2):
      exists lc2_src,
        <<STEP_SRC: Local.fence_step lc1_src sc1 ordr ordw lc2_src sc2>> /\
        <<LC2: sim_local rels lc2_src lc2_tgt>>.
    Proof.
      destruct lc1_src, lc1_tgt.
      inv LC1. inv TVIEW. ss. subst.
      inv STEP_TGT. ss.
      esplits.
      - econs; ss.
        unfold TView.write_fence_sc.
        repeat (condtac; ss); congr.
      - econs; ss. econs; ss; i.
        + repeat (condtac; ss); eauto; try rewrite ACQ; try rewrite CUR; try refl.
          * unfold TView.write_fence_sc, TView.read_fence_tview.
            rewrite ACQ, CUR. refl.
          * specialize (REL loc). rewrite COND in *. ss.
          * unfold TView.write_fence_sc, TView.read_fence_tview.
            rewrite ACQ, CUR. f_equal; refl.
          * specialize (REL loc). rewrite COND in *. ss.
        + repeat (condtac; ss); eauto.
          unfold TView.write_fence_sc.
          repeat (condtac; ss); congr.
        + repeat (condtac; ss); eauto; try congr.
          unfold TView.write_fence_sc.
          repeat (condtac; ss); congr.
    Qed.

    Lemma fence_step
          rels lc1_src mem1_src
          lc1_tgt sc1 mem1_tgt ordr ordw lc2_tgt sc2
          (LC1: sim_local rels lc1_src lc1_tgt)
          (MEM1: sim_memory rels mem1_src mem1_tgt)
          (NORMAL_TVIEW1_SRC: Stable.normal_tview L lc1_src.(Local.tview))
          (NORMAL_TVIEW1_TGT: Stable.normal_tview L lc1_tgt.(Local.tview))
          (STABLE_TVIEW1_SRC: Stable.stable_tview L mem1_src lc1_src.(Local.tview))
          (STABLE_SC1_SRC: Stable.stable_timemap L mem1_src sc1)
          (WF1_SRC: Local.wf lc1_src mem1_src)
          (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
          (STEP_TGT: Local.fence_step lc1_tgt sc1 ordr ordw lc2_tgt sc2):
      exists lc2_src,
        (<<STEP_SRC: Local.fence_step lc1_src sc1 ordr ordw lc2_src sc2>>) /\
        (<<LC2: sim_local rels lc2_src lc2_tgt>>) /\
        (<<NORMAL_TVIEW2_SRC: Stable.normal_tview L lc2_src.(Local.tview)>>) /\
        (<<NORMAL_TVIEW2_TGT: Stable.normal_tview L lc2_tgt.(Local.tview)>>) /\
        (<<STABLE_TVIEW2_SRC: Stable.stable_tview L mem1_src lc2_src.(Local.tview)>>) /\
        (<<STABLE_SC2_SRC: Stable.stable_timemap L mem1_src sc2>>).
    Proof.
      exploit sim_release_writes_wf; eauto. i. des.
      exploit sim_memory_stable_tview; try apply LC1; eauto. intro STABLE_TVIEW1_TGT.
      exploit fence_step_aux; eauto. i. des.
      exploit Stable.fence_step; try exact STEP_TGT; eauto.
      { eapply sim_memory_stable_view; eauto. }
      i. des.
      exploit Stable.fence_step; try exact STEP_SRC; eauto. i. des.
      esplits; eauto.
    Qed.

    Lemma failure_step
          rels lc1_src lc1_tgt
          (LC1: sim_local rels lc1_src lc1_tgt)
          (STEP_TGT: Local.failure_step lc1_tgt):
      <<STEP_SRC: Local.failure_step lc1_src>>.
    Proof.
      destruct lc1_src, lc1_tgt.
      inv LC1. inv TVIEW. ss. subst.
      inv STEP_TGT. ss.
      econs. ii. ss.
      rewrite CUR. eauto.
    Qed.


    Inductive sim_event: forall (e_src e_tgt: ThreadEvent.t), Prop :=
    | sim_event_promise
        loc from to msg kind:
        sim_event (ThreadEvent.promise loc from to msg kind)
                  (ThreadEvent.promise loc from to msg kind)
    | sim_event_silent:
        sim_event ThreadEvent.silent ThreadEvent.silent
    | sim_event_read
        loc to val released_src released_tgt ord:
        sim_event (ThreadEvent.read loc to val released_src ord)
                  (ThreadEvent.read loc to val released_tgt ord)
    | sim_event_write
        loc from to val released_src released_tgt ord:
        sim_event (ThreadEvent.write loc from to val released_src ord)
                  (ThreadEvent.write loc from to val released_tgt ord)
    | sim_event_update
        loc from to valr valw releasedm_src releasedm_tgt released_src released_tgt ordr ordw:
        sim_event (ThreadEvent.update loc from to valr valw releasedm_src released_src ordr ordw)
                  (ThreadEvent.update loc from to valr valw releasedm_tgt released_tgt ordr ordw)
    | sim_event_fence
        ordr ordw:
        sim_event (ThreadEvent.fence ordr ordw) (ThreadEvent.fence ordr ordw)
    | sim_event_syscall
        e:
        sim_event (ThreadEvent.syscall e) (ThreadEvent.syscall e)
    | sim_event_failure:
        sim_event ThreadEvent.failure ThreadEvent.failure
    .
    Hint Constructors sim_event.

    Lemma thread_step
          rels e1_src e1_tgt
          pf e_tgt e2_tgt
          (SIM1: sim_thread rels e1_src e1_tgt)
          (STABLE1_SRC: stable_thread rels e1_src)
          (NORMAL1_SRC: normal_thread e1_src)
          (NORMAL1_TGT: normal_thread e1_tgt)
          (WF1_SRC: Local.wf e1_src.(Thread.local) e1_src.(Thread.memory))
          (WF1_TGT: Local.wf e1_tgt.(Thread.local) e1_tgt.(Thread.memory))
          (SC1_SRC: Memory.closed_timemap e1_src.(Thread.sc) e1_src.(Thread.memory))
          (SC1_TGT: Memory.closed_timemap e1_tgt.(Thread.sc) e1_tgt.(Thread.memory))
          (MEM1_SRC: Memory.closed e1_src.(Thread.memory))
          (MEM1_TGT: Memory.closed e1_tgt.(Thread.memory))
          (PROMISE: forall loc from to msg kind
                      (EVENT: e_tgt = ThreadEvent.promise loc from to msg kind),
              L loc /\ msg = Message.reserve)
          (STEP_TGT: Thread.step pf e_tgt e1_tgt e2_tgt):
      exists e_src e2_src,
        (<<STEP_SRC: OrdThread.step L Ordering.acqrel pf e_src e1_src e2_src>>) /\
        __guard__ (
            (<<SIM2: sim_thread (ReleaseWrites.append L e_src rels) e2_src e2_tgt>>) /\
            (<<EVENT: sim_event e_src e_tgt>>) /\
            (<<STABLE2_SRC: stable_thread (ReleaseWrites.append L e_src rels) e2_src>>) /\
            (<<NORMAL2_SRC: normal_thread e2_src>>) /\
            (<<NORMAL2_TGT: normal_thread e2_tgt>>)
            \/
            (<<RACE: exists loc to val released ord,
                ThreadEvent.is_reading e_src = Some (loc, to, val, released, ord) /\
                RAThread.ra_race L rels e1_src.(Thread.local).(Local.tview) loc to ord>>)).
    Proof.
      destruct e1_src as [st1_src lc1_src sc1_src mem1_src].
      destruct e1_tgt as [st1_tgt lc1_tgt sc1_tgt mem1_tgt].
      inv SIM1. inv STABLE1_SRC. inv NORMAL1_SRC. inv NORMAL1_TGT. ss. subst.
      hexploit sim_memory_stable_tview; eauto; try apply LOCAL. intro STABLE_TVIEW1_TGT.
      hexploit sim_memory_stable_memory; eauto. intro STABLE_MEM1_TGT.
      exploit sim_release_writes_wf; eauto. i. des.
      inv STEP_TGT; inv STEP; [|inv LOCAL0]; ss.
      - (* promise step *)
        exploit PROMISE; eauto. i. des. subst.
        exploit promise_step; try exact LOCAL0; eauto. i. des.
        exploit Stable.promise_step; try exact STEP_SRC; eauto; ss. i. des.
        exploit Stable.promise_step; try exact LOCAL0; eauto; ss. i. des.
        esplits.
        + econs 1. econs; eauto.
        + left. esplits; eauto.
          econs; ss; eauto.
          eapply Stable.future_stable_view; try apply STABLE_SC; eauto.
          exploit Local.promise_step_future; try exact STEP_SRC; eauto. i. des. ss.
      - (* silent step *)
        esplits.
        + econs 2. econs; [|econs 1]. eauto.
        + left. esplits; ss.
      - (* read step *)
        destruct (L loc) eqn:LOC.
        + exploit read_step_loc; try exact LOCAL0; eauto. i. des.
          esplits.
          * econs 2. econs; [|econs 2]; eauto.
          * unguard. des.
            { left. esplits; ss. }
            { right. esplits; ss. }
        + exploit read_step_other; try exact LOCAL0; eauto. i. des.
          esplits.
          * econs 2. econs; [|econs 2]; eauto.
          * left. esplits; ss.
      - (* write step *)
        destruct (L loc) eqn:LOC.
        + hexploit write_step_loc; try exact LOCAL0; eauto; ss. i. des.
          esplits.
          * econs 2. econs; [|econs 3]; eauto.
          * left. rewrite REL in *. unfold ReleaseWrites.append. ss. rewrite LOC.
            esplits; ss. econs; ss. inv STEP_SRC.
            exploit Local.write_step_future; try eapply STEP; eauto. i. des.
            inv STEP. ss.
            eapply Stable.future_stable_view; try exact STABLE_SC; eauto.
        + hexploit write_step_other; try exact LOCAL0; eauto; ss; try congr.
          { apply Stable.bot_stable_view. ss. }
          i. des. esplits.
          * econs 2. econs; [|econs 3]; eauto.
          * left. unfold ReleaseWrites.append. ss. rewrite LOC.
            esplits; ss. econs; ss. inv STEP_SRC.
            exploit Local.write_step_future; try eapply STEP; eauto. i. des.
            inv STEP. ss.
            eapply Stable.future_stable_view; try exact STABLE_SC; eauto.
      - (* update step *)
        destruct (L loc) eqn:LOC.
        + exploit read_step_loc; try exact LOCAL0; eauto. i. des.
          exploit Local.read_step_future; try exact LOCAL1; eauto. i. des.
          dup STEP_SRC. inv STEP_SRC0.
          exploit Local.read_step_future; try exact STEP; eauto. i. des.
          clear STEP. unguard. des.
          * hexploit write_step_loc; try exact LOCAL2; try exact RELEASED_SRC; eauto.
            { inv LOCAL1. inv STEP_SRC. inv STEP. inv MEMORY.
              exploit SOUND; eauto. i. des.
              rewrite GET_TGT in *. inv GET. inv MSG.
              revert RELEASED. condtac; ss. }
            { destruct released_src; ss.
              inv STEP_SRC. inv STEP. eauto. }
            { destruct releasedr; ss. inv LOCAL1. eauto. }
            i. des. esplits.
            { econs 2. econs; [|econs 4]; eauto. }
            { left. rewrite REL in *.
              unfold ReleaseWrites.append. ss. rewrite LOC in *.
              esplits; ss. econs; ss.
              inv STEP_SRC0. exploit Local.write_step_future; try exact STEP; eauto. i. des.
              inv STEP. ss.
              eapply Stable.future_stable_view; try eapply STABLE_SC; ss. }
          * cut (exists releasedw_src lc3_src mem2_src,
                    OrdLocal.write_step L Ordering.acqrel lc2_src sc1_tgt mem1_src
                                        loc tsr tsw valw released_src releasedw_src ordw
                                        lc3_src sc1_tgt mem2_src kind).
            { i. des. esplits.
              - econs 2. econs; [|econs 4]; eauto.
              - right. esplits; ss.
            }
            destruct lc1_src as [tview1_src promises1_src].
            destruct lc1_tgt as [tview1_tgt promises1_tgt].
            inv STEP_SRC. ss.
            exploit Local.read_step_future; try exact LOCAL1; eauto. i. des.
            exploit Local.read_step_future; try exact STEP; eauto. i. des.
            inv LOCAL1. inv STEP. ss. des_ifs.
            inv LOCAL. ss. subst.
            inv LOCAL2. inv WRITE. inv PROMISE0; ss.
            { (* add *)
              exploit (@Memory.add_exists
                         mem1_src loc tsr tsw
                         (Message.concrete valw
                                           (TView.write_released (TView.read_tview tview1_src loc tsr released_src (Ordering.join ordr Ordering.acqrel))
                                                                 sc1_tgt loc tsw released_src (Ordering.join ordw Ordering.acqrel)))).
              { ii. inv MEMORY. exploit SOUND; try exact GET2. i. des.
                exploit Memory.add_get1; try exact GET_TGT; eauto. i.
                exploit Memory.add_get0; try exact MEM. i. des.
                exploit Memory.get_disjoint; [exact x1|exact GET3|]. i.
                des; eauto; congr. }
              { inv MEM. inv ADD. ss. }
              { econs. eapply TViewFacts.write_future0; eauto. apply WF3. }
              i. des.
              exploit Memory.add_exists_le; try exact x0; try eapply WF0. i. des.
              exploit Memory.add_get0; try exact x1. i. des.
              exploit Memory.remove_exists; try exact GET2. i. des.
              esplits. econs.
              { instantiate (1 := Ordering.join ordw Ordering.acqrel).
                condtac; ss. }
              econs; ss.
              - inv WRITABLE. econs. condtac; [|destruct ordr; ss].
                unfold View.singleton_ur_if. condtac; [|destruct ordr; ss].
                unfold View.singleton_ur. ss.
                unfold TimeMap.join, TimeMap.singleton, LocFun.add. condtac; ss.
                unfold TimeMap.join in TS0.
                exploit TimeFacts.le_lt_lt; [eapply Time.join_l|exact TS0|]. i.
                exploit TimeFacts.le_lt_lt; [eapply Time.join_l|exact x3|]. i.
                exploit TimeFacts.le_lt_lt; [eapply Time.join_r|exact x3|]. i.
                repeat apply TimeFacts.join_spec_lt.
                + inv TVIEW. rewrite CUR. ss.
                + revert x5. unfold View.singleton_ur_if. condtac; ss.
                  * unfold TimeMap.singleton, LocFun.add. condtac; ss.
                  * unfold TimeMap.singleton, LocFun.add. condtac; ss.
                + inv MEM1_SRC. exploit CLOSED; eauto. i. des.
                  inv MSG_TS. eapply TimeFacts.le_lt_lt; eauto.
                  inv MEM. inv ADD. ss.
              - econs; eauto. econs 1; eauto.
                + econs. unfold TView.write_released.
                  condtac; [|destruct ordw]; ss.
                  unfold LocFun.add. condtac; ss.
                  condtac; [|destruct ordw]; ss.
                  condtac; [|destruct ordr]; ss.
                  unfold View.singleton_ur_if.
                  condtac; [|destruct ordr]; ss.
                  unfold TimeMap.join, TimeMap.singleton, LocFun.add, LocFun.find.
                  condtac; ss.
                  repeat apply Time.join_spec.
                  * inv MEM1_SRC. exploit CLOSED; eauto. i. des.
                    inv MSG_TS. etrans; eauto. econs.
                    inv MEM. inv ADD. ss.
                  * inv WRITABLE. revert TS0.
                    unfold View.join, TimeMap.join. ss. i.
                    exploit TimeFacts.le_lt_lt; [eapply Time.join_l|exact TS0|]. i.
                    exploit TimeFacts.le_lt_lt; [eapply Time.join_l|exact x3|]. i.
                    econs. inv TVIEW. congr.
                  * econs. inv MEM. inv ADD. ss.
                  * inv MEM1_SRC. exploit CLOSED; eauto. i. des.
                    inv MSG_TS. etrans; eauto. econs.
                    inv MEM. inv ADD. ss.
                  * refl.
                + i. inv MEMORY. exploit SOUND; try exact GET3. i. des. eauto.
              - ii. destruct msg; ss. exploit RESERVE; eauto. ss.
            }
            { (* split *)
              exploit (@Memory.split_exists
                         promises1_tgt loc tsr tsw ts3
                         (Message.concrete valw
                                           (TView.write_released (TView.read_tview tview1_src loc tsr released_src (Ordering.join ordr Ordering.acqrel))
                                                                 sc1_tgt loc tsw released_src (Ordering.join ordw Ordering.acqrel)))
                      msg3).
              { exploit Memory.split_get0; try exact PROMISES. i. des. ss. }
              { inv PROMISES. inv SPLIT. ss. }
              { inv PROMISES. inv SPLIT. ss. }
              { econs. eapply TViewFacts.write_future0; eauto. apply WF3. }
              i. des.
              exploit Memory.split_exists_le; try exact x0; try eapply WF0. i. des.
              exploit Memory.split_get0; try exact x0. i. des.
              exploit Memory.remove_exists; try exact GET3. i. des.
              esplits. econs.
              { instantiate (1 := Ordering.join ordw Ordering.acqrel).
                condtac; ss. }
              econs; ss.
              - inv WRITABLE. econs. condtac; [|destruct ordr; ss].
                unfold View.singleton_ur_if. condtac; [|destruct ordr; ss].
                unfold View.singleton_ur. ss.
                unfold TimeMap.join, TimeMap.singleton, LocFun.add. condtac; ss.
                unfold TimeMap.join in TS0.
                exploit TimeFacts.le_lt_lt; [eapply Time.join_l|exact TS0|]. i.
                exploit TimeFacts.le_lt_lt; [eapply Time.join_l|exact x3|]. i.
                exploit TimeFacts.le_lt_lt; [eapply Time.join_r|exact x3|]. i.
                repeat apply TimeFacts.join_spec_lt.
                + inv TVIEW. rewrite CUR. ss.
                + revert x5. unfold View.singleton_ur_if. condtac; ss.
                  * unfold TimeMap.singleton, LocFun.add. condtac; ss.
                  * unfold TimeMap.singleton, LocFun.add. condtac; ss.
                + inv MEM1_SRC. exploit CLOSED; eauto. i. des.
                  inv MSG_TS. eapply TimeFacts.le_lt_lt; eauto.
                  inv MEM. inv SPLIT. ss.
              - econs; eauto. econs 2; eauto.
                + econs. unfold TView.write_released.
                  condtac; [|destruct ordw]; ss.
                  unfold LocFun.add. condtac; ss.
                  condtac; [|destruct ordw]; ss.
                  condtac; [|destruct ordr]; ss.
                  unfold View.singleton_ur_if.
                  condtac; [|destruct ordr]; ss.
                  unfold TimeMap.join, TimeMap.singleton, LocFun.add, LocFun.find.
                  condtac; ss.
                  repeat apply Time.join_spec.
                  * inv MEM1_SRC. exploit CLOSED; eauto. i. des.
                    inv MSG_TS. etrans; eauto. econs.
                    inv MEM. inv SPLIT. ss.
                  * inv WRITABLE. revert TS0.
                    unfold View.join, TimeMap.join. ss. i.
                    exploit TimeFacts.le_lt_lt; [eapply Time.join_l|exact TS0|]. i.
                    exploit TimeFacts.le_lt_lt; [eapply Time.join_l|exact x3|]. i.
                    econs. inv TVIEW. congr.
                  * econs. inv MEM. inv SPLIT. ss.
                  * inv MEM1_SRC. exploit CLOSED; eauto. i. des.
                    inv MSG_TS. etrans; eauto. econs.
                    inv MEM. inv SPLIT. ss.
                  * refl.
              - ii. destruct msg; ss. exploit RESERVE; eauto. ss.
            }
            { (* lower *)
              des. subst.
              exploit Memory.lower_get0; try exact PROMISES. i. des.
              exploit RESERVE; eauto. ss.
            }
        + exploit read_step_other; try exact LOCAL0; eauto. i. des.
          exploit Local.read_step_future; try exact LOCAL1; eauto. i. des.
          dup STEP_SRC. inv STEP_SRC0.
          exploit Local.read_step_future; try exact STEP; eauto. i. des.
          hexploit write_step_other; try exact LOCAL2; eauto; try congr.
          { inv STEP. ss. destruct releasedr; ss. eauto. }
          { inv STEP. ss. destruct releasedr; ss; try by apply Stable.bot_stable_view.
            eapply STABLE_MEMORY; eauto. left. congr. }
          i. des. esplits.
          * econs 2. econs; [|econs 4]; eauto.
          * left. unfold ReleaseWrites.append. ss. rewrite LOC.
            esplits; ss. econs; ss.
            inv STEP_SRC0.
            exploit Local.write_step_future; try exact STEP0; eauto. i. des.
            inv STEP0. ss.
            eapply Stable.future_stable_view; try eapply STABLE_SC; eauto.
      - (* fence step *)
        exploit fence_step; try exact LOCAL1; eauto. i. des.
        esplits.
        + econs 2. econs; [|econs 5]; eauto.
        + left. esplits; ss.
      - (* syscall step *)
        exploit fence_step; try exact LOCAL1; eauto. i. des.
        esplits.
        + econs 2. econs; [|econs 6]; eauto.
        + left. esplits; ss.
      - (* failure step *)
        exploit failure_step; try exact LOCAL1; eauto. i. des.
        esplits.
        + econs 2. econs; [|econs 7]; eauto.
        + left. esplits; ss.
    Qed.
  End PFtoRASimThread.
End PFtoRASimThread.
