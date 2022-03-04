Require Import Lia.
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

Require Import PFStep.
Require Import OrdStep.
Require Import Writes.
Require Import WStep.
Require Import Stable.

Set Implicit Arguments.


Module APFtoRASim.
  Section APFtoRASim.
    Variable lang: language.
    Variable L: Loc.t -> bool.

    Inductive sim_tview (tview_src tview_tgt: TView.t): Prop :=
    | sim_tview_intro
        (REL: forall loc, if L loc
                     then View.le ((TView.rel tview_tgt) loc) ((TView.rel tview_src) loc)
                     else (TView.rel tview_src) loc = (TView.rel tview_tgt) loc)
        (CUR: (TView.cur tview_src) = (TView.cur tview_tgt))
        (ACQ: (TView.acq tview_src) = (TView.acq tview_tgt))
    .

    Inductive sim_local (lc_src lc_tgt: Local.t): Prop :=
    | sim_local_intro
        (TVIEW: sim_tview (Local.tview lc_src) (Local.tview lc_tgt))
        (PROMISES: (Local.promises lc_src) = (Local.promises lc_tgt))
    .

    Inductive sim_message (loc: Loc.t): forall (msg_src msg_tgt: Message.t), Prop :=
    | sim_message_concrete
        val released_src released_tgt
        (RELEASED: if L loc then View.opt_le released_tgt released_src else released_src = released_tgt):
        sim_message loc (Message.concrete val released_src) (Message.concrete val released_tgt)
    | sim_message_reserve:
        sim_message loc Message.reserve Message.reserve
    | sim_message_undef:
        sim_message loc Message.undef Message.undef
    .

    Program Instance sim_message_PreOrder: forall loc, PreOrder (sim_message loc).
    Next Obligation.
      ii. destruct x; econs; eauto. des_ifs. refl.
    Qed.
    Next Obligation.
      ii. inv H; inv H0; ss; econs; eauto. des_ifs. etrans; eauto.
    Qed.

    Inductive sim_memory (rels: Writes.t) (mem_src mem_tgt: Memory.t): Prop :=
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
        (REL_WRITES: forall loc to ord
                       (IN: List.In (loc, to, ord) rels)
                       (ORD: Ordering.le Ordering.acqrel ord),
            exists from val released,
              <<GET_SRC: Memory.get loc to mem_src = Some (from, Message.concrete val (Some released))>> /\
              <<GET_TGT: Memory.get loc to mem_tgt = Some (from, Message.concrete val (Some released))>>)
    .

    Inductive sim_statelocal (rels: Writes.t):
      forall (sl_src sl_tgt: {lang : language & Language.state lang} * Local.t), Prop :=
    | sim_statelocal_intro
        lang st lc_src lc_tgt
        (LOCAL: sim_local lc_src lc_tgt):
        sim_statelocal rels (existT _ lang st, lc_src) (existT _ lang st, lc_tgt)
    .
    Hint Constructors sim_statelocal.

    Inductive sim_thread (rels: Writes.t) (e_src e_tgt: Thread.t lang): Prop :=
    | sim_thread_intro
        (STATE: (Thread.state e_src) = (Thread.state e_tgt))
        (LOCAL: sim_local (Thread.local e_src) (Thread.local e_tgt))
        (SC: (Thread.sc e_src) = (Thread.sc e_tgt))
        (MEMORY: sim_memory rels (Thread.memory e_src) (Thread.memory e_tgt))
    .
    Hint Constructors sim_thread.


    Lemma sim_tview_ra_race
          rels tview_src tview_tgt e
          (SIM: sim_tview tview_src tview_tgt):
      RARaceW.ra_race L rels tview_src e <->
      RARaceW.ra_race L rels tview_tgt e.
    Proof.
      inv SIM.
      unfold RARaceW.ra_race, RARaceW.wr_race, RARaceW.ww_race.
      split; i; des;
        (try by left; esplits; eauto; congr);
        (try by right; esplits; eauto; congr).
    Qed.

    Lemma sim_local_ra_race
          rels lc_src lc_tgt e
          (SIM: sim_local lc_src lc_tgt):
      RARaceW.ra_race L rels (Local.tview lc_src) e <->
      RARaceW.ra_race L rels (Local.tview lc_tgt) e.
    Proof.
      inv SIM. eapply sim_tview_ra_race; eauto.
    Qed.

    Lemma sim_thread_ra_race
          rels e_src e_tgt e
          (SIM: sim_thread rels e_src e_tgt):
      RARaceW.ra_race L rels (Local.tview (Thread.local e_src)) e <->
      RARaceW.ra_race L rels (Local.tview (Thread.local e_tgt)) e.
    Proof.
      inv SIM. eapply sim_local_ra_race; eauto.
    Qed.

    Lemma sim_memory_ord_le
          loc to ord rels mem_src mem_tgt
          ord'
          (SIM: sim_memory ((loc, to, ord) :: rels) mem_src mem_tgt)
          (LE: Ordering.le ord' ord):
      sim_memory ((loc, to, ord') :: rels) mem_src mem_tgt.
    Proof.
      inv SIM. econs; eauto. i. inv IN.
      - inv H. eapply REL_WRITES; [left; eauto|]. etrans; eauto.
      - eapply REL_WRITES; eauto. right. ss.
    Qed.

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
          lc_src lc_tgt
          (SIM: sim_local lc_src lc_tgt)
          (CONS: Local.promise_consistent lc_tgt):
      Local.promise_consistent lc_src.
    Proof.
      inv SIM. inv TVIEW. ii.
      rewrite PROMISES, CUR in *. eauto.
    Qed.

    Lemma sim_thread_promise_consistent
          rels e_src e_tgt
          (SIM: sim_thread rels e_src e_tgt)
          (CONS: Local.promise_consistent (Thread.local e_tgt)):
      Local.promise_consistent (Thread.local e_src).
    Proof.
      inv SIM. eapply sim_local_promise_consistent; eauto.
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

    Lemma sim_memory_writes_wf
          rels mem_src mem_tgt
          (SIM: sim_memory rels mem_src mem_tgt):
      forall rels', Writes.wf L rels' mem_src <-> Writes.wf L rels' mem_tgt.
    Proof.
      inv SIM. i. split; i; inv H; econs; i.
      - exploit SOUND0; eauto. i. des. split; ss.
        exploit SOUND; eauto. i. des. inv MSG. eauto.
      - exploit COMPLETE; eauto. i. des. inv MSG. eauto.
      - exploit SOUND0; eauto.  i. des. split; ss.
        exploit COMPLETE; eauto. i. des. inv MSG. eauto.
      - exploit SOUND; eauto. i. des. inv MSG. eauto.
    Qed.

    Lemma sim_memory_add
          rels mem1_src
          mem1_tgt loc from to msg mem2_tgt
          (SIM1: sim_memory rels mem1_src mem1_tgt)
          (RELS: forall ord, ~ List.In (loc, to, ord) rels)
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
        des. subst. exploit RELS; eauto. ss.
    Qed.

    Lemma sim_memory_split
          rels mem1_src
          mem1_tgt loc ts1 ts2 ts3 msg2 msg3 mem2_tgt
          (SIM1: sim_memory rels mem1_src mem1_tgt)
          (LOC: ~ L loc)
          (RELS: forall ord, ~ List.In (loc, ts3, ord) rels)
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
        + guardH o. des. subst. exploit RELS; eauto. ss.
    Qed.

    Lemma sim_memory_lower
          rels mem1_src
          mem1_tgt loc from to msg1 msg2 mem2_tgt
          (SIM1: sim_memory rels mem1_src mem1_tgt)
          (LOC: ~ L loc)
          (RELS: forall ord, ~ List.In (loc, to, ord) rels)
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
        des. subst. exploit RELS; eauto. ss.
    Qed.

    Lemma sim_memory_remove
          rels mem1_src
          mem1_tgt loc from to msg mem2_tgt
          (SIM1: sim_memory rels mem1_src mem1_tgt)
          (LOC: ~ L loc)
          (REL: forall ord, ~ List.In (loc, to, ord) rels)
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
        eapply sim_memory_stable_view; eauto.
    Qed.

    Lemma sim_thread_stable
          rels e_src e_tgt
          (SIM: sim_thread rels e_src e_tgt)
          (STABLE_SRC: Stable.stable_thread L rels e_src):
      Stable.stable_thread L rels e_tgt.
    Proof.
      destruct e_src, e_tgt. inv SIM. inv STABLE_SRC. ss. subst.
      inv LOCAL. econs; ss; eauto.
      - eapply sim_memory_stable_tview; eauto.
      - eapply sim_memory_stable_view; eauto.
      - eapply sim_memory_stable_memory; eauto.
    Qed.

    (* step *)

    Lemma promise
          rels mem1_src
          promises1 mem1_tgt loc from to msg promises2 mem2_tgt kind
          (PROMISES1: OrdLocal.reserve_only L promises1)
          (WRITES1: Writes.wf L rels mem1_src)
          (MEM1: sim_memory rels mem1_src mem1_tgt)
          (LE1_SRC: Memory.le promises1 mem1_src)
          (STEP_TGT: Memory.promise promises1 mem1_tgt loc from to msg promises2 mem2_tgt kind)
          (MSG: L loc -> msg = Message.reserve):
      exists mem2_src,
        <<STEP_SRC: Memory.promise promises1 mem1_src loc from to msg promises2 mem2_src kind>> /\
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
          esplits; eauto. econs; i.
          + revert GET_SRC. erewrite Memory.add_o; eauto. condtac; ss.
            { i. des. clarify.
              exploit Memory.add_get0; try exact MEM. i. des.
              esplits; eauto. econs. }
            { i. erewrite Memory.add_o; eauto. condtac; ss; eauto. }
          + revert GET_TGT. erewrite Memory.add_o; eauto. condtac; ss.
            { i. des. inv GET_TGT.
              exploit Memory.add_get0; try exact x0. i. des.
              esplits; eauto. econs. }
            { i. erewrite Memory.add_o; eauto. condtac; ss; eauto. }
          + exploit REL_WRITES; eauto. i. des.
            erewrite Memory.add_o; eauto.
            erewrite (@Memory.add_o mem2_tgt); eauto.
            condtac; ss; eauto. des. subst.
            exploit Memory.add_get0; try exact MEM. i. des. congr.
        - (* split *)
          des. ss.
        - (* lower *)
          des. subst. inv MEM. inv LOWER. inv MSG_LE. ss.
        - (* cancel *)
          exploit Memory.remove_get0; try exact PROMISES. i. des.
          exploit Memory.remove_exists_le; try apply LE1_SRC; eauto. i. des.
          esplits; eauto. econs; i.
          + revert GET_SRC. erewrite Memory.remove_o; eauto. condtac; ss. i.
            erewrite Memory.remove_o; eauto. condtac; ss. eauto.
          + revert GET_TGT. erewrite Memory.remove_o; eauto. condtac; ss. i.
            erewrite Memory.remove_o; eauto. condtac; ss. eauto.
          + exploit REL_WRITES; eauto. i. des.
            erewrite Memory.remove_o; eauto.
            erewrite (@Memory.remove_o mem2_tgt); eauto.
            condtac; ss; eauto. des. subst.
            exploit Memory.remove_get0; try exact x0. i. des. congr.
      }

      (* promises on other loc *)
      clear MSG. inv STEP_TGT.
      - (* add *)
        exploit sim_memory_add; eauto.
        { ii. inv WRITES1. exploit SOUND; eauto. i. des.
          exploit Memory.add_get0; try exact MEM. i. des. congr.
        }
        i. des. esplits; eauto. econs; eauto.
        i. subst. inv MEM1. exploit SOUND; eauto. i. des. eauto.
      - (* split *)
        exploit sim_memory_split; eauto; try congr.
        { ii. inv WRITES1. exploit SOUND; eauto. i. des.
          exploit Memory.split_get0; try exact MEM. i. des.
          inv MEM1. exploit COMPLETE0; try exact GET0. i. des.
          rewrite GET_SRC in *. inv x0. inv MSG0.
          exploit Memory.split_get0; try exact PROMISES. i. des.
          exploit PROMISES1; eauto.
        }
        i. des. esplits; eauto.
      - (* lower *)
        exploit sim_memory_lower; eauto; try congr.
        { ii. inv WRITES1. exploit SOUND; eauto. i. des.
          exploit Memory.lower_get0; try exact MEM. i. des.
          inv MEM1. exploit COMPLETE0; try exact GET. i. des.
          rewrite GET_SRC in *. inv x0. inv MSG0.
          exploit Memory.lower_get0; try exact PROMISES. i. des.
          exploit PROMISES1; eauto. ss.
        }
        i. des.
        inv MEM1. esplits; eauto.
      - (* cancel *)
        exploit sim_memory_remove; eauto; try congr.
        { ii. exploit Memory.remove_get0; try exact PROMISES. i. des.
          exploit LE1_SRC; eauto. i.
          inv WRITES1. exploit SOUND; eauto. i. des. congr.
        }
        i. des. esplits; eauto.
    Qed.

    Lemma write
          rels mem1_src
          promises1 mem1_tgt loc from to msg promises2 mem2_tgt kind
          (PROMISES1: OrdLocal.reserve_only L promises1)
          (WRITES1: Writes.wf L rels mem1_src)
          (MEM1: sim_memory rels mem1_src mem1_tgt)
          (LE1_SRC: Memory.le promises1 mem1_src)
          (STEP_TGT: Memory.write promises1 mem1_tgt loc from to msg promises2 mem2_tgt kind)
          (LOC: ~ L loc):
      exists mem2_src,
        <<STEP_SRC: Memory.write promises1 mem1_src loc from to msg promises2 mem2_src kind>> /\
        <<MEM2: sim_memory rels mem2_src mem2_tgt>>.
    Proof.
      inv STEP_TGT.
      exploit promise; eauto; ss. i. des.
      esplits; eauto.
    Qed.

    Lemma write_na
          rels mem1_src
          ts promises1 mem1_tgt loc from to msg promises2 mem2_tgt msgs kinds kind
          (PROMISES1: OrdLocal.reserve_only L promises1)
          (WRITES1: Writes.wf L rels mem1_src)
          (MEM1: sim_memory rels mem1_src mem1_tgt)
          (LE1_SRC: Memory.le promises1 mem1_src)
          (STEP_TGT: Memory.write_na ts promises1 mem1_tgt loc from to msg promises2 mem2_tgt msgs kinds kind)
          (LOC: ~ L loc):
      exists mem2_src,
        <<STEP_SRC: Memory.write_na ts promises1 mem1_src loc from to msg promises2 mem2_src msgs kinds kind>> /\
        <<MEM2: sim_memory rels mem2_src mem2_tgt>>.
    Proof.
      revert mem1_src PROMISES1 WRITES1 MEM1 LE1_SRC.
      induction STEP_TGT; i.
      { exploit write; eauto. i. des. esplits; eauto. }
      exploit write; eauto. i. des.
      hexploit OrdLocal.write_reserve_only; try exact STEP_SRC; eauto. i.
      hexploit (@Writes.write_wf L Ordering.na); try exact STEP_SRC; eauto; ss. condtac; ss. i.
      hexploit Memory.write_le; try exact STEP_SRC; eauto. i. des.
      exploit IHSTEP_TGT; eauto. i. des.
      esplits; eauto.
    Qed.

    Lemma promise_step
          rels lc1_src mem1_src
          lc1_tgt mem1_tgt loc from to msg lc2_tgt mem2_tgt kind
          (LC1: sim_local lc1_src lc1_tgt)
          (MEM1: sim_memory rels mem1_src mem1_tgt)
          (PROMISES1: OrdLocal.reserve_only L (Local.promises lc1_src))
          (WRITES1: Writes.wf L rels mem1_src)
          (WF1_SRC: Local.wf lc1_src mem1_src)
          (STEP_TGT: Local.promise_step lc1_tgt mem1_tgt loc from to msg lc2_tgt mem2_tgt kind)
          (MSG: L loc -> msg = Message.reserve):
      exists lc2_src mem2_src,
        (<<STEP_SRC: Local.promise_step lc1_src mem1_src loc from to msg lc2_src mem2_src kind>>) /\
        (<<LC2: sim_local lc2_src lc2_tgt>>) /\
        (<<MEM2: sim_memory rels mem2_src mem2_tgt>>).
    Proof.
      inv LC1. inv STEP_TGT. destruct lc1_src, lc1_tgt. ss. subst.
      exploit promise; try exact PROMISE; eauto; try apply WF1_SRC. i. des.
      esplits; try exact MEM2.
      - econs; eauto.
        eapply sim_memory_closed_message_tgt; eauto.
      - econs; eauto.
    Qed.

    Lemma read_step_loc
          rels lc1_src mem1_src
          lc1_tgt mem1_tgt loc to val released_tgt ord lc2_tgt
          (LC1: sim_local lc1_src lc1_tgt)
          (MEM1: sim_memory rels mem1_src mem1_tgt)
          (WRITES1: Writes.wf L rels mem1_src)
          (NORMAL_TVIEW1_SRC: Normal.normal_tview L (Local.tview lc1_src))
          (NORMAL_TVIEW1_TGT: Normal.normal_tview L (Local.tview lc1_tgt))
          (STABLE_TVIEW1_SRC: Stable.stable_tview L mem1_src (Local.tview lc1_src))
          (NORMAL_MEM1_SRC: Normal.normal_memory L mem1_src)
          (NORMAL_MEM1_TGT: Normal.normal_memory L mem1_tgt)
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
            (<<LC2: sim_local lc2_src lc2_tgt>>) /\
            (<<RELEASED_SRC: View.opt_le released_src (Some (TView.cur (Local.tview lc2_src)))>>) /\
            (<<RELEASED_TGT: View.opt_le released_tgt (Some (TView.cur (Local.tview lc2_tgt)))>>) /\
            (<<NORMAL_TVIEW1_SRC: Normal.normal_tview L (Local.tview lc2_src)>>) /\
            (<<NORMAL_TVIEW1_TGT: Normal.normal_tview L (Local.tview lc2_tgt)>>) /\
            (<<STABLE_TVIEW1_SRC: Stable.stable_tview L mem1_src (Local.tview lc2_src)>>)
            \/
            (<<RACE: RARaceW.wr_race L rels (Local.tview lc1_src) loc ord>>)).
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
      des. esplits; eauto.
      dup STEP_SRC. inv STEP_SRC0. inv STEP.
      rewrite GET0 in *. inv GET_SRC.

      inv PLN; cycle 1.
      { (* read from cur view *)
        inv H. left. esplits; try exact STEP_SRC.
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

      inv WRITES1. exploit COMPLETE0; eauto.
      { ii. subst. inv H. }
      i. des.
      destruct (Ordering.le ord0 Ordering.strong_relaxed) eqn:ORDW.
      { (* non release write *)
        right. unfold RARaceW.wr_race. esplits; eauto.
      }
      destruct (Ordering.le ord Ordering.strong_relaxed) eqn:ORDR.
      { (* non acquire read *)
        right. unfold RARaceW.wr_race. esplits; eauto.
      }

      (* RA synchronized *)
      left. splits; ss.
      - econs; ss. rewrite LOC.
        exploit REL_WRITES; eauto; try by destruct ord0; ss. i. des.
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
      - inv STEP_SRC.
        exploit Normal.read_step; try exact STEP; eauto.
        rewrite LOC. destruct ord; ss.
      - exploit Normal.read_step; eauto.
        rewrite LOC. destruct ord; ss.
      - inv STEP_SRC.
        exploit Stable.read_step_loc_ra; try apply STEP; eauto.
        { destruct ord0; ss. }
        { rewrite LOC. destruct ord; ss. }
    Qed.

    Lemma read_step_other_aux
          rels lc1_src mem1_src
          lc1_tgt mem1_tgt loc to val released ord lc2_tgt
          (LC1: sim_local lc1_src lc1_tgt)
          (MEM1: sim_memory rels mem1_src mem1_tgt)
          (LOC: L loc = false)
          (STEP_TGT: Local.read_step lc1_tgt mem1_tgt loc to val released ord lc2_tgt):
      exists lc2_src,
        (<<STEP_SRC: OrdLocal.read_step L Ordering.acqrel lc1_src mem1_src loc to val released ord lc2_src>>) /\
        (<<LC2: sim_local lc2_src lc2_tgt>>).
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
          (LC1: sim_local lc1_src lc1_tgt)
          (MEM1: sim_memory rels mem1_src mem1_tgt)
          (NORMAL_TVIEW1_SRC: Normal.normal_tview L (Local.tview lc1_src))
          (NORMAL_TVIEW1_TGT: Normal.normal_tview L (Local.tview lc1_tgt))
          (STABLE_TVIEW1_SRC: Stable.stable_tview L mem1_src (Local.tview lc1_src))
          (NORMAL_MEM1_SRC: Normal.normal_memory L mem1_src)
          (NORMAL_MEM1_TGT: Normal.normal_memory L mem1_tgt)
          (STABLE_MEM1_SRC: Stable.stable_memory L rels mem1_src)
          (WF1_SRC: Local.wf lc1_src mem1_src)
          (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
          (MEM1_SRC: Memory.closed mem1_src)
          (MEM1_TGT: Memory.closed mem1_tgt)
          (LOC: L loc = false)
          (STEP_TGT: Local.read_step lc1_tgt mem1_tgt loc to val released ord lc2_tgt):
      exists lc2_src,
        (<<STEP_SRC: OrdLocal.read_step L Ordering.acqrel lc1_src mem1_src loc to val released ord lc2_src>>) /\
        (<<LC2: sim_local lc2_src lc2_tgt>>) /\
        (<<NORMAL_TVIEW1_SRC: Normal.normal_tview L (Local.tview lc2_src)>>) /\
        (<<NORMAL_TVIEW1_TGT: Normal.normal_tview L (Local.tview lc2_tgt)>>) /\
        (<<STABLE_TVIEW1_SRC: Stable.stable_tview L mem1_src (Local.tview lc2_src)>>).
    Proof.
      exploit sim_memory_stable_tview; try eapply LC1; eauto. intro STABLE_TVIEW1_TGT.
      hexploit sim_memory_stable_memory; eauto. intro STABLE_MEM1_TGT.
      exploit read_step_other_aux; eauto. i. des.
      dup STEP_SRC. inv STEP_SRC0.
      exploit Normal.read_step; try exact STEP; eauto; try congr. i. des.
      exploit Normal.read_step; try exact STEP_TGT; eauto; try congr. i. des.
      exploit Stable.read_step_other; try exact STEP; eauto; try congr. i. des.
      esplits; eauto.
    Qed.

    Lemma write_step_loc_aux
          rels lc1_src mem1_src releasedm_src
          lc1_tgt sc1 mem1_tgt loc from to val releasedm_tgt released_tgt ord lc2_tgt sc2 mem2_tgt kind
          (LC1: sim_local lc1_src lc1_tgt)
          (MEM1: sim_memory rels mem1_src mem1_tgt)
          (RESERVE_ONLY1: OrdLocal.reserve_only L (Local.promises lc1_src))
          (WF1_SRC: Local.wf lc1_src mem1_src)
          (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
          (RELEASEDM: View.opt_le releasedm_tgt releasedm_src)
          (RELEASEDM_SRC: View.opt_le releasedm_src (Some (TView.cur (Local.tview lc1_src))))
          (RELEASEDM_TGT: View.opt_le releasedm_tgt (Some (TView.cur (Local.tview lc1_tgt))))
          (RELEASEDM_WF_SRC: View.opt_wf releasedm_src)
          (RELEASEDM_WF_TGT: View.opt_wf releasedm_tgt)
          (LOC: L loc)
          (STEP_TGT: Local.write_step lc1_tgt sc1 mem1_tgt loc from to val releasedm_tgt released_tgt ord
                                      lc2_tgt sc2 mem2_tgt kind):
      exists released_src lc2_src mem2_src,
        <<STEP_SRC: OrdLocal.write_step L Ordering.acqrel
                                        lc1_src sc1 mem1_src loc from to val releasedm_src released_src ord
                                        lc2_src sc2 mem2_src kind>> /\
        <<LC2: sim_local lc2_src lc2_tgt>> /\
        <<MEM2: sim_memory ((loc, to, ord) :: rels) mem2_src mem2_tgt>>.
    Proof.
      destruct lc1_src as [tview1_src promises1_src],
          lc1_tgt as [tview1_tgt promises1_tgt].
      inv LC1. inv STEP_TGT. ss. subst.
      exploit OrdLocal.reserve_only_write_add; try exact WRITE; eauto. i. subst.
      inv WRITE. inv PROMISE.
      exploit (@Memory.add_exists
                 mem1_src loc from to
                 (Message.concrete val (TView.write_released tview1_src sc1 loc to releasedm_src
                                                             (Ordering.join ord Ordering.acqrel)))).
      { ii. inv MEM1.
        exploit SOUND; eauto. i. des.
        exploit Memory.add_get1; try exact GET_TGT; eauto. i.
        exploit Memory.add_get0; try exact MEM. i. des.
        exploit Memory.get_disjoint; [exact x1|exact GET0|..]. i. des; eauto.
        subst. congr.
      }
      { inv MEM. inv ADD. ss. }
      { econs. eapply TViewFacts.write_future0; eauto. apply WF1_SRC. }
      i. des.
      exploit Memory.add_exists_le; try exact x0; try eapply WF1_SRC. i. des. ss.
      exploit Memory.add_get0; try exact x1. i. des.
      exploit Memory.remove_exists; try exact GET0. i. des.
      esplits.
      - econs; eauto. condtac; ss. econs; ss.
        + inv TVIEW. rewrite CUR. inv WRITABLE. econs. ss.
        + econs; eauto. econs; eauto.
          { econs. inv TS.
            unfold TView.write_released.
            repeat (condtac; ss); try apply Time.bot_spec; try by destruct ord; ss.
            unfold LocFun.add. condtac; ss.
            unfold TimeMap.join, TimeMap.singleton, LocFun.add, LocFun.find. condtac; ss.
            apply Time.join_spec; ss.
            - destruct releasedm_src; try apply Time.bot_spec. ss.
              inv RELEASEDM_SRC. etrans; try eapply LE.
              inv TVIEW. rewrite CUR. inv WRITABLE. econs. ss.
            - apply Time.join_spec; try refl.
              inv TVIEW. rewrite CUR. inv WRITABLE. econs. ss.
          }
          { i. inv MEM1. exploit SOUND; try exact GET1. i. des.
            eapply ATTACH; eauto; ss.
          }
        + ii. exploit RESERVE_ONLY1; eauto. i. subst. ss.
      - econs; ss.
        + inv TVIEW. econs; ss; try congr. i.
          unfold LocFun.add. condtac; ss; cycle 1.
          { condtac; try congr.
            specialize (REL loc0). des_ifs.
          }
          condtac; ss; cycle 1.
          { specialize (REL loc0). des_ifs. }
          do 2 (condtac; ss); try by destruct ord; ss.
          * rewrite CUR. refl.
          * rewrite CUR. apply View.join_spec; try apply View.join_r.
            etrans; [|apply View.join_l]. apply WF1_TGT.
       + exploit MemoryMerge.add_remove; try exact PROMISES; eauto. i. subst.
         exploit MemoryMerge.add_remove; try exact x1; eauto.
      - inv MEM1. move MEM at bottom. move x0 at bottom. econs; i.
        + erewrite Memory.add_o; eauto.
          revert GET_SRC. erewrite Memory.add_o; eauto.
          condtac; ss; eauto. i. des. clarify. esplits; eauto. econs.
          condtac; ss; try congr.
          apply TViewFacts.write_released_mon; eauto; try refl.
          * inv TVIEW. econs; try rewrite CUR; try rewrite ACQ; try refl.
            i. specialize (REL loc0). des_ifs.
            unfold LocFun.find. rewrite REL. refl.
          * apply WF1_SRC.
          * destruct ord; ss.
        + erewrite Memory.add_o; eauto.
          revert GET_TGT. erewrite Memory.add_o; eauto.
          condtac; ss; eauto. i. des. clarify. esplits; eauto. econs.
          condtac; ss; try congr.
          apply TViewFacts.write_released_mon; eauto; try refl.
          * inv TVIEW. econs; try rewrite CUR; try rewrite ACQ; try refl.
            i. specialize (REL loc0). des_ifs.
            unfold LocFun.find. rewrite REL. refl.
          * apply WF1_SRC.
          * destruct ord; ss.
        + inv IN; cycle 1.
          { exploit REL_WRITES; eauto. i. des.
            exploit Memory.add_get1; try exact GET_SRC; eauto.
            exploit Memory.add_get1; try exact GET_TGT; eauto.
          }
          inv H.
          erewrite (@Memory.add_o mem2); eauto.
          erewrite (@Memory.add_o mem2_tgt); eauto.
          condtac; des; ss.
          replace (Ordering.join ord0 Ordering.acqrel) with ord0 in * by (destruct ord0; ss).
          unfold TView.write_released. condtac; try by (destruct ord0; ss).
          esplits; eauto. do 4 f_equal. ss. condtac; ss.
          unfold LocFun.add. condtac; ss.
          rewrite View.le_join_r; cycle 1.
          { etrans; [|eapply View.join_l]. inv RELEASEDM_TGT; ss. apply View.bot_spec. }
          symmetry.
          rewrite View.le_join_r; cycle 1.
          { etrans; [|eapply View.join_l]. inv RELEASEDM_SRC; ss. apply View.bot_spec. }
          inv TVIEW. rewrite CUR. ss.
    Qed.

    Lemma write_step_loc
          rels lc1_src mem1_src releasedm_src
          lc1_tgt sc1 mem1_tgt loc from to val releasedm_tgt released_tgt ord lc2_tgt sc2 mem2_tgt kind
          (LC1: sim_local lc1_src lc1_tgt)
          (MEM1: sim_memory rels mem1_src mem1_tgt)
          (WRITES1: Writes.wf L rels mem1_src)
          (RESERVE_ONLY1: OrdLocal.reserve_only L (Local.promises lc1_src))
          (NORMAL_TVIEW1_SRC: Normal.normal_tview L (Local.tview lc1_src))
          (NORMAL_TVIEW1_TGT: Normal.normal_tview L (Local.tview lc1_tgt))
          (STABLE_TVIEW1_SRC: Stable.stable_tview L mem1_src (Local.tview lc1_src))
          (NORMAL_MEM1_SRC: Normal.normal_memory L mem1_src)
          (NORMAL_MEM1_TGT: Normal.normal_memory L mem1_tgt)
          (STABLE_MEM1_SRC: Stable.stable_memory L rels mem1_src)
          (WF1_SRC: Local.wf lc1_src mem1_src)
          (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
          (SC1_SRC: Memory.closed_timemap sc1 mem1_src)
          (SC1_TGT: Memory.closed_timemap sc1 mem1_tgt)
          (MEM1_SRC: Memory.closed mem1_src)
          (MEM1_TGT: Memory.closed mem1_tgt)
          (RELEASEDM: View.opt_le releasedm_tgt releasedm_src)
          (RELEASEDM_SRC: View.opt_le releasedm_src (Some (TView.cur (Local.tview lc1_src))))
          (RELEASEDM_TGT: View.opt_le releasedm_tgt (Some (TView.cur (Local.tview lc1_tgt))))
          (RELEASEDM_NORMAL_SRC: Normal.normal_view L (View.unwrap releasedm_src))
          (RELEASEDM_NORMAL_TGT: Normal.normal_view L (View.unwrap releasedm_tgt))
          (RELEASEDM_WF_SRC: View.opt_wf releasedm_src)
          (RELEASEDM_WF_TGT: View.opt_wf releasedm_tgt)
          (RELEASEDM_CLOSED_SRC: Memory.closed_opt_view releasedm_src mem1_src)
          (RELEASEDM_CLOSED_TGT: Memory.closed_opt_view releasedm_tgt mem1_tgt)
          (LOC: L loc)
          (STEP_TGT: Local.write_step lc1_tgt sc1 mem1_tgt loc from to val releasedm_tgt released_tgt ord
                                      lc2_tgt sc2 mem2_tgt kind):
      exists released_src lc2_src mem2_src,
        (<<STEP_SRC: OrdLocal.write_step L Ordering.acqrel
                                         lc1_src sc1 mem1_src loc from to val releasedm_src released_src ord
                                         lc2_src sc2 mem2_src kind>>) /\
        (<<LC2: sim_local lc2_src lc2_tgt>>) /\
        (<<MEM2: sim_memory ((loc, to, ord) :: rels) mem2_src mem2_tgt>>) /\
        (<<NORMAL_TVIEW2_SRC: Normal.normal_tview L (Local.tview lc2_src)>>) /\
        (<<NORMAL_TVIEW2_TGT: Normal.normal_tview L (Local.tview lc2_tgt)>>) /\
        (<<STABLE_TVIEW2_SRC: Stable.stable_tview L mem2_src (Local.tview lc2_src)>>) /\
        (<<NORMAL_MEM2_SRC: Normal.normal_memory L mem2_src>>) /\
        (<<NORMAL_MEM2_TGT: Normal.normal_memory L mem2_tgt>>) /\
        (<<STABLE_MEM2_SRC: Stable.stable_memory L ((loc, to, ord) :: rels) mem2_src>>).
    Proof.
      exploit sim_memory_stable_tview; try apply LC1; eauto. intro STABLE_TVIEW1_TGT.
      hexploit sim_memory_stable_memory; eauto. intro STABLE_MEM1_TGT.
      exploit write_step_loc_aux; try exact STEP_TGT; try exact RELEASEDM_SRC; eauto. i. des.
      exploit Normal.write_step; try exact STEP_TGT; eauto. i. des.
      exploit Stable.write_step; try exact STEP_TGT; eauto.
      { erewrite <- sim_memory_writes_wf; eauto. }
      { inv LC1. rewrite PROMISES in *. ss. }
      { ss. }
      { i. inv RELEASEDM_TGT; ss. apply View.bot_spec. }
      i. des. des_ifs.
      dup STEP_SRC. inv STEP_SRC. des_ifs.
      exploit Normal.write_step; try exact STEP; eauto. i. des.
      exploit Stable.write_step; try exact STEP; eauto.
      { ss. }
      { i. inv RELEASEDM_SRC; ss. apply View.bot_spec. }
      i. des. des_ifs.
      esplits; eauto.
      ii. eapply STABLE_MEM0; eauto. des; eauto.
      right. inv LOC0.
      - inv H. esplits; [econs 1; eauto|]. destruct ord0; ss.
      - esplits; eauto. right. ss.
    Qed.

    Lemma write_step_other_aux
          rels lc1_src mem1_src
          lc1_tgt sc1 mem1_tgt loc from to val releasedm released_tgt ord lc2_tgt sc2 mem2_tgt kind
          (LC1: sim_local lc1_src lc1_tgt)
          (MEM1: sim_memory rels mem1_src mem1_tgt)
          (RESERVE_ONLY1: OrdLocal.reserve_only L (Local.promises lc1_src))
          (WRITES1: Writes.wf L rels mem1_src)
          (WF1_SRC: Local.wf lc1_src mem1_src)
          (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
          (LOC: ~ L loc)
          (STEP_TGT: Local.write_step lc1_tgt sc1 mem1_tgt loc from to val releasedm released_tgt ord
                                      lc2_tgt sc2 mem2_tgt kind):
      exists released_src lc2_src mem2_src,
        <<STEP_SRC: OrdLocal.write_step L Ordering.acqrel
                                        lc1_src sc1 mem1_src loc from to val releasedm released_src ord
                                        lc2_src sc2 mem2_src kind>> /\
        <<LC2: sim_local lc2_src lc2_tgt>> /\
        <<MEM2: sim_memory rels mem2_src mem2_tgt>>.
    Proof.
      destruct (L loc) eqn:LOC'; try by congr.
      destruct lc1_src, lc1_tgt.
      inv LC1. inv STEP_TGT. inv WRITE. ss. subst.
      exploit promise; try exact PROMISE; eauto; try congr.
      { apply WF1_SRC. }
      i. des. esplits.
      - econs; [des_ifs|].
        econs; ss.
        { inv TVIEW. rewrite CUR. ss. }
        erewrite sim_tview_write_released; eauto. congr.
      - econs; ss.
        inv TVIEW. econs; ss; try congr.
        i. unfold LocFun.add.
        repeat (condtac; ss; eauto); subst; try congr.
        + specialize (REL loc0). des_ifs.
        + specialize (REL loc). des_ifs. rewrite REL. refl.
        + specialize (REL loc0). des_ifs.
      - ss.
    Qed.

    Lemma write_step_other
          rels lc1_src mem1_src
          lc1_tgt sc1 mem1_tgt loc from to val releasedm released_tgt ord lc2_tgt sc2 mem2_tgt kind
          (LC1: sim_local lc1_src lc1_tgt)
          (MEM1: sim_memory rels mem1_src mem1_tgt)
          (RESERVE_ONLY1: OrdLocal.reserve_only L (Local.promises lc1_src))
          (WRITES1: Writes.wf L rels mem1_src)
          (NORMAL_TVIEW1_SRC: Normal.normal_tview L (Local.tview lc1_src))
          (NORMAL_TVIEW1_TGT: Normal.normal_tview L (Local.tview lc1_tgt))
          (STABLE_TVIEW1_SRC: Stable.stable_tview L mem1_src (Local.tview lc1_src))
          (NORMAL_MEM1_SRC: Normal.normal_memory L mem1_src)
          (NORMAL_MEM1_TGT: Normal.normal_memory L mem1_tgt)
          (STABLE_MEM1_SRC: Stable.stable_memory L rels mem1_src)
          (WF1_SRC: Local.wf lc1_src mem1_src)
          (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
          (SC1_SRC: Memory.closed_timemap sc1 mem1_src)
          (SC1_TGT: Memory.closed_timemap sc1 mem1_tgt)
          (MEM1_SRC: Memory.closed mem1_src)
          (MEM1_TGT: Memory.closed mem1_tgt)
          (RELEASEDM_WF: View.opt_wf releasedm)
          (RELEASEDM_CLOSED: Memory.closed_opt_view releasedm mem1_src)
          (RELEASEDM_NORMAL: Normal.normal_view L (View.unwrap releasedm))
          (RELEASEDM_STABLE: Stable.stable_view L mem1_src (View.unwrap releasedm))
          (LOC: ~ L loc)
          (STEP_TGT: Local.write_step lc1_tgt sc1 mem1_tgt loc from to val releasedm released_tgt ord
                                      lc2_tgt sc2 mem2_tgt kind):
      exists released_src lc2_src mem2_src,
        (<<STEP_SRC: OrdLocal.write_step L Ordering.acqrel
                                         lc1_src sc1 mem1_src loc from to val releasedm released_src ord
                                         lc2_src sc2 mem2_src kind>>) /\
        (<<LC2: sim_local lc2_src lc2_tgt>>) /\
        (<<MEM2: sim_memory rels mem2_src mem2_tgt>>) /\
        (<<NORMAL_TVIEW2_SRC: Normal.normal_tview L (Local.tview lc2_src)>>) /\
        (<<NORMAL_TVIEW2_TGT: Normal.normal_tview L (Local.tview lc2_tgt)>>) /\
        (<<STABLE_TVIEW2_SRC: Stable.stable_tview L mem2_src (Local.tview lc2_src)>>) /\
        (<<NORMAL_MEM2_SRC: Normal.normal_memory L mem2_src>>) /\
        (<<NORMAL_MEM2_TGT: Normal.normal_memory L mem2_tgt>>) /\
        (<<STABLE_MEM2_SRC: Stable.stable_memory L rels mem2_src>>).
    Proof.
      exploit sim_memory_stable_tview; try apply LC1; eauto. intro STABLE_TVIEW1_TGT.
      hexploit sim_memory_stable_memory; eauto. intro STABLE_MEM1_TGT.
      hexploit sim_memory_closed_opt_view_src; eauto. intro RELEASEDM_CLOSED_TGT.
      hexploit sim_memory_stable_view; eauto. intro RELEASEDM_STABLE_TGT.
      exploit write_step_other_aux; eauto. i. des.
      exploit Normal.write_step; try exact STEP_TGT; eauto. i. des.
      exploit Stable.write_step; try exact STEP_TGT; eauto.
      { erewrite <- sim_memory_writes_wf; eauto. }
      { inv LC1. rewrite <- PROMISES. ss. }
      { ss. }
      i. des.
      dup STEP_SRC. inv STEP_SRC0. des_ifs.
      exploit Normal.write_step; try exact STEP; eauto. i. des.
      exploit Stable.write_step; try exact STEP; eauto; try congr. i. des.
      des_ifs. esplits; eauto.
    Qed.

    Lemma write_na_step_other_aux
          rels lc1_src mem1_src
          lc1_tgt sc1 mem1_tgt loc from to val ord lc2_tgt sc2 mem2_tgt msgs kinds kind
          (LC1: sim_local lc1_src lc1_tgt)
          (MEM1: sim_memory rels mem1_src mem1_tgt)
          (RESERVE_ONLY1: OrdLocal.reserve_only L (Local.promises lc1_src))
          (WRITES1: Writes.wf L rels mem1_src)
          (WF1_SRC: Local.wf lc1_src mem1_src)
          (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
          (LOC: ~ L loc)
          (STEP_TGT: Local.write_na_step lc1_tgt sc1 mem1_tgt loc from to val ord
                                         lc2_tgt sc2 mem2_tgt msgs kinds kind):
      exists lc2_src mem2_src,
        <<STEP_SRC: OrdLocal.write_na_step L Ordering.acqrel
                                           lc1_src sc1 mem1_src loc from to val ord
                                           lc2_src sc2 mem2_src msgs kinds kind>> /\
        <<LC2: sim_local lc2_src lc2_tgt>> /\
        <<MEM2: sim_memory rels mem2_src mem2_tgt>>.
    Proof.
      destruct lc1_src, lc1_tgt.
      inv LC1. inv STEP_TGT. ss. subst.
      exploit write_na; try exact WRITE; eauto; try apply WF1_SRC. i. des.
      esplits.
      - econs; [des_ifs|]. condtac; ss. econs; ss.
        inv TVIEW. rewrite CUR. eauto.
      - econs; ss.
        inv TVIEW. econs; ss; try congr.
        i. unfold LocFun.add.
        repeat (condtac; ss; eauto); subst; try congr.
        + specialize (REL loc0). des_ifs.
        + specialize (REL loc). des_ifs. rewrite REL. refl.
        + specialize (REL loc0). des_ifs.
      - ss.
    Qed.

    Lemma write_na_step_other
          rels lc1_src mem1_src
          lc1_tgt sc1 mem1_tgt loc from to val ord lc2_tgt sc2 mem2_tgt msgs kinds kind
          (LC1: sim_local lc1_src lc1_tgt)
          (MEM1: sim_memory rels mem1_src mem1_tgt)
          (RESERVE_ONLY1: OrdLocal.reserve_only L (Local.promises lc1_src))
          (WRITES1: Writes.wf L rels mem1_src)
          (NORMAL_TVIEW1_SRC: Normal.normal_tview L (Local.tview lc1_src))
          (NORMAL_TVIEW1_TGT: Normal.normal_tview L (Local.tview lc1_tgt))
          (STABLE_TVIEW1_SRC: Stable.stable_tview L mem1_src (Local.tview lc1_src))
          (NORMAL_MEM1_SRC: Normal.normal_memory L mem1_src)
          (NORMAL_MEM1_TGT: Normal.normal_memory L mem1_tgt)
          (STABLE_MEM1_SRC: Stable.stable_memory L rels mem1_src)
          (WF1_SRC: Local.wf lc1_src mem1_src)
          (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
          (SC1_SRC: Memory.closed_timemap sc1 mem1_src)
          (SC1_TGT: Memory.closed_timemap sc1 mem1_tgt)
          (MEM1_SRC: Memory.closed mem1_src)
          (MEM1_TGT: Memory.closed mem1_tgt)
          (LOC: ~ L loc)
          (STEP_TGT: Local.write_na_step lc1_tgt sc1 mem1_tgt loc from to val ord
                                         lc2_tgt sc2 mem2_tgt msgs kinds kind):
      exists lc2_src mem2_src,
        (<<STEP_SRC: OrdLocal.write_na_step L Ordering.acqrel
                                            lc1_src sc1 mem1_src loc from to val ord
                                            lc2_src sc2 mem2_src msgs kinds kind>>) /\
        (<<LC2: sim_local lc2_src lc2_tgt>>) /\
        (<<MEM2: sim_memory rels mem2_src mem2_tgt>>) /\
        (<<NORMAL_TVIEW2_SRC: Normal.normal_tview L (Local.tview lc2_src)>>) /\
        (<<NORMAL_TVIEW2_TGT: Normal.normal_tview L (Local.tview lc2_tgt)>>) /\
        (<<STABLE_TVIEW2_SRC: Stable.stable_tview L mem2_src (Local.tview lc2_src)>>) /\
        (<<NORMAL_MEM2_SRC: Normal.normal_memory L mem2_src>>) /\
        (<<NORMAL_MEM2_TGT: Normal.normal_memory L mem2_tgt>>) /\
        (<<STABLE_MEM2_SRC: Stable.stable_memory L rels mem2_src>>).
    Proof.
      exploit sim_memory_stable_tview; try apply LC1; eauto. intro STABLE_TVIEW1_TGT.
      hexploit sim_memory_stable_memory; eauto. intro STABLE_MEM1_TGT.
      exploit write_na_step_other_aux; eauto. i. des.
      exploit Normal.write_na_step; try exact STEP_TGT; eauto. i. des.
      exploit Stable.write_na_step; try exact STEP_TGT; eauto.
      { erewrite <- sim_memory_writes_wf; eauto. }
      { inv LC1. rewrite <- PROMISES. ss. }
      i. des.
      dup STEP_SRC. inv STEP_SRC0; ss. des_ifs.
      exploit Normal.write_na_step; try exact STEP; eauto. i. des.
      exploit Stable.write_na_step; try exact STEP; eauto; try congr. i. des.
      des_ifs. esplits; eauto.
    Qed.

    Lemma fence_step_aux
          lc1_src
          lc1_tgt sc1 ordr ordw lc2_tgt sc2
          (LC1: sim_local lc1_src lc1_tgt)
          (STEP_TGT: Local.fence_step lc1_tgt sc1 ordr ordw lc2_tgt sc2):
      exists lc2_src,
        <<STEP_SRC: Local.fence_step lc1_src sc1 ordr ordw lc2_src sc2>> /\
        <<LC2: sim_local lc2_src lc2_tgt>>.
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
          (LC1: sim_local lc1_src lc1_tgt)
          (MEM1: sim_memory rels mem1_src mem1_tgt)
          (WRITES1: Writes.wf L rels mem1_src)
          (NORMAL_TVIEW1_SRC: Normal.normal_tview L (Local.tview lc1_src))
          (NORMAL_TVIEW1_TGT: Normal.normal_tview L (Local.tview lc1_tgt))
          (STABLE_TVIEW1_SRC: Stable.stable_tview L mem1_src (Local.tview lc1_src))
          (STABLE_SC1_SRC: Stable.stable_timemap L mem1_src sc1)
          (WF1_SRC: Local.wf lc1_src mem1_src)
          (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
          (STEP_TGT: Local.fence_step lc1_tgt sc1 ordr ordw lc2_tgt sc2):
      exists lc2_src,
        (<<STEP_SRC: Local.fence_step lc1_src sc1 ordr ordw lc2_src sc2>>) /\
        (<<LC2: sim_local lc2_src lc2_tgt>>) /\
        (<<NORMAL_TVIEW2_SRC: Normal.normal_tview L (Local.tview lc2_src)>>) /\
        (<<NORMAL_TVIEW2_TGT: Normal.normal_tview L (Local.tview lc2_tgt)>>) /\
        (<<STABLE_TVIEW2_SRC: Stable.stable_tview L mem1_src (Local.tview lc2_src)>>) /\
        (<<STABLE_SC2_SRC: Stable.stable_timemap L mem1_src sc2>>).
    Proof.
      exploit sim_memory_stable_tview; try apply LC1; eauto. intro STABLE_TVIEW1_TGT.
      exploit fence_step_aux; eauto. i. des.
      exploit Normal.fence_step; try exact STEP_TGT; eauto. i. des.
      exploit Stable.fence_step; try exact STEP_TGT; eauto.
      { eapply sim_memory_stable_view; eauto. }
      { erewrite <- sim_memory_writes_wf; eauto. }
      i. des.
      exploit Normal.fence_step; try exact STEP_SRC; eauto. i. des.
      exploit Stable.fence_step; try exact STEP_SRC; eauto. i. des.
      esplits; eauto.
    Qed.

    Lemma failure_step
          lc1_src lc1_tgt
          (LC1: sim_local lc1_src lc1_tgt)
          (STEP_TGT: Local.failure_step lc1_tgt):
      <<STEP_SRC: Local.failure_step lc1_src>>.
    Proof.
      destruct lc1_src, lc1_tgt.
      inv LC1. inv TVIEW. ss. subst.
      inv STEP_TGT. ss.
      econs. ii. ss.
      rewrite CUR. eauto.
    Qed.

    Lemma is_racy
          rels lc1_src mem1_src
          lc1_tgt mem1_tgt loc to ord
          (LC1: sim_local lc1_src lc1_tgt)
          (MEM1: sim_memory rels mem1_src mem1_tgt)
          (STEP_TGT: Local.is_racy lc1_tgt mem1_tgt loc to ord):
      (<<STEP_SRC: Local.is_racy lc1_src mem1_src loc to ord>>).
    Proof.
      inv LC1. inv TVIEW. inv MEM1. inv STEP_TGT.
      rewrite <- PROMISES, <- CUR in *.
      exploit COMPLETE; eauto. i. des.
      econs; eauto.
      - ii. inv MSG; ss.
      - i. exploit MSG2; eauto. i. subst. inv MSG. ss.
    Qed.

    Lemma racy_read_step
          rels lc1_src mem1_src
          lc1_tgt mem1_tgt loc to val ord
          (LC1: sim_local lc1_src lc1_tgt)
          (MEM1: sim_memory rels mem1_src mem1_tgt)
          (LOC: ~ L loc)
          (STEP_TGT: Local.racy_read_step lc1_tgt mem1_tgt loc to val ord):
      (<<STEP_SRC: OrdLocal.racy_read_step L Ordering.acqrel lc1_src mem1_src loc to val ord>>).
    Proof.
      inv STEP_TGT.
      exploit is_racy; eauto. i. des.
      econs; eauto. condtac; ss.
    Qed.

    Lemma racy_write_step
          rels lc1_src mem1_src
          lc1_tgt mem1_tgt loc to ord
          (LC1: sim_local lc1_src lc1_tgt)
          (MEM1: sim_memory rels mem1_src mem1_tgt)
          (LOC: ~ L loc)
          (STEP_TGT: Local.racy_write_step lc1_tgt mem1_tgt loc to ord):
      (<<STEP_SRC: OrdLocal.racy_write_step L Ordering.acqrel lc1_src mem1_src loc to ord>>).
    Proof.
      inv STEP_TGT.
      exploit is_racy; eauto. i. des.
      econs; eauto. condtac; ss. econs; eauto.
      eapply sim_local_promise_consistent; eauto.
    Qed.

    Lemma racy_update_step
          rels lc1_src mem1_src
          lc1_tgt mem1_tgt loc to ordr ordw
          (LC1: sim_local lc1_src lc1_tgt)
          (MEM1: sim_memory rels mem1_src mem1_tgt)
          (STEP_TGT: Local.racy_update_step lc1_tgt mem1_tgt loc to ordr ordw):
      (<<STEP_SRC: Local.racy_update_step lc1_src mem1_src loc to ordr ordw>>).
    Proof.
      hexploit sim_local_promise_consistent; try eapply LC1; try by inv STEP_TGT; ss. i.
      inv STEP_TGT; eauto.
      exploit is_racy; eauto.
    Qed.


    Variant sim_event: forall (e_src e_tgt: ThreadEvent.t), Prop :=
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
    | sim_event_write_na
        loc msgs from to val ord:
      sim_event (ThreadEvent.write_na loc msgs from to val ord)
                (ThreadEvent.write_na loc msgs from to val ord)
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
    | sim_event_racy_read
        loc to val ord:
      sim_event (ThreadEvent.racy_read loc to val ord)
                (ThreadEvent.racy_read loc to val ord)
    | sim_event_racy_write
        loc to val ord:
      sim_event (ThreadEvent.racy_write loc to val ord)
                (ThreadEvent.racy_write loc to val ord)
    | sim_event_racy_update
        loc to valr valw ordr ordw:
      sim_event (ThreadEvent.racy_update loc to valr valw ordr ordw)
                (ThreadEvent.racy_update loc to valr valw ordr ordw)
    .
    Hint Constructors sim_event.

    Lemma sim_event_eq_program_event
          e_src e_tgt
          (SIM: sim_event e_src e_tgt):
      ThreadEvent.get_program_event e_src = ThreadEvent.get_program_event e_tgt.
    Proof.
      inv SIM; ss.
    Qed.

    Lemma thread_step
          rels e1_src e1_tgt
          pf e_tgt e2_tgt
          (SIM1: sim_thread rels e1_src e1_tgt)
          (WRITES1: Writes.wf L rels (Thread.memory e1_src))
          (RESERVE_ONLY1: OrdLocal.reserve_only L (Local.promises (Thread.local e1_src)))
          (STABLE1_SRC: Stable.stable_thread L rels e1_src)
          (NORMAL1_SRC: Normal.normal_thread L e1_src)
          (NORMAL1_TGT: Normal.normal_thread L e1_tgt)
          (WF1_SRC: Local.wf (Thread.local e1_src) (Thread.memory e1_src))
          (WF1_TGT: Local.wf (Thread.local e1_tgt) (Thread.memory e1_tgt))
          (SC1_SRC: Memory.closed_timemap (Thread.sc e1_src) (Thread.memory e1_src))
          (SC1_TGT: Memory.closed_timemap (Thread.sc e1_tgt) (Thread.memory e1_tgt))
          (MEM1_SRC: Memory.closed (Thread.memory e1_src))
          (MEM1_TGT: Memory.closed (Thread.memory e1_tgt))
          (PROMISE: forall loc from to msg kind
                      (EVENT: e_tgt = ThreadEvent.promise loc from to msg kind),
              L loc /\ msg = Message.reserve)
          (RACY_READ: forall loc to val ord (EVENT: e_tgt = ThreadEvent.racy_read loc to val ord), ~ L loc)
          (RACY_WRITE: forall loc to val ord (EVENT: e_tgt = ThreadEvent.racy_write loc to val ord), ~ L loc)
          (RACY_UPDATE: forall loc to valr valw ordr ordw
                          (EVENT: e_tgt = ThreadEvent.racy_update loc to valr valw ordr ordw),
              ~ L loc \/ Ordering.le ordr Ordering.na \/ Ordering.le ordw Ordering.na)
          (STEP_TGT: OrdThread.step L Ordering.na Ordering.plain pf e_tgt e1_tgt e2_tgt):
      (exists e_src e2_src,
          (<<STEP_SRC: OrdThread.step L Ordering.acqrel Ordering.acqrel pf e_src e1_src e2_src>>) /\
          __guard__ (
              (<<SIM2: sim_thread (Writes.append L e_src rels) e2_src e2_tgt>>) /\
              (<<EVENT: sim_event e_src e_tgt>>) /\
              (<<STABLE2_SRC: Stable.stable_thread L (Writes.append L e_src rels) e2_src>>) /\
              (<<NORMAL2_SRC: Normal.normal_thread L e2_src>>) /\
              (<<NORMAL2_TGT: Normal.normal_thread L e2_tgt>>))) \/
      (<<RACE: RARaceW.ra_race L rels (Local.tview (Thread.local e1_src)) (ThreadEvent.get_program_event e_tgt)>>).
    Proof.
      destruct e1_src as [st1_src lc1_src sc1_src mem1_src].
      destruct e1_tgt as [st1_tgt lc1_tgt sc1_tgt mem1_tgt].
      inv SIM1. inv STABLE1_SRC. inv NORMAL1_SRC. inv NORMAL1_TGT. ss. subst.
      hexploit sim_memory_stable_tview; eauto; try apply LOCAL. intro STABLE_TVIEW1_TGT.
      hexploit sim_memory_stable_memory; eauto. intro STABLE_MEM1_TGT.
      inv STEP_TGT; inv STEP; [|inv LOCAL0]; ss.
      - (* promise step *)
        exploit PROMISE; eauto. i. des. subst.
        exploit promise_step; try exact LOCAL0; eauto. i. des.
        hexploit Normal.promise_step; try exact STEP_SRC; eauto; ss. i. des.
        hexploit Normal.promise_step; try exact LOCAL0; eauto; ss. i. des.
        exploit Stable.promise_step; try exact STEP_SRC; eauto; ss. i. des.
        exploit Stable.promise_step; try exact LOCAL0; eauto; ss. i. des.
        left. esplits.
        + econs 1.
          * econs; eauto.
          * ii. inv PROMISE0. ss.
        + unguard. splits; eauto; econs; eauto. ss.
          eapply Stable.future_stable_view; try apply STABLE_SC; eauto.
          exploit Local.promise_step_future; try exact STEP_SRC; eauto. i. des. ss.
      - (* silent step *)
        left. esplits.
        + econs 2. econs; [|econs 1]. eauto.
        + unguard. esplits; ss.
      - (* read step *)
        inv LOCAL1. rewrite OrdLocal.ordc_na in *; ss.
        destruct (L loc) eqn:LOC.
        + exploit read_step_loc; try exact LOCAL0; eauto. i. unguardH x0. des.
          { left. esplits.
            - econs 2. econs; [|econs 2]; eauto.
            - unguard. esplits; ss.
          }
          { right. left. esplits; ss. }
        + exploit read_step_other; try exact LOCAL0; eauto. i. des.
          left. esplits.
          * econs 2. econs; [|econs 2]; eauto.
          * esplits; ss.
      - (* write step *)
        inv LOCAL1. destruct (L loc) eqn:LOC.
        + hexploit write_step_loc; try exact LOCAL0; eauto; ss. i. des.
          exploit OrdLocal.write_step_le.
          { rewrite LOC. eauto. }
          { ss. }
          i. left. esplits.
          * econs 2. econs; [|econs 3]; eauto.
          * unguard. unfold Writes.append. ss. rewrite LOC.
            esplits; ss.
            { econs; ss. eapply sim_memory_ord_le; eauto. destruct ord; ss. }
            { econs; ss.
              - inv STEP_SRC.
                exploit Local.write_step_future; try eapply STEP0; eauto. i. des.
                inv STEP0. ss.
                eapply Stable.future_stable_view; try exact STABLE_SC; eauto.
              - eapply Stable.stable_memory_le; eauto. destruct ord; ss.
            }
        + hexploit write_step_other; try exact LOCAL0; eauto; ss; try congr.
          { apply Stable.bot_stable_view. ss. }
          i. des. left. esplits.
          * econs 2. econs; [|econs 3]; eauto.
          * unguard. unfold Writes.append. ss. rewrite LOC.
            esplits; ss. econs; ss. inv STEP_SRC.
            exploit Local.write_step_future; try eapply STEP0; eauto. i. des.
            inv STEP0. ss.
            eapply Stable.future_stable_view; try exact STABLE_SC; eauto.
      - (* update step *)
        inv LOCAL1. destruct (L loc) eqn:LOC.
        + exploit read_step_loc; try exact STEP; eauto. i. des.
          exploit Local.read_step_future; try exact STEP; eauto. i. des.
          dup STEP_SRC. inv STEP_SRC0.
          exploit Local.read_step_future; try exact STEP0; eauto. i. des.
          clear STEP0. unguardH x1. des.
          * inv LOCAL2.
            hexploit write_step_loc; try exact STEP0; try exact RELEASED_SRC; eauto.
            { inv STEP_SRC. inv STEP1. ss. }
            { inv STEP. inv STEP_SRC. inv STEP. inv MEMORY.
              exploit SOUND; eauto. i. des.
              rewrite GET_TGT in *. inv GET. inv MSG.
              revert RELEASED. condtac; ss.
            }
            { destruct released_src; ss. inv STEP_SRC. inv STEP1. eauto. }
            { destruct releasedr; ss. inv STEP. eauto. }
            i. des. left. esplits.
            { apply OrdLocal.write_step_le in STEP_SRC0; ss.
              econs 2. econs; [|econs 4]; eauto. destruct ordr; ss.
            }
            { unguard. unfold Writes.append. ss. rewrite LOC in *.
              esplits; ss.
              - econs; ss. eapply sim_memory_ord_le; eauto. destruct ordw; ss.
              - econs; ss.
                inv STEP_SRC0. exploit Local.write_step_future; try exact STEP; eauto. i. des.
                inv STEP1. ss.
                eapply Stable.future_stable_view; try eapply STABLE_SC; ss.
                eapply Stable.stable_memory_le; eauto. destruct ordw; ss.
            }
          * right. left. esplits; ss. destruct ordr; ss.
        + exploit read_step_other; try exact STEP; eauto. i. des.
          exploit Local.read_step_future; try exact STEP; eauto. i. des.
          dup STEP_SRC. inv STEP_SRC0.
          exploit Local.read_step_future; try exact STEP0; eauto. i. des.
          inv LOCAL2. rewrite LOC in *.
          hexploit write_step_other; try exact STEP1; eauto; try congr.
          { inv STEP0. ss. }
          { inv STEP0. ss. destruct releasedr; ss. eauto. }
          { inv STEP0. ss.
            destruct releasedr; ss; try by apply Stable.bot_stable_view.
            eapply STABLE_MEMORY; eauto. left. congr.
          }
          i. des. left. esplits.
          * econs 2. econs; [|econs 4]; eauto.
          * unguard. unfold Writes.append. ss. rewrite LOC.
            esplits; ss. econs; ss.
            inv STEP_SRC0.
            exploit Local.write_step_future; try exact STEP2; eauto. i. des.
            inv STEP2. ss.
            eapply Stable.future_stable_view; try eapply STABLE_SC; eauto.
      - (* fence step *)
        exploit fence_step; try exact LOCAL1; eauto. i. des.
        left. esplits.
        + econs 2. econs; [|econs 5]; eauto.
        + unguard. esplits; ss.
      - (* syscall step *)
        exploit fence_step; try exact LOCAL1; eauto. i. des.
        left. esplits.
        + econs 2. econs; [|econs 6]; eauto.
        + unguard. esplits; ss.
      - (* failure step *)
        exploit failure_step; try exact LOCAL1; eauto. i. des.
        left. esplits.
        + econs 2. econs; [|econs 7]; eauto.
        + unguard. esplits; ss.
      - (* write na step *)
        inv LOCAL1.
        { destruct (L loc) eqn:LOC.
          { inv STEP. destruct ord; ss. }
          hexploit write_na_step_other; try exact STEP; eauto; try congr. i. des.
          left. esplits.
          - econs 2. econs; [|econs 8]; eauto.
          - unguard. unfold Writes.append. ss. rewrite LOC.
            splits; ss. econs; ss.
            inv STEP_SRC.
            + exploit Local.write_na_step_future; try exact STEP0; eauto. i. des.
              inv STEP0; ss.
              eapply Stable.future_stable_view; try eapply STABLE_SC; eauto.
            + exploit Local.write_step_future; try exact STEP0; eauto. i. des.
              inv STEP0; ss.
              eapply Stable.future_stable_view; try eapply STABLE_SC; eauto.
        }
        { hexploit write_step_loc; try exact STEP; eauto; ss. i. des.
          inv STEP_SRC. rewrite LOC in STEP0.
          replace (Ordering.join (Ordering.join ord Ordering.plain) Ordering.acqrel) with
              (Ordering.join ord Ordering.acqrel) in STEP0 by (destruct ord; ss).
          left. esplits.
          - econs 2. econs; [|econs 8]; eauto. econs 2; eauto.
          - unguard. unfold Writes.append. ss. rewrite LOC.
            splits; ss.
            + econs; ss. eapply sim_memory_ord_le; eauto.
            + econs; ss.
              { exploit Local.write_step_future; try exact STEP0; eauto. i. des.
                inv STEP0; ss.
                eapply Stable.future_stable_view; try eapply STABLE_SC; eauto.
              }
              { eapply Stable.stable_memory_le; eauto. }
        }
      - (* racy read step *)
        inv LOCAL1. rewrite OrdLocal.ordc_na in STEP; ss.
        exploit racy_read_step; try exact LOCAL1; eauto. i. des.
        left. esplits.
        + econs 2. econs; [|econs 9]; eauto.
        + unguard. esplits; ss.
      - (* racy write step *)
        inv LOCAL1.
        exploit racy_write_step; try exact LOCAL1; eauto. i. des.
        apply OrdLocal.racy_write_step_le in x0; try by (destruct ord; ss).
        left. esplits.
        + econs 2. econs; [|econs 10]; eauto.
        + unguard. esplits; ss.
      - (* racy update step *)
        exploit racy_update_step; try exact LOCAL1; eauto. i. des.
        left. esplits.
        + econs 2. econs; [|econs 11]; eauto.
        + unguard. esplits; ss.
    Qed.

    Lemma reserve_step
          rels e1_src e1_tgt e2_tgt
          (SIM1: sim_thread rels e1_src e1_tgt)
          (WRITES1: Writes.wf L rels (Thread.memory e1_src))
          (RESERVE_ONLY1: OrdLocal.reserve_only L (Local.promises (Thread.local e1_src)))
          (STABLE1_SRC: Stable.stable_thread L rels e1_src)
          (NORMAL1_SRC: Normal.normal_thread L e1_src)
          (NORMAL1_TGT: Normal.normal_thread L e1_tgt)
          (WF1_SRC: Local.wf (Thread.local e1_src) (Thread.memory e1_src))
          (WF1_TGT: Local.wf (Thread.local e1_tgt) (Thread.memory e1_tgt))
          (SC1_SRC: Memory.closed_timemap (Thread.sc e1_src) (Thread.memory e1_src))
          (SC1_TGT: Memory.closed_timemap (Thread.sc e1_tgt) (Thread.memory e1_tgt))
          (MEM1_SRC: Memory.closed (Thread.memory e1_src))
          (MEM1_TGT: Memory.closed (Thread.memory e1_tgt))
          (STEP_TGT: Thread.reserve_step e1_tgt e2_tgt):
      exists e2_src,
        (<<STEP_SRC: Thread.reserve_step e1_src e2_src>>) /\
        (<<SIM2: sim_thread rels e2_src e2_tgt>>) /\
        (<<STABLE2_SRC: Stable.stable_thread L rels e2_src>>) /\
        (<<NORMAL2_SRC: Normal.normal_thread L e2_src>>) /\
        (<<NORMAL2_TGT: Normal.normal_thread L e2_tgt>>).
    Proof.
      destruct e1_src as [st1_src lc1_src sc1_src mem1_src].
      destruct e1_tgt as [st1_tgt lc1_tgt sc1_tgt mem1_tgt].
      inv SIM1. inv STABLE1_SRC. inv NORMAL1_SRC. inv NORMAL1_TGT. ss.
      hexploit sim_memory_stable_tview; eauto; try apply LOCAL. intro STABLE_TVIEW1_TGT.
      hexploit sim_memory_stable_memory; eauto. intro STABLE_MEM1_TGT.
      inv STEP_TGT. inv STEP; inv STEP0; [|inv LOCAL0].
      exploit promise_step; try exact LOCAL0; eauto. i. des.
      exploit Normal.promise_step; try exact STEP_SRC; eauto; ss. i. des.
      exploit Normal.promise_step; try exact LOCAL0; eauto; ss. i. des.
      exploit Stable.promise_step; try exact STEP_SRC; eauto; ss. i. des.
      exploit Stable.promise_step; try exact LOCAL0; eauto; ss. i. des.
      esplits.
      + econs 1. econs 1. econs; eauto.
      + eauto.
      + econs; ss; eauto.
        eapply Stable.future_stable_view; try apply STABLE_SC; eauto.
        exploit Local.promise_step_future; try exact STEP_SRC; eauto. i. des. ss.
      + econs; eauto.
      + econs; eauto.
    Qed.

    Lemma cancel_step
          rels e1_src e1_tgt e2_tgt
          (SIM1: sim_thread rels e1_src e1_tgt)
          (WRITES1: Writes.wf L rels (Thread.memory e1_src))
          (RESERVE_ONLY1: OrdLocal.reserve_only L (Local.promises (Thread.local e1_src)))
          (STABLE1_SRC: Stable.stable_thread L rels e1_src)
          (NORMAL1_SRC: Normal.normal_thread L e1_src)
          (NORMAL1_TGT: Normal.normal_thread L e1_tgt)
          (WF1_SRC: Local.wf (Thread.local e1_src) (Thread.memory e1_src))
          (WF1_TGT: Local.wf (Thread.local e1_tgt) (Thread.memory e1_tgt))
          (SC1_SRC: Memory.closed_timemap (Thread.sc e1_src) (Thread.memory e1_src))
          (SC1_TGT: Memory.closed_timemap (Thread.sc e1_tgt) (Thread.memory e1_tgt))
          (MEM1_SRC: Memory.closed (Thread.memory e1_src))
          (MEM1_TGT: Memory.closed (Thread.memory e1_tgt))
          (STEP_TGT: Thread.cancel_step e1_tgt e2_tgt):
      exists e2_src,
        (<<STEP_SRC: Thread.cancel_step e1_src e2_src>>) /\
        (<<SIM2: sim_thread rels e2_src e2_tgt>>) /\
        (<<STABLE2_SRC: Stable.stable_thread L rels e2_src>>) /\
        (<<NORMAL2_SRC: Normal.normal_thread L e2_src>>) /\
        (<<NORMAL2_TGT: Normal.normal_thread L e2_tgt>>).
    Proof.
      destruct e1_src as [st1_src lc1_src sc1_src mem1_src].
      destruct e1_tgt as [st1_tgt lc1_tgt sc1_tgt mem1_tgt].
      inv SIM1. inv STABLE1_SRC. inv NORMAL1_SRC. inv NORMAL1_TGT. ss.
      hexploit sim_memory_stable_tview; eauto; try apply LOCAL. intro STABLE_TVIEW1_TGT.
      hexploit sim_memory_stable_memory; eauto. intro STABLE_MEM1_TGT.
      inv STEP_TGT. inv STEP; inv STEP0; [|inv LOCAL0].
      exploit promise_step; try exact LOCAL0; eauto. i. des.
      exploit Normal.promise_step; try exact STEP_SRC; eauto; ss. i. des.
      exploit Normal.promise_step; try exact LOCAL0; eauto; ss. i. des.
      exploit Stable.promise_step; try exact STEP_SRC; eauto; ss. i. des.
      exploit Stable.promise_step; try exact LOCAL0; eauto; ss. i. des.
      esplits.
      + econs 1. econs 1. econs; eauto.
      + eauto.
      + econs; ss; eauto.
        eapply Stable.future_stable_view; try apply STABLE_SC; eauto.
        exploit Local.promise_step_future; try exact STEP_SRC; eauto. i. des. ss.
      + econs; eauto.
      + econs; eauto.
    Qed.


    (* cap *)

    Lemma sim_memory_max_concrete_timemap
          rels mem_src mem_tgt tm_src tm_tgt
          (SIM: sim_memory rels mem_src mem_tgt)
          (MAX_SRC: Memory.max_concrete_timemap mem_src tm_src)
          (MAX_TGT: Memory.max_concrete_timemap mem_tgt tm_tgt):
      tm_src = tm_tgt.
    Proof.
      extensionality loc.
      destruct (MAX_SRC loc). des.
      destruct (MAX_TGT loc). des.
      inv SIM.
      exploit SOUND; eauto. i. des. inv MSG.
      exploit COMPLETE; try exact GET0. i. des. inv MSG.
      apply TimeFacts.antisym; eauto.
    Qed.

    Lemma sim_memory_adjacent_src
          rels mem_src mem_tgt
          loc from1 to1 from2 to2
          (SIM: sim_memory rels mem_src mem_tgt)
          (ADJ: Memory.adjacent loc from1 to1 from2 to2 mem_src):
      Memory.adjacent loc from1 to1 from2 to2 mem_tgt.
    Proof.
      inv SIM. inv ADJ.
      exploit SOUND; try exact GET1. i. des.
      exploit SOUND; try exact GET2. i. des.
      econs; eauto. i.
      exploit EMPTY; eauto. i.
      destruct (Memory.get loc ts mem_tgt) as [[]|] eqn:GETT; ss.
      exploit COMPLETE; eauto. i. des. congr.
    Qed.

    Lemma sim_memory_adjacent_tgt
          rels mem_src mem_tgt
          loc from1 to1 from2 to2
          (SIM: sim_memory rels mem_src mem_tgt)
          (ADJ: Memory.adjacent loc from1 to1 from2 to2 mem_tgt):
      Memory.adjacent loc from1 to1 from2 to2 mem_src.
    Proof.
      inv SIM. inv ADJ.
      exploit COMPLETE; try exact GET1. i. des.
      exploit COMPLETE; try exact GET2. i. des.
      econs; eauto. i.
      exploit EMPTY; eauto. i.
      destruct (Memory.get loc ts mem_src) as [[]|] eqn:GETT; ss.
      exploit SOUND; eauto. i. des. congr.
    Qed.

    Lemma sim_memory_max_ts
          rels mem_src mem_tgt
          (SIM: sim_memory rels mem_src mem_tgt)
          (CLOSED_SRC: Memory.closed mem_src)
          (CLOSED_TGT: Memory.closed mem_tgt):
      forall loc, Memory.max_ts loc mem_src = Memory.max_ts loc mem_tgt.
    Proof.
      inv SIM. i.
      exploit Memory.max_ts_spec; try eapply CLOSED_SRC. i. des.
      exploit Memory.max_ts_spec; try eapply CLOSED_TGT. i. des.
      exploit SOUND; eauto. i. des.
      exploit COMPLETE; try exact GET0. i. des.
      exploit Memory.max_ts_spec; try exact GET_TGT. i. des.
      exploit Memory.max_ts_spec; try exact GET_SRC. i. des.
      apply TimeFacts.antisym; eauto.
    Qed.

    Lemma sim_memory_cap
          rels mem_src mem_tgt cap_src cap_tgt
          (SIM: sim_memory rels mem_src mem_tgt)
          (CLOSED_SRC: Memory.closed mem_src)
          (CLOSED_TGT: Memory.closed mem_tgt)
          (CAP_SRC: Memory.cap mem_src cap_src)
          (CAP_TGT: Memory.cap mem_tgt cap_tgt):
      sim_memory rels cap_src cap_tgt.
    Proof.
      dup SIM. inv SIM0. econs; i.
      - exploit Memory.cap_inv; try exact CAP_SRC; eauto. i. des; subst.
        + exploit SOUND; eauto. i. des.
          inv CAP_TGT. exploit SOUND0; eauto.
        + exploit sim_memory_adjacent_src; eauto. i.
          inv CAP_TGT. exploit MIDDLE; eauto. i.
          esplits; eauto. refl.
        + erewrite sim_memory_max_ts; eauto.
          inv CAP_TGT. esplits; eauto. refl.
      - exploit Memory.cap_inv; try exact CAP_TGT; eauto. i. des; subst.
        + exploit COMPLETE; eauto. i. des.
          inv CAP_SRC. exploit SOUND0; eauto.
        + exploit sim_memory_adjacent_tgt; eauto. i.
          inv CAP_SRC. exploit MIDDLE; eauto. i.
          esplits; eauto. refl.
        + erewrite <- sim_memory_max_ts; eauto.
          inv CAP_SRC. esplits; eauto. refl.
      - exploit REL_WRITES; eauto. i. des.
        inv CAP_SRC. inv CAP_TGT.
        exploit SOUND0; eauto. i.
        exploit SOUND1; eauto.
    Qed.
  End APFtoRASim.
End APFtoRASim.
