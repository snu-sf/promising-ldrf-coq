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

Set Implicit Arguments.


(* TODO: move *)

Lemma time_le_join_l
      l r
      (LE: Time.le r l):
  Time.join l r = l.
Proof.
  unfold Time.join. condtac; auto.
  apply TimeFacts.antisym; auto.
Qed.

Lemma time_le_join_r
      l r
      (LE: Time.le l r):
  Time.join l r = r.
Proof.
  rewrite Time.join_comm.
  apply time_le_join_l; auto.
Qed.


Module Stable.
  Section Stable.
    Variable L: Loc.t -> bool.

    (* normal *)

    Definition normal_view (view: View.t): Prop :=
      forall loc (LOC: L loc), view.(View.rlx) loc = view.(View.pln) loc.

    Inductive normal_tview (tview:TView.t): Prop :=
    | normal_tview_intro
        (REL: forall loc, normal_view (tview.(TView.rel) loc))
        (CUR: normal_view tview.(TView.cur))
        (ACQ: normal_view tview.(TView.acq))
    .

    Definition normal_memory (mem: Memory.t): Prop :=
      forall loc from to val released
        (GET: Memory.get loc to mem = Some (from, Message.concrete val (Some released))),
        normal_view released.

    Lemma join_normal_view
          view1 view2
          (NORMAL1: normal_view view1)
          (NORMAL2: normal_view view2):
      normal_view (View.join view1 view2).
    Proof.
      ii. unfold normal_view in *.
      destruct view1, view2. ss.
      unfold TimeMap.join.
      rewrite NORMAL1, NORMAL2; ss.
    Qed.

    Lemma singleton_ur_normal_view loc ts:
      normal_view (View.singleton_ur loc ts).
    Proof. ss. Qed.

    Lemma singleton_rw_normal_view
          loc ts
          (LOC: ~ L loc):
      normal_view (View.singleton_rw loc ts).
    Proof.
      ii. ss.
      unfold TimeMap.singleton, LocFun.add, LocFun.init, LocFun.find.
      condtac; ss. subst. ss.
    Qed.

    Lemma singleton_ur_if_normal_view
          b loc ts
          (LOC: ~ L loc):
      normal_view (View.singleton_ur_if b loc ts).
    Proof.
      unfold View.singleton_ur_if. condtac.
      - apply singleton_ur_normal_view.
      - apply singleton_rw_normal_view. ss.
    Qed.


    (* stable *)

    Definition stable_view (mem: Memory.t) (view: View.t): Prop :=
      forall loc from val released
        (LOC: L loc)
        (GET: Memory.get loc (view.(View.rlx) loc) mem =
              Some (from, Message.concrete val (Some released))),
        View.le released view.

    Definition stable_timemap (mem: Memory.t) (tm: TimeMap.t): Prop :=
      stable_view mem (View.mk tm tm).

    Inductive stable_tview (mem: Memory.t) (tview: TView.t): Prop :=
    | stable_tview_intro
        (REL: forall loc, stable_view mem (tview.(TView.rel) loc))
        (CUR: stable_view mem tview.(TView.cur))
        (ACQ: stable_view mem tview.(TView.acq))
    .

    Definition stable_memory (mem: Memory.t): Prop :=
      forall loc from to val released
        (GET: Memory.get loc to mem = Some (from, Message.concrete val (Some released))),
        stable_view mem released.


    Lemma future_stable_view
          mem1 mem2 view
          (CLOSED: Memory.closed_view view mem1)
          (STABLE: stable_view mem1 view)
          (MEM_FUTURE: Memory.future mem1 mem2):
      stable_view mem2 view.
    Proof.
      ii. inv CLOSED. specialize (RLX loc). des.
      exploit Memory.future_get1; try exact RLX; eauto. i. des.
      rewrite GET0 in *. inv GET. inv MSG_LE. inv RELEASED.
      exploit STABLE; eauto.
    Qed.

    Lemma future_stable_tview
          mem1 mem2 tview
          (CLOSED: TView.closed tview mem1)
          (STABLE: stable_tview mem1 tview)
          (MEM_FUTURE: Memory.future mem1 mem2):
      stable_tview mem2 tview.
    Proof.
      destruct tview. inv CLOSED. inv STABLE. ss.
      econs; ss; eauto using future_stable_view.
    Qed.

    Lemma join_stable_view
          mem view1 view2
          (STABLE1: stable_view mem view1)
          (STABLE2: stable_view mem view2):
      stable_view mem (View.join view1 view2).
    Proof.
      ii. unfold stable_view in *.
      unfold View.join, TimeMap.join in GET. ss.
      exploit Time.join_cases. i. des.
      - erewrite x0 in GET.
        exploit STABLE1; eauto. i.
        etrans; eauto. apply View.join_l.
      - erewrite x0 in GET.
        exploit STABLE2; eauto. i.
        etrans; eauto. apply View.join_r.
    Qed.

    Lemma bot_stable_view
          mem
          (MEM: Memory.closed mem):
      stable_view mem View.bot.
    Proof.
      ii. inv MEM. rewrite INHABITED in *. inv GET.
    Qed.

    Lemma singleton_ur_stable_view
          mem loc ts
          (MEM: Memory.closed mem)
          (LOC: ~ L loc):
      stable_view mem (View.singleton_ur loc ts).
    Proof.
      ii. revert GET. ss.
      unfold TimeMap.singleton, LocFun.add, LocFun.init, LocFun.find.
      condtac; subst; ss. i.
      inv MEM. rewrite INHABITED in *. inv GET.
    Qed.

    Lemma singleton_rw_stable_view
          mem loc ts
          (MEM: Memory.closed mem)
          (LOC: ~ L loc):
      stable_view mem (View.singleton_rw loc ts).
    Proof.
      ii. revert GET. ss.
      unfold TimeMap.singleton, LocFun.add, LocFun.init, LocFun.find.
      condtac; subst; ss. i.
      inv MEM. rewrite INHABITED in *. inv GET.
    Qed.

    Lemma singleton_ur_if_stable_view
          mem b loc ts
          (MEM: Memory.closed mem)
          (LOC: ~ L loc):
      stable_view mem (View.singleton_ur_if b loc ts).
    Proof.
      unfold View.singleton_ur_if. condtac.
      - apply singleton_ur_stable_view; ss.
      - apply singleton_rw_stable_view; ss.
    Qed.


    (* step *)

    Lemma promise_step
          lc1 mem1 loc from to msg lc2 mem2 kind
          (WF1: Local.wf lc1 mem1)
          (MEM1: Memory.closed mem1)
          (NORMAL_TVIEW1: normal_tview lc1.(Local.tview))
          (NORMAL_MEM1: normal_memory mem1)
          (STABLE_TVIEW1: stable_tview mem1 lc1.(Local.tview))
          (STABLE_MEM1: stable_memory mem1)
          (MSG: forall val released
                  (MSG: msg = Message.concrete val (Some released)),
              normal_view released /\ stable_view mem2 released)
          (STEP: Local.promise_step lc1 mem1 loc from to msg lc2 mem2 kind):
      <<NORMAL_TVIEW2: normal_tview lc2.(Local.tview)>> /\
      <<NORMAL_MEM2: normal_memory mem2>> /\
      <<STABLE_TVIEW2: stable_tview mem2 lc2.(Local.tview)>> /\
      <<STABLE_MEM2: stable_memory mem2>>.
    Proof.
      inv STEP. inv PROMISE; ss.
      { (* add *)
        splits; ss.
        - ii. revert GET.
          erewrite Memory.add_o; eauto. condtac; ss; i.
          + des. subst. inv GET.
            exploit MSG; eauto. i. des. eauto.
          + eapply NORMAL_MEM1; eauto.
        - eapply future_stable_tview; eauto. apply WF1.
        - ii. revert GET.
          erewrite Memory.add_o; eauto. condtac; ss; i.
          + des. subst. inv GET.
            exploit MSG; eauto. i. des. eauto.
          + guardH o. inv MEM1. exploit CLOSED0; eauto. i. des.
            inv MSG_CLOSED. inv CLOSED1. inv CLOSED2.
            specialize (RLX loc1). des.
            exploit Memory.future_get1; try exact RLX.
            { econs 2; eauto. }
            i. des.
            rewrite GET1 in *. inv GET0. inv MSG_LE. inv RELEASED.
            etrans; eauto.
            eapply STABLE_MEM1; eauto.
      }

      { (* split *)
        des. subst.
        splits; ss.
        - ii. revert GET.
          erewrite Memory.split_o; eauto. repeat condtac; ss; i.
          + des. subst. inv GET.
            exploit MSG; eauto. i. des. eauto.
          + guardH o. des. subst. inv GET.
            exploit Memory.split_get0; try exact MEM. i. des.
            eapply NORMAL_MEM1; eauto.
          + eapply NORMAL_MEM1; eauto.
        - eapply future_stable_tview; eauto. apply WF1.
        - ii. revert GET.
          erewrite Memory.split_o; eauto. repeat condtac; ss; i.
          + des. subst. inv GET.
            exploit MSG; eauto. i. des. eauto.
          + guardH o. des. subst. inv GET.
            exploit Memory.split_get0; try exact MEM. i. des.
            inv MEM1. exploit CLOSED0; try exact GET1. i. des.
            inv MSG_CLOSED. inv CLOSED1. inv CLOSED2.
            specialize (RLX loc1). des.
            exploit Memory.future_get1; try exact RLX.
            { econs 2; eauto. }
            i. des.
            rewrite GET4 in *. inv GET0. inv MSG_LE. inv RELEASED.
            etrans; eauto.
            eapply STABLE_MEM1; eauto.
          + guardH o. guardH o0.
            inv MEM1. exploit CLOSED0; eauto. i. des.
            inv MSG_CLOSED. inv CLOSED1. inv CLOSED2.
            specialize (RLX loc1). des.
            exploit Memory.future_get1; try exact RLX.
            { econs 2; eauto. }
            i. des.
            rewrite GET1 in *. inv GET0. inv MSG_LE. inv RELEASED.
            etrans; eauto.
            eapply STABLE_MEM1; eauto.
      }

      { (* lower *)
        splits; ss.
        - ii. revert GET.
          erewrite Memory.lower_o; eauto. condtac; ss; i.
          + des. subst. inv GET.
            exploit MSG; eauto. i. des. eauto.
          + eapply NORMAL_MEM1; eauto.
        - eapply future_stable_tview; eauto. apply WF1.
        - ii. revert GET.
          erewrite Memory.lower_o; eauto. condtac; ss; i.
          + des. subst. inv GET.
            exploit MSG; eauto. i. des. eauto.
          + guardH o. inv MEM1. exploit CLOSED0; eauto. i. des.
            inv MSG_CLOSED. inv CLOSED1. inv CLOSED2.
            specialize (RLX loc1). des.
            exploit Memory.future_get1; try exact RLX.
            { econs 2; eauto. }
            i. des.
            rewrite GET1 in *. inv GET0. inv MSG_LE. inv RELEASED.
            etrans; eauto.
            eapply STABLE_MEM1; eauto.
      }

      { (* cancel *)
        splits; ss.
        - ii. revert GET.
          erewrite Memory.remove_o; eauto. condtac; ss; i.
          eapply NORMAL_MEM1; eauto.
        - eapply future_stable_tview; eauto. apply WF1.
        - ii. revert GET.
          erewrite Memory.remove_o; eauto. condtac; ss; i.
          guardH o. inv MEM1. exploit CLOSED0; eauto. i. des.
          inv MSG_CLOSED. inv CLOSED1. inv CLOSED2.
          specialize (RLX loc1). des.
          exploit Memory.future_get1; try exact RLX.
          { econs 2; eauto. }
          i. des.
          rewrite GET1 in *. inv GET0. inv MSG_LE. inv RELEASED.
          etrans; eauto.
          eapply STABLE_MEM1; eauto.
      }
    Qed.

    Lemma read_step_loc
          lc1 mem1 loc to val released ord lc2
          (WF1: Local.wf lc1 mem1)
          (MEM1: Memory.closed mem1)
          (NORMAL_TVIEW1: normal_tview lc1.(Local.tview))
          (NORMAL_MEM1: normal_memory mem1)
          (STABLE_TVIEW1: stable_tview mem1 lc1.(Local.tview))
          (STABLE_MEM1: stable_memory mem1)
          (LOC: L loc)
          (ORD: Ordering.le Ordering.acqrel ord)
          (STEP: Local.read_step lc1 mem1 loc to val released ord lc2):
      <<NORMAL_TVIEW2: normal_tview lc2.(Local.tview)>> /\
      <<STABLE_TVIEW2: stable_tview mem1 lc2.(Local.tview)>> /\
      <<LC2: to = lc1.(Local.tview).(TView.cur).(View.rlx) loc -> lc1 = lc2>>.
    Proof.
      inv STEP. ss. splits.
      - inv NORMAL_TVIEW1. econs; ss.
        + repeat eapply join_normal_view; ss.
          { destruct ord; ss. }
          { condtac; ss. destruct released; ss; eauto. }
        + repeat eapply join_normal_view; ss.
          { destruct ord; ss. }
          { condtac; ss. destruct released; ss; eauto. }
      - inv STABLE_TVIEW1. econs; ss.
        + unfold View.singleton_ur_if.
          repeat (condtac; [|destruct ord; ss]). ii.
          destruct (Loc.eq_dec loc loc0); subst; ss.
          * unfold TimeMap.join, View.singleton_ur_if,
            TimeMap.singleton, LocFun.add, LocFun.init, LocFun.find in GET0.
            revert GET0. condtac; ss. i.
            rewrite time_le_join_l in GET0; cycle 1.
            { etrans; [|eapply Time.join_r].
              inv MEM1. exploit CLOSED; try exact GET. i. des.
              inv MSG_TS. ss. }
            rewrite time_le_join_r in GET0; cycle 1.
            { inv READABLE. auto. }
            rewrite GET0 in *. inv GET. ss.
            etrans; [|apply View.join_r]. refl.
          * unfold TimeMap.join, View.singleton_ur_if,
            TimeMap.singleton, LocFun.add, LocFun.init, LocFun.find in GET0.
            revert GET0. condtac; try congr; ss. i.
            rewrite (@time_le_join_l _ Time.bot) in GET0; try apply Time.bot_spec.
            exploit Time.join_cases. i. des.
            { rewrite x0 in GET0.
              exploit CUR; eauto. i. etrans; eauto.
              etrans; [|apply View.join_l].
              etrans; [|apply View.join_l].
              refl. }
            { rewrite x0 in GET0. destruct released; ss; cycle 1.
              { unfold TimeMap.bot in *.
                inv MEM1. rewrite INHABITED in GET0. ss. }
              exploit STABLE_MEM1; try exact GET; eauto. i.
              etrans; eauto.
              etrans; [|apply View.join_r].
              refl. }
        + unfold View.singleton_ur_if.
          repeat (condtac; [|destruct ord; ss]). ii.
          destruct (Loc.eq_dec loc loc0); subst; ss.
          * unfold TimeMap.join, View.singleton_ur_if,
            TimeMap.singleton, LocFun.add, LocFun.init, LocFun.find in GET0.
            revert GET0. condtac; ss. i.
            rewrite Time.join_assoc in GET0.
            rewrite (@time_le_join_l to) in GET0; cycle 1.
            { inv MEM1. exploit CLOSED; try exact GET. i. des.
              inv MSG_TS. ss. }
            exploit Time.join_cases. i. des.
            { rewrite x0 in GET0.
              exploit ACQ; eauto. i. etrans; eauto.
              etrans; [|apply View.join_l].
              etrans; [|apply View.join_l].
              refl. }
            { rewrite x0 in GET0. rewrite GET0 in *. inv GET. ss.
              etrans; [|apply View.join_r]. 
              refl. }
          * unfold TimeMap.join, View.singleton_ur_if,
            TimeMap.singleton, LocFun.add, LocFun.init, LocFun.find in GET0.
            revert GET0. condtac; try congr; ss. i.
            rewrite (@time_le_join_l _ Time.bot) in GET0; try apply Time.bot_spec.
            exploit Time.join_cases. i. des.
            { rewrite x0 in GET0.
              exploit ACQ; eauto. i. etrans; eauto.
              etrans; [|apply View.join_l].
              etrans; [|apply View.join_l].
              refl. }
            { rewrite x0 in GET0. destruct released; ss; cycle 1.
              { unfold TimeMap.bot in *.
                inv MEM1. rewrite INHABITED in GET0. ss. }
              exploit STABLE_MEM1; try exact GET; eauto. i.
              etrans; eauto.
              etrans; [|apply View.join_r].
              refl. }
      - i. subst. destruct lc1. f_equal; ss.
        unfold TView.read_tview. condtac; ss. condtac; [|destruct ord]; ss.
        destruct tview; ss. f_equal; ss.
        + repeat rewrite View.le_join_l; ss.
          * eapply View.singleton_ur_spec; try apply WF1.
            inv NORMAL_TVIEW1. rewrite CUR; ss. refl.
          * destruct released; try apply View.bot_spec. ss.
            inv STABLE_TVIEW1. eauto.
          * eapply View.singleton_ur_spec; try apply WF1.
            inv NORMAL_TVIEW1. rewrite CUR; ss. refl.
        + repeat rewrite View.le_join_l; ss.
          * inv WF1. ss. inv TVIEW_WF. ss. etrans; eauto.
            eapply View.singleton_ur_spec; ss.
            inv NORMAL_TVIEW1. rewrite CUR0; ss. refl.
          * inv WF1. ss. inv TVIEW_WF. ss. etrans; eauto.
            destruct released; try apply View.bot_spec. ss.
            inv STABLE_TVIEW1. eauto.
          * inv WF1. ss. inv TVIEW_WF. ss. etrans; eauto.
            eapply View.singleton_ur_spec; ss.
            inv NORMAL_TVIEW1. rewrite CUR0; ss. refl.
    Qed.

    Lemma read_step_other
          lc1 mem1 loc to val released ord lc2
          (WF1: Local.wf lc1 mem1)
          (MEM1: Memory.closed mem1)
          (NORMAL_TVIEW1: normal_tview lc1.(Local.tview))
          (NORMAL_MEM1: normal_memory mem1)
          (STABLE_TVIEW1: stable_tview mem1 lc1.(Local.tview))
          (STABLE_MEM1: stable_memory mem1)
          (LOC: ~ L loc)
          (STEP: Local.read_step lc1 mem1 loc to val released ord lc2):
      <<NORMAL_TVIEW2: normal_tview lc2.(Local.tview)>> /\
      <<STABLE_TVIEW2: stable_tview mem1 lc2.(Local.tview)>>.
    Proof.
      inv STEP. ss. splits.
      - inv NORMAL_TVIEW1. econs; ss.
        + repeat apply join_normal_view; ss.
          * apply singleton_ur_if_normal_view. ss.
          * condtac; ss. destruct released; ss. eauto.
        + repeat apply join_normal_view; ss.
          * apply singleton_ur_if_normal_view. ss.
          * condtac; ss. destruct released; ss. eauto.
      - inv STABLE_TVIEW1. econs; ss.
        + repeat apply join_stable_view; ss.
          * apply singleton_ur_if_stable_view; ss.
          * condtac; ss.
            { destruct released; ss.
              - eapply STABLE_MEM1; eauto.
              - apply bot_stable_view; ss. }
            { apply bot_stable_view; ss. }
        + repeat apply join_stable_view; ss.
          * apply singleton_ur_if_stable_view; ss.
          * condtac; ss.
            { destruct released; ss.
              - eapply STABLE_MEM1; eauto.
              - apply bot_stable_view; ss. }
            { apply bot_stable_view; ss. }
    Qed.
  End Stable.
End Stable.
